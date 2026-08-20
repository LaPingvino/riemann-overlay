// proportion.go — the project's fitness function.
//
// Run after a successful `lake build`:
//
//	go run tools/proportion.go            # print the line
//	go run tools/proportion.go -append    # print it and append to PROPORTION.log
//
// It re-runs the axiom audit (`lake env lean audit/PrintAxioms.lean`), counts
// axioms and sorries in the sources, and prints
//
//	<ISO date> | certified: <p>% | axioms: <n> (<names>) | sorries on best path: <n> | binding constraint: <lemma>
//
// The binding-constraint field is the gradient: it names the single lemma or
// axiom that currently caps the number.
package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"time"
)

type entry struct {
	Row      string  `json:"row"`
	Name     string  `json:"name"`
	Lean     string  `json:"lean"`
	Value    float64 `json:"value"`
	Binding  string  `json:"binding"`
	Requires string  `json:"requires"`
	Note     string  `json:"note"`
	External bool    `json:"external"`
}

type baseInfo struct {
	Version int    `json:"version"`
	Note    string `json:"note"`
	Hash    string `json:"hash"`
	// Context records the *operator's* epistemic state, not the repo's: it is
	// bumped when the executing instance's memory is discontinuous (e.g. a
	// compaction).  The counts do not change; their meaning behind the
	// executor does.  If the error profile shifts, the seam must be findable.
	Context string `json:"context"`
}

// baseHash fingerprints the *statements* of every axiom in Assumptions.lean,
// normalized (comments stripped, whitespace collapsed) and sorted by name.
// It is the third detector beside the count and the names: a degradation that
// reuses an existing axiom's name moves neither of those, but moves this.
func baseHash(root string) (string, []string, error) {
	b, err := os.ReadFile(filepath.Join(root, "Riemann", "Assumptions.lean"))
	if err != nil {
		return "", nil, err
	}
	src := regexp.MustCompile(`(?s)/-.*?-/`).ReplaceAllString(string(b), "")
	src = regexp.MustCompile(`(?m)--.*$`).ReplaceAllString(src, "")
	// each axiom runs from `axiom` to the next top-level declaration or blank-line gap
	re := regexp.MustCompile("(?ms)^axiom\\s+([^\\s:]+)(.*?)(?:\n\n|\\z)")
	var stmts []string
	for _, m := range re.FindAllStringSubmatch(src, -1) {
		norm := strings.Join(strings.Fields(m[1]+" "+m[2]), " ")
		stmts = append(stmts, norm)
	}
	sort.Strings(stmts)
	h := sha256.Sum256([]byte(strings.Join(stmts, "\n")))
	return hex.EncodeToString(h[:])[:12], stmts, nil
}

type metric struct {
	Base        baseInfo `json:"base"`
	Baselines   []entry  `json:"baselines"`
	Certified   []entry  `json:"certified"`
	Conjectural []entry  `json:"conjectural"`
}

var stdAxioms = map[string]bool{"propext": true, "Classical.choice": true, "Quot.sound": true}

// runAudit returns, for each theorem printed by audit/PrintAxioms.lean, the
// non-standard axioms it depends on.
func runAudit(root string) (map[string][]string, error) {
	cmd := exec.Command("lake", "env", "lean", "audit/PrintAxioms.lean")
	cmd.Dir = root
	out, err := cmd.CombinedOutput()
	if err != nil {
		return nil, fmt.Errorf("axiom audit failed: %v\n%s", err, out)
	}
	// Output is pretty-printed and may wrap across lines; rejoin on the marker.
	text := strings.ReplaceAll(string(out), "\n", " ")
	re := regexp.MustCompile(`'([^']+)' depends on axioms: \[([^\]]*)\]`)
	res := map[string][]string{}
	for _, m := range re.FindAllStringSubmatch(text, -1) {
		var extra []string
		for _, a := range strings.Split(m[2], ",") {
			a = strings.TrimSpace(a)
			if a != "" && !stdAxioms[a] {
				extra = append(extra, a)
			}
		}
		sort.Strings(extra)
		res[m[1]] = extra
	}
	return res, nil
}

// countSorries counts `sorry` tokens outside comments, and `axiom` declarations.
func countSources(root string) (sorries int, axioms []string, err error) {
	axRe := regexp.MustCompile(`(?m)^axiom\s+([A-Za-z_][A-Za-z0-9_'.₀-₉]*)`)
	blockComment := regexp.MustCompile(`(?s)/-.*?-/`)
	lineComment := regexp.MustCompile(`(?m)--.*$`)
	err = filepath.Walk(filepath.Join(root, "Riemann"), func(p string, fi os.FileInfo, e error) error {
		if e != nil || fi.IsDir() || !strings.HasSuffix(p, ".lean") {
			return e
		}
		b, e := os.ReadFile(p)
		if e != nil {
			return e
		}
		src := string(b)
		// Strip block comments and docstrings, then line comments, so that
		// prose about `sorry` is not counted as a sorry.
		stripped := blockComment.ReplaceAllString(src, "")
		stripped = lineComment.ReplaceAllString(stripped, "")
		sorries += strings.Count(stripped, "sorry")
		for _, m := range axRe.FindAllStringSubmatch(stripped, -1) {
			axioms = append(axioms, m[1])
		}
		return nil
	})
	sort.Strings(axioms)
	return
}

// axiomKind classifies each declared axiom into `393`'s three groups.  The
// classification is read off the axioms' own docstrings in
// `Riemann/Assumptions.lean`, not judged: a *carrier* is an object declared
// rather than constructed, a *property* is a statement about such an object
// taken on trust, and *too weak* is a statement we believe and that still does
// not deliver what its consumer needs.
//
// `444`: this exists so the ruling `393` raised — should the ledger split the
// axiom count three ways — is a switch rather than an argument.  The default
// output is unchanged; `-axioms-by-kind` prints the split alongside it.
var axiomKind = map[string]string{
	"xiPrimeFamily":               "carrier",
	"closePairsZeta":              "carrier",
	"fujii_closePair_bookkeeping": "property",
	"levinson_montgomery":         "property",
	"zeta23_xiPrime":              "property",
	"fujii_ineffective":           "too-weak",
}

func main() {
	appendLog := flag.Bool("append", false, "append the line to PROPORTION.log")
	byKind := flag.Bool("axioms-by-kind", false,
		"also print `393`'s three-way split of the axiom count")
	flag.Parse()

	root, err := os.Getwd()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}

	var m metric
	b, err := os.ReadFile(filepath.Join(root, "tools", "metric.json"))
	if err != nil {
		fmt.Fprintln(os.Stderr, "cannot read tools/metric.json:", err)
		os.Exit(1)
	}
	if err := json.Unmarshal(b, &m); err != nil {
		fmt.Fprintln(os.Stderr, "bad metric.json:", err)
		os.Exit(1)
	}

	// MANDATORY AUDIT POINT (ISSUES #17): every claimed declaration must exist.
	if out, err := func() ([]byte, error) {
		c := exec.Command("lake", "env", "lean", "audit/Declarations.lean")
		c.Dir = root
		return c.CombinedOutput()
	}(); err != nil {
		// SESSION 142: this branch used to report "a claimed name does not
		// exist" for EVERY failure — including the case where `lake` was not on
		// PATH at all, which is the common one when the Lean env is unexported.
		// A tool that cannot run its own check must not report the check's
		// verdict.  R17: no witness, no belief, and that applies to bad news
		// exactly as much as to good.
		if _, ran := err.(*exec.ExitError); !ran {
			fmt.Fprintf(os.Stderr, "ESCALATION: could not RUN audit/Declarations.lean "+
				"(%v) — this is a harness failure, NOT a verdict on any declaration. "+
				"Is `lake` on PATH?\n%s\n", err, out)
			os.Exit(5)
		}
		fmt.Fprintf(os.Stderr, "ESCALATION: audit/Declarations.lean failed — a claimed name does not exist.\n%s\n", out)
		os.Exit(4)
	}

	// S-WITNESS: "the trusted base derives no falsehood" is an absence claim.
	// Its positive witness is that every file in audit/regression/ FAILS to
	// compile.  Silence here previously depended on a human remembering.
	if fs, e := filepath.Glob(filepath.Join(root, "audit", "regression", "*.lean")); e == nil {
		for _, f := range fs {
			rel, _ := filepath.Rel(root, f)
			c := exec.Command("lake", "env", "lean", rel)
			c.Dir = root
			if c.Run() == nil {
				fmt.Fprintf(os.Stderr, "ESCALATION: %s COMPILED. The trusted base is inconsistent again (ISSUES #8).\n", rel)
				os.Exit(5)
			}
		}
	}

	audit, err := runAudit(root)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}

	hash, stmts, err := baseHash(root)
	if err != nil {
		fmt.Fprintln(os.Stderr, "cannot fingerprint the trusted base:", err)
		os.Exit(1)
	}
	hashMoved := m.Base.Hash != "" && m.Base.Hash != hash

	sorries, declaredAxioms, err := countSources(root)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}

	// Two-row ledger: each row is scored independently, and a row counts only
	// if its audited axiom set contains no sorryAx.
	type row struct {
		e  entry
		ax []string
	}
	var rows []row
	for _, c := range m.Certified {
		ax, ok := audit[c.Lean]
		if !ok {
			fmt.Fprintf(os.Stderr, "warning: %s not in the axiom audit; treating as unproved\n", c.Lean)
			ax = nil
			c.Value = 0
		}
		for _, a := range ax {
			if a == "sorryAx" {
				fmt.Fprintf(os.Stderr, "warning: %s depends on sorryAx; contributes 0\n", c.Lean)
				c.Value = 0
			}
		}
		rows = append(rows, row{c, ax})
	}
	best := entry{Value: 0, Binding: "nothing proved"}
	var bestAxioms []string
	for _, r := range rows {
		if r.e.Value > best.Value {
			best, bestAxioms = r.e, r.ax
		}
	}

	conj := 0.0
	conjName := "—"
	for _, c := range m.Conjectural {
		if c.Value > conj {
			conj, conjName = c.Value, c.Requires
		}
	}

	var cells []string
	for _, r := range rows {
		cells = append(cells, fmt.Sprintf("%s: %.2f%%", r.e.Row, r.e.Value*100))
	}
	ctx := m.Base.Context
	if ctx == "" {
		ctx = "v1"
	}
	line := fmt.Sprintf("%s | base: v%d/%s (%s) | context: %s | certified[%s] | conjectural: %.2f%% (%s) | axioms: %d (%s) | sorries: %d | binding: %s",
		time.Now().Format("2006-01-02"),
		m.Base.Version, hash, strings.Split(m.Base.Note, " —")[0],
		ctx,
		strings.Join(cells, ", "),
		conj*100, conjName,
		len(bestAxioms), strings.Join(bestAxioms, ", "),
		sorries,
		best.Binding)

	fmt.Println(line)
	if *byKind {
		// `444`: the split `393` asked for, printed beside the unchanged line
		// so the ledger's format does not move.  An axiom missing from
		// `axiomKind` is named as unclassified rather than silently bucketed.
		counts := map[string]int{}
		var unclassified []string
		for _, a := range declaredAxioms {
			k, ok := axiomKind[a]
			if !ok {
				unclassified = append(unclassified, a)
				continue
			}
			counts[k]++
		}
		fmt.Printf("  axioms by kind: carrier %d, property %d, too-weak %d\n",
			counts["carrier"], counts["property"], counts["too-weak"])
		for _, k := range []string{"carrier", "property", "too-weak"} {
			var names []string
			for _, a := range declaredAxioms {
				if axiomKind[a] == k {
					names = append(names, a)
				}
			}
			fmt.Printf("    %-9s %s\n", k, strings.Join(names, ", "))
		}
		if len(unclassified) > 0 {
			fmt.Printf("    UNCLASSIFIED %s — add it to axiomKind with its reason\n",
				strings.Join(unclassified, ", "))
		}
	}
	if hashMoved {
		fmt.Printf("\nESCALATION: the trusted base's statement hash moved (%s -> %s) but base.version did not.\n", m.Base.Hash, hash)
		fmt.Printf("  %d axiom statements fingerprinted. Either bump base.version in tools/metric.json\n", len(stmts))
		fmt.Printf("  (an approved meaning-change) or revert the edit. Not writing the log line.\n")
		os.Exit(3)
	}
	for _, r := range rows {
		fmt.Printf("  row %-7s %6.2f%%  binding: %s\n", r.e.Row, r.e.Value*100, r.e.Binding)
	}
	fmt.Printf("  axioms declared in Riemann/: %d (%s)\n", len(declaredAxioms), strings.Join(declaredAxioms, ", "))

	if *appendLog {
		f, err := os.OpenFile(filepath.Join(root, "PROPORTION.log"), os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		defer f.Close()
		fmt.Fprintln(f, line)
	}
}
