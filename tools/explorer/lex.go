package main

// A source-level lexer for Lean 4, good enough to find commands, declaration
// names, namespaces, opens and the identifiers a declaration mentions. It does
// not elaborate anything; see main.go's header for what that means for edges.

import (
	"strings"
	"unicode"
	"unicode/utf8"
)

type tok struct {
	s    string // identifier text, or a punctuation string
	id   bool   // identifier?
	line int32  // 1-based
	col  int32  // 0-based, in runes
	dot  bool   // identifier was preceded by '.' (field/dot notation) or '`'
}

type docstr struct {
	text      string
	startLine int32
	endLine   int32
}

func isIdStart(r rune) bool {
	if r == '_' {
		return true
	}
	if r == 'λ' || r == 'Π' || r == 'Σ' {
		return false
	}
	return unicode.IsLetter(r) || (r >= 0x1D49C && r <= 0x1D59F) || r == 'ℓ'
}

func isIdRest(r rune) bool {
	if isIdStart(r) || unicode.IsDigit(r) || r == '\'' || r == '!' || r == '?' {
		return true
	}
	// subscripts ₀-ₜ, ᵢ-ᵪ, ⱼ
	return (r >= 0x2080 && r <= 0x209C) || (r >= 0x1D62 && r <= 0x1D6A) || r == 0x2C7C
}

// lexFile returns the tokens of src with comments and string literals removed,
// and the docstrings it saw.
func lexFile(src string) ([]tok, []docstr) {
	var toks []tok
	var docs []docstr
	line := int32(1)
	col := int32(0)
	i := 0
	n := len(src)
	prevSig := rune(0) // previous significant rune (not whitespace)
	adv := func(k int) {
		for j := 0; j < k && i < n; {
			r, sz := utf8.DecodeRuneInString(src[i:])
			if r == '\n' {
				line++
				col = 0
			} else {
				col++
			}
			i += sz
			j += sz
		}
	}
	for i < n {
		r, sz := utf8.DecodeRuneInString(src[i:])
		switch {
		case r == '\n' || r == ' ' || r == '\t' || r == '\r':
			adv(sz)
			continue
		case r == '-' && strings.HasPrefix(src[i:], "--"):
			k := strings.IndexByte(src[i:], '\n')
			if k < 0 {
				k = n - i
			}
			adv(k)
			continue
		case r == '/' && strings.HasPrefix(src[i:], "/-"):
			isDoc := strings.HasPrefix(src[i:], "/--") && !strings.HasPrefix(src[i:], "/--/")
			start := i
			sl := line
			depth := 0
			for i < n {
				if strings.HasPrefix(src[i:], "/-") {
					depth++
					adv(2)
				} else if strings.HasPrefix(src[i:], "-/") {
					depth--
					adv(2)
					if depth == 0 {
						break
					}
				} else {
					_, s2 := utf8.DecodeRuneInString(src[i:])
					adv(s2)
				}
			}
			if isDoc {
				body := src[start:i]
				body = strings.TrimSuffix(strings.TrimPrefix(body, "/--"), "-/")
				docs = append(docs, docstr{strings.TrimSpace(body), sl, line})
			}
			continue
		case r == '"':
			adv(1)
			for i < n {
				c := src[i]
				if c == '\\' {
					adv(2)
					continue
				}
				adv(1)
				if c == '"' {
					break
				}
			}
			prevSig = '"'
			continue
		case r == '\'' && !isIdRest(prevSig) && prevSig != ')' && prevSig != ']':
			// char literal 'a' or '\n'
			j := i + 1
			if j < n && src[j] == '\\' {
				j += 2
			} else if j < n {
				_, s2 := utf8.DecodeRuneInString(src[j:])
				j += s2
			}
			if j < n && src[j] == '\'' {
				adv(j + 1 - i)
				prevSig = '\''
				continue
			}
			adv(sz)
			prevSig = r
			continue
		case r == '«' || isIdStart(r):
			sl, sc := line, col
			dot := prevSig == '.' || prevSig == '`'
			var b strings.Builder
			for i < n {
				c, s2 := utf8.DecodeRuneInString(src[i:])
				if c == '«' {
					k := strings.IndexRune(src[i:], '»')
					if k < 0 {
						break
					}
					b.WriteString(src[i+s2 : i+k])
					adv(k + len("»"))
				} else if isIdStart(c) {
					for i < n {
						c2, s3 := utf8.DecodeRuneInString(src[i:])
						if !isIdRest(c2) {
							break
						}
						b.WriteRune(c2)
						adv(s3)
					}
				} else {
					break
				}
				// continue through a dot followed by an identifier start
				if i+1 < n && src[i] == '.' {
					c3, _ := utf8.DecodeRuneInString(src[i+1:])
					if isIdStart(c3) || c3 == '«' {
						b.WriteByte('.')
						adv(1)
						continue
					}
				}
				break
			}
			toks = append(toks, tok{s: b.String(), id: true, line: sl, col: sc, dot: dot})
			prevSig = 'a'
			continue
		default:
			// punctuation of interest
			for _, p := range []string{":=", "@[", "::"} {
				if strings.HasPrefix(src[i:], p) {
					toks = append(toks, tok{s: p, line: line, col: col})
					adv(len(p))
					prevSig = ':'
					goto next
				}
			}
			toks = append(toks, tok{s: string(r), line: line, col: col})
			prevSig = r
			adv(sz)
		next:
		}
	}
	return toks, docs
}
