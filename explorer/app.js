// Alpöge Lean explorer. Plain JS, no build step. Data: data/meta.json and the
// lazily loaded shards written by tools/explorer (see README).
"use strict";

const $ = (sel, el = document) => el.querySelector(sel);
const h = (tag, attrs = {}, ...kids) => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (v == null || v === false) continue;
    if (k === "class") e.className = v;
    else if (k.startsWith("on")) e.addEventListener(k.slice(2), v);
    else e.setAttribute(k, v === true ? "" : v);
  }
  for (const k of kids.flat()) if (k != null && k !== false) e.append(k.nodeType ? k : String(k));
  return e;
};

let META = null, COMP = null;
// ?d=grh reads data/grh/ (another edition, with a compartment map); default data/
const DATA = (() => { const d = new URLSearchParams(location.search).get("d"); return d && /^[a-z0-9-]+$/.test(d) ? `data/${d}/` : "data/"; })();
const shardCache = new Map(); // "n/12" -> Promise
function loadShard(kind, i) {
  const key = kind + "/" + i;
  if (!shardCache.has(key)) {
    shardCache.set(key, fetch(`${DATA}${key}.json`).then(r => {
      if (!r.ok) throw new Error(`${DATA}${key}.json: HTTP ${r.status}`);
      return r.json();
    }));
  }
  return shardCache.get(key);
}

// node row layout, as written by tools/explorer/write.go
// id lists are delta-encoded: [first, gap, gap, …]
const undelta = a => { let x = 0; return (a || []).map(d => (x += d)); }; // Go writes an empty list as null
function decode(id, shard, row) {
  let [name, kind, fi, line, declLine, endLine, sUses, bUses, sExt, bExt,
    usedBy, subDecls, subLines, exact, reach, stmt, doc] = row;
  [sUses, bUses, sExt, bExt] = [sUses, bUses, sExt, bExt].map(undelta);
  return { id, name, kind, file: shard.f[fi], line, declLine, endLine, sUses, bUses,
    sExt, bExt, usedBy, subDecls, subLines, exact: !!exact, reach: !!reach, stmt, doc };
}
async function node(id) {
  const S = META.shard, s = Math.floor(id / S);
  const sh = await loadShard("n", s);
  return decode(id, sh, sh.d[id - s * S]);
}
async function ext(i) {
  const S = META.extShard, s = Math.floor(i / S);
  const sh = await loadShard("x", s);
  const [name, lib, file, line] = sh[i - s * S];
  const L = META.libs[lib];
  return { name, lib: L.name, url: `${L.blob}${file}#L${line}`, file, line };
}

const fmt = n => n.toLocaleString("en-US");
const lines = d => d.endLine - d.line + 1;
function sizeText(d) {
  const a = d.exact ? "" : "≈ ";
  return `${a}${fmt(d.subDecls)} decls · ${a}${fmt(d.subLines)} lines`;
}
const kindChip = k => h("span", { class: "kind k-" + k.replace(/\s+/g, "-") }, k);

// ------------------------------------------------------------------ views

const app = () => $("#app");

function editionLine() {
  const R = META.release;
  return h("p", { class: "editions small" }, "Editions: ",
    h("a", { href: "./" }, "Alpöge's release (17.4M lines)"), " · ",
    h("a", { href: "?d=grh" }, "lsernau/grh-lean, readable edition (477k lines), with a compartment map"),
    R.commit ? h("span", { class: "muted" }, " — showing ", h("a", { href: R.repo }, R.edition), " at ",
      h("code", {}, R.commit.slice(0, 12))) : null);
}

function header() {
  const st = META.stats;
  if (META.release.commit) return h("section", { class: "about" }, editionLine(),
    h("p", {}, `Built from the edition's source at a pinned commit: ${fmt(st.files)} .lean files, ${fmt(st.lines)} lines, `,
      `${fmt(st.decls)} declarations. Declaration edges are [parsed]; in this edition most proofs call lemmas by dot notation on a local `,
      `(D.foo with D : Data P), which a parse cannot type, so the declaration cones below are far too small. `,
      `The compartment map's sizes and cones use module imports, which are exact.`),
    h("p", { class: "small" }, h("b", {}, "Licence: "), META.licence));
  return h("section", { class: "about" }, editionLine(),
    h("p", {},
      `Built from the release alone: ${fmt(st.files)} .lean files, ${fmt(st.lines)} lines, `,
      `${fmt(st.decls)} declarations. The five theorems of `, h("code", {}, "src/Main.lean"),
      ` reach ${fmt(st.reachable)} of them (${fmt(st.reachableLines)} lines). Generated `,
      META.generated.slice(0, 10), ` from the parts whose concatenation has SHA-256 `,
      h("code", { title: META.release.sha256 }, META.release.sha256.slice(0, 12) + "…"), "."),
    h("details", { class: "method" },
      h("summary", {}, "What this is, and what it is not — edges are ", h("b", {}, "[parsed]"), ", not [elaborated]"),
      h("p", {}, h("b", {}, "Read: "), "every .lean file of the release, streamed and parsed at the source level. ",
        "For each declaration the generator takes the identifiers its statement and its proof mention and resolves them ",
        "on the surface — current namespace and its parents, the declaration's own prefix, ", h("code", {}, "open"),
        "s in scope, and the import graph when a name is declared in several modules — against the tree's own names, ",
        "then against the declaration names of the pinned dependencies (",
        META.libs.map(l => `${l.name} ${l.rev.slice(0, 10)}`).join(", "),
        "), read the same way from their source. There the zoom stops and names the dependency's declaration."),
      h("p", {}, h("b", {}, "Inferred, so it can be wrong: "), "every edge here is ", h("b", {}, "[parsed]"),
        ". It misses what the elaborator supplies without a name in the text — instances found by type-class search, ",
        h("code", {}, "simp"), " sets, coercions, notation, terms built by tactics, and dot notation ",
        h("code", {}, "x.foo"), " on a local ", h("code", {}, "x"),
        ". It can add a spurious edge when a local binder shares a name with a declaration in scope. ",
        `References like Foo.ext, generated from a declaration Foo, are credited to Foo (${fmt(st.edgesViaGeneratedName)} mentions). `,
        `${fmt(st.unresolvedMentions)} of ${fmt(st.identifierMentions)} identifier mentions resolved to nothing (mostly local variables). `,
        `${fmt(st.ambiguousLookupsUnsettled)} lookups of a name declared in several modules (counted once per name per file) could not be settled by imports and are dropped.`),
      h("p", {}, h("b", {}, "Not checked: "), "whether the development builds, and with which axioms. No ",
        h("b", {}, "[elaborated]"), " edge appears here: that needs Lean's own environment after a build of the 17M-line tree, which was not done. ",
        "Sizes count the distinct declarations reachable through parsed edges, the node itself included; ",
        `a figure marked ≈ is a bottom-${META.sketchK} estimate (error about ${Math.round(100 / Math.sqrt(META.sketchK))}%), the rest are exact.`),
      h("p", {}, h("b", {}, "Licence: "), META.licence)),
  );
}

function crumbs(path) {
  const nav = h("nav", { class: "crumbs" }, h("a", { href: "#/" }, "Main.lean"));
  path.forEach((p, i) => {
    nav.append(" › ");
    const href = "#/n/" + path.slice(0, i + 1).join(",");
    nav.append(i === path.length - 1 ? h("span", { class: "here", "data-id": p }, "…")
      : h("a", { href, "data-id": p }, "…"));
  });
  // fill in names lazily
  nav.querySelectorAll("[data-id]").forEach(async el => {
    const d = await node(+el.dataset.id);
    el.textContent = lastComp(d.name);
    el.title = d.name;
  });
  return nav;
}
const lastComp = n => { const i = n.lastIndexOf("."); return i < 0 ? n : n.slice(i + 1); };

function card(d, big) {
  const c = h("article", { class: "card" + (big ? " big" : "") },
    h("div", { class: "row1" }, kindChip(d.kind), h("span", { class: "name mono" }, d.name)),
    h("div", { class: "loc mono" }, `${d.file}:${d.declLine}`,
      h("span", { class: "muted" }, ` · ${fmt(lines(d))} lines · used by ${fmt(d.usedBy)}`)),
    h("div", { class: "size" }, "under it: ", h("b", {}, sizeText(d)),
      d.reach || META.release.commit ? null : h("span", { class: "muted" }, " · not reached from Main.lean")),
  );
  if (META.statements) {
    if (d.stmt) c.append(h("pre", { class: "stmt" }, d.stmt));
    if (d.doc) c.append(h("div", { class: "doc" }, d.doc));
  } else if (big) {
    c.append(h("div", { class: "stmt off" }, META.release.commit ? "Statement and docstring left out of this data to keep it small; follow the file link." : "Statement and docstring withheld: the release carries no licence (see “What this is”)."));
  }
  return c;
}

// one row of a children list, expandable in place
function childRow(d, path) {
  const kids = h("div", { class: "kids" });
  let open = false;
  const tog = h("button", { class: "tog", "aria-label": "expand", disabled: d.sUses.length + d.bUses.length + d.sExt.length + d.bExt.length === 0 }, "▸");
  tog.onclick = async () => {
    open = !open;
    tog.textContent = open ? "▾" : "▸";
    kids.replaceChildren();
    if (open) kids.append(await childLists(d, [...path, d.id], true));
  };
  const href = "#/n/" + [...path, d.id].join(",");
  const max = META._max || 1;
  const w = Math.max(2, Math.round(100 * Math.log1p(d.subDecls) / Math.log1p(max)));
  return h("div", { class: "child" },
    h("div", { class: "line" }, tog, kindChip(d.kind),
      h("a", { class: "name mono", href, title: d.name }, d.name),
      h("span", { class: "loc mono muted" }, `${d.file.replace(/^src\//, "")}:${d.declLine}`),
      h("span", { class: "sz", title: sizeText(d) }, h("span", { class: "bar", style: `width:${w}%` }),
        h("span", { class: "szt" }, (d.exact ? "" : "≈") + fmt(d.subDecls)))),
    kids);
}

function extRow(e) {
  return h("div", { class: "child ext" },
    h("div", { class: "line" }, h("span", { class: "tog" }, "·"),
      h("span", { class: "kind k-ext" }, e.lib),
      h("a", { class: "name mono", href: e.url, target: "_blank", rel: "noopener", title: "source at the pinned revision" }, e.name),
      h("span", { class: "loc mono muted" }, `${e.file}:${e.line}`)));
}

async function childLists(d, path, nested) {
  const box = h("div", { class: "lists" + (nested ? " nested" : "") });
  const groups = [
    ["statement uses", d.sUses, d.sExt],
    ["proof uses", d.bUses, d.bExt],
  ];
  for (const [label, tree, exts] of groups) {
    if (!tree.length && !exts.length) continue;
    const ns = await Promise.all(tree.map(node));
    ns.sort((a, b) => b.subDecls - a.subDecls);
    const es = await Promise.all(exts.map(ext));
    es.sort((a, b) => a.name.localeCompare(b.name));
    const sec = h("section", { class: "group" },
      h("h3", {}, label, h("span", { class: "muted" },
        ` — ${tree.length} in the tree, ${exts.length} at the edge`, h("span", { class: "tag" }, "[parsed]"))));
    ns.forEach(x => sec.append(childRow(x, path)));
    if (es.length) {
      const ed = h("details", { class: "edge", open: !nested && es.length <= 12 },
        h("summary", {}, `${es.length} dependency declaration${es.length === 1 ? "" : "s"} (Mathlib and below: the zoom stops here)`));
      es.forEach(e => ed.append(extRow(e)));
      sec.append(ed);
    }
    box.append(sec);
  }
  if (!box.childNodes.length) box.append(h("p", { class: "muted" }, "Mentions no declaration that the parse could resolve."));
  return box;
}

// ------------------------------------------------------------------ compartments

const tk = n => n >= 1e6 ? (n / 1e6).toFixed(1) + "M" : n >= 1e4 ? Math.round(n / 1e3) + "k" : n >= 1e3 ? (n / 1e3).toFixed(1) + "k" : String(n);
function sizeLine(s) {
  return `${fmt(s.files)} files · ${fmt(s.lines)} lines · ~${tk(s.tokens)} tokens · ${fmt(s.decls)} declarations`;
}
function compCrumbs(i) {
  const chain = [];
  for (let j = i; j >= 0; j = COMP.nodes[j].parent) chain.unshift(j);
  const nav = h("nav", { class: "crumbs" });
  chain.forEach((j, k) => {
    if (k) nav.append(" › ");
    nav.append(j === i ? h("span", { class: "here" }, COMP.nodes[j].title) : h("a", { href: "#/c/" + j }, COMP.nodes[j].title));
  });
  return [nav, chain];
}
function edgeList(label, es) {
  if (!es || !es.length) return null;
  return h("p", { class: "small" }, h("b", {}, label + ": "),
    ...es.flatMap(([j, w], k) => [k ? ", " : "", h("a", { href: "#/c/" + j }, COMP.nodes[j].title), h("span", { class: "muted" }, ` (${w})`)]));
}
async function showComp(i) {
  const n = COMP.nodes[i];
  const [nav, chain] = compCrumbs(i);
  // what a reader must hold to read this node: the summaries on the path above it, and this node's own source
  const above = chain.slice(0, -1).reduce((a, j) => a + COMP.nodes[j].title.length + (COMP.nodes[j].summary || "").length, 0);
  const box = h("div", {}, editionLine(), searchBox(), nav,
    h("article", { class: "card big" },
      h("div", { class: "row1" }, h("span", { class: "kind k-" + n.kind }, n.kind), h("span", { class: "name" }, n.title)),
      n.path ? h("div", { class: "loc mono" }, h("a", { href: META.release.blob + n.path, target: "_blank", rel: "noopener" }, n.path)) : null,
      n.summary ? h("p", {}, n.summary) : null,
      n.align ? h("p", { class: "small muted" }, "Aligned with: " + n.align) : null,
      h("p", { class: "size" }, h("b", {}, "Itself: "), sizeLine(n.size)),
      h("p", { class: "size" }, h("b", {}, "Its cone "), "(every file it imports in the tree, itself included; Mathlib not counted): ", sizeLine(n.cone)),
      h("p", { class: "small muted" }, `To read it in one context: its cone, ~${tk(n.cone.tokens)} tokens, plus the map above it, ~${tk(Math.ceil(above / 4))} tokens. ${COMP.rule}.`),
      edgeList("Imports, at this level", n.uses), edgeList("Imported by, at this level", n.usedBy)));
  if (i === 0 && COMP.roots) {
    const sec = h("section", { class: "group" }, h("h3", {}, "The five theorems", h("span", { class: "muted" }, " — parsed declaration cones (an undercount, see above)")));
    for (const r of COMP.roots) sec.append(h("div", { class: "child" }, h("div", { class: "line" },
      h("span", { class: "tog" }, "·"), h("a", { class: "name mono", href: "#/n/" + r.node }, r.name),
      h("span", { class: "loc muted" }, `${fmt(r.decls)} decls · ${fmt(r.lines)} lines · ~${tk(r.tokens)} tokens`))));
    box.append(sec);
  }
  const kids = (n.children || []).map(j => [j, COMP.nodes[j]]);
  if (kids.length) {
    const max = Math.max(...kids.map(([, c]) => c.size.tokens), 1);
    const sec = h("section", { class: "group" }, h("h3", {}, "Inside", h("span", { class: "muted" }, ` — ${kids.length}; bar: tokens of the node itself`)));
    for (const [j, c] of kids) sec.append(h("div", { class: "child" }, h("div", { class: "line" },
      h("span", { class: "kind k-" + c.kind }, c.kind),
      h("a", { class: "name", href: "#/c/" + j, title: c.summary || c.path || "" }, c.title),
      h("span", { class: "loc muted" }, `${fmt(c.size.lines)} lines · cone ~${tk(c.cone.tokens)}`),
      h("span", { class: "sz", title: sizeLine(c.size) }, h("span", { class: "bar", style: `width:${Math.max(2, Math.round(100 * c.size.tokens / max))}%` }),
        h("span", { class: "szt" }, "~" + tk(c.size.tokens))))));
    box.append(sec);
  }
  if (n.decls && n.decls.length) {
    const ds = await Promise.all(n.decls.map(node));
    META._max = META._max || Math.max(...ds.map(d => d.subDecls), 1);
    const sec = h("section", { class: "group" }, h("h3", {}, "Declarations", h("span", { class: "muted" }, ` — ${ds.length}, in file order`)));
    ds.forEach(d => sec.append(childRow(d, [])));
    box.append(sec);
  }
  app().replaceChildren(box);
  window.scrollTo(0, 0);
}

async function showHome() {
  if (COMP) return showComp(0);
  const roots = await Promise.all(META.roots.map(node));
  META._max = Math.max(...roots.map(r => r.subDecls));
  const box = h("div", {}, header(), searchBox(),
    h("h2", {}, "The five theorems of ", h("code", {}, "src/Main.lean")));
  for (const r of roots) {
    const c = card(r, false);
    c.classList.add("root");
    c.onclick = () => (location.hash = "#/n/" + r.id);
    box.append(c);
  }
  app().replaceChildren(box);
}

async function showNode(path) {
  const id = path[path.length - 1];
  const d = await node(id);
  if (!META._max) META._max = d.subDecls;
  const box = h("div", {}, searchBox(), crumbs(path), card(d, true));
  box.append(h("p", { class: "muted small" }, "Children sorted by the size of what lies under them. ▸ opens a child in place; its name zooms in."));
  app().replaceChildren(box);
  box.append(await childLists(d, path, false));
  window.scrollTo(0, 0);
}

// ------------------------------------------------------------------ search

function keyOf(s) {
  const rs = [...s.toLowerCase()].slice(0, 2).join("");
  return [...new TextEncoder().encode(rs)].map(b => b.toString(16).padStart(2, "0")).join("");
}
let searchTimer = null, lastQ = "";
function searchBox() {
  const input = h("input", { type: "search", placeholder: "Search by name: the start of its last part, optionally qualified — rh_of_every, landau_entire, VW.crit", value: lastQ, autocomplete: "off", spellcheck: "false" });
  const out = h("div", { class: "results" });
  input.addEventListener("input", () => {
    clearTimeout(searchTimer);
    searchTimer = setTimeout(() => runSearch(input.value.trim(), out), 150);
  });
  input.addEventListener("keydown", e => {
    if (e.key === "Enter") { const a = out.querySelector("a"); if (a) location.hash = a.getAttribute("href"); }
    if (e.key === "Escape") { input.value = ""; out.replaceChildren(); }
  });
  if (lastQ) runSearch(lastQ, out);
  return h("div", { class: "search" }, input, out);
}
async function runSearch(q, out) {
  lastQ = q;
  if ([...q].length < 2) { out.replaceChildren(); return; }
  // buckets hold names by the first two letters of their last component
  const comps = q.split(".").filter(Boolean);
  const comp = comps[comps.length - 1] || "";
  if (!comp) { out.replaceChildren(); return; }
  let rows;
  try { rows = await loadShard("s", keyOf(comp)); } catch { rows = []; }
  if (q !== lastQ) return;
  const ql = q.toLowerCase();
  const lq = lastComp(ql);
  const hits = rows.filter(r => { const n = r[0].toLowerCase(); return n.includes(ql) && lastComp(n).startsWith(lq); });
  const score = r => {
    const n = r[0].toLowerCase();
    return (n === ql || n.endsWith("." + ql) ? 0 : 2) + (lastComp(n).startsWith(lastComp(ql)) ? 0 : 1) - r[2] * 4;
  };
  hits.sort((a, b) => score(a) - score(b) || a[0].length - b[0].length);
  out.replaceChildren(
    h("div", { class: "muted small" }, `${fmt(hits.length)} match${hits.length === 1 ? "" : "es"}` + (hits.length > 60 ? " — first 60" : "")),
    ...hits.slice(0, 60).map(r => h("a", { class: "hit mono" + (r[2] || META.release.commit ? "" : " unreached"), href: "#/n/" + r[1] }, r[0],
      r[2] || META.release.commit ? null : h("span", { class: "muted" }, " (not reached from Main.lean)"))));
}

// ------------------------------------------------------------------ routing

async function route() {
  const m = location.hash.match(/^#\/n\/([\d,]+)/);
  const c = location.hash.match(/^#\/c\/(\d+)/);
  try {
    if (c && COMP) await showComp(+c[1]);
    else if (m) await showNode(m[1].split(",").map(Number));
    else await showHome();
  } catch (e) {
    app().replaceChildren(h("div", { class: "notice" }, "Could not load: " + e.message));
  }
}

(async function () {
  try {
    const r = await fetch(DATA + "meta.json", { cache: "no-cache" });
    if (!r.ok) throw new Error(r.status);
    META = await r.json();
    if (META.compartments) {
      const rc = await fetch(DATA + "c.json", { cache: "no-cache" });
      if (rc.ok) COMP = await rc.json();
    }
  } catch (e) {
    app().replaceChildren(h("div", { class: "notice" }, h("b", {}, "Data being generated. "),
      "The page is live; the declaration graph is still being parsed from the release and will appear here when the generator has run."));
    return;
  }
  window.addEventListener("hashchange", route);
  route();
})();
