#!/usr/bin/env python3
"""Rebuild doc-gen4's study and theory pages as the docs pages of linglib.io, with their landing page.

A page shows the module docstring and the declarations by section, its headline declarations as
open cards and every other declaration as a row that opens in place, whose "Built from" line opens
the file's definitions its statement names. On a study page, which also shows the paper's title and
citation, the headlines are the theorems with a docstring. The right column places the study in the
library: the theory and fragments its statements use, with the names they use, the imports they
never name, the studies on the same theory, the papers it cites and those citing it, and the papers
it cites that no study formalizes. It also has the theorems whose statements name another paper's
definitions, with their sentences: this page's about other papers, and other pages' about this one.

`random.html` opens a study page at one of its theorems, named by `?t=`, which the page shows under
the citation. It draws from the theorems a module docstring names or that name another paper's
definitions, leaving out proofs that only evaluate and sentences that need the paper open.

On a theory page the headlines are the declarations the module docstring links to, as a mathlib
header names a file's main definitions and results, or the theorems with a docstring if it links to
none. The right column has the theory it builds on, then the theory, studies and fragments whose
statements use it, with the names they use, and the other files of its directory.

Everything comes from doc-gen4's output, read by `docgen_index`, and from the bibliography;
signatures and equations are doc-gen4's own, with their links. With `--checks`, the output of
`checks.py status --json`, a declaration stating an item of a source says whether a person has
checked it against the source (`checks/README.md`).

The pages replace doc-gen4's own at the same addresses, and the landing page its `index.html`, so
links to them keep landing. `--root` is the site's root relative to the docs directory.

Usage, from the repository root, after doc-gen4 has written `.lake/build/doc` and it is copied to
`.lake/build/doc-site/docs`:

    python3 scripts/gen_docs_pages.py --out .lake/build/doc-site/docs
    python3 scripts/gen_docs_pages.py --out DIR --only KehlerRohde2013 Linglib.Phonology   # some only
    python3 scripts/gen_docs_pages.py --out DIR --check   # also confirm anchors survive, links land
    python3 scripts/gen_docs_pages.py --out DIR --redirect OLD   # OLD/Studies/X.html forwards here
    python3 scripts/gen_docs_pages.py --out DIR --checks checks.json   # with the human checks
"""

import argparse
import datetime
import html
import json
import math
import os
import posixpath
import re
import shutil
import sys
from collections import defaultdict
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import docgen_index as dx  # noqa: E402
import gen_bibliography_page as gb  # noqa: E402
import site_shell  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
PAGE = ROOT / "scripts" / "docs_page"
REPO = "https://github.com/linglib-community/linglib"
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"
THEORY = ("Semantics", "Syntax", "Pragmatics", "Morphology", "Phonology", "Processing",
          "Discourse", "Logic")
KW = {"def": "def", "theorem": "theorem", "inductive": "inductive", "instance": "instance",
      "structure": "structure", "abbrev": "abbrev", "class": "class", "axiom": "axiom",
      "opaque": "opaque"}
# How a declaration stands to an item it is checked against, when it does not state it exactly.
RELATION = {"generalizes": "a generalization", "specializes": "a special case",
            "variant": "a variant"}
# A definition's docstring that opens with a paper locator ("(9):", "Eq. (12):", "Table 1:") shows
# it apart. A bare number is a numbered example; any other display carries its kind.
KIND = (r"Tables?|Tableau|Figures?|Fig\.|Eqs?\.|Equations?|Ex\.|Examples?|Def\.|Definitions?"
        r"|Sections?|§")
NUM = r"\(?\d+(?:\.\d+)*[a-z′]*\)?\*?"
LOC = re.compile(rf"^<p>((?:(?:{KIND})\s*|(?=\()){NUM}(?:\s*(?:,|and|to|–)\s*{NUM})*):\s*(\w)")
CITE_LINK = re.compile(r'<a href="([^"]*references\.html#ref_([^"]+))" title="[^"]*" id="[^"]*">'
                       r'(\[[^\]]+\])</a>', re.S)
HEADING = re.compile(r'<h\d id="([^"]+)"[^>]*>(.*?)(?: <a class="hover-link"|</h\d>)', re.S)
DECL_NAME = re.compile(r'<span class="decl_kind">\w+</span>\s*<span class="decl_name">.*?</a></span>',
                       re.S)
REFS = re.compile(r'(<h2 [^>]*id="References"[^>]*>.*?</h2>)\s*<ul>(.*?)</ul>', re.S)
BARE = '<span class="decl_args"> :</span>'
# A proof that only evaluates, which a sentence read alone can make sound like a discovery.
EVALUATED = re.compile(r":=\s*(?:by\s+)?(?:decide|rfl)\s*$")
# A sentence that needs the paper open, by leaning on what comes before it, or that speaks against
# the paper, which is not a first sight of it.
NOT_ALONE = re.compile(r"^(?:\(?\d|§|(?:It|This|These|They|Both|Each|Section|Part)\b)"
                       r"|\bthe (?:paper|book|chapter|author)\b|\bmisprint", re.I)
# A page left where the study pages used to be, which forwards to the page, anchor and all.
REDIRECT = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Moved</title>
<link rel="canonical" href="{href}">
<meta http-equiv="refresh" content="0; url={href}">
<script>location.replace({js} + location.hash);</script>
</head>
<body><p>This page is now at <a href="{href}">{href}</a>.</p></body>
</html>
"""
SHOWN = 5
# How many of each kind of neighbor a theory page's graph and lists show before folding the rest.
FILES_SHOWN, STUDIES_SHOWN = 8, 14
# The sections of a module docstring that note a file's details, rather than say what it offers.
NOTES = "Implementation notes|TODO|Notation|References"
# Docstrings write mathematics in TeX between dollar signs, as doc-gen4 reads them; a page with
# any loads MathJax, configured as doc-gen4's but drawing SVG, so that no web fonts load.
TEX = re.compile(r"(?<![\\$])\$(?!\s)[^$<>]+?(?<![\s\\])\$|\$\$.+?\$\$", re.S)
MATH = """<script>
MathJax = { tex: { inlineMath: [["$", "$"]], displayMath: [["$$", "$$"]] },
  options: { skipHtmlTags: ["script", "noscript", "style", "textarea", "pre", "code"] },
  svg: { fontCache: "global" } };
</script>
<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-svg.js"></script>"""


def text(h):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", h))).strip()


def esc(s):
    return html.escape(str(s), quote=True)


def link(href, label, cls=""):
    """An anchor; `label` is HTML."""
    return f'<a{f" class={chr(34)}{cls}{chr(34)}" if cls else ""} href="{esc(href)}">{label}</a>'


def and_more(items, n=SHOWN):
    return ", ".join(items[:n]) + (f" and {len(items) - n} more" if len(items) > n else "")


# ---------------------------------------------------------------- the library


def node_of(page):
    """The node of the graph a page belongs to: a study, a theory framework, a fragment, data."""
    p = page.split("#")[0].removesuffix(".html").split("/")
    if p[0] == "Studies" and len(p) >= 2:
        return "s", p[1]
    if p[0] != "Linglib" or len(p) < 3:
        return None
    if p[1] == "Fragments":
        return "f", p[2]
    if p[1] in THEORY:
        return "t", f"{p[1]}.{p[2]}"
    if p[1] == "Data":
        return "d", "/".join(p[1:])
    return None


def file_node(page):
    """The node of a page in a theory page's graph, where a theory or Core file is its own node."""
    p = page.split("#")[0].removesuffix(".html").split("/")
    if p[0] == "Linglib" and len(p) >= 3 and (p[1] in THEORY or p[1] == "Core"):
        return ("t" if p[1] in THEORY else "c"), "/".join(p[1:])
    return node_of(page)


def node_id(node):
    kind, name = node
    return name if kind == "s" else f"{kind}-{name}"


def node_label(node):
    kind, name = node
    return " / ".join(re.split(r"[./]", name)) if kind in "tdc" else name


def bib_label(f, year):
    """`Kehler & Rohde 2013` from an entry's authors (or editors) and year."""
    sur = []
    for raw in re.split(r"\s+and\s+", f.get("author") or f.get("editor") or ""):
        n = gb.tex_text(raw).strip()
        if n and n != "others":
            sur.append(n.split(",")[0].strip() if "," in n else n.split()[-1])
    if not sur:
        return ""
    who = sur[0] if len(sur) == 1 else " & ".join(sur) if len(sur) == 2 else f"{sur[0]} et al."
    return f"{who} {year}"


def match_study(key, names):
    """The study formalizing a bibliography entry: by name, ignoring case and hyphens, or as
    `FirstEtAlYEAR` for a key that lists three or more authors."""
    n = gb.study_name(key)
    if n in names:
        return n
    segs = key.split("-")
    yi = next((i for i, s in enumerate(segs) if re.fullmatch(r"\d{4}[a-z]?", s)), None)
    if yi is None:
        return None
    flat, etal = "".join(segs[:yi + 1]), f"{segs[0]}etal{segs[yi]}"
    cands = [s for s in names if s.lower() == flat or (yi >= 3 and s.lower() == etal)]
    cands += [s for s in names if s.lower().startswith(flat) and s[len(flat):][:1].isupper()]
    return cands[0] if cands else None


def namespace(names):
    """The namespace all of a file's declarations but its instances sit in, or "" if none."""
    plain = [n for n in names if not n.rsplit(".", 1)[-1].startswith("inst")] or names
    return ".".join(os.path.commonprefix([n.split(".")[:-1] for n in plain]))


def parents(d):
    """A directory and those above it, up to the root, as paths relative to the root."""
    while d:
        yield d
        d = posixpath.dirname(d)
    yield ""


def page_name(page):
    """A page's name beside the names of other pages: a study's, or a file's path in the library."""
    stem = page.removesuffix(".html")
    return stem.split("/", 1)[1]


def year_of(study):
    m = re.search(r"\d{4}", study)
    return int(m.group(0)) if m else None


class Library:
    """What every page needs from the rest of the library: the bibliography, who cites whom, the
    declarations' references, and which studies use which theory and fragments."""

    def __init__(self, doc, checks=None):
        self.doc = doc
        # The items of the sources, by `source/id`, and those each declaration states.
        self.items, self.items_of = {}, defaultdict(list)
        for c in checks["items"] if checks else ():
            self.items[f'{c["source"]}/{c["id"]}'] = c
            for name in c["decls"]:
                self.items_of[name].append(c)
        self.modules, self.decls, self.used_by = dx.build(doc)
        data = json.loads((doc / "declarations" / "declaration-data.bmp").read_text(encoding="utf-8"))
        self.decl_data, self.instances_for = data["declarations"], data.get("instancesFor", {})
        self.imported_by = {m: d["importedBy"] for m, d in data["modules"].items()}
        self.files = {p.relative_to(doc).as_posix() for p in doc.rglob("*") if p.is_file()}
        # The libraries whose modules the data lists but whose pages the site does not carry.
        carried = {p.split("/")[0].removesuffix(".html") for p in self.files}
        self.upstream = {m.split(".")[0] for m in data["modules"]} - carried
        self.studies = {s for s in gb.study_names() if f"Studies/{s}.html" in self.modules}
        self.bib, self.study_key = {}, {}
        for kind, key, f in gb.parse_bib(gb.BIB.read_text(encoding="utf-8")):
            y = re.search(r"\d{4}[a-z]?", key)
            e = {"label": bib_label(f, y.group(0) if y else f.get("year", "")) or key,
                 "title": gb.tex_html(f.get("title", "")), "authors": gb.authors(f),
                 "year": f.get("year", ""), "venue": gb.venue(kind, f), "doi": f.get("doi", ""),
                 "url": f.get("url", ""), "study": None,
                 "formalized": gb.role(key, f, self.studies) == "formalized"}
            s = match_study(key, self.studies)
            if s and s not in self.study_key:
                self.study_key[s], e["study"] = key, s
            self.bib[key] = e
        self.cited_in = gb.citations(set(self.bib))
        # The theory and fragments each study's statements use, and the reverse.
        self.uses, self.users, self.node_pages = defaultdict(set), defaultdict(set), defaultdict(set)
        for page, mod in self.modules.items():
            node = node_of(page)
            if node:
                self.node_pages[node].add(page)
            if not node or node[0] != "s":
                continue
            for b in mod["blocks"]:
                for ref in b.get("refs", ()):
                    used = node_of(ref)
                    if used and used[0] in "tf":
                        self.uses[node[1]].add(used)
        for s, nodes in self.uses.items():
            for n in nodes:
                self.users[n].add(s)
        # The docstringed theorems of each study whose statements name another study's definitions,
        # by the study named, and the reverse.
        self.about = defaultdict(lambda: defaultdict(list))
        self.about_me = defaultdict(lambda: defaultdict(list))
        for page, mod in self.modules.items():
            node = node_of(page)
            if not node or node[0] != "s":
                continue
            for b in mod["blocks"]:
                if b["type"] != "decl" or b["kind"] != "theorem" or not b["doc"]:
                    continue
                for other in sorted({node_of(r)[1] for r in b["refs"] if r.startswith("Studies/")}
                                    - {node[1]}):
                    self.about[node[1]][other].append(b)
                    self.about_me[other][node[1]].append(b)
        # For each page, the other pages whose statements name its declarations, and those names.
        self.named_by = defaultdict(lambda: defaultdict(set))
        self.in_dir = defaultdict(list)
        for page, mod in self.modules.items():
            self.in_dir[posixpath.dirname(page)].append(page)
            for b in mod["blocks"]:
                for ref in b.get("refs", ()):
                    used, _, anchor = ref.partition("#")
                    if used != page and used in self.modules:
                        self.named_by[used][page].add(anchor)

    def idf(self, node):
        return math.log((len(self.uses) + 1) / (1 + len(self.users[node])))

    def entry(self, study):
        key = self.study_key.get(study)
        return (key, self.bib[key]) if key else (None, None)

    def title(self, page):
        """A module's title, the first heading of its docstring, or its own name."""
        for b in self.modules[page]["blocks"][:1]:
            if b["type"] == "doc" and b["level"] == 1:
                return b["title"]
        return page.removesuffix(".html").split("/")[-1]

    def cites(self, study):
        """The bibliography keys a study's file cites."""
        here = f"Studies/{study}.lean"
        return [k for k, files in self.cited_in.items() if here in files]


# ---------------------------------------------------------------- one page


class ModulePage:
    """A module's page: reading doc-gen4's, and the declarations. A kind of page adds its heading
    and the right column."""

    # Whether a docstring's opening paper locator is shown apart: a locator needs a paper to name.
    locators = True

    def __init__(self, lib, page, site_root, sha):
        self.lib, self.page, self.sha = lib, page, sha
        self.docs = "../" * page.count("/")
        self.root = self.docs + site_root
        self.raw = (lib.doc / page).read_text(encoding="utf-8")
        self.module = re.search(r'const MODULE_NAME="([^"]+)"', self.raw).group(1)
        self.study, self.ns, self.key, self.entry = None, "", None, None

    # -- links and citations

    def href(self, url):
        """A link as doc-gen4 wrote it on this page, for the rebuilt page."""
        if url.startswith(("@@", "#")) or re.match(r"[a-z]+:", url):
            return url
        path, _, frag = dx.site_link(self.page, url).partition("#")
        frag = "#" + frag if frag else ""
        if path == self.page:
            return frag or "#top"
        if path.split("/")[0].removesuffix(".html") in self.lib.upstream:
            return MATHLIB_DOCS + path + frag
        # A docstring's path to a file, which doc-gen4 read from the site's root, starts in some
        # directory above this page or in the library's own.
        here = posixpath.dirname(self.page)
        for d in (*parents(here), "Linglib"):
            if posixpath.join(d, path) in self.lib.files:
                return posixpath.relpath(posixpath.join(d, path), here) + frag
        return None

    def to(self, page, anchor=""):
        """A site-relative page, and anchor, for the rebuilt page."""
        rel = posixpath.relpath(page, posixpath.dirname(self.page))
        return self.href(rel + ("#" + anchor if anchor else ""))

    def to_study(self, study):
        return self.to(f"Studies/{study}.html")

    def cite(self, m):
        key, label = m.group(2), m.group(3)
        b = self.lib.bib.get(key)
        if not b:
            return link(f"@@bibliography/#{key}", label, "cite")
        if self.study and b["study"] == self.study:
            return f'<span class="cite self">{esc(b["label"])}</span>'
        title = esc(text(b["title"]))
        if b["study"]:
            return (f'<a class="cite done" href="{esc(self.to_study(b["study"]))}" title="{title}">'
                    f'{esc(b["label"])}</a>')
        cls, tail = ("cite", "") if b["formalized"] else ("cite open", ", not yet formalized")
        return (f'<a class="{cls}" href="@@bibliography/#{esc(key)}" title="{title}{tail}">'
                f'{esc(b["label"])}</a>')

    def rewrite(self, h, short=False):
        """doc-gen4's HTML with links for the rebuilt page and author-year citations."""
        h = CITE_LINK.sub(self.cite, h)
        # A link to no page, such as a docstring's path to a file since moved, keeps its text.
        def anchor(m):
            return m.group(0) if self.href(html.unescape(m.group(1))) else m.group(2)
        h = re.sub(r'<a href="([^"]*)"[^>]*>(.*?)</a>', anchor, h, flags=re.S)
        h = re.sub(r'href="([^"]*)"',
                   lambda m: f'href="{esc(self.href(html.unescape(m.group(1))) or "#top")}"', h)
        h = h.replace('href="@@', f'href="{self.root}')
        if short:
            # One space between tokens: the nested `.fn` boxes wrap a long term at its own
            # structure, so the pretty-printer's line breaks for a fixed width are dropped. Names
            # print without the study's namespace, which the file opens.
            h = re.sub(r">([^<]*)<", lambda m: ">" + re.sub(r"\s+", " ", m.group(1)) + "<", h)
            if self.ns:
                h = re.sub(r'(?<![#/"\w.])' + re.escape(self.ns) + r"\.(?=\w)", "", h)
        return h

    # -- reading doc-gen4's page

    def section(self, sid="declarations", title="Declarations"):
        s = {"id": sid, "title": title, "prose": "", "decls": []}
        self.sections.append(s)
        return s

    def read(self):
        main = self.raw[self.raw.find("<main>") + len("<main>"):self.raw.rfind("</main>")]
        blocks, end = [], 0
        for m in dx.BLOCK.finditer(main):
            if m.start() < end:
                continue
            end = dx.div_end(main, m.start())
            blocks.append((m.group(1), m.group(2), main[m.start():end]))
        doc = blocks[0][2] if blocks and blocks[0][0] == "mod_doc" else ""
        h1 = re.search(r"<h1[^>]*>(.*?)</h1>", doc, re.S)
        self.h1 = text(re.sub(r'<a class="hover-link".*?</a>', "", h1.group(1))) if h1 else self.module
        doc = re.sub(r"<h1[^>]*>.*?</h1>", "", doc, count=1, flags=re.S)
        doc = re.sub(r' <a class="hover-link" href="#[^"]*">#</a>', "", doc)
        self.moddoc = self.rewrite(doc[doc.find(">") + 1:-len("</div>")]) if doc else ""
        self.moddoc = REFS.sub(self.ref_list, self.moddoc)
        self.sections, self.decls, cur = [], [], None
        for kind, did, block in blocks[1 if doc else 0:]:
            if kind == "mod_doc":
                head = HEADING.search(block)
                prose = re.sub(r"^<div[^>]*>|</div>$", "", block.strip())
                if head:
                    prose = prose[prose.find("</h", prose.find(head.group(2))):]
                    prose = prose[prose.find(">") + 1:]
                    cur = self.section(head.group(1), text(head.group(2)))
                elif cur is None:
                    cur = self.section()
                cur["prose"] += self.rewrite(prose).strip()
                continue
            cur = cur or self.section()
            d = self.read_decl(html.unescape(did), block, cur["id"])
            self.decls.append(d)
            cur["decls"].append(d)
        self.fold()

    def ref_list(self, m):
        """The References list: each entry's label, linked to its bibliography entry, its title,
        and a link to the study formalizing it, if another study does."""
        def item(li):
            study = re.search(r'href="(?:[./]*Studies/)?([A-Z]\w+)\.html"', li.group(1))
            key = re.search(r'bibliography/#([\w-]+)', li.group(1))
            k = key.group(1) if key else self.lib.study_key.get(study.group(1)) if study else self.key
            b = self.lib.bib.get(k)
            if not b:
                return li.group(0)
            out = (f'<li>{link(f"{self.root}bibliography/#{k}", esc(b["label"]))}'
                   f'<span class="rt">, {esc(text(b["title"]))}</span>')
            if b["study"] and b["study"] != self.study:
                out += f' {link(self.to_study(b["study"]), "formalized", "study")}'
            return out + "</li>"
        items = re.sub(r"<li>(.*?)</li>", item, m.group(2), flags=re.S)
        return f'{m.group(1)}<ul class="refs">{items}</ul>'

    def read_decl(self, did, block, section):
        kind = re.search(r'<span class="decl_kind">(\w+)</span>', block)
        src = re.search(r'<div class="gh_link"><a href="([^"]+?#L(\d+)-L(\d+))"', block)
        attrs = re.search(r'<div class="attributes">(.*?)</div>', block, re.S)
        header = DECL_NAME.sub("", dx.part(block, "decl_header"), count=1)
        after = block[block.index('<div class="decl_header">'):]
        after = after[dx.div_end(after, 0):]
        cut = min([i for i in (after.find("<details"), after.find('<ul class="constructors"'),
                               after.find('<ul class="structure_fields"')) if i >= 0] + [len(after)])
        doc = re.sub(r'<div class="attributes">.*?</div>', "", after[:cut], flags=re.S)
        doc = re.sub(r"(\s*</div>)+\s*$", "", doc).strip()
        eqs = re.findall(r'<li class="equation">(.*?)</li>', after, re.S)
        ctors, fields = dx.part(after, "constructors"), dx.part(after, "structure_fields")
        # doc-gen4 puts a structure's constructor anchor on its field list.
        fields_id = re.search(r'<ul class="structure_fields" id="([^"]+)"', after)
        refs = []
        for url in re.findall(r'href="([^"]+)"', header + "".join(eqs) + ctors + fields):
            ref = dx.site_link(self.page, html.unescape(url))
            if ref and "#" in ref and not ref.startswith("references.html"):
                if ref.split("#")[1] != did:
                    refs.append(ref)
        d = {"id": did, "name": did[len(self.ns) + 1:] if did.startswith(self.ns + ".") else did,
             "kind": kind.group(1) if kind else "", "src": src.group(1) if src else "",
             "l0": int(src.group(2)) if src else 0, "l1": int(src.group(3)) if src else 0,
             "attrs": text(attrs.group(1)) if attrs else "", "section": section,
             "parser": "ParserDescr" in text(header),
             "sig": self.rewrite(header, short=True), "doc": self.rewrite(doc),
             "sorried": "sorried" in block[:block.find(">")],
             "ctors": self.rewrite(ctors, short=True), "fields": self.rewrite(fields, short=True),
             "fields_id": fields_id.group(1) if fields_id else "",
             "eqs": [self.rewrite(e, short=True) for e in eqs], "refs": refs,
             "uses": sorted({r.split("#", 1)[1] for r in refs if r.split("#")[0] == self.page})}
        m = LOC.match(d["doc"]) if self.locators else None
        d["loc"] = ""
        if m:
            d["loc"], d["doc"] = text(m.group(1)), "<p>" + m.group(2).upper() + d["doc"][m.end():]
        return d

    def fold(self):
        """Instances and functions a `deriving` clause generated sit inside the type's source
        range: fold them into the type."""
        self.by_id = {d["id"]: d for d in self.decls}
        for d in self.decls:
            d["derives"], d["folded"] = [], False
        for t in self.decls:
            if t["kind"] not in ("inductive", "structure"):
                continue
            base = t["name"].split(".")[-1]
            for d in self.decls:
                if d is not t and t["l0"] <= d["l0"] <= t["l1"] and base in d["name"]:
                    d["folded"], d["into"] = True, t["id"]
                    m = re.match(r"inst(\w+?)" + re.escape(base) + r"$", d["name"].split(".")[-1])
                    if m:
                        t["derives"].append(m.group(1))
        self.shown = [d for d in self.decls if not d["folded"]]
        self.order = {d["id"]: i for i, d in enumerate(self.shown)}
        self.local_users = defaultdict(set)
        for d in self.shown:
            for u in d["uses"]:
                if u in self.by_id:
                    self.local_users[u].add(d["id"])

    # -- the declarations

    def headline(self, d):
        return d["kind"] == "theorem" and bool(text(d["doc"]))

    def built_from(self, d):
        """The file's own definitions that a declaration's statement or equations name."""
        ids = (u for u in d["uses"] if u in self.by_id and not self.by_id[u]["folded"]
               and self.by_id[u]["kind"] != "theorem")
        return sorted(ids, key=self.order.get)

    def elsewhere(self, d):
        """The other pages whose statements use a declaration."""
        users = self.lib.used_by.get(d["id"], ())
        return sorted({self.lib.decls[u]["page"] for u in users if u in self.lib.decls} - {self.page})

    def eq_block(self, d):
        if not d["eqs"]:
            return ""
        if any("did not get rendered" in text(e) for e in d["eqs"]):
            return (f'<p class="eq-note">The definition is too large to print here; '
                    f'{link(d["src"], "read it in the source")}.</p>')
        items = "".join(f"<li>{e}</li>" for e in d["eqs"])
        if sum(len(text(e)) for e in d["eqs"]) <= 420:
            return f'<ul class="eq">{items}</ul>'
        return (f'<details class="eq-more"><summary>Equations</summary>'
                f'<ul class="eq">{items}</ul></details>')

    def loc(self, d):
        """A declaration's paper locator, naming the paper on hover."""
        if not d["loc"]:
            return ""
        paper = self.lib.bib.get(self.key, {}).get("label", "the paper")
        return f'<span class="loc" title="{esc(d["loc"])} in {esc(paper)}">{esc(d["loc"])}</span>'

    def toggle(self, u):
        return (f'<button type="button" class="tg" data-open="{esc(u)}" aria-expanded="false">'
                f'{esc(self.by_id[u]["name"])}{self.loc(self.by_id[u])}</button>')

    def item_name(self, c, source=None):
        """An item by its label, after its source's unless that is `source`."""
        if c["source"] == source:
            return esc(c["label"])
        b = self.lib.bib.get(c["source"])
        label = b["label"] if b else c["source"]
        paper = link(f'{self.root}bibliography/#{c["source"]}', esc(label))
        return f'{paper}, {esc(c["label"])}'

    def checks(self, d):
        """For each item the declaration states, whether a person has checked it."""
        out = ""
        for c in self.lib.items_of.get(d["id"], ()):
            ck = c["check"]
            if c["status"] not in ("checked", "relies", "stale") or not ck:
                continue
            against = self.item_name(c)
            verb = "Checked against"
            if c["relation"] in RELATION:
                against += (f' (<span class="rel" title="{esc(c["notes"])}">'
                            f'{RELATION[c["relation"]]}</span>)')
            elif c["relation"] == "counterexample":
                verb = f'Checked as <span class="rel" title="{esc(c["notes"])}">a counterexample to</span>'
            day = datetime.date.fromisoformat(ck["date"])
            who = (esc(ck["by"]) if ck["via"]
                   else link("https://github.com/" + ck["by"], esc(ck["by"])))
            by = f'by {who} on {day.day} {day:%B} {day.year}'
            if c["status"] == "stale":
                line = (f'{verb} {against} {by}; its statement has changed since '
                        '(<code>checks.py diff</code> shows how).')
            elif c["status"] == "relies":
                rest = [self.lib.items[r] for r in c["blocking"] if r in self.lib.items]
                names = ", ".join(self.item_name(r, c["source"]) for r in rest)
                line = (f'{verb} {against} {by}, relying on {names}, which '
                        f'{"is" if len(rest) == 1 else "are"} not.')
            else:
                line = f'{verb} {against} {by}.'
            out += f'<p class="checked">{line}</p>'
        return out

    def extras(self, d):
        """Below a declaration: whether it is checked against its source, what `deriving` made of
        it, its instances, and who uses it."""
        out = self.checks(d)
        folded = "".join(f'<span id="{esc(x["id"])}"></span>' for x in self.decls
                         if x["folded"] and x.get("into") == d["id"])
        if d["derives"] or folded:
            out += (f'<p class="derives">{folded}'
                    + (f'Derives {", ".join(d["derives"])}.' if d["derives"] else "") + "</p>")
        feeds = self.built_from(d)
        if feeds:
            out += (f'<p class="bf">Built from {", ".join(self.toggle(u) for u in feeds)}</p>'
                    '<div class="bf-area"></div>')
        data = self.lib.decl_data
        inst = [i for i in self.lib.instances_for.get(d["id"], ()) if i in data
                and data[i]["docLink"].removeprefix("./").split("#")[0] != self.page]
        if inst:
            out += '<p class="used">Instances ' + and_more([
                link(self.to(*data[i]["docLink"].removeprefix("./").split("#", 1)), esc(i))
                for i in inst]) + "</p>"
        mine = sorted(self.local_users.get(d["id"], ()), key=lambda x: self.by_id[x]["l0"])
        if mine:
            out += '<p class="used">Used by ' + ", ".join(
                link("#" + x, esc(self.by_id[x]["name"])) for x in mine) + "</p>"
        far = self.elsewhere(d)
        if far:
            out += '<p class="used">Used in ' + and_more([
                link(self.to(p), esc(page_name(p))) for p in far]) + "</p>"
        return out

    def card(self, d):
        head = self.headline(d)
        cls = {"theorem": "thm", "instance": "inst"}.get(d["kind"], "def")
        cls += (" head" if head else " row") + (" sorried" if d["sorried"] else "")
        attrs = f'<span class="attr">{esc(d["attrs"])}</span> ' if d["attrs"] else ""
        lines = f'L{d["l0"]}' + (f'–{d["l1"]}' if d["l1"] != d["l0"] else "")
        sig = d["sig"].strip()
        bare = sig.startswith(BARE)
        if bare:
            sig = '<span class="decl_args">:</span> ' + sig[len(BARE):].lstrip()
        ctors = f'<ul class="ctors">{d["ctors"]}</ul>' if d["ctors"] else ""
        fid = f' id="{esc(d["fields_id"])}"' if d["fields_id"] else ""
        fields = f'<ul class="fields"{fid}>{d["fields"]}</ul>' if d["fields"] else ""
        doc = f'<div class="ddoc">{d["doc"]}</div>\n' if text(d["doc"]) else ""
        lede = ""
        if head and doc:
            lede, doc = f'<div class="lede">{d["doc"]}</div>\n', ""
        loc = self.loc(d)
        src = ""
        if d["src"]:
            src = f'<a class="src" href="{esc(d["src"])}" title="Source, lines {lines}">{lines}</a>'
        uses = " ".join(u for u in d["uses"] if u in self.by_id and not self.by_id[u]["folded"])
        users = " ".join(sorted(self.local_users.get(d["id"], ())))
        data = (f'data-order="{self.order[d["id"]]}" data-sec="{esc(d["section"])}" '
                f'data-uses="{esc(uses)}" data-used-by="{esc(users)}"')
        rest = (f'<div class="sig{" bare" if bare else ""}">{sig}</div>\n'
                f'{ctors}{fields}{self.eq_block(d)}{self.extras(d)}')
        kw = KW.get(d["kind"], d["kind"])
        if head:
            return (f'<article class="decl {cls}" id="{esc(d["id"])}" {data}>\n{lede}'
                    f'<header class="dh">{attrs}<span class="kw">{kw}</span> '
                    f'{link("#" + d["id"], esc(d["name"]), "nm")}{loc}{src}</header>\n'
                    f'{doc}{rest}</article>')
        return (f'<article class="decl {cls}" id="{esc(d["id"])}" {data}>\n'
                f'<header class="dh"><button class="opener" type="button" aria-expanded="false">{attrs}'
                f'<span class="kw">{kw}</span> <span class="nm">{esc(d["name"])}</span>{loc}'
                f'</button>{src}</header>\n<div class="body" hidden>{doc}{rest}</div></article>')

    def body(self):
        out = []
        for s in self.sections:
            mine = [d for d in s["decls"] if not d["folded"]]
            if not mine and not s["prose"]:
                continue
            out.append(f'<section class="dsec" id="sec-{esc(s["id"])}" data-sec="{esc(s["id"])}" '
                       f'aria-labelledby="{esc(s["id"])}"><h2 id="{esc(s["id"])}">{esc(s["title"])}</h2>'
                       + (f'<div class="sprose">{s["prose"]}</div>' if s["prose"] else "")
                       + "\n".join(self.card(d) for d in mine) + "</section>")
        return "\n".join(out)

    def index(self):
        groups = []
        for s in self.sections:
            items = []
            for d in s["decls"]:
                if d["folded"] or d["parser"]:
                    continue
                cls = "thm" if d["kind"] == "theorem" else "def"
                cls = ("head" if cls == "thm" else "def head") if self.headline(d) else cls
                # The column cuts a long name short.
                full = f' title="{esc(d["name"])}"' if len(d["name"]) > 24 else ""
                items.append(f'<li class="{cls}"><a href="#{esc(d["id"])}" data-for="{esc(d["id"])}"{full}>'
                             f'{esc(d["name"])}</a></li>')
            if items:
                groups.append(f'<li class="grp">{link("#" + s["id"], esc(s["title"]), "gh")}'
                              f'<ul>{"".join(items)}</ul></li>')
        return f'<ul class="groups map" id="map">{"".join(groups)}</ul>'

    def preview(self):
        out = {}
        for d in self.shown:
            first = re.split(r"(?<=[.!?])\s", text(d["doc"]), maxsplit=1)[0] if text(d["doc"]) else ""
            ty = re.search(r'<div class="decl_type">(.*)</div>', d["sig"], re.S)
            stmt = text(ty.group(1)) if ty else text(d["sig"])
            out[d["id"]] = {"k": d["kind"], "n": d["name"], "d": first, "l": d["loc"],
                            "s": stmt if len(stmt) <= 240 else stmt[:237] + "…"}
            if self.headline(d):
                out[d["id"]]["c"] = text(d["doc"])
        return out

    # -- where the file sits

    def short(self, node, anchor):
        """A name without its framework's, data module's or this file's namespace."""
        dotted = node[1].replace("/", ".")
        for pre in (dotted, dotted.rsplit(".", 1)[0], self.ns, dotted.split(".")[0]):
            if pre and anchor.startswith(pre + "."):
                return anchor[len(pre) + 1:]
        return anchor

    def named(self):
        """The declarations of other pages this file's statements name: node -> {name: page}."""
        used = defaultdict(dict)
        for d in self.decls:
            for ref in d["refs"]:
                page, anchor = ref.split("#", 1)
                node = self.node(page)
                if node and page != self.page and node[0] in "tfdc":
                    used[node].setdefault(anchor, page)
        return used

    def imports(self):
        listed = self.raw[self.raw.find('<div class="imports">'):self.raw.find("Imported by")]
        return re.findall(r'<li><a href="[^"]*">([^<]+)</a></li>', listed)

    def module_list(self, summary, modules):
        hrefs = {m: self.to(m.replace(".", "/") + ".html") for m in modules}
        rows = "".join(f'<li>{link(hrefs[m], esc(m)) if hrefs[m] else esc(m)}</li>' for m in modules)
        return f"<details><summary>{esc(summary)}</summary><ul>{rows}</ul></details>"

    def study_item(self, nodes, s, note=""):
        """A study's row, adding its node to the graph. `note` is HTML."""
        _, e = self.lib.entry(s)
        nodes.setdefault(s, {"k": "s", "y": year_of(s), "l": e["label"] if e else s,
                             "d": text(e["title"]) if e else s, "h": self.to_study(s)})
        return (f'<li class="s" data-node="{esc(s)}">'
                f'{link(self.to_study(s), esc(nodes[s]["l"]), "nd")}{note}</li>')

    def framework(self, nodes, node, page, desc=None):
        """A theory or fragment node of the graph, whose page is `page`."""
        if not desc:
            m, s = len(self.lib.node_pages[node]), len(self.lib.users[node])
            desc = f"{m} module{'' if m == 1 else 's'} · {s} {'study' if s == 1 else 'studies'}"
        nodes[node_id(node)] = {"k": node[0], "l": node_label(node), "h": self.to(page), "d": desc}

    @staticmethod
    def graph_data(nodes, edges, focus):
        for n in nodes.values():
            if n.get("y") is None:
                n.pop("y", None)
        return {"nodes": nodes, "edges": list(map(list, dict.fromkeys(map(tuple, edges)))),
                "focus": focus}

    # -- the page

    def render(self, template):
        self.read()
        rail, graph = self.rail()
        title, cite, crumbs = self.heading()
        out = site_shell.render(template, self.root, "Docs", self.sha)
        prose = self.moddoc + "".join(s["prose"] for s in self.sections)
        prose += "".join(d["doc"] for d in self.shown)
        tex = TEX.search(re.sub(r"<code>.*?</code>", "", prose, flags=re.S))
        subst = {"<!--MATH-->": MATH if tex else "", "<!--TITLE_TEXT-->": esc(text(title)),
                 "<!--DESCRIPTION-->": esc(text(title)), "<!--ASSETS-->": self.docs,
                 "<!--TITLE-->": title, "<!--CITE-->": cite, "<!--CRUMBS-->": crumbs,
                 "<!--MODDOC-->": self.moddoc,
                 "<!--NDECL-->": str(sum(not d["parser"] for d in self.shown)),
                 "<!--INDEX-->": self.index(), "<!--DECLS-->": self.body(), "<!--RAIL-->": rail,
                 "/*GRAPH*/": json.dumps(graph, ensure_ascii=False).replace("</", "<\\/"),
                 "/*PREVIEW*/": json.dumps(self.preview(), ensure_ascii=False).replace("</", "<\\/")}
        for k, v in subst.items():
            assert out.count(k) >= 1, k
            out = out.replace(k, v)
        return out


class StudyPage(ModulePage):
    def __init__(self, lib, page, site_root, sha):
        super().__init__(lib, page, site_root, sha)
        self.study = self.ns = node_of(page)[1]
        self.key, self.entry = lib.entry(self.study)

    node = staticmethod(node_of)

    def heading(self):
        e = self.entry
        title = e["title"] if e else esc(self.h1)
        cite = ""
        if e:
            venue = f' {e["venue"]}' if e["venue"] else ""
            cite = f'<p class="cite-line">{esc(e["authors"])} ({esc(e["year"])}).{venue}</p>'
        source = f'{REPO}/blob/{self.sha or "main"}/{self.module.replace(".", "/")}.lean'
        links = [link(source, "Source")]
        if self.key:
            links.append(link(f"{self.root}bibliography/#{self.key}", "Bibliography"))
            paper = f'https://doi.org/{e["doi"]}' if e["doi"] else e["url"]
            if paper:
                links.append(link(paper, "Paper"))
        cite += f'\n<p class="links">{" ".join(links)}</p>'
        crumbs = (f'{link(self.docs, "Docs")} / {link(self.docs + "#studies", "Studies")} / '
                  f'{esc(self.module)}')
        return title, cite, crumbs

    def rail(self):
        lib, me = self.lib, self.study
        used = self.named()
        imports = self.imports()
        imported = {node_of(m.replace(".", "/") + ".html") for m in imports} - {None}
        idle = sorted(n for n in imported if n[0] in "tf" and n not in used and lib.node_pages[n])
        label = self.entry["label"] if self.entry else me
        nodes = {me: {"k": "s", "y": year_of(me), "l": label, "d": "This page", "h": "#top"}}
        edges = []
        parts = ['<h2>Connections</h2>\n<div class="graph" id="graph"><svg id="g" viewBox="0 0 300 206" '
                 'role="img" aria-label="This study among the theory and languages its statements use, '
                 'the studies on the same theory by year, and the papers it cites"></svg>'
                 '<div class="tip" id="tip" role="tooltip"></div></div>']

        def framework(node, desc=None):
            first = min(used[node].values()) if node in used else min(lib.node_pages[node])
            self.framework(nodes, node, first, desc)
            return first

        rank = {"t": 0, "f": 1, "d": 2}
        items = []
        for node in sorted(used, key=lambda n: (rank[n[0]], -len(used[n]), n[1])):
            names = [link(self.to(p, a), esc(self.short(node, a)))
                     for a, p in sorted(used[node].items())]
            first = framework(node) if node[0] in "tf" else min(used[node].values())
            if node[0] in "tf":
                edges.append([me, node_id(node), "use"])
            tag = f' data-node="{esc(node_id(node))}"' if node[0] in "tf" else ""
            head = link(self.to(first), esc(node_label(node)), "nd")
            items.append(f'<li class="{node[0]}"{tag}>{head} '
                         f'<span class="names">{and_more(names, 4)}</span></li>')
        if items:
            parts.append("<h3>Builds on</h3>\n<ul>" + "".join(items) + "</ul>")
        if idle:
            for n in idle:
                framework(n, "imported, named in no signature here")
                edges.append([me, node_id(n), "weak"])
            parts.append('<p class="quiet">Imported but named in no signature: ' + ", ".join(
                f'<a href="{esc(nodes[node_id(n)]["h"])}" data-node="{esc(node_id(n))}">'
                f'{esc(node_label(n))}</a>' for n in idle) + ".</p>")

        def study_item(s, why=""):
            note = f' <span class="why">{esc(why)}</span>' if why else ""
            return self.study_item(nodes, s, note)

        def by_year(s):
            return (year_of(s) or 0, s)

        def about(title, theorems, here):
            """Papers, the latest first, each with the sentence of the first of its `theorems`,
            which are on this page if `here` and otherwise on that paper's."""
            shown = sorted(theorems, key=lambda s: (-(year_of(s) or 0), s))
            rows = []
            for s in shown[:SHOWN]:
                t, more = theorems[s][0], len(theorems[s]) - 1
                href = f'#{t["id"]}' if here else self.to(f"Studies/{s}.html", t["id"])
                rows.append(self.study_item(nodes, s, (
                    f'<a class="said" href="{esc(href)}" title="{esc(t["doc"])}">{esc(t["doc"])}</a>'
                    + (f' <span class="why">and {more} more</span>' if more else ""))))
            rest = f'<p class="quiet">and {len(shown) - SHOWN} more</p>' if len(shown) > SHOWN else ""
            parts.append(f"<h3>{title}</h3>\n<ul>" + "".join(rows) + "</ul>" + rest)
            return shown[:SHOWN]

        if lib.about[me]:
            edges += [[me, s, "cite"] for s in
                      about("Theorems here about other papers", lib.about[me], True)]
        if lib.about_me[me]:
            edges += [[s, me, "cite"] for s in
                      about("Theorems elsewhere about this paper", lib.about_me[me], False)]

        mine = lib.uses.get(me, set())
        score = defaultdict(float)
        for n in mine:
            if n[0] == "t":
                for s in lib.users[n] - {me}:
                    score[s] += lib.idf(n)
        peers = sorted(sorted(score, key=lambda s: (-score[s], s))[:SHOWN], key=by_year)
        if peers:
            rows = []
            for s in peers:
                shared = sorted((n for n in mine & lib.uses[s] if n[0] == "t"),
                                key=lib.idf, reverse=True)
                rows.append(study_item(s, ", ".join(n[1].split(".")[-1] for n in shared[:2])))
                edges += [[s, node_id(n), "use"] for n in shared if node_id(n) in nodes]
            parts.append("<h3>Other papers on the same theory</h3>\n<ul>" + "".join(rows) + "</ul>")
        keys = lib.cites(me)
        # A study's file may cite later work; the paper does not.
        cites = sorted(s for s in {lib.bib[k]["study"] for k in keys} - {None, me}
                       if (year_of(s) or 0) <= (year_of(me) or 9999))
        cites = sorted(cites, key=by_year)[:8]
        if cites:
            parts.append("<h3>Cites</h3>\n<ul>" + "".join(map(study_item, cites)) + "</ul>")
            edges += [[me, s, "cite"] for s in cites]
        if self.key:
            files = lib.cited_in.get(self.key, ())
            citing = {f.split("/")[1].removesuffix(".lean") for f in files if f.startswith("Studies/")}
            citing = sorted((s for s in (citing - {me}) & lib.studies
                             if (year_of(s) or 9999) >= (year_of(me) or 0)), key=by_year)[:8]
            if citing:
                parts.append("<h3>Cited by</h3>\n<ul>" + "".join(map(study_item, citing)) + "</ul>")
                edges += [[s, me, "cite"] for s in citing]
        frontier = sorted((k for k in keys if not lib.bib[k]["study"] and not lib.bib[k]["formalized"]
                           and k != self.key), key=lambda k: (lib.bib[k]["year"], k))
        if frontier:
            rows = []
            for k in frontier[:8]:
                b, y = lib.bib[k], re.match(r"\d{4}", lib.bib[k]["year"])
                href, title = f"{self.root}bibliography/#{k}", text(b["title"])
                nodes[f"g-{k}"] = {"k": "g", "y": int(y.group(0)) if y else None, "l": b["label"],
                                   "d": f"{title} · not yet formalized", "h": href}
                edges.append([me, f"g-{k}", "cite"])
                rows.append(f'<li class="g" data-node="g-{esc(k)}">{link(href, esc(b["label"]), "nd")} '
                            f'<span class="why">{esc(title)}</span></li>')
            more = f'<p class="quiet">and {len(frontier) - 8} more</p>' if len(frontier) > 8 else ""
            parts.append("<h3>Cites, not yet formalized</h3>\n<ul>" + "".join(rows) + "</ul>" + more)
        if imports:
            parts.append(self.module_list(f"All {len(imports)} imports", imports))
        return "\n".join(parts), self.graph_data(nodes, edges, me)


    def draws(self):
        """The theorems a random visit may open this page at."""
        named = {html.unescape(u) for u in re.findall(r'href="#([^"]+)"', self.moddoc)}
        about = {b["id"] for bs in self.lib.about[self.study].values() for b in bs}
        path = ROOT / (self.module.replace(".", "/") + ".lean")
        lines = path.read_text(encoding="utf-8").split("\n") if path.exists() else []
        return [d["id"] for d in self.shown
                if d["kind"] == "theorem" and d["id"] in named | about and not d["sorried"]
                and (say := text(d["doc"])) and not NOT_ALONE.search(say) and d["l1"] <= len(lines)
                and not EVALUATED.search("\n".join(lines[d["l0"] - 1:d["l1"]]))]


class TheoryPage(ModulePage):
    locators = False
    node = staticmethod(file_node)

    def __init__(self, lib, page, site_root, sha):
        super().__init__(lib, page, site_root, sha)
        self.me = file_node(page)
        self.ns = namespace([b["id"] for b in lib.modules[page]["blocks"] if b["type"] == "decl"])
        self.headlines = set()

    def read(self):
        super().read()
        doc = re.sub(rf'<h2 [^>]*>(?:{NOTES})\b.*?(?=<h2 |$)', "", self.moddoc, flags=re.S)
        linked = {html.unescape(u) for u in re.findall(r'href="#([^"]+)"', doc)}
        self.headlines = linked & set(self.order)

    def headline(self, d):
        return d["id"] in self.headlines if self.headlines else super().headline(d)

    def heading(self):
        path = self.page.removesuffix(".html").split("/")[1:]
        crumbs = [link(self.docs, "Docs")]
        for i, part in enumerate(path[:-1]):
            crumbs.append(link(f'{self.docs}#{"/".join(path[:i + 1])}', esc(part)))
        crumbs.append(esc(path[-1]))
        line = f"import {self.module}" + (f" · namespace {self.ns}" if self.ns else "")
        source = f'{REPO}/blob/{self.sha or "main"}/{self.module.replace(".", "/")}.lean'
        cite = f'<p class="modline">{esc(line)}</p>\n<p class="links">{link(source, "Source")}</p>'
        return esc(self.h1), cite, " / ".join(crumbs)

    @staticmethod
    def listing(title, rows):
        """Rows under a heading, the first few shown and the others folded."""
        if not rows:
            return ""
        out = f"<h3>{esc(title)}</h3>\n<ul>{''.join(rows[:FILES_SHOWN])}</ul>"
        if len(rows) > FILES_SHOWN:
            out += (f'<details class="more"><summary>and {len(rows) - FILES_SHOWN} more</summary>'
                    f'<ul>{"".join(rows[FILES_SHOWN:])}</ul></details>')
        return out

    def own_names(self, anchors, shown=4):
        """This file's declarations another file names, linked to where they are on this page."""
        names = []
        for a in sorted(anchors):
            d = self.by_id.get(a)
            short = d["name"] if d else a.removeprefix(self.ns + ".")
            names.append(link("#" + a, esc(short)))
        return f'<span class="names">{and_more(names, shown)}</span>'

    def rail(self):
        lib, me = self.lib, node_id(self.me)
        nodes = {me: {"k": "t", "b": "focus", "l": node_label(self.me), "d": "This page", "h": "#top"}}
        edges, pages_of = [], {me: {self.page}}
        parts = ['<h2>Connections</h2>\n<div class="graph" id="graph"><svg id="g" viewBox="0 0 300 206" '
                 'role="img" aria-label="This file below the theory it builds on, above the theory '
                 'built on it, the studies using it by year and the fragments using it"></svg>'
                 '<div class="tip" id="tip" role="tooltip"></div></div>']

        def file_item(node, page, note, in_graph, label=None):
            tag = f' data-node="{esc(node_id(node))}"' if in_graph else ""
            head = link(self.to(page), esc(label or node_label(node)), "nd")
            return f'<li class="{node[0]}"{tag}>{head} {note}</li>'

        def add_file(node, page, band, desc=None):
            self.framework(nodes, node, page, desc or lib.title(page))
            nodes[node_id(node)]["b"] = band
            pages_of[node_id(node)] = {page}

        # What it builds on: the theory above it in the graph, and Core and data in the list alone.
        used = self.named()
        rank = {"t": 0, "f": 1, "c": 2, "d": 3}
        order = sorted(used, key=lambda n: (rank[n[0]], -len(used[n]), n[1]))
        above = [n for n in order if n[0] == "t"][:FILES_SHOWN]
        rows = []
        for node in order:
            first = min(used[node].values())
            if node in above:
                add_file(node, first, "up")
                edges.append([me, node_id(node), "use"])
            names = [link(self.to(p, a), esc(self.short(node, a)))
                     for a, p in sorted(used[node].items())]
            rows.append(file_item(node, first, f'<span class="names">{and_more(names, 4)}</span>',
                                  node in above))
        parts.append(self.listing("Builds on", rows))
        imports = self.imports()
        idle = {}
        for m in imports:
            page = m.replace(".", "/") + ".html"
            node = file_node(page)
            if node and node[0] == "t" and node not in used and page in lib.modules:
                idle[node] = page
        if idle:
            shown = sorted(idle)[:max(0, FILES_SHOWN - len(above))]
            for n in shown:
                add_file(n, idle[n], "up", "imported, named in no signature here")
                edges.append([me, node_id(n), "weak"])
            parts.append('<p class="quiet">Imported but named in no signature: ' + ", ".join(
                f'<a href="{esc(self.to(idle[n]))}"'
                + (f' data-node="{esc(node_id(n))}"' if n in shown else "")
                + f'>{esc(node_label(n))}</a>' for n in sorted(idle)) + ".</p>")

        # What uses it: the theory, then the studies by year, then the languages.
        files, studies, langs = {}, {}, defaultdict(lambda: (set(), set()))
        for page, anchors in lib.named_by.get(self.page, {}).items():
            node = file_node(page)
            if node and node[0] == "t":
                files[node] = (page, anchors)
            elif node and node[0] == "s":
                studies[node[1]] = anchors
            elif node and node[0] == "f":
                langs[node][0].add(page)
                langs[node][1].update(anchors)

        order = sorted(files, key=lambda n: (-len(files[n][1]), n[1]))
        below = order[:FILES_SHOWN]
        rows = []
        for node in order:
            page, anchors = files[node]
            if node in below:
                add_file(node, page, "down")
                edges.append([node_id(node), me, "use"])
            rows.append(file_item(node, page, self.own_names(anchors), node in below))
        parts.append(self.listing("Theory built on it", rows))

        def by_year(s):
            return (year_of(s) or 0, s)

        ranked = sorted(studies, key=lambda s: (-len(studies[s]), by_year(s)))
        listed = (sorted(ranked[:FILES_SHOWN], key=by_year)
                  + sorted(ranked[FILES_SHOWN:], key=by_year))
        rows = [self.study_item(nodes, s, " " + self.own_names(studies[s])) for s in listed]
        for s in ranked[STUDIES_SHOWN:]:
            del nodes[s]
        for s in ranked[:STUDIES_SHOWN]:
            pages_of[s] = {f"Studies/{s}.html"}
            edges.append([s, me, "use"])
        parts.append(self.listing("Studies using it", rows))

        order = sorted(langs, key=lambda n: (-len(langs[n][1]), n[1]))
        rows = []
        for node in order:
            pages, anchors = langs[node]
            first = min(pages)
            if node in order[:FILES_SHOWN]:
                self.framework(nodes, node, first)
                pages_of[node_id(node)] = pages
                edges.append([node_id(node), me, "use"])
            rows.append(file_item(node, first, self.own_names(anchors, 2), node in order[:FILES_SHOWN]))
        parts.append(self.listing("Fragments using it", rows))

        # Among its neighbors, who names whom, which hovering a neighbor shows.
        users = [n for n in pages_of if n != me and nodes[n].get("b") != "up"]
        targets = [n for n in pages_of if n != me and nodes[n]["k"] == "t"]
        for a in users:
            for b in targets:
                named = (q in lib.named_by.get(p, ()) for p in pages_of[b] for q in pages_of[a])
                if a != b and any(named):
                    edges.append([a, b, "near"])

        # The rest of its directory.
        here = posixpath.dirname(self.page)
        siblings = [p for p in lib.in_dir[here] if p != self.page]
        rows = []
        for p in siblings:
            node = file_node(p)
            rows.append(file_item(node, p, f'<span class="why">{esc(lib.title(p))}</span>',
                                  node_id(node) in nodes, p.removesuffix(".html").split("/")[-1]))
        parts.append(self.listing("Also in " + " / ".join(here.split("/")[1:]), rows))

        importers = lib.imported_by.get(self.module, [])
        if imports:
            parts.append(self.module_list(f"All {len(imports)} imports", imports))
        if importers:
            parts.append(self.module_list(f"All {len(importers)} importers", sorted(importers)))
        return "\n".join(p for p in parts if p), self.graph_data(nodes, edges, me)


# ---------------------------------------------------------------- the landing page


def file_tree(lib, pages, base):
    """`pages`, all below the directory `base`: its subdirectories fold, then its files."""
    dirs, rows = defaultdict(list), []
    for page in sorted(pages):
        rest = page[len(base) + 1:]
        if "/" in rest:
            dirs[rest.split("/")[0]].append(page)
        else:
            name, title = rest.removesuffix(".html"), lib.title(page)
            note = f' <span class="ti">{esc(title)}</span>' if title != name else ""
            rows.append(f'<li>{link(page, esc(name), "f")}{note}</li>')
    folds = [fold(f"{base}/{d}".removeprefix("Linglib/"), d, file_tree(lib, dirs[d], f"{base}/{d}"))
             for d in sorted(dirs)]
    return "".join(folds) + (f'<ul>{"".join(rows)}</ul>' if rows else "")


def fold(fid, summary, body):
    return f'<details id="{esc(fid)}"><summary>{esc(summary)}</summary>{body}</details>'


def study_tree(lib, pages):
    """The studies by decade, the latest first, each by year."""
    decades = defaultdict(list)
    for page in pages:
        s = node_of(page)[1]
        decades[(year_of(s) or 0) // 10 * 10].append((year_of(s) or 0, s, page))
    out = []
    for decade in sorted(decades, reverse=True):
        rows = []
        for _, s, page in sorted(decades[decade]):
            _, e = lib.entry(s)
            title = e["title"] if e else esc(lib.title(page))
            rows.append(f'<li>{link(page, esc(e["label"] if e else s))} <span class="ti">{title}</span></li>')
        out.append(fold(f"studies-{decade}s", f"{decade}s", f'<ul>{"".join(rows)}</ul>'))
    return "".join(out)


def landing(lib, template, site_root, sha):
    """The landing page of the docs: the search, and every module by the layer it belongs to."""
    def tree(top):
        return file_tree(lib, [p for p in lib.modules if p.startswith(top + "/")], top)

    areas = "".join(fold(a, a, tree(f"Linglib/{a}")) for a in THEORY)
    general = "".join(f'<li>{link(p, esc(label))}</li>' for p, label in
                      (("foundational_types.html", "Foundational types"), ("tactics.html", "Tactics"),
                       ("references.html", "References")))
    studies = study_tree(lib, [p for p in lib.modules if p.startswith("Studies/")])
    sections = [("theory", "t", "Theory", areas), ("studies", "s", "Studies", studies),
                ("fragments", "f", "Fragments", tree("Linglib/Fragments")),
                ("data", "d", "Data", tree("Linglib/Data")), ("core", "d", "Core", tree("Linglib/Core")),
                ("other", "d", "Other", f'<ul>{general}</ul>')]
    tree = "\n".join(f'<section id="{sid}"><h2 class="{cls}">{esc(title)}</h2>{body}</section>'
                     for sid, cls, title, body in sections)
    return site_shell.render(template, site_root, "Docs", sha).replace("<!--TREE-->", tree)


# ---------------------------------------------------------------- the site


def check(lib, out, written):
    """Declarations doc-gen4 places on a rebuilt page that the page has no anchor for."""
    ids = {p: set(re.findall(r'\bid="([^"]+)"', (out / p).read_text(encoding="utf-8"))) for p in written}
    lost = []
    for d in lib.decl_data.values():
        page, _, frag = d["docLink"].removeprefix("./").partition("#")
        if page in ids and esc(frag) not in ids[page] and frag not in ids[page]:
            lost.append((page, frag))
    return lost


def dead_links(out, written):
    """Relative links on the rebuilt pages, the graph's too, that land on no file of the docs."""
    dead, seen = [], {}
    for page in written:
        raw = (out / page).read_text(encoding="utf-8")
        for a, b in set(re.findall(r'(?:href|src)="([^"#]+)|"h": "([^"#]+)', raw)):
            url = html.unescape(a or b)
            target = posixpath.normpath(posixpath.join(posixpath.dirname(page), url))
            if re.match(r"[a-z]+:", url) or target.startswith("../"):
                continue
            if target not in seen:
                seen[target] = (out / target).is_file() or (out / target / "index.html").is_file()
            if not seen[target]:
                dead.append((page, url))
    return dead


def is_theory(page):
    p = page.split("/")
    return p[0] == "Linglib" and len(p) >= 3 and p[1] in THEORY


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--doc", type=Path, default=Path(".lake/build/doc"), help="doc-gen4's output")
    ap.add_argument("--out", type=Path, required=True, help="the docs directory, for the rebuilt pages")
    ap.add_argument("--root", default="../", help="the site's root, relative to the docs directory")
    ap.add_argument("--only", nargs="*", help="rebuild these studies, modules and modules below these")
    ap.add_argument("--check", action="store_true", help="confirm declarations keep anchors, links land")
    ap.add_argument("--redirect", type=Path, help="also leave pages here that forward to the study pages")
    ap.add_argument("--checks", type=Path, help="`checks.py status --json`, the human checks")
    args = ap.parse_args()

    # The pages are read from `--doc`, whose study pages must still be doc-gen4's: a rebuilt page is
    # no module page, so reading a tree of them would quietly lose the studies.
    if args.doc.resolve() == args.out.resolve():
        sys.exit("--out must not be --doc: the pages are read from the one and written to the other")
    checks = json.loads(args.checks.read_text(encoding="utf-8")) if args.checks else None
    lib = Library(args.doc, checks)
    sha = site_shell.git_commit()
    studies = sorted(p for p in lib.modules if p.startswith("Studies/"))
    theory = sorted(filter(is_theory, lib.modules))
    if not studies or not theory:
        sys.exit(f"{args.doc} has {len(studies)} study and {len(theory)} theory pages of doc-gen4's")
    template = (PAGE / "template.html").read_text(encoding="utf-8")
    args.out.mkdir(parents=True, exist_ok=True)
    for asset in ("docs.css", "docs.js"):
        shutil.copy(PAGE / asset, args.out / asset)
    home = (PAGE / "index.html").read_text(encoding="utf-8")
    (args.out / "index.html").write_text(landing(lib, home, args.root, sha), encoding="utf-8")
    if args.only:
        def chosen(page):
            mod = page.removesuffix(".html").replace("/", ".")
            return any(mod in (o, f"Studies.{o}") or mod.startswith(o + ".") for o in args.only)
        studies, theory = list(filter(chosen, studies)), list(filter(chosen, theory))
    pool = {}
    for cls, pages in ((StudyPage, studies), (TheoryPage, theory)):
        for page in pages:
            dest = args.out / page
            dest.parent.mkdir(parents=True, exist_ok=True)
            built = cls(lib, page, args.root, sha)
            dest.write_text(built.render(template), encoding="utf-8")
            if cls is StudyPage and (draws := built.draws()):
                pool[built.study] = draws
    (args.out / "random.html").write_text(
        (PAGE / "random.html").read_text(encoding="utf-8").replace(
            "/*POOL*/", json.dumps(pool, ensure_ascii=False).replace("</", "<\\/")), encoding="utf-8")
    print(f"{sum(map(len, pool.values()))} theorems of {len(pool)} studies in random.html")
    print(f"wrote the landing page, {len(studies)} study and {len(theory)} theory pages to {args.out}")
    (args.out / "Studies").mkdir(parents=True, exist_ok=True)
    (args.out / "Studies" / "index.html").write_text(
        REDIRECT.format(href="../#studies", js=json.dumps("../#studies")), encoding="utf-8")
    if args.redirect:
        for page in studies:
            stub = args.redirect / page
            stub.parent.mkdir(parents=True, exist_ok=True)
            href = posixpath.relpath((args.out / page).resolve().as_posix(),
                                     stub.parent.resolve().as_posix())
            stub.write_text(REDIRECT.format(href=esc(href), js=json.dumps(href)), encoding="utf-8")
        print(f"wrote {len(studies)} forwarding pages to {args.redirect}")
    if args.check:
        lost = check(lib, args.out, studies + theory)
        for page, frag in lost:
            print(f"{page}: no anchor for {frag}")
        print(f"{len(lost)} declarations without an anchor")
        dead = dead_links(args.out, ["index.html", *studies, *theory])
        for page, url in dead:
            print(f"{page}: no page at {url}")
        print(f"{len(dead)} links to no page")
        sys.exit(1 if lost or dead else 0)


if __name__ == "__main__":
    main()
