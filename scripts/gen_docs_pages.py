#!/usr/bin/env python3
"""Rebuild doc-gen4's study pages as the docs pages of linglib.io.

A study page shows the paper's title and citation, the module docstring, and the declarations by
section. The theorems with a docstring, the study's headline results, are open cards; every other
declaration is a row that opens in place, and a declaration's "Built from" line opens the file's
definitions its statement names. The right column places the study in the library: the theory and
fragments its statements use, with the names they use, the imports they never name, the studies on
the same theory, the papers it cites and those citing it, and the papers it cites that no study
formalizes. Everything comes from doc-gen4's output, read by `docgen_index`, and from the
bibliography; signatures and equations are doc-gen4's own, with their links.

Usage, from the repository root, after doc-gen4 has written `.lake/build/doc`:

    python3 scripts/gen_docs_pages.py --out .lake/build/doc-site/docs-new
    python3 scripts/gen_docs_pages.py --out DIR --only KehlerRohde2013   # some studies only
    python3 scripts/gen_docs_pages.py --out DIR --check   # also confirm every anchor survives
"""

import argparse
import html
import json
import math
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
THEORY = ("Semantics", "Syntax", "Pragmatics", "Morphology", "Phonology", "Processing",
          "Discourse", "Logic", "Typology", "Features", "Phenomena")
KW = {"def": "def", "theorem": "theorem", "inductive": "inductive", "instance": "instance",
      "structure": "structure", "abbrev": "abbrev", "class": "class", "axiom": "axiom",
      "opaque": "opaque"}
# A definition's docstring that opens with a paper locator ("Table 1:", "(9):") shows it apart.
LOC = re.compile(r"^<p>((?:Tables? \d|\(\d)[^:<.]{0,36}):\s*(\w)")
CITE_LINK = re.compile(r'<a href="([^"]*references\.html#ref_([^"]+))" title="[^"]*" id="[^"]*">'
                       r'(\[[^\]]+\])</a>', re.S)
HEADING = re.compile(r'<h\d id="([^"]+)"[^>]*>(.*?)(?: <a class="hover-link"|</h\d>)', re.S)
DECL_NAME = re.compile(r'<span class="decl_kind">\w+</span>\s*<span class="decl_name">.*?</a></span>',
                       re.S)
REFS = re.compile(r'(<h2 [^>]*id="References"[^>]*>.*?</h2>)\s*<ul>(.*?)</ul>', re.S)
BARE = '<span class="decl_args"> :</span>'
SHOWN = 5
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


def node_id(node):
    kind, name = node
    return name if kind == "s" else f"{kind}-{name}"


def node_label(node):
    kind, name = node
    return " / ".join(re.split(r"[./]", name)) if kind in "td" else name


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


def year_of(study):
    m = re.search(r"\d{4}", study)
    return int(m.group(0)) if m else None


class Library:
    """What every page needs from the rest of the library: the bibliography, who cites whom, the
    declarations' references, and which studies use which theory and fragments."""

    def __init__(self, doc):
        self.doc = doc
        self.modules, self.decls, self.used_by = dx.build(doc)
        data = json.loads((doc / "declarations" / "declaration-data.bmp").read_text(encoding="utf-8"))
        self.decl_data, self.instances_for = data["declarations"], data.get("instancesFor", {})
        self.studies = gb.study_names()
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

    def idf(self, node):
        return math.log((len(self.uses) + 1) / (1 + len(self.users[node])))

    def entry(self, study):
        key = self.study_key.get(study)
        return (key, self.bib[key]) if key else (None, None)

    def cites(self, study):
        """The bibliography keys a study's file cites."""
        here = f"Studies/{study}.lean"
        return [k for k, files in self.cited_in.items() if here in files]


# ---------------------------------------------------------------- one page


class StudyPage:
    def __init__(self, lib, page, root, docs_base, sha):
        self.lib, self.page, self.root, self.docs, self.sha = lib, page, root, docs_base, sha
        self.study = self.ns = node_of(page)[1]
        self.raw = (lib.doc / page).read_text(encoding="utf-8")
        self.module = re.search(r'const MODULE_NAME="([^"]+)"', self.raw).group(1)
        self.key, self.entry = lib.entry(self.study)

    # -- links and citations

    def href(self, url):
        """A link as doc-gen4 wrote it on this page, for the rebuilt page."""
        if url.startswith(("@@", "#")) or re.match(r"[a-z]+:", url):
            return url
        path, _, frag = dx.site_link(self.page, url).partition("#")
        if path == self.page:
            return "#" + frag if frag else "#top"
        if path.startswith("Studies/"):
            return path.split("/", 1)[1] + ("#" + frag if frag else "")
        return self.docs + path + ("#" + frag if frag else "")

    def to(self, page, anchor=""):
        """A site-relative page, and anchor, for the rebuilt page."""
        rel = posixpath.relpath(page, posixpath.dirname(self.page))
        return self.href(rel + ("#" + anchor if anchor else ""))

    def cite(self, m):
        key, label = m.group(2), m.group(3)
        b = self.lib.bib.get(key)
        if not b:
            return link(f"@@bibliography/#{key}", label, "cite")
        if b["study"] == self.study:
            return f'<span class="cite self">{esc(b["label"])}</span>'
        title = esc(text(b["title"]))
        if b["study"]:
            return (f'<a class="cite done" href="{esc(b["study"])}.html" title="{title}">'
                    f'{esc(b["label"])}</a>')
        cls, tail = ("cite", "") if b["formalized"] else ("cite open", ", not yet formalized")
        return (f'<a class="{cls}" href="@@bibliography/#{esc(key)}" title="{title}{tail}">'
                f'{esc(b["label"])}</a>')

    def rewrite(self, h, short=False):
        """doc-gen4's HTML with links for the rebuilt page and author-year citations."""
        h = CITE_LINK.sub(self.cite, h)
        h = re.sub(r'href="([^"]*)"', lambda m: f'href="{esc(self.href(html.unescape(m.group(1))))}"', h)
        h = h.replace('href="@@', f'href="{self.root}')
        if short:
            # One space between tokens: the nested `.fn` boxes wrap a long term at its own
            # structure, so the pretty-printer's line breaks for a fixed width are dropped. Names
            # print without the study's namespace, which the file opens.
            h = re.sub(r">([^<]*)<", lambda m: ">" + re.sub(r"\s+", " ", m.group(1)) + "<", h)
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
            d = self.read_decl(did, block, cur["id"])
            self.decls.append(d)
            cur["decls"].append(d)
        self.fold()

    def ref_list(self, m):
        """The References list: each entry's label, then its title."""
        def item(li):
            study = re.search(r'href="([A-Z]\w+)\.html"', li.group(1))
            key = re.search(r'bibliography/#([\w-]+)', li.group(1))
            k = key.group(1) if key else self.lib.study_key.get(study.group(1)) if study else self.key
            if k not in self.lib.bib:
                return li.group(0)
            title = esc(text(self.lib.bib[k]["title"]))
            return f'<li>{li.group(1)}<span class="rt">, {title}</span></li>'
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
             "sig": self.rewrite(header, short=True), "doc": self.rewrite(doc),
             "sorried": "sorried" in block[:block.find(">")],
             "ctors": self.rewrite(ctors, short=True), "fields": self.rewrite(fields, short=True),
             "fields_id": fields_id.group(1) if fields_id else "",
             "eqs": [self.rewrite(e, short=True) for e in eqs], "refs": refs,
             "uses": sorted({r.split("#", 1)[1] for r in refs if r.split("#")[0] == self.page})}
        m = LOC.match(d["doc"])
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

    @staticmethod
    def headline(d):
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

    def toggle(self, u):
        loc = self.by_id[u]["loc"]
        return (f'<button type="button" class="tg" data-open="{esc(u)}" aria-expanded="false">'
                f'{esc(self.by_id[u]["name"])}' + (f'<span class="loc">{esc(loc)}</span>' if loc else "")
                + "</button>")

    def extras(self, d):
        """Below a declaration: what `deriving` made of it, its instances, and who uses it."""
        out = ""
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
                link(self.to(p), esc(p.removesuffix(".html").split("/")[-1])) for p in far]) + "</p>"
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
        if head:
            lede, doc = f'<div class="lede">{d["doc"]}</div>\n', ""
        loc = f'<span class="loc">{esc(d["loc"])}</span>' if d["loc"] else ""
        copy = (f'<button class="copy" type="button" data-copy="{esc(d["id"])}" '
                f'aria-label="Copy the name {esc(d["id"])}" title="Copy name">copy</button>')
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
                    f'{link("#" + d["id"], esc(d["name"]), "nm")}{copy}{loc}{src}</header>\n'
                    f'{doc}{rest}</article>')
        return (f'<article class="decl {cls}" id="{esc(d["id"])}" {data}>\n'
                f'<header class="dh"><button class="opener" type="button" aria-expanded="false">{attrs}'
                f'<span class="kw">{kw}</span> <span class="nm">{esc(d["name"])}</span>{loc}'
                f'</button>{copy}{src}</header>\n<div class="body" hidden>{doc}{rest}</div></article>')

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
                if d["folded"]:
                    continue
                cls = ("head" if self.headline(d) else "thm") if d["kind"] == "theorem" else "def"
                items.append(f'<li class="{cls}"><a href="#{esc(d["id"])}" data-for="{esc(d["id"])}">'
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

    # -- where the study sits

    def short(self, node, anchor):
        """A name without its framework's, data module's or this study's namespace."""
        dotted = node[1].replace("/", ".")
        for pre in (dotted, dotted.rsplit(".", 1)[0], self.ns, dotted.split(".")[0]):
            if anchor.startswith(pre + "."):
                return anchor[len(pre) + 1:]
        return anchor

    def rail(self):
        lib, me = self.lib, self.study
        used = defaultdict(dict)   # node -> {anchor: page}
        for d in self.decls:
            for ref in d["refs"]:
                page, anchor = ref.split("#", 1)
                node = node_of(page)
                if node and page != self.page and node[0] in "tfd":
                    used[node].setdefault(anchor, page)
        listed = self.raw[self.raw.find('<div class="imports">'):self.raw.find("Imported by")]
        imports = re.findall(r'<li><a href="[^"]*">([^<]+)</a></li>', listed)
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
            m, s = len(lib.node_pages[node]), len(lib.users[node])
            count = (f"{m} module{'' if m == 1 else 's'} · "
                     f"{s} {'study' if s == 1 else 'studies'}")
            nodes[node_id(node)] = {"k": node[0], "l": node_label(node), "h": self.to(first),
                                    "d": desc or count}
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
            _, e = lib.entry(s)
            nodes.setdefault(s, {"k": "s", "y": year_of(s), "l": e["label"] if e else s,
                                 "d": text(e["title"]) if e else s, "h": f"{s}.html"})
            note = f' <span class="why">{esc(why)}</span>' if why else ""
            return (f'<li class="s" data-node="{esc(s)}">'
                    f'{link(s + ".html", esc(nodes[s]["l"]), "nd")}{note}</li>')

        by_year = (lambda s: (year_of(s) or 0, s))
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
        cites = sorted({lib.bib[k]["study"] for k in keys} - {None, me}, key=by_year)[:8]
        if cites:
            parts.append("<h3>Cites</h3>\n<ul>" + "".join(map(study_item, cites)) + "</ul>")
            edges += [[me, s, "cite"] for s in cites]
        if self.key:
            files = lib.cited_in.get(self.key, ())
            citing = {f.split("/")[1].removesuffix(".lean") for f in files if f.startswith("Studies/")}
            citing = sorted((citing - {me}) & lib.studies, key=by_year)[:8]
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
            parts.append(f"<details><summary>All {len(imports)} imports</summary><ul>"
                         + "".join(f"<li>{esc(m)}</li>" for m in imports) + "</ul></details>")
        for n in nodes.values():
            if n.get("y") is None:
                n.pop("y", None)
        return "\n".join(parts), {"nodes": nodes, "edges": edges, "focus": me}

    # -- the page

    def render(self, template):
        self.read()
        rail, graph = self.rail()
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
        out = site_shell.render(template, self.root, "Docs", self.sha)
        prose = self.moddoc + "".join(s["prose"] for s in self.sections)
        prose += "".join(d["doc"] for d in self.shown)
        tex = TEX.search(re.sub(r"<code>.*?</code>", "", prose, flags=re.S))
        subst = {"<!--MATH-->": MATH if tex else "","<!--TITLE_TEXT-->": esc(text(title)), "<!--DESCRIPTION-->": esc(text(title)),
                 "<!--ASSETS-->": "../", "<!--TITLE-->": title, "<!--CITE-->": cite,
                 "<!--CRUMBS-->": f'{link(self.docs, "Docs")} / Studies / {esc(self.module)}',
                 "<!--MODDOC-->": self.moddoc, "<!--NDECL-->": str(len(self.shown)),
                 "<!--INDEX-->": self.index(), "<!--DECLS-->": self.body(), "<!--RAIL-->": rail,
                 "/*GRAPH*/": json.dumps(graph, ensure_ascii=False).replace("</", "<\\/"),
                 "/*PREVIEW*/": json.dumps(self.preview(), ensure_ascii=False).replace("</", "<\\/")}
        for k, v in subst.items():
            assert out.count(k) >= 1, k
            out = out.replace(k, v)
        return out


# ---------------------------------------------------------------- the site


def check(lib, out, written):
    """Declarations doc-gen4 places on a study page that the rebuilt page has no anchor for."""
    ids = {p: set(re.findall(r'\bid="([^"]+)"', (out / p).read_text(encoding="utf-8"))) for p in written}
    lost = []
    for d in lib.decl_data.values():
        page, _, frag = d["docLink"].removeprefix("./").partition("#")
        if page in ids and esc(frag) not in ids[page] and frag not in ids[page]:
            lost.append((page, frag))
    return lost


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--doc", type=Path, default=Path(".lake/build/doc"), help="doc-gen4's output")
    ap.add_argument("--out", type=Path, required=True, help="directory for the rebuilt pages")
    ap.add_argument("--root", default="../../", help="the site's root, relative to a study page")
    ap.add_argument("--docs-base", default="../../docs/",
                    help="doc-gen4's pages, relative to a study page")
    ap.add_argument("--only", nargs="*", help="rebuild these studies only")
    ap.add_argument("--check", action="store_true", help="confirm every declaration keeps its anchor")
    args = ap.parse_args()

    lib = Library(args.doc)
    sha = site_shell.git_commit()
    template = (PAGE / "template.html").read_text(encoding="utf-8")
    (args.out / "Studies").mkdir(parents=True, exist_ok=True)
    for asset in ("docs.css", "docs.js"):
        shutil.copy(PAGE / asset, args.out / asset)
    pages = sorted(p for p in lib.modules if p.startswith("Studies/"))
    if args.only:
        pages = [p for p in pages if node_of(p)[1] in args.only]
    for page in pages:
        out = StudyPage(lib, page, args.root, args.docs_base, sha).render(template)
        (args.out / page).write_text(out, encoding="utf-8")
    print(f"wrote {len(pages)} study pages to {args.out}")
    if args.check:
        lost = check(lib, args.out, pages)
        for page, frag in lost:
            print(f"{page}: no anchor for {frag}")
        print(f"{len(lost)} declarations without an anchor")
        sys.exit(1 if lost else 0)


if __name__ == "__main__":
    main()
