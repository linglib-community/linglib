#!/usr/bin/env python3
"""Write the pages that read as a text: a source's items at `/checks/<bib-key>/`, and each file
those items rest on at `/text/<path>/`.

`checks/<bib-key>.toml` lists the items of a source (`checks/README.md`). A source's page shows
the claims under the source's sections, each headed by its kind and the source's name for it. A
file's page shows its module docstring, its section headings and its documented declarations in
the order of the source, each headed by its kind and a number. On either, choosing an item shows
beside it the Lean: the statements of the declarations, what they use, opening in place, and for
a source's item how the Lean departs from it and the sign-off. Until an item is chosen the side
holds a chart of what the page rests on: files linked where a statement of one mentions a
declaration of the other, mathlib at the top, the page at the bottom, and under a file what
rests on it. The index lists the sources that have a record.

Everything comes from `checks.py status --json`, the bibliography, the check files, which give
each item's line for the link to its record, and the first heading of a file that has no text.
Nothing is read from doc-gen4's output: a declaration's link to the API docs is its module's
page and its name.

Usage, from the repository root:

    python3 scripts/checks.py status --json > checks.json
    python3 scripts/gen_checks_pages.py --checks checks.json --out SITE
"""

import argparse
import datetime
import functools
import html
import json
import posixpath
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import gen_bibliography_page as gb  # noqa: E402
import site_shell  # noqa: E402
from gen_docs_pages import bib_label, match_study  # noqa: E402

PAGE = ROOT / "scripts" / "checks_page"
# How the Lean departs from an item, said before the notes; an exact statement needs no word.
RELATION = {"generalizes": "More general than the source.", "specializes": "A special case.",
            "variant": "A variant.", "counterexample": "A counterexample.",
            "missing": "Not formalized yet."}
KW = {"def": "def", "theorem": "theorem", "inductive": "inductive", "constructor": "constructor",
      "recursor": "recursor", "opaque": "opaque", "axiom": "axiom", "quot": "quot"}
# The heading of a declaration in a file's text, by the keyword it is written with.
HEAD = {"def": "Definition", "abbrev": "Definition", "structure": "Definition",
        "class": "Definition", "inductive": "Definition", "opaque": "Definition",
        "theorem": "Theorem", "instance": "Instance"}
# Sections of a module docstring that close a file's text, and those the text itself replaces.
CLOSING = {"Implementation notes": "Notes on the formalization", "References": "References",
           "TODO": "To do", "Notation": "Notation"}
LISTS = re.compile(r"Main (definitions|results|statements|theorems|declarations)\b")
CITE = r"[a-z0-9][a-z0-9-]*-\d{4}[a-z]?"
INLINE = re.compile(r"`([^`]+)`|\[([^\]]+)\]\((##)?([^)\s]+)\)|\[(" + CITE + r")\]"
                    r"|\*\*(.+?)\*\*|\*([^*\s][^*]*?)\*")

esc = html.escape


def generated(name):
    """Whether Lean made the declaration: a constructor, an instance it named, an auxiliary."""
    last = name.split(".")[-1]
    return ("._" in name or last.startswith("inst")
            or last in ("mk", "casesOn", "recOn", "rec", "noConfusion"))


def display(node, name):
    """A definition as its file writes it; a theorem's statement, and what Lean generated, as Lean
    prints it, without the universe list after a name and with the last component of its own
    name, since the full one stands above it."""
    if node["source"]:
        return node["source"]
    text = re.sub(r"(?m)^(\s*(?:\| )?[^\s({\[:]+)\.\{[^}]*\}", r"\1", node["display"])
    return name.split(".")[-1] + text[len(name):] if text.startswith(name) else text


def keyword(node):
    """The keyword a declaration is written with, which for a structure or a class is not the
    kind Lean files it under."""
    m = re.match(r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|"
                 r"nonrec|scoped|local)\s+)*"
                 r"(def|abbrev|structure|class|inductive|instance|opaque)\b",
                 node["source"] or "")
    return m.group(1) if m else KW.get(node["kind"], node["kind"])


class Site:
    """What a page needs of the rest: the bibliography, the declarations, and where each
    module and each documented declaration is shown."""

    def __init__(self, data):
        self.items, self.nodes, self.texts = data["items"], data["nodes"], data.get("texts", {})
        self.bib = {key: (kind, f)
                    for kind, key, f in gb.parse_bib(gb.BIB.read_text(encoding="utf-8"))}
        self.sources = {}
        for item in self.items:
            self.sources.setdefault(item["source"], []).append(item)
        # A file's text has its documented declarations that a statement closure describes.
        self.shown = {m: [d for d in t["decls"] if d["doc"] and d["name"] in self.nodes]
                      for m, t in self.texts.items()}
        self.home = {d["name"]: m for m, ds in self.shown.items() for d in ds}
        self.titles = {m: self.title(m) for m in {n["module"] for n in self.nodes.values()}}
        # The items of the sources that a declaration states.
        self.stated = {}
        for item in self.items:
            for d in item["decls"]:
                self.stated.setdefault(d, []).append(item)
        # Statement-level use between modules, and the names one uses of another.
        self.uses = {m: set() for m in self.titles}
        self.named = {}
        for node in self.nodes.values():
            for u in node["uses"]:
                other = self.nodes.get(u)
                if other and other["module"] != node["module"]:
                    self.uses[node["module"]].add(other["module"])
                    if not generated(u):
                        self.named.setdefault((node["module"], other["module"]),
                                              set()).add(u.split(".")[-1])

    def title(self, module):
        """A module's first heading, from its text or else its file."""
        docs = [d["doc"] for d in self.texts.get(module, {}).get("docs", ())]
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not docs and path.exists():
            docs = re.findall(r"/-!(.*?)-/", path.read_text(encoding="utf-8"), re.S)[:1]
        for doc in docs:
            m = re.search(r"(?m)^# (.+)$", doc)
            if m:
                return m.group(1).strip()
        return module.split(".")[-1]

    def label(self, key):
        f = self.bib[key][1]
        return bib_label(f, f.get("year", "")) or key

    @staticmethod
    def text_path(module):
        parts = module.split(".")
        return "text/" + "/".join(parts[1:] if parts[0] == "Linglib" else parts) + "/"

    @staticmethod
    def docs_path(module, name=None):
        return f'docs/{module.replace(".", "/")}.html' + (f"#{name}" if name else "")

    def module_path(self, module):
        """The page of a module: its text if it has one, else the API docs."""
        return self.text_path(module) if module in self.texts else self.docs_path(module)

    def decl_path(self, name):
        """Where a declaration is shown: its place in a text, else the API docs."""
        if name in self.home:
            return self.text_path(self.home[name]) + "#" + name
        node = self.nodes.get(name)
        return self.docs_path(node["module"], name) if node else None

    @functools.lru_cache(None)
    def reach(self, module):
        out = set()
        for m in self.uses[module]:
            out |= {m} | self.reach(m)
        return frozenset(out)


class Page:
    """A page at `path` under the site's root, which makes its links relative."""

    def __init__(self, site, path):
        self.site, self.path = site, path
        self.root = "../" * path.count("/")
        self.here = set()   # the items of this page, which a link chooses in place of leaving
        self.cover = {}     # for a source's page, the items that cover a declaration

    def href(self, target):
        return esc(self.root + target, quote=True)

    def inline(self, text, titles=False):
        """Inline Markdown: code, emphasis, a bold term, and links to a declaration, to the
        bibliography, with the work's title in a list of references, or elsewhere."""
        out, at = [], 0
        for m in INLINE.finditer(text):
            out.append(esc(text[at:m.start()]))
            at = m.end()
            code, label, decl, target, key, bold, em = m.groups()
            if code:
                out.append(f"<code>{esc(code)}</code>")
            elif label and decl:
                inner, to = self.inline(label), self.site.decl_path(target)
                if target in self.here:
                    out.append(f'<a class="pick" href="#{esc(target, quote=True)}">{inner}</a>')
                else:
                    out.append(f'<a class="ref" href="{self.href(to)}">{inner}</a>' if to
                               else inner)
            elif label:
                out.append(f'<a class="ref" href="{esc(target, quote=True)}">'
                           f'{self.inline(label)}</a>')
            elif key in self.site.bib:
                title = gb.tex_text(self.site.bib[key][1].get("title", ""))
                out.append(f'<a class="ref" href="{self.href("bibliography/#" + key)}">'
                           f'{esc(self.site.label(key))}</a>'
                           + (f", {esc(title)}" if title and titles else ""))
            elif key:
                out.append(esc(m.group(0)))
            elif bold:
                out.append(f'<b class="term">{self.inline(bold)}</b>')
            else:
                out.append(f"<em>{self.inline(em)}</em>")
        return "".join(out + [esc(text[at:])])

    def blocks(self, text):
        """Markdown as `(kind, content)`: a heading with its title, or a paragraph, a list or a
        code block as HTML."""
        out, para, items, code, refs = [], [], [], None, False

        def flush():
            if para:
                out.append(("p", "<p>" + self.inline(" ".join(para)) + "</p>"))
                para.clear()
            if items:
                out.append(("ul", "<ul>" + "".join(f"<li>{self.inline(i, refs)}</li>"
                                                   for i in items) + "</ul>"))
                items.clear()

        for line in text.strip().split("\n"):
            fence = line.strip().startswith("```")
            heading = re.match(r"(#+)\s+(.*)", line)
            if code is not None:
                if fence:
                    out.append(("pre", "<pre>" + esc("\n".join(code)) + "</pre>"))
                    code = None
                else:
                    code.append(line)
            elif fence:
                flush()
                code = []
            elif heading:
                flush()
                refs = heading.group(2).strip() == "References"
                out.append((f"h{len(heading.group(1))}", heading.group(2).strip()))
            elif re.match(r"\s*[*-]\s+", line):
                if para:
                    flush()
                items.append(re.sub(r"^\s*[*-]\s+", "", line))
            elif not line.strip():
                flush()
            elif items and line.startswith(" "):
                items[-1] += " " + line.strip()
            else:
                if items:
                    flush()
                para.append(line.strip())
        flush()
        return out

    def prose(self, text):
        return "".join(content for kind, content in self.blocks(text) if kind[0] != "h")

    def closure(self, names):
        """The declarations the page's script shows: those named and what they use."""
        nodes, used, todo = self.site.nodes, {}, list(names)
        while todo:
            n = todo.pop()
            if n in used or n not in nodes:
                continue
            used[n] = {"k": keyword(nodes[n]), "t": display(nodes[n], n),
                       "u": [u for u in nodes[n]["uses"]
                             if u in nodes and u != n and not generated(u)],
                       "h": self.root + self.site.decl_path(n), "c": self.cover.get(n, [])}
            todo += used[n]["u"]
        return used

    def chart(self, focus, focus_label, roots, below=()):
        """What the page rests on. The declarations `roots` and all their statements reach are
        sorted into their files, with a link where a statement in the lower file mentions a
        declaration of the upper and no longer path says so; mathlib is at the top and the page
        at the bottom, the file `focus` or else a source that the files of `roots` hold up.
        `below` it is what rests on it, as `(label, path, shape, why)`."""
        nodes = self.site.nodes
        reached, todo = set(), [r for r in roots if r in nodes]
        while todo:
            d = todo.pop()
            if d not in reached:
                reached.add(d)
                todo += [u for u in nodes[d]["uses"] if u in nodes]
        uses, named = {nodes[d]["module"]: set() for d in reached}, {}
        for d in reached:
            for u in nodes[d]["uses"]:
                if u in reached and nodes[u]["module"] != nodes[d]["module"]:
                    uses[nodes[d]["module"]].add(nodes[u]["module"])
                    if not generated(u):
                        named.setdefault(nodes[u]["module"], set()).add(u.split(".")[-1])
        if focus not in uses:
            uses[focus] = {nodes[r]["module"] for r in roots if r in nodes}

        @functools.lru_cache(None)
        def reach(m):
            return frozenset(uses[m]).union(*(reach(b) for b in uses[m]))

        @functools.lru_cache(None)
        def depth(m):
            return 1 + max((depth(b) for b in uses[m]), default=-1)

        level = {m: depth(m) for m in {focus} | reach(focus)}
        links = [(a, b) for a in level for b in uses[a]
                 if not any(b in reach(c) for c in uses[a] if c != b)]
        rows = {}
        for m in level:
            rows.setdefault(level[m], []).append(m)
        widest = max(max(len(r) for r in rows.values()), len(below))
        width, row, top = max(560, 112 * widest), 86, 30
        x, y = {}, {}
        for lv in sorted(rows):
            def over(m):
                up = [x[b] for b in uses[m] if b in x]
                return sum(up) / len(up) if up else 0
            rows[lv].sort(key=lambda m: (over(m), self.site.titles.get(m, "")))
            for k, m in enumerate(rows[lv]):
                x[m], y[m] = width * (k + 1) / (len(rows[lv]) + 1), top + 28 + lv * row

        def label(text, cx, cy, cls=""):
            lines, cur = [], ""
            for word in text.split():
                if cur and len(cur) + len(word) > 17:
                    lines.append(cur)
                    cur = word
                else:
                    cur = (cur + " " + word).strip()
            lines = (lines + [cur])[:3]
            return len(lines), "".join(
                f'<text class="gl {cls}" x="{cx:.0f}" y="{cy + 19 + 14 * k:.0f}" '
                f'text-anchor="middle">{esc(line)}</text>' for k, line in enumerate(lines))

        def curve(x1, y1, x2, y2):
            mid = (y1 + y2) / 2
            return (f'<path class="ge" d="M{x1:.0f},{y1:.0f} C{x1:.0f},{mid:.0f} {x2:.0f},'
                    f'{mid:.0f} {x2:.0f},{y2 - 7:.0f}"/>')

        marks, foot = [], {}
        for m in level:
            mine = m == focus
            n, text = label(focus_label if mine else self.site.titles[m], x[m], y[m],
                            "here" if mine else "")
            foot[m] = y[m] + 12 + 14 * n
            kind = "here" if mine else "study" if m.startswith("Studies.") else "theory"
            mark = (f'<rect class="gn {kind}" x="{x[m] - 5:.0f}" y="{y[m] - 5:.0f}" width="10" '
                    f'height="10" rx="1.5"/>{text}')
            if mine:
                marks.append(mark)
            else:
                why = ", ".join(sorted(named.get(m, ())))
                marks.append(f'<a href="{self.href(self.site.module_path(m))}">'
                             f'<title>{esc(why)}</title>{mark}</a>')
        lines = [f'<line class="gbase" x1="16" y1="{top}" x2="{width - 16}" y2="{top}"/>'
                 f'<text class="gl base" x="{width / 2:.0f}" y="{top - 9}" text-anchor="middle">'
                 'mathlib</text>']
        lines += [f'<path class="ge" d="M{x[m]:.0f},{top} L{x[m]:.0f},{y[m] - 7:.0f}"/>'
                  for m in rows.get(0, ())]
        lines += [curve(x[b], foot[b], x[a], y[a]) for a, b in links]
        height = max(foot.values()) + 14
        for k, (text, path, shape, why) in enumerate(below):
            bx, by = width * (k + 1) / (len(below) + 1), y[focus] + row
            lines.append(curve(x[focus], foot[focus], bx, by))
            n, text = label(text, bx, by)
            mark = (f'<circle class="gn study" cx="{bx:.0f}" cy="{by:.0f}" r="5.5"/>'
                    if shape == "source" else
                    f'<rect class="gn {shape}" x="{bx - 5:.0f}" y="{by - 5:.0f}" width="10" '
                    'height="10" rx="1.5"/>')
            marks.append(f'<a href="{self.href(path)}"><title>{esc(why)}</title>{mark}{text}</a>')
            height = max(height, by + 26 + 14 * n)
        return (f'<svg class="chart" viewBox="0 0 {width} {height:.0f}" '
                f'style="max-width:{width}px" role="img" aria-label="What this page rests on">'
                + "".join(lines + marks) + "</svg>")

    def render(self, title, crumbs, h1, by, body, links, aside, panel, sha):
        template = (PAGE / "template.html").read_text(encoding="utf-8")
        page = site_shell.render(template, self.root, None, sha)
        nodes = self.closure([d for item in panel.values() for d in item["decls"]])
        data = json.dumps({"items": panel, "nodes": nodes}, ensure_ascii=False,
                          separators=(",", ":"))
        fill = {"<!--TITLE-->": esc(title), "<!--CRUMBS-->": crumbs, "<!--H1-->": h1,
                "<!--BY-->": by, "<!--ITEMS-->": "\n".join(body), "<!--LINKS-->": " ".join(links),
                "<!--ASIDE-->": aside, "/*DATA*/{}": data.replace("</", "<\\/")}
        for mark, value in fill.items():
            assert page.count(mark) == 1, f"the template needs exactly one {mark}"
            page = page.replace(mark, value)
        return page


def who(ck):
    by = esc(ck["by"])
    return by if ck["via"] else f'<a href="https://github.com/{by}">{by}</a>'


def when(ck):
    day = datetime.date.fromisoformat(ck["date"])
    return f"{day.day} {day:%B} {day.year}"


def refs(ids, items, source):
    """Links that choose items of the same page by their labels, and plain names for those of
    another."""
    out = []
    for ref in ids:
        it = items.get(ref)
        if it and it["source"] == source:
            out.append(f'<a class="pick" href="#{esc(it["id"], quote=True)}">'
                       f'{esc(it["label"])}</a>')
        else:
            out.append(esc(ref))
    return ", ".join(out)


def state(it, items):
    """The line that says whether a person has checked the item."""
    ck, st = it["check"], it["status"]
    signed = f"Checked by {who(ck)} on {when(ck)}" if ck else ""
    if st == "missing":
        return ""
    if st == "broken":
        names = ", ".join(f"<code>{esc(n)}</code>" for n in it["unresolved"])
        return f"No longer resolves: {names}."
    if st == "unproved":
        names = ", ".join(f"<code>{esc(n)}</code>" for n in it["axioms"])
        return f"Not proved: rests on {names}." + (f" {signed}." if signed else "")
    if st == "unchecked":
        return "Not yet checked."
    if st == "stale":
        return f"{signed}; the statement has changed since."
    if st == "relies":
        rest = it["blocking"]
        verb = "is" if len(rest) == 1 else "are"
        return f"{signed}, relying on {refs(rest, items, it['source'])}, which {verb} not."
    return f"{signed}."


def head(i):
    """The run-in heading of an item: its kind and the source's own name for it, with a mark when a
    person has checked it."""
    kind, label = esc(i["kind"].capitalize()), esc(i["label"])
    name = (f'{kind} <span class="no">{label}.</span>' if label.startswith("(")
            else f'{kind}<span class="no">, {label}.</span>')
    mark, ck = "", i["check"]
    if ck and i["status"] in ("checked", "relies"):
        mark = (f'<span class="mark" title="Checked by {esc(ck["by"], quote=True)} on '
                f'{when(ck)}">✓</span>')
    elif ck and i["status"] == "stale":
        mark = ('<span class="mark stale" title="Its statement has changed since it was '
                'checked">✓</span>')
    return f'<span class="head">{name}</span>{mark}'


def source_page(site, key, studies, sha, lines):
    page = Page(site, f"checks/{key}/")
    its = site.sources[key]
    kind, f = site.bib[key]
    items = {f'{i["source"]}/{i["id"]}': i for i in its}
    year = f.get("year", "")
    cite = ". ".join(p for p in (f"{esc(gb.authors(f))} ({esc(year)})", gb.venue(kind, f)) if p)
    record = f"{site_shell.REPO}/blob/main/checks/{key}.toml"
    links = [f'<a href="{page.href("bibliography/#" + key)}">Bibliography</a>']
    study = match_study(key, studies)
    if study:
        links.append(f'<a href="{page.href(site.module_path("Studies." + study))}">Study</a>')
    links.append(f'<a href="{record}">Record</a>')
    for i in its:
        for d in i["decls"]:
            page.cover.setdefault(d, []).append((i["id"], i["label"]))

    body, panel = [], {}
    for i in its:
        iid = esc(i["id"], quote=True)
        if i["section"]:
            n, _, title = i["section"].partition(" ")
            body.append(f'<h2 class="sec"><span class="n">{esc(n)}</span>{esc(title)}</h2>'
                        if n.startswith("§") else f'<h2 class="sec">{esc(i["section"])}</h2>')
        claim = page.prose(i["claim"]).replace("<p>", f"<p>{head(i)} ", 1)
        body.append(f'<article class="item" id="{iid}" tabindex="0">{claim}</article>')
        line = state(i, items)
        if i["relies"] and i["status"] != "relies":
            verb = "defines" if len(i["relies"]) == 1 else "define"
            uses = f"Its statement uses what {refs(i['relies'], items, key)} {verb}."
            line = f"{line} {uses}" if line else uses
        if i["id"] in lines:
            line += (" " if line else "") + f'<a href="{record}#L{lines[i["id"]]}">Record</a>.'
        how = f'<p class="rel">{RELATION[i["relation"]]}</p>' if i["relation"] in RELATION else ""
        panel[i["id"]] = {"how": how + page.prose(i["notes"]), "decls": i["decls"],
                          "state": line}

    label = site.label(key)
    return page.path, page.render(
        gb.tex_text(f.get("title", key)), f'<a href="../">Checks</a> / {esc(label)}',
        gb.tex_html(f.get("title", key)), cite, body, links,
        page.chart(key, label, [d for i in its for d in i["decls"]]), panel, sha)


def module_page(site, module, sha):
    page = Page(site, site.text_path(module))
    text, shown = site.texts[module], site.shown[module]
    page.here = {d["name"] for d in shown}
    stream = sorted([(d["line"], "doc", d) for d in text["docs"]]
                    + [(d["line"], "decl", d) for d in shown], key=lambda t: t[0])
    body, tail, panel, count, title = [], [], {}, 0, site.titles[module]
    for _, what, x in stream:
        if what == "doc":
            section = None
            for kind, content in page.blocks(x["doc"]):
                if kind == "h1":
                    continue
                if kind[0] == "h":
                    section = content
                    if content in CLOSING:
                        tail.append(f'<h2 class="sec">{esc(CLOSING[content])}</h2>')
                    elif not LISTS.match(content):
                        body.append(f'<h2 class="sec">{page.inline(content)}</h2>')
                elif section in CLOSING:
                    cls = "refs" if section == "References" else "prose"
                    tail.append(f'<div class="{cls}">{content}</div>')
                elif not (section and LISTS.match(section)):
                    body.append(f'<div class="prose">{content}</div>')
            continue
        count += 1
        name = x["name"]
        kw = keyword(site.nodes[name])
        heading = (f'<span class="head">{HEAD.get(kw, kw.capitalize())} '
                   f'<span class="no">{count}.</span></span>')
        doc = page.prose(x["doc"])
        doc = (doc.replace("<p>", f"<p>{heading} ", 1) if doc.startswith("<p>")
               else f"<p>{heading}</p>{doc}")
        body.append(f'<article class="item" id="{esc(name, quote=True)}" tabindex="0">{doc}'
                    '</article>')
        states = [f'States <a href="{page.href("checks/" + i["source"] + "/#" + i["id"])}">'
                  f'{esc(i["label"])} of {esc(site.label(i["source"]))}</a>.'
                  for i in site.stated.get(name, ())]
        panel[name] = {"how": "", "decls": [name], "state": " ".join(states)}

    # Under the file: the texts that use it and no longer path says so, and the sources it states.
    below = []
    for m in sorted(site.texts, key=lambda m: site.titles[m]):
        if module in site.uses[m] and not any(module in site.reach(c)
                                              for c in site.uses[m] if c != module):
            why = ", ".join(sorted(site.named.get((m, module), ())))
            shape = "study" if m.startswith("Studies.") else "theory"
            below.append((site.titles[m], site.module_path(m), shape, why))
    stating = {}
    for d in text["decls"]:
        for i in site.stated.get(d["name"], ()):
            stating.setdefault(i["source"], []).append(i["label"])
    below += [(site.label(key), f"checks/{key}/", "source", ", ".join(dict.fromkeys(labels)))
              for key, labels in stating.items()]

    parts = module.split(".")
    crumbs = esc(" / ".join(parts[1:-1] if parts[0] == "Linglib" else parts[:-1]))
    links = [f'<a href="{page.href(site.docs_path(module))}">API docs</a>',
             f'<a href="{site_shell.REPO}/blob/main/{module.replace(".", "/")}.lean">Source</a>']
    return page.path, page.render(
        title, crumbs, page.inline(title), f"<code>{esc(module)}</code>", body + tail, links,
        page.chart(module, title, [d["name"] for d in text["decls"]], below), panel, sha)


def index_page(site, sha):
    rows = []
    for key, its in sorted(site.sources.items(), key=lambda kv: gb.surname(
            site.bib[kv[0]][1].get("author") or site.bib[kv[0]][1].get("editor") or kv[0])):
        f = site.bib[key][1]
        done = sum(1 for i in its if i["status"] == "checked")
        count = f'{len(its)} item{"" if len(its) == 1 else "s"}'
        tally = f"{count}, {done} checked" if done else f"{count}, none checked yet"
        cls = "all" if done == len(its) else "some" if done else "none"
        rows.append(f'<li class="source {cls}"><a href="{esc(key, quote=True)}/">'
                    f'<strong>{esc(site.label(key))}</strong> '
                    f'{gb.tex_html(f.get("title", ""))}</a>'
                    f'<span class="tally">{tally}</span></li>')
    template = (PAGE / "index.html").read_text(encoding="utf-8")
    page = site_shell.render(template, "../", None, sha)
    assert page.count("<!--SOURCES-->") == 1, "the index needs exactly one <!--SOURCES-->"
    return page.replace("<!--SOURCES-->", "\n".join(rows))


def item_lines(key):
    """The line of each item of a check file, by its id."""
    out = {}
    path = ROOT / "checks" / f"{key}.toml"
    if path.exists():
        for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            m = re.match(r'\s*id\s*=\s*"([^"]+)"', line)
            if m:
                out.setdefault(m.group(1), n)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--checks", type=Path, required=True, help="`checks.py status --json`")
    ap.add_argument("--out", type=Path, required=True, help="the site's root directory")
    args = ap.parse_args()

    site = Site(json.loads(args.checks.read_text(encoding="utf-8")))
    studies = {p.stem for p in (ROOT / "Studies").glob("*.lean")}
    sha = site_shell.git_commit()
    missing = sorted(set(site.sources) - set(site.bib))
    if missing:
        sys.exit("not in references.bib: " + ", ".join(missing))

    pages = {"checks/": index_page(site, sha)}
    pages.update(source_page(site, key, studies, sha, item_lines(key)) for key in site.sources)
    pages.update(module_page(site, module, sha) for module in site.texts)
    for path, page in pages.items():
        (args.out / path).mkdir(parents=True, exist_ok=True)
        (args.out / path / "index.html").write_text(page, encoding="utf-8")
    # A link from one of these pages to another must land on a page written here.
    dead = [(p, t) for p, page in pages.items()
            for t in re.findall(r'href="((?:\.\./)+(?:checks|text)/[^"#]*)', page)
            if posixpath.normpath(posixpath.join(p, t)) + "/" not in pages]
    for p, t in dead:
        print(f"{p}: no page at {t}", file=sys.stderr)
    print(f"wrote {args.out}: {len(site.sources)} source{'' if len(site.sources) == 1 else 's'}, "
          f"{len(site.items)} items, {len(site.texts)} files as texts")
    sys.exit(1 if dead else 0)


if __name__ == "__main__":
    main()
