#!/usr/bin/env python3
"""Read doc-gen4's HTML output into an index of modules, sections and declarations.

Each module page holds the module docstring, section docstrings (`mod_doc`) and declarations
(`decl`), in source order. A declaration's references are the declarations its signature,
equations, constructors and fields link to: what its statement uses, as doc-gen4 resolved it.
Links are kept site-relative (`Studies/KehlerRohde2013.html#KehlerRohde2013.mixture`), whatever
the page's depth. `--check` confirms that every declaration doc-gen4's search data lists for a
module has an anchor on that module's page.

Usage, from the repository root:

    python3 scripts/docgen_index.py --doc .lake/build/doc            # summary of the index
    python3 scripts/docgen_index.py --doc .lake/build/doc --check    # anchors, exit 1 if any lost
"""

import argparse
import html
import json
import posixpath
import re
import sys
from collections import defaultdict
from pathlib import Path

MODULE_NAME = re.compile(r'const MODULE_NAME="([^"]+)"')
BLOCK = re.compile(r'<div class="(mod_doc|decl)(?: [^"]*)?"(?: id="([^"]*)")?>')
HREF = re.compile(r'href="([^"]+)"')
ANCHOR = re.compile(r'\bid="([^"]+)"')
NOT_MODULES = {"index.html", "search.html", "foundational_types.html", "references.html",
               "404.html", "navbar.html", "tactics.html"}


def text(h):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", h))).strip()


def div_end(s, start):
    """The index just past the `</div>` closing the `<div>` that opens at `start`."""
    depth = 0
    for m in re.finditer(r"<div\b|</div>", s[start:]):
        depth += 1 if m.group(0) == "<div" else -1
        if depth == 0:
            return start + m.end()
    raise ValueError("unbalanced <div>")


def site_link(page, href):
    """`href` as written on `page`, as a site-relative path with its fragment, or None when it
    leaves the site."""
    if re.match(r"[a-z]+:", href) or href.startswith("#"):
        return None
    return posixpath.normpath(posixpath.join(posixpath.dirname(page), href))


def part(h, cls):
    """The inner HTML of the first `<div class="cls">` or `<ul class="cls">` in `h`, or ""."""
    m = re.search(r'<(div|ul) class="' + cls + r'"[^>]*>', h)
    if not m:
        return ""
    if m.group(1) == "div":
        return h[m.end():div_end(h, m.start()) - len("</div>")]
    return h[m.end():h.index("</ul>", m.end())]


def parse_decl(page, block, did):
    kind = re.search(r'<span class="decl_kind">(\w+)</span>', block)
    src = re.search(r'<div class="gh_link"><a href="([^"]+?)#L(\d+)-L(\d+)"', block)
    header = part(block, "decl_header")
    after = block[block.index('<div class="decl_header">'):]
    after = after[div_end(after, 0):]
    eqs = re.findall(r'<li class="equation">(.*?)</li>', after, re.S)
    stmt = header + "".join(eqs) + part(after, "constructors") + part(after, "structure_fields")
    refs = []
    for href in HREF.findall(stmt):
        link = site_link(page, href)
        if link and "#" in link and not link.startswith("references.html"):
            if link.split("#", 1)[1] != did and link not in refs:
                refs.append(link)
    return {
        "id": did,
        "kind": kind.group(1) if kind else "",
        "src": src.group(1) if src else "",
        "lines": [int(src.group(2)), int(src.group(3))] if src else None,
        "sorried": 'class="decl sorried"' in block[:80] or "sorried" in block[:block.find(">")],
        "anchors": [a for a in ANCHOR.findall(block) if a != did],
        "refs": refs,
        "doc": text(after[:min([i for i in (after.find("<details"), after.find('<ul class="'))
                                if i >= 0] + [len(after)])]),
    }


def parse_page(doc, path):
    """One module page as {module, path, doc, blocks}; blocks are sections and declarations in
    source order."""
    page = path.relative_to(doc).as_posix()
    raw = path.read_text(encoding="utf-8")
    name = MODULE_NAME.search(raw)
    if not name:
        return None
    main = raw[raw.find("<main>") + len("<main>"):raw.rfind("</main>")]
    blocks, end = [], 0
    for m in BLOCK.finditer(main):
        if m.start() < end:
            continue
        end = div_end(main, m.start())
        block = main[m.start():end]
        if m.group(1) == "mod_doc":
            head = re.search(r'<h(\d) id="([^"]+)"[^>]*>(.*?)(?: <a class="hover-link"|</h\d>)', block, re.S)
            blocks.append({"type": "doc", "level": int(head.group(1)) if head else 0,
                           "id": head.group(2) if head else "", "title": text(head.group(3)) if head else "",
                           "text": text(block)})
        else:
            blocks.append({"type": "decl", **parse_decl(page, block, m.group(2))})
    return {"module": name.group(1), "path": page, "blocks": blocks}


def module_pages(doc):
    for path in sorted(doc.rglob("*.html")):
        rel = path.relative_to(doc).as_posix()
        if rel in NOT_MODULES or rel.split("/")[0] in ("find", "declarations"):
            continue
        yield path


def build(doc):
    """The index: modules by page path, declarations by name, and who refers to whom."""
    modules, decls = {}, {}
    for path in module_pages(doc):
        mod = parse_page(doc, path)
        if not mod:
            continue
        modules[mod["path"]] = mod
        for b in mod["blocks"]:
            if b["type"] == "decl":
                decls[b["id"]] = {"page": mod["path"], **{k: b[k] for k in ("kind", "lines", "refs")}}
    used_by = defaultdict(set)
    for name, d in decls.items():
        for link in d["refs"]:
            used_by[link.split("#", 1)[1]].add(name)
    return modules, decls, used_by


def check(doc, modules):
    """Declarations doc-gen4's search data places on a page we read but that has no anchor there."""
    data = json.loads((doc / "declarations" / "declaration-data.bmp").read_text(encoding="utf-8"))
    anchors = defaultdict(set)
    for path, mod in modules.items():
        for b in mod["blocks"]:
            if b["type"] == "decl":
                anchors[path].add(b["id"])
                anchors[path].update(b["anchors"])
    lost = []
    for name, d in data["declarations"].items():
        page, _, frag = d["docLink"].removeprefix("./").partition("#")
        if page in modules and frag not in anchors[page]:
            lost.append((page, frag))
    return lost


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--doc", type=Path, default=Path(".lake/build/doc"), help="doc-gen4's output")
    ap.add_argument("--check", action="store_true", help="report declarations without an anchor")
    args = ap.parse_args()
    modules, decls, used_by = build(args.doc)
    if args.check:
        lost = check(args.doc, modules)
        for page, frag in lost:
            print(f"{page}: no anchor for {frag}")
        print(f"{len(modules)} module pages, {len(decls)} declarations, {len(lost)} without an anchor")
        sys.exit(1 if lost else 0)
    refs = sum(len(d["refs"]) for d in decls.values())
    print(f"{len(modules)} module pages, {len(decls)} declarations, {refs} references, "
          f"{sum(1 for n in decls if used_by.get(n))} declarations used elsewhere")


if __name__ == "__main__":
    main()
