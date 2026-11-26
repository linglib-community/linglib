#!/usr/bin/env python3
"""Write the pages of `/checks/`: a source's items in its own order, each with the Lean that
states it and whether a person has checked the two against each other.

`checks/<bib-key>.toml` lists the items of a source (`checks/README.md`). A source's page shows
the claims as a text to read, under the source's sections, each headed by its kind and the
source's name for it. Choosing an item shows beside it how the Lean stands to it, the statements
of the declarations that state it, and the sign-off; the project declarations a statement
mentions open in place, and those open in turn, so the page holds what a signer reads. The index
lists the sources that have a record.

Everything comes from `checks.py status --json`, the bibliography and the check files, which give
each item's line for the link to its record. Nothing is read from doc-gen4's output: a
declaration's link to the API docs is its module's page and its name.

Usage, from the repository root:

    python3 scripts/checks.py status --json > checks.json
    python3 scripts/gen_checks_pages.py --checks checks.json --out DIR
"""

import argparse
import datetime
import html
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import gen_bibliography_page as gb  # noqa: E402
import site_shell  # noqa: E402
from gen_docs_pages import bib_label, match_study  # noqa: E402

PAGE = ROOT / "scripts" / "checks_page"
# How the Lean stands to an item, as the line under its claim says it.
RELATION = {"exact": "The Lean states this.",
            "generalizes": "The Lean states something more general.",
            "specializes": "The Lean states a special case.",
            "variant": "The Lean states a variant.",
            "counterexample": "The Lean gives a counterexample.",
            "missing": "Not formalized yet."}
KW = {"def": "def", "theorem": "theorem", "inductive": "inductive", "constructor": "constructor",
      "recursor": "recursor", "opaque": "opaque", "axiom": "axiom", "quot": "quot"}

esc = html.escape


def prose(text):
    """Paragraphs of a claim or notes as HTML, with backquoted code and, in bold, a term the
    item defines (`**term**`)."""
    out = []
    for para in re.split(r"\n\s*\n", text.strip()):
        parts = re.split(r"`([^`]+)`", " ".join(para.split()))
        out.append("<p>" + "".join(
            f"<code>{esc(p)}</code>" if i % 2
            else re.sub(r"\*\*(.+?)\*\*", r'<b class="term">\1</b>', esc(p))
            for i, p in enumerate(parts)) + "</p>")
    return "".join(out) if text.strip() else ""


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


def doc_href(docs, node, name):
    return f'{docs}{node["module"].replace(".", "/")}.html#{esc(name, quote=True)}'


def who(ck):
    by = esc(ck["by"])
    return by if ck["via"] else f'<a href="https://github.com/{by}">{by}</a>'


def when(ck):
    day = datetime.date.fromisoformat(ck["date"])
    return f"{day.day} {day:%B} {day.year}"


def refs(ids, items, source):
    """Links to items of the same page by their labels, and plain names for those of another."""
    out = []
    for ref in ids:
        it = items.get(ref)
        if it and it["source"] == source:
            out.append(f'<a href="#{esc(it["id"], quote=True)}">{esc(it["label"])}</a>')
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
                f'{when(ck)}">\u2713</span>')
    elif ck and i["status"] == "stale":
        mark = ('<span class="mark stale" title="Its statement has changed since it was '
                'checked">\u2713</span>')
    return f'<span class="head">{name}</span>{mark}'


def source_page(key, its, nodes, bib, studies, sha, lines):
    kind, f = bib[key]
    items = {f'{i["source"]}/{i["id"]}': i for i in its}
    docs = "../../docs/"
    cover = {}
    for i in its:
        for d in i["decls"]:
            cover.setdefault(d, []).append((i["id"], i["label"]))
    year = f.get("year", "")
    cite = ". ".join(p for p in (f"{esc(gb.authors(f))} ({esc(year)})", gb.venue(kind, f)) if p)
    record = f"{site_shell.REPO}/blob/main/checks/{key}.toml"
    links = [f'<a href="../../bibliography/#{esc(key, quote=True)}">Bibliography</a>']
    study = match_study(key, studies)
    if study:
        links.append(f'<a href="{docs}Studies/{study}.html">Study</a>')
    links.append(f'<a href="{record}">Record</a>')

    body, panel = [], {}
    for i in its:
        iid = esc(i["id"], quote=True)
        if i["section"]:
            n, _, title = i["section"].partition(" ")
            body.append(f'<h2 class="sec"><span class="n">{esc(n)}</span>{esc(title)}</h2>'
                        if n.startswith("§") else f'<h2 class="sec">{esc(i["section"])}</h2>')
        claim = prose(i["claim"]).replace("<p>", f"<p>{head(i)} ", 1)
        body.append(f'<article class="item" id="{iid}" tabindex="0">{claim}</article>')
        line = state(i, items)
        if i["relies"] and i["status"] != "relies":
            verb = "defines" if len(i["relies"]) == 1 else "define"
            uses = f"Its statement uses what {refs(i['relies'], items, key)} {verb}."
            line = f"{line} {uses}" if line else uses
        if i["id"] in lines:
            line += (" " if line else "") + f'<a href="{record}#L{lines[i["id"]]}">Record</a>.'
        # An exact item with no notes needs no sentence; notes read as its continuation.
        bare = i["relation"] == "exact" and not i["notes"]
        how = "" if bare else f'<p>{RELATION[i["relation"]]}</p>'
        panel[i["id"]] = {"title": f'{i["label"]} in Lean', "how": how + prose(i["notes"]),
                          "decls": i["decls"], "state": line}

    used, todo = {}, [d for i in its for d in i["decls"]]
    while todo:
        n = todo.pop()
        if n in used or n not in nodes:
            continue
        node = nodes[n]
        used[n] = {"k": keyword(node), "t": display(node, n),
                   "u": [u for u in node["uses"] if u in nodes and u != n],
                   "h": doc_href(docs, node, n), "c": cover.get(n, [])}
        todo += node["uses"]
    data = json.dumps({"items": panel, "nodes": used}, ensure_ascii=False, separators=(",", ":"))
    template = (PAGE / "template.html").read_text(encoding="utf-8")
    page = site_shell.render(template, "../../", None, sha)
    fill = {"<!--TITLE-->": esc(gb.tex_text(f.get("title", key))),
            "<!--LABEL-->": esc(bib_label(f, year) or key),
            "<!--H1-->": gb.tex_html(f.get("title", key)), "<!--CITE-->": cite,
            "<!--LINKS-->": " ".join(links), "<!--ITEMS-->": "\n".join(body),
            "/*DATA*/{}": data.replace("</", "<\\/")}
    for mark, value in fill.items():
        assert page.count(mark) == 1, f"the template needs exactly one {mark}"
        page = page.replace(mark, value)
    return page


def index_page(by_source, bib, sha):
    rows = []
    for key, its in sorted(by_source.items(), key=lambda kv: gb.surname(
            bib[kv[0]][1].get("author") or bib[kv[0]][1].get("editor") or kv[0])):
        kind, f = bib[key]
        done = sum(1 for i in its if i["status"] == "checked")
        count = f'{len(its)} item{"" if len(its) == 1 else "s"}'
        tally = f"{count}, {done} checked" if done else f"{count}, none checked yet"
        cls = "all" if done == len(its) else "some" if done else "none"
        rows.append(f'<li class="source {cls}"><a href="{esc(key, quote=True)}/">'
                    f'<strong>{esc(bib_label(f, f.get("year", "")) or key)}</strong> '
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
    ap.add_argument("--out", type=Path, required=True, help="directory for the pages")
    args = ap.parse_args()

    data = json.loads(args.checks.read_text(encoding="utf-8"))
    bib = {key: (kind, f) for kind, key, f in gb.parse_bib(gb.BIB.read_text(encoding="utf-8"))}
    studies = {p.stem for p in (ROOT / "Studies").glob("*.lean")}
    sha = site_shell.git_commit()
    by_source = {}
    for item in data["items"]:
        by_source.setdefault(item["source"], []).append(item)
    missing = sorted(set(by_source) - set(bib))
    if missing:
        sys.exit("not in references.bib: " + ", ".join(missing))

    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "index.html").write_text(index_page(by_source, bib, sha), encoding="utf-8")
    for key, its in by_source.items():
        (args.out / key).mkdir(exist_ok=True)
        (args.out / key / "index.html").write_text(
            source_page(key, its, data["nodes"], bib, studies, sha, item_lines(key)),
            encoding="utf-8")
    print(f"wrote {args.out}: {len(by_source)} source{'' if len(by_source) == 1 else 's'}, "
          f"{len(data['items'])} items")


if __name__ == "__main__":
    main()
