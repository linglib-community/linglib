#!/usr/bin/env python3
"""Generate the evaluations page, the `Eval` verdicts published at linglib.io/eval/.

Every verdict on the page comes from `scripts/eval_page/Export.lean`, which reads the theorems of
`Eval` and `Lab` about an `Eval.Experiment`, instantiates them at each theory and each cell, and
reduces their right-hand sides with Lean. The page lays out whatever experiments those theorems
are about, so a new experiment needs no change here. This script adds what the page shows around
the verdicts: labels and printed numbers from `Linglib/Data/Experiments/<Paper>.json`, author-year
citations from `references.bib`, and links to each theorem's documentation. It types no verdict by
hand.

Usage, from the repository root, once `Eval` and `Lab` are built:

    python3 scripts/gen_eval_page.py --export        # run the Lean export first
    python3 scripts/gen_eval_page.py --out DIR        # write DIR/index.html and DIR/<page>/

The page is self-contained: the data is embedded in the HTML, so the file opens from disk too.
"""

import argparse
import csv
import html
import json
import os
import re
import subprocess
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from gen_bibliography_page import study_name, tex_text  # noqa: E402
import site_shell  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
EXPORT = ROOT / "scripts" / "eval_page" / "Export.lean"
TEMPLATE = ROOT / "scripts" / "eval_page" / "template.html"
DEFAULT_JSON = ROOT / ".lake" / "build" / "eval-page" / "verdicts.json"
DEFAULT_OUT = ROOT / ".lake" / "build" / "eval-page"
DATA = ROOT / "Linglib" / "Data" / "Experiments"
LIBRARIES = ["Eval", "Lab"]
# The project the page belongs to, cited from `references.bib`.
PROJECT = "chemla-spector-kalomoiros-schlenker-2026"


# ---------------------------------------------------------------- bibliography


def bib_entries(keys):
    """Author-year labels, titles and DOIs of the given `references.bib` keys."""
    text = (ROOT / "references.bib").read_text(encoding="utf-8")
    out = {}
    for key in keys:
        m = re.search(r"@\w+\{" + re.escape(key) + r",(.*?)\n\}", text, re.S)
        if not m:
            continue
        body = m.group(1)

        def field(name):
            f = re.search(r"^\s*" + name + r"\s*=\s*\{", body, re.M)
            if not f:
                return ""
            depth, i = 1, f.end()
            while depth and i < len(body):
                depth += {"{": 1, "}": -1}.get(body[i], 0)
                i += 1
            return re.sub(r"\s+", " ", body[f.end():i - 1]).strip()

        surnames = [tex_text(a.split(",")[0].strip())
                    for a in field("author").split(" and ") if a.strip()]
        who = surnames[0] + " et al." if len(surnames) > 2 else " & ".join(surnames)
        authors = ", ".join(surnames[:-1]) + " & " + surnames[-1] if len(surnames) > 1 else who
        title = tex_text(re.sub(r"\\emph\s*", "", field("title")))
        out[key] = {"key": key, "who": who, "authors": authors, "year": field("year"),
                    "title": title, "doi": field("doi"), "url": field("url")}
    return out


CITE = re.compile(r"\[([a-z0-9][a-z0-9-]*-\d{4}[a-z]?)\]('s)?")


def doc_html(doc, bib, bibliography):
    """A docstring as HTML: `[key]` links become author-year citations linked to the entry on the
    bibliography page, backticks code, asterisks emphasis."""
    doc = " ".join(doc.split())
    parts = []
    pos = 0
    for m in re.finditer(r"`([^`]*)`|\*([^*]+)\*|" + CITE.pattern, doc):
        parts.append(html.escape(doc[pos:m.start()]))
        if m.group(1) is not None:
            parts.append("<code>" + html.escape(m.group(1)) + "</code>")
        elif m.group(2) is not None:
            parts.append("<i>" + html.escape(m.group(2)) + "</i>")
        else:
            entry = bib.get(m.group(3))
            if entry:
                poss = "'s" if m.group(4) else ""
                href = html.escape(f"{bibliography}#{m.group(3)}")
                parts.append(f'<a href="{href}">{html.escape(entry["who"])}{poss} '
                             f'({html.escape(entry["year"])})</a>')
            else:
                parts.append(html.escape(m.group(0)))
        pos = m.end()
    parts.append(html.escape(doc[pos:]))
    return "".join(parts)


# ---------------------------------------------------------------- labels


def words(ident):
    return re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+", ident)


def short(name):
    return name.split(".")[-1]


def theory_label(ident):
    """`transparencyIncremental` -> "Transparency, incremental"; `limitedSymmetry` -> "Limited
    Symmetry"."""
    ws = words(short(ident))
    if len(ws) > 1 and ws[-1].lower() in ("incremental", "symmetric"):
        return " ".join(w.capitalize() for w in ws[:-1]) + ", " + ws[-1].lower()
    return " ".join(w.capitalize() for w in ws)


def sentence_label(ident):
    """`oneStep` -> "One step"; `experiment1` -> "Experiment 1"."""
    label = " ".join(words(short(ident))).lower()
    return label[:1].upper() + label[1:]


_specs = {}


def spec(paper):
    """The data file of a paper, if there is one."""
    if paper not in _specs:
        f = DATA / f"{paper}.json"
        _specs[paper] = json.loads(f.read_text(encoding="utf-8")) if f.exists() else None
    return _specs[paper]


def sample_row(ident):
    """A language's name and its row's codes, when a cell names a language of a paper's
    `Data/Structures` file (`Paper.Structures.language`)."""
    parts = ident.split(".")
    if len(parts) < 3 or parts[-2] != "Structures":
        return None
    f = ROOT / "Linglib" / "Data" / "Structures" / f"{parts[-3]}.json"
    if not f.exists():
        return None
    d = json.loads(f.read_text(encoding="utf-8"))
    name = next((x["Name"] for x in d["LanguageTable"] if x["ID"] == parts[-1]), None)
    if name is None:
        return None
    codes = {c["ID"]: c["Name"] for c in d["CodeTable"]}
    values = [v for v in d["ValueTable"] if v["Language_ID"] == parts[-1]]

    def column(p):
        return unique(codes[v["Code_ID"]] for v in values if v["Parameter_ID"] == p)

    return {"name": name, "codes": {p["ID"]: column(p["ID"]) for p in d["ParameterTable"]}}


def first_clause(doc):
    """A docstring's first clause, as the label of what it documents."""
    return re.split(r",\s|\s\(|\.\s|\.$", " ".join(doc.split()), maxsplit=1)[0]


def named_label(ctor):
    """The printed label of a constructor of a data type, `Paper.Type.level`, as the paper's data
    file gives it; a triple's language and forms; a sampled language's name; a root pattern in
    capitals (`AAB`); otherwise none."""
    triple = root_classes(ctor)
    if triple:
        return f"{triple['language']} {', '.join(triple['forms'])}"
    sampled = sample_row(ctor)
    if sampled:
        return sampled["name"]
    if re.fullmatch(r"[abc]{3}", ctor.split(".")[-1]):
        return ctor.split(".")[-1].upper()
    parts = ctor.split(".")
    if len(parts) >= 3 and spec(parts[-3]):
        for t in spec(parts[-3])["types"]:
            if t["name"] == parts[-2]:
                for lv in t["levels"]:
                    if lv["name"] == parts[-1]:
                        return lv["label"]
    return None


def level_label(ctor):
    """A constructor's label as `named_label` gives it, and otherwise its words."""
    return named_label(ctor) or " ".join(words(ctor.split(".")[-1])).lower()


def doc_href(decl, base):
    return base + decl["module"].replace(".", "/") + ".html#" + decl["name"]


# ---------------------------------------------------------------- page data


def tree_label(t):
    """An outcome as a reduced constructor tree: `none` is no observation, and a truth value is
    yes or no."""
    if t == "none":
        return None
    if isinstance(t, dict):
        return " ".join(str(tree_label(a)) for a in t["args"])
    return {"true": "yes", "false": "no"}.get(t, str(t))


_languages = {}


def language_name(glottocode):
    """A language's name, the shortest WALS gives its Glottolog code, or the code itself."""
    if not _languages:
        with open(ROOT / "Linglib" / "Data" / "WALS" / "raw" / "languages.csv",
                  encoding="utf-8") as f:
            for row in csv.DictReader(f):
                g = row["Glottocode"]
                if g and (g not in _languages or len(row["Name"]) < len(_languages[g])):
                    _languages[g] = row["Name"]
    return _languages.get(glottocode, glottocode)


def root_classes(ident):
    """The forms and root classes of a triple, when a cell names a row of a paper's
    `Data/Forms` file (`Paper.Forms.row.roots`)."""
    parts = ident.split(".")
    if "Forms" not in parts[:-1]:
        return None
    i = parts.index("Forms")
    f = ROOT / "Linglib" / "Data" / "Forms" / f"{parts[i - 1]}.json"
    if i == 0 or not f.exists():
        return None
    d = json.loads(f.read_text(encoding="utf-8"))
    row = next((r for r in d["RootClassTable"] if r["ID"] == parts[i + 1]), None)
    if not row:
        return None
    lexeme = next(x for x in d["LexemeTable"] if x["ID"] == row["Lexeme_ID"])
    forms = {x["ID"]: x for x in d["FormTable"]}
    cells = [forms[i]["Cell"] for i in row["Form_IDs"]]
    return {"language": language_name(lexeme["Language_ID"]),
            "forms": [forms[i]["Form"] for i in row["Form_IDs"]],
            "classes": "".join(row["Classes"][c] for c in cells)}


def unique(xs):
    return list(dict.fromkeys(xs))


def kebab(ident):
    return re.sub(r"(?<=[a-z])(?=[A-Z0-9])|(?<=[0-9])(?=[A-Z])", "-", ident).lower()


def slug(ident, experiment=False):
    """The address of a theory's or an experiment's page under /eval/: its name in kebab case, an
    experiment's after its paper's, a theory under development's after `lab-`."""
    parts = ident.split(".")
    if experiment:
        return f"{kebab(parts[-2])}-{kebab(parts[-1])}"
    return ("lab-" if parts[0] == "Lab" else "") + kebab(parts[-1])


def build(export, root):
    """The page's data, with links relative to `root`, the site's root seen from the page."""
    base, bibliography = root + "docs/", root + "bibliography/"
    names = export["names"]
    keys = {m.group(1) for n in names.values() for m in CITE.finditer(n["doc"])} | {PROJECT}
    bib = bib_entries(sorted(keys))

    def decl(n):
        d = names.get(n, {"name": n, "module": "", "doc": "", "rank": 1000})
        return {"name": d["name"], "short": short(d["name"]),
                "href": doc_href(d, base) if d["module"] else "",
                "doc": doc_html(d["doc"], bib, bibliography)}

    def rank(n):
        return names.get(n, {}).get("rank", 1000)

    def cell_label(x):
        """A cell's label; for a constant nothing names, its docstring's first clause."""
        doc = names.get(x, {}).get("doc", "")
        return named_label(x) or (first_clause(doc) if doc else level_label(x))

    def source(n):
        return "lab" if names.get(n, {}).get("module", "").startswith("Lab.") else "registered"

    # Theories: the registered accounts in their order, then theories under development.
    ids = {r["theory"] for r in export["verdicts"]}
    # Each with the definitions of `Linglib` and `Studies` its registration reaches.
    theories = [{"id": t, "label": theory_label(t), "source": source(t), "decl": decl(t),
                 "definitions": [decl(n) for n in export["definitions"].get(t, [])]}
                for t in sorted(ids, key=lambda t: (source(t) != "registered", rank(t), t))]

    stipulations = {r["variant"]: r for r in export["stipulations"]}
    same_parse = {r["variant"]: r for r in export["sameParse"]}
    observed = {(r["experiment"], tuple(r["cell"])): r for r in export["observed"]}

    experiments = []
    cells = {}
    for X in sorted({r["experiment"] for r in export["verdicts"]}):
        rows = [r for r in export["verdicts"] if r["experiment"] == X]
        doc = names[X]["doc"]
        key = next((m.group(1) for m in CITE.finditer(doc)), None)
        paper = names[X]["module"].split(".")[-1]
        cell_list = sorted({tuple(r["cell"]) for r in rows}, key=lambda c: [rank(x) for x in c])
        variant_list = sorted({r["variant"] for r in rows if r["variant"]}, key=rank)
        columns = []
        for c in cell_list:
            obs = observed.get((X, c))
            for v in variant_list or [None]:
                seen = tree_label(obs["observed"]) if obs else None
                # A recorded triple's observation is its root classes, a sampled language's its
                # comparative and superlative codes.
                triple = root_classes(c[0]) if len(c) == 1 else None
                sampled = sample_row(c[0]) if len(c) == 1 else None
                if triple and seen == "yes":
                    seen = triple["classes"]
                if sampled and seen == "yes":
                    seen = (f"CMPR {', '.join(sampled['codes'].get('cmpr', []))}; "
                            f"SPRL {', '.join(sampled['codes'].get('sprl', []))}")
                col = {"key": "|".join(c) + "#" + (v or ""), "cell": [cell_label(x) for x in c],
                       "observed": seen,
                       "observedTheorem": decl(obs["theorem"]) if obs else None}
                if v:
                    st = stipulations.get(v)
                    sp = same_parse.get(v)
                    col["variant"] = {
                        "id": v, "label": sentence_label(v), "decl": decl(v),
                        "stipulations": [level_label(s) for s in st["sentences"]] if st else None,
                        "stipulationsTheorem": decl(st["theorem"]) if st else None,
                        "sameAs": sentence_label(sp["as"]) if sp else None,
                        "sameAsTheorem": decl(sp["theorem"]) if sp else None}
                columns.append(col)
        for r in rows:
            k = "|".join(r["cell"]) + "#" + (r["variant"] or "")
            cells[f"{X}|{r['theory']}|{k}"] = {"verdict": r["verdict"],
                                               "theorem": decl(r["theorem"])}
        experiments.append({
            "id": X, "label": sentence_label(X), "decl": decl(X), "paper": paper,
            "cite": bib.get(key), "columns": columns, "variants": bool(variant_list)})
    experiments.sort(key=lambda e: ((e["cite"] or {}).get("year", ""), e["id"]))

    # The domains: an experiment's is its namespace under `Eval` (`Eval.Presupposition`), and a
    # theory belongs to the domains of the experiments it is scored on. Each gets its own board.
    def domain(X):
        return X.split(".")[1]

    domains = {}
    for e in experiments:
        domains.setdefault(domain(e["id"]), {"name": domain(e["id"]), "experiments": [],
                                             "theories": []})["experiments"].append(e["id"])
    scored = {(domain(r["experiment"]), r["theory"]) for r in export["verdicts"]}
    for d in domains.values():
        d["theories"] = [t["id"] for t in theories if (d["name"], t["id"]) in scored]

    # The papers a domain brings together: the studies that define its theories, and the papers
    # whose experiments score them, each linked to its study where linglib has one.
    keys_of = {study_name(k): k for k in re.findall(r"^@\w+\{([^,\s]+),",
                                                     (ROOT / "references.bib").read_text(
                                                         encoding="utf-8"), re.M)}

    def studies_of(t):
        return unique(names[n["name"]]["module"].split(".")[1] for n in t["definitions"]
                      if names[n["name"]]["module"].startswith("Studies."))

    needed = {p for t in theories for p in studies_of(t)} | {e["paper"] for e in experiments}
    cited = bib_entries(sorted(keys_of[p] for p in needed if p in keys_of))

    def paper(study):
        study_file = ROOT / "Studies" / f"{study}.lean"
        # A study named otherwise than its key is cited by its experiments.
        ref = cited.get(keys_of.get(study, ""), {}) or next(
            (e["cite"] for e in experiments if e["paper"] == study and e["cite"]), {})
        href = (f"{base}Studies/{study}.html" if study_file.exists() else
                f"https://doi.org/{ref['doi']}" if ref.get("doi") else ref.get("url", ""))
        return {"study": study, "cite": ref or None, "href": href}

    by_id = {t["id"]: t for t in theories}
    for t in theories:
        t["papers"] = [paper(p) for p in studies_of(t)]
    for d in domains.values():
        d["theoryPapers"] = [paper(p) for p in unique(p for t in d["theories"]
                                                      for p in studies_of(by_id[t]))]
        d["dataPapers"] = [paper(p) for p in unique(e["paper"] for e in experiments
                                                    if e["id"] in d["experiments"])]

    # The printed numbers behind the observations, from the papers' data files.
    papers = {}
    for e in experiments:
        s = spec(e["paper"])
        if s and e["paper"] not in papers:
            papers[e["paper"]] = {
                "cite": e["cite"], "description": s["meta"]["description"],
                "tables": [{"name": t["name"], "doc": t["doc"], "locator": t.get("locator", ""),
                            "verified": t.get("verified", ""), "rows": t["rows"]}
                           for t in s["tables"]],
                "experiments": [x["decl"] for x in experiments if x["paper"] == e["paper"]]}

    # Each theory and experiment has a page of its own.
    slugs = {t["id"]: slug(t["id"]) for t in theories}
    slugs.update({e["id"]: slug(e["id"], experiment=True) for e in experiments})
    assert len(set(slugs.values())) == len(slugs), "two pages would share an address"
    return {"theories": theories, "experiments": experiments, "domains": sorted(
                domains.values(), key=lambda d: d["name"]),
            "slugs": slugs, "cells": cells, "papers": papers,
            "project": bib.get(PROJECT)}


# ---------------------------------------------------------------- running


def run_export(json_path):
    """Run the Lean export on every module of `Eval` and `Lab`: the export's body, after a line
    importing them all, so that Lean reads their theorems as it elaborates the file."""
    modules = sorted(".".join(f.relative_to(ROOT).with_suffix("").parts)
                     for lib in LIBRARIES for f in (ROOT / lib).rglob("*.lean"))
    body = EXPORT.read_text(encoding="utf-8")
    header = "import Lean\n"
    assert body.startswith(header)
    source = header + "".join(f"import {m}\n" for m in modules) + body[len(header):]
    json_path.parent.mkdir(parents=True, exist_ok=True)
    composed = json_path.parent / "Export.lean"
    composed.write_text(source, encoding="utf-8")
    env = dict(os.environ, EVAL_PAGE_JSON=str(json_path))
    if subprocess.run(["lake", "env", "lean", str(composed)], cwd=ROOT, env=env).returncode:
        sys.exit("the Lean export failed")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--export", action="store_true", help="run the Lean export first")
    ap.add_argument("--json", type=Path, default=DEFAULT_JSON, help="the Lean export's output")
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT,
                    help="directory for index.html and the pages of theories and experiments")
    args = ap.parse_args()

    if args.export:
        run_export(args.json)

    export = json.loads(args.json.read_text(encoding="utf-8"))
    template = TEMPLATE.read_text(encoding="utf-8")
    title = "<title>Evaluations | Linglib</title>"
    assert template.count(title) == 1
    sha = site_shell.git_commit()

    def write(path, page, root, name):
        data = json.dumps(page, ensure_ascii=False).replace("</", "<\\/")
        out = (site_shell.render(template, root, "Evaluations", sha)
               .replace(title, f"<title>{html.escape(name)} | Linglib</title>")
               .replace("/*EVAL_DATA*/{}", data))
        path.mkdir(parents=True, exist_ok=True)
        (path / "index.html").write_text(out, encoding="utf-8")

    # The boards at /eval/, and a page for each theory and experiment one level down.
    board = build(export, "../")
    write(args.out, {**board, "view": None, "up": ""}, "../", "Evaluations")
    pages = build(export, "../../")
    for t in pages["theories"]:
        write(args.out / pages["slugs"][t["id"]],
              {**pages, "view": {"kind": "theory", "id": t["id"]}, "up": "../"}, "../../",
              t["label"] + (" (Lab)" if t["source"] == "lab" else ""))
    for e in pages["experiments"]:
        name = f"{e['cite']['who']} ({e['cite']['year']}), {e['label']}" if e["cite"] else e["label"]
        write(args.out / pages["slugs"][e["id"]],
              {**pages, "view": {"kind": "experiment", "id": e["id"]}, "up": "../"}, "../../", name)
    print(f"wrote {args.out}: {len(board['experiments'])} experiments, "
          f"{len(board['theories'])} theories, {len(board['cells'])} verdicts, "
          f"{len(board['slugs'])} pages")


if __name__ == "__main__":
    main()
