#!/usr/bin/env python3
"""Generate typed verb class catalogues from canonical per-book JSON.

A book's catalogue of verb classes is canonical JSON at `Linglib/Data/VerbClasses/<Book>.json`, one
entry per class in the book's order: the section number and title as printed, the page on which the
class begins, the members and the members marked doubtful, and the property table. A property line
names an alternation by its section number in the book's catalogue of alternations
(`"alternation"`) or a further property (`"property"`, with `"reading"` for a derived nominal and
`"goal"` for a sentential complement), with the judgment the book's mark gives it (`"acceptable"`,
`"ungrammatical"`, `"marginal"`), its scope with the members it excepts (`"exceptions"`), and any
further printed qualifier. This emits the typed Lean module `Linglib/Data/VerbClasses/<Book>.lean`
(`<Book>.classes`). The generated Lean is never hand-edited: edit the JSON and re-run.

    python3 scripts/gen_verb_classes.py Levin1993       # (re)generate
    python3 scripts/gen_verb_classes.py --check         # verify every book, no writes (CI)

Alternation section numbers are validated against `DiathesisAlternation.number`.
"""
import sys, json, re, textwrap
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "VerbClasses"
ALTERNATIONS = ROOT / "Linglib" / "Semantics" / "ArgumentStructure" / "LevinClass" / "Alternation.lean"

JUDGMENTS = {"acceptable", "ungrammatical", "marginal"}
SCOPES = {"all", "most", "many", "some", "few"}
PLAIN = {"zeroRelatedNominal", "erNominal", "ingNominal", "processNominal", "resultNominal",
         "ableAdjective", "zeroRelatedAdjective", "extraposition", "directSpeech",
         "parentheticalUse", "infinitivalCopularClause", "measurePhrase", "pathPhrase",
         "depictivePhrase", "substanceObject", "bodyPartObject", "collectiveNPSubject",
         "impersonalPassive", "passivePrepositionChoice", "fromPhrase", "withAlternatesWithIn",
         "ofAlternatesWithOut", "unspecifiedObjectPlusLocativePP",
         "coreferentialInterpretationVaries"}
READINGS = {"active", "passive"}
GOALS = {"unspecified": ".unspecified", "absent": ".absent",
         "required object": "(.required .object)", "required toPhrase": "(.required .toPhrase)",
         "optional object": "(.optional .object)", "optional toPhrase": "(.optional .toPhrase)"}


def alternation_numbers() -> set:
    text = ALTERNATIONS.read_text(encoding="utf-8")
    body = text.split("def number : DiathesisAlternation → List ℕ")[1].split("\n\n")[0]
    return {tuple(int(x) for x in v.split(",")) for v in re.findall(r"=> \[([\d, ]+)\]", body)}


def lean_string(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def heading(line: dict, known: set) -> str:
    if "alternation" in line:
        num = tuple(line["alternation"])
        if num not in known:
            raise ValueError(f"unknown alternation section {num}")
        return f".alternation [{', '.join(map(str, num))}]"
    p = line["property"]
    if p in PLAIN:
        return f".property .{p}"
    if p == "derivedNominal" and line.get("reading") in READINGS:
        return f".property (.derivedNominal .{line['reading']})"
    if p == "sententialComplement" and line.get("goal") in GOALS:
        return f".property (.sententialComplement {GOALS[line['goal']]})"
    raise ValueError(f"bad property line {line}")


def scope(line: dict, members: list) -> str:
    exceptions = line.get("exceptions", [])
    if line["scope"] not in SCOPES or exceptions and line["scope"] != "all":
        raise ValueError(f"bad scope {line}")
    for m in exceptions:
        if m not in members:
            raise ValueError(f"excepted verb {m} is not a member: {line}")
    if exceptions:
        return f"(.all [{', '.join(lean_string(m) for m in exceptions)}])"
    return f".{line['scope']}"


def property_line(line: dict, known: set, members: list) -> str:
    if line["judgment"] not in JUDGMENTS:
        raise ValueError(f"bad judgment {line}")
    q = line.get("qualifier")
    qual = "none" if q is None else f"some {lean_string(q)}"
    return f"⟨{heading(line, known)}, .{line['judgment']}, {scope(line, members)}, {qual}⟩"


def wrap_list(items: list, indent: int, tail: int = 4) -> str:
    """A Lean list literal of `items`, wrapped at 100 columns with the given continuation indent,
    leaving `tail` columns for what follows the closing bracket."""
    lines, cur = [], "["
    for i, it in enumerate(items):
        last = i == len(items) - 1
        tok = it + (", " if not last else "]")
        if len(cur) + len(tok.rstrip()) + indent + (tail if last else 0) > 100 and cur != "[":
            lines.append(cur.rstrip())
            cur = " " * indent + tok
        else:
            cur += tok
    if not items:
        cur = "[]"
    lines.append(cur.rstrip())
    return "\n".join(lines)


def wrap_append(names: list) -> str:
    """`names` joined by `++`, wrapped at 100 columns with a four-space continuation."""
    lines, cur = [], ""
    for i, n in enumerate(names):
        tok = n + (" ++ " if i < len(names) - 1 else "")
        if len(cur) + len(tok.rstrip()) + 2 > 100:
            lines.append(cur.rstrip())
            cur = "  " + tok
        else:
            cur += tok
    lines.append(cur.rstrip())
    return "\n".join(lines)


def render_class(page: dict, known: set) -> str:
    for d in page["doubtful"]:
        if d not in page["members"]:
            raise ValueError(f"doubtful member {d} not listed on {page['number']}")
    members = wrap_list([lean_string(m) for m in page["members"]], 6)
    doubtful = wrap_list([lean_string(m) for m in page["doubtful"]], 6)
    props = wrap_list([property_line(l, known, page["members"]) for l in page["properties"]], 6)
    return (f"  {{ number := {lean_string(page['number'])}, page := {page['page']},\n"
            f"    title := {lean_string(page['title'])},\n"
            f"    members :=\n      {members},\n"
            f"    doubtful := {doubtful},\n"
            f"    properties :=\n      {props} }}")


def render(book: str, data: dict) -> str:
    known = alternation_numbers()
    chapters: dict = {}
    for p in data["classes"]:
        chapters.setdefault(p["number"].split(".")[0], []).append(p)
    blocks = []
    for ch, ps in chapters.items():
        body = ",\n".join(render_class(p, known) for p in ps)
        blocks.append(f"/-- The classes of chapter {ch}. -/\ndef chapter{ch} : List VerbClass := [\n{body}]\n")
    chain = wrap_append([f"chapter{ch}" for ch in chapters])
    description = textwrap.fill(data["description"], width=100)
    return f"""import Linglib.Data.VerbClasses.Schema

/-!
# {book}: verb classes (generated)

Auto-generated from `Linglib/Data/VerbClasses/{book}.json` by `scripts/gen_verb_classes.py`.
**Do not edit by hand**: edit the JSON and re-run the generator.

{description}

## References

* [{data['bibkey']}]
-/

namespace Data.VerbClasses.{book}

open Data.VerbClasses

{chr(10).join(blocks)}
/-- The classes, in the book's order. -/
def classes : List VerbClass :=
  {chain}

end Data.VerbClasses.{book}
"""


def generate(book: str, check: bool) -> bool:
    src = DATA_DIR / f"{book}.json"
    out = DATA_DIR / f"{book}.lean"
    data = json.loads(src.read_text(encoding="utf-8"))
    text = as_module_if_possible(render(book, data))
    if check:
        ok = out.exists() and out.read_text(encoding="utf-8") == text
        print(f"[{'ok' if ok else 'STALE'}] {out.relative_to(ROOT)}")
        return ok
    out.write_text(text, encoding="utf-8")
    print(f"[gen] {out.relative_to(ROOT)} ← {src.relative_to(ROOT)} ({len(data['classes'])} classes)")
    return True


def main(argv: list) -> int:
    check = "--check" in argv
    args = [a for a in argv if not a.startswith("--")]
    books = args or (sorted(p.stem for p in DATA_DIR.glob("*.json")) if check else [])
    if not books:
        print(__doc__)
        return 2
    return 0 if all([generate(b, check) for b in books]) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
