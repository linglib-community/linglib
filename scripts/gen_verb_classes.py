#!/usr/bin/env python3
"""Generate typed verb class catalogues from canonical per-book JSON.

A book's catalogue of verb classes is canonical JSON at `Linglib/Data/VerbClasses/<Book>.json`, one
entry per class in the book's order: the section number and title as printed, the page on which the
class begins, the members and the members marked doubtful, and the property table. A property line
names an alternation by its section number in the book's catalogue of alternations
(`"alternation"`) or a further property (`"property"`, with `"reading"` for a derived nominal and
`"goal"` for a sentential complement), with the judgment the book's mark gives it (`"acceptable"`,
`"ungrammatical"`, `"marginal"`), its scope with the members it excepts (`"exceptions"`), and any
further printed qualifier; `"id"` names the class's constructor and `"enum"` the enumeration. This
emits three typed Lean modules: `<Book>/Class.lean`, the enumeration of the classes with their
section numbers; `<Book>/Index.lean`, one constant per verb with the classes listing it, the inverse
of the member lists; and `<Book>.lean`, one constant per class page with `entry`, the enumeration's
map to them. The generated Lean is never hand-edited: edit the JSON and re-run.

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


KEYWORDS = {"at", "by", "do", "else", "end", "export", "fun", "from", "have", "if", "import", "in",
            "let", "match", "open", "show", "then", "where", "with", "deriving", "extends",
            "example", "instance", "local", "private", "protected", "section", "namespace",
            "universe", "variable", "theorem", "def", "class", "structure", "inductive", "abbrev",
            "opaque", "mutual", "calc", "suffices", "nomatch", "nofun", "try", "catch", "finally",
            "return", "for", "unless", "break", "continue", "mut", "sorry", "omit", "include",
            "partial", "unsafe", "noncomputable", "macro", "syntax", "elab", "notation", "infix",
            "prefix", "postfix", "attribute", "set_option", "termination_by", "decreasing_by",
            "public", "meta", "module", "deprecate", "recall", "repeat", "seal"}


def ident(name: str) -> str:
    """A Lean identifier for `name`, guillemet-quoted unless it is a plain non-keyword word."""
    if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name) and name not in KEYWORDS:
        return name
    return f"«{name}»"


def header(book: str, title: str, body: str, bibkey: str, imports: list) -> str:
    lines = "\n".join(f"import {i}" for i in imports)
    return f"""{lines}

/-!
# {book}: {title} (generated)

Auto-generated from `Linglib/Data/VerbClasses/{book}.json` by `scripts/gen_verb_classes.py`.
**Do not edit by hand**: edit the JSON and re-run the generator.

{textwrap.fill(body, width=100)}

## References

* [{bibkey}]
-/
"""


def render_enum(book: str, data: dict) -> str:
    """The class enumeration, one constructor per class page in the book's order, and the section
    number of each."""
    ns, name = data["enum"]["namespace"], data["enum"]["name"]
    ctors = "\n".join(f"  /-- {c['number']}, {c['title']}. -/\n  | {c['id']}" for c in data["classes"])
    numbers = "\n".join(f"  | .{c['id']} => [{', '.join(c['number'].split('.'))}]"
                        for c in data["classes"])
    body = (f"The verb classes of Part II of the book, one constructor per class page with a member "
            f"list, in the book's order and named by the class's head word or the book's label, "
            f"with the section number the book prints (`{name}.number`). The class pages are in "
            f"`Data/VerbClasses/{book}.lean` and the classes of each verb in "
            f"`Data/VerbClasses/{book}/Index.lean`.")
    return header(book, "the verb classes", body, data["bibkey"],
                  ["Mathlib.Tactic.DeriveFintype"]) + f"""
namespace {ns}

set_option maxRecDepth 4000 in
/-- The verb classes of [{data['bibkey']}] Part II. -/
inductive {name} where
{ctors}
  deriving DecidableEq, Repr, Fintype

namespace {name}

/-- The section number the book prints, as its list of numerals. -/
def number : {name} → List ℕ
{numbers}

end {name}

end {ns}
"""


def render_index(book: str, data: dict) -> str:
    """The classes of each verb, the inverse of the member lists, one constant per spelling."""
    ns, name = data["enum"]["namespace"], data["enum"]["name"]
    index: dict = {}
    for c in data["classes"]:
        for m in c["members"]:
            e = index.setdefault(m, ([], []))
            e[0].append(c["id"])
            if m in c["doubtful"]:
                e[1].append(c["id"])
    names = [ident(f) for f in index]
    if len(set(names)) != len(names):
        raise ValueError("two spellings share an identifier")
    defs = []
    for form in sorted(index, key=lambda f: (f.lower(), f)):
        cls, doubt = index[form]
        head = f"def {ident(form)} : IndexEntry {name} :="
        body = (f"⟨{lean_string(form)}, [{', '.join('.' + c for c in cls)}], "
                f"[{', '.join('.' + c for c in doubt)}]⟩")
        if len(head) + 1 + len(body) <= 100:
            defs.append(f"{head} {body}")
        else:
            cl = wrap_list(["." + c for c in cls], 4, tail=len(f", [{', '.join('.' + c for c in doubt)}]⟩"))
            defs.append(f"{head}\n  ⟨{lean_string(form)},\n    {cl}, [{', '.join('.' + c for c in doubt)}]⟩")
    body = (f"The book's verbs, each with the classes whose member lists carry it and those of them "
            f"that mark it with a question mark: the inverse of the member lists, which the book "
            f"prints as its Verb Index together with the sections of Part One that cite each verb. "
            f"A constant is named by the verb's spelling, so an English verb entry links to the "
            f"book's record of its verb by name.")
    return header(book, "the verb index", body, data["bibkey"],
                  ["Linglib.Data.VerbClasses.Schema", f"Linglib.Data.VerbClasses.{book}.Class"]) + f"""
namespace Data.VerbClasses.{book}.Index

open {ns}

{chr(10).join(defs)}

end Data.VerbClasses.{book}.Index
"""


def render_page(page: dict, known: set) -> str:
    for d in page["doubtful"]:
        if d not in page["members"]:
            raise ValueError(f"doubtful member {d} not listed on {page['number']}")
    members = wrap_list([lean_string(m) for m in page["members"]], 4)
    doubtful = wrap_list([lean_string(m) for m in page["doubtful"]], 14)
    props = wrap_list([property_line(l, known, page["members"]) for l in page["properties"]], 4)
    return (f"/-- {page['number']}, {page['title']}. -/\n"
            f"def {page['id']} : VerbClass where\n"
            f"  number := {lean_string(page['number'])}\n"
            f"  title := {lean_string(page['title'])}\n"
            f"  page := {page['page']}\n"
            f"  members :=\n    {members}\n"
            f"  doubtful := {doubtful}\n"
            f"  properties :=\n    {props}\n")


def render_pages(book: str, data: dict) -> str:
    """The class pages, one constant per class, and the enumeration's map to them."""
    ns, name = data["enum"]["namespace"], data["enum"]["name"]
    known = alternation_numbers()
    pages = "\n".join(render_page(p, known) for p in data["classes"])
    arms = "\n".join(f"  | .{c['id']} => {book}.Entry.{c['id']}" for c in data["classes"])
    return header(book, "the class pages", data["description"], data["bibkey"],
                  ["Linglib.Data.VerbClasses.Schema", f"Linglib.Data.VerbClasses.{book}.Class"]) + f"""
namespace Data.VerbClasses.{book}.Entry

open Data.VerbClasses

{pages}
end Data.VerbClasses.{book}.Entry

namespace {ns}.{name}

open Data.VerbClasses

/-- The class's page in the book. -/
def entry : {name} → VerbClass
{arms}

end {ns}.{name}
"""


def generate(book: str, check: bool) -> bool:
    src = DATA_DIR / f"{book}.json"
    data = json.loads(src.read_text(encoding="utf-8"))
    ids = [c["id"] for c in data["classes"]]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate class id")
    outs = [(DATA_DIR / book / "Class.lean", render_enum),
            (DATA_DIR / book / "Index.lean", render_index),
            (DATA_DIR / f"{book}.lean", render_pages)]
    ok = True
    for out, render in outs:
        text = as_module_if_possible(render(book, data))
        if check:
            good = out.exists() and out.read_text(encoding="utf-8") == text
            print(f"[{'ok' if good else 'STALE'}] {out.relative_to(ROOT)}")
            ok = ok and good
        else:
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
            print(f"[gen] {out.relative_to(ROOT)} ← {src.relative_to(ROOT)}")
    return ok


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
