#!/usr/bin/env python3
"""Record and verify human checks that Lean statements are faithful to their sources.

Each file `checks/<bib-key>.toml` lists the items of one source, its numbered definitions,
results and data, and the Lean declarations that state each one (`checks/README.md`). A human who
has read the source and the Lean signs an item, and the sign-off records a hash of the item's
statement closure: the types of its declarations, and the types and bodies of every
project definition those statements mention, but no proofs. `lake exe checkClosure` computes the
closures.

An item is

* `checked` when its newest sign-off matches the current hash and every item covering a
  definition in its closure is checked too;
* `relies` when it is signed and current but such an item is not checked;
* `stale` when its statement closure has changed since the sign-off;
* `unchecked` when it has no sign-off;
* `missing` when the source's item has no Lean statement yet;
* `broken` when one of its declarations does not resolve;
* `unproved` when one of its declarations rests, through its proof or the definitions it uses, on
  `sorry` or on an axiom beyond Lean's standard three, whatever its sign-off says.

The checked items form the reviewed core: their declarations, and the project definitions their
statements use. Since an item is checked only if the items it relies on are, nothing in the core
depends for its meaning on anything outside it.

Usage, from the repository root:

    python3 scripts/checks.py status [SOURCE ...]
    python3 scripts/checks.py status --json   # every item, for the docs pages
    python3 scripts/checks.py diff SOURCE ITEM
    python3 scripts/checks.py core [--json]
    python3 scripts/checks.py sign SOURCE (--all | --items ID,ID,...) --by GITHUB_HANDLE
    python3 scripts/checks.py selftest   # after changing `checkClosure` or Lean
    python3 scripts/checks.py renames    # after upgrading Lean or Mathlib
    python3 scripts/checks.py gloss SOURCE --command CMD [--items ID,ID,...]

`gloss` prints, for each item, a blind English gloss of its Lean statement, to help a reviewer who
does not read Lean. A model of the reviewer's choice, run by the shell command CMD, writes it from
the statement closure alone, with the declarations' names hidden and no access to docstrings,
files or tools, so that it says what the Lean says rather than what it is meant to say. A gloss is an aid to review and never evidence for a
sign-off: the sign-off is of the Lean. Glosses are cached in `.cache/checks/glosses/`.

`renames` records in `checks/renames.toml` the renames of Lean and Mathlib constants that the
items' statements use, under the old name or the new one, where the old name is a deprecated alias
of the new. In the hashed terms all the names of a renamed constant stand for one, so a sign-off
stays current when a statement switches to the new name. Run it after an upgrade, while the
aliases still exist; `status` says when there is something to record.

Sign-offs are made by people. `sign` refuses to run inside an agent session (`CLAUDECODE`).
"""

import argparse
import concurrent.futures
import copy
import datetime
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECKS = ROOT / "checks"
LIBRARIES = ["Linglib", "Studies"]
KINDS = {"definition", "result", "datum"}
RELATIONS = {"exact", "generalizes", "specializes", "variant", "refutes", "missing"}
HASH_VERSION = "v3"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RENAMES = CHECKS / "renames.toml"
LEDGER = CHECKS / "ledger"
LEDGER_NODES = LEDGER / "nodes"
# Names that are not a person's: a bot account, or an AI agent. A heuristic that stops accidents.
AGENT_NAME = re.compile(r"(?i)\[bot\]|\bbot\b|-bot\b|claude|copilot|codex|gemini|chatgpt|\bgpt\b")
LOGIN = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?")


def load_renames():
    """The recorded renames of Lean and Mathlib constants, oldest first."""
    if not RENAMES.exists():
        return []
    with RENAMES.open("rb") as f:
        renames = tomllib.load(f).get("rename", [])
    for r in renames:
        if not (isinstance(r.get("old"), str) and isinstance(r.get("new"), str)
                and r["old"] != r["new"]):
            sys.exit(f"{RENAMES}: a rename needs distinct `old` and `new` names, not {r}")
    return renames


def canonical_names(renames):
    """The name that stands for each renamed constant in a term, for every constant that is not
    its own: all the names linked by renames stand for one, the earliest recorded. Since a rename
    is recorded under its old name first, a term that uses a constant's old name keeps its hash
    when it switches to the new one. Recording a rename changes the name standing for a constant
    only if the rename adds the constant to a group, or joins its group to an earlier one, and
    `renames` reports any sign-off that this makes stale."""
    parent, order = {}, {}

    def find(n):
        while parent[n] != n:
            parent[n] = parent[parent[n]]
            n = parent[n]
        return n

    for r in renames:
        for n in (r["old"], r["new"]):
            parent.setdefault(n, n)
            order.setdefault(n, len(order))
        a, b = find(r["old"]), find(r["new"])
        if a != b:
            first, second = (a, b) if order[a] < order[b] else (b, a)
            parent[second] = first
    return {n: find(n) for n in parent if find(n) != n}


def unrecorded(data, renames):
    """The renames that `checkClosure` found among the closures' constants and that are not yet
    recorded."""
    known = {(r["old"], r["new"]) for r in renames}
    return [a for a in data.get("aliases", []) if (a["old"], a["new"]) not in known]


def short_hash(data):
    """The name of a ledger file or node: the start of the SHA-256 of its bytes."""
    return hashlib.sha256(data).hexdigest()[:16]


def load_ledger():
    """The ledger entries of every item, oldest first, keyed by `(source, id)`. A file is named by
    the hash of its contents, so that an edited entry is found."""
    entries = {}
    for path in sorted(LEDGER.glob("*.toml")):
        raw = path.read_bytes()
        if path.stem != short_hash(raw):
            sys.exit(f"{path}: its name is not the hash of its contents")
        sign = tomllib.loads(raw.decode("utf-8"))
        for item in sign.get("item", []):
            entries.setdefault((sign["source"], item["id"]), []).append({
                "by": sign["by"], "recorded_by": sign["recorded_by"], "via": sign.get("via"),
                "date": sign["date"], "hash": item["hash"], "nodes": item.get("nodes", []),
                "file": path.name})
    for found in entries.values():
        found.sort(key=lambda e: e["date"])
    return entries


def node_text(digest):
    """The text of a declaration as a signer read it, from the ledger's node store."""
    path = LEDGER_NODES / f"{digest}.txt"
    raw = path.read_bytes()
    if short_hash(raw) != digest:
        sys.exit(f"{path}: its name is not the hash of its contents")
    return raw.decode("utf-8")


def load_sources(keys=None):
    """The check files, keyed by source, each with its path and items."""
    sources = {}
    for path in sorted(CHECKS.glob("*.toml")):
        if path == RENAMES:
            continue
        with path.open("rb") as f:
            data = tomllib.load(f)
        key = data.get("source")
        if key != path.stem:
            sys.exit(f"{path}: `source = {key!r}` does not match the file name")
        sources[key] = {"path": path, "items": data.get("item", [])}
    ledger = load_ledger()
    for key, src in sources.items():
        for item in src["items"]:
            if "check" in item:
                sys.exit(f"{src['path']}: {item.get('id')} has `[[item.check]]` blocks, which "
                         "the ledger replaced: sign-offs are kept in checks/ledger/")
            item["check"] = ledger.get((key, item.get("id")), [])
    if keys:
        unknown = set(keys) - sources.keys()
        if unknown:
            sys.exit(f"no check file for: {', '.join(sorted(unknown))}")
    return sources


def validate(sources):
    bib = (ROOT / "references.bib").read_text(encoding="utf-8")
    problems = []
    for key, src in sources.items():
        if not re.search(r"@\w+\{" + re.escape(key) + r",", bib):
            problems.append(f"{key}: not in references.bib")
        ids = set()
        for item in src["items"]:
            cid = item.get("id", "?")
            if cid in ids:
                problems.append(f"{key}/{cid}: duplicate id")
            ids.add(cid)
            kind = item.get("kind")
            if kind not in KINDS:
                problems.append(f"{key}/{cid}: kind {kind!r} is not one of {sorted(KINDS)}")
            relation = item.get("relation")
            if relation not in RELATIONS:
                problems.append(
                    f"{key}/{cid}: relation {relation!r} is not one of {sorted(RELATIONS)}")
            if relation == "refutes" and kind != "result":
                problems.append(f"{key}/{cid}: only a result can be refuted, not a {kind}")
            if relation not in ("exact", "missing") and not item.get("notes"):
                problems.append(f"{key}/{cid}: a `{relation}` item needs notes")
            if relation == "missing" and item.get("decls"):
                problems.append(f"{key}/{cid}: a `missing` item has no decls")
            if relation != "missing" and not item.get("decls"):
                problems.append(f"{key}/{cid}: no decls")
    return problems


def candidate_modules(names):
    """The modules whose source may declare one of the names."""
    lasts = {n.split(".")[-1] for n in names}
    pattern = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
        r"(?:def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque|axiom)\s+"
        r"(?:_root_\.)?([^\s(:{\[]+)",
        re.M,
    )
    modules = set()
    for lib in LIBRARIES:
        for path in (ROOT / lib).rglob("*.lean"):
            text = path.read_text(encoding="utf-8")
            if any(m.group(1).split(".")[-1] in lasts for m in pattern.finditer(text)):
                modules.add(".".join(path.relative_to(ROOT).with_suffix("").parts))
    return sorted(modules)


def check_closure(modules, names, renames):
    """The output of `checkClosure` on built modules, with the recorded renames applied."""
    with tempfile.NamedTemporaryFile("w", suffix=".json") as f:
        json.dump(canonical_names(renames), f)
        f.flush()
        out = subprocess.run(["lake", "exe", "checkClosure", "--renames", f.name, *modules, "--",
                              *names], cwd=ROOT, check=True, capture_output=True, text=True).stdout
    return json.loads(out)


def closures(names, renames=None):
    """Run `checkClosure` on the names, building the modules that may declare them."""
    if not names:
        return {"roots": {}, "nodes": {}, "aliases": []}
    modules = candidate_modules(names)
    if not modules:
        return {"roots": {n: {"found": False} for n in names}, "nodes": {}, "aliases": []}
    build = subprocess.run(["lake", "build", "checkClosure", *modules], cwd=ROOT,
                           capture_output=True, text=True)
    if build.returncode:
        errors = [l for l in build.stdout.splitlines() if l.startswith("error")]
        sys.exit("the modules declaring the items do not build:\n" + "\n".join(errors[:20]))
    return check_closure(modules, names, load_renames() if renames is None else renames)


def item_hash(item, data):
    """The hash of an item's statement closure."""
    h = hashlib.sha256(HASH_VERSION.encode())
    closure = set()
    for name in sorted(item["decls"]):
        root = data["roots"][name]
        h.update(f"\0root\0{name}\0{data['nodes'][name]['term']}".encode())
        closure.update(root["closure"])
    for name in sorted(closure - set(item["decls"])):
        h.update(f"\0node\0{name}\0{data['nodes'][name]['term']}".encode())
    return h.hexdigest()[:16]


def evaluate(sources, renames=None):
    """The status and details of every item, keyed by `(source, id)`, and the closures."""
    names = sorted({d for src in sources.values() for c in src["items"]
                    for d in c.get("decls", [])})
    data = closures(names, renames)
    covering = {}
    for key, src in sources.items():
        for item in src["items"]:
            for d in item.get("decls", []):
                covering.setdefault(d, set()).add((key, item["id"]))

    own, info = {}, {}
    for key, src in sources.items():
        for item in src["items"]:
            ref = (key, item["id"])
            decls = item.get("decls", [])
            info[ref] = {"item": item, "deps": set(), "hash": None}
            if item.get("relation") == "missing" or not decls:
                own[ref] = "missing"
                continue
            unresolved = [d for d in decls if not data["roots"].get(d, {}).get("found")]
            if unresolved:
                own[ref] = "broken"
                info[ref]["unresolved"] = unresolved
                continue
            digest = item_hash(item, data)
            info[ref]["hash"] = digest
            closure = {n for d in decls for n in data["roots"][d]["closure"]}
            info[ref]["deps"] = {c for n in closure for c in covering.get(n, ())} - {ref}
            info[ref]["closure"] = closure | set(decls)
            info[ref]["files"] = sorted({data["nodes"][n]["module"] for n in closure | set(decls)})
            checks = item.get("check", [])
            if not checks:
                own[ref] = "unchecked"
            elif checks[-1].get("hash") != digest:
                own[ref] = "stale"
            else:
                own[ref] = "signed"
            info[ref]["signoff"] = own[ref]
            axioms = {a for d in decls for a in data["roots"][d]["axioms"]} - STANDARD_AXIOMS
            if axioms:
                info[ref]["axioms"] = sorted(axioms)
                own[ref] = "unproved"

    status = {}

    def effective(ref, seen=()):
        if ref in status:
            return status[ref]
        if own[ref] != "signed":
            return own[ref]
        if ref in seen:
            return "checked"
        blocking = [d for d in info[ref]["deps"] if effective(d, seen + (ref,)) != "checked"]
        info[ref]["blocking"] = sorted(blocking)
        return "relies" if blocking else "checked"

    for ref in own:
        status[ref] = effective(ref)
    return status, info, data


def status_json(sources, status, info):
    """Every item with its status and newest sign-off, as `gen_docs_pages.py --checks` reads it."""
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, check=True,
                            capture_output=True, text=True).stdout.strip()
    items = []
    for (key, cid), st in status.items():
        item = info[(key, cid)]["item"]
        last = (item.get("check") or [None])[-1]
        items.append({
            "source": key, "id": cid, "kind": item.get("kind"), "label": item.get("label", cid),
            "relation": item.get("relation"), "notes": item.get("notes", "").strip(),
            "decls": item.get("decls", []), "status": st,
            "check": last and {"by": last["by"], "recorded_by": last["recorded_by"],
                               "via": last["via"], "date": last["date"].date().isoformat()},
            "blocking": [f"{k}/{c}" for k, c in info[(key, cid)].get("blocking", [])]})
    return {"commit": commit, "items": items}


def cmd_status(args):
    sources = load_sources(args.sources)
    problems = validate(sources)
    if args.json:
        if problems:
            sys.exit("invalid check files:\n" + "\n".join(problems))
        status, info, _ = evaluate(sources)
        print(json.dumps(status_json(sources, status, info), indent=2))
        return 0
    for p in problems:
        print(f"invalid: {p}")
    status, info, data = evaluate(sources)
    pending = unrecorded(data, load_renames())
    if pending:
        print(f"{len(pending)} rename(s) of constants these items use are not recorded, and stale "
              "sign-offs may be current once they are: run `checks.py renames`", file=sys.stderr)
    if args.ci:
        for (key, cid), st in status.items():
            if st == "stale":
                print(f"::warning title=Stale sign-off::{key}/{cid}: its statement has changed "
                      f"since it was signed; `checks.py diff {key} {cid}` shows how")
            if st == "broken":
                print(f"::error title=Broken item::{key}/{cid}: "
                      f"{', '.join(info[(key, cid)]['unresolved'])} does not resolve")
    for key in sources if not args.sources else args.sources:
        refs = [r for r in status if r[0] == key]
        counts = {}
        for r in refs:
            counts[status[r]] = counts.get(status[r], 0) + 1
        summary = ", ".join(f"{n} {s}" for s, n in sorted(counts.items()))
        print(f"{key}: {summary}")
        for r in refs:
            line = f"  {status[r]:<10} {r[1]}"
            if status[r] == "relies":
                line += "  (relies on " + ", ".join(b[1] if b[0] == key else f"{b[0]}/{b[1]}"
                                                    for b in info[r]["blocking"]) + ")"
            if status[r] == "broken":
                line += "  (unresolved: " + ", ".join(info[r]["unresolved"]) + ")"
            if status[r] == "unproved":
                line += f"  ({info[r]['signoff']}; rests on " + ", ".join(info[r]["axioms"]) + ")"
            print(line)
    return 1 if problems or (args.ci and "broken" in status.values()) else 0


def cmd_core(args):
    sources = load_sources()
    status, info, data = evaluate(sources)
    items = sorted(r for r in status if status[r] == "checked")
    decls = {}
    for ref in items:
        for name in info[ref]["closure"]:
            node = data["nodes"][name]
            entry = decls.setdefault(name, {"module": node["module"], "kind": node["kind"],
                                            "states": []})
            if name in info[ref]["item"]["decls"]:
                entry["states"].append(f"{ref[0]}/{ref[1]}")
    modules = sorted({d["module"] for d in decls.values()})
    if args.json:
        print(json.dumps({"items": [f"{k}/{c}" for k, c in items], "modules": modules,
                          "declarations": dict(sorted(decls.items()))}, indent=2))
        return 0
    print(f"{len(items)} checked item(s) from {len({k for k, _ in items})} source(s): "
          f"{len(decls)} declaration(s) in {len(modules)} module(s)")
    for module in modules:
        print(module)
        for name, d in sorted(decls.items()):
            if d["module"] == module:
                states = f"  (states {', '.join(d['states'])})" if d["states"] else ""
                print(f"  {d['kind']:<11} {name}{states}")
    return 0


def cmd_diff(args):
    sources = load_sources([args.source])
    status, info, data = evaluate(sources)
    ref = (args.source, args.item)
    if ref not in info:
        sys.exit(f"no item {args.item} in {args.source}")
    checks = info[ref]["item"]["check"]
    if not checks:
        sys.exit(f"{args.item} has never been signed")
    last = checks[-1]
    print(f"{args.item}: {status[ref]}; signed by {last['by']} on {last['date']:%Y-%m-%d}")
    if status[ref] != "stale":
        return 0
    signed = {n["name"]: n for n in last["nodes"]}
    now = info[ref]["closure"]
    for name in sorted(signed.keys() - now):
        print(f"\n{name}: no longer in the statement's closure")
    for name in sorted(now - signed.keys()):
        print(f"\n{name}: now in the statement's closure")
    for name in sorted(now & signed.keys()):
        before, after = node_text(signed[name]["text"]), data["nodes"][name]["text"]
        if before != after:
            print()
            print("\n".join(difflib.unified_diff(before.splitlines(), after.splitlines(),
                                                  f"{name} (signed)", f"{name} (now)",
                                                  lineterm="")))
        elif signed[name]["term"] != short_hash(data["nodes"][name]["term"].encode()):
            print(f"\n{name}: the printed text is the same, but the term differs, as in a "
                  "bound variable's type that printing hides")
    return 0


def ledger_problems(changes, author, author_type):
    """What is wrong with a change to the ledger, given as `(status, path)` pairs from `git diff
    --name-status`, made by the GitHub account `author`."""
    problems = []
    prefix = f"checks/{LEDGER.name}/"
    for state, path in changes:
        if state != "A":
            problems.append(f"{path}: the ledger is append-only, but this file is "
                            f"{'deleted' if state == 'D' else 'changed'}")
            continue
        raw = (ROOT / path).read_bytes()
        stem = Path(path).stem
        if stem != short_hash(raw):
            problems.append(f"{path}: its name is not the hash of its contents")
        if path.startswith(prefix + "nodes/") or not path.endswith(".toml"):
            continue
        try:
            sign = tomllib.loads(raw.decode("utf-8"))
        except (tomllib.TOMLDecodeError, UnicodeDecodeError) as e:
            problems.append(f"{path}: not valid TOML: {e}")
            continue
        problems += entry_problems(path, sign, author, author_type)
    return problems


def entry_problems(path, sign, author, author_type):
    """What is wrong with one new ledger file."""
    problems = []
    by, recorded_by, via = sign.get("by"), sign.get("recorded_by"), sign.get("via")
    source = sign.get("source")
    if not all(isinstance(v, str) and v for v in (by, recorded_by, source)):
        return [f"{path}: `source`, `by` and `recorded_by` must all be given"]
    if not isinstance(sign.get("date"), datetime.datetime):
        problems.append(f"{path}: `date` must be a date and time")
    if recorded_by.lower() != author.lower():
        problems.append(f"{path}: recorded_by is {recorded_by}, but the pull request is by "
                        f"{author}")
    if author_type == "Bot" or AGENT_NAME.search(recorded_by):
        problems.append(f"{path}: a sign-off is recorded by a person, not {recorded_by}")
    if AGENT_NAME.search(by):
        problems.append(f"{path}: a sign-off is made by a person, not {by}")
    if by == recorded_by:
        if via:
            problems.append(f"{path}: `via` is for a sign-off recorded for someone else")
    elif not via:
        problems.append(f"{path}: a sign-off recorded for someone else needs `via`")
    ids = set()
    source_file = CHECKS / f"{source}.toml"
    if source_file.exists():
        ids = {i.get("id") for i in tomllib.loads(source_file.read_text("utf-8")).get("item", [])}
    else:
        problems.append(f"{path}: no check file for {source}")
    if not sign.get("item"):
        problems.append(f"{path}: it signs no item")
    for item in sign.get("item", []):
        if ids and item.get("id") not in ids:
            problems.append(f"{path}: {source} has no item {item.get('id')}")
        if not isinstance(item.get("hash"), str) or not item.get("nodes"):
            problems.append(f"{path}: item {item.get('id')} needs a `hash` and its `nodes`")
        for node in item.get("nodes", []):
            file = LEDGER_NODES / f"{node.get('text')}.txt"
            if not file.exists():
                problems.append(f"{path}: the text {node.get('text')} of {node.get('name')} "
                                "is not in the ledger")
            elif short_hash(file.read_bytes()) != node["text"]:
                problems.append(f"{file.name}: its name is not the hash of its contents")
    return problems


def cmd_verify_ledger(args):
    out = subprocess.run(["git", "diff", "--name-status", "--no-renames", f"{args.base}...HEAD",
                          "--", f"checks/{LEDGER.name}"], cwd=ROOT, capture_output=True,
                         text=True)
    if out.returncode:
        sys.exit(f"git diff against {args.base} failed:\n{out.stderr}")
    changes = [tuple(line.split("\t", 1)) for line in out.stdout.splitlines()]
    problems = ledger_problems(changes, args.author, args.author_type)
    for p in problems:
        print(f"::error::{p}")
    print(f"{len(changes)} change(s) to the ledger, {len(problems)} problem(s)")
    return 1 if problems else 0


RENAMES_HEADER = """\
# Renames of Lean and Mathlib constants, recorded by `python3 scripts/checks.py renames`.
#
# Each is a constant that an upgrade renamed, keeping the old name as a deprecated alias of the
# new one, so that the two mean the same. In the terms that sign-offs hash, every name linked by
# these renames stands for the earliest recorded, so a sign-off stays current when a statement
# switches from a constant's old name to its new one, even after the alias is removed. Entries are
# never removed or reordered, since that would change the hashes.
"""


def cmd_renames(args):
    sources = load_sources()
    problems = validate(sources)
    if problems:
        sys.exit("fix the check files first:\n" + "\n".join(problems))
    renames = load_renames()
    before, info_before, data = evaluate(sources, renames)
    pending = unrecorded(data, renames)
    if not pending:
        print("every rename of the constants the items use is recorded")
        return 0
    text = RENAMES.read_text(encoding="utf-8") if RENAMES.exists() else RENAMES_HEADER
    for a in pending:
        since = f'\nsince = "{a["since"]}"' if a.get("since") else ""
        text += f'\n[[rename]]\nold   = "{a["old"]}"\nnew   = "{a["new"]}"{since}\n'
        print(f"recorded {a['old']} -> {a['new']}")
    RENAMES.write_text(text, encoding="utf-8")
    _, info_after, _ = evaluate(sources, load_renames())
    for ref in info_before:
        was, now = info_before[ref].get("signoff"), info_after[ref].get("signoff")
        if was != now and "signed" in (was, now):
            print(f"  {ref[0]}/{ref[1]}: {was} -> {now}")
    return 0


def toml_string(s):
    """A TOML basic string, which JSON's escapes also write."""
    return json.dumps(s, ensure_ascii=False)


def ledger_file(source, by, recorded_by, via, when, signed):
    """The text of a ledger file, and the node texts it needs, for the items just signed, given as
    `(id, hash, nodes)`, each node `(name, term, text)`."""
    lines = [f"source = {toml_string(source)}", f"by = {toml_string(by)}",
             f"recorded_by = {toml_string(recorded_by)}"]
    if via:
        lines.append(f"via = {toml_string(via)}")
    lines.append(f"date = {when}")
    for cid, digest, nodes in signed:
        lines += ["", "[[item]]", f"id = {toml_string(cid)}", f"hash = {toml_string(digest)}",
                  "nodes = ["]
        for name, term, text in nodes:
            lines.append(f"  {{ name = {toml_string(name)}, term = "
                         f'"{short_hash(term.encode())}", text = "{short_hash(text.encode())}" }},')
        lines.append("]")
    return "\n".join(lines) + "\n"


def cmd_sign(args):
    if os.environ.get("CLAUDECODE"):
        sys.exit("sign-offs are made by people: run `sign` yourself, outside an agent session")
    by = args.by.strip()
    recorded_by = args.recorded_by or by
    if not by or any(c in by for c in '\n\r"\\'):
        sys.exit(f"--by takes the reviewer's name or GitHub handle, not {args.by!r}")
    if not LOGIN.fullmatch(recorded_by):
        sys.exit("--recorded-by takes your GitHub handle, and defaults to --by, which is not one: "
                 f"{recorded_by!r}")
    if by != recorded_by and not args.via:
        sys.exit("a sign-off recorded for someone else needs --via, saying how they made the "
                 "check known, such as `email` or `issue #123`")
    if args.via and by == recorded_by:
        sys.exit("--via is for a sign-off recorded for someone else")
    return record(args, by, recorded_by)


def record(args, by, recorded_by):
    """Write the ledger file for the items `args` selects, and the node texts it needs."""
    sources = load_sources([args.source])
    problems = [p for p in validate(sources)]
    if problems:
        sys.exit("fix the check file first:\n" + "\n".join(problems))
    status, info, data = evaluate(sources)
    # A rename recorded after a sign-off would change the name standing for a constant that the
    # signed statement already uses under its new name, and make the sign-off stale.
    pending = unrecorded(data, load_renames())
    if pending:
        sys.exit("record the renames of the constants these items use first, with "
                 "`checks.py renames`: " + ", ".join(f"{a['old']} -> {a['new']}" for a in pending))
    items = sources[args.source]["items"]
    ids = [c["id"] for c in items] if args.all else args.items.split(",")
    signed = []
    for cid in ids:
        ref = (args.source, cid)
        if ref not in status:
            sys.exit(f"no item {cid} in {args.source}")
        if status[ref] in ("missing", "broken"):
            if args.all:
                continue
            sys.exit(f"{cid} is {status[ref]} and cannot be signed")
        if info[ref]["signoff"] == "signed" and args.all:
            continue
        nodes = [(n, data["nodes"][n]["term"], data["nodes"][n]["text"])
                 for n in sorted(info[ref]["closure"])]
        signed.append((cid, info[ref]["hash"], nodes))
    if not signed:
        print("nothing to sign")
        return 0
    when = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    text = ledger_file(args.source, by, recorded_by, args.via, when, signed)
    LEDGER_NODES.mkdir(parents=True, exist_ok=True)
    for _, _, nodes in signed:
        for _, _, node in nodes:
            path = LEDGER_NODES / f"{short_hash(node.encode())}.txt"
            if not path.exists():
                path.write_text(node, encoding="utf-8")
    path = LEDGER / f"{short_hash(text.encode())}.toml"
    path.write_text(text, encoding="utf-8")
    print(f"signed {len(signed)} item(s) of {args.source} in checks/{LEDGER.name}/{path.name}: "
          f"{', '.join(c for c, _, _ in signed)}")
    return 0


GLOSS_PROMPT = ROOT / "scripts" / "checks" / "gloss-prompt.md"
GLOSS_CACHE = ROOT / ".cache" / "checks" / "glosses"


def gloss_input(item, data):
    """The text a gloss is written from, and the names it hides.

    The item's declarations become T1, T2, …, followed by the project declarations their statements
    use, each after those it mentions. The namespace of the study the declarations come from is
    dropped, since it names the source. Docstrings are left out."""
    nodes = data["nodes"]
    targets = item["decls"]
    closure = set()
    for name in targets:
        closure.update(data["roots"][name]["closure"])
    names = sorted(closure - set(targets))
    studies = {nodes[n]["module"].split(".")[-1] for n in [*targets, *names]
               if nodes[n]["module"].startswith("Studies.")}
    table = {t: f"T{i + 1}" for i, t in enumerate(targets)}
    for n in names:
        if n.split(".")[0] in studies:
            table[n] = n.split(".", 1)[1]
    keys = sorted(table, key=len, reverse=True)
    pattern = re.compile(r"(?<![\w.])(" + "|".join(map(re.escape, keys)) + r")(?![\w])")
    hide = lambda text: pattern.sub(lambda m: table[m.group(1)], text)

    mentions = {n: {m for m in names if m != n and re.search(
        r"(?<![\w.])" + re.escape(m) + r"(?![\w])", nodes[n]["text"])} for n in names}
    order, done = [], set()
    def visit(n, path=()):
        if n in done or n in path:
            return
        for m in sorted(mentions[n]):
            visit(m, path + (n,))
        done.add(n)
        order.append(n)
    for n in names:
        visit(n)

    parts = ["## Target declarations\n"]
    for t in targets:
        parts.append(f"### {table[t]} ({nodes[t]['kind']})\n```lean\n{hide(nodes[t]['text'])}\n```\n")
    parts.append("## Project declarations the targets use\n")
    for n in order:
        parts.append(f"### {hide(n)} ({nodes[n]['kind']})\n```lean\n{hide(nodes[n]['text'])}\n```\n")
    return "\n".join(parts), {table[t]: t for t in targets}


def write_gloss(text, command):
    """A gloss of `text` by the shell command `command`, which reads the text on standard input and
    the prompt from the file named by `$GLOSS_PROMPT`, and writes the gloss to standard output."""
    out = subprocess.run(command, shell=True, input=text, cwd=ROOT, capture_output=True, text=True,
                         env={**os.environ, "GLOSS_PROMPT": str(GLOSS_PROMPT)})
    gloss = out.stdout.strip()
    if out.returncode or not gloss.startswith("### T1"):
        detail = (gloss or out.stderr).strip()
        raise RuntimeError(detail.splitlines()[0] if detail else f"exit {out.returncode}")
    return gloss


def cmd_gloss(args):
    sources = load_sources([args.source])
    items = [i for i in sources[args.source]["items"] if i.get("decls")]
    if args.items:
        wanted = args.items.split(",")
        unknown = set(wanted) - {i["id"] for i in items}
        if unknown:
            sys.exit(f"no item with declarations: {', '.join(sorted(unknown))}")
        items = [i for i in items if i["id"] in wanted]
    data = closures(sorted({d for i in items for d in i["decls"]}))
    missing = sorted(d for i in items for d in i["decls"] if not data["roots"][d]["found"])
    if missing:
        sys.exit("declarations not found: " + ", ".join(missing))

    prompt = GLOSS_PROMPT.read_text(encoding="utf-8")
    GLOSS_CACHE.mkdir(parents=True, exist_ok=True)
    jobs = {}
    for item in items:
        text, names = gloss_input(item, data)
        key = hashlib.sha256("\0".join([args.command, prompt, text]).encode()).hexdigest()[:16]
        jobs[item["id"]] = (key, text, names)

    def ensure(cid):
        key, text, names = jobs[cid]
        path = GLOSS_CACHE / f"{key}.json"
        if path.exists() and not args.refresh:
            return
        gloss = write_gloss(text, args.command)
        path.write_text(json.dumps({"command": args.command, "input": text, "names": names,
                                    "gloss": gloss}, ensure_ascii=False, indent=1),
                        encoding="utf-8")

    failed = {}
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        futures = {pool.submit(ensure, cid): cid for cid in jobs}
        for f in concurrent.futures.as_completed(futures):
            try:
                f.result()
            except RuntimeError as e:
                failed[futures[f]] = str(e)

    for item in items:
        cid = item["id"]
        print(f"# {args.source}/{cid}: {item.get('label', '')}\n")
        if cid in failed:
            print(f"_No gloss: {failed[cid]}_\n")
            continue
        entry = json.loads((GLOSS_CACHE / f"{jobs[cid][0]}.json").read_text(encoding="utf-8"))
        print(", ".join(f"{t} is `{n}`" for t, n in entry["names"].items()) + ".\n")
        print(entry["gloss"] + "\n")
    for cid, err in failed.items():
        print(f"{args.source}/{cid}: no gloss: {err}", file=sys.stderr)
    return 1 if failed else 0


# Groups of declarations in `scripts/checks/ChecksFixture.lean` whose terms must all be equal
# (True), since they differ only in proofs, bound names or binder annotations, or all differ
# (False), since what they say differs.
SELFTEST_GROUPS = [
    ("a bound variable's type", False, ["unionOne", "unionZero"]),
    ("the statement", False, ["bounded", "boundedStrict"]),
    ("a bound variable's name", True, ["bounded", "boundedRenamed"]),
    ("a binder's annotation", True, ["subset_explicit", "subset_implicit"]),
    ("a theorem's proof", True, ["subset_explicit", "subset_otherProof"]),
    ("a proof in a definition's body", True, ["positiveByDecide", "positiveByLemma"]),
    ("a proof in a statement", True, ["val_byDecide", "val_byLemma"]),
    ("a constant's unrecorded rename", False, ["evenOld", "evenNew"]),
]
# Declarations whose closures must leave out a declaration that only their proofs use.
SELFTEST_UNUSED = [("positiveByLemma", "one_pos")]
# The rename in `scripts/checks/ChecksFixtureDeps.lean`, and groups whose terms, once it is
# recorded, must all be equal or all differ.
SELFTEST_RENAME = {"old": "ChecksFixtureDeps.twice", "new": "ChecksFixtureDeps.double"}
SELFTEST_RENAMED_GROUPS = [
    ("a constant's recorded rename", True, ["evenOld", "evenNew"]),
    ("a deprecation that is no rename", False, ["evenNew", "evenAddSelf"]),
]
# Recorded renames, as (old, new) pairs, and the name that must stand for each renamed constant.
SELFTEST_CANONICAL = [
    ([("a", "b"), ("b", "c")], {"b": "a", "c": "a"}),
    ([("a", "b"), ("c", "d"), ("d", "b")], {"b": "a", "c": "a", "d": "a"}),
]


def selftest_groups(data, groups):
    failures = 0
    for what, same, group in groups:
        terms = [data["nodes"][f"ChecksFixture.{n}"]["term"] for n in group]
        ok = len(set(terms)) == 1 if same else len(set(terms)) == len(terms)
        failures += not ok
        effect = "keeps" if same else "changes"
        print(f"{'ok  ' if ok else 'FAIL'}  {what} {effect} the term  ({', '.join(group)})")
    return failures


def selftest_docstring(data, name):
    """Whether the hash of an item stays the same when a declaration's docstring changes."""
    full = f"ChecksFixture.{name}"
    item = {"decls": [full]}
    other = copy.deepcopy(data)
    other["roots"][full]["doc"] += " A different docstring."
    ok = item_hash(item, data) == item_hash(item, other)
    print(f"{'ok  ' if ok else 'FAIL'}  a docstring keeps the hash  ({name})")
    return not ok


def cmd_selftest(args):
    names = sorted({f"ChecksFixture.{n}" for _, _, ns in SELFTEST_GROUPS + SELFTEST_RENAMED_GROUPS
                    for n in ns} | {f"ChecksFixture.{n}" for n, _ in SELFTEST_UNUSED})
    build = subprocess.run(["lake", "build", "checkClosure", "ChecksFixture"], cwd=ROOT,
                           capture_output=True, text=True)
    if build.returncode:
        sys.exit("the fixture does not build:\n" + build.stdout[-2000:])
    data = check_closure(["ChecksFixture"], names, [])
    failures = selftest_groups(data, SELFTEST_GROUPS)
    failures += selftest_docstring(data, SELFTEST_GROUPS[0][2][0])
    for name, unused in SELFTEST_UNUSED:
        ok = f"ChecksFixture.{unused}" not in data["roots"][f"ChecksFixture.{name}"]["closure"]
        failures += not ok
        print(f"{'ok  ' if ok else 'FAIL'}  a declaration used only in a proof is not in the "
              f"closure  ({unused} in {name})")
    found = [{"old": a["old"], "new": a["new"]} for a in data["aliases"]]
    ok = found == [SELFTEST_RENAME]
    failures += not ok
    print(f"{'ok  ' if ok else 'FAIL'}  a deprecated alias is found as a rename, and a deprecation "
          f"that is no alias is not  ({', '.join(a['old'] for a in found) or 'none found'})")
    data = check_closure(["ChecksFixture"], names, [SELFTEST_RENAME])
    failures += selftest_groups(data, SELFTEST_RENAMED_GROUPS)
    for pairs, expected in SELFTEST_CANONICAL:
        got = canonical_names([{"old": o, "new": n} for o, n in pairs])
        ok = got == expected
        failures += not ok
        print(f"{'ok  ' if ok else 'FAIL'}  renames {', '.join(f'{o}->{n}' for o, n in pairs)} "
              f"stand for the earliest name  ({got})")
    return 1 if failures else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("status", help="the status of every item")
    p.add_argument("sources", nargs="*")
    p.add_argument("--json", action="store_true", help="as data, for the docs pages")
    p.add_argument("--ci", action="store_true",
                   help="annotate stale items as warnings, and fail on a broken item")
    p.set_defaults(func=cmd_status)
    p = sub.add_parser("diff", help="what changed since an item was signed")
    p.add_argument("source")
    p.add_argument("item")
    p.set_defaults(func=cmd_diff)
    p = sub.add_parser("core", help="the declarations of the checked items")
    p.add_argument("--json", action="store_true")
    p.set_defaults(func=cmd_core)
    p = sub.add_parser("sign", help="sign items you have checked")
    p.add_argument("source")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--all", action="store_true", help="every unsigned or stale item")
    g.add_argument("--items", help="comma-separated item ids")
    p.add_argument("--by", required=True,
                   help="who checked: your GitHub handle, or the name of a reviewer you record for")
    p.add_argument("--recorded-by", help="your GitHub handle, if --by is someone else")
    p.add_argument("--via", help="how that reviewer made the check known (`email`, `issue #123`)")
    p.set_defaults(func=cmd_sign)
    p = sub.add_parser("gloss", help="blind English glosses of the items' Lean statements")
    p.add_argument("source")
    p.add_argument("--items", help="comma-separated item ids (default: every item)")
    p.add_argument("--command", required=True,
                   help="shell command that writes a gloss: text on stdin, prompt file in "
                        "$GLOSS_PROMPT, gloss on stdout (see checks/README.md)")
    p.add_argument("--jobs", type=int, default=4, help="glosses written at once")
    p.add_argument("--refresh", action="store_true", help="rewrite cached glosses")
    p.set_defaults(func=cmd_gloss)
    p = sub.add_parser("verify-ledger", help="check a pull request's changes to the ledger")
    p.add_argument("--base", required=True, help="the branch the pull request targets")
    p.add_argument("--author", required=True, help="the GitHub login of the pull request's author")
    p.add_argument("--author-type", default="User", help="the account's type: User or Bot")
    p.set_defaults(func=cmd_verify_ledger)
    p = sub.add_parser("renames", help="record the renames of constants the items use")
    p.set_defaults(func=cmd_renames)
    p = sub.add_parser("selftest", help="check that the hash changes exactly when it should")
    p.set_defaults(func=cmd_selftest)
    args = parser.parse_args()
    sys.exit(args.func(args))


if __name__ == "__main__":
    main()
