#!/usr/bin/env python3
"""Record and verify human checks that Lean statements are faithful to their sources.

Each file `checks/<bib-key>.toml` lists the claims of one source, a paper's numbered definitions,
propositions and remarks, and the Lean declarations that state each one (`checks/README.md`). A
human who has read the source and the Lean signs a claim, and the sign-off records a hash of the
claim's statement closure: the types and docstrings of its declarations, and the types and bodies
of every project definition those statements mention, but no proofs. `lake exe checkClosure`
computes the closures.

A claim is

* `checked` when its newest sign-off matches the current hash and every claim covering a
  definition in its closure is checked too;
* `relies` when it is signed and current but such a claim is not checked;
* `stale` when its statement closure has changed since the sign-off;
* `unchecked` when it has no sign-off;
* `missing` when the source's claim has no Lean statement yet;
* `broken` when one of its declarations does not resolve;
* `unproved` when one of its declarations rests, through its proof or the definitions it uses, on
  `sorry` or on an axiom beyond Lean's standard three, whatever its sign-off says.

The checked claims form the reviewed core: their declarations, and the project definitions their
statements use. Since a claim is checked only if the claims it relies on are, nothing in the core
depends for its meaning on anything outside it.

Usage, from the repository root:

    python3 scripts/checks.py status [SOURCE ...]
    python3 scripts/checks.py status --json   # every claim, for the docs pages
    python3 scripts/checks.py diff SOURCE CLAIM
    python3 scripts/checks.py core [--json]
    python3 scripts/checks.py sign SOURCE (--all | --claims ID,ID,...) --by GITHUB_HANDLE

Sign-offs are made by people. `sign` refuses to run inside an agent session (`CLAUDECODE`).
"""

import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECKS = ROOT / "checks"
LIBRARIES = ["Linglib", "Studies", "Eval", "Lab"]
RELATIONS = {"exact", "generalizes", "specializes", "variant", "missing"}
HASH_VERSION = "v1"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def load_sources(keys=None):
    """The check files, keyed by source, each with its path and claims."""
    sources = {}
    for path in sorted(CHECKS.glob("*.toml")):
        with path.open("rb") as f:
            data = tomllib.load(f)
        key = data.get("source")
        if key != path.stem:
            sys.exit(f"{path}: `source = {key!r}` does not match the file name")
        sources[key] = {"path": path, "claims": data.get("claim", [])}
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
        for claim in src["claims"]:
            cid = claim.get("id", "?")
            if cid in ids:
                problems.append(f"{key}/{cid}: duplicate id")
            ids.add(cid)
            relation = claim.get("relation")
            if relation not in RELATIONS:
                problems.append(
                    f"{key}/{cid}: relation {relation!r} is not one of {sorted(RELATIONS)}")
            if relation not in ("exact", "missing") and not claim.get("notes"):
                problems.append(f"{key}/{cid}: a `{relation}` claim needs notes")
            if relation == "missing" and claim.get("decls"):
                problems.append(f"{key}/{cid}: a `missing` claim has no decls")
            if relation != "missing" and not claim.get("decls"):
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


def closures(names):
    """Run `checkClosure` on the names, building the modules that may declare them."""
    if not names:
        return {"roots": {}, "nodes": {}}
    modules = candidate_modules(names)
    if not modules:
        return {"roots": {n: {"found": False} for n in names}, "nodes": {}}
    build = subprocess.run(["lake", "build", "checkClosure", *modules], cwd=ROOT,
                           capture_output=True, text=True)
    if build.returncode:
        errors = [l for l in build.stdout.splitlines() if l.startswith("error")]
        sys.exit("the modules declaring the claims do not build:\n" + "\n".join(errors[:20]))
    out = subprocess.run(["lake", "exe", "checkClosure", *modules, "--", *names], cwd=ROOT,
                         check=True, capture_output=True, text=True).stdout
    return json.loads(out)


def claim_hash(claim, data):
    """The hash of a claim's statement closure."""
    h = hashlib.sha256(HASH_VERSION.encode())
    closure = set()
    for name in sorted(claim["decls"]):
        root = data["roots"][name]
        h.update(f"\0root\0{name}\0{root['doc']}\0{data['nodes'][name]['text']}".encode())
        closure.update(root["closure"])
    for name in sorted(closure - set(claim["decls"])):
        h.update(f"\0node\0{name}\0{data['nodes'][name]['text']}".encode())
    return h.hexdigest()[:16]


def evaluate(sources):
    """The status and details of every claim, keyed by `(source, id)`, and the closures."""
    names = sorted({d for src in sources.values() for c in src["claims"]
                    for d in c.get("decls", [])})
    data = closures(names)
    covering = {}
    for key, src in sources.items():
        for claim in src["claims"]:
            for d in claim.get("decls", []):
                covering.setdefault(d, set()).add((key, claim["id"]))

    own, info = {}, {}
    for key, src in sources.items():
        for claim in src["claims"]:
            ref = (key, claim["id"])
            decls = claim.get("decls", [])
            info[ref] = {"claim": claim, "deps": set(), "hash": None}
            if claim.get("relation") == "missing" or not decls:
                own[ref] = "missing"
                continue
            unresolved = [d for d in decls if not data["roots"].get(d, {}).get("found")]
            if unresolved:
                own[ref] = "broken"
                info[ref]["unresolved"] = unresolved
                continue
            digest = claim_hash(claim, data)
            info[ref]["hash"] = digest
            closure = {n for d in decls for n in data["roots"][d]["closure"]}
            info[ref]["deps"] = {c for n in closure for c in covering.get(n, ())} - {ref}
            info[ref]["closure"] = closure | set(decls)
            info[ref]["files"] = sorted({data["nodes"][n]["module"] for n in closure | set(decls)})
            checks = claim.get("check", [])
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
    """Every claim with its status and newest sign-off, as `gen_docs_pages.py --checks` reads it."""
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, check=True,
                            capture_output=True, text=True).stdout.strip()
    claims = []
    for (key, cid), st in status.items():
        claim = info[(key, cid)]["claim"]
        last = (claim.get("check") or [None])[-1]
        claims.append({
            "source": key, "id": cid, "label": claim.get("label", cid),
            "relation": claim.get("relation"), "notes": claim.get("notes", "").strip(),
            "decls": claim.get("decls", []), "status": st,
            "check": last and {"by": last.get("by"), "date": str(last.get("date")),
                               "commit": last.get("commit")},
            "blocking": [f"{k}/{c}" for k, c in info[(key, cid)].get("blocking", [])]})
    return {"commit": commit, "claims": claims}


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
    status, info, _ = evaluate(sources)
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
    return 1 if problems else 0


def cmd_core(args):
    sources = load_sources()
    status, info, data = evaluate(sources)
    claims = sorted(r for r in status if status[r] == "checked")
    decls = {}
    for ref in claims:
        for name in info[ref]["closure"]:
            node = data["nodes"][name]
            entry = decls.setdefault(name, {"module": node["module"], "kind": node["kind"],
                                            "states": []})
            if name in info[ref]["claim"]["decls"]:
                entry["states"].append(f"{ref[0]}/{ref[1]}")
    modules = sorted({d["module"] for d in decls.values()})
    if args.json:
        print(json.dumps({"claims": [f"{k}/{c}" for k, c in claims], "modules": modules,
                          "declarations": dict(sorted(decls.items()))}, indent=2))
        return 0
    print(f"{len(claims)} checked claim(s) from {len({k for k, _ in claims})} source(s): "
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
    status, info, _ = evaluate(sources)
    ref = (args.source, args.claim)
    if ref not in info:
        sys.exit(f"no claim {args.claim} in {args.source}")
    checks = info[ref]["claim"].get("check", [])
    if not checks:
        sys.exit(f"{args.claim} has never been signed")
    last = checks[-1]
    print(f"{args.claim}: {status[ref]}; signed at {last['commit']} by {last['by']} "
          f"on {last['date']}")
    if status[ref] != "stale":
        return 0
    files = [str(Path(*m.split(".")).with_suffix(".lean")) for m in info[ref].get("files", [])]
    return subprocess.run(["git", "diff", last["commit"], "--", *files], cwd=ROOT).returncode


def insert_check(text, cid, entry):
    """The TOML text with `entry` appended to the claim with id `cid`."""
    lines = text.splitlines(keepends=True)
    id_line = re.compile(rf'\s*id\s*=\s*"{re.escape(cid)}"\s*$')
    start = next(i for i, l in enumerate(lines) if id_line.match(l))
    end = next((i for i in range(start + 1, len(lines)) if lines[i].strip() == "[[claim]]"),
               len(lines))

    def filler(line):
        return not line.strip() or line.lstrip().startswith("#")

    while end > start + 1 and filler(lines[end - 1]):
        end -= 1
    return "".join(lines[:end]) + entry + "".join(lines[end:])


def cmd_sign(args):
    if os.environ.get("CLAUDECODE"):
        sys.exit("sign-offs are made by people: run `sign` yourself, outside an agent session")
    if not re.fullmatch(r"[A-Za-z0-9-]+", args.by):
        sys.exit(f"--by takes a GitHub handle, not {args.by!r}")
    sources = load_sources([args.source])
    problems = [p for p in validate(sources)]
    if problems:
        sys.exit("fix the check file first:\n" + "\n".join(problems))
    status, info, _ = evaluate(sources)
    claims = sources[args.source]["claims"]
    ids = [c["id"] for c in claims] if args.all else args.claims.split(",")
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, check=True,
                            capture_output=True, text=True).stdout.strip()
    today = datetime.date.today().isoformat()
    path = sources[args.source]["path"]
    text = path.read_text(encoding="utf-8")
    signed = []
    for cid in ids:
        ref = (args.source, cid)
        if ref not in status:
            sys.exit(f"no claim {cid} in {args.source}")
        if status[ref] in ("missing", "broken"):
            if args.all:
                continue
            sys.exit(f"{cid} is {status[ref]} and cannot be signed")
        if info[ref]["signoff"] == "signed" and args.all:
            continue
        entry = (f'\n  [[claim.check]]\n  by     = "{args.by}"\n  date   = {today}\n'
                 f'  commit = "{commit}"\n  hash   = "{info[ref]["hash"]}"\n')
        text = insert_check(text, cid, entry)
        signed.append(cid)
    path.write_text(text, encoding="utf-8")
    print(f"signed {len(signed)} claim(s) of {args.source} at {commit}: {', '.join(signed)}")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("status", help="the status of every claim")
    p.add_argument("sources", nargs="*")
    p.add_argument("--json", action="store_true", help="as data, for the docs pages")
    p.set_defaults(func=cmd_status)
    p = sub.add_parser("diff", help="what changed since a claim was signed")
    p.add_argument("source")
    p.add_argument("claim")
    p.set_defaults(func=cmd_diff)
    p = sub.add_parser("core", help="the declarations of the checked claims")
    p.add_argument("--json", action="store_true")
    p.set_defaults(func=cmd_core)
    p = sub.add_parser("sign", help="sign claims you have checked")
    p.add_argument("source")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--all", action="store_true", help="every unsigned or stale claim")
    g.add_argument("--claims", help="comma-separated claim ids")
    p.add_argument("--by", required=True, help="your GitHub handle")
    p.set_defaults(func=cmd_sign)
    args = parser.parse_args()
    sys.exit(args.func(args))


if __name__ == "__main__":
    main()
