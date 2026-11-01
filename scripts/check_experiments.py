#!/usr/bin/env python3
"""Recompute printed experimental results from the authors' released data.

A paper whose tables in `Linglib/Data/Experiments/<Paper>.json` or `Linglib/Data/Corpus/<Paper>.json`
are marked
`verified: raw-data` has a recompute module `scripts/experiments/<Paper>.py`
defining

* `SOURCES`: a dict from a local file name to the download URL of a released file;
* `recompute(paths)`: given the downloaded files by name, a dict from a table name to
  its rows as the JSON writes them (labels, printed decimals need not be given as
  strings; a float is compared to the printed decimal at the printed precision).

This script downloads the sources into `scratch/experiment-data/<Paper>/` (cached),
recomputes, and compares every recomputed cell with the JSON: a natural number must
be equal, a float must round to the printed decimal, anything else must be equal.
Tables marked `raw-data` must be recomputed. The raw data is not committed; it needs
network access, so this runs by hand, not in CI.

    python3 scripts/check_experiments.py Schwarzer2026
    python3 scripts/check_experiments.py --all
"""
import importlib.util
import json
import sys
import urllib.request
from decimal import Decimal
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIRS = [ROOT / "Linglib" / "Data" / k for k in ("Experiments", "Corpus")]
MODULES = ROOT / "scripts" / "experiments"
CACHE = ROOT / "scratch" / "experiment-data"


def fetch(paper: str, sources: dict) -> dict:
    paths = {}
    for name, url in sources.items():
        path = CACHE / paper / name
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            req = urllib.request.Request(url, headers={"User-Agent": "linglib-check-experiments"})
            try:
                with urllib.request.urlopen(req) as r:
                    path.write_bytes(r.read())
            except OSError as e:
                sys.exit(f"[raw] {paper}: cannot fetch {name} from {url}: {e}")
        paths[name] = path
    return paths


def matches(printed, value) -> bool:
    if isinstance(value, float):
        d = Decimal(printed)
        half = Decimal(1).scaleb(d.as_tuple().exponent) / 2
        return abs(Decimal(repr(value)) - d) <= half
    return printed == value


def check(paper: str) -> bool:
    spec = importlib.util.spec_from_file_location(paper, MODULES / f"{paper}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    src = next(d / f"{paper}.json" for d in DATA_DIRS if (d / f"{paper}.json").exists())
    doc = json.loads(src.read_text(encoding="utf-8"))
    tables = {tb["name"]: tb for tb in doc["tables"]}
    got = mod.recompute(fetch(paper, mod.SOURCES))
    ok = True
    for name, tb in tables.items():
        if tb.get("verified") == "raw-data" and name not in got:
            print(f"[raw] {paper}.{name}: marked raw-data but not recomputed")
            ok = False
    for name, rows in got.items():
        tb = tables[name]
        key = tb.get("key") or [c["name"] for c in tb["columns"]][:1]
        printed = {tuple(r[k] for k in key): r for r in tb["rows"]}
        for row in rows:
            kv = tuple(row[k] for k in key)
            if kv not in printed:
                print(f"[raw] {paper}.{name}{list(kv)}: no printed row")
                ok = False
                continue
            for col, value in row.items():
                if not matches(printed[kv][col], value):
                    print(f"[raw] {paper}.{name}{list(kv)}.{col}: printed {printed[kv][col]!r}, "
                          f"recomputed {value!r}")
                    ok = False
        if len(rows) != len(tb["rows"]):
            print(f"[raw] {paper}.{name}: {len(tb['rows'])} printed rows, {len(rows)} recomputed")
            ok = False
    print(f"[raw] {paper}: {'agrees' if ok else 'DISAGREES'} with its released data")
    return ok


def main():
    args = sys.argv[1:]
    if args == ["--all"]:
        papers = sorted(p.stem for p in MODULES.glob("*.py"))
    elif len(args) == 1:
        papers = args
    else:
        sys.stderr.write(__doc__)
        sys.exit(2)
    sys.exit(0 if all([check(p) for p in papers]) else 1)


if __name__ == "__main__":
    main()
