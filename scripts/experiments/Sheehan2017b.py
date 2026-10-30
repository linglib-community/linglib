"""Recompute the parenthetical counts of Table 5.2 of [sheehan-2017b] from WALS.

The counts printed in parentheses are the languages coded in the WALS CLDF release of
`Linglib/Data/WALS/raw/` for both feature 92A (the position of polar question particles) and
feature 94A (the order of adverbial subordinator and clause), by the initial and final values of
each. The languages, genera and families printed before them are not recomputed.
"""
import csv
from collections import Counter
from pathlib import Path

SOURCES = {}

VALUES = Path(__file__).resolve().parents[2] / "Linglib" / "Data" / "WALS" / "raw" / "values.csv"
POSITION = {"1": "Initial", "2": "Final"}


def recompute(paths):
    values = {}
    with open(VALUES, encoding="utf-8") as f:
        for r in csv.DictReader(f):
            if r["Parameter_ID"] in ("92A", "94A"):
                values.setdefault(r["Parameter_ID"], {})[r["Language_ID"]] = r["Value"]
    counts = Counter()
    for lang, pol in values["92A"].items():
        c = values["94A"].get(lang)
        if pol in POSITION and c in POSITION:
            counts[(POSITION[pol], POSITION[c])] += 1
    rows = [{"pol": p, "c": c, "inParentheses": n} for (p, c), n in counts.items()]
    return {"polarityComplementizer": rows}
