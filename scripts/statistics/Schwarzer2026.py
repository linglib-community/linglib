"""Recompute table (14) and the forced choices of [schwarzer-2026] from its OSF data.

`accept.csv` has a row per Experiment 1 item (its complement and whether the verb
selects a clause) and a column per participant holding the z-scored rating, with a
decimal comma; `2afc.csv` has a row per Experiment 2 pair (its position and whether
it is a control) and a column per participant holding the order chosen.
"""
import csv
import statistics
from collections import Counter, defaultdict

SOURCES = {
    "accept.csv": "https://osf.io/download/amchx/",
    "2afc.csv": "https://osf.io/download/ryxem/",
}

COMPLEMENT = {"coord": "coord.", "dass": "dass"}
POSITION = {"preV": "preverbal", "postV": "postverbal"}


def rows(path):
    with open(path, encoding="utf-8-sig", newline="") as f:
        return list(csv.reader(f, delimiter=";"))


def recompute(paths):
    ratings = defaultdict(list)
    for r in rows(paths["accept.csv"])[1:]:
        ratings[(COMPLEMENT[r[1]], r[2])] += [float(v.replace(",", ".")) for v in r[3:] if v]
    choices = Counter()
    for r in rows(paths["2afc.csv"])[1:]:
        if r[2] == "no":
            choices.update((POSITION[r[1]], v) for v in r[3:] if v)
    return {
        "ratings": [{"complement": c, "selection": s, "observations": len(v),
                     "meanZ": statistics.mean(v), "sd": statistics.stdev(v),
                     "medianZ": statistics.median(v)}
                    for (c, s), v in ratings.items()],
        "choices": [{"position": p, "order": o, "count": n} for (p, o), n in choices.items()],
    }
