"""Recompute the Experiments 1a and 1b means of [degen-tonhauser-2022] from the authors'
released trial-level data.

Each `cd.csv` has a row per trial: `workerid`, `verb` (the predicate, or a control label) and
`response`, a slider rating in [0, 1] (1a) or `Yes`/`No` coded 1 and 0 (1b). The participant
exclusions of the data-exclusion paragraphs are already applied: 266 and 436 participants
remain. Experiment 1a is the repository's `5-projectivity-no-fact` and 1b its
`8-projectivity-no-fact-binary`.
"""
import csv
import statistics
from collections import defaultdict

RAW = "https://raw.githubusercontent.com/judith-tonhauser/projective-probability/master/results"
SOURCES = {
    "exp1a_cd.csv": f"{RAW}/5-projectivity-no-fact/data/cd.csv",
    "exp1b_cd.csv": f"{RAW}/8-projectivity-no-fact-binary/data/cd.csv",
}

PREDICATES = [
    "acknowledge", "admit", "announce", "be annoyed", "be right", "confess", "confirm",
    "demonstrate", "discover", "establish", "hear", "inform", "know", "pretend", "prove",
    "reveal", "say", "see", "suggest", "think",
]


def means(path):
    """The mean response by predicate, `Yes`/`No` coded 1 and 0."""
    ratings = defaultdict(list)
    with open(path, encoding="utf-8", newline="") as f:
        for r in csv.DictReader(f):
            v = r["response"]
            ratings[r["verb"]].append({"Yes": 1.0, "No": 0.0}.get(v) if v in ("Yes", "No")
                                      else float(v))
    return {p: statistics.mean(ratings[p]) for p in PREDICATES}


def recompute(paths):
    a, b = means(paths["exp1a_cd.csv"]), means(paths["exp1b_cd.csv"])
    return {
        "certainty": [{"task": task, "predicate": p, "mean": m[p]}
                      for task, m in (("gradient", a), ("categorical", b)) for p in PREDICATES],
    }
