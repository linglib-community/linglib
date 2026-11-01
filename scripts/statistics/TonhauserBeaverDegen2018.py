"""Recompute the Experiments 1a and 1b means of [tonhauser-beaver-degen-2018] from the
authors' released trial-level data.

`data_preprocessed.csv` of each experiment has a row per trial: `workerid`, `short_trigger`
(the target expression, or `MC` for a main-clause control), `question_type` (`projective` for
the certain-that question, `ai` for the asking-whether question), `trigger_class` (the authors'
coding) and `response`, the slider rating in [0, 1] already coded so that 1 is projecting and
not-at-issue (the procedure paragraphs). The participant exclusions of the data-exclusion
paragraphs are already applied: 210 and 235 participants remain.
"""
import csv
import statistics
from collections import defaultdict

RAW = "https://raw.githubusercontent.com/judith-tonhauser/how-projective/master/results"
SOURCES = {
    "exp1a_data_preprocessed.csv": f"{RAW}/exp1a/data/data_preprocessed.csv",
    "exp1b_data_preprocessed.csv": f"{RAW}/exp1b/data/data_preprocessed.csv",
}

EXPRESSIONS = {
    "NRRC": "NRRC", "NomApp": "nominal appositive", "possNP": "possessive NP",
    "annoyed": "be annoyed", "discover": "discover", "know": "know", "only": "only",
    "stop": "stop", "stupid": "be stupid to",
}
PREDICATES = {
    "is_annoyed": "be annoyed", "noticed": "notice", "is_aware": "be aware",
    "realize": "realize", "is_amused": "be amused", "saw": "see", "found_out": "find out",
    "learned": "learn", "discovered": "discover", "revealed": "reveal",
    "confessed": "confess", "established": "establish",
}


def means(path):
    """By target expression: the trigger class and the mean rating per question type."""
    ratings, classes = defaultdict(list), {}
    with open(path, encoding="utf-8", newline="") as f:
        for r in csv.DictReader(f):
            ratings[(r["short_trigger"], r["question_type"])].append(float(r["response"]))
            classes[r["short_trigger"]] = r["trigger_class"]
    return {t: (classes[t], statistics.mean(ratings[(t, "projective")]),
                statistics.mean(ratings[(t, "ai")]))
            for t in classes}


def recompute(paths):
    a = means(paths["exp1a_data_preprocessed.csv"])
    b = means(paths["exp1b_data_preprocessed.csv"])
    return {
        "heterogeneous": [{"expression": label, "triggerClass": a[t][0],
                           "projectivity": a[t][1], "notAtIssueness": a[t][2]}
                          for t, label in EXPRESSIONS.items()],
        "predicates": [{"predicate": label, "triggerClass": b[t][0],
                        "projectivity": b[t][1], "notAtIssueness": b[t][2]}
                       for t, label in PREDICATES.items()],
        "controls": [{"experiment": "1a", "projectivity": a["MC"][1], "notAtIssueness": a["MC"][2]},
                     {"experiment": "1b", "projectivity": b["MC"][1], "notAtIssueness": b["MC"][2]}],
    }
