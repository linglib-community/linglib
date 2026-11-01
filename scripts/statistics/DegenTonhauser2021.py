"""Recompute the by-content prior and by-predicate certainty means of [degen-tonhauser-2021]
from the authors' released trial-level data.

Experiment 1 (within participant) is the repository's `9-prior-projection`: a row carries one
participant's prior and certainty rating for a content, `prior_type` the fact condition,
`short_trigger` the embedding predicate (`MC` the main-clause controls). Experiments 2a and 2b
(between participants) are `1-prior` (prior ratings, the content read off the
`How likely is it that ...?` prompt) and `3-projectivity` (certainty ratings, `fact_type` the
fact condition, `verb` the predicate or `control`). The participant exclusions of Supplement B
are already applied: 286, 75 and 266 participants remain.
"""
import csv
import statistics
from collections import defaultdict

RAW = "https://raw.githubusercontent.com/judith-tonhauser/projective-probability/master/results"
SOURCES = {
    "exp1_cd.csv": f"{RAW}/9-prior-projection/data/cd.csv",
    "exp2a_cd.csv": f"{RAW}/1-prior/data/cd.csv",
    "exp2b_cd.csv": f"{RAW}/3-projectivity/data/cd.csv",
}

WITHIN, BETWEEN = "within participant", "between participants"
LOWER, HIGHER = "lower probability", "higher probability"

# The 20 contents of Supplement A, keyed by their subject, the short label of the released data.
CLAUSES = {
    "mary": "Mary is pregnant",
    "josie": "Josie went on vacation to France",
    "emma": "Emma studied on Saturday morning",
    "olivia": "Olivia sleeps until noon",
    "sophia": "Sophia got a tattoo",
    "mia": "Mia drank 2 cocktails last night",
    "isabella": "Isabella ate a steak on Sunday",
    "emily": "Emily bought a car yesterday",
    "grace": "Grace visited her sister",
    "zoe": "Zoe calculated the tip",
    "danny": "Danny ate the last cupcake",
    "frank": "Frank got a cat",
    "jackson": "Jackson ran 10 miles",
    "jayden": "Jayden rented a car",
    "tony": "Tony had a drink last night",
    "owen": "Owen shoveled snow last winter",
    "julian": "Julian dances salsa",
    "jon": "Jon walks to work",
    "charley": "Charley speaks Spanish",
    "josh": "Josh learned to ride a bike yesterday",
}

# Predicate spellings of the released data, by the label the paper prints.
EXP1_PREDICATES = {"be_annoyed": "be annoyed", "be_right": "be right"}
EXP2B_PREDICATES = {"annoyed": "be annoyed", "be_right_that": "be right", "inform_Sam": "inform"}


def rows_of(path):
    with open(path, encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def recompute(paths):
    prior, certainty, controls = [], [], defaultdict(list)

    # Exp. 1: one row per participant and content, prior and certainty rating side by side.
    by_content, by_predicate = defaultdict(list), defaultdict(list)
    for r in rows_of(paths["exp1_cd.csv"]):
        if r["short_trigger"] == "MC":
            controls[WITHIN].append(float(r["projective"]))
            continue
        fact = {"low_prior": LOWER, "high_prior": HIGHER}[r["prior_type"]]
        by_content[(fact, CLAUSES[r["content"]])].append(float(r["prior"]))
        predicate = EXP1_PREDICATES.get(r["short_trigger"], r["short_trigger"])
        by_predicate[(fact, predicate)].append(float(r["projective"]))
    prior += [{"design": WITHIN, "fact": f, "content": c, "mean": statistics.mean(v)}
              for (f, c), v in by_content.items()]
    certainty += [{"design": WITHIN, "fact": f, "predicate": p, "mean": statistics.mean(v)}
                  for (f, p), v in by_predicate.items()]

    # Exp. 2a: prior ratings only, the content and fact condition read off the prompt and item.
    by_content = defaultdict(list)
    for r in rows_of(paths["exp2a_cd.csv"]):
        if r["itemType"] not in ("H", "L"):
            continue
        subject = r["prompt"].removeprefix("How likely is it that ").split()[0].lower()
        fact = LOWER if r["itemType"] == "L" else HIGHER
        by_content[(fact, CLAUSES[subject])].append(float(r["response"]))
    prior += [{"design": BETWEEN, "fact": f, "content": c, "mean": statistics.mean(v)}
              for (f, c), v in by_content.items()]

    # Exp. 2b: certainty ratings only.
    by_predicate = defaultdict(list)
    for r in rows_of(paths["exp2b_cd.csv"]):
        if r["verb"] == "control":
            controls[BETWEEN].append(float(r["response"]))
            continue
        fact = {"factL": LOWER, "factH": HIGHER}[r["fact_type"]]
        predicate = EXP2B_PREDICATES.get(r["verb"], r["verb"])
        by_predicate[(fact, predicate)].append(float(r["response"]))
    certainty += [{"design": BETWEEN, "fact": f, "predicate": p, "mean": statistics.mean(v)}
                  for (f, p), v in by_predicate.items()]

    return {
        "prior": prior,
        "certainty": certainty,
        "controls": [{"design": d, "mean": statistics.mean(v)} for d, v in controls.items()],
    }
