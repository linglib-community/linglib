"""Recompute the Block 1 means of [solstad-bott-2024] from the authors' released trial-level data.

The OSF archive `RMD_files_occasion_verbs.zip` holds a tab-separated file per experiment with a
row per Block 1 trial: the participant, the item, the context type `kontext` (1 neutral, 2
anaphoric, 3 cataphoric), the trigger type, and the slider `rating` in [0, 100] (`NA` where a
trial is missing). The coding of `kontext` is fixed by the occasion-verb means the paper prints
for Experiment 2 (.49, .69, .68) and by its regression tables, which the means reproduce. The
participant exclusions are already applied: 71 and 60 participants remain.
"""
import statistics
import zipfile
from collections import defaultdict

SOURCES = {"RMD_files_occasion_verbs.zip": "https://osf.io/download/zehgq/"}

DATA = "RMD_files_occasion_verbs/data"
CONTEXTS = {"1": "neutral", "2": "anaphoric", "3": "cataphoric"}
EXP1 = {
    "Occasion-Verbs": "occasion verbs", "Pronoun": "personal pronoun",
    "demonstrative-NP": "demonstrative NP", "Possessive": "possessive NP", "NRRC": "NRRC",
    "know": "know", "discover": "discover", "stop": "stop",
}
EXP2 = {
    "Occasion": "occasion verbs", "auch": "too", "wieder": "again", "def": "definite article",
    "impl_verben": "manage", "cleft": "cleft", "appositives": "appositive",
    "es_verbs": "es-verbs", "se_verbs": "se-verbs",
}


def means(archive, member, labels):
    """By trigger type and context type: the mean rating, on the unit interval."""
    with archive.open(f"{DATA}/{member}") as f:
        lines = f.read().decode("utf-8").splitlines()
    header = lines[0].split()
    ratings = defaultdict(list)
    for line in lines[1:]:
        row = dict(zip(header, line.split("\t")))
        if row and row["rating"] != "NA":
            ratings[(row["trigger"], row["kontext"])].append(float(row["rating"]) / 100)
    return [{"trigger": label, "context": name, "mean": statistics.mean(ratings[(t, k)])}
            for t, label in labels.items() for k, name in CONTEXTS.items()]


def recompute(paths):
    with zipfile.ZipFile(paths["RMD_files_occasion_verbs.zip"]) as archive:
        return {
            "blockOneExp1": means(archive, "exp1/input_block1.txt", EXP1),
            "blockOneExp2": means(archive, "exp2/input_block1_exp2.txt", EXP2),
        }
