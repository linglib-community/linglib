"""Recompute the stimulus pictures and the response counts of [marty-etal-2026] from the authors'
released trial-level data.

`processed_data_existence.csv` (Exp. 1) and `processed_data_gender.csv` (Exp. 2) hold a row per
trial of the participants left after the exclusions of §3.5 (74 and 71). A target trial has
`Status` `Test`; `Type` is the sentence (`M-Pos`, `M-Neg`, `NM-Pos`, `NM-Neg`), `Condition` the
picture, with `Target-A` the paper's Target-1 and `Target-E` its Target-2, and `Binary` the
response, 1 for 'Good'. A picture shows the four children `N1`-`N4` with what lies in front of
each, `P1`-`P4`: `empty.png` for no present, `<colour>-Cpresent.png` for a closed one and
`<colour>-Opresent.png` for an open one. Exp. 2 tells girls from boys only by name: the girls
are Phoebe, Carrie, Jenny and Kim, as in Table 2. The positions of the children vary between the
four instances of a condition, so a picture is recorded as the multiset of its children, listed in
the order of the levels; every instance of a condition shows the same multiset.
"""
import csv
from collections import Counter, defaultdict

OSF = "https://osf.io/download"
SOURCES = {
    "processed_data_existence.csv": f"{OSF}/hsrt6/",
    "processed_data_gender.csv": f"{OSF}/bnhzf/",
}

EXPERIMENTS = {"processed_data_existence.csv": "Exp.1", "processed_data_gender.csv": "Exp.2"}
SENTENCES = {"M-Pos": "m-pos", "M-Neg": "m-neg", "NM-Pos": "nm-pos", "NM-Neg": "nm-neg"}
PICTURES = {"False": "False", "Target-A": "Target-1", "Target-E": "Target-2", "True": "True"}
GIFTS = ["no present", "closed present", "open present"]
RECIPIENTS = ["girl, open present", "girl, closed present", "boy, open present",
              "boy, closed present"]
GIRLS = {"Phoebe", "Carrie", "Jenny", "Kim"}


def gift(p):
    if p == "empty.png":
        return "no present"
    if "-Cpresent" in p:
        return "closed present"
    if "-Opresent" in p:
        return "open present"
    raise ValueError(p)


def recipient(name, p):
    g = gift(p)
    if g == "no present":
        raise ValueError(f"Exp. 2 picture without a present: {name}")
    return ("girl" if name in GIRLS else "boy") + ", " + g


def recompute(paths):
    pictures = {"Exp.1": defaultdict(set), "Exp.2": defaultdict(set)}
    counts = defaultdict(Counter)
    for file, exp in EXPERIMENTS.items():
        with open(paths[file], encoding="utf-8") as f:
            for r in csv.DictReader(f):
                if r["Status"] != "Test":
                    continue
                key = (SENTENCES[r["Type"]], PICTURES[r["Condition"]])
                cells = [(r[f"N{i}"], r[f"P{i}"]) for i in range(1, 5)]
                if exp == "Exp.1":
                    kids = sorted((gift(p) for _, p in cells), key=GIFTS.index)
                else:
                    kids = sorted((recipient(n, p) for n, p in cells), key=RECIPIENTS.index)
                pictures[exp][key].add(tuple(kids))
                counts[(exp,) + key][int(r["Binary"])] += 1
    for exp, table in pictures.items():
        for key, kids in table.items():
            if len(kids) != 1:
                raise ValueError(f"{exp} {key}: instances differ: {kids}")
    rows = lambda exp: [{"sentence": s, "picture": p, "children": list(next(iter(k)))}
                        for (s, p), k in pictures[exp].items()]
    return {
        "existencePictures": rows("Exp.1"),
        "genderPictures": rows("Exp.2"),
        "responses": [{"experiment": e, "sentence": s, "picture": p, "good": c[1],
                       "trials": c[0] + c[1]} for (e, s, p), c in counts.items()],
    }
