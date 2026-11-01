"""Recompute footnote 13 of [khoo-2015] from its semanticsarchive survey export.

`datamd.xlsx` is a Qualtrics export: a header row of column codes, a row of question
texts, and a row per participant. The ratings are in `C1 false` and `M false` (the False
condition) and `C1 no` and `M no` (the Rejection condition). Needs `openpyxl`. The export
also holds identifying fields, which are not read.
"""
import statistics
import warnings

SOURCES = {"datamd.xlsx": "https://semanticsarchive.net/Archive/Tc0NmIzY/datamd.xlsx"}

COLUMNS = {("Control", "False"): "C1 false", ("Control", "Rejection"): "C1 no",
           ("Modal", "False"): "M false", ("Modal", "Rejection"): "M no"}


def recompute(paths):
    import openpyxl
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        sheet = next(iter(openpyxl.load_workbook(paths["datamd.xlsx"], data_only=True)))
    header, _, *data = sheet.iter_rows(values_only=True)
    rows = []
    for (sentence, response), col in COLUMNS.items():
        j = header.index(col)
        v = [r[j] for r in data if isinstance(r[j], (int, float))]
        rows.append({"sentence": sentence, "response": response,
                     "mean": statistics.mean(v), "sd": statistics.stdev(v)})
    return {"ratings": rows}
