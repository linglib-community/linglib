#!/usr/bin/env python3
"""Generate Lean 4 modules from PHOIBLE 2.0 inventory data.

Usage:
    python3 scripts/gen_phoible.py [ISO[=ID]...]
    python3 scripts/gen_phoible.py --chart
    python3 scripts/gen_phoible.py --check

Examples:
    python3 scripts/gen_phoible.py eng deu jpn   # specific ISO codes
    python3 scripts/gen_phoible.py kor=2197      # a chosen inventory, by InventoryID
    python3 scripts/gen_phoible.py               # every inventory already generated
    python3 scripts/gen_phoible.py --chart       # the glyph-indexed feature chart
    python3 scripts/gen_phoible.py --check       # chart and inventories in sync (CI)

Reads from:  Linglib/Data/PHOIBLE/raw/phoible.csv
Writes to:   Linglib/Data/PHOIBLE/Inventories/{Name}.lean, one per requested ISO.
             Linglib/Data/PHOIBLE/Chart.lean with `--chart`.

In PHOIBLE a glyph determines its feature values, whatever the inventory, so the chart has
one feature matrix per glyph. `--chart` and `--check` fail if the CSV ever breaks that
invariant, or what the docstring of `Data.PHOIBLE.Source` says each source records. Tones
are left out, and so are glyphs with a contour value such as `-,+`, which a `Bool`-valued
matrix cannot hold.

An inventory is the one `ISO=ID` names, else the ISO's lowest InventoryID. Each generated
module records the argument that regenerates it, and a run without arguments regenerates
every module in `Inventories/` from its recorded argument. A phoneme whose glyph is in the
chart takes its feature matrix from `Chart.lean`; tones and contour-valued glyphs carry theirs
inline, with each contour read as the meet of its phases. PHOIBLE's `NA` becomes `none`.

Dependencies: pure stdlib (csv module).
"""

import csv
import re
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402
from collections import OrderedDict

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "Linglib" / "Data" / "PHOIBLE" / "raw" / "phoible.csv"
OUT  = ROOT / "Linglib" / "Data" / "PHOIBLE" / "Inventories"
CHART = ROOT / "Linglib" / "Data" / "PHOIBLE" / "Chart.lean"

# ── PHOIBLE feature columns (in CSV order, matching Schema.lean) ───────────

# The distinctive-feature columns, with "tone" and "stress" appended when emitting.
FEATURE_COLS = [
    "syllabic", "short", "long", "consonantal", "sonorant", "continuant",
    "delayedRelease", "approximant", "tap", "trill", "nasal", "lateral",
    "labial", "round", "labiodental", "coronal", "anterior", "distributed",
    "strident", "dorsal", "high", "low", "front", "back", "tense",
    "retractedTongueRoot", "advancedTongueRoot", "periodicGlottalSource",
    "epilaryngealSource", "spreadGlottis", "constrictedGlottis", "fortis",
    "lenis", "raisedLarynxEjective", "loweredLarynxImplosive", "click",
]
# Plus tone + stress at the end.

# Column-to-constructor renames in `Data.PHOIBLE.Feature` (none at present).
COL_TO_FIELD = {}

# The `Source` column's codes, which are the constructors of `Data.PHOIBLE.Source`.
SOURCES = ["spa", "upsid", "aa", "ph", "ra", "saphon", "ea", "er"]

# What each source records, as the docstring of `Source` states; `check_row` verifies it.
LISTS_ALLOPHONES = {"aa", "ph", "spa"}
MARKS_MARGINAL = {"aa", "ea", "er", "ph", "upsid"}
HAS_TONES = {"aa", "ph", "ra", "spa"}

# ── Helpers ────────────────────────────────────────────────────────────────

def feature_value(s: str):
    """Map a CSV cell to a Lean `Bool`, or `None` for an unspecified feature.

    A cell is `+`, `-`, `0` (not applicable) or a contour of these such as `-,+`. The value is
    the meet of the cell's phases in the subsumption order: the value every phase has, and
    unspecified when the phases differ or one of them is `0`."""
    phases = set(s.strip().split(","))
    if phases == {"+"}: return "true"
    if phases == {"-"}: return "false"
    return None

def format_features(pairs, indent="        "):
    """Emit `.ofRow { ... }` over the specified (feature, value) pairs."""
    items = [f"{f} := {v}" for f, v in pairs]
    lines = []; cur = indent
    for it in items:
        piece = (it if cur.strip() == "" else ", " + it)
        if len(cur) + len(piece) + 1 > 96:
            lines.append(cur + ","); cur = indent + it
        else:
            cur += piece if cur.strip() else it
    lines.append(cur)
    return ".ofRow {" + chr(10) + chr(10).join(lines) + " }"

def segment_class(s: str) -> str:
    s = s.strip().strip('"')
    if s in ("consonant", "vowel", "tone"): return "." + s
    raise ValueError(f"unknown segment class {s!r}")

def source_constructor(s: str) -> str:
    s = s.strip().strip('"').lower()
    if s in SOURCES: return "." + s
    raise ValueError(f"unknown PHOIBLE source {s!r}: add it to `SOURCES` and to `Source`")

def marginal_value(s: str) -> str:
    """The `Marginal` column, `TRUE`, `FALSE` or `NA`, as a Lean `Option Bool`."""
    s = s.strip().strip('"')
    if s == "TRUE": return "some true"
    if s == "FALSE": return "some false"
    if s == "NA": return "none"
    raise ValueError(f"unknown Marginal value {s!r}")

def lean_string(s: str) -> str:
    """Quote a string for Lean source. Escapes backslashes and quotes."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'

def lean_option_string(s: str) -> str:
    """A CSV cell as a Lean `Option String`, `none` for `NA` and for the blank SAPHON writes."""
    s = s.strip().strip('"')
    return "none" if s in ("NA", "") else f"some {lean_string(s)}"

def allophones_value(s: str) -> str:
    """The `Allophones` column, a space-separated list or `NA`, as a Lean `Option (List String)`."""
    s = s.strip().strip('"')
    if s == "NA": return "none"
    return "some [" + ", ".join(lean_string(a) for a in s.split()) + "]"

def check_row(row: dict):
    """Fail unless the row bears out what the docstring of `Source` says each source records,
    and a listed set of allophones contains the phoneme's glyph."""
    s, glyph = row["Source"], row["Phoneme"]
    if s not in SOURCES:
        sys.exit(f"FATAL: unknown PHOIBLE source {s!r}: add it to `SOURCES` and to `Source`")
    if (row["Allophones"] != "NA") != (s in LISTS_ALLOPHONES):
        sys.exit(f"FATAL: {s} row {glyph!r} breaks the allophone record of `Source`")
    if row["Allophones"] != "NA" and glyph not in row["Allophones"].split():
        sys.exit(f"FATAL: {s} row {glyph!r} lacks its glyph among its allophones")
    if (row["Marginal"] != "NA") != (s in MARKS_MARGINAL):
        sys.exit(f"FATAL: {s} row {glyph!r} breaks the marginality record of `Source`")
    if row["SegmentClass"] == "tone" and s not in HAS_TONES:
        sys.exit(f"FATAL: {s} row {glyph!r} is a tone, which `Source` says it has none of")

def lang_module_name(lang_name: str, iso: str) -> str:
    """Lean module name from PHOIBLE LanguageName + ISO. Title-case, ASCII only."""
    name = lang_name.strip().strip('"')
    # Strip parentheses, special chars; collapse spaces.
    name = re.sub(r'\(.*?\)', '', name)
    name = re.sub(r'[^A-Za-z0-9]+', ' ', name).strip()
    parts = name.split()
    if not parts:
        return iso.upper()
    # Title-case first letter of each word, ASCII fallback.
    title = "".join(p[:1].upper() + p[1:].lower() for p in parts)
    # Lean module names need to be valid identifiers.
    if not title or not title[0].isalpha():
        return iso.upper()
    return title

# ── Per-inventory emission ─────────────────────────────────────────────────

def in_chart(row: dict) -> bool:
    """Whether the chart has this row's glyph: not a tone, no contour value."""
    return (row["SegmentClass"] != "tone"
            and not any("," in row[c] for c in FEATURE_COLS + ["tone", "stress"]))

def emit_phoneme(row: dict) -> str:
    """Emit one Lean `Phoneme` literal."""
    if in_chart(row):
        feature_block = f".«{row['Phoneme']}»"
    else:
        pairs = []
        for col in FEATURE_COLS + ["tone", "stress"]:
            val = feature_value(row[col])
            if val is not None:
                pairs.append((COL_TO_FIELD.get(col, col), val))
        feature_block = format_features(pairs)

    glyph = row["Phoneme"].strip().strip('"')

    return f"""    {{ glyph := {lean_string(glyph)},
      allophones := {allophones_value(row["Allophones"])},
      marginal := {marginal_value(row["Marginal"])},
      segmentClass := {segment_class(row["SegmentClass"])},
      features := {feature_block} }}"""

def emit_inventory(rows: list, var_name: str) -> str:
    """Emit one Lean `Inventory` literal for a list of CSV rows."""
    if not rows:
        raise ValueError("empty rows")
    head = rows[0]
    phoneme_blocks = ",\n".join(emit_phoneme(r) for r in rows)

    return f"""def {var_name} : Inventory :=
  {{ id := {int(head["InventoryID"])},
    glottocode := {lean_option_string(head["Glottocode"])},
    iso := {lean_string(head["ISO6393"].strip().strip('"'))},
    languageName := {lean_string(head["LanguageName"].strip().strip('"'))},
    specificDialect := {lean_option_string(head["SpecificDialect"])},
    source := {source_constructor(head["Source"])},
    phonemes := [
{phoneme_blocks} ] }}"""

def emit_module(iso: str, rows_by_inv: dict, module_name: str, inv_id=None) -> str:
    """Emit a complete Lean module for one ISO: the chosen inventory, else the first."""
    if not rows_by_inv:
        raise ValueError(f"no inventories for {iso}")
    first_inv_id = min(rows_by_inv.keys()) if inv_id is None else inv_id
    rows = rows_by_inv[first_inv_id]
    var_name = iso.lower()
    if not var_name.isidentifier():
        var_name = "lang"

    inv_block = emit_inventory(rows, var_name)
    head = rows[0]
    lang_name = head["LanguageName"].strip().strip('"')
    glottocode = head["Glottocode"].strip().strip('"')
    glotto = "" if glottocode == "NA" else f" (Glottocode `{glottocode}`)"
    source = head["Source"].strip().strip('"').upper()

    regen = iso if inv_id is None else f"{iso}={inv_id}"
    return f"""import Linglib.Data.PHOIBLE.Chart

/-!
# PHOIBLE inventory of {lang_name}

This is PHOIBLE 2.0's inventory {first_inv_id} of {lang_name}{glotto}, from the {source} source,
with {len(rows)} phonemes.

Auto-generated by `scripts/gen_phoible.py`. **Do not edit by hand**: regenerate with
`python3 scripts/gen_phoible.py {regen}`.

## References

* [moran-mccloy-2019]
-/

namespace Data.PHOIBLE.Inventories.{module_name}

open Data.PHOIBLE

{inv_block}

end Data.PHOIBLE.Inventories.{module_name}
"""

# ── The glyph chart ────────────────────────────────────────────────────────

def chart_rows():
    """One CSV row per glyph, in order of first appearance; checks every row with `check_row`
    and that a glyph determines its feature values."""
    cols = FEATURE_COLS + ["tone", "stress"]
    first = OrderedDict()
    with open(DATA, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            check_row(row)
            glyph = row["Phoneme"]
            vec = tuple(row[c] for c in cols)
            seen = first.get(glyph)
            if seen is None:
                first[glyph] = (row, vec)
            elif seen[1] != vec:
                sys.exit(f"FATAL: glyph {glyph!r} has two feature vectors")
    return [row for row, _ in first.values()]

def emit_chart() -> str:
    cols = FEATURE_COLS + ["tone", "stress"]
    entries = []
    skipped_tone = skipped_contour = 0
    for row in sorted(chart_rows(), key=lambda r: r["GlyphID"]):
        if row["SegmentClass"] == "tone":
            skipped_tone += 1; continue
        if any("," in row[c] for c in cols):
            skipped_contour += 1; continue
        glyph = row["Phoneme"]
        if "»" in glyph or "-/" in glyph:
            sys.exit(f"FATAL: glyph {glyph!r} cannot be quoted")
        pairs = [(COL_TO_FIELD.get(c, c), feature_value(row[c])) for c in cols]
        pairs = [(f, v) for f, v in pairs if v is not None]
        block = format_features(pairs, indent="  ")
        entries.append(
            f"/-- {glyph} (GlyphID {row['GlyphID']}), {row['SegmentClass']}. -/\n"
            f"def «{glyph}» : FeatureMatrix := {block}")
    body = "\n\n".join(entries)
    return f"""import Linglib.Data.PHOIBLE.Schema

/-!
# PHOIBLE feature chart

This file lists the feature matrix PHOIBLE 2.0 assigns to each segment glyph. In PHOIBLE a
glyph determines its feature values in every inventory that uses it, so one matrix per glyph
is the whole of the database's feature information. Each matrix is a constant named by its
glyph in the namespace of `FeatureMatrix`, so that `.«n»` and `.«t̠ʃ»` are feature matrices
wherever one is expected. A feature PHOIBLE marks `0`, not applicable, is left unspecified.

The chart has {len(entries)} glyphs. It omits the {skipped_tone} tones and the {skipped_contour} glyphs with a contour
value such as `-,+`, the prenasalized, secondarily articulated and click segments and the
diphthongs, which a two-valued matrix cannot hold.

Auto-generated by `scripts/gen_phoible.py --chart`. **Do not edit by hand.**

## References

* [moran-mccloy-2019]
-/

namespace Data.PHOIBLE.FeatureMatrix

{body}

end Data.PHOIBLE.FeatureMatrix
"""

# ── Main ───────────────────────────────────────────────────────────────────

REGEN = re.compile(r"python3 scripts/gen_phoible\.py ([a-z]{3}(?:=\d+)?)`")

def recorded_args() -> list:
    """The argument each module in `Inventories/` records for its regeneration."""
    args = []
    for path in sorted(OUT.glob("*.lean")):
        m = REGEN.search(path.read_text(encoding="utf-8"))
        if m is None:
            sys.exit(f"FATAL: {path.relative_to(ROOT)} records no regeneration argument")
        args.append(m.group(1))
    return args

def inventory_modules(args: list) -> dict:
    """The module for each `ISO` or `ISO=ID` argument, keyed by its output path."""
    chosen = {}
    for a in args:
        iso, _, inv = a.lower().partition("=")
        chosen[iso] = int(inv) if inv else None

    # Collect rows per (ISO, InventoryID).
    by_iso = {iso: OrderedDict() for iso in chosen}
    with open(DATA, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            iso = row["ISO6393"].strip().strip('"').lower()
            if iso in by_iso:
                by_iso[iso].setdefault(int(row["InventoryID"]), []).append(row)

    modules = {}
    for iso, inv_id in chosen.items():
        invs = by_iso[iso]
        if not invs:
            sys.stderr.write(f"WARN: no rows for ISO {iso}; skipping\n")
            continue
        first_inv_id = min(invs.keys()) if inv_id is None else inv_id
        if first_inv_id not in invs:
            sys.exit(f"FATAL: ISO {iso} has no inventory {first_inv_id}; it has {sorted(invs)}")
        module_name = lang_module_name(invs[first_inv_id][0]["LanguageName"], iso)
        modules[OUT / f"{module_name}.lean"] = (
            as_module_if_possible(emit_module(iso, invs, module_name, inv_id)),
            len(invs[first_inv_id]), iso, first_inv_id)
    return modules

def main():
    if not DATA.exists():
        sys.stderr.write(f"FATAL: {DATA} not found. Download with:\n")
        sys.stderr.write(f"  curl -sL https://raw.githubusercontent.com/phoible/dev/master/data/phoible.csv -o {DATA}\n")
        sys.exit(1)

    if sys.argv[1:] == ["--check"]:
        stale = []
        if not CHART.exists() or CHART.read_text(encoding="utf-8") != as_module_if_possible(emit_chart()):
            stale.append(CHART)
        for path, (content, *_) in inventory_modules(recorded_args()).items():
            if path.read_text(encoding="utf-8") != content:
                stale.append(path)
        if stale:
            sys.exit("FAIL: out of sync, regenerate: "
                     + ", ".join(str(p.relative_to(ROOT)) for p in stale))
        sys.stdout.write("OK: the PHOIBLE chart and inventories are in sync\n")
        return
    if sys.argv[1:] == ["--chart"]:
        content = as_module_if_possible(emit_chart())
        CHART.write_text(content, encoding="utf-8")
        sys.stdout.write(f"[gen] {CHART.relative_to(ROOT)} ({content.count(chr(10))} lines)\n")
        return

    args = sys.argv[1:] or recorded_args()
    OUT.mkdir(parents=True, exist_ok=True)
    modules = inventory_modules(args)
    for path, (content, n, iso, inv_id) in modules.items():
        path.write_text(content, encoding="utf-8")
        sys.stdout.write(f"[gen] {path.name} ({n} phonemes, ISO {iso}, InvID {inv_id})\n")
    sys.stdout.write(f"\nGenerated {len(modules)} modules under {OUT.relative_to(ROOT)}\n")

if __name__ == "__main__":
    main()
