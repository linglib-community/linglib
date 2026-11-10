#!/usr/bin/env python3
"""Generate Lean 4 modules from WALS CLDF data, on demand.

Usage:
    python3 scripts/gen_wals.py [FEATURE_IDS...] [--prune] [--check]

Examples:
    python3 scripts/gen_wals.py            # every feature some module imports
    python3 scripts/gen_wals.py 81A        # a feature a study is about to import
    python3 scripts/gen_wals.py --prune    # also delete features nothing imports
    python3 scripts/gen_wals.py --check    # verify sync; writes nothing

A feature is generated only when a module imports it: the import graph is the
manifest. Adding a chapter means adding the import and running this script.

Reads from:  Linglib/Data/WALS/raw/*.csv
Writes to:   Linglib/Data/WALS/Features/F{ID}.lean
             Linglib/Data/WALS/Languages.lean (only when some module imports it)

Each feature module holds the value enum and `allData : List (String × V)`,
rows keyed by WALS code and sorted by it, each row commented with the lect's
name; lookup is core `List.lookup`. Features in WITH_SOURCES also get
`sources : List (String × String)`, the WALS source of each row.

Features can be configured in FEATURES (manually curated constructor names)
or auto-generated from codes.csv (AUTO_FEATURES). AUTO_FEATURES need only
an enum name; constructor names are derived from the WALS value labels.
"""

import csv
import re
import sys
import textwrap
from functools import cache
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402
from check_orphan_imports import IMPORT_RE  # noqa: E402
from collections import defaultdict

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "Linglib" / "Data" / "WALS" / "raw"
OUT  = ROOT / "Linglib" / "Data" / "WALS"

# ── Helpers for auto-generating Lean constructor names ─────────────────────

def name_to_constructor(name):
    """Convert a WALS value name to a valid Lean constructor name.

    Examples:
        "SOV" → "sov"
        "No dominant order" → "noDominantOrder"
        "Definite word distinct from demonstrative" → "definiteWordDistinctFromDemonstrative"
        "6-7 cases" → "cases6_7"
        "10 or more cases" → "cases10OrMore"
        "Negative affix" → "negativeAffix"
    """
    s = name.strip()

    # Handle leading numbers: "10 or more cases" → "cases10OrMore", "6-7 cases" → "cases6_7"
    m = re.match(r'^(\d+)\s+or\s+more\s+(.+)', s)
    if m:
        num, rest = m.group(1), m.group(2)
        rest_id = name_to_constructor(rest)
        return f"{rest_id}{num}OrMore"

    m = re.match(r'^(\d+)(?:\s*[-–]\s*(\d+))?\s+(.+)', s)
    if m:
        num1, num2, rest = m.group(1), m.group(2), m.group(3)
        rest_id = name_to_constructor(rest)
        if num2:
            return f"{rest_id}{num1}_{num2}"
        return f"{rest_id}{num1}"

    # Remove parenthetical qualifiers
    s = re.sub(r'\s*\(.*?\)', '', s)
    # Remove quotes
    s = s.replace("'", "").replace("'", "").replace('"', '')
    # Replace punctuation/separators with spaces
    s = re.sub(r'[^a-zA-Z0-9\s]', ' ', s)
    # Split into words and camelCase
    words = s.split()
    if not words:
        return "unknown"
    result = words[0].lower() + ''.join(w.capitalize() for w in words[1:])
    # Ensure it starts with a letter
    if result and result[0].isdigit():
        result = "v" + result
    return result


# ── Feature configuration ─────────────────────────────────────────────────
# FEATURES: manually curated constructor names (highest quality).
# AUTO_FEATURES: auto-generated constructors from WALS labels.
# Both produce identical output; the only difference is how constructor
# names are determined.

FEATURES = {
    "106A": {
        "name": "Reciprocal Constructions",
        "chapter": 106,
        "enum": "ReciprocalType",
        "author": "maslova-nedjalkov-2013",
        "values": {
            1: ("noReciprocalConstruction", "No reciprocal construction"),
            2: ("distinctFromReflexive", "Distinct from reflexive"),
            3: ("mixed", "Mixed"),
            4: ("identicalToReflexive", "Identical to reflexive"),
        },
    },
    "107A": {
        "name": "Passive Constructions",
        "chapter": 107,
        "enum": "PassiveType",
        "author": "siewierska-2013",
        "values": {
            1: ("present", "Present"),
            2: ("absent", "Absent"),
        },
    },
    "108A": {
        "name": "Antipassive Constructions",
        "chapter": 108,
        "enum": "AntipassiveType",
        "author": "polinsky-2013-antipassive",
        "values": {
            1: ("implicitPatient", "Implicit patient"),
            2: ("obliquePatient", "Oblique patient"),
            3: ("noAntipassive", "No antipassive"),
        },
    },
    "108B": {
        "name": "Productivity of the Antipassive Construction",
        "chapter": 108,
        "enum": "AntipassiveProductivity",
        "author": "polinsky-2013-antipassive",
        "values": {
            1: ("productive", "Productive"),
            2: ("partiallyProductive", "Partially productive"),
            3: ("notProductive", "Not productive"),
            4: ("noAntipassive", "No antipassive"),
        },
    },
    "109A": {
        "name": "Applicative Constructions",
        "chapter": 109,
        "enum": "ApplicativeType",
        "author": "polinsky-2013-applicative",
        "values": {
            1: ("benefactiveBothBases", "Benefactive object; both bases"),
            2: ("benefactiveTransOnly", "Benefactive object; only transitive"),
            3: ("benefactiveAndOtherBothBases", "Benefactive and other; both bases"),
            4: ("benefactiveAndOtherTransOnly", "Benefactive and other; only transitive"),
            5: ("nonBenefactiveBothBases", "Non-benefactive object; both bases"),
            6: ("nonBenefactiveTransOnly", "Non-benefactive object; only transitive"),
            7: ("nonBenefactiveIntransOnly", "Non-benefactive object; only intransitive"),
            8: ("noApplicative", "No applicative construction"),
        },
    },
    "109B": {
        "name": "Other Roles of Applied Objects",
        "chapter": 109,
        "enum": "AppliedObjectRole",
        "author": "polinsky-2013-applicative",
        "values": {
            1: ("instrument", "Instrument"),
            2: ("locative", "Locative"),
            3: ("instrumentAndLocative", "Instrument and locative"),
            4: ("onlyBenefactive", "No other roles (= Only benefactive)"),
            5: ("noApplicative", "No applicative construction"),
        },
    },
    "110A": {
        "name": "Periphrastic Causative Constructions",
        "chapter": 110,
        "enum": "PeriphrasticCausativeType",
        "author": "song-2013-periphrastic",
        "values": {
            1: ("sequentialOnly", "Sequential but no purposive"),
            2: ("purposiveOnly", "Purposive but no sequential"),
            3: ("both", "Both"),
        },
    },
    "111A": {
        "name": "Nonperiphrastic Causative Constructions",
        "chapter": 111,
        "enum": "NonperiphrCausativeType",
        "author": "song-2013-nonperiphrastic",
        "values": {
            1: ("neither", "Neither"),
            2: ("morphologicalOnly", "Morphological but no compound"),
            3: ("compoundOnly", "Compound but no morphological"),
            4: ("both", "Both"),
        },
    },
}

# Auto-generated features: enum name + optional author override.
# Constructor names are derived from WALS value labels in codes.csv.
AUTO_FEATURES = {
    # ── Word Order (Ch 81–90) ──────────────────────────────────────────
    "81A": {"enum": "BasicWordOrder",      "author": "dryer-2013-wals"},
    "82A": {"enum": "SubjectVerbOrder",    "author": "dryer-2013-wals"},
    "83A": {"enum": "ObjectVerbOrder",     "author": "dryer-2013-wals"},
    "84A": {"enum": "ObjectObliqueVerbOrder", "author": "dryer-2013-wals"},
    "85A": {"enum": "AdpositionNPOrder",   "author": "dryer-2013-wals"},
    "86A": {"enum": "GenitiveNounOrder",   "author": "dryer-2013-wals"},
    "87A": {"enum": "AdjectiveNounOrder",  "author": "dryer-2013-wals"},
    "88A": {"enum": "DemonstrativeNounOrder", "author": "dryer-2013-wals"},
    "89A": {"enum": "NumeralNounOrder",    "author": "dryer-2013-wals"},
    "90A": {"enum": "RelClauseNounOrder",  "author": "dryer-2013-wals"},

    # ── Articles/Determiners (Ch 37–38) ────────────────────────────────
    "37A": {"enum": "DefiniteArticleType", "author": "dryer-2013-wals"},
    "38A": {"enum": "IndefiniteArticleType", "author": "dryer-2013-wals"},

    # ── Case (Ch 49–51) ────────────────────────────────────────────────
    "49A": {"enum": "CaseCount",           "author": "iggesen-2013"},
    "50A": {"enum": "AsymmetricalCaseMarking", "author": "iggesen-2013"},
    "51A": {"enum": "CaseAffixPosition",   "author": "iggesen-2013"},

    # ── Tense/Aspect (Ch 65–69) ────────────────────────────────────────
    "65A": {"enum": "PerfectiveImperfective", "author": "dahl-2013"},
    "66A": {"enum": "PastTenseType",       "author": "dahl-2013"},
    "67A": {"enum": "FutureTenseType",     "author": "dahl-2013"},
    "68A": {"enum": "PerfectType",         "author": "dahl-2013"},
    "69A": {"enum": "TenseAspectAffixPosition", "author": "dryer-2013-wals"},

    # ── Modality/Evidentiality (Ch 74–78) ──────────────────────────────
    "74A": {"enum": "SituationalPossibility", "author": "vanderauwera-ammann-2013"},
    "75A": {"enum": "EpistemicPossibility", "author": "vanderauwera-ammann-2013"},
    "76A": {"enum": "ModalOverlap",        "author": "vanderauwera-ammann-2013"},
    "77A": {"enum": "EvidentialityDistinctions", "author": "de-haan-2013"},
    "78A": {"enum": "EvidentialityCoding", "author": "de-haan-2013b"},

    # ── Negation (Ch 112–115, 143) ─────────────────────────────────────
    "112A": {"enum": "NegativeMorphemeType", "author": "dryer-2013-wals"},
    "113A": {"enum": "NegationSymmetry",   "author": "miestamo-2013"},
    "114A": {"enum": "AsymmetricNegationSubtype", "author": "miestamo-2013"},
    "115A": {"enum": "NegativeIndefiniteType", "author": "haspelmath-2013"},
    "143A": {"enum": "NegVerbOrder",       "author": "dryer-2013-wals"},

    # ── Questions (Ch 116) ─────────────────────────────────────────────
    "116A": {"enum": "PolarQuestionType",  "author": "dryer-2013-wals"},

    # ── Gender/Number (Ch 30–31, 33–35) ────────────────────────────────
    "30A": {"enum": "GenderCount",         "author": "corbett-2013"},
    "31A": {"enum": "GenderBasis",         "author": "corbett-2013"},
    "33A": {"enum": "PluralityCoding",     "author": "dryer-2013-wals"},
    "34A": {"enum": "PluralityOccurrence", "author": "haspelmath-2013b"},
    "35A": {"enum": "PronounPlurality",    "author": "daniel-2013"},

    # ── Reflexives (Ch 47) ─────────────────────────────────────────────
    "47A": {"enum": "IntensifierReflexive", "author": "koenig-siemund-2013"},

    # ── Comparatives/Relatives (Ch 121–123) ────────────────────────────
    "121A": {"enum": "ComparativeType",    "author": "stassen-2013"},
    "122A": {"enum": "SubjectRelativization", "author": "comrie-kuteva-2013a"},
    "123A": {"enum": "ObliqueRelativization", "author": "comrie-kuteva-2013b"},

    # ── Morphology (Ch 20–22, 26–27) ──────────────────────────────────
    "20A": {"enum": "FusionType",          "author": "bickel-nichols-2013a"},
    "21A": {"enum": "ExponenceType",       "author": "bickel-nichols-2013b"},
    "22A": {"enum": "InflectionalSynthesis", "author": "bickel-nichols-2013c"},
    "26A": {"enum": "PrefixSuffixPreference", "author": "dryer-2013-wals"},
    "27A": {"enum": "ReduplicationType",   "author": "rubino-2013"},

    # ── Alignment (Ch 98–100) ──────────────────────────────────────────
    "98A": {"enum": "NPCaseAlignment",     "author": "comrie-2013b"},
    "99A": {"enum": "PronounCaseAlignment", "author": "comrie-2013b"},
    "100A": {"enum": "VerbalPersonAlignment", "author": "siewierska-2013b"},

    # ── Predication (Ch 117–120) ───────────────────────────────────────
    "117A": {"enum": "PredicativePossession", "author": "stassen-2013b"},
    "118A": {"enum": "PredicativeAdjectiveType", "author": "stassen-2013b"},
    "119A": {"enum": "NominalLocationalPredication", "author": "stassen-2013b"},
    "120A": {"enum": "ZeroCopulaType",     "author": "stassen-2013b"},

    # ── Complement/Adverbial Clauses (Ch 121–128) ──────────────────────
    "124A": {"enum": "WantComplementSubject", "author": "cristofaro-2013"},
    "125A": {"enum": "PurposeClauseType",  "author": "cristofaro-2013"},
    "126A": {"enum": "WhenClauseType",     "author": "cristofaro-2013"},
    "127A": {"enum": "ReasonClauseType",   "author": "cristofaro-2013"},
    "128A": {"enum": "UtteranceComplementType", "author": "cristofaro-2013"},
}


def load_codes():
    """Load WALS value codes from codes.csv."""
    codes = defaultdict(dict)  # feature_id → {number → name}
    with open(DATA / "codes.csv", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            codes[row["Parameter_ID"]][int(row["Number"])] = row["Name"]
    return codes


def load_parameters():
    """Load WALS feature metadata from parameters.csv."""
    params = {}
    with open(DATA / "parameters.csv", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            params[row["ID"]] = {
                "name": row["Name"],
                "chapter": int(re.match(r'\d+', row["ID"]).group()),
            }
    return params


def feature_name_to_enum(name):
    """Convert a WALS feature name to a Lean enum type name.

    Examples:
        "Consonant Inventories" → "ConsonantInventories"
        "The Velar Nasal" → "VelarNasal"
        "M-T Pronouns" → "MtPronouns"
    """
    s = name.strip()
    # Remove leading articles
    s = re.sub(r'^(The|A|An)\s+', '', s)
    # Remove parenthetical qualifiers
    s = re.sub(r'\s*\(.*?\)', '', s)
    # Remove quotes
    s = s.replace("'", "").replace("'", "").replace('"', '')
    # Replace punctuation/separators with spaces
    s = re.sub(r'[^a-zA-Z0-9\s]', ' ', s)
    # PascalCase
    words = s.split()
    if not words:
        return "Unknown"
    result = ''.join(w.capitalize() for w in words)
    # Ensure starts with letter
    if result and result[0].isdigit():
        result = "V" + result
    return result


def split_camel_words(name):
    """Split a camelCase identifier into word tokens.

    Tokens are runs of lowercase, single-uppercase + lowercase, or
    digit/underscore. This preserves things like `cases6_7` and
    `categoriesPerWord10_11` as splittable units.

    Examples:
        "noDominantOrder" → ["no", "Dominant", "Order"]
        "cases6_7"        → ["cases", "6_7"]
        "sov"             → ["sov"]
    """
    return re.findall(r'[a-z]+|[A-Z][a-z]*|[0-9_]+', name)


# Lean 4 reserved keywords / common identifiers we must not produce as constructor names.
# Stripping a prefix from e.g. `internallyHeadedExists` to `exists` would collide with
# Lean's `∃` keyword and break the inductive declaration.
LEAN_RESERVED = {
    "exists", "forall", "fun", "let", "have", "match", "with", "where",
    "do", "if", "then", "else", "by", "from", "show", "suffices",
    "in", "out", "for", "while", "return", "break", "continue",
    "namespace", "section", "end", "import", "open", "instance",
    "theorem", "lemma", "def", "structure", "inductive", "class",
    "true", "false", "this",
}


def strip_common_camel_prefix(ctors):
    """Drop a shared leading word prefix from a set of camelCase names.

    Returns a dict mapping each input name to its stripped form, or
    `{c: c for c in ctors}` (no-op) if no useful prefix exists.

    The prefix is meaningful only if:
      * at least 2 ctors are present
      * at least one shared word at the start (case-insensitive on first letter)
      * shared prefix is ≥ 4 characters
      * stripping leaves every ctor with at least one remaining word
      * no stripped name would collide with an existing one or each other

    The first letter of each stripped name is lowercased so the result
    remains a valid Lean identifier in lowerCamelCase.
    """
    if len(ctors) < 2:
        return {c: c for c in ctors}

    word_lists = {c: split_camel_words(c) for c in ctors}
    if any(not ws for ws in word_lists.values()):
        return {c: c for c in ctors}

    # Find longest shared word-prefix length (case-insensitive).
    min_len = min(len(ws) for ws in word_lists.values())
    shared_n = 0
    for i in range(min_len):
        firsts = {ws[i].lower() for ws in word_lists.values()}
        if len(firsts) == 1:
            shared_n = i + 1
        else:
            break

    if shared_n == 0 or shared_n == min_len:
        return {c: c for c in ctors}

    # Prefix must be substantive (≥ 4 chars) — otherwise stripping `no` etc.
    # produces noisier names than it removes.
    sample_words = next(iter(word_lists.values()))
    prefix_str = ''.join(sample_words[:shared_n])
    if len(prefix_str) < 4:
        return {c: c for c in ctors}

    rename = {}
    for c, ws in word_lists.items():
        rest = ws[shared_n:]
        # Lowercase the first letter to keep lowerCamelCase.
        head = rest[0]
        head = head[0].lower() + head[1:]
        stripped = head + ''.join(rest[1:])
        # Per-name fallback: a single Lean reserved word (e.g. `exists` from
        # `internallyHeadedExists`) used to discard the entire rename, leaving
        # every constructor with the verbose prefix. Suffix the colliding name
        # with `_` instead — `exists_` is a valid Lean identifier.
        if stripped in LEAN_RESERVED:
            stripped = stripped + "_"
        rename[c] = stripped

    # Reject if any stripped name collides or is empty.
    new_names = list(rename.values())
    if len(set(new_names)) != len(new_names):
        return {c: c for c in ctors}
    if any(not n for n in new_names):
        return {c: c for c in ctors}
    # Reject if any stripped name starts with a non-letter (e.g. digit-only rest).
    if any(not n[0].isalpha() for n in new_names):
        return {c: c for c in ctors}

    return rename


# Chapter→bibkey map, derived once from the curated AUTO_FEATURES entries.
# Authors of WALS chapters are stable across features within a chapter, so a
# feature like 90D (chapter 90) inherits the bibkey from any curated 90X.
_CHAPTER_AUTHOR = {}
for _fid, _cfg in AUTO_FEATURES.items():
    _ch_match = re.match(r'\d+', _fid)
    if not _ch_match:
        continue
    _ch = int(_ch_match.group())
    _author = _cfg.get("author")
    if _author and _ch not in _CHAPTER_AUTHOR:
        _CHAPTER_AUTHOR[_ch] = _author
# Same for FEATURES (curated entries use a `chapter` key directly).
for _fid, _cfg in FEATURES.items():
    _ch = _cfg.get("chapter")
    _author = _cfg.get("author")
    if _ch is not None and _author and _ch not in _CHAPTER_AUTHOR:
        _CHAPTER_AUTHOR[_ch] = _author

# Track chapters we've already warned about, so each missing author prints once.
_WARNED_CHAPTERS = set()

def chapter_author(chapter):
    """Look up the bibkey for the author of a WALS chapter.

    Falls back to `wals-2013` (the generic WALS Online citation) and prints a
    one-time warning for any chapter without a curated author. Add the chapter
    to FEATURES or AUTO_FEATURES with an `author` field to silence the warning.
    """
    if chapter in _CHAPTER_AUTHOR:
        return _CHAPTER_AUTHOR[chapter]
    if chapter not in _WARNED_CHAPTERS:
        print(f"  ⚠ chapter {chapter}: no curated author, using wals-2013 fallback")
        _WARNED_CHAPTERS.add(chapter)
    return "wals-2013"


def resolve_feature(feature_id, codes, params):
    """Resolve a feature config — from FEATURES if curated, else auto-generate.

    Features not in FEATURES or AUTO_FEATURES are fully auto-generated
    from parameters.csv and codes.csv.
    """
    if feature_id in FEATURES:
        return FEATURES[feature_id]

    auto = AUTO_FEATURES.get(feature_id)
    param = params.get(feature_id, {})
    feat_codes = codes.get(feature_id, {})

    if not feat_codes:
        return None  # No codes at all — skip

    # Auto-generate values from codes.csv
    raw_values = {}
    seen_ctors = set()
    for num in sorted(feat_codes):
        label = feat_codes[num]
        ctor = name_to_constructor(label)
        # Deduplicate constructor names
        if ctor in seen_ctors:
            ctor = f"{ctor}_{num}"
        seen_ctors.add(ctor)
        raw_values[num] = (ctor, label)

    # Strip shared word prefix if present (e.g. inflectionalOptative{Present,Absent}
    # → present/absent). Curated FEATURES are exempt — their constructor names are
    # hand-chosen and shouldn't be auto-stripped.
    raw_ctors = [c for c, _ in raw_values.values()]
    rename = strip_common_camel_prefix(raw_ctors)
    values = {num: (rename[c], label) for num, (c, label) in raw_values.items()}

    # Determine enum name: from AUTO_FEATURES if present, else derived from feature name
    chapter = param.get("chapter", 0)
    if auto:
        enum_name = auto["enum"]
        author = auto.get("author") or chapter_author(chapter)
    else:
        enum_name = feature_name_to_enum(param.get("name", feature_id))
        author = chapter_author(chapter)

    return {
        "name": param.get("name", feature_id),
        "chapter": param.get("chapter", 0),
        "enum": enum_name,
        "author": author,
        "values": values,
    }


@cache
def load_languages():
    """Load WALS language metadata."""
    langs = {}
    with open(DATA / "languages.csv", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            langs[row["ID"]] = {
                "name": row["Name"],
                "iso": row["ISO639P3code"],
                "family": row["Family"],
                "genus": row["Genus"],
            }
    return langs


@cache
def load_all_values():
    """All datapoints by feature, each list sorted by WALS code."""
    by_feature = defaultdict(list)
    with open(DATA / "values.csv", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            by_feature[row["Parameter_ID"]].append({
                "language_id": row["Language_ID"],
                "value": int(row["Value"]),
                "source": row["Source"],
            })
    for entries in by_feature.values():
        entries.sort(key=lambda e: e["language_id"])
        codes = [e["language_id"] for e in entries]
        assert len(codes) == len(set(codes)), "a feature codes some lect twice"
    return by_feature


def load_values(feature_id):
    """The datapoints of a WALS feature, sorted by WALS code."""
    return load_all_values().get(feature_id, [])


def lean_safe_string(s):
    """Escape a string for use in Lean string literals."""
    return s.replace("\\", "\\\\").replace('"', '\\"')


# Features whose per-row WALS source a study reads (`F{ID}.sources`).
WITH_SOURCES = {"101A"}

# Rows per list literal: larger literals hit Lean's maxRecDepth.
CHUNK = 500

# Line width of the generated Lean.
WIDTH = 100


def doc_lines(text, indent=""):
    """A `/-- … -/` docstring, wrapped to WIDTH."""
    return textwrap.wrap(f'/-- {text} -/', WIDTH, initial_indent=indent,
                         subsequent_indent=indent + "  ", break_on_hyphens=False)


def row_lines(prefix, lit, comment):
    """A list-literal row: `prefix lit -- comment` on one line when it fits; else the
    comment on a line of its own, and the literal broken between string elements."""
    one = f'{prefix} {lit}' + (f' -- {comment}' if comment else '')
    if len(one) <= WIDTH:
        return [one]
    out = [f'  -- {comment}'] if comment else []
    line = f'{prefix} '
    for i, piece in enumerate(re.split(r'(?<=[^\\]", )(?=")', lit)):
        if i and len(line) + len(piece) > WIDTH:
            out.append(line.rstrip())
            line = '      '
        line += piece
    return out + [line]


def emit_table(name, elem_type, rows, doc):
    """Lines defining `name : List elem_type` from `(literal, comment)` rows, split
    into `name_0 ++ name_1 ++ …` chunks when the table is long."""
    def literal(chunk_name, chunk):
        out = [f'def {chunk_name} : List ({elem_type}) :=']
        for i, (lit, comment) in enumerate(chunk):
            out += row_lines("  [" if i == 0 else "  ,", lit, comment)
        out.append('  ]')
        return out

    if len(rows) <= CHUNK:
        return doc_lines(doc) + literal(name, rows) + ['']
    lines = []
    chunks = [rows[i:i + CHUNK] for i in range(0, len(rows), CHUNK)]
    for ci, chunk in enumerate(chunks):
        lines += doc_lines(f'Rows {ci * CHUNK + 1} to {ci * CHUNK + len(chunk)} of `{name}`.')
        lines += literal(f'{name}_{ci}', chunk) + ['']
    refs = ' ++ '.join(f'{name}_{i}' for i in range(len(chunks)))
    return lines + doc_lines(doc) + [f'def {name} : List ({elem_type}) := {refs}', '']


def generate_feature(feature_id, cfg, langs):
    """Generate a Lean module for a single WALS feature."""
    entries = load_values(feature_id)

    # Count per value
    counts = defaultdict(int)
    for e in entries:
        counts[e["value"]] += 1

    def name(e):
        return langs.get(e["language_id"], {}).get("name", "")

    lines = []

    # Module docstring
    lines.append(f'/-!')
    lines.append(f'# WALS Feature {feature_id}: {cfg["name"]}')
    lines.append(f'[{cfg["author"]}]')
    lines.append(f'')
    lines.append(f'Auto-generated from WALS v2020.4 CLDF data.')
    lines.append(f'**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py {feature_id}`.')
    lines.append(f'')
    lines.append(f'Chapter {cfg["chapter"]}, {len(entries)} languages.')
    lines.append(f'-/')
    lines.append(f'')
    lines.append(f'namespace Data.WALS.F{feature_id}')
    lines.append(f'')

    # Value enum
    lines.append(f'/-- WALS {feature_id} values. -/')
    lines.append(f'inductive {cfg["enum"]} where')
    for num in sorted(cfg["values"]):
        ctor, desc = cfg["values"][num]
        lines += doc_lines(f'{desc} ({counts.get(num, 0)} languages).', "  ")
        lines.append(f'  | {ctor}')
    lines.append(f'  deriving DecidableEq, Repr')
    lines.append(f'')

    # Count claims live in the per-constructor `/-- ... (N languages). -/` comments.
    # We don't emit `count_*` theorems: the count and the list come from the same CSV
    # pass in this generator, so they cannot disagree. The integrity property worth
    # checking ("Lean file matches WALS CSV") is `--check`, outside Lean.
    rows = [(f'("{e["language_id"]}", .{cfg["values"][e["value"]][0]})', name(e))
            for e in entries]
    lines += emit_table(
        'allData', f'String × {cfg["enum"]}', rows,
        f'The WALS {feature_id} coding: each language\'s value, keyed by its WALS code '
        f'({len(entries)} languages).')

    if feature_id in WITH_SOURCES:
        def refs(e):
            return ", ".join(f'"{lean_safe_string(r)}"' for r in e["source"].split(";"))
        rows = [(f'("{e["language_id"]}", [{refs(e)}])', name(e)) for e in entries if e["source"]]
        lines += emit_table(
            'sources', 'String × List String', rows,
            f'The sources WALS cites for each language\'s {feature_id} value, keyed by its WALS '
            f'code: WALS reference keys, with pages in brackets ({len(rows)} languages).')

    lines.append(f'end Data.WALS.F{feature_id}')
    lines.append(f'')

    return "\n".join(lines)


def generate_languages(langs, used_ids):
    """Generate the shared Languages module: every lect some feature codes.

    Splits the language list into chunks of 500 to avoid Lean's
    maxRecDepth limit on large list literals. ISO and Glottocode are
    attributes of a lect here, never keys: several lects share one.
    """
    sorted_langs = sorted(
        ((lid, langs[lid]) for lid in sorted(used_ids) if lid in langs),
        key=lambda x: x[1]["name"]
    )
    total = len(sorted_langs)
    CHUNK = 500

    lines = []
    lines.append('/-!')
    lines.append('# WALS Language Metadata')
    lines.append('')
    lines.append('Auto-generated from WALS v2020.4 CLDF data.')
    lines.append('**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py`.')
    lines.append('')
    lines.append(f'{total} languages referenced across generated features.')
    lines.append('-/')
    lines.append('')
    lines.append('namespace Data.WALS')
    lines.append('')
    lines.append('/-- WALS language metadata. -/')
    lines.append('structure Language where')
    lines.append('  walsCode : String')
    lines.append('  name : String')
    lines.append('  iso : String')
    lines.append('  family : String')
    lines.append('  genus : String')
    lines.append('  deriving DecidableEq, Repr')
    lines.append('')

    # Split into chunks
    chunks = []
    for start in range(0, total, CHUNK):
        chunk = sorted_langs[start:start + CHUNK]
        chunks.append(chunk)

    for ci, chunk in enumerate(chunks):
        lines.append(f'/-- Languages {ci * CHUNK + 1} to {ci * CHUNK + len(chunk)} of `languages`. -/')
        lines.append(f'def languages_{ci} : List Language :=')
        for i, (lid, lang) in enumerate(chunk):
            name = lean_safe_string(lang["name"])
            iso = lang["iso"]
            family = lean_safe_string(lang["family"])
            genus = lean_safe_string(lang["genus"])
            prefix = "  [" if i == 0 else "  ,"
            lines.append(
                f'{prefix} {{ walsCode := "{lid}", name := "{name}", iso := "{iso}", '
                f'family := "{family}", genus := "{genus}" }}'
            )
        lines.append('  ]')
        lines.append('')

    lines.append(f'/-- All languages referenced in generated WALS features ({total}). -/')
    chunk_refs = ' ++ '.join(f'languages_{i}' for i in range(len(chunks)))
    lines.append(f'def languages : List Language := {chunk_refs}')
    lines.append('')
    lines.append('end Data.WALS')
    lines.append('')

    return "\n".join(lines)


REFERENCES_BIB = ROOT / "references.bib"

def load_bib_keys():
    """Return the set of bibkeys defined in references.bib."""
    keys = set()
    with open(REFERENCES_BIB, encoding="utf-8") as f:
        for line in f:
            m = re.match(r'\s*@\w+\{\s*([^,\s]+)\s*,', line)
            if m:
                keys.add(m.group(1))
    return keys


WALS_MODULE = "Linglib.Data.WALS."


def imported_wals_modules():
    """The `Linglib.Data.WALS.*` modules some module outside `Data/WALS/` imports.
    `Linglib.lean`, which imports the whole library, is not read."""
    mods = set()
    for path in (p for d in ("Linglib", "Studies") for p in (ROOT / d).rglob("*.lean")):
        if OUT in path.parents:
            continue
        for line in path.read_text(encoding="utf-8").splitlines():
            m = IMPORT_RE.match(line)
            if m and m.group(1).startswith(WALS_MODULE):
                mods.add(m.group(1).removeprefix(WALS_MODULE))
    return mods


def feature_order(fid):
    return (int(re.match(r'\d+', fid).group()), fid)


def main():
    args = sys.argv[1:]
    check_only = "--check" in args
    prune = "--prune" in args
    explicit = [a for a in args if not a.startswith("--")]

    codes = load_codes()
    params = load_parameters()
    imported = imported_wals_modules()
    demanded = {m.removeprefix("Features.F") for m in imported if m.startswith("Features.F")}
    unknown = sorted(demanded - params.keys())
    if unknown:
        print(f"ERROR: imported features absent from parameters.csv: {', '.join(unknown)}")
        sys.exit(1)
    feature_ids = sorted(demanded | set(explicit), key=feature_order)

    resolved = {}
    for fid in feature_ids:
        cfg = resolve_feature(fid, codes, params)
        if cfg is None:
            print(f"Warning: skipping {fid} (no codes found).")
            continue
        resolved[fid] = cfg

    # Validate every emitted citation key against references.bib BEFORE writing
    # any files: a broken key propagates to every feature sharing that author.
    bib_keys = load_bib_keys()
    bad_cites = {fid: cfg["author"] for fid, cfg in resolved.items()
                 if cfg["author"] not in bib_keys}
    if bad_cites:
        print(f"\nERROR: {len(bad_cites)} feature(s) reference unknown bibkeys:")
        for fid, key in sorted(bad_cites.items()):
            print(f"  {key} → {fid}")
        sys.exit(1)

    langs = load_languages()
    wanted = {OUT / "Features" / f"F{fid}.lean":
              as_module_if_possible(generate_feature(fid, cfg, langs))
              for fid, cfg in resolved.items()}
    if "Languages" in imported:
        used = {e["language_id"] for es in load_all_values().values() for e in es}
        wanted[OUT / "Languages.lean"] = as_module_if_possible(generate_languages(langs, used))
    present = set((OUT / "Features").glob("F*.lean"))
    if (OUT / "Languages.lean").exists():
        present.add(OUT / "Languages.lean")
    orphans = sorted(present - wanted.keys())

    if check_only:
        stale = sorted(p for p, text in wanted.items()
                       if not p.exists() or p.read_text(encoding="utf-8") != text)
        for p in stale:
            print(f"STALE or MISSING: {p.relative_to(ROOT)}")
        for p in orphans:
            print(f"ORPHAN (nothing imports it): {p.relative_to(ROOT)}")
        if stale or orphans:
            print("Run `python3 scripts/gen_wals.py --prune` and commit the result.")
            sys.exit(1)
        print(f"--check OK: {len(wanted)} WALS modules, all imported and in sync.")
        return

    for path, text in wanted.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        print(f"  → {path.relative_to(ROOT)}")
    for path in orphans:
        if prune:
            path.unlink()
            print(f"  ✗ {path.relative_to(ROOT)} (nothing imports it)")
        else:
            print(f"  orphan: {path.relative_to(ROOT)} (nothing imports it; --prune deletes)")


if __name__ == "__main__":
    main()
