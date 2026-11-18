"""The Leipzig Glossing Rules as the example data applies them: the conformance level of an
example (CLDF's `LGR_Conformance`) and the pairing of a word's morphemes with their glosses, which
follows `pyigt.lgrmorphemes.GlossedWord`.

Shared by `gen_examples.py`, which emits the level and the segmented words on each Lean row, and
`export_examples_cldf.py`, which writes the level to the CLDF dataset, so that the two cannot
disagree. Pure standard library.
"""

import re

# The punctuation written around the morphs of a word: the brackets of optional material and
# sentence marks. It is dropped from surface morphs, so that `tükörben.` is the morph `tükörben`.
PUNCT = '()[],.!?;:"…'

# The morpheme separators of `pyigt.lgrmorphemes`: the affix boundary and the clitic boundary of
# Rule 2 and the reduplication boundary of Rule 10.
MORPHEME_SEPARATORS = "-=~"

_SPLIT = re.compile("([" + re.escape(MORPHEME_SEPARATORS) + "])")


def boundary_symbols(decl):
    """The separators and the marks a data file declares for its source's notation, as two
    strings, or the Leipzig separators and no marks for a file that declares none."""
    if not decl:
        return MORPHEME_SEPARATORS, ""
    return ("".join(lv["symbol"] for lv in decl["levels"]),
            "".join(m["symbol"] for m in decl.get("marks", [])))


def leipzig_pairs(pairs, decl):
    """The word-gloss `pairs` in the notation of the Leipzig rules: each boundary symbol the
    file declares written as the Leipzig separator it declares for it, and its marks dropped."""
    if not decl:
        return pairs
    table = {lv["symbol"]: lv["leipzig"] for lv in decl["levels"]}
    table.update({m["symbol"]: "" for m in decl.get("marks", [])})
    tr = lambda s: "".join(table.get(c, c) for c in s)
    return [(tr(w), tr(g)) for w, g in pairs]


def lgr_conformance(pairs):
    """The `LGR_Conformance` of an example with the word-gloss `pairs`: `None` for an example
    with no gloss, its words unglossed or absent, `MORPHEME_ALIGNED` when every word and its gloss
    have the same number of `-` and of `=` boundaries (Rules 2 and 2A) and at least one word is
    segmented, else `WORD_ALIGNED`."""
    if not any(g for _, g in pairs):
        return None
    aligned = all(w.count("-") == g.count("-") and w.count("=") == g.count("=")
                  for w, g in pairs)
    segmented = any("-" in w or "=" in w for w, _ in pairs)
    return "MORPHEME_ALIGNED" if aligned and segmented else "WORD_ALIGNED"


def glossed_morphemes(word, gloss, decl=None):
    """The (morpheme, gloss, separator) triples of a word, as `pyigt`'s `GlossedWord` pairs
    them, or `None` when the word is not valid: its gloss has a different number of morphemes,
    or a different separator somewhere. The separator is the one before the morpheme, `None` for
    the first, and the morpheme is given without the punctuation written around it. A word the
    source segments without glossing it, its gloss empty, has its morphemes with empty glosses, as
    `pyigt.lgrmorphemes.split_morphemes` segments a word alone. A file that declares the
    boundary symbols of its source is segmented at those, and its marks are dropped from the
    morphemes."""
    seps, marks = boundary_symbols(decl)
    split = re.compile("([" + re.escape(seps) + "])")
    drop = PUNCT + marks
    if not gloss:
        out, sep = [], None
        for m in split.split(word):
            if m in seps and len(m) == 1:
                sep = m
                continue
            form = "".join(c for c in m if c not in drop)
            if not form:
                return None
            out.append((form, "", sep))
            sep = None
        return out or None
    mm, gg = split.split(word), split.split(gloss)
    if len(mm) != len(gg):
        return None
    out, sep = [], None
    for m, g in zip(mm, gg):
        if m in seps and len(m) == 1:
            if m != g:
                return None
            sep = m
            continue
        if not m and not g:
            continue
        form = "".join(c for c in m if c not in drop)
        if not form or not g:
            return None
        out.append((form, g, sep))
        sep = None
    return out or None
