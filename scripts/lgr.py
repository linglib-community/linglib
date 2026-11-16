"""The Leipzig Glossing Rules as the example data applies them: the conformance level of an
example (CLDF's `LGR_Conformance`) and the segmentation of a word and its gloss into morphs.

Shared by `gen_examples.py`, which emits the level and the segmented words on each Lean row, and
`export_examples_cldf.py`, which writes the level to the CLDF dataset, so that the two cannot
disagree. Pure standard library.
"""

import re

# The punctuation written around the morphs of a word: the brackets of optional material and
# sentence marks. It is dropped from surface morphs, so that `tükörben.` is the morph `tükörben`.
PUNCT = '()[],.!?;:"…'

BOUNDARY = re.compile("[-=]")


def lgr_conformance(pairs):
    """The `LGR_Conformance` of an example with the word-gloss `pairs`: `None` for an example
    with no gloss, `MORPHEME_ALIGNED` when every word and its gloss have the same number of `-`
    and of `=` boundaries (Rules 2 and 2A) and at least one word is segmented, else
    `WORD_ALIGNED`."""
    if not pairs:
        return None
    aligned = all(w.count("-") == g.count("-") and w.count("=") == g.count("=")
                  for w, g in pairs)
    segmented = any("-" in w or "=" in w for w, _ in pairs)
    return "MORPHEME_ALIGNED" if aligned and segmented else "WORD_ALIGNED"


def segment(word, gloss):
    """The surface morphs of `word`, punctuation dropped, and the morph glosses of `gloss`, each
    split at the affix boundary `-` and the clitic boundary `=`. The two lists have the same
    length exactly when the word is segmented as its gloss is."""
    morphs = ["".join(c for c in m if c not in PUNCT) for m in BOUNDARY.split(word)]
    return morphs, BOUNDARY.split(gloss)
