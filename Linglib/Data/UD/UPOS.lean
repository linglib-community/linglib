module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype

/-!
# Universal Dependencies: part-of-speech tags

Universal Dependencies v2 assigns every word one of seventeen universal part-of-speech tags. The
tags stay close to the eight traditional parts of speech of English: each traditional part of
speech [is one tag or splits into several](##UD.UPOS.exists_traditional_eq), and the tags of
particles, of words of no category, of symbols and of punctuation
[have no traditional counterpart](##UD.UPOS.traditional_eq_none_iff).

## Main definitions

* `UD.UPOS`: the universal part-of-speech tags.
* `UD.UPOS.traditional`: the traditional part of speech a tag refines, if any.

## Implementation notes

The constructors are spelled as in CoNLL-U files, in capitals, and ordered as in the source's
table. A typo or an abbreviation takes the tag of the correct or unabbreviated word, so `X` is
not the tag of either.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

namespace UD

/-- The universal part-of-speech tags of Universal Dependencies, one of which every word of every
language can be assigned. -/
inductive UPOS where
  /-- A common noun. -/
  | NOUN
  /-- A proper noun. -/
  | PROPN
  /-- A main verb. -/
  | VERB
  /-- An auxiliary verb or other tense, aspect or mood particle. -/
  | AUX
  /-- An adjective. -/
  | ADJ
  /-- A determiner, articles included. -/
  | DET
  /-- A cardinal numeral. -/
  | NUM
  /-- An adverb. -/
  | ADV
  /-- A pronoun. -/
  | PRON
  /-- An adposition, a preposition or a postposition. -/
  | ADP
  /-- A coordinating conjunction. -/
  | CCONJ
  /-- A subordinating conjunction. -/
  | SCONJ
  /-- An interjection. -/
  | INTJ
  /-- A particle, a special single-word marker of some languages. -/
  | PART
  /-- A word of no other category, such as a word of a foreign-language expression. -/
  | X
  /-- A symbol other than punctuation, such as a hash sign or an emoji. -/
  | SYM
  /-- Punctuation. -/
  | PUNCT
  deriving DecidableEq, Fintype, Inhabited, Repr

namespace UPOS

/-- There are seventeen tags. -/
theorem card : Fintype.card UPOS = 17 := rfl

/-- The eight traditional parts of speech of English. -/
inductive TraditionalPOS where
  | noun
  | verb
  | adjective
  | adverb
  | pronoun
  | preposition
  | conjunction
  | interjection
  deriving DecidableEq, Fintype, Repr

/-- The traditional part of speech a tag refines, if any. -/
def traditional : UPOS → Option TraditionalPOS
  | NOUN | PROPN => some .noun
  | VERB | AUX => some .verb
  | ADJ | DET | NUM => some .adjective
  | ADV => some .adverb
  | PRON => some .pronoun
  | ADP => some .preposition
  | CCONJ | SCONJ => some .conjunction
  | INTJ => some .interjection
  | PART | X | SYM | PUNCT => none

/-- Every traditional part of speech is refined by a tag. -/
theorem exists_traditional_eq (t : TraditionalPOS) : ∃ p : UPOS, p.traditional = some t := by
  cases t <;> decide

/-- The tags with no traditional counterpart are those of particles, of words of no category, of
symbols and of punctuation. -/
theorem traditional_eq_none_iff {p : UPOS} :
    p.traditional = none ↔ p = PART ∨ p = X ∨ p = SYM ∨ p = PUNCT := by
  cases p <;> decide

end UPOS

end UD
