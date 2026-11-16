/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Schema

/-!
# The gloss line as structured data

A glossed token is already structured: the Leipzig Glossing Rules segment the surface word and
its gloss at the same affix and clitic boundaries (Rule 2), separate by periods the several
metalanguage elements that render one object-language element (Rule 4), and write grammatical
category labels in capitals (Rule 3), so a row's gloss line determines a morph-by-morph token
stream without any analysis beyond the source's own. The generator pairs each word's morphemes
with their glosses in a `GlossedWord` of `Data/Examples/Schema.lean`, the row's `glossedWords`,
and this file reads that structure: a gloss element is a category label or a lexical gloss by
its capitalization. Readers built on it consult the row's form
rather than a curated feature, the first step from annotated stimuli toward parsed ones.

## Main definitions

* `Gloss.toLower`: `Char.toLower` extended over the Latin-1 Supplement and Latin Extended-A
  capitals, for sentence-initial tokens in European orthographies.
* `Gloss.segments`: the morphs of a token, split at the `-` and `=` boundaries.
* `Gloss.elements`, `Gloss.IsLabel`, `Gloss.labels`: the period-separated elements of a morph's
  gloss, an element being a category label when written without lower-case letters, and the
  labels of a gloss.
* `GlossedWord.IsValid`, `GlossedWord.morphs`, `GlossedWord.glosses`, `GlossedWord.form`: the
  word has its morphemes, their forms and glosses, and the word without separators.
* `Datum.glossedWord?`: the glossed word of a row printed as a given form.
* `GlossedWord.stem`, `GlossedWord.wordform`, `GlossedWord.labels`,
  `GlossedWord.lexicalGloss?`, `GlossedWord.lexicalMorph?`: the first surface morph and the
  joined word, decapitalized, the word's category labels, and its first lexical gloss with the
  morph it glosses.

## Implementation notes

* Everything is defined on `List Char`: the kernel reduces list operations where the positional
  `String` primitives get stuck, and the readers built here are consumed by `decide`.
* A word that is not valid, its surface and gloss segmented differently, has no morphemes but
  keeps its category labels and its lexical gloss, read off its gloss; `GlossedWord.stem` and
  `GlossedWord.lexicalMorph?` need the morphemes.

## References

* [comrie-haspelmath-bickel-2008]
-/

@[expose] public section

namespace Gloss

/-- `Char.toLower` extended over the Latin-1 Supplement and Latin Extended-A capitals by the
Unicode case pairings of those blocks, with dotted İ lowered to `i`; `Char.toLower` itself only
lowers ASCII. -/
def toLower (c : Char) : Char :=
  if c.toNat = 0x130 then 'i'
  else if 0xC0 ≤ c.toNat ∧ c.toNat ≤ 0xDE ∧ c.toNat ≠ 0xD7 then Char.ofNat (c.toNat + 0x20)
  else if 0x100 ≤ c.toNat ∧ c.toNat ≤ 0x177 ∧ c.toNat % 2 = 0 then Char.ofNat (c.toNat + 1)
  else c.toLower

example : toLower 'Á' = 'á' := by decide
example : toLower 'Ő' = 'ő' := by decide
example : toLower 'L' = 'l' := by decide
example : toLower 'é' = 'é' := by decide

/-- Splits a list of characters at the given separators. Core has `List.splitOn`, but its body
does not reduce across the module boundary under `decide`, so the recursion is restated here
structurally. -/
def split (seps : List Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    let rest := split seps cs
    if c ∈ seps then [] :: rest
    else
      match rest with
      | r :: rs => (c :: r) :: rs
      | [] => [[c]]

/-- The morphs of a token, split at the affix boundary `-` and the clitic boundary `=` of the
Leipzig rules. -/
def segments (s : String) : List (List Char) :=
  split ['-', '='] s.toList

example : segments "lát-t-a" = ["lát".toList, "t".toList, "a".toList] := by decide

/-- The punctuation written around morphs: the brackets of optional material and sentence
marks. -/
def punct : List Char := ['(', ')', '[', ']', ',', '.', '!', '?', ';', ':', '"', '…']

/-- A surface morph with its annotation punctuation dropped: the brackets of optional material
may sit inside a token, as in *(þangað) til*. -/
def trim (m : List Char) : List Char := m.filter (· ∉ punct)

example : trim "(az".toList = "az".toList := by decide
example : trim "miatt,".toList = "miatt".toList := by decide
example : trim "(þangað) til".toList = "þangað til".toList := by decide

/-- The words of an orthographic sentence: split at spaces, annotation punctuation dropped,
decapitalized. For a language whose sources print no gloss line, the words are matched against
the forms the language's fragment declares or realizes, which play the gloss line's role. -/
def tokens (s : String) : List (List Char) :=
  ((((split [' '] s.toList).map trim).map (·.map toLower)).filter (!·.isEmpty))

example : tokens "He will tell." = ["he".toList, "will".toList, "tell".toList] := by decide

/-- A declared, possibly multiword, form as the normalized tokens a row's stream shows. The
fragments keep their forms raw; normalization happens here, where a reader meets a row. -/
def formTokens (f : String) : List (List Char) := tokens f

/-- The entry of `lex` whose declared form starts earliest in the stream, the first listed where
several start together. -/
def lookup? {α : Type*} (lex : List (String × α)) : List (List Char) → Option α
  | [] => none
  | ts@(_ :: rest) =>
    ((lex.find? fun p ↦ (formTokens p.1).isPrefixOf ts).map (·.2)).orElse
      fun _ ↦ lookup? lex rest

/-- The stream shows the declared form `f`. -/
def containsForm (ts : List (List Char)) (f : String) : Bool := (lookup? [(f, ())] ts).isSome

example : lookup? [("fyrr en", 1), ("til", 2)] (tokens "svaf fyrr en fimm") = some 1 := by
  decide
example : containsForm (tokens "He will tell her.") "will tell" = true := by decide
example : containsForm (tokens "He told her.") "will tell" = false := by decide

/-- A gloss is a category label, as the Leipzig rules write `PST` or `3SG.DF`, when it has no
lower-case letter; otherwise it is a lexical gloss. -/
def IsLabel (g : List Char) : Prop := ∀ c ∈ g, ¬ c.isLower

instance (g : List Char) : Decidable (IsLabel g) :=
  inferInstanceAs (Decidable (∀ c ∈ g, _))

example : IsLabel "3SG.DF".toList := by decide
example : ¬ IsLabel "see".toList := by decide

/-- The elements of a morph's gloss: an object-language element rendered by several metalanguage
elements, words or category labels, has them separated by periods (Rule 4), as `come.out` or
`left.SG.MASC`. -/
def elements (g : List Char) : List (List Char) := split ['.'] g

/-- The category labels of a gloss: the elements of its morphs written without lower-case letters
(Rules 2–4), as `PST` and `3SG` in `be-PST.3SG`. -/
def labels (g : String) : List (List Char) :=
  ((segments g).flatMap elements).filter fun l ↦ decide (IsLabel l) && !l.isEmpty

end Gloss

namespace GlossedWord

variable (w : GlossedWord)

/-- The word and its gloss are segmented alike (Rule 2), so the word has its morphemes: `pyigt`'s
`GlossedWord.is_valid`. -/
def IsValid : Prop := w.glossedMorphemes ≠ []

instance : Decidable w.IsValid := inferInstanceAs (Decidable (_ ≠ _))

/-- The forms of the word's morphemes. -/
def morphs : List (List Char) := w.glossedMorphemes.map (·.morpheme)

/-- The glosses of the word's morphemes; of a word that is not valid, its gloss split at the
morpheme separators. -/
def glosses : List (List Char) :=
  if w.IsValid then w.glossedMorphemes.map (·.gloss) else Gloss.split ['-', '=', '~'] w.gloss

/-- The word without morpheme separators and the punctuation around it, `pyigt`'s
`GlossedWord.form`. -/
def form : List Char :=
  if w.IsValid then w.morphs.flatten else Gloss.trim (w.word.filter (· ∉ ['-', '=', '~']))

/-- The word's form, decapitalized: the form that a lexicon keys. -/
def wordform : List Char := w.form.map Gloss.toLower

/-- The word's first morpheme, decapitalized. -/
def stem : List Char := (w.morphs.headD []).map Gloss.toLower

/-- The category labels among the elements of the word's glosses. -/
def labels : List (List Char) :=
  (w.glosses.flatMap Gloss.elements).filter fun l ↦ decide (Gloss.IsLabel l) && !l.isEmpty

/-- The word's first lexical gloss, where it has one. -/
def lexicalGloss? : Option (List Char) :=
  w.glosses.find? fun g ↦ !decide (Gloss.IsLabel g)

/-- The morpheme of the word's first lexical gloss, decapitalized: the form that a lexicon of
roots keys. -/
def lexicalMorph? : Option (List Char) :=
  (w.glossedMorphemes.find? fun m ↦ !decide (Gloss.IsLabel m.gloss)).map
    (·.morpheme.map Gloss.toLower)

end GlossedWord

/-- The glossed word of the row printed as `w`, the first if there are several. -/
def Datum.glossedWord? (e : Datum) (w : String) : Option GlossedWord :=
  ((e.glossedTokens.map (·.1)).zip e.glossedWords).lookup w

/-- The row's gloss-line stream: each glossed word's form, split at its internal spaces, the
stream that declared forms are matched against. -/
def Datum.glossStream (e : Datum) : List (List Char) :=
  e.glossedWords.flatMap fun w ↦ (Gloss.split [' '] w.wordform).filter (!·.isEmpty)
