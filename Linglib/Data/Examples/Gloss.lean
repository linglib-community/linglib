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
its gloss at the same affix and clitic boundaries (Rule 2) and write grammatical category labels
in capitals (Rule 3), so a row's gloss line determines a morph-by-morph token stream without any
analysis beyond the source's own. This file reads that structure: a `GlossedWord` is a token's
surface morphs beside their glosses, a gloss segment is a category label or a lexical gloss by
its capitalization, and `Datum.glossedWords` lists a row's well-aligned tokens. Readers built on
it consult the row's form rather than a curated feature, the first step from annotated stimuli
toward parsed ones.

## Main definitions

* `Gloss.toLower`: `Char.toLower` extended over the Latin-1 Supplement and Latin Extended-A
  capitals, for sentence-initial tokens in European orthographies.
* `Gloss.segments`: the morphs of a token, split at the `-` and `=` boundaries.
* `Gloss.IsLabel`: a gloss segment is a category label, written without lower-case letters.
* `GlossedWord`, `Datum.glossedWords`: a token's aligned surface and gloss morphs, and a row's
  well-aligned tokens.
* `GlossedWord.stem`, `GlossedWord.wordform`, `GlossedWord.labels`,
  `GlossedWord.lexicalGloss?`: the first surface morph and the joined word, decapitalized, and
  the word's category labels and first lexical gloss.

## Implementation notes

* Everything is defined on `List Char`: the kernel reduces list operations where the positional
  `String` primitives get stuck, and the readers built here are consumed by `decide`.
* A token whose surface and gloss segment differently, against Rule 2, contributes no
  `GlossedWord`: the misalignment is the digitization's to fix, not the reader's to guess.

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

/-- A gloss segment is a category label, as the Leipzig rules write `PST` or `3SG.DF`, when it
has no lower-case letter; otherwise it is a lexical gloss. -/
def IsLabel (g : List Char) : Prop := ∀ c ∈ g, ¬ c.isLower

instance (g : List Char) : Decidable (IsLabel g) :=
  inferInstanceAs (Decidable (∀ c ∈ g, _))

example : IsLabel "3SG.DF".toList := by decide
example : ¬ IsLabel "see".toList := by decide

end Gloss

/-- A token of the gloss line as the Leipzig rules structure it: each surface morph beside its
gloss, in order. -/
structure GlossedWord where
  /-- The surface morphs with their glosses. -/
  morphs : List (List Char × List Char)
  deriving DecidableEq, Repr

namespace GlossedWord

variable (w : GlossedWord)

/-- The word's first surface morph, decapitalized: the form that a lexicon keys. -/
def stem : List Char := (w.morphs.headD ([], [])).1.map Gloss.toLower

/-- The category labels among the word's glosses. -/
def labels : List (List Char) :=
  (w.morphs.map (·.2)).filter fun g ↦ decide (Gloss.IsLabel g) && !g.isEmpty

/-- The word's first lexical gloss, where it has one. -/
def lexicalGloss? : Option (List Char) :=
  (w.morphs.map (·.2)).find? fun g ↦ !decide (Gloss.IsLabel g)

/-- The word's surface form: its morphs joined, decapitalized. -/
def wordform : List Char := (w.morphs.flatMap (·.1)).map Gloss.toLower

end GlossedWord

/-- The row's tokens whose surface and gloss segment alike, each as a `GlossedWord`, its surface
morphs trimmed of surrounding punctuation. -/
def Datum.glossedWords (e : Datum) : List GlossedWord :=
  e.glossedTokens.filterMap fun (s, g) ↦
    let ss := (Gloss.segments s).map Gloss.trim
    let gs := Gloss.segments g
    if ss.length = gs.length then some ⟨ss.zip gs⟩ else none

/-- The row's gloss-line stream: each glossed word's form, split at its internal spaces, the
stream that declared forms are matched against. -/
def Datum.glossStream (e : Datum) : List (List Char) :=
  e.glossedWords.flatMap fun w ↦ (Gloss.split [' '] w.wordform).filter (!·.isEmpty)
