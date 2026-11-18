/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Phrase
public import Linglib.Phonology.Prosody.Match
public import Linglib.Phonology.OptimalityTheory.Constraint.Alignment
public import Linglib.Phonology.OptimalityTheory.Evaluation

/-!
# Selkirk (1996): The prosodic structure of function words

[selkirk-1996] gives a function word before a lexical word four possible prosodic structures:
a prosodic word of its own, or a clitic that is a daughter of the phonological phrase (free), of
the lexical word's prosodic word (internal), or of a prosodic word over that one (affixal). Which
is realized follows from the ranking of two constraints on prosodic domination, Exhaustivity at
the phrase and Nonrecursivity at the word, with the constraints aligning the edges of lexical
words and prosodic words. A stressless function word [cannot be a prosodic
word](##Selkirk1996.word_notMem_optimal), since Headedness is never violated; the English
ranking [selects the free clitic](##Selkirk1996.english_free), and three rankings
[select the three clitics](##Selkirk1996.serboCroatian) of three dialects of Serbo-Croatian.

## Implementation notes

Violations are computed from the definitions of the constraints. The outer prosodic word of the
affixal clitic begins at the function word, so that structure violates the left-edge alignment
of prosodic words with lexical words as well as Nonrecursivity. The hierarchy of `Prosody.Level`
ends at the intonational phrase, so the isolation form is stated without the utterance node.

## TODO

The phrase-final function words, whose strong form follows from the alignment of maximal
projections with phonological phrases, the object pronouns, and the English and Serbo-Croatian
forms themselves are not formalized.

## References

* [selkirk-1996]
* [mccarthy-prince-1993b]
-/

@[expose] public section

namespace Selkirk1996

open Prosody OptimalityTheory

/-! ### The four structures -/

/-- A weak function word, a stressless syllable heading no foot. -/
def fnc : Tree := .σ 1

/-- The foot of the lexical word. -/
def foot : Tree := .ft [.σ 2]

/-- The lexical word, a prosodic word over its foot. -/
def lex : Tree := .om [foot]

/-- The four organizations of a function word and a following lexical word into prosodic
words. -/
inductive Parse
  /-- The function word is a daughter of the phonological phrase. -/
  | free
  /-- The function word is a daughter of a prosodic word over that of the lexical word. -/
  | affixal
  /-- The function word is inside the prosodic word of the lexical word. -/
  | internal
  /-- The function word is a prosodic word. -/
  | word
  deriving DecidableEq, Fintype, Repr

/-- The phonological phrase of each organization. -/
def Parse.tree : Parse → Tree
  | .free => .ph [fnc, lex]
  | .affixal => .ph [.om [fnc, lex]]
  | .internal => .ph [.om [fnc, foot]]
  | .word => .ph [.om [fnc], lex]

-- (18): all four are layered phonological phrases.
theorem isPhrase_tree : ∀ p : Parse, IsPhrase p.tree := by decide

/-! ### The constraints -/

/-- The constraints of the analysis: Headedness, Nonrecursivity at the prosodic word,
Exhaustivity at the phonological phrase, and the alignment of each edge of a lexical word with a
prosodic word and of a prosodic word with a lexical word. -/
inductive Con
  | headedness | nonRec | exh | wdConL | wdConR | pwdConL | pwdConR
  deriving DecidableEq, Fintype, Repr

/-- The span of the lexical word, the second of two syllables. -/
def lexSpans : List (NonemptyInterval ℕ) := [⟨(1, 2), by decide⟩]

/-- The marks of a prosodic tree over a function word and a lexical word. -/
def marks (t : Tree) : Con → ℕ
  | .headedness => headedness t
  | .nonRec => nonrecursivity .om t
  | .exh => exhaustivity .ph t
  | .wdConL => Constraint.alignLeft (lexSpans, levelSpans .om t)
  | .wdConR => Constraint.alignRight (lexSpans, levelSpans .om t)
  | .pwdConL => Constraint.alignLeft (levelSpans .om t, lexSpans)
  | .pwdConR => Constraint.alignRight (levelSpans .om t, lexSpans)

/-- **The violations of the four structures**, (25): the free clitic violates only Exhaustivity
at the phrase, the affixal clitic Nonrecursivity at the word and the alignment of the left edge
of a prosodic word, the internal clitic the alignment of the left edges both ways, and the
function word as a prosodic word Headedness and the alignment of both edges of a prosodic
word. -/
theorem violations (c : Con) :
    (marks Parse.free.tree c ≠ 0 ↔ c = .exh) ∧
    (marks Parse.affixal.tree c ≠ 0 ↔ c = .nonRec ∨ c = .pwdConL) ∧
    (marks Parse.internal.tree c ≠ 0 ↔ c = .wdConL ∨ c = .pwdConL) ∧
    (marks Parse.word.tree c ≠ 0 ↔ c = .headedness ∨ c = .pwdConL ∨ c = .pwdConR) := by
  revert c; decide

-- (14): a function word in isolation is footed, and its structure is strictly layered.
theorem isStrictlyLayered_isolation :
    IsStrictlyLayered (Tree.iota [.ph [.om [.ft [.σ 2]]]]) := by decide

/-! ### Rankings -/

/-- The dominance that an analysis requires: Headedness over every other constraint, and each
constraint of the stratum `hi` over each of the stratum `lo`. -/
def Requires (hi lo : List Con) (i j : Con) : Prop :=
  i = .headedness ∧ j ≠ .headedness ∨ i ∈ hi ∧ j ∈ lo

instance (hi lo : List Con) : DecidableRel (Requires hi lo) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∨ _))

variable {r : Ranking Con}

/-- **A stressless function word is not a prosodic word**: under every ranking with Headedness
undominated, the structure in which the function word is a prosodic word loses to the free
clitic. -/
theorem word_notMem_optimal (hr : ∀ j, j ≠ .headedness → r.Dominates .headedness j) :
    Parse.word ∉ r.optimal (marks ∘ Parse.tree) Finset.univ := fun h ↦
  ((Ranking.Enumeration.mem_optimal_iff.1 h).2 .free (Finset.mem_univ _)).not_gt <|
    Ranking.Enumeration.profile_lt_iff_exists_dominates.2 ⟨.headedness, by decide,
      fun j hj ↦ hr j (by rintro rfl; revert hj; decide)⟩

/-- **English nonfinal function words are free clitics**: under every ranking with the
alignment of lexical words and Nonrecursivity at the word over the alignment of prosodic words
and Exhaustivity at the phrase, the free clitic is optimal. -/
theorem english_free
    (hr : Requires [.wdConL, .wdConR, .nonRec] [.pwdConL, .pwdConR, .exh] ≤ r.Dominates) :
    r.optimal (marks ∘ Parse.tree) Finset.univ = {.free} :=
  Ranking.Enumeration.optimal_eq_singleton_of_rel hr (by simp) (by decide)

/-- **Three rankings, three clitics**, (47): with Nonrecursivity and Exhaustivity over the
alignment constraints the internal clitic is optimal; with Exhaustivity under the others, the
free clitic; and with the alignment of lexical words and Exhaustivity over Nonrecursivity and
the alignment of prosodic words, the affixal clitic. -/
theorem serboCroatian :
    (Requires [.nonRec, .exh] [.wdConL, .wdConR, .pwdConL, .pwdConR] ≤ r.Dominates →
      r.optimal (marks ∘ Parse.tree) Finset.univ = {.internal}) ∧
    (Requires [.wdConL, .wdConR, .pwdConL, .pwdConR, .nonRec] [.exh] ≤ r.Dominates →
      r.optimal (marks ∘ Parse.tree) Finset.univ = {.free}) ∧
    (Requires [.wdConL, .wdConR, .exh] [.nonRec, .pwdConL, .pwdConR] ≤ r.Dominates →
      r.optimal (marks ∘ Parse.tree) Finset.univ = {.affixal}) :=
  ⟨fun hr ↦ Ranking.Enumeration.optimal_eq_singleton_of_rel hr (by simp) (by decide),
    fun hr ↦ Ranking.Enumeration.optimal_eq_singleton_of_rel hr (by simp) (by decide),
    fun hr ↦ Ranking.Enumeration.optimal_eq_singleton_of_rel hr (by simp) (by decide)⟩

/-! ### The hierarchies of the paper

The paper states each grammar as strata, leaving the order within a stratum open. Each ranking
below lists the strata in order, with Headedness first, and is one of the rankings its theorem
quantifies over. -/

/-- A ranking of the English hierarchy in its revised form (42), the alignment of lexical words
over Nonrecursivity over the alignment of prosodic words and Exhaustivity. -/
def english : Ranking Con :=
  .ofList [.headedness, .wdConL, .wdConR, .nonRec, .pwdConL, .pwdConR, .exh]

/-- A ranking of the first Serbo-Croatian dialect of (47). -/
def ns1 : Ranking Con :=
  .ofList [.headedness, .nonRec, .exh, .wdConL, .wdConR, .pwdConL, .pwdConR]

/-- A ranking of the second Serbo-Croatian dialect of (47). -/
def ns2 : Ranking Con :=
  .ofList [.headedness, .wdConL, .wdConR, .pwdConL, .pwdConR, .nonRec, .exh]

/-- A ranking of the third Serbo-Croatian dialect of (47). -/
def ns3 : Ranking Con :=
  .ofList [.headedness, .wdConL, .wdConR, .exh, .nonRec, .pwdConL, .pwdConR]

-- (36), (42)
theorem english_respects :
    Requires [.wdConL, .wdConR, .nonRec] [.pwdConL, .pwdConR, .exh] ≤ english.Dominates :=
  fun i j h ↦ by revert i j; decide

-- (47a)
theorem ns1_respects :
    Requires [.nonRec, .exh] [.wdConL, .wdConR, .pwdConL, .pwdConR] ≤ ns1.Dominates :=
  fun i j h ↦ by revert i j; decide

-- (47b)
theorem ns2_respects :
    Requires [.wdConL, .wdConR, .pwdConL, .pwdConR, .nonRec] [.exh] ≤ ns2.Dominates :=
  fun i j h ↦ by revert i j; decide

-- (47c)
theorem ns3_respects :
    Requires [.wdConL, .wdConR, .exh] [.nonRec, .pwdConL, .pwdConR] ≤ ns3.Dominates :=
  fun i j h ↦ by revert i j; decide

-- English: the free clitic.
example : english.optimal (marks ∘ Parse.tree) Finset.univ = {.free} :=
  english_free english_respects

-- The three dialects: the internal, the free and the affixal clitic.
example : ns1.optimal (marks ∘ Parse.tree) Finset.univ = {.internal} :=
  serboCroatian.1 ns1_respects

example : ns2.optimal (marks ∘ Parse.tree) Finset.univ = {.free} :=
  serboCroatian.2.1 ns2_respects

example : ns3.optimal (marks ∘ Parse.tree) Finset.univ = {.affixal} :=
  serboCroatian.2.2 ns3_respects

end Selkirk1996
