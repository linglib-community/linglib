module

public import Mathlib.Data.PNat.Defs
public import Linglib.Phonology.Segmental.Basic
public import Linglib.Core.Data.RoseTree.Basic

/-!
# Syllables

This file defines nucleus-headed syllables, the levels of the prosodic hierarchy, and the
prosodic tree over them. A nucleus-headed syllable is an onset over a spine of morae whose first
mora is the nucleus, and its weight is its number of morae. A node of the tree may dominate only
nodes of its own level or below.

## Main definitions

* `Syllable`: a nucleus-headed syllable, with an `onset`, the `nucleus` that bears its first
  mora, and the `tail` of further morae.
* `Syllable.moraCount`, `weight`, `IsHeavy`, `IsLight`: the number of morae and the weight
  predicates.
* `Syllable.ofVowel`, `ofLongVowel`: the open syllables of a short and of a long vowel.
* `nucleusSplit`: a string split at its first run of syllabic segments.
* `Syllable.Weight`, `Yield`: a mora count, and the weight profile of a string of syllables.
* `Level`, `Constituent`, `Tree`: the levels σ < f < ω < φ < ι, the prosodic constituents, and
  the prosodic tree over them.
* `Constituent.Licenses`: Layeredness, by which a node dominates only its own level or below.

## Main statements

* `Tree.recLeafBranch`: induction on a prosodic tree with the syllable leaves as base case.

## Implementation notes

* A `Syllable` is the special case of a syllable of a `MoraicForm` in which the nucleus bears
  the first mora, so that every syllable is at least light. [vasquez-aguilar-etal-2026] shows
  that a language need not observe it: in Shiwilu a syllable whose nucleus is the interior vowel
  takes its only mora from its coda.
* `Syllable.Weight` is `Nat`, the mora count, and `Weight.light`, `heavy`, and `superheavy`
  name one, two, and three morae.
* In `Constituent` the level is the constructor, so that a weight on a foot or a head mark on
  the ι root is unrepresentable.
* The prosodic tree is an ordered rose tree, so No-Tangling holds by construction. It is the
  carrier of candidates for the violable constraints defined with feet and words, so it includes
  ill-formed structures that `IsWord` rules out; Selkirk's Nonrecursivity and Exhaustivity,
  which she takes to be violable, are the constraints `noRec` and `parseInto`, not part of
  `Constituent.Licenses`.

## TODO

* Read `Syllable` off the syllables of a `MoraicForm` that the nucleus heads, and its weight off
  `MoraicForm.weight`.

## References

* [E. Selkirk, *The Role of Prosodic Categories in English Word Stress* (1980)][selkirk-1980]
* [L. M. Hyman, *A Theory of Phonological Weight* (1985)][hyman-1985]
* [M. Nespor and I. Vogel, *Prosodic Phonology* (1986)][nespor-vogel-1986]
* [B. Hayes, *Compensatory Lengthening in Moraic Phonology* (1989)][hayes-1989]
* [J. J. McCarthy and A. Prince, *Prosodic Morphology: Constraint Interaction and
  Satisfaction* (1993)][mccarthy-prince-1993]
* [E. Selkirk, *The Prosodic Structure of Function Words* (1996)][selkirk-1996]
* [J. Itô and A. Mester, *Japanese Morphophonemics: Markedness and Word Structure*
  (2003)][ito-mester-2003]
* [H. Dolatian, *Computational Locality of Cyclic Phonology in Armenian* (2020)][dolatian-2020]
* [A. Vásquez-Aguilar, M. K. Gordon, A. Katsika and S. Th. Gries, *Moraicity, gemination and
  syllable well-formedness in Shiwilu* (2026)][vasquez-aguilar-etal-2026]
-/

@[expose] public section

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- A nucleus-headed syllable: a non-moraic `onset`, the `nucleus`, which bears the first mora,
and the `tail` of further morae, those of a long vowel and of a moraic coda, each given by the
melody it dominates. -/
structure Syllable where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The nucleus, the melody of the first mora. -/
  nucleus : List Segment
  /-- The melodies of the further morae. -/
  tail : List (List Segment)
  deriving DecidableEq

namespace Syllable

/-- Syllable weight is the mora count; `Weight.light`, `heavy`, and `superheavy` name one, two,
and three morae. -/
abbrev Weight := Nat

namespace Weight
abbrev light : Weight := 1
abbrev heavy : Weight := 2
abbrev superheavy : Weight := 3
end Weight

/-- The number of morae: the nucleus mora and the tail. -/
def moraCount (σ : Syllable) : Nat := σ.tail.length + 1

/-- The weight of a syllable, its mora count: the weight units of [hyman-1985] and the morae of
[hayes-1989]. -/
abbrev weight (σ : Syllable) : Weight := σ.moraCount

theorem moraCount_pos (σ : Syllable) : 0 < σ.moraCount := Nat.succ_pos _

/-- The mora count as a positive natural. -/
def pnatMoraCount (σ : Syllable) : ℕ+ := ⟨σ.moraCount, σ.moraCount_pos⟩

/-- A syllable is heavy when it has at least two morae. -/
def IsHeavy (σ : Syllable) : Prop := Weight.heavy ≤ σ.weight
/-- A syllable is light when it has exactly one mora. -/
def IsLight (σ : Syllable) : Prop := σ.weight = Weight.light

instance (σ : Syllable) : Decidable σ.IsHeavy := by unfold IsHeavy; infer_instance
instance (σ : Syllable) : Decidable σ.IsLight := by unfold IsLight; infer_instance

/-- The open syllable of an onset and a short vowel has one mora. -/
def ofVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, [v], []⟩

/-- The open syllable of an onset and a long vowel has two morae dominating the same melody
([hayes-1989]). -/
def ofLongVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, [v], [[v]]⟩

@[simp] theorem moraCount_ofVowel (onset : List Segment) (v : Segment) :
    (ofVowel onset v).moraCount = 1 := rfl

@[simp] theorem moraCount_ofLongVowel (onset : List Segment) (v : Segment) :
    (ofLongVowel onset v).moraCount = 2 := rfl

end Syllable

/-! ### The nucleus of a string -/

/-- A string split at its first maximal run of syllabic segments: what precedes the run, the run,
    and what follows it. In a monosyllable the run is the nucleus, a diphthong included, and the
    rest is the material before and after it. -/
def nucleusSplit (w : List Segment) : List Segment × List Segment × List Segment :=
  let (pre, rest) := w.span fun x ↦ !decide x.IsSyllabic
  let (nuc, post) := rest.span fun x ↦ decide x.IsSyllabic
  (pre, nuc, post)

/-- The three parts of `nucleusSplit` spell out the string. -/
theorem nucleusSplit_append (w : List Segment) :
    (nucleusSplit w).1 ++ (nucleusSplit w).2.1 ++ (nucleusSplit w).2.2 = w := by
  simp only [nucleusSplit, List.span_eq_takeWhile_dropWhile, List.append_assoc,
    List.takeWhile_append_dropWhile]

/-! ### Yields -/

/-- A *yield* is the string of syllable weights of a prosodic structure, the unparsed input or
    the leaves of a prosodic `Tree`. Unlike a prosodic word, which is a headed constituent, a
    yield has no head and no constituency. -/
abbrev Yield := List Syllable.Weight

namespace Yield

/-- The weight profile of a string of syllables. -/
def ofSyllables (σs : List Syllable) : Yield := σs.map Syllable.weight

/-- The total mora count of a yield. -/
def moraCount (y : Yield) : Nat := y.sum

/-- A minimal-word condition: the yield has at least `minMorae` morae, by default two, the
    bimoraic minimum that [mccarthy-prince-1993] derives from the Prosodic Hierarchy and Foot
    Binarity. The condition does not ask for a foot, since some languages show no evidence for
    feet, as [dolatian-2020] reports of Armenian. -/
abbrev satisfiesMinWord (y : Yield) (minMorae : Nat := 2) : Prop := minMorae ≤ y.moraCount

end Yield

/-! ### The prosodic tree

The prosodic tree is the ordered rose tree `RoseTree` labelled by `Constituent`s. It is the
carrier of candidates for the violable constraints defined with feet and words, so it includes
ill-formed structures, such as a syllable directly under a phrase, that `IsWord` rules out, as
well as the recursive prosodic word that [ito-mester-2003] admits for compounds. It is defined
here because a syllable node carries a `Syllable.Weight`. -/

/-- The levels of the prosodic hierarchy, linearly ordered σ < f < ω < φ < ι. Syllable, stress
foot, and prosodic word are the prosodic categories of [selkirk-1980]; the seven-level
hierarchy of [nespor-vogel-1986] adds the clitic group between word and phrase and the
phonological utterance above the intonational phrase, neither of which is a `Level` here. -/
inductive Level
  | syl | ft | om | ph | iota
  deriving DecidableEq, Repr

namespace Level

/-- The rank of a level, σ lowest. -/
def toNat : Level → ℕ
  | syl => 0 | ft => 1 | om => 2 | ph => 3 | iota => 4

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

instance : LinearOrder Level := LinearOrder.lift' toNat toNat_injective

end Level

/-- A prosodic node, whose level is its constructor. A syllable carries its `weight` in morae and
    `isHead`, and every level below the ι root carries `isHead`, whether the node heads its
    parent; a weight on a foot or a head mark on the ι root is unrepresentable. -/
inductive Constituent
  /-- A syllable of the given `weight`, optionally the head of its foot. -/
  | syl (weight : Syllable.Weight := 0) (isHead : Bool := false)
  /-- A foot, optionally the head foot of its word. -/
  | ft (isHead : Bool := false)
  /-- A prosodic word ω, optionally the head word of its phrase. -/
  | om (isHead : Bool := false)
  /-- A phonological phrase φ, optionally the head phrase of its
  intonational phrase. -/
  | ph (isHead : Bool := false)
  /-- An intonational phrase ι, the headless root of the hierarchy. -/
  | iota
  deriving DecidableEq, Repr

namespace Constituent

/-- Whether a node heads its parent (a σ heads its foot, a foot heads its word, an ω its phrase,
    a φ its intonational phrase); `false` for the ι root. -/
def isHead : Constituent → Bool
  | .syl _ h => h | .ft h => h | .om h => h | .ph h => h | .iota => false

/-- The mora weight of a σ node; `none` for non-σ nodes. -/
def weight? : Constituent → Option Syllable.Weight
  | .syl w _ => some w | _ => none

/-- The level of a node, the constructor without its weight and head mark. -/
def level : Constituent → Level
  | .syl .. => .syl | .ft _ => .ft | .om _ => .om | .ph _ => .ph | .iota => .iota

@[simp] theorem level_syl (w : Syllable.Weight) (h : Bool) : (syl w h).level = .syl := rfl
@[simp] theorem level_ft (h : Bool) : (ft h).level = .ft := rfl
@[simp] theorem level_om (h : Bool) : (om h).level = .om := rfl
@[simp] theorem level_ph (h : Bool) : (ph h).level = .ph := rfl
@[simp] theorem level_iota : iota.level = .iota := rfl

/-- Under the *Layeredness* of [selkirk-1996] a node dominates only nodes of its own level or
    below. `Licenses a ks`
    says that `a` may dominate daughters labelled `ks`: a syllable dominates nothing, a foot a
    non-empty list of syllables, so that foot recursion is excluded, and ω, φ, and ι dominate any
    node at or below their level, so that recursion at those levels and level skipping, a
    syllable or a foot directly under a φ, are admitted. -/
def Licenses : Constituent → List Constituent → Prop
  | .syl .., ks => ks = []
  | .ft _, ks => ks ≠ [] ∧ ∀ k ∈ ks, k.level = .syl
  | a, ks => ∀ k ∈ ks, k.level ≤ a.level

instance : ∀ (a : Constituent) (ks : List Constituent), Decidable (Licenses a ks)
  | .syl .., ks => inferInstanceAs (Decidable (ks = []))
  | .ft _, ks => inferInstanceAs (Decidable (ks ≠ [] ∧ ∀ k ∈ ks, k.level = .syl))
  | .om _, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.level ≤ (Constituent.om _).level))
  | .ph _, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.level ≤ (Constituent.ph _).level))
  | .iota, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.level ≤ Constituent.iota.level))

end Constituent

/-- A prosodic tree is an ordered rose tree labelled by `Constituent`s; ordered children give
    No-Tangling by construction. -/
abbrev Tree := RoseTree Constituent

/-- A syllable leaf, the metrical terminal: a syllable of weight `w` with head mark `h`. -/
abbrev Tree.σ (w : Syllable.Weight := 0) (h : Bool := false) : Tree := .node (.syl w h) []

/-- A foot node over `cs`, optionally the head foot of its word. -/
abbrev Tree.ft (h : Bool) (cs : List Tree) : Tree := .node (.ft h) cs

/-- A prosodic-word (ω) node over `cs`. -/
abbrev Tree.om (cs : List Tree) : Tree := .node .om cs

/-- A phonological-phrase (φ) node over `cs`. -/
abbrev Tree.ph (cs : List Tree) : Tree := .node .ph cs

/-- Induction on a prosodic tree with the syllable leaves as base case: every other node, whether
    a foot, a word, a phrase, or an ill-formed node, is a branch, with the hypothesis for its
    children and the fact that it is not a syllable leaf. -/
@[elab_as_elim]
theorem Tree.recLeafBranch {motive : Tree → Prop}
    (leaf : ∀ a, a.level = .syl → motive (.node a []))
    (branch : ∀ a cs, ¬(a.level = .syl ∧ cs = []) → (∀ c ∈ cs, motive c) → motive (.node a cs))
    (t : Tree) : motive t := by
  induction t using RoseTree.rec' with
  | node a cs ih =>
    by_cases h : a.level = .syl ∧ cs = []
    · obtain ⟨ha, rfl⟩ := h; exact leaf a ha
    · exact branch a cs h ih

end Prosody
