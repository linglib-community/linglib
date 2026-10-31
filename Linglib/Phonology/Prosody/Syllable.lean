module

public import Mathlib.Data.PNat.Defs
public import Linglib.Phonology.Prosody.Mora
public import Linglib.Core.Data.RoseTree.Basic

/-!
# Syllables

A *syllable* is a headed moraic constituent: a non-moraic `onset` over a spine of morae whose
head, the nucleus, comes first and is mandatory, so that a syllable has at least one mora, and
whose `tail` holds the further morae of a long vowel and of a moraic coda. The nucleus is the
sonority peak of the syllable under the Sonority Sequencing Principle of [clements-1990], a
reading the file describes and does not represent. Weight is the number
of morae (`Syllable.weight`), the weight units of [hyman-1985] and the morae of [hayes-1989],
where a long vowel has two morae (`Syllable.ofLongVowel`) and Weight by Position gives the first
coda consonant a mora of its own (`Syllable.ofCV`); a syllable with one mora is light and one
with two or more is heavy (`Syllable.IsLight`, `Syllable.IsHeavy`). The onset-rime structure of
a syllable is a re-representation of the same object (`Syllable.toOnsetRime`), whose rime has
as many morae as the syllable has weight (`Syllable.toOnsetRime_weight`). The file also defines
the levels of the prosodic hierarchy, of which syllable, foot, and prosodic word are the
prosodic categories of [selkirk-1980] and all five are among the seven of [nespor-vogel-1986],
the prosodic constituents and the prosodic tree over them, and the relation
`Constituent.Licenses` by which a node licenses its daughters, the Layeredness of
[selkirk-1996].

## Main definitions

* `Syllable`: a headed moraic syllable, with an `onset`, the nucleus `head` mora, and the
  `tail` of further morae.
* `Syllable.morae`, `moraCount`, `weight`, `IsHeavy`, `IsLight`: the spine of morae, its
  length, and the weight predicates.
* `Syllable.ofCV`, `ofVowel`, `ofLongVowel`, `mk'`, `ofMorae`: constructors from segments and
  from morae.
* `Syllable.yield`, `Syllable.toOnsetRime`: the segment string of a syllable, and its
  onset-rime structure.
* `Syllable.Weight`, `Yield`: a mora count, and the weight profile of a string of syllables.
* `Level`, `Constituent`, `Tree`: the levels σ < f < ω < φ < ι, the prosodic constituents, and
  the prosodic tree over them.
* `Constituent.Licenses`: Layeredness, by which a node dominates only its own level or below.

## Main statements

* `Syllable.toOnsetRime_weight`: the rime of a syllable has as many morae as the syllable has
  weight.
* `Tree.recLeafBranch`: induction on a prosodic tree with the syllable leaves as base case.

## Implementation notes

* `Syllable.Weight` is `Nat`, the mora count, and `Weight.light`, `heavy`, and `superheavy`
  name one, two, and three morae.
* In `Constituent` the level is the constructor, so that a weight on a foot or a head mark on
  the ι root is unrepresentable.
* The prosodic tree is an ordered rose tree, so No-Tangling holds by construction. It is the
  carrier of candidates for the violable constraints defined with feet and words, so it includes
  ill-formed structures that `IsWord` rules out; the Nonrecursivity and Exhaustivity of
  [selkirk-1996], which she takes to be violable, are the constraints `noRec` and `parseInto`,
  not part of `Constituent.Licenses`.

## References

* [E. Selkirk, *The Role of Prosodic Categories in English Word Stress* (1980)][selkirk-1980]
* [L. M. Hyman, *A Theory of Phonological Weight* (1985)][hyman-1985]
* [M. Nespor and I. Vogel, *Prosodic Phonology* (1986)][nespor-vogel-1986]
* [B. Hayes, *Compensatory Lengthening in Moraic Phonology* (1989)][hayes-1989]
* [G. N. Clements, *The role of the sonority cycle in core syllabification*
  (1990)][clements-1990]
* [J. J. McCarthy and A. Prince, *Prosodic Morphology: Constraint Interaction and
  Satisfaction* (1993)][mccarthy-prince-1993]
* [E. Selkirk, *The Prosodic Structure of Function Words* (1996)][selkirk-1996]
* [J. Itô and A. Mester, *Japanese Morphophonemics: Markedness and Word Structure*
  (2003)][ito-mester-2003]
* [H. Dolatian, *Computational Locality of Cyclic Phonology in Armenian* (2020)][dolatian-2020]
-/

@[expose] public section

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- A syllable is a headed moraic constituent, as in [hayes-1989]: a non-moraic `onset`, the
    nucleus `head` mora, which is mandatory and comes first, and a `tail` of further morae, those
    of a long vowel and of a moraic coda. -/
structure Syllable where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The nucleus mora, the head of the syllable and its sonority peak under the Sonority
      Sequencing Principle of [clements-1990]; its presence gives the syllable at least one
      mora. -/
  head  : Mora
  /-- The further morae: those of a long vowel and of a moraic coda. -/
  tail  : List Mora
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

/-- The spine of morae, nucleus first. -/
def morae (σ : Syllable) : List Mora := σ.head :: σ.tail

/-- The nucleus, the head mora. -/
abbrev nucleusMora (σ : Syllable) : Mora := σ.head

/-- The segments of the nucleus. -/
def nucleusSegments (σ : Syllable) : List Segment := σ.head.dominates

/-- The number of morae. -/
def moraCount (σ : Syllable) : Nat := σ.morae.length

/-- The weight of a syllable, its mora count. -/
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

/-- A syllable from an onset, a nucleus mora, and any further morae. -/
def mk' (onset : List Segment) (nucleus : Mora) (coda : List Mora := []) : Syllable :=
  ⟨onset, nucleus, coda⟩

/-- A syllable from an onset and a non-empty list of morae, the first being the nucleus. -/
def ofMorae (onset : List Segment) (ms : List Mora) (h : ms ≠ [] := by simp) : Syllable :=
  ⟨onset, ms.head h, ms.tail⟩

/-- A syllable from onset, nucleus, and coda segments. Each nucleus segment projects a mora, the
    first being the head. Under Weight by Position ([hayes-1989]) the first coda segment projects
    a mora of its own and any further coda segments attach to it; without it the coda attaches
    to the last nucleus mora. The nucleus must be non-empty. -/
def ofCV (onset nucleus coda : List Segment) (wbp : Bool := true)
    (hn : nucleus ≠ [] := by simp) : Syllable :=
  match nucleus, hn with
  | [], h => (h rfl).elim
  | n₀ :: ns, _ =>
    match wbp, coda with
    | true, c :: cs => ⟨onset, Mora.of n₀, ns.map Mora.of ++ [(Mora.of c).attach cs]⟩
    | _, _ =>
      match (ns.map Mora.of).reverse with
      | last :: rest => ⟨onset, Mora.of n₀, rest.reverse ++ [last.attach coda]⟩
      | []           => ⟨onset, (Mora.of n₀).attach coda, []⟩

/-- The open syllable of an onset and a short vowel has one mora. -/
def ofVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, .of v, []⟩

/-- The open syllable of an onset and a long vowel has two morae dominating the same melody
([hayes-1989]). -/
def ofLongVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, .of v, [.of v]⟩

@[simp] theorem moraCount_ofVowel (onset : List Segment) (v : Segment) :
    (ofVowel onset v).moraCount = 1 := rfl

@[simp] theorem moraCount_ofLongVowel (onset : List Segment) (v : Segment) :
    (ofLongVowel onset v).moraCount = 2 := rfl

/-- The segment string, or *yield*, of a syllable: its onset followed by the segments of its
    morae. -/
def yield (σ : Syllable) : List Segment := σ.onset ++ σ.morae.flatMap (·.dominates)

end Syllable

/-! ### Onset-rime structure -/

/-- The *onset-rime structure* of a syllable, an onset over a rime, as a re-representation of the
    moraic `Syllable`. -/
structure OnsetRime where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The rime, the spine of morae. -/
  rime  : List Mora
  deriving DecidableEq

/-- The onset-rime structure of a syllable, whose rime is the spine of morae. -/
def Syllable.toOnsetRime (σ : Syllable) : OnsetRime := ⟨σ.onset, σ.morae⟩

/-- The rime of a syllable has as many morae as the syllable has weight, so that the moraic and
    onset-rime representations agree on weight. -/
theorem Syllable.toOnsetRime_weight (σ : Syllable) :
    σ.toOnsetRime.rime.length = σ.moraCount := rfl

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
