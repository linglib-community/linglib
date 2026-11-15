/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Syllable
public import Linglib.Core.Data.RoseTree.Licensed

/-!
# The prosodic hierarchy

The prosodic hierarchy orders the categories of prosodic structure, syllable below foot below
prosodic word below phonological phrase below intonational phrase, and a prosodic tree is an
ordered tree of constituents of these categories. A constituent of a level is well formed when
its tree is rooted at that level and every node dominates what `Constituent.Licenses` allows:
its own level or below, with the syllable dominating nothing and the foot a non-empty list of
syllables.

## Implementation notes

* In `Constituent` the level is the constructor, so that a weight on a foot or a head mark on
  the ι root is unrepresentable.
* The prosodic tree is an ordered rose tree, so No-Tangling holds by construction. It is the
  carrier of candidates for violable constraints, so it includes structures that are not well
  formed, such as a phrase under a word, as well as the recursive prosodic word that
  [ito-mester-2003] admits for compounds.
* The Nonrecursivity and Exhaustivity of [selkirk-1996] are violable and are not part of
  `Constituent.Licenses`; they are the constraints `nonrecursivity` and `exhaustivity`.
* The clitic group and the phonological utterance of [nespor-vogel-1986] are not levels.

## References

* [selkirk-1980]
* [nespor-vogel-1986]
* [selkirk-1996]
* [ito-mester-2003]
-/

@[expose] public section

namespace Prosody

/-! ### Levels, constituents and the tree

The prosodic tree is the ordered rose tree `RoseTree` labelled by `Constituent`s. -/

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

/-- `Licenses a ks` says that `a` may dominate daughters labelled `ks`. Every node obeys the
    *Layeredness* of [selkirk-1996], dominating only its own level or below; ω, φ, and ι obey
    nothing further, so that recursion at those levels and level skipping, a syllable or a foot
    directly under a φ, are admitted. The syllable and the foot are strictly layered: a syllable
    dominates nothing, and a foot a non-empty list of syllables. -/
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

/-! ### Well-formed constituents -/

/-- A well-formed prosodic constituent at the level `ℓ` is a tree rooted in an `ℓ`-node and
licensed by `Constituent.Licenses`, so every node dominates only the levels Layeredness allows
under it. -/
def IsConstituent (ℓ : Level) (t : Tree) : Prop :=
  t.value.level = ℓ ∧ t.Licensed Constituent.Licenses

instance (ℓ : Level) (t : Tree) : Decidable (IsConstituent ℓ t) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Prosody
