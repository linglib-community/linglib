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

A prosodic tree groups a string into nested constituents, each of a category drawn from a
linearly ordered hierarchy: syllable below foot below prosodic word below phonological phrase
below intonational phrase. A node carries its category and its marks, whatever else the
representation records at a node. The weight of a syllable is a mark, and so is prominence:
`Tree` marks weight alone, and `MetricalTree` adds the strong–weak labelling of
[liberman-prince-1977], which [is forgotten](##Prosody.MetricalTree.constituency) to recover
the grouping. A constituent of a level is well formed when its tree is rooted at that level and
every node dominates what `Constituent.Licenses` allows.

## Implementation notes

* `Constituent L M` takes the categories `L` and the marks `M` as parameters, so that what is
  said of grouping alone holds of every marked tree, and theories that differ in their
  categories share it. The clitic group and the phonological utterance of [nespor-vogel-1986]
  are not among the categories of `Level`.
* The prosodic tree is an ordered rose tree, so No-Tangling holds by construction. It is the
  carrier of candidates for violable constraints, so it includes structures that are not well
  formed, such as a phrase under a word, as well as the recursive prosodic word that
  [ito-mester-2003] admits for compounds.
* A strong–weak mark says whether a node heads its mother, so a node with no strong daughter
  or with several is representable; the mark on a root says nothing.
* The Nonrecursivity and Exhaustivity of [selkirk-1996] are violable and are not part of
  `Constituent.Licenses`; they are the constraints `nonrecursivity` and `exhaustivity`.

## References

* [selkirk-1980]
* [liberman-prince-1977]
* [nespor-vogel-1986]
* [selkirk-1996]
* [ito-mester-2003]
-/

@[expose] public section

namespace Prosody

/-! ### Categories -/

/-- The levels of the prosodic hierarchy, linearly ordered σ < f < ω < φ < ι. Syllable, stress
foot, and prosodic word are the prosodic categories of [selkirk-1980]. -/
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

instance : OrderBot Level where
  bot := syl
  bot_le a := by cases a <;> decide

@[simp] theorem bot_eq : (⊥ : Level) = syl := rfl

instance : WellFoundedLT Level := InvImage.wf toNat Nat.lt_wfRel.wf

/-- What a node of a level may dominate: a syllable nothing, a foot a non-empty list of
syllables and feet, and ω, φ and ι any nodes at or below their level. -/
def Licenses : Level → List Level → Prop
  | syl, ks => ks = []
  | ft, ks => ks ≠ [] ∧ ∀ k ∈ ks, k ≤ ft
  | a, ks => ∀ k ∈ ks, k ≤ a

instance : ∀ (a : Level) (ks : List Level), Decidable (Licenses a ks)
  | syl, ks => inferInstanceAs (Decidable (ks = []))
  | ft, ks => inferInstanceAs (Decidable (ks ≠ [] ∧ ∀ k ∈ ks, k ≤ ft))
  | om, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k ≤ om))
  | ph, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k ≤ ph))
  | iota, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k ≤ iota))

theorem Licenses.le {a : Level} {ks : List Level} (h : Licenses a ks) : ∀ k ∈ ks, k ≤ a := by
  cases a with
  | syl => rintro k hk; rw [show ks = [] from h] at hk; simp at hk
  | ft => exact h.2
  | om => exact h
  | ph => exact h
  | iota => exact h

end Level

/-! ### Constituents and trees -/

/-- A node of a prosodic tree: its category `level` and its `mark`. -/
structure Constituent (L : Type*) (M : Type*) where
  /-- The category of the node. -/
  level : L
  /-- What else the representation records at the node. -/
  mark : M
  deriving DecidableEq, Repr

namespace Constituent

variable {L M N : Type*}

/-- A node with its mark changed by `f`. -/
def map (f : M → N) (a : Constituent L M) : Constituent L N := ⟨a.level, f a.mark⟩

@[simp] theorem level_map (f : M → N) (a : Constituent L M) : (a.map f).level = a.level := rfl

/-- Whether a node with a strong–weak mark heads its mother. -/
def isHead {W : Type*} (a : Constituent L (W × Bool)) : Bool := a.mark.2

/-- The mora weight of a σ node; `none` for non-σ nodes. -/
def weight? (a : Constituent Level Syllable.Weight) : Option Syllable.Weight :=
  if a.level = .syl then some a.mark else none

/-- Under the *Layeredness* of [selkirk-1996] a node dominates only its own level or below.
`Licenses a ks` says that `a` may dominate daughters labelled `ks`: ω, φ, and ι obey nothing
further, so that recursion at those levels and level skipping, a syllable or a foot directly
under a φ, are admitted, and the syllable and the foot are strictly layered. -/
def Licenses (a : Constituent Level M) (ks : List (Constituent Level M)) : Prop :=
  a.level.Licenses (ks.map (·.level))

instance (a : Constituent Level M) (ks : List (Constituent Level M)) : Decidable (a.Licenses ks) :=
  inferInstanceAs (Decidable (Level.Licenses _ _))

end Constituent

/-- A prosodic tree is an ordered rose tree of constituents marked with syllable weight; ordered
children give No-Tangling by construction. -/
abbrev Tree := RoseTree (Constituent Level Syllable.Weight)

/-- A metrical tree is a prosodic tree whose nodes are also marked strong or weak
([liberman-prince-1977]). -/
abbrev MetricalTree := RoseTree (Constituent Level (Syllable.Weight × Bool))

/-- The label of a node of a metrical tree: its level, its weight and its strong–weak mark. -/
abbrev MetricalTree.Label := Constituent Level (Syllable.Weight × Bool)

/-- A syllable leaf of weight `w`. -/
abbrev Tree.σ (w : Syllable.Weight := 0) : Tree := .node ⟨.syl, w⟩ []

/-- A foot node over `cs`. -/
abbrev Tree.ft (cs : List Tree) : Tree := .node ⟨.ft, 0⟩ cs

/-- A prosodic-word (ω) node over `cs`. -/
abbrev Tree.om (cs : List Tree) : Tree := .node ⟨.om, 0⟩ cs

/-- A phonological-phrase (φ) node over `cs`. -/
abbrev Tree.ph (cs : List Tree) : Tree := .node ⟨.ph, 0⟩ cs

/-- An intonational-phrase (ι) node over `cs`. -/
abbrev Tree.iota (cs : List Tree) : Tree := .node ⟨.iota, 0⟩ cs

namespace MetricalTree

/-- A syllable leaf of weight `w`, strong when `h`. -/
abbrev σ (w : Syllable.Weight := 0) (h : Bool := false) : MetricalTree := .node ⟨.syl, w, h⟩ []

/-- A foot node over `cs`, strong when `h`. -/
abbrev ft (h : Bool) (cs : List MetricalTree) : MetricalTree := .node ⟨.ft, 0, h⟩ cs

/-- A prosodic-word (ω) node over `cs`, strong when `h`. -/
abbrev om (h : Bool) (cs : List MetricalTree) : MetricalTree := .node ⟨.om, 0, h⟩ cs

/-- A phonological-phrase (φ) node over `cs`, strong when `h`. -/
abbrev ph (h : Bool) (cs : List MetricalTree) : MetricalTree := .node ⟨.ph, 0, h⟩ cs

/-- An intonational-phrase (ι) node over `cs`. -/
abbrev iota (cs : List MetricalTree) : MetricalTree := .node ⟨.iota, 0, false⟩ cs

/-- The grouping of a metrical tree, its strong–weak marks forgotten. -/
def constituency (m : MetricalTree) : Tree := m.map (Constituent.map Prod.fst)

end MetricalTree

variable {M : Type*}

/-- Induction on a prosodic tree with the syllable leaves as base case: every other node, whether
    a foot, a word, a phrase, or an ill-formed node, is a branch, with the hypothesis for its
    children and the fact that it is not a syllable leaf. -/
@[elab_as_elim]
theorem Tree.recLeafBranch {motive : RoseTree (Constituent Level M) → Prop}
    (leaf : ∀ a, a.level = .syl → motive (.node a []))
    (branch : ∀ a cs, ¬(a.level = .syl ∧ cs = []) → (∀ c ∈ cs, motive c) → motive (.node a cs))
    (t : RoseTree (Constituent Level M)) : motive t := by
  induction t using RoseTree.rec' with
  | node a cs ih =>
    by_cases h : a.level = .syl ∧ cs = []
    · obtain ⟨ha, rfl⟩ := h; exact leaf a ha
    · exact branch a cs h ih

/-! ### Well-formed constituents -/

/-- A well-formed prosodic constituent at the level `ℓ` is a tree rooted in an `ℓ`-node and
licensed by `Constituent.Licenses`, so every node dominates only the levels Layeredness allows
under it. -/
def IsConstituent (ℓ : Level) (t : RoseTree (Constituent Level M)) : Prop :=
  t.value.level = ℓ ∧ t.Licensed Constituent.Licenses

instance (ℓ : Level) (t : RoseTree (Constituent Level M)) : Decidable (IsConstituent ℓ t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A constituent keeps its level and well-formedness when its marks are changed. -/
theorem isConstituent_map {N : Type*} (f : M → N) {ℓ : Level}
    {t : RoseTree (Constituent Level M)} :
    IsConstituent ℓ (t.map (Constituent.map f)) ↔ IsConstituent ℓ t := by
  rw [IsConstituent, IsConstituent, RoseTree.licensed_map, RoseTree.value_map,
    Constituent.level_map]
  refine and_congr_right fun _ ↦ ?_
  simp only [Constituent.Licenses, List.map_map, Constituent.level_map, Function.comp_def]
  exact Iff.rfl

end Prosody
