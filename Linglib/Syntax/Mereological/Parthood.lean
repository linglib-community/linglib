module

public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Data.Finset.Option
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Pi

/-!
# Dimensioned parthood

Mereological syntax builds structure by Subjoin, which makes one syntactic object a proper part
of another. Parthood comes in two dimensions: the first subjunction to an object makes a 1-part,
the extended-projection complement, the second a 2-part, the specifier, and there is no third
(Dimensionality). Parthood is transitive within a dimension but not across dimensions, which is
what makes 2-parts locality domains.

A `Parthood α` records the 1-part and the 2-part of each object of `α`. An object may be a part
of several others, which is how one object occupies several positions. Structures are ordered by
inclusion of their parthood edges, and Subjoin only moves up in this order.

## Main definitions

* `MereologicalSyntax.Parthood`: the 1-part and 2-part functions, indexed by the dimensions
  `Parthood.Dim` and ordered by inclusion.
* `Parthood.Imm n x y`: `x` is the immediate `n`-part of `y`. `Parthood.NPart n` is its
  transitive closure, `Parthood.Descendant` is parthood through both dimensions, and
  `Parthood.IsPart x` says that `x` is a part of something.
* `Parthood.Acyclic`, `Parthood.Dimensional`: Irreflexivity, and a 2-part only after a 1-part.
* `Parthood.subjoin`: Subjoin, adding a part in the next free dimension of the target.

## Main statements

* `Parthood.imm_subjoin_iff`: Subjoin adds exactly one parthood edge, in the dimension that
  Dimensionality assigns.
* `Parthood.Dimensional.subjoin`: Subjoin preserves Dimensionality.

## Implementation notes

* An object has at most one `n`-part, so its `n`-parts form a chain, and `NPart n` is decided by
  following it (`Relation.ReflTransGen.decidable_TransGen_of_option`). `Descendant` branches,
  and is decided by closing a set.
* Irreflexivity is a property of structures rather than a check inside `subjoin`. The licensed
  subjunctions of `Parthood.Subjoins` preserve it.

## References

* [adger-2025]
-/

@[expose] public section

namespace MereologicalSyntax

/-- A dimensioned parthood structure on `α` gives each object at most one 1-part and at most one
2-part (Dimensionality). -/
@[ext]
structure Parthood (α : Type*) where
  /-- The 1-part of an object, if any. -/
  onePart : α → Option α
  /-- The 2-part of an object, if any. -/
  twoPart : α → Option α

namespace Parthood

open Relation

/-- The two dimensions of parthood, the extended-projection complement (1-part) and the specifier
(2-part). -/
inductive Dim
  | one
  | two
  deriving DecidableEq, Repr, Fintype

variable {α : Type*} (P : Parthood α)

instance [Fintype α] [DecidableEq α] : DecidableEq (Parthood α) := fun _ _ ↦
  decidable_of_iff _ Parthood.ext_iff.symm

/-- The `n`-part of an object, if any. -/
def part : Dim → α → Option α
  | .one => P.onePart
  | .two => P.twoPart

/-! ### Parthood relations -/

/-- `x` is the immediate `n`-part of `y`. -/
def Imm (n : Dim) (x y : α) : Prop := P.part n y = some x

/-- `x` is an `n`-part of `y`, through a chain of immediate `n`-parts. -/
def NPart (n : Dim) : α → α → Prop := TransGen (P.Imm n)

/-- `x` is reachable from `y` through parts of either dimension. -/
def Descendant : α → α → Prop := TransGen fun x y ↦ ∃ n, P.Imm n x y

/-- `x` is a part of something. -/
def IsPart (x : α) : Prop := ∃ n y, P.Imm n x y

/-- Nothing is a part of itself, through any mix of dimensions (Irreflexivity). -/
def Acyclic : Prop := ∀ x, ¬ P.Descendant x x

/-- Only an object with a 1-part has a 2-part, since Subjoin fills the first dimension first. -/
def Dimensional : Prop := ∀ y, (P.twoPart y).isSome → (P.onePart y).isSome

instance [DecidableEq α] (n : Dim) : DecidableRel (P.Imm n) := fun _ _ ↦
  inferInstanceAs (Decidable (_ = _))

section Fintype

variable [Fintype α] [DecidableEq α]

instance (n : Dim) : DecidableRel (P.NPart n) := fun x y ↦
  haveI := ReflTransGen.decidable_TransGen_of_option (P.part n) y x
  decidable_of_iff _ transGen_swap

instance : DecidableRel P.Descendant := fun x y ↦
  haveI := ReflTransGen.decidable_TransGen_of_fintype_step
    (r := Function.swap fun x y ↦ ∃ n, P.Imm n x y)
    (fun y ↦ Finset.univ.biUnion fun n ↦ (P.part n y).toFinset)
    (fun _ _ ↦ by simp [Function.swap, Imm]) y x
  decidable_of_iff _ transGen_swap

instance : DecidablePred P.IsPart := fun _ ↦ inferInstanceAs (Decidable (∃ _ _, _))

instance : Decidable P.Acyclic := inferInstanceAs (Decidable (∀ _, _))

instance : Decidable P.Dimensional := inferInstanceAs (Decidable (∀ _, _))

end Fintype

/-! ### Extension -/

/-- `P ≤ Q` when every parthood edge of `P` is one of `Q`. -/
instance : PartialOrder (Parthood α) where
  le P Q := ∀ ⦃n x y⦄, P.Imm n x y → Q.Imm n x y
  le_refl _ _ _ _ := id
  le_trans _ _ _ h₁ h₂ _ _ _ h := h₂ (h₁ h)
  le_antisymm P Q h₁ h₂ := by
    have (n : Dim) (y : α) : P.part n y = Q.part n y :=
      Option.ext fun x ↦ ⟨fun h ↦ h₁ (n := n) (y := y) h, fun h ↦ h₂ (n := n) (y := y) h⟩
    exact Parthood.ext (funext (this .one)) (funext (this .two))

variable {P} {Q : Parthood α} {n : Dim} {x y z : α}

theorem le_iff : P ≤ Q ↔ ∀ n x y, P.Imm n x y → Q.Imm n x y :=
  ⟨fun h _ _ _ ↦ @h _ _ _, fun h _ _ _ ↦ h _ _ _⟩

theorem NPart.mono (h : P ≤ Q) (hxy : P.NPart n x y) : Q.NPart n x y :=
  TransGen.mono (fun _ _ ↦ @h n _ _) _ _ hxy

theorem Descendant.mono (h : P ≤ Q) (hxy : P.Descendant x y) : Q.Descendant x y :=
  TransGen.mono (fun _ _ ⟨n, hn⟩ ↦ ⟨n, h hn⟩) _ _ hxy

theorem IsPart.mono (h : P ≤ Q) (hx : P.IsPart x) : Q.IsPart x :=
  let ⟨n, y, hy⟩ := hx
  ⟨n, y, h hy⟩

theorem descendant_of_nPart (h : P.NPart n x y) : P.Descendant x y :=
  TransGen.mono (fun _ _ h ↦ ⟨n, h⟩) _ _ h

theorem Descendant.trans (h₁ : P.Descendant x y) (h₂ : P.Descendant y z) : P.Descendant x z :=
  TransGen.trans h₁ h₂

theorem NPart.eq_or_nPart_of_imm (hz : P.Imm n z y) (h : P.NPart n x y) :
    x = z ∨ P.NPart n x z := by
  obtain ⟨z', hxz', hz'y⟩ := TransGen.tail'_iff.1 h
  obtain rfl : z' = z := Option.some_injective _ (hz'y.symm.trans hz)
  exact (reflTransGen_iff_eq_or_transGen.1 hxz').imp_left Eq.symm

theorem Descendant.isPart (h : P.Descendant x y) : P.IsPart x :=
  let ⟨_, hxb, _⟩ := TransGen.head'_iff.1 h
  let ⟨n, hn⟩ := hxb
  ⟨n, _, hn⟩

/-! ### Subjoin -/

variable (P) in
/-- The dimension of the next subjunction to `y`: the first if `y` has no 1-part, the second if it
has a 1-part only, and none if it has both (Dimensionality). -/
def nextDim (y : α) : Option Dim :=
  match P.onePart y, P.twoPart y with
  | none, _ => some .one
  | some _, none => some .two
  | some _, some _ => none

theorem part_eq_none_of_nextDim (h : P.nextDim y = some n) : P.part n y = none := by
  unfold nextDim at h
  split at h <;> cases h <;> simp_all [part]

theorem nextDim_eq_two (h₁ : (P.onePart y).isSome) (h : P.nextDim y = some n) : n = .two := by
  unfold nextDim at h
  split at h <;> simp_all

theorem isSome_onePart_of_nextDim_two (h : P.nextDim y = some .two) : (P.onePart y).isSome := by
  unfold nextDim at h
  split at h <;> simp_all

variable [DecidableEq α]

variable (P) in
/-- `P` with `x` added as the `n`-part of `y`. -/
def addPart : Dim → α → α → Parthood α
  | .one, x, y => { P with onePart := Function.update P.onePart y (some x) }
  | .two, x, y => { P with twoPart := Function.update P.twoPart y (some x) }

variable (P) in
/-- Subjoin `x` to `y`, adding it in the next free dimension of `y`. -/
def subjoin (x y : α) : Option (Parthood α) := (P.nextDim y).map (P.addPart · x y)

theorem part_addPart (m : Dim) (b : α) :
    (P.addPart n x y).part m b = if m = n ∧ b = y then some x else P.part m b := by
  cases n <;> cases m <;> simp [addPart, part, Function.update_apply]

theorem imm_subjoin_iff (h : P.subjoin x y = some Q) :
    ∃ n, P.nextDim y = some n ∧ ∀ m a b, Q.Imm m a b ↔ P.Imm m a b ∨ (m = n ∧ a = x ∧ b = y) := by
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨n, hn, fun m a b ↦ ?_⟩
  have := part_eq_none_of_nextDim hn
  simp only [Imm, part_addPart]
  split_ifs with hmb
  · obtain ⟨rfl, rfl⟩ := hmb
    simp [this, eq_comm]
  · exact ⟨.inl, fun h ↦ h.resolve_right fun ⟨h₁, _, h₂⟩ ↦ hmb ⟨h₁, h₂⟩⟩

theorem le_of_subjoin (h : P.subjoin x y = some Q) : P ≤ Q :=
  let ⟨_, _, hQ⟩ := imm_subjoin_iff h
  fun _ _ _ hab ↦ (hQ _ _ _).2 (.inl hab)

theorem subjoin_eq_none_of_full (h₁ : (P.onePart y).isSome) (h₂ : (P.twoPart y).isSome) :
    P.subjoin x y = none := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h₁
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h₂
  simp [subjoin, nextDim, ha, hb]

theorem Dimensional.subjoin (hP : P.Dimensional) (h : P.subjoin x y = some Q) :
    Q.Dimensional := by
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  intro b hb
  cases n with
  | one =>
    simp only [addPart, Function.update_apply] at hb ⊢
    split_ifs with hby
    · rfl
    · exact hP b hb
  | two =>
    show (P.onePart b).isSome
    simp only [addPart, Function.update_apply] at hb
    by_cases hby : b = y
    · exact hby ▸ isSome_onePart_of_nextDim_two hn
    · simp only [hby, ite_false] at hb
      exact hP b hb

end Parthood

end MereologicalSyntax
