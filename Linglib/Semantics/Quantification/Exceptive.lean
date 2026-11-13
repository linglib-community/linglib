module

public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Order.Bounds.Basic

/-!
# Exceptive quantifiers

An exceptive, as in *every student but John*, subtracts an exception set from the restrictor of a
determiner. The subtraction is `Restrictive` when the quantification holds with it and fails
without it, and the set is the exception set, `IsExceptionSet`, when it is the least whose
subtraction verifies the quantification: [von-fintel-1993]'s semantics of the free exceptive and
of the *but*-phrase. A restrictive subtraction of an atom is [a minimal verifying
one](##Quantifier.Exceptive.restrictive_singleton_iff_minimal), which with *every* and *no* is
[the least](##Quantifier.Exceptive.minimal_every_iff). As a proposition, a subtraction that
entails just the larger ones is exhaustified against all others [where it is the
least](##Quantifier.Exceptive.mem_exh_range_subtraction_iff), and one that entails none of its
proper parts' is exhaustified against those [where it is
minimal](##Quantifier.Exceptive.mem_exh_image_Iio_subtraction_iff).

## Implementation notes

Restrictor, scope and exception set are sets, so subtraction is `\`, inclusion `≤` and
disjointness `Disjoint` of the Boolean algebra of sets, and `every R S` is definitionally
`R ≤ S` (`every_iff_le`) and `no R S` definitionally `R ≤ Sᶜ` (`no_iff_le_compl`). The
disjointness formulation of the uniqueness condition is equivalent to the definition only for
an exception set within the restrictor, which the definition entails
(`IsExceptionSet.le_restrictor`) and the formulation does not.

`Exhaustification.exh` denies the alternatives its prejacent does not entail, so under a
left-upward-monotone determiner, where every smaller subtraction is entailed
(`subtraction_anti`), exhaustification against the smaller subtractions changes nothing while
`Restrictive` is contradictory.

## References

* [von-fintel-1993]
-/

@[expose] public section

namespace Quantifier.Exceptive

open Quantifier Quantifier.Det

variable {α : Type*} {Q : Det α} {A C B : Set α}

/-! ### Domain subtraction with restrictiveness and the exception set -/

/-- Subtracting `C` from the restrictor is restrictive when the quantification holds with the
subtraction and fails without it, (17) of [von-fintel-1993] and his semantics of the free
exceptive (38). -/
def Restrictive (Q : Det α) (A C B : Set α) : Prop :=
  Q (A \ C) B ∧ ¬ Q A B

/-- `C` is the exception set of the quantification when it is the least set whose subtraction
from the restrictor makes the quantification true, (20) and (21) of [von-fintel-1993] and his
semantics of the *but*-phrase. -/
def IsExceptionSet (Q : Det α) (A C B : Set α) : Prop :=
  IsLeast {S | Q (A \ S) B} C

namespace Restrictive

/-- A left-upward-monotone determiner falsifies every restrictive exceptive. -/
theorem not_of_restrictorMonotone (hQ : RestrictorMonotone Q) : ¬ Restrictive Q A C B :=
  fun h ↦ h.2 (hQ B sdiff_le h.1)

/-- Under a left-downward-monotone determiner a restrictive exceptive survives enlarging the
exception set, the inference the exception set blocks. -/
theorem mono (hQ : RestrictorAntitone Q) (h : Restrictive Q A C B) {C' : Set α}
    (hC : C ≤ C') : Restrictive Q A C' B :=
  ⟨hQ B (sdiff_le_sdiff_left hC) h.1, h.2⟩

/-- Under an intersective determiner a restrictive subtraction removes something the scope holds
of: part of the exception set lies in the restrictor and in the scope. -/
theorem inter_nonempty (hQ : Q.Intersective) (h : Restrictive Q A C B) : (A ∩ B ∩ C).Nonempty :=
  Set.not_disjoint_iff_nonempty_inter.1 fun hd ↦ h.2 ((hQ.sdiff_iff hd).1 h.1)

/-- Under a co-intersective determiner a restrictive subtraction removes something the scope
fails of: part of the exception set lies in the restrictor and outside the scope. -/
theorem sdiff_nonempty (hQ : Q.CoIntersective) (h : Restrictive Q A C B) :
    ((A \ B) ∩ C).Nonempty :=
  Set.not_disjoint_iff_nonempty_inter.1 fun hd ↦ h.2 ((hQ.sdiff_iff hd).1 h.1)

end Restrictive

namespace IsExceptionSet

/-- The exception set is unique. -/
theorem unique (h : IsExceptionSet Q A C B) {C' : Set α} (h' : IsExceptionSet Q A C' B) :
    C = C' :=
  IsLeast.unique h h'

/-- The exception set lies within the restrictor, since subtracting `C ⊓ A` subtracts as much
as `C`. -/
theorem le_restrictor (h : IsExceptionSet Q A C B) : C ≤ A :=
  (le_inf_iff.1 (h.2 (show Q (A \ (C ⊓ A)) B by rw [sdiff_inf_self_right]; exact h.1))).2

/-- A left-upward-monotone determiner has only the empty exception set, since once the
quantification holds with `C` subtracted it holds with nothing subtracted. -/
theorem eq_bot_of_restrictorMonotone (hQ : RestrictorMonotone Q) (h : IsExceptionSet Q A C B) :
    C = ⊥ :=
  le_bot_iff.1 (h.2 (show Q (A \ ⊥) B by rw [sdiff_bot]; exact hQ B sdiff_le h.1))

theorem restrictive (h : IsExceptionSet Q A C B) (hC : C ≠ ⊥) : Restrictive Q A C B :=
  ⟨h.1, fun hQA ↦ hC (le_bot_iff.1 (h.2 (show Q (A \ ⊥) B by rwa [sdiff_bot])))⟩

/-- If removing `S` rescues the quantification exactly when `S` covers `r`, then `r` is the
exception set ([von-fintel-1993]'s §1.6). -/
theorem of_iff_le {r : Set α} (h : ∀ S, Q (A \ S) B ↔ r ≤ S) : IsExceptionSet Q A r B :=
  ⟨(h r).2 le_rfl, fun S hS ↦ (h S).1 hS⟩

end IsExceptionSet

/-! ### The three formulations of the uniqueness condition -/

/-- For `C ≤ A`, `C` is an exception set iff removing it verifies the quantification and it is
disjoint from every verifying subset of the restrictor (21). -/
theorem isExceptionSet_iff_disjoint (hCA : C ≤ A) :
    IsExceptionSet Q A C B ↔ Q (A \ C) B ∧ ∀ D ≤ A, Q D B → Disjoint C D := by
  unfold IsExceptionSet IsLeast
  refine and_congr_right fun _ ↦ ⟨fun h D hDA hD ↦ ?_, fun h S hS ↦ ?_⟩
  · exact (le_sdiff.1 (h (show Q (A \ (A \ D)) B by rwa [sdiff_sdiff_eq_self hDA]))).2
  · exact (le_sdiff.2 ⟨hCA, h (A \ S) sdiff_le hS⟩).trans
      (sdiff_sdiff_right_self.le.trans inf_le_right)

/-- In the third formulation of (21) the exception set is the intersection of the sets whose
subtraction verifies the quantification. -/
theorem isExceptionSet_iff_sInf_eq :
    IsExceptionSet Q A C B ↔ Q (A \ C) B ∧ sInf {S | Q (A \ S) B} = C :=
  ⟨fun h ↦ ⟨h.1, h.isGLB.sInf_eq⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2 ▸ fun _ hS ↦ sInf_le hS⟩⟩

/-! ### The universal determiners -/

theorem isExceptionSet_every (A B : Set α) : IsExceptionSet every A (A \ B) B :=
  .of_iff_le fun _ ↦ every_iff_le.trans sdiff_le_comm

theorem isExceptionSet_no (A B : Set α) : IsExceptionSet no A (A ⊓ B) B :=
  .of_iff_le fun S ↦ by rw [no_iff_le_compl, sdiff_le_comm, sdiff_compl]

/-- (23) of [von-fintel-1993] for *every*. -/
theorem isExceptionSet_every_iff : IsExceptionSet every A C B ↔ A \ B = C :=
  IsLeast.isLeast_iff_eq (isExceptionSet_every A B)

/-- (23) of [von-fintel-1993] for *no*. -/
theorem isExceptionSet_no_iff : IsExceptionSet no A C B ↔ A ⊓ B = C :=
  IsLeast.isLeast_iff_eq (isExceptionSet_no A B)

theorem restrictive_every_iff : Restrictive every A C B ↔ A \ B ≤ C ∧ ¬ A ≤ B := by
  unfold Restrictive
  rw [every_iff_le, sdiff_le_comm, every_iff_le]

theorem restrictive_no_iff : Restrictive no A C B ↔ A ⊓ B ≤ C ∧ ¬ Disjoint A B := by
  unfold Restrictive
  rw [no_iff_le_compl, sdiff_le_comm, sdiff_compl, no_iff_disjoint]

/-! ### Minimal and least verifying subtractions -/

/-- Subtracting an atom is restrictive exactly when the atom is a minimal set whose subtraction
verifies the quantification. -/
theorem restrictive_singleton_iff_minimal {a : α} :
    Restrictive Q A {a} B ↔ Minimal (fun S ↦ Q (A \ S) B) {a} := by
  rw [minimal_iff_forall_lt]
  refine and_congr_right fun _ ↦ ⟨fun h S hS hQ ↦ h ?_, fun h hQ ↦
    h (Set.ssubset_singleton_iff.2 rfl) (by rwa [Set.sdiff_empty])⟩
  rwa [Set.ssubset_singleton_iff.1 hS, Set.sdiff_empty] at hQ

/-- With *every* the minimal verifying subtraction is the least, the exception set. -/
theorem minimal_every_iff :
    Minimal (fun S ↦ every (A \ S) B) C ↔ IsExceptionSet every A C B :=
  (isExceptionSet_every A B).minimal_iff.trans (eq_comm.trans isExceptionSet_every_iff.symm)

/-- With *no* the minimal verifying subtraction is the least, the exception set. -/
theorem minimal_no_iff : Minimal (fun S ↦ no (A \ S) B) C ↔ IsExceptionSet no A C B :=
  (isExceptionSet_no A B).minimal_iff.trans (eq_comm.trans isExceptionSet_no_iff.symm)

/-! ### Subtraction as a proposition and its exhaustification -/

section Subtraction

open Exhaustification

variable {W : Type*} {A B : W → Set α} {w : W}

/-- The proposition that the quantification holds with `C` subtracted from the restrictor, for a
restrictor and a scope that vary with the world. -/
def subtraction (Q : Det α) (A B : W → Set α) (C : Set α) : Set W := {w | Q (A w \ C) (B w)}

@[simp] theorem mem_subtraction : w ∈ subtraction Q A B C ↔ Q (A w \ C) (B w) := Iff.rfl

@[simp] theorem subtraction_empty : subtraction Q A B ∅ = {w | Q (A w) (B w)} := by
  simp only [subtraction, Set.sdiff_empty]

/-- Under a left-downward-monotone determiner a larger subtraction is a weaker proposition. -/
theorem subtraction_mono (hQ : RestrictorAntitone Q) : Monotone (subtraction Q A B) :=
  fun _ _ h w ↦ hQ (B w) (sdiff_le_sdiff_left h)

/-- Under a left-upward-monotone determiner a larger subtraction is a stronger proposition. -/
theorem subtraction_anti (hQ : RestrictorMonotone Q) : Antitone (subtraction Q A B) :=
  fun _ _ h w ↦ hQ (B w) (sdiff_le_sdiff_left h)

/-- Against the subtractions of its proper parts, none of which it entails, the subtraction of
`C` is exhaustified exactly where `C` is a minimal set whose subtraction verifies the
quantification. -/
theorem mem_exh_image_Iio_subtraction_iff
    (h : ∀ S < C, ¬ subtraction Q A B C ⊆ subtraction Q A B S) :
    w ∈ exh (subtraction Q A B '' Set.Iio C) (subtraction Q A B C) ↔
      Minimal (fun S ↦ Q (A w \ S) (B w)) C :=
  mem_exh_image_Iio_iff_minimal h

/-- Where the subtractions that the subtraction of `C` entails are those of the sets containing
`C`, it is exhaustified against every subtraction exactly where `C` is the exception set. -/
theorem mem_exh_range_subtraction_iff
    (h : ∀ S, subtraction Q A B C ⊆ subtraction Q A B S ↔ C ≤ S) :
    w ∈ exh (Set.range (subtraction Q A B)) (subtraction Q A B C) ↔
      IsExceptionSet Q (A w) C (B w) :=
  mem_exh_range_iff_isLeast_of_forall h

end Subtraction

end Quantifier.Exceptive
