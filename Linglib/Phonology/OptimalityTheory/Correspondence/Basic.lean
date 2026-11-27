/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Defs
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Logic.Relator

/-!
# MAX, DEP, INTEGRITY and UNIFORMITY

A faithfulness constraint is a condition on a correspondence $ℜ$. MAX requires every position of
the first structure to have a correspondent and DEP every position of the second:
`Correspondence.maxViol` and `Correspondence.depViol` count the positions without one, and vanish
when the domain and the range of $ℜ$ are everything (`Correspondence.maxViol_eq_zero_iff`,
`Correspondence.depViol_eq_zero_iff`). INTEGRITY and UNIFORMITY forbid a position of the first or
of the second structure from having several correspondents, and vanish when $ℜ$ is right-unique
or left-unique (`Correspondence.integrityViol_eq_zero_iff`,
`Correspondence.uniformityViol_eq_zero_iff`). A larger correspondence violates MAX and DEP no
more often (`Correspondence.maxViol_anti`), and a composite of a correspondence without
coalescence deletes no more than its two factors (`Correspondence.maxViol_comp_le`).

## Implementation notes

Each constraint on the range is the constraint on the domain of the converse: DEP is MAX of
`Correspondence.inv`, and UNIFORMITY is INTEGRITY.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [A. Payne, M. H. Vu and J. Heinz, *A Formal Analysis of Correspondence Theory*
  (2017)][payne-vu-heinz-2017]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

open scoped SetRel

variable {ι κ μ : Type*}

/-! ### MAX and INTEGRITY

The constraints on the domain: MAX vanishes iff the domain is everything, and INTEGRITY iff the
relation is right-unique. -/

section Domain

variable [Fintype ι] [DecidableEq ι]

/-- MAX restricted to the positions satisfying `P` counts those without a correspondent, as in
MAX-V, MAX-C, and the positional faithfulness constraints. -/
def maxViolOn (P : ι → Prop) [DecidablePred P] (R : Correspondence ι κ) : ℕ :=
  (Finset.univ.filter P \ R.image Prod.fst).card

/-- MAX counts the positions of the first string without a correspondent in the second. -/
def maxViol (R : Correspondence ι κ) : ℕ :=
  (Finset.univ \ R.image Prod.fst).card

/-- INTEGRITY counts the positions of the first string with more than one correspondent. -/
def integrityViol (R : Correspondence ι κ) : ℕ :=
  (Finset.univ.filter fun i ↦ 1 < (R.filter fun x ↦ x.1 = i).card).card

@[simp] theorem maxViolOn_true (R : Correspondence ι κ) :
    R.maxViolOn (fun _ ↦ True) = R.maxViol := by
  simp [maxViolOn, maxViol]

theorem maxViol_eq_zero_iff (R : Correspondence ι κ) : R.maxViol = 0 ↔ R.rel.dom = Set.univ := by
  rw [maxViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff,
    dom_rel, Finset.coe_eq_univ]

theorem integrityViol_eq_zero_iff (R : Correspondence ι κ) :
    R.integrityViol = 0 ↔ Relator.RightUnique (· ~[R.rel] ·) := by
  simp only [integrityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_const, not_lt, Finset.card_le_one, Finset.mem_filter, and_imp, Prod.forall,
    Prod.mk.injEq]
  exact ⟨fun h i j j' hj hj' ↦ (h i j hj rfl i j' hj' rfl).2,
    fun h i a j hj ha a' j' hj' ha' ↦ by subst ha ha'; exact ⟨rfl, h hj hj'⟩⟩

variable {R : Correspondence ι κ} {f : ι → κ}

theorem maxViol_eq_zero_of_graph (hf : R.rel = Function.graph f) : R.maxViol = 0 :=
  R.maxViol_eq_zero_iff.2 <| hf ▸ Set.eq_univ_of_forall fun i ↦ ⟨f i, rfl⟩

theorem integrityViol_eq_zero_of_graph (hf : R.rel = Function.graph f) : R.integrityViol = 0 :=
  R.integrityViol_eq_zero_iff.2 <| hf ▸ fun _ _ _ h h' ↦ h.symm.trans h'

/-- A relation with no MAX or INTEGRITY violation is the graph of a map of positions. -/
theorem exists_rel_eq_graph (hmax : R.maxViol = 0) (hint : R.integrityViol = 0) :
    ∃ f : ι → κ, R.rel = Function.graph f := by
  rw [maxViol_eq_zero_iff] at hmax
  rw [integrityViol_eq_zero_iff] at hint
  choose f hf using Set.eq_univ_iff_forall.1 hmax
  exact ⟨f, Set.ext fun ⟨i, j⟩ ↦ ⟨fun h ↦ hint (hf i) h, fun (h : f i = j) ↦ h ▸ hf i⟩⟩

/-- A larger correspondence leaves fewer positions without a correspondent. -/
theorem maxViol_anti {S : Correspondence ι κ} (h : R ⊆ S) : S.maxViol ≤ R.maxViol :=
  Finset.card_le_card (Finset.sdiff_subset_sdiff subset_rfl (Finset.image_subset_image h))

end Domain

/-! ### DEP and UNIFORMITY

Each constraint on the range is the constraint on the domain of the converse. -/

section Range

variable [Fintype κ] [DecidableEq κ]

/-- DEP restricted to the positions of the second string satisfying `P`. -/
def depViolOn (P : κ → Prop) [DecidablePred P] (R : Correspondence ι κ) : ℕ :=
  R.inv.maxViolOn P

/-- DEP counts the positions of the second string without a correspondent in the first. -/
def depViol (R : Correspondence ι κ) : ℕ :=
  R.inv.maxViol

/-- UNIFORMITY counts the positions of the second string with more than one correspondent. -/
def uniformityViol (R : Correspondence ι κ) : ℕ :=
  R.inv.integrityViol

variable (R : Correspondence ι κ) (S : Correspondence κ ι)

@[simp] theorem maxViol_inv : R.inv.maxViol = R.depViol := rfl

@[simp] theorem depViol_inv : S.inv.depViol = S.maxViol := by rw [depViol, inv_inv]

@[simp] theorem maxViolOn_inv (P : κ → Prop) [DecidablePred P] :
    R.inv.maxViolOn P = R.depViolOn P := rfl

@[simp] theorem depViolOn_inv (P : κ → Prop) [DecidablePred P] :
    S.inv.depViolOn P = S.maxViolOn P := by rw [depViolOn, inv_inv]

@[simp] theorem integrityViol_inv : R.inv.integrityViol = R.uniformityViol := rfl

@[simp] theorem uniformityViol_inv : S.inv.uniformityViol = S.integrityViol := by
  rw [uniformityViol, inv_inv]

theorem depViolOn_eq (P : κ → Prop) [DecidablePred P] :
    R.depViolOn P = (Finset.univ.filter P \ R.image Prod.snd).card := by
  rw [depViolOn, maxViolOn, image_fst_inv]

theorem depViol_eq : R.depViol = (Finset.univ \ R.image Prod.snd).card := by
  rw [depViol, maxViol, image_fst_inv]

@[simp] theorem depViolOn_true : R.depViolOn (fun _ ↦ True) = R.depViol :=
  maxViolOn_true R.inv

theorem depViol_eq_zero_iff : R.depViol = 0 ↔ R.rel.cod = Set.univ := by
  rw [depViol, maxViol_eq_zero_iff, rel_inv, SetRel.dom_inv]

theorem uniformityViol_eq_zero_iff :
    R.uniformityViol = 0 ↔ Relator.LeftUnique (· ~[R.rel] ·) := by
  rw [uniformityViol, integrityViol_eq_zero_iff, rel_inv]
  exact ⟨fun h _ _ _ h₁ h₂ ↦ h h₁ h₂, fun h _ _ _ h₁ h₂ ↦ h h₁ h₂⟩

variable {R} {f : ι → κ}

theorem depViol_anti {T : Correspondence ι κ} (h : R ⊆ T) : T.depViol ≤ R.depViol :=
  maxViol_anti fun ⟨_, _⟩ hji ↦ mem_inv.2 (h (mem_inv.1 hji))

theorem depViol_eq_zero_of_graph (hf : R.rel = Function.graph f) (hsurj : Function.Surjective f) :
    R.depViol = 0 :=
  R.depViol_eq_zero_iff.2 <| hf ▸ Set.eq_univ_of_forall hsurj

theorem depViolOn_of_graph [Fintype ι] (hf : R.rel = Function.graph f) (P : κ → Prop)
    [DecidablePred P] : R.depViolOn P = (Finset.univ.filter P \ Finset.univ.image f).card := by
  rw [depViolOn_eq]
  congr 2
  ext j
  simp [mem_iff_of_graph hf]

theorem uniformityViol_eq_zero_of_graph (hf : R.rel = Function.graph f)
    (hinj : Function.Injective f) : R.uniformityViol = 0 :=
  R.uniformityViol_eq_zero_iff.2 <| hf ▸ fun _ _ _ h h' ↦ hinj (h.trans h'.symm)

end Range

/-! ### Composition -/

section Comp

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Correspondence ι κ}

/-- A composite deletes no more than its two factors, provided the first does not coalesce: a
position the composite deletes is deleted by the first factor, or its one correspondent is
deleted by the second. -/
theorem maxViol_comp_le [DecidableEq μ] {S : Correspondence κ μ}
    (hR : R.uniformityViol = 0) : (R.comp S).maxViol ≤ R.maxViol + S.maxViol := by
  rw [uniformityViol_eq_zero_iff] at hR
  have hsub : Finset.univ \ (R.comp S).image Prod.fst ⊆
      (Finset.univ \ R.image Prod.fst) ∪
        ((R.image Prod.fst) \ (R.comp S).image Prod.fst) := fun i hi ↦ by
    by_cases h : i ∈ R.image Prod.fst
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨h, (Finset.mem_sdiff.1 hi).2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left ?_ _))
  refine Finset.card_le_card_of_forall_subsingleton (fun i j ↦ (i, j) ∈ R) (fun i hi ↦ ?_)
    fun j _ i hi i' hi' ↦ hR hi.2 hi'.2
  obtain ⟨hi, hi'⟩ := Finset.mem_sdiff.1 hi
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.1 hi
  refine ⟨j, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hj ↦ hi' ?_⟩, hij⟩
  obtain ⟨⟨j, k⟩, hjk, rfl⟩ := Finset.mem_image.1 hj
  exact Finset.mem_image.2 ⟨(i, k), mem_comp.2 ⟨j, hij, hjk⟩, rfl⟩

end Comp

end OptimalityTheory.Correspondence
