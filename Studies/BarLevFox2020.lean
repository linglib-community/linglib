module

public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Conditionals.Counterfactual
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Focus.Particles
public import Linglib.Logic.Modal.Basic
public import Linglib.Data.Examples.BarLevFox2020
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Bar-Lev and Fox 2020: Free choice, simplification, and Innocent Inclusion

Exhaustification with Innocent Inclusion returns the cell of the partition induced by the
alternatives whenever that cell is consistent. Free-choice disjunction `◇(a ∨ b)`, whose
alternatives are `◇a`, `◇b` and `◇(a ∧ b)`, strengthens to `◇a ∧ ◇b ∧ ¬◇(a ∧ b)`; plain `a ∨ b`,
whose conjunctive alternative is the conjunction of the other two, only denies it. `only`
presupposes the includable alternatives, so free choice under `only` projects. Free choice
under a universal quantifier, its negative counterpart, the existential-over-universal case
and *most* with a disjunctive restrictor are one computation over eight alternatives.
Simplification of disjunctive antecedents is the same strengthening over a variably strict
conditional: it fails when the consequent is one of the disjuncts, and an *or both*
antecedent, exhaustified by Hurford's constraint, turns the conjunctive simplification from
excluded into included.

## Main results

* `freeChoice`, `simpleDisjunction`: the modal and the plain disjunction.
* `II_fcAlts`, `isInnocentlyExcludable_fcAlts_iff`: what free choice includes and excludes.
* `support_only_fcAlts`: free choice under `only` is presupposed.
* `posExt_only_eq`: without symmetric alternatives `only` agrees with the exclusive
  `Focus.Particles.only`.
* `universalFreeChoice`, `negativeUniversalFreeChoice`, `freeChoiceOverUniversal`,
  `simplificationMost`: instances of `Exhaustification.exhIEII_quantified`.
* `sda`, `sda_consequent_disjunct`, `orBoth`: simplification, its failure, and the switches.

## References

* [bar-lev-fox-2020]
* [fox-2007]
* [alxatib-2014]
* [chemla-2009b]
* [nouwen-2017]
* [mckay-vaninwagen-1977]
* [nute-1980]
* [ciardelli-zhang-champollion-2018]
* [chierchia-fox-spector-2012]
-/

@[expose] public section

namespace BarLevFox2020

open Exhaustification ModalLogic SetRel

variable {W : Type*}

/-! ### Free choice and simple disjunction -/

section FreeChoice

variable (R : SetRel W W) (a b : Set W)

/-- The alternatives of `◇(a ∨ b)` replace the disjunction by its disjuncts and their
conjunction. -/
def fcAlts : Set (Set W) := {R.preimage (a ∪ b), R.preimage a, R.preimage b, R.preimage (a ∩ b)}

/-- Free choice needs a world permitting only `a`, one permitting only `b`, and one permitting
each but not both. -/
structure FreeChoiceWitnesses : Prop where
  only_left : ∃ w ∈ R.preimage a, w ∉ R.preimage b
  only_right : ∃ w ∈ R.preimage b, w ∉ R.preimage a
  not_both : ∃ w ∈ R.preimage a ∩ R.preimage b, w ∉ R.preimage (a ∩ b)

variable {R a b} (hF : FreeChoiceWitnesses R a b)
include hF

private theorem FreeChoiceWitnesses.exists_left :
    ∃ w ∈ R.preimage (a ∪ b) ∩ R.preimage a, w ∉ R.preimage b ∪ R.preimage (a ∩ b) :=
  hF.only_left.imp fun _ h ↦ ⟨⟨preimage_mono Set.subset_union_left h.1, h.1⟩,
    fun h' ↦ h.2 (h'.elim id (fun h' ↦ (preimage_inter_subset _ h').2))⟩

private theorem FreeChoiceWitnesses.exists_right :
    ∃ w ∈ R.preimage (a ∪ b) ∩ R.preimage b, w ∉ R.preimage a ∪ R.preimage (a ∩ b) :=
  hF.only_right.imp fun _ h ↦ ⟨⟨preimage_mono Set.subset_union_right h.1, h.1⟩,
    fun h' ↦ h.2 (h'.elim id (fun h' ↦ (preimage_inter_subset _ h').1))⟩

private theorem FreeChoiceWitnesses.exists_both :
    ∃ w ∈ R.preimage (a ∪ b) ∩ R.preimage a ∩ R.preimage b, w ∉ R.preimage (a ∩ b) :=
  hF.not_both.imp fun _ h ↦ ⟨⟨⟨preimage_mono Set.subset_union_left h.1.1, h.1.1⟩, h.1.2⟩, h.2⟩

/-- Given the witnesses, `◇(a ∨ b)` strengthens to `◇a ∧ ◇b ∧ ¬◇(a ∧ b)`, free choice. -/
theorem freeChoice : exhIEII (fcAlts R a b) (R.preimage (a ∪ b)) =
    (R.preimage a ∩ R.preimage b) \ R.preimage (a ∩ b) := by
  rw [fcAlts, exhIEII_pair (preimage_union ..).le hF.exists_left hF.exists_right hF.exists_both,
    Set.inter_assoc, Set.inter_eq_right.2 fun _ h ↦ preimage_mono Set.subset_union_left h.1]

/-- The includable alternatives of `◇(a ∨ b)` are the prejacent and the disjunct
alternatives. -/
theorem II_fcAlts :
    II (fcAlts R a b) (R.preimage (a ∪ b)) = {R.preimage (a ∪ b), R.preimage a, R.preimage b} :=
  II_pair (preimage_union ..).le hF.exists_left hF.exists_right hF.exists_both

/-- The only excludable alternative of `◇(a ∨ b)` is the conjunctive one. -/
theorem isInnocentlyExcludable_fcAlts_iff {q : Set W} :
    IsInnocentlyExcludable (fcAlts R a b) (R.preimage (a ∪ b)) q ↔ q = R.preimage (a ∩ b) :=
  isInnocentlyExcludable_pair_iff (preimage_union ..).le hF.exists_left hF.exists_right

end FreeChoice

section SimpleDisjunction

variable {a b : Set W}

/-- Without the modal the conjunctive alternative is the conjunction of the disjunct
alternatives, so exhaustification denies it and includes neither disjunct. -/
theorem simpleDisjunction (h₁ : ∃ w ∈ a, w ∉ b) (h₂ : ∃ w ∈ b, w ∉ a) :
    exhIEII {a ∪ b, a, b, a ∩ b} (a ∪ b) = (a ∪ b) \ (a ∩ b) :=
  exhIEII_pair_inter le_rfl (h₁.imp fun _ h ↦ ⟨⟨Or.inl h.1, h.1⟩, h.2⟩)
    (h₂.imp fun _ h ↦ ⟨⟨Or.inr h.1, h.1⟩, h.2⟩)

theorem simpleDisjunction_cell (h₁ : ∃ w ∈ a, w ∉ b) (h₂ : ∃ w ∈ b, w ∉ a) :
    cell {a ∪ b, a, b, a ∩ b} (a ∪ b) = ∅ :=
  cell_pair_inter le_rfl (h₁.imp fun _ h ↦ ⟨⟨Or.inl h.1, h.1⟩, h.2⟩)
    (h₂.imp fun _ h ↦ ⟨⟨Or.inr h.1, h.1⟩, h.2⟩)

end SimpleDisjunction

/-! ### `only` -/

open Classical in
/-- `only` presupposes the innocently includable alternatives and asserts that the innocently
excludable ones are false (32). -/
noncomputable def only (ALT : Set (Set W)) (φ : Set W) : W → SignType :=
  {w | ∀ r ∈ II ALT φ, w ∈ r}.indicator
    fun w ↦ SignType.ofProp (∀ q, IsInnocentlyExcludable ALT φ q → w ∉ q)

/-- Free choice under `only` is presupposed, since `only ◇(a ∨ b)` presupposes `◇a` and `◇b`. -/
theorem support_only_fcAlts {R : SetRel W W} {a b : Set W} (hF : FreeChoiceWitnesses R a b) :
    Function.support (only (fcAlts R a b) (R.preimage (a ∪ b))) =
      R.preimage a ∩ R.preimage b := by
  ext w
  simp only [Function.mem_support, ne_eq, only, Set.indicator_apply_eq_zero,
    SignType.ofProp_ne_zero, imp_false, not_not, Set.mem_ofPred_eq, II_fcAlts hF,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun h ↦ ⟨h.2.1, h.2.2⟩, fun h ↦ ⟨preimage_mono Set.subset_union_left h.1, h.1, h.2⟩⟩

/-- Where the prejacent is the only includable alternative and exactly the non-entailed ones are
excludable, `only` agrees with the exclusive entry (29b) on the entailment scale. -/
theorem posExt_only_eq {ALT : Set (Set W)} {φ : Set W} (hφ : φ ∈ ALT)
    (hIE : ∀ q, IsInnocentlyExcludable ALT φ q ↔ q ∈ ALT ∧ ¬ φ ⊆ q) (hII : II ALT φ = {φ}) :
    Trivalent.posExt (only ALT φ) =
      Trivalent.posExt (Focus.Particles.only (· ⊆ ·) ALT φ) := by
  rw [Focus.Particles.posExt_only_subset hφ]
  ext w
  simp only [Trivalent.mem_posExt, only, Trivalent.indicator_apply_eq_one_iff,
    SignType.ofProp_eq_one_iff, Set.mem_ofPred_eq, hII, Set.mem_singleton_iff, forall_eq, hIE,
    and_imp, mem_exh]
  exact ⟨fun ⟨hw, h⟩ ↦ ⟨hw, fun q hq hwq ↦ by_contra fun hne ↦ h q hq hne hwq⟩,
    fun ⟨hw, h⟩ ↦ ⟨hw, fun q hq hne hwq ↦ hne (h q hq hwq)⟩⟩

/-! ### Simplification of disjunctive antecedents -/

section Simplification

open Conditional

variable (ord : W → Preorder W) (p q r : Set W)

/-- The alternatives of `(p ∨ q) → r` replace the antecedent's disjunction by its disjuncts
and their conjunction. -/
def sdaAlts : Set (Set W) :=
  {closestImp ord (p ∪ q) r, closestImp ord p r, closestImp ord q r,
    closestImp ord (p ∩ q) r}

variable {ord p q r}

/-- Disjunctive antecedents simplify. Over total similarity preorders, given a world where only
the first simplification holds, one where only the second does, and one where both hold but the
conjunctive one fails, `(p ∨ q) → r` strengthens to `(p → r) ∧ (q → r) ∧ ¬((p ∧ q) → r)`. -/
theorem sda (htot : ∀ w, Std.Total (ord w).le)
    (h₁ : ∃ w ∈ closestImp ord (p ∪ q) r,
      w ∉ closestImp ord q r ∪ closestImp ord (p ∩ q) r)
    (h₂ : ∃ w ∈ closestImp ord (p ∪ q) r,
      w ∉ closestImp ord p r ∪ closestImp ord (p ∩ q) r)
    (h : ∃ w ∈ closestImp ord p r ∩ closestImp ord q r,
      w ∉ closestImp ord (p ∩ q) r) :
    exhIEII (sdaAlts ord p q r) (closestImp ord (p ∪ q) r) =
      (closestImp ord p r ∩ closestImp ord q r) \ closestImp ord (p ∩ q) r := by
  have hsub : closestImp ord p r ∩ closestImp ord q r ⊆ closestImp ord (p ∪ q) r :=
    fun _ h ↦ mem_closestImp_union h.1 h.2
  have hcov : closestImp ord (p ∪ q) r ⊆ closestImp ord p r ∪ closestImp ord q r :=
    fun _ h ↦ mem_closestImp_or_of_mem_union htot h
  rw [sdaAlts, exhIEII_pair hcov
    (h₁.imp fun w h ↦ ⟨⟨h.1, (hcov h.1).resolve_right fun h' ↦ h.2 (Or.inl h')⟩, h.2⟩)
    (h₂.imp fun w h ↦ ⟨⟨h.1, (hcov h.1).resolve_left fun h' ↦ h.2 (Or.inl h')⟩, h.2⟩)
    (h.imp fun w h ↦ ⟨⟨⟨hsub h.1, h.1.1⟩, h.1.2⟩, h.2⟩), Set.inter_assoc, Set.inter_eq_right.2 hsub]

/-- Simplification fails when the consequent is one of the disjuncts (71), since the other
simplification is the only contingent alternative and so is excluded. -/
theorem sda_consequent_disjunct
    (h : ∃ w ∈ closestImp ord (p ∪ q) p, w ∉ closestImp ord q p) :
    exhIEII (sdaAlts ord p q p) (closestImp ord (p ∪ q) p) =
      closestImp ord (p ∪ q) p \ closestImp ord q p := by
  refine exhIEII_eq_diff_of_forall_subset (by simp [sdaAlts]) (fun x hx hne ↦ ?_) h
  simp only [sdaAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact le_rfl
  · exact fun _ _ ↦ by rw [closestImp_eq_univ_of_subset le_rfl]; trivial
  · exact absurd rfl hne
  · exact fun _ _ ↦ by rw [closestImp_eq_univ_of_subset Set.inter_subset_left]; trivial

variable (ord p q r) in
/-- The alternatives of `(Exh(p ∨ q) ∨ (p ∧ q)) → r`, the *or both* antecedent parsed with an
embedded exhaustifier by Hurford's constraint (80), are the antecedent's three cells. -/
def orBothAlts : Set (Set W) :=
  {closestImp ord (p ∪ q) r, closestImp ord (p \ q) r,
    closestImp ord (q \ p) r, closestImp ord (p ∩ q) r}

/-- With the antecedent's cells as alternatives, `(p ∨ q) → r` asserts the conjunctive conditional
(82). -/
theorem orBoth (htot : ∀ w, Std.Total (ord w).le)
    (h₁ : ∃ w ∈ closestImp ord (p ∪ q) r ∩ closestImp ord (p \ q) r,
      w ∉ closestImp ord (q \ p) r ∪ closestImp ord (p ∩ q) r)
    (h₂ : ∃ w ∈ closestImp ord (p ∪ q) r ∩ closestImp ord (q \ p) r,
      w ∉ closestImp ord (p \ q) r ∪ closestImp ord (p ∩ q) r)
    (h₃ : ∃ w ∈ closestImp ord (p ∪ q) r ∩ closestImp ord (p ∩ q) r,
      w ∉ closestImp ord (p \ q) r ∪ closestImp ord (q \ p) r)
    (h : ∃ w ∈ closestImp ord (p ∪ q) r, w ∈ closestImp ord (p \ q) r ∧
      w ∈ closestImp ord (q \ p) r ∧ w ∈ closestImp ord (p ∩ q) r) :
    exhIEII (orBothAlts ord p q r) (closestImp ord (p ∪ q) r) =
      closestImp ord (p ∪ q) r ∩ closestImp ord (p \ q) r ∩
        closestImp ord (q \ p) r ∩ closestImp ord (p ∩ q) r := by
  have hcov : closestImp ord (p ∪ q) r ⊆
      ⋃ i, ![closestImp ord (p \ q) r, closestImp ord (q \ p) r,
        closestImp ord (p ∩ q) r] i := by
    intro w hw
    have hpq : p ∪ q = p \ q ∪ (q \ p ∪ p ∩ q) := by
      ext x; by_cases hp : x ∈ p <;> by_cases hq : x ∈ q <;> simp [hp, hq]
    rw [hpq] at hw
    rcases mem_closestImp_or_of_mem_union htot hw with h | h
    · exact Set.mem_iUnion.2 ⟨0, h⟩
    rcases mem_closestImp_or_of_mem_union htot h with h | h
    · exact Set.mem_iUnion.2 ⟨1, h⟩
    · exact Set.mem_iUnion.2 ⟨2, h⟩
  have hA : orBothAlts ord p q r = insert (closestImp ord (p ∪ q) r)
      (Set.range ![closestImp ord (p \ q) r, closestImp ord (q \ p) r,
        closestImp ord (p ∩ q) r]) := by
    simp only [orBothAlts, Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.union_empty]
  rw [hA, exhIEII_insert_range hcov ?_ ?_]
  · ext w
    simp [Set.mem_iInter, Fin.forall_fin_succ, and_assoc]
  · intro i
    fin_cases i
    · exact h₁.imp fun w h ↦ ⟨h.1, fun j hj hw ↦ by
        fin_cases j
        · exact hj rfl
        · exact h.2 (Or.inl hw)
        · exact h.2 (Or.inr hw)⟩
    · exact h₂.imp fun w h ↦ ⟨h.1, fun j hj hw ↦ by
        fin_cases j
        · exact h.2 (Or.inl hw)
        · exact hj rfl
        · exact h.2 (Or.inr hw)⟩
    · exact h₃.imp fun w h ↦ ⟨h.1, fun j hj hw ↦ by
        fin_cases j
        · exact h.2 (Or.inl hw)
        · exact h.2 (Or.inr hw)
        · exact hj rfl⟩
  · exact h.imp fun w h ↦ ⟨h.1, fun i ↦ by fin_cases i <;> simp [h.2.1, h.2.2.1, h.2.2.2]⟩

end Simplification

/-! ### The switches -/

/-- A world of [ciardelli-zhang-champollion-2018]'s scenario records whether each switch is up,
and the wiring of the light. -/
structure Switch where
  up₁ : Bool
  up₂ : Bool
  light : Bool → Bool → Bool
  deriving DecidableEq, Fintype

namespace Switch

open Conditional

/-- Worlds with a different wiring are farther than any with the same; among the latter,
distance is the number of switches in another position. -/
def rank (w₀ w : Switch) : ℕ :=
  (if w.light = w₀.light then 0 else 4) + (if w.up₁ = w₀.up₁ then 0 else 1) +
    (if w.up₂ = w₀.up₂ then 0 else 1)

/-- Similarity to `w₀`, ordered by `rank`. -/
abbrev sim (w₀ : Switch) : Preorder Switch := Preorder.lift (rank w₀)

theorem sim_total (w₀ : Switch) : Std.Total (sim w₀).le := Preorder.total_lift (rank w₀)

/-- Switch A is down. -/
abbrev down₁ : Set Switch := {w | w.up₁ = false}

/-- Switch B is down. -/
abbrev down₂ : Set Switch := {w | w.up₂ = false}

/-- The light is off. -/
abbrev off : Set Switch := {w | w.light w.up₁ w.up₂ = false}

/-- Both switches up, and the light on exactly when the switches agree. -/
def actual : Switch := ⟨true, true, fun x y ↦ x == y⟩

-- (76)
theorem sda_actual :
    actual ∈ exhIEII (sdaAlts sim down₁ down₂ off)
      (closestImp sim (down₁ ∪ down₂) off) := by
  rw [sda sim_total ⟨⟨false, true, fun x y ↦ !x && !y⟩, by decide⟩
    ⟨⟨true, false, fun x y ↦ !x && !y⟩, by decide⟩ ⟨actual, by decide⟩]
  decide

-- (78)
theorem orBoth_actual :
    actual ∉ exhIEII (orBothAlts sim down₁ down₂ off)
      (closestImp sim (down₁ ∪ down₂) off) := by
  rw [orBoth sim_total ⟨⟨false, true, fun x y ↦ x || !y⟩, by decide⟩
    ⟨⟨true, false, fun x y ↦ y || !x⟩, by decide⟩ ⟨⟨false, false, fun x y ↦ x || y⟩, by decide⟩
    ⟨⟨true, true, fun x y ↦ x && y⟩, by decide⟩]
  decide

end Switch

/-! ### Free choice under quantifiers -/

section Quantified

variable {D : Type*} [Nonempty D] (P Q B : D → Set W)

/-- The alternatives of `∀x(Px ∨ Qx)` (41) replace the disjunction by its disjuncts and by
their conjunctive counterpart `B`, and the universal by the existential. -/
def universalAlts : Set (Set W) :=
  {⋂ x, P x ∪ Q x, ⋂ x, P x, ⋂ x, Q x, ⋂ x, B x, ⋃ x, P x ∪ Q x, ⋃ x, P x, ⋃ x, Q x, ⋃ x, B x}

variable {P Q B}

/-- Given the four witnessing worlds, `∀x(Px ∨ Qx)` strengthens to universal free choice `∀x Px ∧ ∀x
Qx ∧ ¬∃x Bx` (44), of which (36) is the modal instance. -/
theorem universalFreeChoice (hB : ∀ x, B x ⊆ P x ∩ Q x)
    (h₁ : ∃ w, (∀ x, w ∈ P x) ∧ ∀ x, w ∉ Q x) (h₂ : ∃ w, (∀ x, w ∈ Q x) ∧ ∀ x, w ∉ P x)
    (h₃ : ∃ w, (∀ x, w ∈ P x ↔ w ∉ Q x) ∧ (∃ x, w ∈ P x) ∧ ∃ x, w ∈ Q x)
    (h : ∃ w, (∀ x, w ∈ P x) ∧ (∀ x, w ∈ Q x) ∧ ∀ x, w ∉ B x) :
    exhIEII (universalAlts P Q B) (⋂ x, P x ∪ Q x) = ((⋂ x, P x) ∩ ⋂ x, Q x) \ ⋃ x, B x := by
  obtain ⟨x₀⟩ := ‹Nonempty D›
  rw [universalAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_union,
      not_or, not_exists]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨-, hP⟩, hQ⟩, -⟩, -⟩, -⟩, -, hB'⟩
      exact ⟨⟨hP, hQ⟩, hB'⟩
    · rintro ⟨⟨hP, hQ⟩, hB'⟩
      exact ⟨⟨⟨⟨⟨⟨fun x ↦ Or.inl (hP x), hP⟩, hQ⟩, ⟨x₀, Or.inl (hP x₀)⟩⟩, ⟨x₀, hP x₀⟩⟩,
        ⟨x₀, hQ x₀⟩⟩, fun hx ↦ hB' x₀ (hx x₀), hB'⟩
  · intro w hw
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union] at hw ⊢
    by_cases hq : ∀ x, w ∉ Q x
    · exact Or.inl ⟨fun x ↦ (hw x).resolve_right (hq x), ⟨x₀, hw x₀⟩,
        ⟨x₀, (hw x₀).resolve_right (hq x₀)⟩⟩
    push Not at hq
    obtain ⟨y, hy⟩ := hq
    by_cases hp : ∀ x, w ∉ P x
    · exact Or.inr (Or.inl ⟨fun x ↦ (hw x).resolve_left (hp x), ⟨x₀, hw x₀⟩, ⟨y, hy⟩⟩)
    push Not at hp
    obtain ⟨z, hz⟩ := hp
    exact Or.inr (Or.inr ⟨⟨x₀, hw x₀⟩, ⟨z, hz⟩, ⟨y, hy⟩⟩)
  · obtain ⟨w, hP, hQ⟩ := h₁
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    exact ⟨fun x ↦ Or.inl (hP x), hP, ⟨x₀, Or.inl (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩,
      ⟨x₀, fun h ↦ hQ x₀ (hB x₀ h).2⟩, hQ, fun x h ↦ hQ x (hB x h).2⟩
  · obtain ⟨w, hQ, hP⟩ := h₂
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    exact ⟨fun x ↦ Or.inr (hQ x), hQ, ⟨x₀, Or.inr (hQ x₀)⟩, ⟨x₀, hQ x₀⟩, ⟨x₀, hP x₀⟩,
      ⟨x₀, fun h ↦ hP x₀ (hB x₀ h).1⟩, hP, fun x h ↦ hP x (hB x h).1⟩
  · obtain ⟨w, hPQ, ⟨y, hy⟩, ⟨z, hz⟩⟩ := h₃
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    refine ⟨fun x ↦ by by_cases h : w ∈ P x; exacts [Or.inl h, Or.inr (not_not.1 (mt (hPQ x).2 h))],
      ⟨y, Or.inl hy⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨z, (hPQ z).not.2 (not_not.2 hz)⟩, ⟨y, (hPQ y).1 hy⟩,
      ⟨y, fun h ↦ (hPQ y).1 hy (hB y h).2⟩, fun x h ↦ (hPQ x).1 (hB x h).1 (hB x h).2⟩
  · obtain ⟨w, hP, hQ, hB'⟩ := h
    refine ⟨w, ?_⟩
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_union, not_forall, not_exists]
    exact ⟨fun x ↦ Or.inl (hP x), hP, hQ, ⟨x₀, Or.inl (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩,
      ⟨x₀, hB' x₀⟩, hB'⟩

section Negative

variable (R : SetRel W W) (p q : D → Set W)

/-- The alternatives of `¬∃x □(px ∧ qx)`, *no student is required to solve both* (46), replace
the conjunction by its conjuncts and their disjunction, and *no* by *not every*. -/
def negativeUniversalAlts : Set (Set W) :=
  {(⋃ x, R.core (p x ∩ q x))ᶜ, (⋃ x, R.core (p x))ᶜ, (⋃ x, R.core (q x))ᶜ,
    (⋃ x, R.core (p x ∪ q x))ᶜ, (⋂ x, R.core (p x ∩ q x))ᶜ, (⋂ x, R.core (p x))ᶜ,
    (⋂ x, R.core (q x))ᶜ, (⋂ x, R.core (p x ∪ q x))ᶜ}

variable {R p q}

/-- Given the corresponding worlds, `¬∃x □(px ∧ qx)` strengthens to negative universal free choice
`¬∃x □px ∧ ¬∃x □qx ∧ ∀x □(px ∨ qx)` (47). -/
theorem negativeUniversalFreeChoice
    (h₁ : ∃ w, (∀ x, w ∉ R.core (p x)) ∧ ∀ x, w ∈ R.core (q x))
    (h₂ : ∃ w, (∀ x, w ∉ R.core (q x)) ∧ ∀ x, w ∈ R.core (p x))
    (h₃ : ∃ w, (∀ x, w ∈ R.core (p x ∪ q x)) ∧ (∀ x, w ∉ R.core (p x ∩ q x)) ∧
      (∃ x, w ∈ R.core (p x)) ∧ (∃ x, w ∈ R.core (q x)) ∧ (∃ x, w ∉ R.core (p x)) ∧
      ∃ x, w ∉ R.core (q x))
    (h : ∃ w, (∀ x, w ∉ R.core (p x)) ∧ (∀ x, w ∉ R.core (q x)) ∧ ∀ x, w ∈ R.core (p x ∪ q x)) :
    exhIEII (negativeUniversalAlts R p q) (⋃ x, R.core (p x ∩ q x))ᶜ =
      ((⋃ x, R.core (p x))ᶜ ∩ (⋃ x, R.core (q x))ᶜ) ∩ ⋂ x, R.core (p x ∪ q x) := by
  obtain ⟨x₀⟩ := ‹Nonempty D›
  have hpq : ∀ {w : W} {x : D}, w ∉ R.core (p x) → w ∉ R.core (p x ∩ q x) :=
    fun h h' ↦ h fun v hv ↦ (h' hv).1
  have hqp : ∀ {w : W} {x : D}, w ∉ R.core (q x) → w ∉ R.core (p x ∩ q x) :=
    fun h h' ↦ h fun v hv ↦ (h' hv).2
  rw [negativeUniversalAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
      Set.mem_iInter, Set.mem_iUnion, not_or, not_exists, not_forall, not_not]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨-, hP⟩, hQ⟩, -⟩, -⟩, -⟩, -, hPQ⟩
      exact ⟨⟨hP, hQ⟩, hPQ⟩
    · rintro ⟨⟨hP, hQ⟩, hPQ⟩
      exact ⟨⟨⟨⟨⟨⟨fun x ↦ hpq (hP x), hP⟩, hQ⟩, ⟨x₀, hpq (hP x₀)⟩⟩, ⟨x₀, hP x₀⟩⟩, ⟨x₀, hQ x₀⟩⟩,
        ⟨x₀, hPQ x₀⟩, hPQ⟩
  · intro w hw
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall] at hw ⊢
    by_cases hp : ∀ x, w ∉ R.core (p x)
    · exact Or.inl ⟨hp, ⟨x₀, hw x₀⟩, ⟨x₀, hp x₀⟩⟩
    push Not at hp
    obtain ⟨y, hy⟩ := hp
    by_cases hq : ∀ x, w ∉ R.core (q x)
    · exact Or.inr (Or.inl ⟨hq, ⟨x₀, hw x₀⟩, ⟨x₀, hq x₀⟩⟩)
    push Not at hq
    obtain ⟨z, hz⟩ := hq
    exact Or.inr (Or.inr ⟨⟨x₀, hw x₀⟩, ⟨z, fun h ↦ hw z fun v hv ↦ ⟨h hv, hz hv⟩⟩,
      ⟨y, fun h ↦ hw y fun v hv ↦ ⟨hy hv, h hv⟩⟩⟩)
  · obtain ⟨w, hP, hQ⟩ := h₁
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨fun x ↦ hpq (hP x), hP, ⟨x₀, hpq (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩,
      ⟨x₀, core_mono Set.subset_union_right (hQ x₀)⟩, hQ,
      fun x ↦ core_mono Set.subset_union_right (hQ x)⟩
  · obtain ⟨w, hQ, hP⟩ := h₂
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨fun x ↦ hqp (hQ x), hQ, ⟨x₀, hqp (hQ x₀)⟩, ⟨x₀, hQ x₀⟩, ⟨x₀, hP x₀⟩,
      ⟨x₀, core_mono Set.subset_union_left (hP x₀)⟩, hP,
      fun x ↦ core_mono Set.subset_union_left (hP x)⟩
  · obtain ⟨w, hPQ, hB, ⟨y, hy⟩, ⟨z, hz⟩, ⟨y', hy'⟩, ⟨z', hz'⟩⟩ := h₃
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨hB, ⟨x₀, hB x₀⟩, ⟨y', hy'⟩, ⟨z', hz'⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨x₀, hPQ x₀⟩, hPQ⟩
  · obtain ⟨w, hP, hQ, hPQ⟩ := h
    refine ⟨w, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_exists, not_forall, not_not]
    exact ⟨fun x ↦ hpq (hP x), hP, hQ, ⟨x₀, hpq (hP x₀)⟩, ⟨x₀, hP x₀⟩, ⟨x₀, hQ x₀⟩, ⟨x₀, hPQ x₀⟩,
      hPQ⟩

end Negative

section OverUniversal

variable (R : SetRel W W) (p q : D → Set W)

/-- The alternatives of `◇∀x(px ∨ qx)` (55). -/
def overUniversalAlts : Set (Set W) :=
  {R.preimage (⋂ x, p x ∪ q x), R.preimage (⋂ x, p x), R.preimage (⋂ x, q x),
    R.preimage (⋂ x, p x ∩ q x), R.preimage (⋃ x, p x ∪ q x), R.preimage (⋃ x, p x),
    R.preimage (⋃ x, q x), R.preimage (⋃ x, p x ∩ q x)}

variable {R p q}

/-- Given the corresponding worlds, `◇∀x(px ∨ qx)` strengthens to `◇∀x px ∧ ◇∀x qx ∧ ¬◇∃x(px ∧ qx)`
(57), [nouwen-2017]'s case. -/
theorem freeChoiceOverUniversal
    (h₁ : ∃ w ∈ R.preimage (⋂ x, p x), w ∉ R.preimage (⋃ x, q x))
    (h₂ : ∃ w ∈ R.preimage (⋂ x, q x), w ∉ R.preimage (⋃ x, p x))
    (h₃ : ∃ w ∈ R.preimage (⋂ x, p x ∪ q x) ∩ R.preimage (⋃ x, p x) ∩ R.preimage (⋃ x, q x),
      w ∉ R.preimage (⋂ x, p x) ∪ R.preimage (⋂ x, q x) ∪ R.preimage (⋃ x, p x ∩ q x))
    (h : ∃ w ∈ R.preimage (⋂ x, p x) ∩ R.preimage (⋂ x, q x), w ∉ R.preimage (⋃ x, p x ∩ q x)) :
    exhIEII (overUniversalAlts R p q) (R.preimage (⋂ x, p x ∪ q x)) =
      (R.preimage (⋂ x, p x) ∩ R.preimage (⋂ x, q x)) \ R.preimage (⋃ x, p x ∩ q x) := by
  obtain ⟨x₀⟩ := ‹Nonempty D›
  have hφ : R.preimage (⋂ x, p x) ⊆ R.preimage (⋂ x, p x ∪ q x) :=
    preimage_mono (Set.iInter_mono fun x ↦ Set.subset_union_left)
  have hφ' : R.preimage (⋂ x, q x) ⊆ R.preimage (⋂ x, p x ∪ q x) :=
    preimage_mono (Set.iInter_mono fun x ↦ Set.subset_union_right)
  have he : R.preimage (⋂ x, p x) ⊆ R.preimage (⋃ x, p x ∪ q x) :=
    preimage_mono fun w h ↦ Set.mem_iUnion.2 ⟨x₀, Or.inl (Set.mem_iInter.1 h x₀)⟩
  have he₁ : R.preimage (⋂ x, p x) ⊆ R.preimage (⋃ x, p x) :=
    preimage_mono fun w h ↦ Set.mem_iUnion.2 ⟨x₀, Set.mem_iInter.1 h x₀⟩
  have he₂ : R.preimage (⋂ x, q x) ⊆ R.preimage (⋃ x, q x) :=
    preimage_mono fun w h ↦ Set.mem_iUnion.2 ⟨x₀, Set.mem_iInter.1 h x₀⟩
  have hsb : R.preimage (⋂ x, p x ∩ q x) ⊆ R.preimage (⋃ x, p x ∩ q x) :=
    preimage_mono fun w h ↦ Set.mem_iUnion.2 ⟨x₀, Set.mem_iInter.1 h x₀⟩
  have hbp : R.preimage (⋃ x, p x ∩ q x) ⊆ R.preimage (⋃ x, p x) :=
    preimage_mono (Set.iUnion_mono fun x ↦ Set.inter_subset_left)
  have hbq : R.preimage (⋃ x, p x ∩ q x) ⊆ R.preimage (⋃ x, q x) :=
    preimage_mono (Set.iUnion_mono fun x ↦ Set.inter_subset_right)
  rw [overUniversalAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, not_or]
    exact ⟨fun h ↦ ⟨⟨h.1.1.1.1.1.2, h.1.1.1.1.2⟩, h.2.2⟩,
      fun h ↦ ⟨⟨⟨⟨⟨⟨hφ h.1.1, h.1.1⟩, h.1.2⟩, he h.1.1⟩, he₁ h.1.1⟩, he₂ h.1.2⟩,
        fun h' ↦ h.2 (hsb h'), h.2⟩⟩
  · rintro w ⟨v, hvpq, hv⟩
    have hvpq' := fun x ↦ Set.mem_iInter.1 hvpq x
    by_cases hq : ∀ x, v ∉ q x
    · exact Or.inl ⟨⟨v, Set.mem_iInter.2 fun x ↦ (hvpq' x).resolve_right (hq x), hv⟩,
        ⟨v, Set.mem_iUnion.2 ⟨x₀, hvpq' x₀⟩, hv⟩,
        ⟨v, Set.mem_iUnion.2 ⟨x₀, (hvpq' x₀).resolve_right (hq x₀)⟩, hv⟩⟩
    push Not at hq
    obtain ⟨y, hy⟩ := hq
    by_cases hp : ∀ x, v ∉ p x
    · exact Or.inr (Or.inl ⟨⟨v, Set.mem_iInter.2 fun x ↦ (hvpq' x).resolve_left (hp x), hv⟩,
        ⟨v, Set.mem_iUnion.2 ⟨x₀, hvpq' x₀⟩, hv⟩, ⟨v, Set.mem_iUnion.2 ⟨y, hy⟩, hv⟩⟩)
    push Not at hp
    obtain ⟨z, hz⟩ := hp
    exact Or.inr (Or.inr ⟨⟨v, Set.mem_iUnion.2 ⟨x₀, hvpq' x₀⟩, hv⟩,
      ⟨v, Set.mem_iUnion.2 ⟨z, hz⟩, hv⟩, ⟨v, Set.mem_iUnion.2 ⟨y, hy⟩, hv⟩⟩)
  · obtain ⟨w, hP, hQ⟩ := h₁
    exact ⟨w, hφ hP, hP, he hP, he₁ hP, fun h ↦ hQ (he₂ h), fun h ↦ hQ (hbq (hsb h)), hQ,
      fun h ↦ hQ (hbq h)⟩
  · obtain ⟨w, hQ, hP⟩ := h₂
    exact ⟨w, hφ' hQ, hQ, preimage_mono (Set.iUnion_mono fun x ↦ Set.subset_union_right) (he₂ hQ),
      he₂ hQ, fun h ↦ hP (he₁ h), fun h ↦ hP (hbp (hsb h)), hP, fun h ↦ hP (hbp h)⟩
  · obtain ⟨w, ⟨⟨hPQ, hP⟩, hQ⟩, hn⟩ := h₃
    simp only [Set.mem_union, not_or] at hn
    exact ⟨w, hPQ, preimage_mono (Set.iUnion_mono fun x ↦ Set.subset_union_left) hP, hP, hQ, hn.1.1,
      hn.1.2, fun h ↦ hn.2 (hsb h), hn.2⟩
  · obtain ⟨w, ⟨hP, hQ⟩, hB⟩ := h
    exact ⟨w, hφ hP, hP, hQ, he hP, he₁ hP, he₂ hQ, fun h ↦ hB (hsb h), hB⟩

end OverUniversal

end Quantified

/-! ### Simplification with *most* -/

section Most

variable {D : Type*} [DecidableEq D]

/-- `Most P S` says that more than half of `P` lies in `S` (86). -/
def Most (P S : Finset D) : Prop := P.card < 2 * (P ∩ S).card

/-- `Overlaps P S` says that `P` and `S` meet. -/
def Overlaps (P S : Finset D) : Prop := (P ∩ S).Nonempty

variable {P Q S : Finset D}

theorem Most.overlaps (h : Most P S) : Overlaps P S :=
  Finset.card_pos.1 (by unfold Most at h; omega)

theorem Overlaps.of_inter_left (h : Overlaps (P ∩ Q) S) : Overlaps P S :=
  h.mono (Finset.inter_subset_inter_right Finset.inter_subset_left)

theorem Overlaps.of_inter_right (h : Overlaps (P ∩ Q) S) : Overlaps Q S :=
  h.mono (Finset.inter_subset_inter_right Finset.inter_subset_right)

theorem overlaps_union_iff : Overlaps (P ∪ Q) S ↔ Overlaps P S ∨ Overlaps Q S := by
  simp only [Overlaps, Finset.union_inter_distrib_right, Finset.union_nonempty]

theorem Most.of_union (h : Most (P ∪ Q) S) (hQ : ¬ Overlaps Q S) : Most P S := by
  have h₁ : (P ∪ Q) ∩ S = P ∩ S := by
    rw [Finset.union_inter_distrib_right, Finset.not_nonempty_iff_eq_empty.1 hQ,
      Finset.union_empty]
  have h₂ := Finset.card_le_card (Finset.subset_union_left (s₁ := P) (s₂ := Q))
  unfold Most at h ⊢
  rw [h₁] at h
  omega

theorem Most.of_union_right (h : Most (P ∪ Q) S) (hP : ¬ Overlaps P S) : Most Q S :=
  (Finset.union_comm P Q ▸ h).of_union hP

variable (P Q S : W → Finset D)

/-- The alternatives of `most(P ∪ Q)(S)` (87) replace the disjunctive restrictor by its
disjuncts and their intersection, and *most* by *some*. -/
def mostAlts : Set (Set W) :=
  {{w | Most (P w ∪ Q w) (S w)}, {w | Most (P w) (S w)}, {w | Most (Q w) (S w)},
    {w | Most (P w ∩ Q w) (S w)}, {w | Overlaps (P w ∪ Q w) (S w)}, {w | Overlaps (P w) (S w)},
    {w | Overlaps (Q w) (S w)}, {w | Overlaps (P w ∩ Q w) (S w)}}

variable {P Q S}

/-- Given the four witnessing worlds, `most(P ∪ Q)(S)` strengthens to `most(P)(S) ∧ most(Q)(S) ∧
¬some(P ∩ Q)(S)` (89). -/
theorem simplificationMost
    (h₁ : ∃ w, Most (P w ∪ Q w) (S w) ∧ Most (P w) (S w) ∧ ¬ Overlaps (Q w) (S w))
    (h₂ : ∃ w, Most (P w ∪ Q w) (S w) ∧ Most (Q w) (S w) ∧ ¬ Overlaps (P w) (S w))
    (h₃ : ∃ w, Most (P w ∪ Q w) (S w) ∧ ¬ Most (P w) (S w) ∧ ¬ Most (Q w) (S w) ∧
      Overlaps (P w) (S w) ∧ Overlaps (Q w) (S w) ∧ ¬ Overlaps (P w ∩ Q w) (S w))
    (h : ∃ w, Most (P w ∪ Q w) (S w) ∧ Most (P w) (S w) ∧ Most (Q w) (S w) ∧
      ¬ Overlaps (P w ∩ Q w) (S w)) :
    exhIEII (mostAlts P Q S) {w | Most (P w ∪ Q w) (S w)} =
      ({w | Most (P w ∪ Q w) (S w)} ∩ {w | Most (P w) (S w)} ∩ {w | Most (Q w) (S w)}) \
        {w | Overlaps (P w ∩ Q w) (S w)} := by
  rw [mostAlts, exhIEII_quantified ?_ ?_ ?_ ?_ ?_]
  · ext w
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, not_or]
    exact ⟨fun h ↦ ⟨⟨⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2⟩, h.1.1.1.1.2⟩, h.2.2⟩,
      fun h ↦ ⟨⟨⟨⟨⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩, h.1.1.1.overlaps⟩, h.1.1.2.overlaps⟩,
        h.1.2.overlaps⟩, fun h' ↦ h.2 h'.overlaps, h.2⟩⟩
  · intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rcases overlaps_union_iff.1 hw.overlaps with hP | hQ
    · by_cases hQ : Overlaps (Q w) (S w)
      · exact Or.inr (Or.inr ⟨hw.overlaps, hP, hQ⟩)
      · exact Or.inl ⟨hw.of_union hQ, hw.overlaps, hP⟩
    · by_cases hP : Overlaps (P w) (S w)
      · exact Or.inr (Or.inr ⟨hw.overlaps, hP, hQ⟩)
      · exact Or.inr (Or.inl ⟨hw.of_union_right hP, hw.overlaps, hQ⟩)
  · obtain ⟨w, hPQ, hP, hQ⟩ := h₁
    exact ⟨w, hPQ, hP, hPQ.overlaps, hP.overlaps, fun h ↦ hQ h.overlaps,
      fun h ↦ hQ h.overlaps.of_inter_right, hQ, fun h ↦ hQ h.of_inter_right⟩
  · obtain ⟨w, hPQ, hQ, hP⟩ := h₂
    exact ⟨w, hPQ, hQ, hPQ.overlaps, hQ.overlaps, fun h ↦ hP h.overlaps,
      fun h ↦ hP h.overlaps.of_inter_left, hP, fun h ↦ hP h.of_inter_left⟩
  · obtain ⟨w, hPQ, hP, hQ, hP', hQ', hB⟩ := h₃
    exact ⟨w, hPQ, hPQ.overlaps, hP', hQ', hP, hQ, fun h ↦ hB h.overlaps, hB⟩
  · obtain ⟨w, hPQ, hP, hQ, hB⟩ := h
    exact ⟨w, hPQ, hP, hQ, hPQ.overlaps, hP.overlaps, hQ.overlaps, fun h ↦ hB h.overlaps, hB⟩

end Most

end BarLevFox2020
