module

public import Linglib.Data.Examples.KrizChemla2015
public import Linglib.Data.Experiments.KrizChemla2015
public import Linglib.Logic.Trivalent.Flat
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Semantics.Quantification.NumberTree
public import Studies.Magri2014
public import Mathlib.Data.List.Sections

/-!
# Križ and Chemla (2015): finding truth-value gaps

Križ and Chemla introduce two experimental methods for detecting truth-value gaps and use them to
ask where the homogeneity gap of a plural definite survives embedding, under sentential negation,
*all*, *no* and *exactly 2*. A display gives each of four cells, or boys, the trivalent value of
the bare plural over its nine symbols, or presents, and a sentence is evaluated by its quantifier
on the display resolved existentially or universally, the variants with *some* and with *all* in
place of the definite. Gaps were found exactly where the two variants differ, which includes the
GAP?? configuration of *exactly 2* and excludes its GAP? configuration. Of the accounts the paper
assesses, Spector's supervaluation over the two resolutions fits every finding; comparing the
literal with the globally exhaustified meaning, after Magri, misses the gaps under negation, under
*no* and in the GAP?? configuration; and the universal projection of a homogeneity presupposition
predicts gaps where false was found.

## Main results

* `items_variants`: every display of Table 13 realizes its condition, except the faulty A2 and B2
  *no* items (`faulty_items`) and the GAP? item 5599 (`misprinted_gapQQ`).
* `found_iff`: Table 2 finds a gap exactly outside GAP?, apart from the discounted *no* tests.
* `supervaluation_eq_one_iff_condition`, `supervaluation_eq_zero_iff_found`: the supervaluation
  predicts every designed value and every finding.
* `globalConstrual_misfit_iff`: the implicature construal misfits exactly the downward-entailing
  GAP items and the GAP?? items; `globalConstrual_wideScope`: a wide-scope definite rescues it
  under plain negation.
* `pointwise_ne_iff`: supervaluating over per-boy resolutions departs exactly on GAP?.
* `situations_variants`: Table 12's parses and construals follow from its six situations.
* `globalExh_iff_mem_strengthened`: global exhaustification is Magri's double strengthening.

## Implementation notes

The stimuli and findings are the tables of `Data/Experiments/KrizChemla2015`. The E-neg tests reuse
the E-∅ displays with the negated sentence, whose designed values swap (`negationItems`), and
sentential negation is the outer negation `notAll` of the unembedded sentence. The weak and strong
variants are the some- and all-substituted readings, exchanged under a downward-entailing scope,
which is how §3's principle, stated for upward-entailing contexts, extends to negation and *no*.
The A2 and B2 *no* tests are discounted, as footnotes 10 and 14 do. The statistics are stored as
printed and not re-thresholded; the (si2) and (si4) construals are the supervaluation by Table
12's lit ≠ loc column.

## TODO

* The trivalent projection theory after George that §6.3 credits with matching the
  supervaluation is not implemented.

## References

* [kriz-chemla-2015]
* [spector-2013b]
* [magri-2009]
* [magri-2014]
* [chierchia-fox-spector-2012]
* [schwarzschild-1994]
* [lobner-2000]
* [gajewski-2005]
* [george-2008]
* [steedman-2012]
* [beaver-krahmer-2001]
* [van-benthem-1984]
-/

@[expose] public section

namespace KrizChemla2015

open Quantifier
open Trivalent (Designation)

/-! ### Displays and their resolutions -/

/-- A display lists, for each boy, the trivalent value of *he found his presents*. -/
abbrev Display := List SignType

/-- A cell in which `n` of the nine objects are found or target-colored has the value of the
bare plural over the nine, true when all are, false when none are, and a gap otherwise. -/
def cell (n : ℕ) : SignType :=
  Homogeneity.barePlural (fun j m ↦ j < m) (Finset.range 9) n

/-- A cell is true, designated at K3, when all nine objects are found. -/
theorem designated_k3_cell (n : ℕ) : cell n = 1 ↔ 9 ≤ n := by
  rw [cell, Homogeneity.barePlural, SignType.supervaluation_eq_one_iff]
  exact ⟨fun h ↦ h 8 (by simp), fun h j hj ↦ by simp at hj; omega⟩

/-- A cell is non-false, designated at LP, when at least one object is found. -/
theorem designated_lp_cell (n : ℕ) : 0 ≤ cell n ↔ 1 ≤ n := by
  rw [SignType.nonneg_iff_ne_neg_one, Ne, cell, Homogeneity.barePlural,
    SignType.supervaluation_eq_neg_one_iff]
  simp only [Finset.mem_range, not_and, not_forall, not_not, exists_prop]
  exact ⟨fun h ↦ by obtain ⟨j, -, hj⟩ := h ⟨0, by simp⟩; omega,
    fun h _ ↦ ⟨0, by omega, h⟩⟩

/-- A number tree holds of a resolution according to how many boys it resolves out of and into
the scope. -/
def holds (q : NumberTree) (c : List Bool) : Prop := q (c.count false) (c.count true)

instance (q : NumberTree) [DecidableRel q] (c : List Bool) : Decidable (holds q c) :=
  inferInstanceAs (Decidable (q _ _))

/-- Reversing every boy's resolution evaluates the inner negation. -/
theorem holds_map_not (q : NumberTree) (c : List Bool) :
    holds q (c.map not) ↔ holds q.innerNeg c := by
  have h (b : Bool) : (c.map not).count b = c.count (!b) := by
    induction c with
    | nil => rfl
    | cons x xs ih => cases x <;> cases b <;> simp [ih]
  simp [holds, NumberTree.innerNeg, h]

/-- The uniform resolution of a display at a designation standard puts each boy in the scope
when his value is designated. -/
def resolve (δ : Designation) (d : Display) : List Bool := d.map fun v ↦ decide (δ.threshold ≤ v)

/-- Negating every cell resolves at the dual standard and reverses the result. -/
theorem resolve_map_neg (δ : Designation) (d : Display) :
    resolve δ (d.map Neg.neg) = (resolve δ.dual d).map not := by
  simp only [resolve, List.map_map]
  refine List.map_congr_left fun v _ ↦ ?_
  have := Trivalent.Designation.dual_threshold_le_neg_iff δ.dual v
  rw [Trivalent.Designation.dual_dual] at this
  simp only [Function.comp_apply, this, decide_not]

/-- The resolutions of a display that choose a designation standard boy by boy. -/
def resolutions (d : Display) : List (List Bool) :=
  (d.map fun v ↦ [decide (0 ≤ v), decide (v = 1)]).sections

theorem resolve_mem_resolutions (δ : Designation) (d : Display) :
    resolve δ d ∈ resolutions d := by
  refine List.mem_sections.2 <| List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
    List.forall₂_same.2 fun v _ ↦ ?_
  cases δ <;> simp

/-- The K3 resolution is least and the LP resolution greatest among the resolutions. -/
theorem resolve_le_of_mem_resolutions {d : Display} {c : List Bool} (hc : c ∈ resolutions d) :
    List.Forall₂ (· ≤ ·) (resolve .k3 d) c ∧ List.Forall₂ (· ≤ ·) c (resolve .lp d) := by
  have h := List.forall₂_map_right_iff.1 (List.mem_sections.1 hc)
  refine ⟨List.forall₂_map_left_iff.2 (h.flip.imp fun v b hb ↦ ?_),
    List.forall₂_map_right_iff.2 (h.imp fun b v hb ↦ ?_)⟩ <;>
  cases v <;> cases b <;> simp_all

/-- A display without partial cells has a single resolution. -/
theorem resolve_lp_eq_resolve_k3 {d : Display} (h : ∀ v ∈ d, v ≠ 0) :
    resolve .lp d = resolve .k3 d :=
  List.map_congr_left fun v hv ↦ by cases v <;> first | rfl | exact absurd rfl (h _ hv)

/-- Moving boys into the scope preserves a scope-monotone quantifier. -/
theorem holds_of_forall₂_le {q : NumberTree} (hq : q.ScopeMonotone) {c c' : List Bool}
    (h : List.Forall₂ (· ≤ ·) c c') (hc : holds q c) : holds q c' := by
  obtain ⟨j, h₁, h₂⟩ : ∃ j, c'.count true = c.count true + j ∧
      c.count false = c'.count false + j := by
    clear hc
    induction h with
    | nil => exact ⟨0, rfl, rfl⟩
    | @cons b b' _ _ hb _ ih =>
      obtain ⟨j, h₁, h₂⟩ := ih
      cases b <;> cases b'
      · exact ⟨j, by simp [h₁], by simp [h₂]; omega⟩
      · exact ⟨j + 1, by simp [h₁]; omega, by simp [h₂]; omega⟩
      · exact absurd hb (by decide)
      · exact ⟨j, by simp [h₁]; omega, by simp [h₂]⟩
  unfold holds at hc ⊢
  rw [h₂] at hc
  rw [h₁]
  exact hq.shift j hc

/-! ### The some- and all-substituted readings

§3's guiding principle: a sentence with a definite plural has a gap in a situation where the
variant with an existential in place of the definite is true while the variant with a universal is
false. -/

section Readings

variable (q : NumberTree) (d : Display)

/-- A reading evaluates the quantifier over the uniform resolution at `δ`, which at LP
(non-false) is the existential resolution of the definite and at K3 (true) the universal one. -/
def reading (δ : Designation) : Prop := holds q (resolve δ d)

/-- The some-substituted reading puts *some (of his) presents* in place of the definite. It is
the literal meaning on [magri-2014]'s analysis and the existential resolution on
[spector-2013b]'s. -/
abbrev someReading : Prop := reading q d .lp

/-- The all-substituted reading puts *all of his presents* in place of the definite. It is the
locally exhaustified parse on [magri-2014]'s analysis and the universal resolution on
[spector-2013b]'s. -/
abbrev allReading : Prop := reading q d .k3

instance [DecidableRel q] (δ : Designation) : Decidable (reading q d δ) :=
  inferInstanceAs (Decidable (holds q _))

variable {q d}

/-- The universal quantifier holds of a resolution when every boy is in the scope. -/
theorem reading_all (δ : Designation) : reading NumberTree.all d δ ↔ ∀ v ∈ d, δ.threshold ≤ v := by
  simp [reading, holds, resolve, NumberTree.all, List.count_eq_zero]

/-- The negative quantifier holds of a resolution when no boy is in the scope. -/
theorem reading_no (δ : Designation) : reading NumberTree.no d δ ↔ ∀ v ∈ d, ¬ δ.threshold ≤ v := by
  simp [reading, holds, resolve, NumberTree.no, List.count_eq_zero]

/-- Negating the predicate in every cell evaluates the inner negation of the quantifier at the
dual standard, so it exchanges the some- and all-substituted readings. -/
theorem reading_map_neg (δ : Designation) :
    reading q (d.map Neg.neg) δ ↔ reading q.innerNeg d δ.dual := by
  rw [reading, reading, resolve_map_neg, holds_map_not]

/-- On a display without partial cells the two resolutions coincide. -/
theorem someReading_iff_allReading (h : ∀ v ∈ d, v ≠ 0) :
    someReading q d ↔ allReading q d := by
  rw [someReading, allReading, reading, reading, resolve_lp_eq_resolve_k3 h]

/-- Under a scope-monotone quantifier the universal variant entails the existential one. -/
theorem allReading_imp_someReading (hq : q.ScopeMonotone) : allReading q d → someReading q d :=
  holds_of_forall₂_le hq (resolve_le_of_mem_resolutions (resolve_mem_resolutions .lp d)).1

/-- Under a scope-antitone quantifier the existential variant entails the universal one. -/
theorem someReading_imp_allReading (hq : q.ScopeAntitone) : someReading q d → allReading q d :=
  fun hs ↦ not_not.1 fun ha ↦ allReading_imp_someReading (q := qᶜ) hq.compl ha hs

end Readings

/-! ### Two-component verdicts -/

/-- The verdict from two meaning components is the supervaluation over the pair, clearly true
when both hold, clearly false when neither does, and a truth-value gap when they conflict. -/
def gapValue (p q : Prop) [Decidable p] [Decidable q] : SignType :=
  SignType.supervaluation Finset.univ fun b : Bool ↦ if b then p else q

section GapValue

variable {p q : Prop} [Decidable p] [Decidable q]

@[simp] theorem gapValue_eq_one_iff : gapValue p q = 1 ↔ p ∧ q := by
  simp [gapValue, SignType.supervaluation_eq_one_iff, Bool.forall_bool, and_comm]

@[simp] theorem gapValue_eq_neg_one_iff : gapValue p q = -1 ↔ ¬ p ∧ ¬ q := by
  simp [gapValue, SignType.supervaluation_eq_neg_one_iff, Bool.forall_bool, and_comm]

@[simp] theorem gapValue_eq_zero_iff : gapValue p q = 0 ↔ ¬ (p ↔ q) := by
  simp only [gapValue, SignType.supervaluation_eq_zero_iff, Finset.mem_univ, true_and,
    Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true]
  tauto

/-- Two components that agree yield a bivalent verdict. -/
theorem gapValue_ne_zero (h : p ↔ q) : gapValue p q ≠ 0 := by simp [h]

end GapValue

/-! ### The approaches of §6 -/

section GlobalExh

variable (q : NumberTree) (d : Display)

/-- The globally double-exhaustified meaning, (30) and (39), is the conjunction of the some- and
all-substituted readings, [magri-2014]'s double strengthening
(`globalExh_iff_mem_strengthened`). In a downward-entailing scope exhaustification is vacuous,
and the conjunction is then the literal meaning (`globalExh_iff_of_scopeAntitone`). -/
def globalExh : Prop := someReading q d ∧ allReading q d

variable {q d} in
/-- Under a downward-entailing quantifier global exhaustification is vacuous. -/
theorem globalExh_iff_of_scopeAntitone (hq : q.ScopeAntitone) :
    globalExh q d ↔ someReading q d :=
  ⟨And.left, fun h ↦ ⟨h, someReading_imp_allReading hq h⟩⟩

end GlobalExh

section Approaches

variable (q : NumberTree) [DecidableRel q] (d : Display)

/-- The supervaluation of [spector-2013b] (§6.2) makes the sentence true when it is true however
the definite is resolved, existentially or universally, and false when it is false however it is
resolved. -/
def supervaluation : SignType := SignType.supervaluation Finset.univ (reading q d)

instance : Decidable (globalExh q d) := inferInstanceAs (Decidable (_ ∧ _))

/-- The implicature construals (si1) and (si3) of §6.1.2, after [magri-2009]'s oddness condition,
put a gap where the literal and the globally exhaustified meaning conflict. -/
def globalConstrual : SignType := gapValue (someReading q d) (globalExh q d)

/-- Homogeneity as a presupposition projecting universally from the quantifier's scope, after
[schwarzschild-1994], [lobner-2000] and [gajewski-2005] as assessed in §6.3, is the presupposition
that every cell is homogeneous weakly conjoined with the universal-force assertion. The
presupposition is the ∂ of [beaver-krahmer-2001], the join `p ⊔ 0` with the gap. -/
def universalPresupposition : SignType :=
  (SignType.ofProp (∀ v ∈ d, v ≠ 0) ⊔ 0).meetWeak (.ofProp (allReading q d))

/-- Supervaluation over the resolutions that treat the partial cells one by one, a richer
candidate set than the existential and universal readings, of the kind §6.2 says predicts a gap
in the gap? condition; footnote 19 notes that quantified trivalent logics make the same
prediction. -/
def pointwise : SignType := SignType.supervaluation (resolutions d).toFinset (holds q)

variable {q d}

/-- The supervaluation ranges over the two designation standards. -/
theorem supervaluation_eq_designations :
    supervaluation q d = SignType.supervaluation Finset.univ (reading q d) :=
  rfl

private theorem forall_designation {P : Designation → Prop} : (∀ δ, P δ) ↔ P .lp ∧ P .k3 :=
  ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨h₁, h₂⟩ δ ↦ by cases δ <;> assumption⟩

/-- The supervaluation is true when both variants are. -/
theorem supervaluation_eq_one_iff :
    supervaluation q d = 1 ↔ someReading q d ∧ allReading q d := by
  simp [supervaluation, SignType.supervaluation_eq_one_iff, forall_designation]

/-- The supervaluation is false when neither variant is true. -/
theorem supervaluation_eq_neg_one_iff :
    supervaluation q d = -1 ↔ ¬ someReading q d ∧ ¬ allReading q d := by
  simp [supervaluation, SignType.supervaluation_eq_neg_one_iff, forall_designation]

/-- The supervaluation gaps when the variants differ. -/
theorem supervaluation_eq_zero_iff :
    supervaluation q d = 0 ↔ ¬ (someReading q d ↔ allReading q d) := by
  have h {P : Designation → Prop} : (∃ δ, P δ) ↔ P .lp ∨ P .k3 :=
    ⟨fun ⟨δ, h⟩ ↦ by cases δ <;> tauto, fun h ↦ h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩
  simp only [supervaluation, SignType.supervaluation_eq_zero_iff, Finset.mem_univ, true_and, h]
  tauto

/-- A display without partial cells gets a bivalent verdict, whatever the quantifier. -/
theorem supervaluation_ne_zero (h : ∀ v ∈ d, v ≠ 0) : supervaluation q d ≠ 0 := by
  simp [supervaluation_eq_zero_iff, someReading_iff_allReading h]

/-- The supervaluation does not see the scope of the definite relative to a negation inside the
cells, since negating every cell gives the supervaluation of the inner negation. -/
theorem supervaluation_map_neg :
    supervaluation q (d.map Neg.neg) = supervaluation q.innerNeg d := by
  have h : (Finset.univ : Finset Designation).image Designation.dual = Finset.univ := by decide
  rw [supervaluation, supervaluation]
  conv_rhs => rw [← h, SignType.supervaluation_image]
  exact SignType.supervaluation_congr fun δ _ ↦ reading_map_neg δ

/-- The outer negation of the quantifier negates the supervaluation. -/
theorem supervaluation_compl : supervaluation qᶜ d = -supervaluation q d := by
  rw [supervaluation, supervaluation, ← SignType.supervaluation_not _ Finset.univ_nonempty]
  rfl

/-- The global construal gaps where the literal meaning holds and the all-substituted one fails. -/
theorem globalConstrual_eq_zero_iff :
    globalConstrual q d = 0 ↔ someReading q d ∧ ¬ allReading q d := by
  rw [globalConstrual, gapValue_eq_zero_iff, globalExh]
  tauto

/-- The global construals depart from supervaluation exactly where the literal meaning is false
and the locally exhaustified meaning true. -/
theorem globalConstrual_ne_supervaluation_iff :
    globalConstrual q d ≠ supervaluation q d ↔ ¬ someReading q d ∧ allReading q d := by
  rcases h₁ : globalConstrual q d with _ | _ | _ <;>
    rcases h₂ : supervaluation q d with _ | _ | _ <;>
    simp_all [globalConstrual, globalExh, supervaluation_eq_one_iff, supervaluation_eq_neg_one_iff,
      supervaluation_eq_zero_iff]

/-- In the scope of a scope-monotone quantifier such as *every* the implicature construals all
align, since comparing the literal meaning with global exhaustification and with local
exhaustification comes to the same thing (§6.1.3). -/
theorem globalConstrual_eq_supervaluation_of_scopeMonotone (hq : q.ScopeMonotone) :
    globalConstrual q d = supervaluation q d :=
  not_not.1 fun h ↦ (globalConstrual_ne_supervaluation_iff.1 h).elim fun hs ha ↦
    hs (allReading_imp_someReading hq ha)

/-- Without local exhaustification no gap can arise in the scope of a downward-entailing
quantifier such as *no*, since exhaustification is vacuous there and the literal and globally
exhaustified meanings never conflict. -/
theorem globalConstrual_ne_zero_of_scopeAntitone (hq : q.ScopeAntitone) :
    globalConstrual q d ≠ 0 :=
  gapValue_ne_zero (globalExh_iff_of_scopeAntitone hq).symm

/-- Universal projection fails exactly on the displays with a partial cell. -/
theorem universalPresupposition_eq_zero_iff :
    universalPresupposition q d = 0 ↔ 0 ∈ d := by
  rw [universalPresupposition, SignType.meetWeak_eq_zero_iff]
  simp only [SignType.sup_zero_eq_zero_iff, SignType.ofProp_ne_zero, or_false, Ne,
    SignType.ofProp_eq_one_iff, not_forall, exists_prop, not_not, exists_eq_right]

end Approaches

/-! ### Negation and the wide-scope parse (§6.1.3) -/

/-- Over one cell the unembedded sentence takes the cell's value. -/
theorem supervaluation_all_singleton (v : SignType) : supervaluation NumberTree.all [v] = v := by
  cases v <;> decide

/-- The literal-against-global construal never gaps under plain negation, which is downward
entailing. -/
theorem globalConstrual_notAll_ne_zero (v : SignType) :
    globalConstrual NumberTree.notAll [v] ≠ 0 :=
  globalConstrual_ne_zero_of_scopeAntitone NumberTree.scopeAntitone_notAll

/-- On the parse (35) where the definite takes scope over negation, the literal-against-global
construal of *the shapes are not green* is the supervaluation of its narrow-scope negation, so it
gaps exactly on the mixed cell. No such parse is available under *no*, whose definite contains a
variable the quantifier binds. -/
theorem globalConstrual_wideScope (v : SignType) :
    globalConstrual NumberTree.all [-v] = supervaluation NumberTree.notAll [v] := by
  rw [globalConstrual_eq_supervaluation_of_scopeMonotone NumberTree.scopeMonotone_all]
  exact supervaluation_map_neg (q := NumberTree.all) (d := [v]) |>.trans (by cases v <;> decide)

/-! ### Global exhaustification is double strengthening -/

section Strengthening

open Magri2014 (strengthened primalMates primal)

variable (q : NumberTree) [DecidableRel q] (n : ℕ)

/-- The displays of `n` boys on which the some-substituted reading holds, the weak pole. -/
def weakPole : Finset (Fin n → SignType) :=
  Finset.univ.filter fun w ↦ someReading q (List.ofFn w)

/-- The displays of `n` boys on which the all-substituted reading holds, the strong pole. -/
def strongPole : Finset (Fin n → SignType) :=
  Finset.univ.filter fun w ↦ allReading q (List.ofFn w)

variable {q n}

/-- Exhaustifying the sentence twice over its some- and all-substituted alternatives, by
[magri-2014]'s double strengthening, yields `globalExh`, (30) and (39), provided either the strong
pole is weaker, as in a downward-entailing scope, or the two poles are compatible. -/
theorem globalExh_iff_mem_strengthened
    (h : weakPole q n ⊆ strongPole q n ∨ (weakPole q n ∩ strongPole q n).Nonempty)
    (w : Fin n → SignType) :
    globalExh q (List.ofFn w) ↔
      w ∈ strengthened primalMates (primal (weakPole q n) (strongPole q n)) .mystery := by
  rcases (weakPole q n \ strongPole q n).eq_empty_or_nonempty with h₀ | h₀
  · have hsub := Finset.sdiff_eq_empty_iff_subset.1 h₀
    rw [Magri2014.strengthened_primal_mystery_of_subset hsub]
    have hw : w ∈ weakPole q n ↔ someReading q (List.ofFn w) := by simp [weakPole]
    have hw' : w ∈ strongPole q n ↔ allReading q (List.ofFn w) := by simp [strongPole]
    exact ⟨fun h ↦ hw.2 h.1, fun h ↦ ⟨hw.1 h, hw'.1 (hsub h)⟩⟩
  · have h₂ := h.resolve_left fun hsub ↦ by simp [Finset.sdiff_eq_empty_iff_subset.2 hsub] at h₀
    rw [Magri2014.strengthened_primal_mystery h₀ h₂]
    simp [weakPole, strongPole, globalExh]

end Strengthening

/-! ### Per-boy resolutions -/

section Pointwise

variable {q : NumberTree} [DecidableRel q] {d : Display}

/-- The two-candidate supervaluation ranges over the uniform resolutions. -/
theorem supervaluation_eq_image :
    supervaluation q d =
      SignType.supervaluation (Finset.univ.image fun δ ↦ resolve δ d) (holds q) := by
  rw [supervaluation, SignType.supervaluation_image]
  rfl

/-- Richer candidates can only add gaps, since whatever the quantifier the per-boy supervaluation
is at most as informative as the two-candidate one. -/
theorem toFlat_pointwise_le :
    SignType.toFlat (pointwise q d) ≤ SignType.toFlat (supervaluation q d) := by
  rw [supervaluation_eq_image]
  refine SignType.toFlat_supervaluation_mono _ (fun c hc ↦ ?_) (Finset.univ_nonempty.image _)
  obtain ⟨δ, -, rfl⟩ := Finset.mem_image.1 hc
  exact List.mem_toFinset.2 (resolve_mem_resolutions δ d)

/-- Under a scope-monotone quantifier the per-boy resolutions add no gap, the uniform ones being
their extremes. -/
theorem pointwise_eq_supervaluation_of_scopeMonotone (hq : q.ScopeMonotone) :
    pointwise q d = supervaluation q d := by
  have hk3 := List.mem_toFinset.2 (resolve_mem_resolutions .k3 d)
  have hlp := List.mem_toFinset.2 (resolve_mem_resolutions .lp d)
  have hall : (∀ c ∈ (resolutions d).toFinset, holds q c) ↔ allReading q d :=
    ⟨fun h ↦ h _ hk3, fun h c hc ↦ holds_of_forall₂_le hq
      (resolve_le_of_mem_resolutions (List.mem_toFinset.1 hc)).1 h⟩
  have hex : (∃ c ∈ (resolutions d).toFinset, holds q c) ↔ someReading q d :=
    ⟨fun ⟨c, hc, h⟩ ↦ holds_of_forall₂_le hq
      (resolve_le_of_mem_resolutions (List.mem_toFinset.1 hc)).2 h, fun h ↦ ⟨_, hlp, h⟩⟩
  have hle := allReading_imp_someReading (d := d) hq
  cases h : supervaluation q d
  · have ⟨hs, ha⟩ : someReading q d ∧ ¬ allReading q d := by
      have := supervaluation_eq_zero_iff.1 h
      tauto
    exact (SignType.supervaluation_eq_zero_iff ..).2 ⟨hex.2 hs, _, hk3, ha⟩
  · exact (SignType.supervaluation_eq_neg_one_iff ..).2 ⟨⟨_, hk3⟩,
      fun c hc hq' ↦ (supervaluation_eq_neg_one_iff.1 h).1 (hex.1 ⟨c, hc, hq'⟩)⟩
  · exact (SignType.supervaluation_eq_one_iff ..).2 (hall.2 (supervaluation_eq_one_iff.1 h).2)

/-- The outer negation of the quantifier negates the per-boy supervaluation. -/
theorem pointwise_compl : pointwise qᶜ d = -pointwise q d :=
  SignType.supervaluation_not _ ⟨_, List.mem_toFinset.2 (resolve_mem_resolutions .k3 d)⟩

/-- Under a scope-antitone quantifier, likewise. -/
theorem pointwise_eq_supervaluation_of_scopeAntitone (hq : q.ScopeAntitone) :
    pointwise q d = supervaluation q d := by
  have := pointwise_eq_supervaluation_of_scopeMonotone (d := d) hq.compl
  rwa [pointwise_compl, supervaluation_compl, neg_involutive.injective.eq_iff] at this

variable {c : List Bool}

/-- A resolution of a display puts in the scope every boy whose cell is true and some of those
whose cell is a gap. -/
theorem count_true_mem_resolutions (hc : c ∈ resolutions d) :
    d.count 1 ≤ c.count true ∧ c.count true ≤ d.count 1 + d.count 0 := by
  have h := List.forall₂_map_right_iff.1 (List.mem_sections.1 hc)
  clear hc
  induction h with
  | nil => simp
  | @cons b v c d hb _ ih =>
    rcases (by decide : ∀ v : SignType, v = 0 ∨ v = -1 ∨ v = 1) v with rfl | rfl | rfl <;>
      cases b <;> simp_all <;> omega

/-- Every number between the boys whose cell is true and those whose cell is not false is the
number some resolution puts in the scope. -/
theorem exists_mem_resolutions_count_true {k : ℕ} (h₁ : d.count 1 ≤ k)
    (h₂ : k ≤ d.count 1 + d.count 0) : ∃ c ∈ resolutions d, c.count true = k := by
  induction d generalizing k with
  | nil => exact ⟨[], by simp [resolutions], by simp_all⟩
  | cons v d ih =>
    have hcons (b : Bool) (hb : b ∈ [decide (0 ≤ v), decide (v = 1)]) {c : List Bool}
        (hc : c ∈ resolutions d) : b :: c ∈ resolutions (v :: d) :=
      List.mem_sections.2 (.cons hb (List.mem_sections.1 hc))
    rcases (by decide : ∀ v : SignType, v = 0 ∨ v = -1 ∨ v = 1) v with rfl | rfl | rfl <;>
      simp only [List.count_cons] at h₁ h₂ <;> norm_num at h₁ h₂
    · by_cases hk : k ≤ d.count 1 + d.count 0
      · obtain ⟨c, hc, rfl⟩ := ih (by omega) hk
        exact ⟨false :: c, hcons false (by simp) hc, by simp⟩
      · obtain ⟨c, hc, hck⟩ := ih (k := k - 1) (by omega) (by omega)
        exact ⟨true :: c, hcons true (by simp) hc, by simp [hck]; omega⟩
    · obtain ⟨c, hc, rfl⟩ := ih h₁ h₂
      exact ⟨false :: c, hcons false (by simp) hc, by simp⟩
    · obtain ⟨c, hc, hck⟩ := ih (k := k - 1) (by omega) (by omega)
      exact ⟨true :: c, hcons true (by simp) hc, by simp [hck]; omega⟩

/-- Under a cardinal quantifier the per-boy supervaluation is true when every number between the
true and the non-false cells is in the quantifier's set. -/
theorem pointwise_cardinal_eq_one_iff {s : Set ℕ} [DecidablePred (· ∈ s)] :
    pointwise (NumberTree.cardinal s) d = 1 ↔
      ∀ k, d.count 1 ≤ k → k ≤ d.count 1 + d.count 0 → k ∈ s := by
  rw [pointwise, SignType.supervaluation_eq_one_iff]
  refine ⟨fun h k h₁ h₂ ↦ ?_, fun h c hc ↦ ?_⟩
  · obtain ⟨c, hc, rfl⟩ := exists_mem_resolutions_count_true h₁ h₂
    exact h c (List.mem_toFinset.2 hc)
  · have := count_true_mem_resolutions (List.mem_toFinset.1 hc)
    exact h _ this.1 this.2

/-- Under a cardinal quantifier the per-boy supervaluation is false when no number between the
true and the non-false cells is in the quantifier's set. -/
theorem pointwise_cardinal_eq_neg_one_iff {s : Set ℕ} [DecidablePred (· ∈ s)] :
    pointwise (NumberTree.cardinal s) d = -1 ↔
      ∀ k, d.count 1 ≤ k → k ≤ d.count 1 + d.count 0 → k ∉ s := by
  rw [pointwise, SignType.supervaluation_eq_neg_one_iff]
  refine ⟨fun h k h₁ h₂ ↦ ?_, fun h ↦ ⟨⟨_, List.mem_toFinset.2 (resolve_mem_resolutions .k3 d)⟩,
    fun c hc ↦ ?_⟩⟩
  · obtain ⟨c, hc, rfl⟩ := exists_mem_resolutions_count_true h₁ h₂
    exact h.2 c (List.mem_toFinset.2 hc)
  · have := count_true_mem_resolutions (List.mem_toFinset.1 hc)
    exact h _ this.1 this.2

/-- A display without gaps, read off a resolution, has that resolution alone. -/
theorem mem_resolutions_map_ofProp {c' : List Bool} :
    c' ∈ resolutions (c.map fun b : Bool ↦ SignType.ofProp b) ↔ c' = c := by
  rw [resolutions, List.map_map, List.mem_sections, List.forall₂_map_right_iff]
  constructor
  · intro h
    exact List.forall₂_eq_eq_eq ▸ h.imp fun b b' hb ↦ by cases b' <;> simp_all
  · rintro rfl
    exact List.forall₂_same.2 fun b _ ↦ by cases b <;> simp

/-- The per-boy supervaluation of a display without gaps is the quantifier's value at it. -/
theorem pointwise_map_ofProp :
    pointwise q (c.map fun b : Bool ↦ SignType.ofProp b) = SignType.ofProp (holds q c) := by
  have : (resolutions (c.map fun b : Bool ↦ SignType.ofProp b)).toFinset = {c} := by
    ext c'; simp [mem_resolutions_map_ofProp]
  rw [pointwise, this, SignType.supervaluation_singleton]

end Pointwise

/-! ### The experiments -/

/-- The number tree of each environment; sentential negation is the outer negation of the
unembedded sentence over its one cell. -/
def Embedding.tree : Embedding → NumberTree
  | .unembedded => NumberTree.all
  | .negation => NumberTree.notAll
  | .all => NumberTree.all
  | .no => NumberTree.no
  | .exactly => NumberTree.cardinal {numeral}

instance : (e : Embedding) → DecidableRel e.tree
  | .unembedded | .all => inferInstanceAs (DecidableRel NumberTree.all)
  | .negation => inferInstanceAs (DecidableRel NumberTree.notAll)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .exactly => inferInstanceAs (DecidableRel (NumberTree.cardinal {2}))

/-- Negation and *no* are downward entailing; the other environments are not. -/
instance : (e : Embedding) → Decidable e.tree.ScopeAntitone
  | .unembedded | .all => isFalse fun h ↦ Nat.one_ne_zero (h 0 0 rfl)
  | .negation => isTrue NumberTree.scopeAntitone_notAll
  | .no => isTrue NumberTree.scopeAntitone_no
  | .exactly => isFalse fun h ↦ by simpa [Embedding.tree, numeral] using h 0 1

/-- The display of an item, each cell's trivalent value. -/
def Item.display (i : Item) : Display := i.cells.map cell

/-- The designed value of the negated sentence swaps TRUE and FALSE. -/
def Condition.neg : Condition → Condition
  | .clearlyTrue => .clearlyFalse
  | .clearlyFalse => .clearlyTrue
  | c => c

/-- The E-neg items are the E-∅ displays judged with the negated sentence. -/
def negationItems : List Item :=
  (items.filter (·.embedding = .unembedded)).map fun i ↦
    { i with embedding := .negation, condition := i.condition.neg }

/-- The items judged in the experiments, Table 13's and the E-neg ones. -/
def tested : List Item := items ++ negationItems

/-- The weak variant of the sentence, which the strong one entails, is the some-substituted
reading, or under a downward-entailing scope the all-substituted one. -/
def weak (e : Embedding) (d : Display) : Prop :=
  if e.tree.ScopeAntitone then allReading e.tree d else someReading e.tree d

/-- The strong variant of the sentence. -/
def strong (e : Embedding) (d : Display) : Prop :=
  if e.tree.ScopeAntitone then someReading e.tree d else allReading e.tree d

instance (e : Embedding) (d : Display) : Decidable (weak e d) := by
  unfold weak; infer_instance

instance (e : Embedding) (d : Display) : Decidable (strong e d) := by
  unfold strong; infer_instance

/-- The GAP? item 5599 of Table 13, whose two full cells §3.3.2's description of the GAP? items
excludes. -/
def misprinted : Item := ⟨.exactly, .gapQ, [5, 5, 9, 9], .used⟩

/-- The item is printed in Table 13. -/
theorem misprinted_mem : misprinted ∈ items := by decide

/-- The item realizes the GAP?? pattern, its all-variant true and its some-variant false. -/
theorem misprinted_gapQQ :
    ¬ weak .exactly misprinted.display ∧ strong .exactly misprinted.display := by
  decide

/-- Every tested item realizes its condition by §3's principle, read with the entailment
direction of its scope, the weak variant holding in the TRUE and GAP conditions and the strong one
in the TRUE and GAP?? conditions. -/
theorem items_variants : ∀ i ∈ tested, i.status ≠ .faulty → i ≠ misprinted →
    (weak i.embedding i.display ↔ i.condition ∈ [.clearlyTrue, .gap]) ∧
      (strong i.embedding i.display ↔ i.condition ∈ [.clearlyTrue, .gapQQ]) := by
  decide

/-- Because of the coding error of §3.2.4, the faulty E-no items, coded FALSE, realize the GAP
pattern. -/
theorem faulty_items : ∀ i ∈ items, i.status = .faulty →
    weak i.embedding i.display ∧ ¬ strong i.embedding i.display := by
  decide

/-- A test is discounted when it is one of the A2 and B2 tests of *no*, whose sentences lacked
negative inversion (fn 10) and were plausibly read with an unbound definite (fn 14). -/
def GapTest.Discounted (t : GapTest) : Prop := t.experiment ∈ [.a2, .b2] ∧ t.embedding = .no

instance (t : GapTest) : Decidable t.Discounted := inferInstanceAs (Decidable (_ ∧ _))

/-- Table 2 found a gap in every GAP and GAP?? test and in no GAP? test, except in the discounted
tests. -/
theorem found_iff : ∀ t ∈ gapTests, (t.found = .yes ↔ t.condition ≠ .gapQ) ↔ ¬ t.Discounted := by
  decide

/-- Table 2 tests only the gap conditions. -/
theorem gapTests_condition : ∀ t ∈ gapTests, t.condition ∈ [.gap, .gapQ, .gapQQ] := by decide

/-- The supervaluation is true exactly on the variants' agreement in truth. -/
theorem supervaluation_eq_one_iff_weak (e : Embedding) (d : Display) :
    supervaluation e.tree d = 1 ↔ weak e d ∧ strong e d := by
  unfold weak strong
  split_ifs <;> simp [supervaluation_eq_one_iff, and_comm]

/-- The supervaluation gaps exactly where the variants differ. -/
theorem supervaluation_eq_zero_iff_weak (e : Embedding) (d : Display) :
    supervaluation e.tree d = 0 ↔ ¬ (weak e d ↔ strong e d) := by
  unfold weak strong
  split_ifs <;> simp [supervaluation_eq_zero_iff, Iff.comm]

/-- The supervaluation is true exactly on the items designed true. -/
theorem supervaluation_eq_one_iff_condition : ∀ i ∈ tested, i.status ≠ .faulty →
    i ≠ misprinted → (supervaluation i.embedding.tree i.display = 1 ↔
      i.condition = .clearlyTrue) := by
  intro i hi hs hm
  obtain ⟨h₁, h₂⟩ := items_variants i hi hs hm
  rw [supervaluation_eq_one_iff_weak, h₁, h₂]
  cases i.condition <;> simp

/-- The supervaluation gaps on an item exactly when its environment and condition were found to
gap, outside the discounted tests. -/
theorem supervaluation_eq_zero_iff_found : ∀ i ∈ tested, i.status ≠ .faulty → i ≠ misprinted →
    ∀ t ∈ gapTests, ¬ t.Discounted → t.embedding = i.embedding → t.condition = i.condition →
      (supervaluation i.embedding.tree i.display = 0 ↔ t.found = .yes) := by
  intro i hi hs hm t ht hd _ hc
  obtain ⟨h₁, h₂⟩ := items_variants i hi hs hm
  have hg := gapTests_condition t ht
  rw [supervaluation_eq_zero_iff_weak, h₁, h₂, (found_iff t ht).2 hd, hc]
  rw [hc] at hg
  revert hg
  cases i.condition <;> simp

/-- The literal-against-global construal misfits exactly the GAP items under a downward-entailing
scope, sentential negation and *no*, and the GAP?? items, where the all-variant is true and the
some-variant false (§6.1.3). -/
theorem globalConstrual_misfit_iff : ∀ i ∈ tested, i.status ≠ .faulty → i ≠ misprinted →
    ∀ t ∈ gapTests, ¬ t.Discounted → t.embedding = i.embedding → t.condition = i.condition →
      (¬ (globalConstrual i.embedding.tree i.display = 0 ↔ t.found = .yes) ↔
        (i.embedding.tree.ScopeAntitone ∧ i.condition = .gap) ∨ i.condition = .gapQQ) := by
  decide

/-- Universal projection predicts a presupposition failure on a FALSE item of *all*, where the
sentence was judged false as soon as one cell has no target symbols, the argument from (42). -/
theorem universalPresupposition_false_item :
    ∃ i ∈ items, i.embedding = .all ∧ i.condition = .clearlyFalse ∧
      universalPresupposition i.embedding.tree i.display = 0 := by
  decide

/-- The per-boy supervaluation departs from the two-candidate one on exactly the GAP? items. -/
theorem pointwise_ne_iff : ∀ i ∈ tested, i.status ≠ .faulty → i ≠ misprinted →
    (pointwise i.embedding.tree i.display ≠ supervaluation i.embedding.tree i.display ↔
      i.condition = .gapQ) := by
  decide

/-- The at-least reading of *exactly 2* that §3.4 discusses. -/
def atLeastTwo : NumberTree := NumberTree.cardinal {b | 2 ≤ b}

instance : DecidableRel atLeastTwo := fun _ b ↦ inferInstanceAs (Decidable (2 ≤ b))

/-- On the at-least reading the GAP? items are gap items. -/
theorem atLeastTwo_gapQ : ∀ i ∈ items, i.condition = .gapQ → i ≠ misprinted →
    supervaluation atLeastTwo i.display = 0 := by
  decide

/-- On the at-least reading the FALSE items of *exactly* with three or more full cells are true,
the items with elevated true responses in Fig. 10. -/
theorem atLeastTwo_false : ∀ i ∈ items, i.embedding = .exactly → i.condition = .clearlyFalse →
    (supervaluation atLeastTwo i.display = 1 ↔ 3 ≤ i.cells.count 9) := by
  decide

/-- A teacher's cell in a situation of Table 12. -/
def Share.value : Share → SignType
  | .all => 1
  | .half => 0
  | .none => (-1)

/-- The display of a situation of Table 12, Bill's, Mary's and Sue's cells. -/
def Situation.display (s : Situation) : Display := [s.bill, s.mary, s.sue].map Share.value

/-- Table 12 follows from its situations. The literal and locally exhaustified parses hold as its
corresponding conditions require, the (si2) and (si4) construals, the supervaluation, gap exactly
where a gap was found, and the (si1) and (si3) construals miss the GAP?? situation. -/
theorem situations_variants : ∀ s ∈ situations,
    (someReading Embedding.exactly.tree s.display ↔ s.condition ∈ [.clearlyTrue, .gap]) ∧
      (allReading Embedding.exactly.tree s.display ↔ s.condition ∈ [.clearlyTrue, .gapQQ]) ∧
      (supervaluation Embedding.exactly.tree s.display = 0 ↔ s.found = .yes) ∧
      (globalConstrual Embedding.exactly.tree s.display = 0 ↔ s.condition = .gap) := by
  decide

end KrizChemla2015
