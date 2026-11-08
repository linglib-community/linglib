module

public import Linglib.Data.Examples.KrizChemla2015
public import Linglib.Data.Statistics.KrizChemla2015
public import Linglib.Logic.Trivalent.Knowledge
public import Linglib.Logic.Trivalent.Supervaluation
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

## Implementation notes

The stimuli and findings are the tables of `Data/Statistics/KrizChemla2015`. The E-neg tests reuse
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
abbrev Display := List Trivalent

/-- A cell in which `n` of the nine objects are found or target-colored has the value of the
bare plural over the nine, true when all are, false when none are, and a gap otherwise. -/
def cell (n : ℕ) : Trivalent :=
  Homogeneity.barePlural (fun j m ↦ j < m) (Finset.range 9) n

theorem designated_k3_cell (n : ℕ) : cell n = .true ↔ 9 ≤ n := by
  rw [cell, Homogeneity.barePlural, Trivalent.supervaluation_eq_true_iff]
  exact ⟨fun h ↦ h 8 (by simp), fun h j hj ↦ by simp at hj; omega⟩

theorem designated_lp_cell (n : ℕ) : .undefined ≤ cell n ↔ 1 ≤ n := by
  rw [Trivalent.undefined_le_iff_ne_false, Ne, cell, Homogeneity.barePlural,
    Trivalent.supervaluation_eq_false_iff]
  simp only [Finset.mem_range, not_and, not_forall, not_not, exists_prop]
  exact ⟨fun h ↦ by obtain ⟨j, -, hj⟩ := h ⟨0, by simp⟩; omega,
    fun h _ ↦ ⟨0, by omega, h⟩⟩

/-- A number tree holds of a resolution according to how many boys it resolves out of and into
the scope. -/
def holds (q : NumberTree) (c : List Bool) : Prop := q (c.count Bool.false) (c.count Bool.true)

instance (q : NumberTree) [DecidableRel q] (c : List Bool) : Decidable (holds q c) :=
  inferInstanceAs (Decidable (q _ _))

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

theorem resolve_map_compl (δ : Designation) (d : Display) :
    resolve δ (d.map compl) = (resolve δ.dual d).map not := by
  simp only [resolve, List.map_map]
  refine List.map_congr_left fun v _ ↦ ?_
  have := Trivalent.Designation.dual_threshold_le_compl_iff δ.dual v
  rw [Trivalent.Designation.dual_dual] at this
  simp only [Function.comp_apply, this, decide_not]

/-- The resolutions of a display that choose a designation standard boy by boy. -/
def resolutions (d : Display) : List (List Bool) :=
  (d.map fun v ↦ [decide (.undefined ≤ v), decide (v = .true)]).sections

theorem resolve_mem_resolutions (δ : Designation) (d : Display) :
    resolve δ d ∈ resolutions d := by
  refine List.mem_sections.2 <| List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
    List.forall₂_same.2 fun v _ ↦ ?_
  cases δ <;> cases v <;> decide

theorem resolve_le_of_mem_resolutions {d : Display} {c : List Bool} (hc : c ∈ resolutions d) :
    List.Forall₂ (· ≤ ·) (resolve .k3 d) c ∧ List.Forall₂ (· ≤ ·) c (resolve .lp d) := by
  have h := List.forall₂_map_right_iff.1 (List.mem_sections.1 hc)
  refine ⟨List.forall₂_map_left_iff.2 (h.flip.imp fun v b hb ↦ ?_),
    List.forall₂_map_right_iff.2 (h.imp fun b v hb ↦ ?_)⟩ <;>
  cases v <;> cases b <;> simp_all +decide

theorem resolve_lp_eq_resolve_k3 {d : Display} (h : ∀ v ∈ d, v ≠ .undefined) :
    resolve .lp d = resolve .k3 d :=
  List.map_congr_left fun v hv ↦ by cases v <;> first | rfl | exact absurd rfl (h _ hv)

theorem holds_of_forall₂_le {q : NumberTree} (hq : q.ScopeMonotone) {c c' : List Bool}
    (h : List.Forall₂ (· ≤ ·) c c') (hc : holds q c) : holds q c' := by
  obtain ⟨j, h₁, h₂⟩ : ∃ j, c'.count Bool.true = c.count Bool.true + j ∧
      c.count Bool.false = c'.count Bool.false + j := by
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

theorem reading_all (δ : Designation) : reading NumberTree.all d δ ↔ ∀ v ∈ d, δ.threshold ≤ v := by
  simp [reading, holds, resolve, NumberTree.all, List.count_eq_zero]

theorem reading_no (δ : Designation) : reading NumberTree.no d δ ↔ ∀ v ∈ d, ¬ δ.threshold ≤ v := by
  simp [reading, holds, resolve, NumberTree.no, List.count_eq_zero]

theorem reading_map_compl (δ : Designation) :
    reading q (d.map compl) δ ↔ reading q.innerNeg d δ.dual := by
  rw [reading, reading, resolve_map_compl, holds_map_not]

theorem someReading_iff_allReading (h : ∀ v ∈ d, v ≠ .undefined) :
    someReading q d ↔ allReading q d := by
  rw [someReading, allReading, reading, reading, resolve_lp_eq_resolve_k3 h]

theorem allReading_imp_someReading (hq : q.ScopeMonotone) : allReading q d → someReading q d :=
  holds_of_forall₂_le hq (resolve_le_of_mem_resolutions (resolve_mem_resolutions .lp d)).1

theorem someReading_imp_allReading (hq : q.ScopeAntitone) : someReading q d → allReading q d :=
  fun hs ↦ not_not.1 fun ha ↦ allReading_imp_someReading (q := qᶜ) hq.compl ha hs

end Readings

/-! ### Two-component verdicts -/

/-- The verdict from two meaning components is the supervaluation over the pair, clearly true
when both hold, clearly false when neither does, and a truth-value gap when they conflict. -/
def gapValue (p q : Prop) [Decidable p] [Decidable q] : Trivalent :=
  Trivalent.supervaluation Finset.univ fun b : Bool ↦ if b then p else q

section GapValue

variable {p q : Prop} [Decidable p] [Decidable q]

@[simp] theorem gapValue_eq_true_iff : gapValue p q = .true ↔ p ∧ q := by
  simp [gapValue, Trivalent.supervaluation_eq_true_iff, Bool.forall_bool, and_comm]

@[simp] theorem gapValue_eq_false_iff : gapValue p q = .false ↔ ¬ p ∧ ¬ q := by
  simp [gapValue, Trivalent.supervaluation_eq_false_iff, Bool.forall_bool, and_comm]

@[simp] theorem gapValue_eq_undefined_iff : gapValue p q = .undefined ↔ ¬ (p ↔ q) := by
  simp only [gapValue, Trivalent.supervaluation_eq_undefined_iff, Finset.mem_univ, true_and,
    Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true]
  tauto

theorem gapValue_ne_undefined (h : p ↔ q) : gapValue p q ≠ .undefined := by simp [h]

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
theorem globalExh_iff_of_scopeAntitone (hq : q.ScopeAntitone) :
    globalExh q d ↔ someReading q d :=
  ⟨And.left, fun h ↦ ⟨h, someReading_imp_allReading hq h⟩⟩

end GlobalExh

section Approaches

variable (q : NumberTree) [DecidableRel q] (d : Display)

/-- The supervaluation of [spector-2013b] (§6.2) makes the sentence true when it is true however
the definite is resolved, existentially or universally, and false when it is false however it is
resolved. -/
def supervaluation : Trivalent := Trivalent.supervaluation Finset.univ (reading q d)

instance : Decidable (globalExh q d) := inferInstanceAs (Decidable (_ ∧ _))

/-- The implicature construals (si1) and (si3) of §6.1.2, after [magri-2009]'s oddness condition,
put a gap where the literal and the globally exhaustified meaning conflict. -/
def globalConstrual : Trivalent := gapValue (someReading q d) (globalExh q d)

/-- Homogeneity as a presupposition projecting universally from the quantifier's scope, after
[schwarzschild-1994], [lobner-2000] and [gajewski-2005] as assessed in §6.3, is the presupposition
that every cell is homogeneous weakly conjoined with the universal-force assertion. The
presupposition is the ∂ of [beaver-krahmer-2001], the join `p ⊔ undefined` with the gap. -/
def universalPresupposition : Trivalent :=
  (Trivalent.ofProp (∀ v ∈ d, v ≠ .undefined) ⊔ .undefined).meetWeak (.ofProp (allReading q d))

/-- Supervaluation over the resolutions that treat the partial cells one by one, a richer
candidate set than the existential and universal readings, of the kind §6.2 says predicts a gap
in the gap? condition; footnote 19 notes that quantified trivalent logics make the same
prediction. -/
def pointwise : Trivalent := Trivalent.supervaluation (resolutions d).toFinset (holds q)

variable {q d}

theorem supervaluation_eq_designations :
    supervaluation q d = Trivalent.supervaluation Finset.univ (reading q d) :=
  rfl

private theorem forall_designation {P : Designation → Prop} : (∀ δ, P δ) ↔ P .lp ∧ P .k3 :=
  ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨h₁, h₂⟩ δ ↦ by cases δ <;> assumption⟩

theorem supervaluation_eq_true_iff :
    supervaluation q d = .true ↔ someReading q d ∧ allReading q d := by
  simp [supervaluation, Trivalent.supervaluation_eq_true_iff, forall_designation]

theorem supervaluation_eq_false_iff :
    supervaluation q d = .false ↔ ¬ someReading q d ∧ ¬ allReading q d := by
  simp [supervaluation, Trivalent.supervaluation_eq_false_iff, forall_designation]

theorem supervaluation_eq_undefined_iff :
    supervaluation q d = .undefined ↔ ¬ (someReading q d ↔ allReading q d) := by
  have h {P : Designation → Prop} : (∃ δ, P δ) ↔ P .lp ∨ P .k3 :=
    ⟨fun ⟨δ, h⟩ ↦ by cases δ <;> tauto, fun h ↦ h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩
  simp only [supervaluation, Trivalent.supervaluation_eq_undefined_iff, Finset.mem_univ, true_and,
    h]
  tauto

theorem supervaluation_ne_undefined (h : ∀ v ∈ d, v ≠ .undefined) :
    supervaluation q d ≠ .undefined := by
  simp [supervaluation_eq_undefined_iff, someReading_iff_allReading h]

theorem supervaluation_map_compl :
    supervaluation q (d.map compl) = supervaluation q.innerNeg d := by
  have h : (Finset.univ : Finset Designation).image Designation.dual = Finset.univ := by decide
  rw [supervaluation, supervaluation]
  conv_rhs => rw [← h, Trivalent.supervaluation_image]
  exact Trivalent.supervaluation_congr fun δ _ ↦ reading_map_compl δ

theorem supervaluation_compl : supervaluation qᶜ d = (supervaluation q d)ᶜ := by
  rw [supervaluation, supervaluation, ← Trivalent.supervaluation_not _ Finset.univ_nonempty]
  rfl

theorem globalConstrual_eq_undefined_iff :
    globalConstrual q d = .undefined ↔ someReading q d ∧ ¬ allReading q d := by
  rw [globalConstrual, gapValue_eq_undefined_iff, globalExh]
  tauto

theorem globalConstrual_ne_supervaluation_iff :
    globalConstrual q d ≠ supervaluation q d ↔ ¬ someReading q d ∧ allReading q d := by
  rcases h₁ : globalConstrual q d with _ | _ | _ <;>
    rcases h₂ : supervaluation q d with _ | _ | _ <;>
    simp_all [globalConstrual, globalExh, supervaluation_eq_true_iff, supervaluation_eq_false_iff,
      supervaluation_eq_undefined_iff]

-- §6.1.3
theorem globalConstrual_eq_supervaluation_of_scopeMonotone (hq : q.ScopeMonotone) :
    globalConstrual q d = supervaluation q d :=
  not_not.1 fun h ↦ (globalConstrual_ne_supervaluation_iff.1 h).elim fun hs ha ↦
    hs (allReading_imp_someReading hq ha)

theorem globalConstrual_ne_undefined_of_scopeAntitone (hq : q.ScopeAntitone) :
    globalConstrual q d ≠ .undefined :=
  gapValue_ne_undefined (globalExh_iff_of_scopeAntitone hq).symm

theorem universalPresupposition_eq_undefined_iff :
    universalPresupposition q d = .undefined ↔ .undefined ∈ d := by
  rw [universalPresupposition, Trivalent.meetWeak_eq_undefined_iff]
  simp only [Trivalent.sup_undefined_eq_undefined_iff, Trivalent.ofProp_ne_undefined, or_false, Ne,
    Trivalent.ofProp_eq_true_iff, not_forall, exists_prop, not_not, exists_eq_right]

end Approaches

/-! ### Negation and the wide-scope parse (§6.1.3) -/

theorem supervaluation_all_singleton (v : Trivalent) : supervaluation NumberTree.all [v] = v := by
  cases v <;> decide

theorem globalConstrual_notAll_ne_undefined (v : Trivalent) :
    globalConstrual NumberTree.notAll [v] ≠ .undefined :=
  globalConstrual_ne_undefined_of_scopeAntitone NumberTree.scopeAntitone_notAll

/-- On the wide-scope parse (35), the literal-against-global construal of *the shapes are not green*
is the supervaluation of its narrow-scope negation. -/
theorem globalConstrual_wideScope (v : Trivalent) :
    globalConstrual NumberTree.all [vᶜ] = supervaluation NumberTree.notAll [v] := by
  rw [globalConstrual_eq_supervaluation_of_scopeMonotone NumberTree.scopeMonotone_all]
  exact supervaluation_map_compl (q := NumberTree.all) (d := [v]) |>.trans
    (by cases v <;> decide)

/-! ### Global exhaustification is double strengthening -/

section Strengthening

open Magri2014 (strengthened primalMates primal)

variable (q : NumberTree) (n : ℕ)

/-- The displays of `n` boys on which the some-substituted reading holds, the weak pole. -/
def weakPole : Set (Fin n → Trivalent) := {w | someReading q (List.ofFn w)}

/-- The displays of `n` boys on which the all-substituted reading holds, the strong pole. -/
def strongPole : Set (Fin n → Trivalent) := {w | allReading q (List.ofFn w)}

variable {q n}

/-- Double strengthening ([magri-2014]) yields `globalExh`, (30) and (39), provided the strong pole
is weaker or the two poles are compatible. -/
theorem globalExh_iff_mem_strengthened
    (h : weakPole q n ⊆ strongPole q n ∨ (weakPole q n ∩ strongPole q n).Nonempty)
    (w : Fin n → Trivalent) :
    globalExh q (List.ofFn w) ↔
      w ∈ strengthened primalMates (primal (weakPole q n) (strongPole q n)) .mystery := by
  rcases (weakPole q n \ strongPole q n).eq_empty_or_nonempty with h₀ | h₀
  · have hsub := Set.sdiff_eq_empty.1 h₀
    rw [Magri2014.strengthened_primal_mystery_of_subset hsub]
    exact ⟨And.left, fun h ↦ ⟨h, hsub h⟩⟩
  · have h₂ := h.resolve_left fun hsub ↦ by simp [Set.sdiff_eq_empty.2 hsub] at h₀
    rw [Magri2014.strengthened_primal_mystery h₀ h₂]
    rfl

end Strengthening

/-! ### Per-boy resolutions -/

section Pointwise

variable {q : NumberTree} [DecidableRel q] {d : Display}

theorem supervaluation_eq_image :
    supervaluation q d =
      Trivalent.supervaluation (Finset.univ.image fun δ ↦ resolve δ d) (holds q) := by
  rw [supervaluation, Trivalent.supervaluation_image]
  rfl

open Bilattice in
theorem pointwise_kLE_supervaluation : pointwise q d ≤ₖ supervaluation q d := by
  rw [supervaluation_eq_image]
  refine Trivalent.supervaluation_kLE_supervaluation _ (fun c hc ↦ ?_)
    (Finset.univ_nonempty.image _)
  obtain ⟨δ, -, rfl⟩ := Finset.mem_image.1 hc
  exact List.mem_toFinset.2 (resolve_mem_resolutions δ d)

theorem pointwise_eq_supervaluation_of_scopeMonotone (hq : q.ScopeMonotone) :
    pointwise q d = supervaluation q d := by
  rw [pointwise, Trivalent.supervaluation_eq_of_between
      (List.mem_toFinset.2 (resolve_mem_resolutions .k3 d))
      (List.mem_toFinset.2 (resolve_mem_resolutions .lp d)) fun _ hc ↦
        ⟨holds_of_forall₂_le hq (resolve_le_of_mem_resolutions (List.mem_toFinset.1 hc)).1,
          holds_of_forall₂_le hq (resolve_le_of_mem_resolutions (List.mem_toFinset.1 hc)).2⟩,
    supervaluation_eq_image,
    show (Finset.univ : Finset Designation) = {.k3, .lp} by decide, Finset.image_insert,
    Finset.image_singleton]

theorem pointwise_compl : pointwise qᶜ d = (pointwise q d)ᶜ :=
  Trivalent.supervaluation_not _ ⟨_, List.mem_toFinset.2 (resolve_mem_resolutions .k3 d)⟩

theorem pointwise_eq_supervaluation_of_scopeAntitone (hq : q.ScopeAntitone) :
    pointwise q d = supervaluation q d := by
  have := pointwise_eq_supervaluation_of_scopeMonotone (d := d) hq.compl
  rwa [pointwise_compl, supervaluation_compl, InvolutiveCompl.compl_inj_iff] at this

variable {c : List Bool}

theorem count_true_mem_resolutions (hc : c ∈ resolutions d) :
    d.count .true ≤ c.count Bool.true ∧ c.count Bool.true ≤ d.count .true + d.count .undefined := by
  have h := List.forall₂_map_right_iff.1 (List.mem_sections.1 hc)
  clear hc
  induction h with
  | nil => simp
  | @cons b v c d hb _ ih =>
    cases v <;> cases b <;> simp_all <;> omega

theorem exists_mem_resolutions_count_true {k : ℕ} (h₁ : d.count .true ≤ k)
    (h₂ : k ≤ d.count .true + d.count .undefined) : ∃ c ∈ resolutions d, c.count Bool.true = k := by
  induction d generalizing k with
  | nil => exact ⟨[], by simp [resolutions], by simp_all⟩
  | cons v d ih =>
    have hcons (b : Bool) (hb : b ∈ [decide (.undefined ≤ v), decide (v = .true)]) {c : List Bool}
        (hc : c ∈ resolutions d) : b :: c ∈ resolutions (v :: d) :=
      List.mem_sections.2 (.cons hb (List.mem_sections.1 hc))
    cases v <;> simp only [List.count_cons] at h₁ h₂ <;> norm_num at h₁ h₂
    · obtain ⟨c, hc, rfl⟩ := ih h₁ h₂
      exact ⟨Bool.false :: c, hcons Bool.false (by simp) hc, by simp⟩
    · by_cases hk : k ≤ d.count .true + d.count .undefined
      · obtain ⟨c, hc, rfl⟩ := ih (by omega) hk
        exact ⟨Bool.false :: c, hcons Bool.false (by simp) hc, by simp⟩
      · obtain ⟨c, hc, hck⟩ := ih (k := k - 1) (by omega) (by omega)
        exact ⟨Bool.true :: c, hcons Bool.true (by simp) hc, by simp [hck]; omega⟩
    · obtain ⟨c, hc, hck⟩ := ih (k := k - 1) (by omega) (by omega)
      exact ⟨Bool.true :: c, hcons Bool.true (by simp) hc, by simp [hck]; omega⟩

theorem pointwise_cardinal_eq_true_iff {s : Set ℕ} [DecidablePred (· ∈ s)] :
    pointwise (NumberTree.cardinal s) d = .true ↔
      ∀ k, d.count .true ≤ k → k ≤ d.count .true + d.count .undefined → k ∈ s := by
  rw [pointwise, Trivalent.supervaluation_eq_true_iff]
  refine ⟨fun h k h₁ h₂ ↦ ?_, fun h c hc ↦ ?_⟩
  · obtain ⟨c, hc, rfl⟩ := exists_mem_resolutions_count_true h₁ h₂
    exact h c (List.mem_toFinset.2 hc)
  · have := count_true_mem_resolutions (List.mem_toFinset.1 hc)
    exact h _ this.1 this.2

theorem pointwise_cardinal_eq_false_iff {s : Set ℕ} [DecidablePred (· ∈ s)] :
    pointwise (NumberTree.cardinal s) d = .false ↔
      ∀ k, d.count .true ≤ k → k ≤ d.count .true + d.count .undefined → k ∉ s := by
  rw [pointwise, Trivalent.supervaluation_eq_false_iff]
  refine ⟨fun h k h₁ h₂ ↦ ?_, fun h ↦ ⟨⟨_, List.mem_toFinset.2 (resolve_mem_resolutions .k3 d)⟩,
    fun c hc ↦ ?_⟩⟩
  · obtain ⟨c, hc, rfl⟩ := exists_mem_resolutions_count_true h₁ h₂
    exact h.2 c (List.mem_toFinset.2 hc)
  · have := count_true_mem_resolutions (List.mem_toFinset.1 hc)
    exact h _ this.1 this.2

theorem mem_resolutions_map_ofProp {c' : List Bool} :
    c' ∈ resolutions (c.map fun b : Bool ↦ Trivalent.ofProp b) ↔ c' = c := by
  rw [resolutions, List.map_map, List.mem_sections, List.forall₂_map_right_iff]
  constructor
  · intro h
    exact List.forall₂_eq_eq_eq ▸ h.imp fun b b' hb ↦ by cases b' <;> simp_all
  · rintro rfl
    exact List.forall₂_same.2 fun b _ ↦ by cases b <;> simp

theorem pointwise_map_ofProp :
    pointwise q (c.map fun b : Bool ↦ Trivalent.ofProp b) = Trivalent.ofProp (holds q c) := by
  have : (resolutions (c.map fun b : Bool ↦ Trivalent.ofProp b)).toFinset = {c} := by
    ext c'; simp [mem_resolutions_map_ofProp]
  rw [pointwise, this, Trivalent.supervaluation_singleton]

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

-- Table 13
theorem misprinted_mem : misprinted ∈ items := by decide

/-- The item realizes the GAP?? pattern, its all-variant true and its some-variant false. -/
theorem misprinted_gapQQ :
    ¬ weak .exactly misprinted.display ∧ strong .exactly misprinted.display := by
  decide

/-- Every tested item realizes its condition by §3's principle, with the weak variant true in TRUE
and GAP and the strong one in TRUE and GAP?? (Table 13). -/
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

-- Table 2
theorem gapTests_condition : ∀ t ∈ gapTests, t.condition ∈ [.gap, .gapQ, .gapQQ] := by decide

theorem supervaluation_eq_true_iff_weak (e : Embedding) (d : Display) :
    supervaluation e.tree d = .true ↔ weak e d ∧ strong e d := by
  unfold weak strong
  split_ifs <;> simp [supervaluation_eq_true_iff, and_comm]

theorem supervaluation_eq_undefined_iff_weak (e : Embedding) (d : Display) :
    supervaluation e.tree d = .undefined ↔ ¬ (weak e d ↔ strong e d) := by
  unfold weak strong
  split_ifs <;> simp [supervaluation_eq_undefined_iff, Iff.comm]

/-- The supervaluation is true exactly on the items designed true. -/
theorem supervaluation_eq_true_iff_condition : ∀ i ∈ tested, i.status ≠ .faulty →
    i ≠ misprinted → (supervaluation i.embedding.tree i.display = .true ↔
      i.condition = .clearlyTrue) := by
  intro i hi hs hm
  obtain ⟨h₁, h₂⟩ := items_variants i hi hs hm
  rw [supervaluation_eq_true_iff_weak, h₁, h₂]
  cases i.condition <;> simp

/-- The supervaluation gaps on an item exactly when its environment and condition were found to
gap, outside the discounted tests. -/
theorem supervaluation_eq_undefined_iff_found : ∀ i ∈ tested, i.status ≠ .faulty → i ≠ misprinted →
    ∀ t ∈ gapTests, ¬ t.Discounted → t.embedding = i.embedding → t.condition = i.condition →
      (supervaluation i.embedding.tree i.display = .undefined ↔ t.found = .yes) := by
  intro i hi hs hm t ht hd _ hc
  obtain ⟨h₁, h₂⟩ := items_variants i hi hs hm
  have hg := gapTests_condition t ht
  rw [supervaluation_eq_undefined_iff_weak, h₁, h₂, (found_iff t ht).2 hd, hc]
  rw [hc] at hg
  revert hg
  cases i.condition <;> simp

/-- The literal-against-global construal misfits exactly the GAP items under sentential negation and
*no*, and the GAP?? items (§6.1.3). -/
theorem globalConstrual_misfit_iff : ∀ i ∈ tested, i.status ≠ .faulty → i ≠ misprinted →
    ∀ t ∈ gapTests, ¬ t.Discounted → t.embedding = i.embedding → t.condition = i.condition →
      (¬ (globalConstrual i.embedding.tree i.display = .undefined ↔ t.found = .yes) ↔
        (i.embedding.tree.ScopeAntitone ∧ i.condition = .gap) ∨ i.condition = .gapQQ) := by
  decide

-- (42)
theorem universalPresupposition_false_item :
    ∃ i ∈ items, i.embedding = .all ∧ i.condition = .clearlyFalse ∧
      universalPresupposition i.embedding.tree i.display = .undefined := by
  decide

/-- The per-boy supervaluation departs from the two-candidate one on exactly the GAP? items. -/
theorem pointwise_ne_iff : ∀ i ∈ tested, i.status ≠ .faulty → i ≠ misprinted →
    (pointwise i.embedding.tree i.display ≠ supervaluation i.embedding.tree i.display ↔
      i.condition = .gapQ) := by
  decide

/-- The at-least reading of *exactly 2* that §3.4 discusses. -/
def atLeastTwo : NumberTree := NumberTree.cardinal {b | 2 ≤ b}

instance : DecidableRel atLeastTwo := fun _ b ↦ inferInstanceAs (Decidable (2 ≤ b))

theorem atLeastTwo_gapQ : ∀ i ∈ items, i.condition = .gapQ → i ≠ misprinted →
    supervaluation atLeastTwo i.display = .undefined := by
  decide

-- Fig. 10
theorem atLeastTwo_false : ∀ i ∈ items, i.embedding = .exactly → i.condition = .clearlyFalse →
    (supervaluation atLeastTwo i.display = .true ↔ 3 ≤ i.cells.count 9) := by
  decide

/-- A teacher's cell in a situation of Table 12. -/
def Share.value : Share → Trivalent
  | .all => .true
  | .half => .undefined
  | .none => (.false)

/-- The display of a situation of Table 12, Bill's, Mary's and Sue's cells. -/
def Situation.display (s : Situation) : Display := [s.bill, s.mary, s.sue].map Share.value

/-- Each reading of Table 12 holds in exactly the situations its condition requires, and the
supervaluation gaps exactly where a gap was found. -/
theorem situations_variants : ∀ s ∈ situations,
    (someReading Embedding.exactly.tree s.display ↔ s.condition ∈ [.clearlyTrue, .gap]) ∧
      (allReading Embedding.exactly.tree s.display ↔ s.condition ∈ [.clearlyTrue, .gapQQ]) ∧
      (supervaluation Embedding.exactly.tree s.display = .undefined ↔ s.found = .yes) ∧
      (globalConstrual Embedding.exactly.tree s.display = .undefined ↔ s.condition = .gap) := by
  decide

end KrizChemla2015
