module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Counterfactual conditionals: three theories

This file defines three theories of counterfactuals, all stated over the closest
antecedent-worlds of a similarity ordering. On the universal theory of Lewis and Kratzer *if p,
would q* is true when every closest `p`-world is a `q`-world. On the selectional theory of
Stalnaker a selection function picks one closest `p`-world and ties are resolved by
supervaluation over the completions of the ordering, so the counterfactual is true when every
closest `p`-world is a `q`-world, false when none is, and indeterminate otherwise. On the
homogeneity theory of von Fintel and Križ the universal assertion carries the presupposition
that the closest `p`-worlds agree on `q`. The three agree whenever the closest antecedent-worlds
agree on the consequent, and part under embedding.

## Main definitions

* `selectionalCounterfactual`: the selectional counterfactual, super-truth over
  the closest antecedent-worlds.
* `superCounterfactual`: Stalnaker's supervaluation over completions.
* `homogeneityCounterfactual`: the homogeneity counterfactual, a trivalent proposition.
* `selectionalMight`: the selectional *might*.

## Main results

* `homogeneityCounterfactual_eq_selectionalCounterfactual`: unembedded, the homogeneity
  counterfactual is the selectional one.
* `superCounterfactual_eq_selectionalCounterfactual`: on a finite, strongly
  centered ordering the supervaluation over completions is the selectional counterfactual.

## References

* [S. Ramotowska, P. Marty, J. Romoli and P. Santorio, *Counterfactuals and quantificational force:
  Experimental evidence for selectional semantics* (2025)][ramotowska-marty-romoli-santorio-2025]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
* [K. von Fintel, *Bare Plurals, Bare Conditionals, and Only* (1997)][von-fintel-1997]
* [M. Križ, *Aspects of Homogeneity in the Semantics of Natural Language* (2015)][kriz-2015]
-/

@[expose] public section


namespace Conditional

section Theories

variable {W : Type*} (ord : W → Preorder W) (p q r : Set W) (w : W)

/-! ### The homogeneity theory

The homogeneity counterfactual is a trivalent proposition. Unembedded it is the selectional
counterfactual, and the two theories part only under embedding, where
[ramotowska-marty-romoli-santorio-2025] test them. -/

open Classical in
/-- The homogeneity counterfactual, which asserts that every closest `p`-world is a `q`-world and
presupposes that the closest `p`-worlds agree on `q`. -/
noncomputable def homogeneityCounterfactual : W → SignType :=
  (closestImp ord p q ∪ closestImp ord p qᶜ).indicator
    fun v ↦ SignType.ofProp (v ∈ closestImp ord p q)

variable {ord p q w}

@[simp] theorem homogeneityCounterfactual_eq_one_iff :
    homogeneityCounterfactual ord p q w = 1 ↔ w ∈ closestImp ord p q := by
  simp +contextual [homogeneityCounterfactual]

@[simp] theorem homogeneityCounterfactual_eq_neg_one_iff :
    homogeneityCounterfactual ord p q w = -1 ↔
      w ∉ closestImp ord p q ∧ w ∈ closestImp ord p qᶜ := by
  simp +contextual [homogeneityCounterfactual, and_comm]

@[simp] theorem homogeneityCounterfactual_eq_zero_iff :
    homogeneityCounterfactual ord p q w = 0 ↔
      w ∉ closestImp ord p q ∧ w ∉ closestImp ord p qᶜ := by
  simp [homogeneityCounterfactual]

theorem support_homogeneityCounterfactual_compl :
    Function.support (homogeneityCounterfactual ord p qᶜ) =
      Function.support (homogeneityCounterfactual ord p q) := by
  ext; simp [and_comm]

theorem homogeneityCounterfactual_compl (h : ((ord w).minimals p).Nonempty) :
    homogeneityCounterfactual ord p qᶜ w = -homogeneityCounterfactual ord p q w := by
  obtain ⟨v, hv⟩ := h
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp [and_comm]) ?_
  rw [SignType.neg_eq_one_iff, homogeneityCounterfactual_eq_one_iff,
    homogeneityCounterfactual_eq_neg_one_iff]
  exact ⟨fun hn ↦ ⟨fun hq ↦ hn hv (hq hv), hn⟩, And.right⟩

/-! ### The selectional theory

The selectional counterfactual is super-truth over the closest antecedent-worlds, each of them
one resolution of the selection function's tie. -/

variable (ord p q w) [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ p)]
  [DecidablePred (· ∈ q)] [DecidablePred (· ∈ r)]

/-- The selectional counterfactual, true when every closest `p`-world is a `q`-world, false when
every one is a `qᶜ`-world, and indeterminate otherwise. -/
def selectionalCounterfactual : SignType :=
  SignType.supervaluation ((ord w).minimals p).toFinset (· ∈ q)

variable {ord p q w}

theorem selectionalCounterfactual_eq_one_iff :
    selectionalCounterfactual ord p q w = 1 ↔ w ∈ closestImp ord p q := by
  simp [selectionalCounterfactual, SignType.supervaluation_eq_one_iff, Set.subset_def]

theorem selectionalCounterfactual_eq_neg_one_iff :
    selectionalCounterfactual ord p q w = -1 ↔
      w ∉ closestImp ord p q ∧ w ∈ closestImp ord p qᶜ := by
  simp only [selectionalCounterfactual, SignType.supervaluation_eq_neg_one_iff,
    Set.toFinset_nonempty, Set.mem_toFinset, mem_closestImp, Set.subset_def, Set.mem_compl_iff]
  exact ⟨fun ⟨⟨v, hv⟩, h⟩ ↦ ⟨fun h' ↦ h v hv (h' v hv), h⟩, fun ⟨hn, h⟩ ↦
    ⟨Set.nonempty_iff_ne_empty.2 fun he ↦ hn fun v hv ↦ absurd hv (he ▸ Set.notMem_empty v), h⟩⟩

theorem selectionalCounterfactual_eq_zero_iff :
    selectionalCounterfactual ord p q w = 0 ↔
      w ∉ closestImp ord p q ∧ w ∉ closestImp ord p qᶜ := by
  simp [selectionalCounterfactual, SignType.supervaluation_eq_zero_iff, Set.not_subset, and_comm]

theorem selectionalCounterfactual_compl (h : ((ord w).minimals p).Nonempty) :
    selectionalCounterfactual ord p qᶜ w = -selectionalCounterfactual ord p q w := by
  simpa [selectionalCounterfactual] using
    SignType.supervaluation_not (· ∈ q) (by simpa using h)

variable (ord p q w)

theorem cem_selectional :
    selectionalCounterfactual ord p q w ⊔ selectionalCounterfactual ord p qᶜ w ≠ -1 := by
  rcases ((ord w).minimals p).eq_empty_or_nonempty with h | h
  · simp [selectionalCounterfactual, h]
  · rw [selectionalCounterfactual_compl h]
    cases selectionalCounterfactual ord p q w <;> decide

theorem homogeneityCounterfactual_eq_selectionalCounterfactual :
    homogeneityCounterfactual ord p q w = selectionalCounterfactual ord p q w :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff
    (by rw [homogeneityCounterfactual_eq_zero_iff, selectionalCounterfactual_eq_zero_iff])
    (by rw [homogeneityCounterfactual_eq_one_iff, selectionalCounterfactual_eq_one_iff])

/-! ### *Might* counterfactuals

[lewis-1973] defines *if p, might q* as *not (if p, would not q)*. Together with Conditional
Excluded Middle that definition makes *might* equivalent to *would*, which Lewis counts against a
semantics validating it. [stalnaker-1981] rejects the definition instead, reading *might* as a
possibility operator over the whole conditional. -/

/-- The selectional *might* holds when the selectional counterfactual is not false. -/
def selectionalMight : Prop := selectionalCounterfactual ord p q w ≠ -1

instance : Decidable (selectionalMight ord p q w) := inferInstanceAs (Decidable (_ ≠ _))

/-- The selectional *might* is weaker than *would*, since with mixed closest worlds *might*
holds while *would* is indeterminate. -/
theorem selectional_might_weaker :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (_ : ∀ w, DecidableRel (ord w).le) (p q : Set (Fin 3))
      (_ : DecidablePred (· ∈ p)) (_ : DecidablePred (· ∈ q)) (w : Fin 3),
      selectionalMight ord p q w ∧ selectionalCounterfactual ord p q w = 0 :=
  ⟨fun _ ↦ ⊥, inferInstance, {1, 2}, {1}, inferInstance,
    inferInstance, 0, by decide, by decide⟩

/-! ### Distribution

Distribution of a counterfactual over a disjunctive consequent fails for the universal theory,
which quantifies over every closest world, and holds for the selectional theory when there is at
most one closest world ([stalnaker-1981]). -/

theorem distribution_selectional (h_unique : ((ord w).minimals p).Subsingleton)
    (h : selectionalCounterfactual ord p (q ∪ r) w = 1) :
    selectionalCounterfactual ord p q w = 1 ∨ selectionalCounterfactual ord p r w = 1 := by
  simp only [selectionalCounterfactual_eq_one_iff, mem_closestImp] at h ⊢
  rcases h_unique.eq_empty_or_singleton with h0 | ⟨v, hv⟩
  · simp [h0]
  · simpa only [hv, Set.singleton_subset_iff, Set.mem_union] using h

theorem distribution_fails_universal :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (p q r : Set (Fin 3)) (w : Fin 3),
      w ∈ closestImp ord p (q ∪ r) ∧ w ∉ closestImp ord p q ∧ w ∉ closestImp ord p r :=
  ⟨fun _ ↦ ⊥, {1, 2}, {1}, {2}, 0, by decide,
    by decide, by decide⟩

end Theories

/-! ### The selectional theory as supervaluation

[stalnaker-1981] supervaluates the [stalnaker-1968] selection conditional over the completions of
a similarity ordering. A conditional is true when every completion makes it true, false when
every one makes it false, and indeterminate otherwise (`superCounterfactual`), which for a single
conditional on a finite, strongly centered ordering is the selectional counterfactual. -/

section Supervaluation

variable {W : Type*} (ord : W → Preorder W) (p q : Set W) (w : W)

/-- The supervaluation of the selection conditional over the completions of a family of
preorders, true when every compatible selection function makes *if p, q* true, false when every
one makes it false, and indeterminate otherwise. -/
noncomputable def superCounterfactual : SignType :=
  open Classical in
  if ∀ s : SelectionFunction W, s.Compatible ord → w ∈ selectionConditional s p q then 1
  else if ∀ s : SelectionFunction W, s.Compatible ord → w ∉ selectionConditional s p q then -1
  else 0

variable {ord p q w} [Fintype W] [∀ w, DecidableRel (ord w).le]
  [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)]

theorem selectionalCounterfactual_eq_one_iff_forall_compatible (hc : IsCentered ord) :
    selectionalCounterfactual ord p q w = 1 ↔
      ∀ s : SelectionFunction W, s.Compatible ord → w ∈ selectionConditional s p q :=
  selectionalCounterfactual_eq_one_iff.trans (mem_closestImp_iff_forall_compatible hc)

theorem selectionalCounterfactual_eq_neg_one_iff_forall_compatible (hc : IsCentered ord) :
    selectionalCounterfactual ord p q w = -1 ↔
      ∀ s : SelectionFunction W, s.Compatible ord → w ∉ selectionConditional s p q := by
  rw [selectionalCounterfactual_eq_neg_one_iff, mem_closestImp_iff_forall_compatible hc,
    mem_closestImp_iff_forall_compatible hc]
  obtain ⟨s₀, hs₀, -⟩ := SelectionFunction.exists_compatible (p := Set.univ) (w := w) hc
    ⟨Set.mem_univ w, fun u _ _ ↦ hc.le w u⟩
  constructor
  · rintro ⟨hn, hc'⟩ s hs hq
    rcases p.eq_empty_or_nonempty with rfl | hp
    · exact hn fun s _ ↦ by simp [mem_selectionConditional]
    · exact (mem_selectionConditional_of_nonempty s hp).1 (hc' s hs)
        ((mem_selectionConditional_of_nonempty s hp).1 hq)
  · intro h
    refine ⟨fun hall ↦ h s₀ hs₀ (hall s₀ hs₀), fun s hs ↦ ?_⟩
    rw [mem_selectionConditional]
    intro hp hq
    exact h s hs ((mem_selectionConditional_of_nonempty s hp).2 hq)

theorem superCounterfactual_eq_selectionalCounterfactual (hc : IsCentered ord) :
    superCounterfactual ord p q w = selectionalCounterfactual ord p q w := by
  unfold superCounterfactual
  rw [← selectionalCounterfactual_eq_one_iff_forall_compatible hc,
    ← selectionalCounterfactual_eq_neg_one_iff_forall_compatible hc]
  cases selectionalCounterfactual ord p q w <;> simp

theorem selectionalCounterfactual_eq_ofProp {s : SelectionFunction W} (hs : s.Compatible ord)
    (hu : ((ord w).minimals p).Subsingleton) (hp : p.Nonempty) :
    selectionalCounterfactual ord p q w = SignType.ofProp (s.sel w p ∈ q) := by
  have h : (ord w).minimals p = {s.sel w p} := hu.eq_singleton_of_mem (hs.sel_mem_minimals hp)
  by_cases hq : s.sel w p ∈ q <;> simp [selectionalCounterfactual, h, hq]

end Supervaluation

/-! ### Ties -/

theorem stalnaker_lewis_would_diverge :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (s : SelectionFunction (Fin 3)), IsCentered ord ∧
      s.Compatible ord ∧ (0 : Fin 3) ∈ selectionConditional s {1, 2} {1} ∧
      (0 : Fin 3) ∉ closestImp ord {1, 2} {1} := by
  let ord : Fin 3 → Preorder (Fin 3) := fun w ↦ Preorder.lift fun v ↦ if w = v then 0 else 1
  have hc : IsCentered ord := fun w w' h ↦ by simp [ord, h]
  obtain ⟨s, hs, hsel⟩ := SelectionFunction.exists_compatible (ord := ord) (w := 0)
    (p := {1, 2}) (v := 1) hc (by decide)
  refine ⟨ord, s, hc, hs, ?_, by decide⟩
  rw [mem_selectionConditional_of_nonempty _ ⟨1, by simp⟩, hsel]
  rfl

end Conditional
