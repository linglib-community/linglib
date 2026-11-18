module

public import Linglib.Core.MeasureTheory.Measure.Prod
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Pragmatics.Probabilistic.Listener

/-!
# Latent variables

A latent the speaker knows and the listener does not is a coordinate of the listener's state, and
her beliefs about the world and about the latent are [the two marginals of her
posterior](##RSA.listener_fst_real_singleton). In the lexical-uncertainty model of Bergen, Levy
and Goodman the latent is a lexicon with a prior independent of the state's. The paper states the
listener's belief about the state as the listener of the speaker averaged over lexica, and [the
two presentations agree](##RSA.listener_prod_fst); her belief about the lexicon is [the listener
of the speaker averaged over states](##RSA.listener_prod_snd). A state is possible after an
utterance exactly when it has positive prior and some lexicon of positive prior has its speaker
produce the utterance there ([the union of the lexica's
supports](##RSA.listener_prod_fst_apply_singleton_ne_zero_iff)), and two states the speakers of
every such lexicon treat alike [keep their prior
odds](##RSA.listener_prod_fst_apply_singleton_mul_eq). A threshold, a comparison class, a scope
reading or a question under discussion enters the same way. When the listener hears only the form
of the speaker's choice, the latent is the choice, and its prior depends on the state: the joint
of the world prior and the speaker.

## References

* [bergen-levy-goodman-2016]
* [M. Franke and L. Bergen, *Theory-Driven Statistical Modeling for Semantics and Pragmatics: A
  Case Study on Grammatically Generated Implicature Readings* (2020)][franke-bergen-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section Pipeline

variable {W U O : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSpace O]

section Listener

variable [Countable U] [MeasurableSingletonClass U]

/-! ##### Marginals of a listener over a product

A latent the speaker also knows, a lexicon or a threshold or a question, is a coordinate of the
state: the speaker at a pair is `fun p ↦ speaker α C (L p.2) Measure.dirac p.1`, addressing that
latent's listener, and her listener holds a prior over pairs. Its marginals pool the
prior-weighted production probabilities over the other coordinate. When the prior over pairs is a
product, this is lexical uncertainty (`Linglib.Pragmatics.Probabilistic.Latent`). -/

section Prod

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Fintype A] [Fintype B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B] (μ : Measure (A × B))
  (S : A × B → Measure U) [IsFiniteMeasure μ] [∀ p, IsFiniteMeasure (S p)]

theorem listener_fst_apply_singleton_ne_zero_iff (u : U) (a : A) :
    (listener μ S u).fst {a} ≠ 0 ↔ ∃ b, μ {(a, b)} ≠ 0 ∧ S (a, b) {u} ≠ 0 := by
  rw [Measure.fst_apply_singleton, ne_eq, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, not_forall, listener_apply_singleton_ne_zero_iff]

theorem listener_snd_apply_singleton_ne_zero_iff (u : U) (b : B) :
    (listener μ S u).snd {b} ≠ 0 ↔ ∃ a, μ {(a, b)} ≠ 0 ∧ S (a, b) {u} ≠ 0 := by
  rw [Measure.snd_apply_singleton, ne_eq, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, not_forall, listener_apply_singleton_ne_zero_iff]

theorem listener_fst_real_singleton (u : U) (a : A) :
    (listener μ S u).fst.real {a} =
      (∑ b, μ.real {(a, b)} * (S (a, b)).real {u}) / ∑ p, μ.real {p} * (S p).real {u} := by
  rw [Measure.fst_real_singleton_eq_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun b _ ↦ listener_real_singleton μ S u (a, b)

theorem listener_snd_real_singleton (u : U) (b : B) :
    (listener μ S u).snd.real {b} =
      (∑ a, μ.real {(a, b)} * (S (a, b)).real {u}) / ∑ p, μ.real {p} * (S p).real {u} := by
  rw [Measure.snd_real_singleton_eq_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ ↦ listener_real_singleton μ S u (a, b)

theorem listener_fst_real_lt_iff (u : U) (a₁ a₂ : A) :
    (listener μ S u).fst.real {a₁} < (listener μ S u).fst.real {a₂} ↔
      ∑ b, μ.real {(a₁, b)} * (S (a₁, b)).real {u} <
        ∑ b, μ.real {(a₂, b)} * (S (a₂, b)).real {u} := by
  have key (a : A) : (listener μ S u).fst.real {a} =
      (listener μ S u).real ↑(({a} : Finset A) ×ˢ (Finset.univ : Finset B)) := by
    rw [measureReal_def, measureReal_def, Measure.fst_apply (measurableSet_singleton a)]
    congr 2
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [key, key, listener_real_finset_lt_iff, Finset.sum_product, Finset.sum_product,
    Finset.sum_singleton, Finset.sum_singleton]

theorem listener_snd_real_lt_iff (u : U) (b₁ b₂ : B) :
    (listener μ S u).snd.real {b₁} < (listener μ S u).snd.real {b₂} ↔
      ∑ a, μ.real {(a, b₁)} * (S (a, b₁)).real {u} <
        ∑ a, μ.real {(a, b₂)} * (S (a, b₂)).real {u} := by
  have key (b : B) : (listener μ S u).snd.real {b} =
      (listener μ S u).real ↑((Finset.univ : Finset A) ×ˢ ({b} : Finset B)) := by
    rw [measureReal_def, measureReal_def, Measure.snd_apply (measurableSet_singleton b)]
    congr 2
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [key, key, listener_real_finset_lt_iff, Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_singleton]

section Flat

variable (hμeq : ∀ p q : A × B, μ {p} = μ {q}) (hμ0 : ∀ p, μ {p} ≠ 0)
include hμeq hμ0

/-- At a prior giving every pair the same positive mass, the first marginal of the listener
prefers the point with the greater production probability summed over the second coordinate. -/
theorem listener_fst_real_lt_iff_of_forall_eq (u : U) (a₁ a₂ : A) :
    (listener μ S u).fst.real {a₁} < (listener μ S u).fst.real {a₂} ↔
      ∑ b, (S (a₁, b)).real {u} < ∑ b, (S (a₂, b)).real {u} := by
  rcases isEmpty_or_nonempty B with hB | ⟨⟨b₀⟩⟩
  · simp [Measure.fst_real_singleton_eq_sum]
  · have key (a : A) : ∑ b, μ.real {(a, b)} * (S (a, b)).real {u} =
        μ.real {(a₁, b₀)} * ∑ b, (S (a, b)).real {u} := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ ↦ by
        rw [show μ.real {(a, b)} = μ.real {(a₁, b₀)} by rw [measureReal_def, measureReal_def, hμeq]]
    rw [listener_fst_real_lt_iff, key, key, mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real _ from ENNReal.toReal_pos (hμ0 _) (measure_ne_top _ _))]

/-- At a prior giving every pair the same positive mass, the second marginal of the listener
prefers the point with the greater production probability summed over the first coordinate. -/
theorem listener_snd_real_lt_iff_of_forall_eq (u : U) (b₁ b₂ : B) :
    (listener μ S u).snd.real {b₁} < (listener μ S u).snd.real {b₂} ↔
      ∑ a, (S (a, b₁)).real {u} < ∑ a, (S (a, b₂)).real {u} := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
  · simp [Measure.snd_real_singleton_eq_sum]
  · have key (b : B) : ∑ a, μ.real {(a, b)} * (S (a, b)).real {u} =
        μ.real {(a₀, b₁)} * ∑ a, (S (a, b)).real {u} := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ ↦ by
        rw [show μ.real {(a, b)} = μ.real {(a₀, b₁)} by rw [measureReal_def, measureReal_def, hμeq]]
    rw [listener_snd_real_lt_iff, key, key, mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real _ from ENNReal.toReal_pos (hμ0 _) (measure_ne_top _ _))]

end Flat

end Prod

end Listener

/-! #### The heard form

When the listener hears only the form `obs u` of the speaker's choice `u` (eqs. 18b/21b), her
state is the pair of the world and the choice, her prior the joint of the world prior and the
speaker, and her channel the point mass at the form. Her first marginal is her belief about the
world and her second her belief about the choice. -/

private theorem compProd_real_mul_dirac_real [MeasurableSingletonClass W]
    [MeasurableSingletonClass U] [MeasurableSingletonClass O] [DecidableEq O] (μ : Measure W)
    [SFinite μ] (κ : Kernel W U) [IsSFiniteKernel κ] (obs : U → O) (o : O) (w : W) (u : U) :
    (μ ⊗ₘ κ).real {(w, u)} * (Measure.dirac (obs u)).real {o} =
      if obs u = o then μ.real {w} * (κ w).real {u} else 0 := by
  rw [measureReal_def, measureReal_def, Measure.compProd_apply_singleton, ENNReal.toReal_mul,
    Measure.dirac_apply' _ (measurableSet_singleton o), ← measureReal_def, ← measureReal_def]
  split_ifs with h <;> simp [h]

section Form

variable [Fintype W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]
  [Countable O] [MeasurableSingletonClass O] (μ : Measure W) [IsFiniteMeasure μ] (κ : Kernel W U)
  [IsFiniteKernel κ] (obs : U → O)

theorem listener_compProd_dirac_apply_singleton_ne_zero_iff (o : O) (w : W) (u : U) :
    listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o {(w, u)} ≠ 0 ↔
      obs u = o ∧ μ {w} ≠ 0 ∧ κ w {u} ≠ 0 := by
  rw [listener_apply_singleton_ne_zero_iff, Measure.compProd_apply_singleton, mul_ne_zero_iff,
    Measure.dirac_apply' _ (measurableSet_singleton o)]
  by_cases h : obs u = o <;> simp [h]

variable [DecidableEq O]

/-- The listener of the form prefers the state with the greater prior-weighted production
probability pooled over the choices with the form heard. -/
theorem listener_compProd_dirac_fst_real_lt_iff (o : O) (w₁ w₂ : W) :
    (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₁} <
        (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₂} ↔
      ∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₁} * (κ w₁).real {u} <
        ∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₂} * (κ w₂).real {u} := by
  rw [listener_fst_real_lt_iff]
  simp only [compProd_real_mul_dirac_real, Finset.sum_filter]

/-- Between two choices with the form heard, the listener of the form prefers the one with the
greater prior-weighted production probability pooled over the states. -/
theorem listener_compProd_dirac_snd_real_lt_iff {o : O} {u₁ u₂ : U} (h₁ : obs u₁ = o)
    (h₂ : obs u₂ = o) :
    (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₁} <
        (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₂} ↔
      ∑ w, μ.real {w} * (κ w).real {u₁} < ∑ w, μ.real {w} * (κ w).real {u₂} := by
  rw [listener_snd_real_lt_iff]
  simp only [compProd_real_mul_dirac_real, ite_eq_left h₁, ite_eq_left h₂]

/-- At a uniform prior the listener of the form prefers the state likelier to produce a choice
with the form heard. -/
theorem listener_uniformOn_compProd_dirac_fst_real_lt_iff (o : O) (w₁ w₂ : W) :
    (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₁} <
        (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₂} ↔
      (κ w₁).real ↑(Finset.univ.filter (obs · = o)) <
        (κ w₂).real ↑(Finset.univ.filter (obs · = o)) := by
  have : Nonempty W := ⟨w₁⟩
  simp_rw [listener_compProd_dirac_fst_real_lt_iff, uniformOn_univ_real_singleton,
    ← Finset.mul_sum, sum_measureReal_singleton]
  exact mul_lt_mul_iff_right₀ (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))

/-- At a uniform prior the listener of the form prefers, of two choices with the form heard, the
one the states together are likelier to produce. -/
theorem listener_uniformOn_compProd_dirac_snd_real_lt_iff {o : O} {u₁ u₂ : U} (h₁ : obs u₁ = o)
    (h₂ : obs u₂ = o) :
    (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₁} <
        (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₂} ↔
      ∑ w, (κ w).real {u₁} < ∑ w, (κ w).real {u₂} := by
  rcases isEmpty_or_nonempty W with hW | hW
  · simp [listener_compProd_dirac_snd_real_lt_iff _ κ obs h₁ h₂]
  · simp_rw [listener_compProd_dirac_snd_real_lt_iff _ κ obs h₁ h₂, uniformOn_univ_real_singleton,
      ← Finset.mul_sum]
    exact mul_lt_mul_iff_right₀ (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))

end Form

end Pipeline

/-! ### A latent with an independent prior -/

section Independent

variable {A B U : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace U]
  [Fintype A] [Fintype B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [Countable U] [MeasurableSingletonClass U]

/-- **Lexical uncertainty.** Against a product prior, the first marginal of the listener is the
listener of the speaker averaged over the second coordinate by its prior. -/
theorem listener_prod_fst (μ : Measure A) (ν : Measure B) (S : A × B → Measure U) :
    (listener (μ.prod ν) S).fst = listener μ fun a ↦ ∑ b, ν {b} • S (a, b) := by
  ext u : 1
  refine Measure.ext_of_singleton fun a ↦ ?_
  change (listener (μ.prod ν) S u).fst {a} = _
  simp_rw [Measure.fst_apply_singleton, listener_apply_singleton, div_eq_mul_inv, ← Finset.sum_mul,
    Fintype.sum_prod_type, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  congr 1
  · ring
  · exact congrArg _ <| Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Against a product prior, the second marginal of the listener, her belief about the latent, is
the listener of the speaker averaged over the first coordinate by its prior. -/
theorem listener_prod_snd (μ : Measure A) (ν : Measure B) (S : A × B → Measure U) :
    (listener (μ.prod ν) S).snd = listener ν fun b ↦ ∑ a, μ {a} • S (a, b) := by
  ext u : 1
  refine Measure.ext_of_singleton fun b ↦ ?_
  change (listener (μ.prod ν) S u).snd {b} = _
  simp_rw [Measure.snd_apply_singleton, listener_apply_singleton, div_eq_mul_inv, ← Finset.sum_mul,
    Fintype.sum_prod_type, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  congr 1
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  · rw [Finset.sum_comm]
    exact congrArg _ <| Finset.sum_congr rfl fun _ _ ↦ by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Against a product prior, the listener keeps the prior odds of two states at which the speaker
gives the utterance the same mass at every value of positive prior of the second coordinate. -/
theorem listener_prod_fst_apply_singleton_mul_eq (μ : Measure A) (ν : Measure B)
    (S : A × B → Measure U) {u : U} {a₁ a₂ : A}
    (h : ∀ b, ν {b} ≠ 0 → S (a₁, b) {u} = S (a₂, b) {u}) :
    (listener (μ.prod ν) S).fst u {a₁} * μ {a₂} = (listener (μ.prod ν) S).fst u {a₂} * μ {a₁} := by
  rw [listener_prod_fst]
  refine listener_apply_singleton_mul_eq_of_apply_eq _ _ ?_
  simp only [Measure.finsetSum_apply, Measure.smul_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rcases eq_or_ne (ν {b}) 0 with hb | hb
  · rw [hb, zero_smul, zero_smul]
  · rw [h b hb]

variable (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure B) [IsFiniteMeasure ν]
  (S : A × B → Measure U) [∀ p, IsFiniteMeasure (S p)] (u : U) (a : A)

theorem listener_prod_fst_real_singleton :
    (listener (μ.prod ν) S u).fst.real {a} =
      μ.real {a} * (∑ b, ν.real {b} * (S (a, b)).real {u}) /
        ∑ p, (μ.prod ν).real {p} * (S p).real {u} := by
  rw [listener_fst_real_singleton]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [Measure.prod_real_singleton, mul_assoc]

/-- Against a product prior, a state is possible after an utterance exactly when it has positive
prior and the speaker produces the utterance there at some value of positive prior of the second
coordinate. -/
theorem listener_prod_fst_apply_singleton_ne_zero_iff :
    (listener (μ.prod ν) S u).fst {a} ≠ 0 ↔ μ {a} ≠ 0 ∧ ∃ b, ν {b} ≠ 0 ∧ S (a, b) {u} ≠ 0 := by
  simp_rw [listener_fst_apply_singleton_ne_zero_iff, ← Set.singleton_prod_singleton,
    Measure.prod_prod, mul_ne_zero_iff]
  exact ⟨fun ⟨b, ⟨ha, hb⟩, h⟩ ↦ ⟨ha, b, hb, h⟩, fun ⟨ha, b, hb, h⟩ ↦ ⟨b, ⟨ha, hb⟩, h⟩⟩

end Independent

end RSA
