/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: transducer sections of `Mathlib.Computability.MyhillNerode`, with
`Function.residual` beside `Language.leftQuotient`.
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Option
public import Linglib.Core.Computability.Residual
public import Linglib.Core.Computability.Subsequential

/-!
# The Myhill–Nerode theorem for subsequential transducers

A function `f : List α → List β` is left-subsequential if and only if it has finitely many
residuals `f.residual u` (`isLeftSubsequential_iff_finite_range_residual`), as a language is
regular if and only if it has finitely many left quotients. The residuals are the states of a
transducer computing `f`, which emits on each symbol the prefix function of the current residual
and at the end of the word what the residual leaves. In particular a function whose residuals
factor through a summary with finitely many values is left-subsequential
(`IsLeftSubsequential.of_factorsThrough_residual`).

## References

* [J. Chandlee, R. Eyraud and J. Heinz, *Output Strictly Local Functions*
  (2015)][chandlee-eyraud-heinz-2015]: recalls the characterization of Oncina and García
-/

@[expose] public section

open Function

variable {α β : Type*} {f : List α → List β}

theorem SubsequentialTransducer.residual_run {σ : Type*} (T : SubsequentialTransducer σ α β)
    (u : List α) : T.run.residual u = (T.runFrom (T.eval u)).residual [] :=
  residual_eq_of_forall (P := T.emitted T.start u) fun w ↦ by
    rw [List.nil_append]; exact T.run_append u w

theorem IsLeftSubsequential.finite_range_residual (hf : IsLeftSubsequential f) :
    (Set.range f.residual).Finite := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact (Set.finite_range fun q ↦ (T.runFrom q).residual []).subset
    (Set.range_subset_iff.mpr fun u ↦ ⟨_, (T.residual_run u).symm⟩)

theorem IsLeftSubsequential.of_finite_range_residual (hf : (Set.range f.residual).Finite) :
    IsLeftSubsequential f := by
  have := hf.fintype
  let fn : Option (Set.range f.residual) → List α → List β := fun q ↦ q.elim f Subtype.val
  have hstep : ∀ q x, (fn q).residual [x] ∈ Set.range f.residual := by
    rintro (_ | ⟨_, u, rfl⟩) x
    · exact ⟨[x], rfl⟩
    · exact ⟨u ++ [x], residual_append u [x]⟩
  let T : SubsequentialTransducer (Option (Set.range f.residual)) α β :=
    { start := none
      step := fun q x ↦ some ⟨_, hstep q x⟩
      output := fun q x ↦ (fn q).prefixFunction [x]
      finalOutput := fun q ↦ fn q [] }
  have hrun : ∀ q v, T.runFrom q v = fn q v := by
    intro q v
    induction v generalizing q with
    | nil => rfl
    | cons x v ih =>
      rw [SubsequentialTransducer.runFrom_cons, ih]
      exact prefixFunction_append_residual [x] v
  have hT : T.run = f := funext fun v ↦ hrun none v
  exact hT ▸ T.isLeftSubsequential

/-- A function whose residuals factor through a summary with finitely many values is
left-subsequential. -/
theorem IsLeftSubsequential.of_factorsThrough_residual {γ : Type*} {W : List α → γ}
    (hW : f.residual.FactorsThrough W) (hfin : (Set.range W).Finite) : IsLeftSubsequential f :=
  .of_finite_range_residual <| (hfin.image (Function.extend W f.residual fun _ _ ↦ [])).subset <|
    Set.range_subset_iff.mpr fun u ↦ ⟨_, Set.mem_range_self u, hW.extend_apply _ u⟩

/-- A function is left-subsequential iff it has finitely many residuals, which is the Myhill–Nerode
theorem for subsequential transducers ([chandlee-eyraud-heinz-2015], after Oncina and García). -/
theorem isLeftSubsequential_iff_finite_range_residual :
    IsLeftSubsequential f ↔ (Set.range f.residual).Finite :=
  ⟨IsLeftSubsequential.finite_range_residual, IsLeftSubsequential.of_finite_range_residual⟩

theorem isRightSubsequential_iff_finite_range_residual :
    IsRightSubsequential f ↔ (Set.range (List.revConj f).residual).Finite :=
  isLeftSubsequential_iff_finite_range_residual
