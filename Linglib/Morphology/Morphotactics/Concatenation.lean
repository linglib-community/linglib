/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Mealy
public import Linglib.Morphology.Inflection
public import Linglib.Morphology.Morphotactics.Template.Basic

/-!
# Morphotactics over strings of exponents

A morphotactics builds the form of a word from a stem and its inflectional material. Here the
material is a string of exponents, so a morphotactics is a function `m : Z → List E → F`.

We define `ofStep base step`, which attaches the exponents to the stem one at a time: its form
on `es` is `es.foldl step (base z)`. A morphotactics is *stepwise* when
`m z es = m z' es'` implies `m z (es ++ [e]) = m z' (es' ++ [e])`, which holds exactly when it
attaches its exponents one at a time by some step (`isStepwise_iff_exists_step`). A
morphotactics whose forms are strings is *concatenative* when `m z es` is a prefix of
`m z (es ++ [e])`.

We also define `realization m L`, the `Morphology.Realization` whose contexts are the strings
that `L` licenses. For `ofStep`, the strings with a given form are found one exponent at a time
(`concat_mem_cells_ofStep`).

## Implementation notes

`ofStep` is a left fold, since suffixes attach to the right of what is already built;
`FreeMonoid.mkMulAction` is the right fold.

## TODO

* `PFM.evalBlocks` folds rule blocks at a fixed cell. Its relation to `ofStep` is not stated.
* A string here is a string of suffixes. Prefixes are not treated.

## References

* [bickel-nichols-2007]
-/

@[expose] public section

namespace Morphotactics

open Morphology

variable {Z E F G α β σ : Type*}

/-! ### Attaching one exponent at a time -/

section OfStep

variable (base : Z → F) (step : F → E → F) (z : Z) (es es' : List E) (e : E)

/-- `ofStep base step z es` is the form of the stem `z` with the exponents of `es` attached in
turn, each by `step` to the form before it. -/
def ofStep : F := es.foldl step (base z)

@[simp] theorem ofStep_nil : ofStep base step z [] = base z := rfl

theorem ofStep_concat : ofStep base step z (es ++ [e]) = step (ofStep base step z es) e := by
  simp [ofStep]

theorem ofStep_append :
    ofStep base step z (es ++ es') = es'.foldl step (ofStep base step z es) :=
  List.foldl_append

end OfStep

/-! ### Stepwise morphotactics -/

/-- A morphotactics is *stepwise* when two strings with the same form have the same form with
one more exponent: the exponent sees only the form it attaches to. -/
def IsStepwise (m : Z → List E → F) : Prop :=
  ∀ ⦃z z' : Z⦄ ⦃es es' : List E⦄ (e : E), m z es = m z' es' → m z (es ++ [e]) = m z' (es' ++ [e])

theorem isStepwise_ofStep (base : Z → F) (step : F → E → F) : IsStepwise (ofStep base step) :=
  fun _ _ _ _ e h ↦ by rw [ofStep_concat, ofStep_concat, h]

theorem IsStepwise.append {m : Z → List E → F} (h : IsStepwise m) {z z' : Z} {es es' : List E}
    (hm : m z es = m z' es') (s : List E) : m z (es ++ s) = m z' (es' ++ s) := by
  induction s using List.reverseRecOn with
  | nil => simpa using hm
  | append_singleton s e ih => rw [← List.append_assoc, ← List.append_assoc]; exact h e ih

/-- A morphotactics is stepwise exactly when it attaches its exponents one at a time by some
step. -/
theorem isStepwise_iff_exists_step {m : Z → List E → F} :
    IsStepwise m ↔ ∃ step : F → E → F, ∀ z es, m z es = es.foldl step (m z []) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨step, hs⟩ z z' es es' e hm ↦ ?_⟩
  · refine ⟨fun f e ↦ if hf : ∃ z es, m z es = f then
      m hf.choose (hf.choose_spec.choose ++ [e]) else f, fun z es ↦ ?_⟩
    induction es using List.reverseRecOn with
    | nil => rfl
    | append_singleton es e ih =>
      have hf : ∃ z' es', m z' es' = m z es := ⟨z, es, rfl⟩
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih, dite_eq_left hf]
      exact h e hf.choose_spec.choose_spec.symm
  · rw [hs z, hs z', List.foldl_append, List.foldl_append, ← hs z, ← hs z', hm]

/-- A map of forms applied after `ofStep` gives a stepwise morphotactics when forms with the
same image have the same image after a step. -/
theorem isStepwise_comp_ofStep (base : Z → F) {step : F → E → F} {g : F → G}
    (hg : ∀ ⦃f f' : F⦄ (e : E), g f = g f' → g (step f e) = g (step f' e)) :
    IsStepwise fun z es ↦ g (ofStep base step z es) :=
  fun _ _ _ _ e h ↦ by simp only [ofStep_concat]; exact hg e h

/-! ### Concatenative morphotactics -/

/-- A morphotactics whose forms are strings is *concatenative* when a further exponent leaves
the form before it in place. -/
def IsConcatenative (m : Z → List E → List α) : Prop :=
  ∀ z es e, m z es <+: m z (es ++ [e])

theorem isConcatenative_iff {m : Z → List E → List α} :
    IsConcatenative m ↔ ∀ z ⦃es es' : List E⦄, es <+: es' → m z es <+: m z es' := by
  refine ⟨fun h z es es' hp ↦ ?_, fun h z es e ↦ h z (List.prefix_append es [e])⟩
  obtain ⟨s, rfl⟩ := hp
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s e ih => rw [← List.append_assoc]; exact ih.trans (h z (es ++ s) e)

theorem isConcatenative_ofStep (base : Z → List α) {step : List α → E → List α}
    (h : ∀ f e, f <+: step f e) : IsConcatenative (ofStep base step) :=
  fun z es e ↦ by rw [ofStep_concat]; exact h _ e

theorem IsConcatenative.comp {m : Z → List E → List α} (h : IsConcatenative m)
    {g : List α → List β} (hg : ∀ ⦃u v : List α⦄, u <+: v → g u <+: g v) :
    IsConcatenative fun z es ↦ g (m z es) :=
  fun z es e ↦ hg (h z es e)

theorem IsConcatenative.run {m : Z → List E → List α} (h : IsConcatenative m)
    (T : Mealy σ α β) : IsConcatenative fun z es ↦ T.run (m z es) :=
  h.comp fun u _ ⟨t, ht⟩ ↦ ht ▸ ⟨_, (T.runFrom_append T.start u t).symm⟩

/-! ### The realization of a morphotactics -/

section Realization

variable (m : Z → List E → F) (L : List E → Prop) [DecidablePred L]
  {z : Z} {es : List E} {e : E} {f : F}

/-- `realization m L` realizes a stem at each string of exponents that `L` licenses by its form
under `m`, and at no other string. -/
def realization : Realization Z (List E) F :=
  .ofOption fun z es ↦ if L es then some (m z es) else none

variable {m L}

theorem mem_cells_realization : es ∈ (realization m L).cells z f ↔ L es ∧ m z es = f := by
  unfold realization
  simp only [Realization.mem_cells, Realization.ofOption]
  split_ifs with h <;> simp [h, eq_comm]

theorem isLicensed_realization : (realization m L).IsLicensed z es ↔ L es := by
  unfold realization Realization.IsLicensed
  simp only [Realization.ofOption]
  split_ifs with h <;> simp [h]

/-- The cells of a form under `ofStep` are found one exponent at a time: a string with one more
exponent fills the cell of `f` exactly when it is licensed and the string before it fills the
cell of a form that the step takes to `f`. -/
theorem concat_mem_cells_ofStep {base : Z → F} {step : F → E → F}
    (hL : ∀ ⦃es : List E⦄ ⦃e : E⦄, L (es ++ [e]) → L es) :
    es ++ [e] ∈ (realization (ofStep base step) L).cells z f ↔
      L (es ++ [e]) ∧ ∃ f', es ∈ (realization (ofStep base step) L).cells z f' ∧
        step f' e = f := by
  rw [mem_cells_realization]
  refine ⟨?_, ?_⟩
  · rintro ⟨hl, rfl⟩
    exact ⟨hl, _, mem_cells_realization.2 ⟨hL hl, rfl⟩, (ofStep_concat ..).symm⟩
  · rintro ⟨hl, f', hf', rfl⟩
    exact ⟨hl, by rw [ofStep_concat, (mem_cells_realization.1 hf').2]⟩

end Realization

theorem Template.licensed_of_isPrefix {Slot : Type*}
    [DecidableEq Slot] {t : Template Slot} {X : Slot → Type*} {w w' : List (Σ s, X s)}
    (h : t.Licensed w') (hp : w <+: w') : t.Licensed w :=
  Template.isSublistClosed_language (hp.sublist.map Sigma.fst) h

end Morphotactics
