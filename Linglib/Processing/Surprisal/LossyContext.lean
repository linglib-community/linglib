/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Surprisal
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Memory processes

This file defines the memory process of [futrell-gibson-levy-2020]'s lossy-context surprisal. A
memory process encodes a context as a distribution over memory representations and predicts the
next word from the representation alone, so that the representation mediates all information
flow from the context to the prediction. The difficulty of a word in a context is its expected
surprisal over the representations the context can produce, and the average difficulty of the
process under a language model and a context prior averages it over contexts and the words they
predict.

A process whose encoder is deterministic and whose predictor, read through the encoder, is a
language model loses no information, and its difficulty is that model's surprisal: surprisal
theory is the lossless special case.

## Main definitions

* `MemoryProcess`: an encoder `Kernel C R` and a predictor `Kernel R W`.
* `MemoryProcess.expectedSurprisal`, `MemoryProcess.averageDifficulty`.
* `MemoryProcess.IsLosslessFor`: the process realizes a language model through a deterministic
  summary of the context.

## Main results

* `MemoryProcess.expectedSurprisal_of_dirac`, `MemoryProcess.expectedSurprisal_of_bernoulli`:
  expected surprisal under a point-mass and under a two-point encoder.
* `MemoryProcess.expectedSurprisal_eq_surprisal_of_lossless`.

## References

* [futrell-gibson-levy-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ProbabilityTheory unitInterval

namespace LossyContext

variable {C R W : Type*} [MeasurableSpace C] [MeasurableSpace R] [MeasurableSpace W]

/-- A memory process: a lossy encoder from contexts to memory representations and a predictor
from memory representations to next words. The representation mediates all information flow
from the context to the prediction. -/
structure MemoryProcess (C R W : Type*) [MeasurableSpace C] [MeasurableSpace R]
    [MeasurableSpace W] where
  /-- The distribution over memory representations a context produces. -/
  encode : Kernel C R
  /-- The next-word distribution a memory representation predicts. -/
  predict : Kernel R W

namespace MemoryProcess

variable (mp : MemoryProcess C R W)

/-- The surprisal of the word `w` at the memory representation `r`. -/
noncomputable def perStateSurprisal (r : R) (w : W) : ℝ := surprisal (mp.predict r) w

/-- The expected surprisal of `w` in the context `c`: the difficulty of `w` under the process. -/
noncomputable def expectedSurprisal (c : C) (w : W) : ℝ :=
  ∫ r, mp.perStateSurprisal r w ∂(mp.encode c)

/-- The average difficulty of the process under the language model `L` and the context prior
`π`: expected surprisal averaged over contexts and the words they predict. -/
noncomputable def averageDifficulty (L : Kernel C W) (π : Measure C) : ℝ :=
  ∫ c, ∫ w, mp.expectedSurprisal c w ∂(L c) ∂π

/-- The process realizes the language model `L` through the summary `f`: the encoder is
deterministic at `f`, and the predictor pulled back along `f` is `L`. -/
def IsLosslessFor (L : Kernel C W) : Prop :=
  ∃ (f : C → R) (hf : Measurable f), mp.encode = Kernel.deterministic f hf ∧
    mp.predict.comap f hf = L

variable {mp}

theorem isLosslessFor_comap {f : C → R} {hf : Measurable f}
    (h : mp.encode = Kernel.deterministic f hf) : mp.IsLosslessFor (mp.predict.comap f hf) :=
  ⟨f, hf, h, rfl⟩

variable [MeasurableSingletonClass R] {c : C}

theorem expectedSurprisal_of_dirac {r : R} (h : mp.encode c = Measure.dirac r) (w : W) :
    mp.expectedSurprisal c w = mp.perStateSurprisal r w := by
  rw [expectedSurprisal, h, integral_dirac]

theorem expectedSurprisal_of_bernoulli {r₁ r₂ : R} {p : I} (h : mp.encode c = Ber(r₁, r₂, p))
    (w : W) : mp.expectedSurprisal c w
      = p * mp.perStateSurprisal r₁ w + (1 - p) * mp.perStateSurprisal r₂ w := by
  rw [expectedSurprisal, h, integral_bernoulliMeasure, smul_eq_mul, smul_eq_mul]

theorem expectedSurprisal_of_deterministic {f : C → R} {hf : Measurable f}
    (h : mp.encode = Kernel.deterministic f hf) (c : C) (w : W) :
    mp.expectedSurprisal c w = mp.perStateSurprisal (f c) w :=
  expectedSurprisal_of_dirac (h ▸ Kernel.deterministic_apply hf c) w

theorem expectedSurprisal_eq_surprisal_of_lossless {L : Kernel C W} (h : mp.IsLosslessFor L)
    (c : C) (w : W) : mp.expectedSurprisal c w = surprisal (L c) w := by
  obtain ⟨f, hf, he, hp⟩ := h
  rw [expectedSurprisal_of_deterministic he, perStateSurprisal, ← hp, Kernel.comap_apply]

end MemoryProcess

end LossyContext
