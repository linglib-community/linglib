module

public import Linglib.Semantics.Questions.Partition.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# The σ-algebra of a question

The information in a partition question `Q` is the σ-algebra `Setoid.measurableSpace Q` of the
sets that are unions of cells, the pullback of the discrete σ-algebra along the quotient map. Its
measurable sets are exactly the propositions the question determines
(`measurableSet_measurableSpace_iff`), so a finer question has a larger σ-algebra
(`measurableSpace_anti`), the finest question has every set and the trivial question only `∅`
and the whole space. Conditioning on this σ-algebra is conditioning on the answer.

## TODO

* The conditional expectation given `Q.measurableSpace` as the average over the cell, and the
  value of a question through it for an arbitrary probability space of worlds.
-/

@[expose] public section

open MeasureTheory

namespace Setoid

variable {W : Type*} {Q Q' : Setoid W} {s : Set W}

variable (Q) in
/-- The σ-algebra of a question is the pullback of the discrete σ-algebra on its answers along
the quotient map. -/
@[instance_reducible]
def measurableSpace : MeasurableSpace W := MeasurableSpace.comap (Quotient.mk Q) ⊤

/-- The measurable sets of the σ-algebra of a question are the propositions it determines. -/
theorem measurableSet_measurableSpace_iff :
    MeasurableSet[Q.measurableSpace] s ↔ Q.Determines s := by
  rw [measurableSpace, MeasurableSpace.measurableSet_comap, determines_iff]
  constructor
  · rintro ⟨t, -, rfl⟩ w v h
    simp only [Set.mem_preimage, Quotient.sound h]
  · intro h
    refine ⟨Quotient.mk Q '' s, trivial, Set.ext fun w ↦ ⟨?_, fun hw ↦ ⟨w, hw, rfl⟩⟩⟩
    rintro ⟨v, hv, hvw⟩
    exact (h v w (Quotient.exact hvw)).1 hv

/-- A finer question has a larger σ-algebra. -/
theorem measurableSpace_anti : Antitone (measurableSpace : Setoid W → MeasurableSpace W) :=
  fun _ _ h _ hs ↦ measurableSet_measurableSpace_iff.2
    ((measurableSet_measurableSpace_iff.1 hs).mono h)

@[simp] theorem measurableSpace_bot : (⊥ : Setoid W).measurableSpace = ⊤ :=
  top_unique fun _ _ ↦ measurableSet_measurableSpace_iff.2 bot_determines

end Setoid
