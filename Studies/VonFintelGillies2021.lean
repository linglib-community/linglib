module

public import Studies.VonFintelGillies2010
public import Linglib.Data.Examples.VonFintelGillies2021

/-!
# von Fintel & Gillies (2021): Still Going Strong

This file formalizes von Fintel and Gillies's return to the strong *must* of their 2010
paper. Two observations about epistemic *can't* pose a dilemma for the
Mantra: *can't* patterns with *must* in its evidential distribution (Observation 4), and
*can't φ* is incompatible with *it's possible that φ* (Observation 5), so *can't* can be the
negation neither of a strong nor of a weak existential modal. Kernel semantics resolves the
dilemma: *can't φ* is *must* of the negation, so its evidential signal is that of *must*, and
its assertion, that the modal base excludes `φ`, contradicts *might φ* and under a realistic
base entails the negation of the prejacent, the thesis S2. On the wet-rain-gear kernel of the
earlier paper *it can't be not raining* is defined, true, and excludes *it might be not raining*
at once, the joint profile the Mantra cannot assign (`cant_dilemma_resolved`), and direct
information that settles the prejacent, seeing the rain, gives *can't* presupposition failure as
it does *must*. The anti-knowledge
examples of §4.2, Phil who checked dinner himself against Meryl who followed instructions (24)
and (25), are the rows of `Data.Examples.VonFintelGillies2021`.

## References

* [von-fintel-gillies-2021]
* [von-fintel-gillies-2010]
-/

@[expose] public section

namespace VonFintelGillies2021

/-! ### The can't dilemma (§4.1, Observations 4 and 5)

The Mantra faces a dilemma: no assignment of force to *can't* simultaneously
explains its evidential distribution (Observation 4: *can't* patterns like
*must*) and its incompatibility with *it's possible that φ* (Observation 5).
Kernel semantics resolves this: *can't φ* = *must*(¬φ) by definition
(`kernelCant`), so Observation 4's evidential parallelism holds by
construction, while the strong assertion B_K ⊆ ⟦¬φ⟧ delivers Observation 5. -/

open Modality VonFintelGillies2010

/-- `⟦not raining⟧`. -/
abbrev notRaining : World → Prop := fun w ↦ ¬ raining w

variable {W : Type*} (k : Kernel W) (φ : W → Prop) (w : W)

-- Observation 5
theorem cant_might_exclusion (hCant : kernelCant k φ w = 1) : kernelMight k φ w = -1 := by
  rw [kernelMight_eq_neg_kernelCant, Pi.neg_apply, hCant]

theorem cant_entails_negation (hReal : w ∈ k.base) (hTrue : kernelCant k φ w = 1) : ¬ φ w :=
  must_entails_prejacent k _ w hReal (kernelMust_eq_one_iff.1 hTrue).2

theorem cant_dilemma_resolved :
    (true, true) ∈ wetGearK.base ∧ kernelCant wetGearK notRaining (true, true) = 1 ∧
      kernelMight wetGearK notRaining (true, true) = -1 ∧ ¬ notRaining (true, true) := by
  have hCant : kernelCant wetGearK notRaining (true, true) = 1 := by
    refine kernelMust_eq_one_iff.2 ⟨?_, ?_⟩
    · rintro ⟨x, hx, hxor⟩
      rcases hx with rfl | hx'
      · rcases hxor with h_sub | h_disj
        · exact h_sub (show onlyRainWets (false, false) from by decide) (by decide)
        · exact Set.disjoint_left.mp h_disj (show onlyRainWets (true, true) from by decide)
            (show ¬ notRaining (true, true) from by decide)
      · obtain rfl : x = wetGear := hx'
        rcases hxor with h_sub | h_disj
        · exact h_sub (show wetGear (true, false) from by decide) (by decide)
        · exact Set.disjoint_left.mp h_disj (show wetGear (true, true) from by decide)
            (show ¬ notRaining (true, true) from by decide)
    · rw [Kernel.followsFrom_iff, wetGearK_base]
      rintro w rfl
      decide
  exact ⟨by rw [wetGearK_base]; rfl, hCant, cant_might_exclusion _ _ _ hCant, by decide⟩

theorem cant_direct_evidence_infelicity (w : World) : kernelCant rainK notRaining w = 0 :=
  kernelMust_eq_zero_iff.2 ⟨raining, by simp [rainK], Or.inl fun _ hw hn ↦ hn hw⟩

end VonFintelGillies2021
