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
base entails the negation of the prejacent, the thesis S2. On the worked kernel of the earlier
paper *can't not-blue* is defined, true, and excludes *might not-blue* at once, the joint
profile the Mantra cannot assign (`cant_dilemma_resolved`), and direct information that settles
the prejacent gives *can't* presupposition failure as it does *must*. The anti-knowledge
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

/-- `⟦not blue⟧`. -/
abbrev notBlue : World → Prop := (· ≠ .w1)

variable {W : Type*} (k : Kernel W) (φ : W → Prop) (w : W)

/-- When can't `φ` is true (`B_K ⊆ ⟦¬φ⟧`), might `φ` is false (Observation 5). -/
theorem cant_might_exclusion (hCant : kernelCant k φ w = 1) : kernelMight k φ w = -1 := by
  rw [kernelMight_eq_neg_kernelCant, Pi.neg_apply, hCant]

theorem cant_entails_negation (hReal : w ∈ k.base) (hTrue : kernelCant k φ w = 1) : ¬ φ w :=
  must_entails_prejacent k _ w hReal (kernelMust_eq_one_iff.1 hTrue).2

theorem cant_dilemma_resolved :
    .w1 ∈ mastermindK.base ∧ kernelCant mastermindK notBlue .w1 = 1 ∧
      kernelMight mastermindK notBlue .w1 = -1 ∧ ¬ notBlue .w1 := by
  have hCant : kernelCant mastermindK notBlue .w1 = 1 := by
    refine kernelMust_eq_one_iff.2 ⟨?_, ?_⟩
    · rintro ⟨x, hx, hxor⟩
      rcases hx with rfl | hx'
      · rcases hxor with h_sub | h_disj
        · exact h_sub (show redOrBlue .w0 from by decide) (by decide)
        · exact Set.disjoint_left.mp h_disj (show redOrBlue .w1 from by decide)
            (show ¬ notBlue .w1 from by decide)
      · obtain rfl : x = notRed := hx'
        rcases hxor with h_sub | h_disj
        · exact h_sub (show notRed .w2 from by decide) (by decide)
        · exact Set.disjoint_left.mp h_disj (show notRed .w1 from by decide)
            (show ¬ notBlue .w1 from by decide)
    · rw [Kernel.followsFrom_iff, mastermind_base]
      rintro w rfl
      decide
  exact ⟨by rw [mastermind_base]; rfl, hCant, cant_might_exclusion _ _ _ hCant, by decide⟩

theorem cant_direct_evidence_infelicity : kernelCant mastermindK red .w0 = 0 :=
  kernelMust_eq_zero_iff.2 ⟨notRed, by simp [mastermindK], Or.inl fun _ hw ↦ hw⟩

end VonFintelGillies2021
