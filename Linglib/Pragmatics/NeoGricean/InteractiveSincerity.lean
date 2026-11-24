module

public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Semantics.Focus.Inquisitive

/-!
# Interactive sincerity and primary implicatures

Two conditions on a speaker's information state derive the ignorance that *at least* conveys. The
Maxim of Interactive Sincerity asks that a proposition with several possibilities keep several
within the state. The neo-Gricean primary implicatures ask that the state be certain of no
alternative stronger than what was asserted. This file relates the two.

For a proposition whose possibilities are pairwise disjoint, a speaker who believes its
informative content satisfies the maxim just in case the state satisfies the primary implicatures
taken with the possibilities themselves as alternatives. The two conditions then differ only
through the alternatives. For *at least `a`* over the exact answers `μ ⁻¹' {d}` to a degree
question, the maxim is the primary implicatures against the exact answers from `a` up. The primary
implicatures against the exact answer at `a` and the comparative `μ ⁻¹' Ioi a` are the maxim
together with the requirement that the state leave the degree `a` itself open.

## Main results

* `NeoGricean.interactiveSincerity_iff_mem_primaryImplicatures`: on disjoint possibilities the
  maxim is the primary implicatures against the possibilities.
* `NeoGricean.interactiveSincerity_atLeast_iff_mem_primaryImplicatures`: the case of *at least*
  over the exact answers to a degree question.
* `NeoGricean.mem_primaryImplicatures_exact_comparative_iff`: the primary implicatures against the
  exact and the comparative alternative are the maxim and that the degree `a` is open.

## Implementation notes

The exact and the comparative alternative are the two that asymmetrically entail *at least `a`*
among the forms of one numeral, the alternatives of [kennedy-2015]. The possibilities raised by
*at least `a`* are those of [coppock-brochhagen-2013].

## References

* [coppock-brochhagen-2013]
* [sauerland-2004]
* [kennedy-2015]
-/

@[expose] public section

namespace NeoGricean

open Set Inquisitive
open Inquisitive.Unrestricted (InteractiveSincerity nontrivial_restrict_iff)

variable {W : Type*} {P : Set (Set W)} {k : Set W}

/-- On pairwise disjoint possibilities, a speaker who believes the informative content of a
proposition satisfies the Maxim of Interactive Sincerity just in case the speaker is certain of
none of its possibilities. -/
theorem interactiveSincerity_iff_mem_primaryImplicatures (hd : P.PairwiseDisjoint id)
    (h0 : ∅ ∉ P) (hP : P.Nontrivial) (hk : k.Nonempty) (hq : k ⊆ ⋃₀ P) :
    InteractiveSincerity P k ↔ k ∈ primaryImplicatures P (⋃₀ P) := by
  rw [mem_primaryImplicatures]
  constructor
  · intro h ψ hψ _ hkψ
    obtain ⟨p, hp, q, hq', ⟨w, hw⟩, ⟨v, hv⟩, hne⟩ := nontrivial_restrict_iff.1 (h hP)
    have hpψ : ψ = p := hd.elim_set hψ hp w (hkψ hw.1) hw.2
    have hqψ : ψ = q := hd.elim_set hψ hq' v (hkψ hv.1) hv.2
    exact hne (by rw [← hpψ, ← hqψ])
  · intro h _
    obtain ⟨w, hw⟩ := hk
    obtain ⟨p, hp, hwp⟩ := hq hw
    obtain ⟨q, hq', hqp⟩ := hP.exists_ne p
    obtain ⟨u, hu⟩ : q.Nonempty := nonempty_iff_ne_empty.2 (by rintro rfl; exact h0 hq')
    have hup : u ∉ p := fun hup ↦ hqp (hd.elim_set hq' hp u hu hup)
    have hpss : p ⊂ ⋃₀ P := ⟨subset_sUnion_of_mem hp, fun hsub ↦ hup (hsub ⟨q, hq', hu⟩)⟩
    obtain ⟨v, hvk, hvp⟩ := not_subset.1 (h p hp hpss)
    obtain ⟨r, hr, hvr⟩ := hq hvk
    exact nontrivial_restrict_iff.2 ⟨p, hp, r, hr, ⟨w, hw, hwp⟩, ⟨v, hvk, hvr⟩,
      fun e ↦ hvp (e.symm.subset ⟨hvk, hvr⟩).2⟩

/-! ### Degree questions -/

variable {α : Type*} [PartialOrder α] {μ : W → α} {a c : α}

/-- Over the exact answers to a degree question, a speaker who believes *at least `a`* satisfies
the Maxim of Interactive Sincerity just in case the speaker is certain of no exact answer from `a`
up. -/
theorem interactiveSincerity_atLeast_iff_mem_primaryImplicatures (hμ : Function.Surjective μ)
    (hac : a < c) (hk : k.Nonempty) (hq : k ⊆ μ ⁻¹' Ici a) :
    InteractiveSincerity (Unrestricted.atLeast (· ≥ ·) univ (fun d ↦ μ ⁻¹' {d}) a) k ↔
      k ∈ primaryImplicatures ((fun d ↦ μ ⁻¹' {d}) '' Ici a) (μ ⁻¹' Ici a) := by
  have hU : ⋃₀ ((fun d ↦ μ ⁻¹' {d}) '' Ici a) = μ ⁻¹' Ici a := by
    rw [sUnion_image, ← preimage_iUnion₂, biUnion_of_singleton]
  have hne : ∀ {d e : α}, μ ⁻¹' {d} = μ ⁻¹' {e} → d = e := fun {d e} h ↦ by
    obtain ⟨w, rfl⟩ := hμ d
    exact h.subset (rfl : w ∈ μ ⁻¹' {μ w})
  rw [Unrestricted.atLeast_ge_univ, ← hU]
  refine interactiveSincerity_iff_mem_primaryImplicatures ?_ ?_ ?_ hk (hU ▸ hq)
  · rintro _ ⟨d, -, rfl⟩ _ ⟨e, -, rfl⟩ h
    exact Disjoint.preimage μ (disjoint_singleton.2 fun hde ↦ h (by rw [hde]))
  · rintro ⟨d, -, hd⟩
    obtain ⟨w, rfl⟩ := hμ d
    exact (hd.subset (rfl : w ∈ μ ⁻¹' {μ w}) : w ∈ (∅ : Set W))
  · exact ⟨_, mem_image_of_mem _ self_mem_Ici, _, mem_image_of_mem _ hac.le,
      fun h ↦ hac.ne (hne h)⟩

/-- The primary implicatures of *at least `a`* against the exact answer at `a` and the comparative
*more than `a`* hold of a speaker who believes it just in case the Maxim of Interactive Sincerity
does and the speaker's state leaves the degree `a` open. -/
theorem mem_primaryImplicatures_exact_comparative_iff (hμ : Function.Surjective μ) (hac : a < c)
    (hq : k ⊆ μ ⁻¹' Ici a) :
    k ∈ primaryImplicatures {μ ⁻¹' {a}, μ ⁻¹' Ioi a} (μ ⁻¹' Ici a) ↔
      InteractiveSincerity (Unrestricted.atLeast (· ≥ ·) univ (fun d ↦ μ ⁻¹' {d}) a) k ∧
        a ∈ μ '' k := by
  obtain ⟨wa, hwa⟩ := hμ a
  obtain ⟨wc, hwc⟩ := hμ c
  have hA : μ ⁻¹' {a} ⊂ μ ⁻¹' Ici a := by
    refine ⟨preimage_mono (singleton_subset_iff.2 self_mem_Ici), fun h ↦ ?_⟩
    have hc : wc ∈ μ ⁻¹' {a} := h (by rw [mem_preimage, hwc]; exact hac.le)
    rw [mem_preimage, hwc] at hc
    exact hac.ne' hc
  have hB : μ ⁻¹' Ioi a ⊂ μ ⁻¹' Ici a := by
    refine ⟨preimage_mono Ioi_subset_Ici_self, fun h ↦ ?_⟩
    have ha : wa ∈ μ ⁻¹' Ioi a := h (by rw [mem_preimage, hwa]; exact self_mem_Ici)
    rw [mem_preimage, hwa] at ha
    exact lt_irrefl a ha
  have hL : k ∈ primaryImplicatures {μ ⁻¹' {a}, μ ⁻¹' Ioi a} (μ ⁻¹' Ici a) ↔
      ¬ k ⊆ μ ⁻¹' {a} ∧ ¬ k ⊆ μ ⁻¹' Ioi a := by
    simp only [mem_primaryImplicatures, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq, imp_iff_right hA, imp_iff_right hB]
  rw [hL]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨v, hvk, hv⟩ := not_subset.1 h2
    have hva : a = μ v := eq_of_le_of_not_lt (hq hvk) hv
    refine ⟨(interactiveSincerity_atLeast_iff_mem_primaryImplicatures hμ hac ⟨v, hvk⟩ hq).2
      (mem_primaryImplicatures.2 ?_), v, hvk, hva.symm⟩
    rintro _ ⟨d, -, rfl⟩ - hkd
    have hd : μ v = d := hkd hvk
    exact h1 (by rw [hva, hd]; exact hkd)
  · rintro ⟨hIS, v, hvk, hva⟩
    have h := mem_primaryImplicatures.1
      ((interactiveSincerity_atLeast_iff_mem_primaryImplicatures hμ hac ⟨v, hvk⟩ hq).1 hIS)
    refine ⟨h _ (mem_image_of_mem _ self_mem_Ici) hA, fun hk ↦ ?_⟩
    have hv : v ∈ μ ⁻¹' Ioi a := hk hvk
    rw [mem_preimage, hva] at hv
    exact lt_irrefl a hv

end NeoGricean
