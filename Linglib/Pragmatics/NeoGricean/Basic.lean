module

public import Linglib.Semantics.Exhaustification.MinimalWorlds
public import Linglib.Semantics.Questions.Polar
public import Mathlib.Order.SupClosed

/-!
# Neo-Gricean pragmatics: primary and secondary implicatures

The epistemic step of neo-Gricean scalar reasoning, after Sauerland's primary and secondary
implicatures and Geurts's Standard Recipe. A speaker's epistemic state is a set of worlds
`s : Set W`, and an epistemic proposition, what an utterance implicates about the speaker, is a
set of states `Set (Set W)`. Certainty `Kφ` is the principal down-set `Set.Iic φ`, so the primary
implicature `¬Kψ` is `(Set.Iic ψ)ᶜ` and the secondary implicature `K¬ψ` is `Set.Iic ψᶜ`, and
competence `Kψ ∨ K¬ψ` is resolving the polar question `Question.polar ψ`. The empty state, a
member of every `Set.Iic`, is the inconsistent speaker.

Asserting `φ` implicates `Kφ` by Quality and the primary implicature `¬Kψ` of each alternative
`ψ` that asymmetrically entails `φ`; for such a `ψ`, `K¬ψ` is a secondary implicature iff it is
consistent with `Kφ` and all the primary implicatures.

The speaker's side of the same condition is `NeoGricean.IsOptimal`: asserting `φ` is optimal in
the states satisfying Quality and the primary implicatures. Where every world of the assertion
lies above a minimal one, as over finitely many alternatives, the assertion is optimal in the
state of its minimal worlds, `Exhaustification.exhMW`, and when the alternatives include the
assertion and are closed under intersection and nonempty unions that state is the most informed
one: every consistent state in which the assertion is optimal contains a world making the same
alternatives true as each minimal world.

## Main definitions

* `NeoGricean.primaryImplicatures`: the primary implicatures of the stronger alternatives,
  conjoined.
* `NeoGricean.IsSecondaryImplicature`: the consistency condition on `K¬ψ`.
* `NeoGricean.IsOptimal`: the assertion is optimal for a speaker in a state.

## Main statements

* `NeoGricean.isSecondaryImplicature_iff`: `K¬ψ` is a secondary implicature iff `φ \ ψ` entails
  no stronger alternative.
* `NeoGricean.compl_Iic_inter_polar`: the Standard Recipe.
* `NeoGricean.isOptimal_exhMW`, `NeoGricean.IsOptimal.exists_satisfied_eq`: the assertion is
  optimal in the state of its minimal worlds, the most informed state in which it is.

## Implementation notes

The assertion enters the consistency check as `Kφ`, by Quality, as in Sauerland's own
derivation for disjunction; against the bare proposition `φ` the secondary implicature `K¬A` of
*A or B* would not be blocked.

`Kφ` and the primary implicatures are the hearer's inferences about the speaker's beliefs, not
public commitments in the sense of `Commitment.committed`. The two meet at Quality, where Sincerity
turns the speaker's commitment to the asserted `φ` into the belief `Kφ`.

## References

* [sauerland-2004]
* [geurts-2010]
* [soames-1982]
* [horn-1989]
* [vanrooij-schulz-2004]
* [spector-2006]
* [spector-2007]
-/

@[expose] public section

namespace NeoGricean

open Set

variable {W ι : Type*} {s φ ψ : Set W} {alts : Set (Set W)}

/-! ### Primary and secondary implicatures -/

/-- The primary implicatures of `φ` against `alts`, conjoined: the states not certain of any
alternative that asymmetrically entails `φ` ([sauerland-2004] (42)). -/
def primaryImplicatures (alts : Set (Set W)) (φ : Set W) : Set (Set W) :=
  ⋂ ψ ∈ alts ∩ Iio φ, (Iic ψ)ᶜ

@[simp] theorem mem_primaryImplicatures :
    s ∈ primaryImplicatures alts φ ↔ ∀ ψ ∈ alts, ψ ⊂ φ → ¬ s ⊆ ψ := by
  simp [primaryImplicatures]

/-- `K¬ψ` is a secondary implicature of asserting `φ` against `alts` iff `¬Kψ` is a primary
implicature and `K¬ψ` is consistent with `Kφ` and all the primary implicatures
([sauerland-2004] (43)). -/
def IsSecondaryImplicature (alts : Set (Set W)) (φ ψ : Set W) : Prop :=
  ψ ∈ alts ∧ ψ ⊂ φ ∧ ((Iic φ ∩ primaryImplicatures alts φ ∩ Iic ψᶜ) \ {∅}).Nonempty

/-- The strengthened meaning `φ \ ψ` is the canonical witness: `K¬ψ` is a secondary implicature
iff `φ \ ψ` entails no stronger alternative, so a blocked secondary implicature is always
blocked by a single primary one. -/
theorem isSecondaryImplicature_iff : IsSecondaryImplicature alts φ ψ ↔
    ψ ∈ alts ∧ ψ ⊂ φ ∧ ∀ χ ∈ alts, χ ⊂ φ → ¬ φ \ ψ ⊆ χ := by
  refine and_congr_right fun _ ↦ and_congr_right fun hψ ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨s, ⟨⟨hφ, hprim⟩, hs⟩, -⟩ χ hχ hχφ hsub
    exact mem_primaryImplicatures.1 hprim χ hχ hχφ fun w hw ↦ hsub ⟨hφ hw, hs hw⟩
  · exact ⟨φ \ ψ, ⟨⟨sdiff_subset, mem_primaryImplicatures.2 h⟩, fun _ hw ↦ hw.2⟩,
      (sdiff_nonempty.2 hψ.2).ne_empty⟩

theorem isSecondaryImplicature_range_iff {f : ι → Set W} {i : ι} :
    IsSecondaryImplicature (range f) φ (f i) ↔ f i ⊂ φ ∧ ∀ j, f j ⊂ φ → ¬ φ \ f i ⊆ f j := by
  simp [isSecondaryImplicature_iff]

theorem isSecondaryImplicature_singleton : IsSecondaryImplicature {ψ} φ ψ ↔ ψ ⊂ φ := by
  simp only [isSecondaryImplicature_iff, mem_singleton_iff, forall_eq, true_and,
    and_iff_left_iff_imp]
  exact fun h _ hsub ↦ h.2 fun w hw ↦ by_contra fun hψ ↦ hψ (hsub ⟨hw, hψ⟩)

/-! ### Competence and the Standard Recipe -/

/-- The Standard Recipe: on consistent states, the weak implicature `¬Kψ` together with
competence about `ψ`, resolving the polar question whether `ψ`, is the strong implicature
`K¬ψ`. -/
theorem compl_Iic_inter_polar (ψ : Set W) :
    (Iic ψ)ᶜ ∩ Question.polar ψ = Iic ψᶜ \ {∅} := by
  ext s
  simp only [mem_inter_iff, mem_compl_iff, mem_Iic, SetLike.mem_coe, Question.mem_polar,
    mem_sdiff, mem_singleton_iff]
  refine ⟨fun ⟨h, hc⟩ ↦ ⟨hc.resolve_left h, fun he ↦ h (he ▸ empty_subset ψ)⟩,
    fun ⟨hψ, hs⟩ ↦ ⟨fun h ↦ ?_, Or.inr hψ⟩⟩
  obtain ⟨w, hw⟩ := nonempty_iff_ne_empty.2 hs
  exact hψ hw (h hw)

/-! ### Optimal assertions -/

/-- Asserting `φ` is optimal for a speaker in the state `s`, against the alternatives `alts`,
when she is certain of `φ` and of no alternative that asymmetrically entails it: [spector-2007]'s
optimal answer, at the question that separates every two worlds. -/
@[mk_iff] structure IsOptimal (alts : Set (Set W)) (φ s : Set W) : Prop where
  /-- Quality: the speaker is certain of what she asserts. -/
  subset : s ⊆ φ
  /-- Quantity: she is certain of no stronger alternative. -/
  not_ssubset : ∀ ψ ∈ alts, s ⊆ ψ → ¬ ψ ⊂ φ

/-- The assertion is optimal in the states that satisfy Quality and the primary implicatures. -/
theorem isOptimal_iff_mem : IsOptimal alts φ s ↔ s ∈ Iic φ ∩ primaryImplicatures alts φ := by
  rw [isOptimal_iff, mem_inter_iff, mem_primaryImplicatures]
  exact and_congr_right fun _ ↦ ⟨fun h ψ hψ hlt hsub ↦ h ψ hψ hsub hlt,
    fun h ψ hψ hsub hlt ↦ h ψ hψ hlt hsub⟩

/-! ### Minimal worlds -/

section MinimalWorlds

open Exhaustification

/-- Where every world of the assertion lies above a minimal one, as over finitely many
alternatives, the assertion is optimal in the state of its minimal worlds. -/
theorem isOptimal_exhMW (h : ∀ w ∈ φ, ∃ u ∈ exhMW alts φ,
    Preorder.satisfied (· ∈ ·) alts u ⊆ Preorder.satisfied (· ∈ ·) alts w) :
    IsOptimal alts φ (exhMW alts φ) :=
  ⟨exhMW_subset, fun _ hψ hsub hψφ ↦ hψφ.2 fun w hw ↦
    let ⟨_, hu, huw⟩ := h w hw
    (huw ⟨hψ, hsub hu⟩).2⟩

variable (hinf : InfClosed alts) (hsup : ∀ A ⊆ alts, A.Nonempty → ⋃₀ A ∈ alts) (hφ : φ ∈ alts)
  (hne : s.Nonempty) (hs : IsOptimal alts φ s)
include hinf hsup hφ hne hs

/-- When the alternatives include the assertion and are closed under intersection and nonempty
unions, a consistent state in which the assertion is optimal contains, for each minimal world of
the assertion, a world making the same alternatives true. -/
theorem IsOptimal.exists_satisfied_eq {u : W} (hu : u ∈ exhMW alts φ) :
    ∃ w ∈ s, Preorder.satisfied (· ∈ ·) alts w = Preorder.satisfied (· ∈ ·) alts u := by
  by_contra hcon
  have hA : ∀ w ∈ s, ∃ a ∈ alts, w ∈ a ∧ u ∉ a := fun w hw ↦ by
    by_contra h
    have hle : Preorder.satisfied (· ∈ ·) alts w ⊆ Preorder.satisfied (· ∈ ·) alts u :=
      fun a ha ↦ ⟨ha.1, by_contra fun hua ↦ h ⟨a, ha.1, ha.2, hua⟩⟩
    exact hcon ⟨w, hw, hle.antisymm (hu.2 (hs.subset hw) hle)⟩
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨a₀, ha₀, -, hua₀⟩ := hA w₀ hw₀
  have hmem : ⋃₀ {a ∈ alts | u ∉ a} ∩ φ ∈ alts :=
    hinf (hsup _ (sep_subset _ _) ⟨a₀, ha₀, hua₀⟩) hφ
  refine hs.not_ssubset _ hmem (fun w hw ↦ ?_) ⟨inter_subset_right, fun h ↦ ?_⟩
  · obtain ⟨a, ha, hwa, hua⟩ := hA w hw
    exact ⟨⟨a, ⟨ha, hua⟩, hwa⟩, hs.subset hw⟩
  · obtain ⟨a, ha, hua⟩ := (h hu.1).1
    exact ha.2 hua

/-- Under the same closure conditions the minimal worlds are the most informed state in which the
assertion is optimal: they entail every alternative that a consistent such state entails. -/
theorem IsOptimal.exhMW_subset (hψ : ψ ∈ alts) (hsψ : s ⊆ ψ) : exhMW alts φ ⊆ ψ := fun _ hu ↦
  let ⟨_, hw, h⟩ := hs.exists_satisfied_eq hinf hsup hφ hne hu
  (h.subset ⟨hψ, hsψ hw⟩).2

/-- And they exclude every alternative that such a state excludes. -/
theorem IsOptimal.exhMW_subset_compl (hψ : ψ ∈ alts) (hsψ : s ⊆ ψᶜ) :
    exhMW alts φ ⊆ ψᶜ := fun _ hu huψ ↦
  let ⟨_, hw, h⟩ := hs.exists_satisfied_eq hinf hsup hφ hne hu
  hsψ hw (h.superset ⟨hψ, huψ⟩).2

end MinimalWorlds

end NeoGricean
