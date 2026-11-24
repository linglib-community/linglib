module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Core.Order.SupClosed

/-!
# Exhaustification and the closure of the alternatives

Closing the alternatives under conjunction and disjunction, or under any part of that closure,
[leaves the minimal worlds unchanged](##Exhaustification.exhMW_eq_of_subset_latticeClosure), since
it leaves unchanged how the alternatives rank worlds. Innocent exclusion is not invariant in that
way, but closing the alternatives
[under disjunction](##Exhaustification.exhIE_sUnion_image_powerset) leaves it unchanged, and
alternatives that [include every conjunction of finitely many propositions and are built from
them by conjunction and disjunction](##Exhaustification.exhIE_eq_exhMW_of_infClosure_subset) give it
the minimal worlds over those propositions. Finitely many alternatives
[closed under conjunction](##Exhaustification.exhMW_eq_exhIE_of_infClosed) are the case where the
propositions are the alternatives themselves.

## Implementation notes

The closure under conjunction and disjunction is `latticeClosure`, the closure under finite meets
and joins, where [spector-2016] closes under the conjunction and disjunction of arbitrary subsets;
the closures under disjunction alone and conjunction alone are stated for arbitrary subsets.

## References

* [spector-2016]
-/

@[expose] public section

namespace Exhaustification

open Set

variable {World : Type*} (ALT : Set (Set World)) (φ : Set World)

variable {ALT φ} in
/-- Alternative sets that rank worlds alike have the same minimal worlds. -/
theorem exhMW_congr {ALT' : Set (Set World)}
    (h : premisePreorder ALT' = premisePreorder ALT) :
    exhMW ALT' φ = exhMW ALT φ := by
  ext u
  simp only [mem_exhMW, MinimalFor, ← Preorder.ofCriteria_le_iff_subset (· ∈ ·)]
  rw [show Preorder.ofCriteria (· ∈ ·) ALT' = Preorder.ofCriteria (· ∈ ·) ALT from h]

theorem exhMW_sUnion_image_powerset : exhMW (sUnion '' 𝒫 ALT) φ = exhMW ALT φ := by
  refine exhMW_congr (Preorder.ofCriteria_eq_of_subset
    (fun a ha ↦ ⟨{a}, singleton_subset_iff.2 ha, sUnion_singleton a⟩) ?_)
  rintro _ ⟨X, hX, rfl⟩ u v h ⟨q, hq, hvq⟩
  exact ⟨q, hq, h q (hX hq) hvq⟩

theorem exhMW_sInter_image_powerset : exhMW (sInter '' 𝒫 ALT) φ = exhMW ALT φ := by
  refine exhMW_congr (Preorder.ofCriteria_eq_of_subset
    (fun a ha ↦ ⟨{a}, singleton_subset_iff.2 ha, sInter_singleton a⟩) ?_)
  rintro _ ⟨X, hX, rfl⟩ u v h hv q hq
  exact h q (hX hq) (hv q hq)

variable {ALT φ} in
/-- Closing the alternatives under conjunction and disjunction, or under any part of that closure,
leaves the minimal worlds unchanged ([spector-2016]): the propositions true at `v` whenever they
are true at `u` form a sublattice. -/
theorem exhMW_eq_of_subset_latticeClosure {S : Set (Set World)} (h₁ : S ⊆ ALT)
    (h₂ : ALT ⊆ latticeClosure S) : exhMW ALT φ = exhMW S φ := by
  refine exhMW_congr (Preorder.ofCriteria_eq_of_subset h₁ fun q hq u v h ↦ ?_)
  have hsub : IsSublattice {q : Set World | v ∈ q → u ∈ q} :=
    ⟨fun _ hp _ hq hv ↦ hv.imp hp hq, fun _ hp _ hq hv ↦ ⟨hp hv.1, hq hv.2⟩⟩
  exact latticeClosure_min h hsub (h₂ hq)

@[simp] theorem exhMW_latticeClosure : exhMW (latticeClosure ALT) φ = exhMW ALT φ :=
  exhMW_eq_of_subset_latticeClosure subset_latticeClosure subset_rfl

variable {ALT φ} in
/-- Alternatives that include every conjunction of finitely many propositions `E`, and are built
from `E` by conjunction and disjunction, give innocent exclusion the minimal worlds over `E`
([spector-2016]). A prejacent world above another verifies the conjunction of the members of `E`
true at it, which every minimal world falsifies. -/
theorem exhIE_eq_exhMW_of_infClosure_subset {E : Set (Set World)} (hfin : E.Finite)
    (h₁ : infClosure E ⊆ ALT) (h₂ : ALT ⊆ latticeClosure E) : exhIE ALT φ = exhMW E φ := by
  have hMW : exhMW ALT φ = exhMW E φ :=
    exhMW_eq_of_subset_latticeClosure (subset_infClosure.trans h₁) h₂
  rw [← hMW]
  refine (exhIE_eq_exhMW_iff ALT φ).2 fun u hu hmin ↦ ?_
  rw [hMW] at hmin ⊢
  obtain ⟨v, hv, hvu, huv⟩ : ∃ v ∈ φ, {a ∈ E | v ∈ a} ⊆
      {a ∈ E | u ∈ a} ∧ ¬ {a ∈ E | u ∈ a} ⊆
        {a ∈ E | v ∈ a} := by
    simpa [mem_exhMW, MinimalFor, hu] using hmin
  have hne : {a ∈ E | u ∈ a}.Nonempty := by
    by_contra h
    exact huv fun a ha ↦ (h ⟨a, ha⟩).elim
  refine ⟨⋂₀ {a ∈ E | u ∈ a}, h₁ (infClosed_infClosure.sInf_mem_of_nonempty
    (hfin.subset fun _ h ↦ h.1) hne fun _ h ↦ subset_infClosure h.1), fun a ha ↦ ha.2,
    fun w hw hwA ↦ huv ?_⟩
  have huw : {a ∈ E | u ∈ a} ⊆ {a ∈ E | w ∈ a} :=
    fun a ha ↦ ⟨ha.1, hwA a ha⟩
  exact huw.trans (hw.2 hv (hvu.trans huw))

/-- With finitely many alternatives closed under conjunction the two exhaustifiers coincide. -/
theorem exhMW_eq_exhIE_of_infClosed (hfin : ALT.Finite) (hinf : InfClosed ALT) :
    exhMW ALT φ = exhIE ALT φ :=
  (exhIE_eq_exhMW_of_infClosure_subset hfin hinf.infClosure_eq.subset subset_latticeClosure).symm

/-- Innocent exclusion is unchanged by closing the alternatives under disjunction, since a
disjunction fails at every minimal world iff each disjunct does. -/
theorem exhIE_sUnion_image_powerset : exhIE (sUnion '' 𝒫 ALT) φ = exhIE ALT φ := by
  ext u
  refine and_congr_right fun _ ↦ ⟨fun h a ha ↦ h a ?_, fun h a ha ↦ ?_⟩
  · have ha' : a ∈ sUnion '' 𝒫 ALT := ⟨{a}, singleton_subset_iff.2 ha.1, sUnion_singleton a⟩
    rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha', exhMW_sUnion_image_powerset]
    exact (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha.1).1 ha
  · obtain ⟨X, hX, rfl⟩ := ha.1
    rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha.1,
      exhMW_sUnion_image_powerset] at ha
    rintro ⟨b, hb, hub⟩
    refine h b ((isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (hX hb)).2 ?_) hub
    exact fun w hw hwb ↦ ha hw ⟨b, hb, hwb⟩

theorem exhMW_eq_exhIE_of_infClosed_sUnion_image (hfin : ALT.Finite)
    (hinf : InfClosed (sUnion '' 𝒫 ALT)) : exhMW ALT φ = exhIE ALT φ := by
  rw [← exhMW_sUnion_image_powerset, ← exhIE_sUnion_image_powerset]
  exact exhMW_eq_exhIE_of_infClosed _ _ (hfin.finite_subsets.image _) hinf

/-- Against the closure of finitely many propositions under conjunction and disjunction, innocent
exclusion keeps the minimal worlds over the propositions themselves ([spector-2016]). -/
theorem exhIE_latticeClosure (hfin : ALT.Finite) : exhIE (latticeClosure ALT) φ = exhMW ALT φ :=
  exhIE_eq_exhMW_of_infClosure_subset hfin
    (infClosure_min subset_latticeClosure isSublattice_latticeClosure.infClosed) subset_rfl

end Exhaustification
