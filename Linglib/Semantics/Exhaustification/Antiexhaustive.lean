module

public import Linglib.Core.Order.SupClosed
public import Mathlib.Basic.Rel

/-!
# Antiexhaustive enrichment

This file defines Chierchia's antiexhaustive enrichment `antiExh F D` of a proposition `F` that
depends on a domain: `F D` holds, and `F` holds of no nonempty subdomain without holding of every
nonempty subdomain disjoint from it. The implicature is a zero-one law: the alternatives over the
nonempty proper subdomains are all true or all false. Over an existential only the first case is
consistent, which gives universal force over the domain; under an antitone operator the
enrichment is vacuous; under a necessity modal the second case makes every member an option.

## Main statements

* `Exhaustification.mem_antiExh_iff`: the zero-one law.
* `Exhaustification.antiExh_biUnion`: over an existential the enrichment is the universal.
* `Exhaustification.antiExh_eq_of_antitone`: under an antitone operator it is vacuous.

## References

* [chierchia-2006]
-/

@[expose] public section

namespace Exhaustification

variable {W E : Type*}

section Antiexhaustive

variable {F : Finset E → Set W} {D S T : Finset E} {w : W}

/-- The antiexhaustive enrichment `O⁻` of the domain-dependent proposition `F` over the domain
`D`, (108c), holds where `F D` holds and `F` holds of no nonempty subdomain without holding of
every nonempty subdomain disjoint from it. -/
def antiExh (F : Finset E → Set W) (D : Finset E) : Set W :=
  F D ∩ {w | ∀ S ⊆ D, ∀ T ⊆ D, S.Nonempty → T.Nonempty → Disjoint S T → w ∈ F S → w ∈ F T}

theorem antiExh_subset : antiExh F D ⊆ F D := Set.inter_subset_left

/-- Where the enrichment holds, the alternatives over any two members of the domain agree. -/
theorem mem_iff_mem_of_mem_antiExh (h : w ∈ antiExh F D) {i j : E} (hi : i ∈ D) (hj : j ∈ D) :
    w ∈ F {i} ↔ w ∈ F {j} := by
  obtain rfl | hij := eq_or_ne i j
  · rfl
  exact ⟨h.2 {i} (by simpa) {j} (by simpa) (by simp) (by simp) (Finset.disjoint_singleton.2 hij),
    h.2 {j} (by simpa) {i} (by simpa) (by simp) (by simp) (Finset.disjoint_singleton.2 hij.symm)⟩

theorem notMem_antiExh_of_singleton {i j : E} (hi : i ∈ D) (hj : j ∈ D) (hwi : w ∈ F {i})
    (hwj : w ∉ F {j}) : w ∉ antiExh F D :=
  fun h ↦ hwj ((mem_iff_mem_of_mem_antiExh h hi hj).1 hwi)

private theorem ssubset_of_disjoint (hS : S ⊆ D) (hS' : S.Nonempty) (hT : T ⊆ D)
    (hST : Disjoint S T) : T ⊂ D :=
  hT.ssubset_of_not_subset fun h ↦
    let ⟨_, hx⟩ := hS'; Finset.disjoint_left.1 hST hx (h (hS hx))

/-- The antiexhaustive implicature is a zero-one law: the alternatives over the nonempty proper
subdomains are all true or all false. -/
theorem mem_antiExh_iff : w ∈ antiExh F D ↔ w ∈ F D ∧
    ((∀ S ⊂ D, S.Nonempty → w ∈ F S) ∨ ∀ S ⊂ D, S.Nonempty → w ∉ F S) := by
  refine ⟨fun h ↦ ⟨h.1, or_iff_not_imp_right.2 fun hn T hT hT' ↦ ?_⟩, ?_⟩
  · obtain ⟨S, hS, hS', hwS⟩ : ∃ S ⊂ D, S.Nonempty ∧ w ∈ F S := by simpa using hn
    obtain ⟨b, hb, hbS⟩ := Finset.exists_of_ssubset hS
    obtain ⟨c, hc, hcT⟩ := Finset.exists_of_ssubset hT
    refine h.2 {c} (by simpa) T hT.subset (by simp) hT' (Finset.disjoint_singleton_left.2 hcT)
      ((mem_iff_mem_of_mem_antiExh h hb hc).1 ?_)
    exact h.2 S hS.subset {b} (by simpa) hS' (by simp) (Finset.disjoint_singleton_right.2 hbS) hwS
  · rintro ⟨hD, h | h⟩
    · exact ⟨hD, fun S hS T hT hS' hT' hST _ ↦ h T (ssubset_of_disjoint hS hS' hT hST) hT'⟩
    · exact ⟨hD, fun S hS T hT hS' hT' hST hwS ↦
        absurd hwS (h S (ssubset_of_disjoint hT hT' hS hST.symm) hS')⟩

/-- A statement that entails each of its variants carries a vacuous antiexhaustive implicature,
(66). -/
theorem antiExh_eq_self (h : ∀ T ⊆ D, T.Nonempty → F D ⊆ F T) : antiExh F D = F D :=
  Set.inter_eq_left.2 fun _ hw _ _ T hT _ hT' _ _ ↦ h T hT hT' hw

variable (P : E → Set W)

/-- Antiexhaustive enrichment gives an existential universal force over its domain, (63c)–(63d),
which negation over σ denies, (64). -/
theorem antiExh_biUnion (hD : D.Nonempty) :
    antiExh (fun S ↦ ⋃ a ∈ S, P a) D = ⋂ a ∈ D, P a := by
  refine Set.Subset.antisymm (fun w h ↦ Set.mem_iInter₂.2 fun a ha ↦ ?_) fun w hw ↦ ?_
  · obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 h.1
    simpa using (mem_iff_mem_of_mem_antiExh h hx ha).1 (by simpa)
  · obtain ⟨a, ha⟩ := hD
    have h := Set.mem_iInter₂.1 hw
    exact ⟨Set.mem_biUnion ha (h a ha), fun _ _ T hT _ ⟨b, hb⟩ _ _ ↦
      Set.mem_biUnion hb (h b (hT hb))⟩

/-- On an existential the implicature says that the alternative over each nonempty proper subdomain
implies the alternative over the rest of the domain, the form in which footnote 29 negates the
exhaustified alternatives. -/
theorem mem_antiExh_biUnion_iff [DecidableEq E] {w : W} :
    w ∈ antiExh (fun S ↦ ⋃ a ∈ S, P a) D ↔ w ∈ ⋃ a ∈ D, P a ∧
      ∀ S ⊂ D, S.Nonempty → w ∈ ⋃ a ∈ S, P a → w ∈ ⋃ a ∈ D \ S, P a := by
  refine ⟨fun h ↦ ⟨h.1, fun S hS hS' ↦ h.2 S hS.subset _ Finset.sdiff_subset hS'
    (Finset.sdiff_nonempty.2 hS.not_subset) Finset.disjoint_sdiff⟩, fun ⟨hw, h⟩ ↦ ?_⟩
  obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 hw
  rw [antiExh_biUnion P ⟨x, hx⟩]
  refine Set.mem_iInter₂.2 fun a ha ↦ ?_
  obtain rfl | hxa := eq_or_ne x a
  · exact hPx
  have hxS : x ∈ D.erase a := Finset.mem_erase.2 ⟨hxa, hx⟩
  simpa [Finset.sdiff_erase_self ha] using
    h _ (Finset.erase_ssubset ha) ⟨x, hxS⟩ (Set.mem_biUnion hxS hPx)

/-- On an existential the simpler (62) agrees with (108c), the enrichment asserting the statement
and every alternative over a nonempty subdomain, as in (63c). -/
theorem antiExh_biUnion_eq_inter_sInter (hD : D.Nonempty) :
    antiExh (fun S ↦ ⋃ a ∈ S, P a) D = (⋃ a ∈ D, P a) ∩ ⋂₀ supClosure (P '' D) := by
  obtain ⟨a, ha⟩ := hD
  rw [antiExh_biUnion P ⟨a, ha⟩, Set.sInter_supClosure, Set.sInter_image]
  simp only [Finset.mem_coe]
  exact (Set.inter_eq_right.2 fun w hw ↦ Set.mem_biUnion ha (Set.mem_iInter₂.1 hw a ha)).symm

/-- With σ over negation, (65)–(66), the statement entails every variant, so the free-choice
implicature vanishes and *any* acts as a negative-polarity item. -/
theorem antiExh_eq_of_antitone {C : Set W → Set W} (hC : Antitone C) :
    antiExh (fun S ↦ C (⋃ a ∈ S, P a)) D = C (⋃ a ∈ D, P a) :=
  antiExh_eq_self fun _ hT _ ↦ hC (Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 hT))

/-- Under an antitone context the strong σ's presupposition (72) fails, so *qualunque* has no
negative-polarity construal (70). -/
theorem not_antiExh_ssubset_of_antitone {C : Set W → Set W} (hC : Antitone C) :
    ¬ antiExh (fun S ↦ C (⋃ a ∈ S, P a)) D ⊂ C (⋃ a ∈ D, P a) := by
  rw [antiExh_eq_of_antitone P hC]
  exact ssubset_irrefl _

/-- In a positive context, antiexhaustive enrichment properly strengthens the statement (71). -/
theorem antiExh_ssubset {a b : E} {w : W} (ha : a ∈ D) (hb : b ∈ D) (hPa : w ∈ P a)
    (hPb : w ∉ P b) : antiExh (fun S ↦ ⋃ a ∈ S, P a) D ⊂ ⋃ a ∈ D, P a :=
  (Set.ssubset_iff_of_subset fun _ h ↦ h.1).2 ⟨w, Set.mem_biUnion ha hPa, fun h ↦
    hPb (Set.mem_iInter₂.1 (antiExh_biUnion P ⟨a, ha⟩ ▸ h) b hb)⟩

/-- Under a possibility modal, antiexhaustive enrichment makes every domain member a witness in
some accessible world, as in (83)–(85). -/
theorem antiExh_preimage_biUnion (R : SetRel W W) (hD : D.Nonempty) :
    antiExh (fun S ↦ R.preimage (⋃ a ∈ S, P a)) D = ⋂ a ∈ D, R.preimage (P a) := by
  simp only [SetRel.preimage_iUnion]
  exact antiExh_biUnion _ hD

/-- Under a necessity modal, antiexhaustive enrichment makes every member of a domain of two or
more an option, (93c)–(93d). -/
theorem antiExh_core_biUnion_inter_dom_subset {R : SetRel W W} (hD : 1 < D.card) :
    antiExh (fun S ↦ R.core (⋃ a ∈ S, P a)) D ∩ R.dom ⊆ ⋂ a ∈ D, R.preimage (P a) := by
  classical
  refine fun w ⟨⟨hall, h⟩, v, hv⟩ ↦ Set.mem_iInter₂.2 fun a ha ↦ by_contra fun hna ↦ ?_
  have hne : (D.erase a).Nonempty := Finset.card_pos.1 (by rw [Finset.card_erase_of_mem ha]; omega)
  have hrest : w ∈ R.core (⋃ x ∈ D.erase a, P x) := fun u hu ↦
    let ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 (hall hu)
    Set.mem_biUnion (Finset.mem_erase.2 ⟨fun hxa ↦ hna ⟨u, hxa ▸ hPx, hu⟩, hx⟩) hPx
  obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 (h _ (Finset.erase_subset a D) {a} (by simpa) hne
    (by simp) (Finset.disjoint_singleton_right.2 (Finset.notMem_erase a D)) hrest hv)
  exact hna ⟨v, Finset.mem_singleton.1 hx ▸ hPx, hv⟩

end Antiexhaustive

end Exhaustification
