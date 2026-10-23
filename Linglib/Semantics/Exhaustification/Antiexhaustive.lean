module

public import Linglib.Semantics.Exhaustification.Disjunctive
public import Mathlib.Basic.Rel

/-!
# Antiexhaustive enrichment

The antiexhaustive enrichment `O⁻` of a domain-dependent proposition over a domain holds where
the proposition holds over the domain and holds of no nonempty subdomain without holding of every
nonempty subdomain disjoint from it. Over an existential it gives universal force over the
domain, the free-choice reading of *any*; under negation or any antitone operator it is vacuous;
under a necessity modal it makes every member of the domain an option; and an actualist episodic
existential over a domain wider than what exists is never enriched consistently. These are the
free-choice and subtrigging facts of Chierchia's account of polarity-sensitive items.

## Main statements

* `Exhaustification.oMinus_biUnion`: over an existential the enrichment is the universal.
* `Exhaustification.oMinus_core_biUnion_subset`: under a necessity modal every member of the
  domain is an option.
* `Exhaustification.oMinus_biUnion_eq_empty_of_isActualist`: an actualist episodic existential
  over a widened domain is contradictory.

## References

* [chierchia-2006]
-/

@[expose] public section

namespace Exhaustification

variable {W E : Type*}

/-! ### The enrichment -/

section Antiexhaustive

variable {D : Finset E} {F : Finset E → Set W}

/-- The antiexhaustive enrichment `O⁻` of the domain-dependent proposition `F` over the domain
`D`, (108c), holds where `F D` holds and `F` holds of no nonempty subdomain without holding of
every nonempty subdomain disjoint from it. -/
def oMinus (F : Finset E → Set W) (D : Finset E) : Set W :=
  F D ∩ {w | ∀ S ⊆ D, ∀ T ⊆ D, S.Nonempty → T.Nonempty → Disjoint S T → w ∈ F S → w ∈ F T}

theorem oMinus_subset : oMinus F D ⊆ F D := Set.inter_subset_left

/-- A statement that entails each of its variants carries a vacuous antiexhaustive implicature,
(66). -/
theorem oMinus_eq_self (h : ∀ T ⊆ D, T.Nonempty → F D ⊆ F T) : oMinus F D = F D :=
  Set.inter_eq_left.2 fun _ hw _ _ T hT _ hT' _ _ ↦ h T hT hT' hw

theorem mem_oMinus_of_forall_ne {w : W} (hD : w ∈ F D)
    (h : ∀ S ∈ D.powerset, S ≠ D → S.Nonempty → w ∉ F S) : w ∈ oMinus F D :=
  ⟨hD, fun S hS _ hT hS' ⟨_, ht⟩ hST hwS ↦ absurd hwS <| h S (Finset.mem_powerset.2 hS)
    (fun h ↦ Finset.disjoint_left.1 hST (h ▸ hT ht) ht) hS'⟩

theorem mem_oMinus_of_forall_subset {w : W} (h : ∀ T ⊆ D, T.Nonempty → w ∈ F T)
    (hD : w ∈ F D) : w ∈ oMinus F D :=
  ⟨hD, fun _ _ T hT _ hT' _ _ ↦ h T hT hT'⟩

theorem notMem_oMinus {w : W} {S T : Finset E} (hS : S ⊆ D) (hT : T ⊆ D) (hS' : S.Nonempty)
    (hT' : T.Nonempty) (hST : Disjoint S T) (hwS : w ∈ F S) (hwT : w ∉ F T) : w ∉ oMinus F D :=
  fun h ↦ hwT (h.2 S hS T hT hS' hT' hST hwS)

theorem notMem_oMinus_of_singleton {w : W} {i j : E} (hi : i ∈ D) (hj : j ∈ D) (hij : i ≠ j)
    (hwi : w ∈ F {i}) (hwj : w ∉ F {j}) : w ∉ oMinus F D :=
  notMem_oMinus (by simpa) (by simpa) (by simp) (by simp) (Finset.disjoint_singleton.2 hij)
    hwi hwj

variable (P : E → Set W)

/-- Antiexhaustive enrichment gives an existential universal force over its domain, (63c)–(63d):
*I saw any student* says that every possible student was seen. Negation over σ denies this
universal, the rhetorical reading (64). -/
theorem oMinus_biUnion (hD : D.Nonempty) : oMinus (fun S ↦ ⋃ a ∈ S, P a) D = ⋂ a ∈ D, P a := by
  classical
  refine Set.Subset.antisymm (fun w ⟨hw, h⟩ ↦ Set.mem_iInter₂.2 fun a ha ↦ ?_) fun w hw ↦ ?_
  · obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 hw
    by_cases hxa : x = a
    · exact hxa ▸ hPx
    · simpa using h {x} (by simpa) {a} (by simpa) (by simp) (by simp)
        (Finset.disjoint_singleton.2 hxa) (by simpa)
  · obtain ⟨a, ha⟩ := hD
    have h := Set.mem_iInter₂.1 hw
    exact ⟨Set.mem_biUnion ha (h a ha), fun _ _ T hT _ ⟨b, hb⟩ _ _ ↦
      Set.mem_biUnion hb (h b (hT hb))⟩

/-- On an existential the simpler (62) agrees with (108c), the enrichment asserting the statement
and every alternative over a nonempty subdomain, as in (63c). -/
theorem oMinus_biUnion_eq_inter_sInter (hD : D.Nonempty) :
    oMinus (fun S ↦ ⋃ a ∈ S, P a) D = (⋃ a ∈ D, P a) ∩ ⋂₀ supClosure (P '' D) := by
  obtain ⟨a, ha⟩ := hD
  rw [oMinus_biUnion P ⟨a, ha⟩, Set.sInter_supClosure, Set.sInter_image]
  simp only [Finset.mem_coe]
  exact (Set.inter_eq_right.2 fun w hw ↦ Set.mem_biUnion ha (Set.mem_iInter₂.1 hw a ha)).symm

/-- With σ over negation, (65)–(66), the statement entails every variant, so the free-choice
implicature vanishes and *any* acts as a negative-polarity item. -/
theorem oMinus_antitone_eq {C : Set W → Set W} (hC : Antitone C) :
    oMinus (fun S ↦ C (⋃ a ∈ S, P a)) D = C (⋃ a ∈ D, P a) :=
  oMinus_eq_self fun _ hT _ ↦ hC (Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 hT))

/-- The presupposition of the strong σ, (72), fails under an antitone context, since the
enrichment coincides with the plain statement: *qualunque* has no negative-polarity construal,
(70). -/
theorem not_oMinus_ssubset_of_antitone {C : Set W → Set W} (hC : Antitone C) :
    ¬ oMinus (fun S ↦ C (⋃ a ∈ S, P a)) D ⊂ C (⋃ a ∈ D, P a) := by
  rw [oMinus_antitone_eq P hC]
  exact ssubset_irrefl _

/-- In a positive context the antiexhaustive enrichment properly strengthens the statement,
(71): a world where one member of the domain is a witness and another is not satisfies the
statement but not its enrichment. -/
theorem oMinus_ssubset {a b : E} {w : W} (ha : a ∈ D) (hb : b ∈ D) (hPa : w ∈ P a)
    (hPb : w ∉ P b) : oMinus (fun S ↦ ⋃ a ∈ S, P a) D ⊂ ⋃ a ∈ D, P a :=
  (Set.ssubset_iff_of_subset fun _ h ↦ h.1).2 ⟨w, Set.mem_biUnion ha hPa, fun h ↦
    hPb (Set.mem_iInter₂.1 (oMinus_biUnion P ⟨a, ha⟩ ▸ h) b hb)⟩

/-- Under a possibility modal the antiexhaustive enrichment is the universal over the options:
every member of the domain is a witness in some accessible world, the distribution of (83)–(85)
without the uniqueness implicature. -/
theorem oMinus_preimage_biUnion (R : SetRel W W) (hD : D.Nonempty) :
    oMinus (fun S ↦ R.preimage (⋃ a ∈ S, P a)) D = ⋂ a ∈ D, R.preimage (P a) := by
  simp only [SetRel.preimage_iUnion]
  exact oMinus_biUnion _ hD

/-- Under a necessity modal the antiexhaustive enrichment makes every member of a domain with
two members an option, (93c)–(93d): a member witnessed in no accessible world would make the
rest of the domain necessary without making that member necessary. -/
theorem oMinus_core_biUnion_subset {R : SetRel W W} (hD : 1 < D.card) :
    oMinus (fun S ↦ R.core (⋃ a ∈ S, P a)) D ∩ R.dom ⊆ ⋂ a ∈ D, R.preimage (P a) := by
  classical
  refine fun w ⟨⟨hall, h⟩, v, hv⟩ ↦ Set.mem_iInter₂.2 fun a ha ↦ by_contra fun hna ↦ ?_
  have hne : (D.erase a).Nonempty :=
    Finset.card_pos.1 (by rw [Finset.card_erase_of_mem ha]; omega)
  have hrest : w ∈ R.core (⋃ x ∈ D.erase a, P x) := fun u hu ↦
    let ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 (hall hu)
    Set.mem_biUnion (Finset.mem_erase.2 ⟨fun hxa ↦ hna ⟨u, hxa ▸ hPx, hu⟩, hx⟩) hPx
  obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 (h _ (Finset.erase_subset a D) {a} (by simpa) hne
    (by simp) (Finset.disjoint_singleton_right.2 (Finset.notMem_erase a D)) hrest hv)
  exact hna ⟨v, Finset.mem_singleton.1 hx ▸ hPx, hv⟩

end Antiexhaustive

/-! ### Episodic existentials -/

section Subtrigging

variable (P : E → Set W) {D : Finset E}

/-- An episodic scope holds only of the individuals `actual w` that exist at the world `w`. -/
def IsActualist (actual : W → Set E) (P : E → Set W) : Prop := ∀ a w, w ∈ P a → a ∈ actual w

/-- Over a domain that contains a merely possible individual at every world, an actualist
universal is never true, (67): *I saw any student* is too strong to ever be true. -/
theorem oMinus_biUnion_eq_empty_of_isActualist {actual : W → Set E}
    (hP : IsActualist actual P) (hD : D.Nonempty) (hwide : ∀ w, ∃ a ∈ D, a ∉ actual w) :
    oMinus (fun S ↦ ⋃ a ∈ S, P a) D = ∅ := by
  rw [oMinus_biUnion P hD]
  refine Set.eq_empty_of_forall_notMem fun w hw ↦ ?_
  obtain ⟨a, ha, hna⟩ := hwide w
  exact hna (hP a w (Set.mem_iInter₂.1 hw a ha))

end Subtrigging

end Exhaustification
