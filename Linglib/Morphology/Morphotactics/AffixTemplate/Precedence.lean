module

public import Linglib.Morphology.Morphotactics.AffixTemplate.Basic
public import Linglib.Phonology.Subregular.Precedence

/-!
# The precedence relation of a template

A template is a ranking of exponents with ties. `AffixTemplate.Precedes` is the relation "may
stand before" that a template induces on its positions, and the admitted strings are those in
which every position may stand before every later one (`mem_language_iff_pairwise`), the
language `Language.pairwise` of that relation.

Without stacking positions the relation is a strict weak order on exponents, whose classes of
mutually exclusive exponents are the positions (`isStrictWeakOrder_precedes`). Conversely every
strict weak order on a finite set of exponents arises from a template
(`exists_template_of_isStrictWeakOrder`).

## References

* [bickel-nichols-2007]
-/

@[expose] public section

namespace Morphology

namespace AffixTemplate

open List

variable {Slot : Type*} [DecidableEq Slot] {t : AffixTemplate Slot} {v : List Slot}

variable (t) in
/-- `a` may stand before `b` in the template: its position comes earlier, or the two are one
stacking position. -/
def Precedes (a b : Slot) : Prop :=
  t.slots.idxOf a < t.slots.idxOf b ∨ a = b ∧ a ∈ t.stacking

instance : DecidableRel t.Precedes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A string is admitted when its positions are the template's and each may stand before every
later one. -/
theorem mem_language_iff_pairwise :
    v ∈ t.language ↔ (∀ a ∈ v, a ∈ t.slots) ∧ v.Pairwise t.Precedes := by
  refine ⟨fun ⟨hs, h⟩ ↦ ⟨fun a ha ↦ (h a ha).1, ?_⟩, fun ⟨hm, hp⟩ ↦ ⟨?_, fun a ha ↦ ⟨hm a ha, ?_⟩⟩⟩
  · refine pairwise_iff_forall_sublist.2 fun {a b} hab ↦ ?_
    have hle := pairwise_iff_forall_sublist.1 (pairwise_map.1 (sortedLE_iff_pairwise.1 hs)) hab
    rcases hle.lt_or_eq with hlt | heq
    · exact .inl hlt
    · have ha : a ∈ v := hab.subset (by simp)
      obtain rfl := (idxOf_inj (h a ha).1).1 heq
      refine .inr ⟨rfl, (h a ha).2.resolve_right fun hc ↦ ?_⟩
      have := hab.count_le a
      simp at this
      omega
  · exact (pairwise_map.2 (hp.imp fun {a b} h ↦
      h.elim le_of_lt fun h ↦ h.1 ▸ le_rfl)).sortedLE
  · refine or_iff_not_imp_left.2 fun hs ↦ not_lt.1 fun hc ↦ ?_
    have h2 : [a, a] <+ v := replicate_sublist_iff.2 hc
    exact (pairwise_iff_forall_sublist.1 hp h2).elim (lt_irrefl _) fun h ↦ hs h.2

/-- The language of a template is the language of its precedence relation, cut down to the
template's positions. -/
theorem language_eq_pairwise_inf :
    t.language = Language.pairwise t.Precedes ⊓ {v | ∀ a ∈ v, a ∈ t.slots} :=
  Set.ext fun _ ↦ mem_language_iff_pairwise.trans and_comm

/-- A string of exponents is licensed when its positions are the template's and each exponent
may stand before every later one. -/
theorem licensed_iff_pairwise {E : Slot → Type*} {w : List (Σ σ, E σ)} :
    t.Licensed w ↔ (∀ x ∈ w, x.1 ∈ t.slots) ∧ w.Pairwise (Sigma.fst ⁻¹'o t.Precedes) := by
  rw [Licensed, mem_language_iff_pairwise, pairwise_map]
  exact and_congr forall_mem_map .rfl

/-- On the exponents of a template without stacking positions, "may stand before" is a strict
weak order: exponents of one position exclude each other, and positions are linearly ordered. -/
theorem isStrictWeakOrder_precedes (h : t.stacking = ∅) (E : Slot → Type*) :
    IsStrictWeakOrder (Σ σ, E σ) (Sigma.fst ⁻¹'o t.Precedes) := by
  have key (a b : Σ σ, E σ) :
      (Sigma.fst ⁻¹'o t.Precedes) a b ↔ t.slots.idxOf a.1 < t.slots.idxOf b.1 := by
    simp [Order.Preimage, Precedes, h]
  exact
    { irrefl := fun a ha ↦ lt_irrefl _ ((key a a).1 ha)
      trans := fun a b c hab hbc ↦ (key a c).2 (((key a b).1 hab).trans ((key b c).1 hbc))
      incomp_trans := fun a b c hab hbc ↦ by simp only [key] at *; omega }

open Classical in
/-- In a strict weak order on a finite type, an element is below another exactly when fewer
elements are below it. -/
private theorem rel_iff_card_lt {F : Type*} [Fintype F] (R : F → F → Prop)
    [IsStrictWeakOrder F R] (a b : F) :
    R a b ↔ (Finset.univ.filter (R · a)).card < (Finset.univ.filter (R · b)).card := by
  have incomp {a b : F} (h : ¬ R a b ∧ ¬ R b a) (c : F) (hc : R c a) : R c b := by
    by_contra hcb
    have hbc : ¬ R b c := fun hbc ↦ h.2 (_root_.trans hbc hc)
    exact (IsStrictWeakOrder.incomp_trans c b a ⟨hcb, hbc⟩ ⟨h.2, h.1⟩).1 hc
  refine ⟨fun hab ↦ Finset.card_lt_card ⟨fun c hc ↦ ?_, fun hsub ↦ ?_⟩, fun hlt ↦ ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact _root_.trans hc hab
  · have := hsub (show a ∈ Finset.univ.filter (R · b) by simpa using hab)
    exact irrefl a (by simpa using this)
  · by_contra hab
    by_cases hba : R b a
    · refine absurd (Finset.card_le_card fun c hc ↦ ?_) (not_le.2 hlt)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact _root_.trans hc hba
    · refine absurd (Finset.card_le_card fun c hc ↦ ?_) (not_le.2 hlt)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact incomp ⟨hba, hab⟩ c hc

open Classical in
/-- Every strict weak order on a finite set of exponents is the precedence relation of a
template: its positions are the classes of mutually exclusive exponents. -/
theorem exists_template_of_isStrictWeakOrder {F : Type*} [Finite F] (R : F → F → Prop)
    [IsStrictWeakOrder F R] :
    ∃ (t : AffixTemplate ℕ) (slot : F → ℕ), t.stacking = ∅ ∧
      ∀ w : List F, w.Pairwise R ↔ w.map slot ∈ t.language := by
  have := Fintype.ofFinite F
  let rank (a : F) : ℕ := (Finset.univ.filter (R · a)).card
  have hrank (a : F) : rank a < Fintype.card F + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_univ _)
  refine ⟨{ suffixSlots := List.range (Fintype.card F + 1) }, rank, rfl, fun w ↦ ?_⟩
  have hidx (i : ℕ) (hi : i < Fintype.card F + 1) :
      (List.range (Fintype.card F + 1)).idxOf i = i := by
    have := (List.nodup_range (n := Fintype.card F + 1)).idxOf_getElem i
      (by rw [List.length_range]; exact hi)
    simpa using this
  rw [mem_language_iff_pairwise, pairwise_map]
  refine ⟨fun h ↦ ⟨by simpa [slots] using fun a _ ↦ hrank a, h.imp fun {a b} hab ↦ ?_⟩,
    fun h ↦ h.2.imp fun {a b} hab ↦ ?_⟩
  · exact .inl (by simpa [slots, hidx _ (hrank a), hidx _ (hrank b)] using
      (rel_iff_card_lt R a b).1 hab)
  · refine (rel_iff_card_lt R a b).2 ?_
    simpa [Precedes, slots, hidx _ (hrank a), hidx _ (hrank b)] using hab
end AffixTemplate

end Morphology
