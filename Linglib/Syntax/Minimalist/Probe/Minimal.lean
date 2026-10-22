/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Command
public import Linglib.Syntax.Minimalist.Probe.Agree
public import Mathlib.Order.Minimal
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Relativized Minimality

A probe finds the goals of its domain that satisfy it and that no satisfying goal is closer than.
Closeness is read through a key into an ordered type, such as a goal's position in a list, its
class of equidistant goals, or the nodes that dominate it, so finding is mathlib's `MinimalFor`
and a theory of closeness is a choice of key. Agree inspects the goals that no satisfier is closer
than and agrees with those of them that interact. Keyed by position, these are `Probe.search` and
`Probe.inspected`.

## Main definitions

* `Minimalist.Probe.Finds`: a goal is a closest satisfier.
* `Minimalist.Probe.Inspects`, `Minimalist.Probe.AgreesWith`: no satisfier is closer than a goal,
  and the goal also interacts.
* `Minimalist.Probe.Spec.bestMatch`, `Minimalist.Probe.Spec.copied`: Best Match as a refinement of
  a closeness key, and the features Agree copies.

## Main results

* `Minimalist.Probe.finds_iff`: a probe finds the inspected goals that satisfy it.
* `Minimalist.Probe.exists_finds`: under a well-founded key a probe with a satisfier finds a goal.
* `Minimalist.Probe.Inspects.of_subset`: a goal inspected in a domain is inspected in any part of
  it containing the goal, as a horizon cuts the domain.
* `Minimalist.Probe.Finds.of_bestMatch`: a goal found under Best Match is found under the key it
  refines.
* `Minimalist.Probe.agreesWith_iff_finds`: when the interacting goals satisfy the probe, it agrees
  with what it finds.
* `Minimalist.Probe.search_eq_some_iff_finds`, `Minimalist.Probe.mem_inspected_iff_inspects`,
  `Minimalist.Probe.mem_agree_interacted_iff`: the list search and the list Agree, keyed by
  position.
* `Minimalist.Probe.finds_ancestors_iff`, `Minimalist.Probe.not_finds_ancestors_of_lt`: keyed by
  the generators above a node, finding is the Minimal Link Condition among satisfiers none of which
  dominates another, and a goal inside a satisfier is not found.

## References

* [rizzi-1990]
* [deal-2025a]
* [hiraiwa-2001]
* [hammerly-mathieu-2026]
-/

@[expose] public section

namespace Minimalist.Probe

variable {α β : Type*} [Preorder β] (p : Probe α) (s : Set α) (key : α → β)

/-- A probe finds a goal of `s` that satisfies it and that no satisfying goal of `s` is closer than,
closeness read through `key`: Relativized Minimality ([rizzi-1990]). -/
def Finds (a : α) : Prop := MinimalFor (fun b ↦ b ∈ s ∧ p.sat b) key a

/-- A probe inspects a goal of `s` that no satisfying goal of `s` is closer than. -/
def Inspects (a : α) : Prop := a ∈ s ∧ ∀ ⦃b⦄, b ∈ s → p.sat b → ¬ key b < key a

/-- A probe agrees with a goal it inspects and interacts with ([deal-2025a]). -/
def AgreesWith (a : α) : Prop := p.Inspects s key a ∧ p.int a

variable {p s key} {a b : α}

/-- A probe finds the inspected goals that satisfy it. -/
theorem finds_iff : p.Finds s key a ↔ p.Inspects s key a ∧ p.sat a := by
  rw [Finds, minimalFor_iff_forall_lt, Inspects]
  constructor
  · rintro ⟨⟨ha, hs⟩, h⟩
    exact ⟨⟨ha, fun b hb hsb hlt ↦ h hlt ⟨hb, hsb⟩⟩, hs⟩
  · rintro ⟨⟨ha, h⟩, hs⟩
    exact ⟨⟨ha, hs⟩, fun b hlt hb ↦ h hb.1 hb.2 hlt⟩

theorem Finds.inspects (h : p.Finds s key a) : p.Inspects s key a := (finds_iff.1 h).1

theorem Finds.sat (h : p.Finds s key a) : p.sat a := (finds_iff.1 h).2

theorem Finds.mem (h : p.Finds s key a) : a ∈ s := h.inspects.1

theorem Inspects.mem (h : p.Inspects s key a) : a ∈ s := h.1

/-- In a linearly ordered key, a found goal is at least as close as every satisfier. -/
theorem Finds.le {β : Type*} [LinearOrder β] {key : α → β} (h : p.Finds s key a) (hb : b ∈ s)
    (hs : p.sat b) : key a ≤ key b :=
  MinimalFor.le h ⟨hb, hs⟩

/-- Under a well-founded key, a probe with a satisfier in its domain finds a goal. -/
theorem exists_finds [WellFoundedLT β] (h : ∃ a ∈ s, p.sat a) : ∃ a, p.Finds s key a :=
  exists_minimalFor_of_wellFoundedLT _ key (let ⟨a, ha, hs⟩ := h; ⟨a, ha, hs⟩)

/-- A goal inspected in a domain is inspected in any part of it that contains the goal, as a
horizon cuts the domain. -/
theorem Inspects.of_subset {t : Set α} (h : p.Inspects s key a) (hts : t ⊆ s) (ha : a ∈ t) :
    p.Inspects t key a :=
  ⟨ha, fun _ hb ↦ h.2 (hts hb)⟩

/-- A goal found in a domain is found in any part of it that contains the goal. -/
theorem Finds.of_subset {t : Set α} (h : p.Finds s key a) (hts : t ⊆ s) (ha : a ∈ t) :
    p.Finds t key a :=
  finds_iff.2 ⟨h.inspects.of_subset hts ha, h.sat⟩

/-- When every interacting goal satisfies the probe, it agrees with the goals it finds that
interact. -/
theorem agreesWith_iff_finds (hp : ∀ a, p.int a → p.sat a) :
    p.AgreesWith s key a ↔ p.Finds s key a ∧ p.int a := by
  rw [AgreesWith, finds_iff]
  exact ⟨fun ⟨h, hi⟩ ↦ ⟨⟨h, hp a hi⟩, hi⟩, fun ⟨⟨h, _⟩, hi⟩ ↦ ⟨h, hi⟩⟩

/-- A relativized probe agrees with what it finds. -/
theorem agreesWith_relativized_iff {f : α → Bool} :
    (relativized f).AgreesWith s key a ↔ (relativized f).Finds s key a := by
  rw [agreesWith_iff_finds fun _ h ↦ h]
  exact ⟨And.left, fun h ↦ ⟨h, h.sat⟩⟩

/-- An insatiable probe inspects its whole domain, Multiple Agree ([hiraiwa-2001]). -/
theorem inspects_insatiable_iff {f : α → Bool} : (insatiable f).Inspects s key a ↔ a ∈ s := by
  simp [Inspects]

theorem agreesWith_insatiable_iff {f : α → Bool} :
    (insatiable f).AgreesWith s key a ↔ a ∈ s ∧ f a := by
  simp [AgreesWith, inspects_insatiable_iff]

/-! ### Finite domains -/

section Fintype

variable [Fintype α] [DecidablePred (· ∈ s)] [DecidableRel ((· < ·) : β → β → Prop)]

instance : DecidablePred (p.Inspects s key) := fun a ↦
  inferInstanceAs (Decidable (a ∈ s ∧ ∀ ⦃b⦄, b ∈ s → p.sat b → ¬ key b < key a))

instance : DecidablePred (p.Finds s key) := fun _ ↦ decidable_of_iff _ finds_iff.symm

instance : DecidablePred (p.AgreesWith s key) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

end Fintype

/-! ### Feature specifications: Best Match and copying -/

namespace Spec

variable {F : Type*} [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

/-- Best Match refines a closeness key: of equally close goals, the one bearing more satisfaction
features is closer ([hammerly-mathieu-2026]). -/
def bestMatch (key : α → β) (a : α) : β ×ₗ ℕᵒᵈ :=
  toLex (key a, OrderDual.toDual (sp.satFeatures feats a).card)

/-- Comparing goals under Best Match is decidable when comparing their closeness is. -/
instance [DecidableEq β] [DecidableRel ((· < ·) : β → β → Prop)] :
    DecidableRel ((· < ·) : β ×ₗ ℕᵒᵈ → β ×ₗ ℕᵒᵈ → Prop) :=
  Prod.Lex.decidable _ _

/-- The features Agree copies, the interaction features of the goals the probe agrees with. -/
def copied [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] (key : α → β)
    [DecidableRel ((· < ·) : β → β → Prop)] : Finset F :=
  (Finset.univ.filter fun a ↦ (sp.toProbe feats).AgreesWith s key a).biUnion (sp.intFeatures feats)

variable {sp feats}

theorem mem_copied_iff [Fintype α] {s : Set α} [DecidablePred (· ∈ s)] {key : α → β}
    [DecidableRel ((· < ·) : β → β → Prop)] {x : F} :
    x ∈ sp.copied feats s key ↔
      ∃ a, (sp.toProbe feats).AgreesWith s key a ∧ x ∈ sp.intFeatures feats a := by
  simp [copied]

end Spec

/-- A goal found under Best Match is found under the closeness it refines. -/
theorem Finds.of_bestMatch {F : Type*} [DecidableEq F] {sp : Spec F} {feats : α → Finset F}
    (h : (sp.toProbe feats).Finds s (sp.bestMatch feats key) a) :
    (sp.toProbe feats).Finds s key a := by
  rw [finds_iff] at h ⊢
  refine ⟨⟨h.1.1, fun b hb hsb hlt ↦ h.1.2 hb hsb ?_⟩, h.2⟩
  rw [Spec.bestMatch, Spec.bestMatch, Prod.Lex.toLex_lt_toLex]
  exact .inl hlt

/-! ### Closeness in phrase structure -/

section Closeness

open PhraseStructure
open scoped SetRel

variable {α : Type*} [PartialOrder α] {P : Set α} {p : Probe α} {s : Set α} {a b x : α}

/-- Among satisfiers none of which dominates another, a probe finds those that no satisfier
asymmetrically commands, the Minimal Link Condition. -/
theorem finds_ancestors_iff (hs : IsAntichain (· ≤ ·) {b | b ∈ s ∧ p.sat b}) :
    p.Finds s (ancestors P) a ↔ (a ∈ s ∧ p.sat a) ∧
      ∀ ⦃b⦄, b ∈ s → p.sat b → ¬ (b ~[commandRelation P] a ∧ ¬ a ~[commandRelation P] b) := by
  simpa only [Finds, and_imp, Set.mem_ofPred_eq] using minimalFor_ancestors_iff (P := P) hs

/-- A probe does not find a goal that a satisfier dominates through a generator: the container is
found before what it contains, as the A-over-A principle requires. -/
theorem not_finds_ancestors_of_lt (hb : b ∈ s) (hsb : p.sat b) (hbx : b ≤ x) (hxa : x < a)
    (hx : x ∈ P) : ¬ p.Finds s (ancestors P) a := fun h ↦
  h.inspects.2 hb hsb (ancestors_ssubset_ancestors_of_le_of_lt hbx hxa hx)

end Closeness

/-! ### The list search, keyed by position -/

/-- The list search finds the inspected goal that satisfies the probe. -/
theorem search_eq_some_iff_mem_inspected {l : List α} :
    p.search l = some a ↔ a ∈ p.inspected l ∧ p.sat a := by
  rw [Probe.inspected, List.mem_append]
  constructor
  · intro h
    exact ⟨.inr (by simp [h]), sat_of_search_eq_some h⟩
  · rintro ⟨h | h, hs⟩
    · exact absurd hs (by simpa using List.mem_takeWhile_imp h)
    · cases hc : p.search l <;> simp_all

section List

variable [DecidableEq α] {l : List α}

/-- The goals the list search inspects are those that no satisfier precedes. -/
theorem mem_inspected_iff_inspects :
    a ∈ p.inspected l ↔ p.Inspects {b | b ∈ l} l.idxOf a := by
  induction l with
  | nil => simp [Probe.inspected, Inspects]
  | cons x l ih =>
    by_cases hx : p.sat x
    · have hins : p.inspected (x :: l) = [x] := by
        simp [Probe.inspected, search, hx, List.find?_cons_of_pos hx]
      rw [hins, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨by simp, fun b _ _ ↦ by simp⟩
      · rintro ⟨-, h⟩
        by_contra hne
        exact h (List.mem_cons_self ..) hx (by simp [List.idxOf_cons_self, List.idxOf_cons_ne l
          (Ne.symm hne)])
    · have hins : p.inspected (x :: l) = x :: p.inspected l := by
        simp [Probe.inspected, search, hx, List.find?_cons_of_neg hx]
      rw [hins, List.mem_cons, ih]
      by_cases hax : a = x
      · subst hax
        simp only [true_or, true_iff]
        exact ⟨by simp, fun b _ _ ↦ by simp⟩
      · simp only [hax, false_or, Inspects, Set.mem_ofPred_eq, List.mem_cons]
        constructor
        · rintro ⟨ha, h⟩
          refine ⟨ha, fun b hb hsb hlt ↦ ?_⟩
          rcases hb with rfl | hb
          · exact hx hsb
          · have hbx : b ≠ x := fun e ↦ hx (e ▸ hsb)
            rw [List.idxOf_cons_ne l (Ne.symm hbx), List.idxOf_cons_ne l (Ne.symm hax)] at hlt
            exact h hb hsb (Nat.succ_lt_succ_iff.1 hlt)
        · rintro ⟨ha, h⟩
          refine ⟨ha, fun b hb hsb hlt ↦ ?_⟩
          have hbx : b ≠ x := fun e ↦ hx (e ▸ hsb)
          exact h (.inr hb) hsb (by
            rw [List.idxOf_cons_ne l (Ne.symm hbx), List.idxOf_cons_ne l (Ne.symm hax)]
            exact Nat.succ_lt_succ hlt)

/-- The list search is Relativized Minimality keyed by position. -/
theorem search_eq_some_iff_finds : p.search l = some a ↔ p.Finds {b | b ∈ l} l.idxOf a := by
  rw [search_eq_some_iff_mem_inspected, mem_inspected_iff_inspects, finds_iff]

/-- The list Agree flags the goals the probe agrees with, keyed by position. -/
theorem mem_agree_interacted_iff {σ : Type*} {copy : α → σ → σ} {st : σ} :
    a ∈ (p.agree copy st l).interacted ↔ p.AgreesWith {b | b ∈ l} l.idxOf a := by
  rw [agree_interacted, List.mem_filter, mem_inspected_iff_inspects, AgreesWith]

end List

end Minimalist.Probe
