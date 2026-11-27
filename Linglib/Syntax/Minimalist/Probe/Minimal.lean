/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Command.Closeness
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
* `Minimalist.Probe.AllLicensed`: the probe agrees with every position holding a goal that
  needs licensing.
* `Minimalist.Probe.Spec.copied`: the features Agree copies.

## Main results

* `Minimalist.Probe.finds_iff`: a probe finds the inspected goals that satisfy it.
* `Minimalist.Probe.exists_finds`: under a well-founded key a probe with a satisfier finds a goal.
* `Minimalist.Probe.Inspects.of_subset`: a goal inspected in a domain is inspected in any part of
  it containing the goal, as a horizon cuts the domain.
* `Minimalist.Probe.Finds.of_refines`: a goal found under a key is found under any key it refines.
* `Minimalist.Probe.agreesWith_iff_finds`: when the interacting goals satisfy the probe, it agrees
  with what it finds.
* `Minimalist.Probe.search_eq_some_iff_finds`, `Minimalist.Probe.mem_inspected_iff_inspects`,
  `Minimalist.Probe.mem_agree_interacted_iff`: the list search and the list Agree, keyed by
  position.
* `Minimalist.Probe.allLicensed_iff`: over a goal sequence, licensing is that every needy goal
  interacts and no goal before a needy one satisfies the probe.
* `Minimalist.Probe.AllLicensed.countP_le_one`, `Minimalist.Probe.allLicensed_sat_iff`: one search
  licenses at most one goal.
* `Minimalist.Probe.indiscriminate_allLicensed_iff`: under bare minimality only the closest goal
  may need licensing.
* `Minimalist.Probe.finds_ancestors_iff`, `Minimalist.Probe.not_finds_ancestors_of_lt`: keyed by
  the generators above a node, finding is the Minimal Link Condition among satisfiers none of which
  dominates another, and a goal inside a satisfier is not found.

## References

* [rizzi-1990]
* [deal-2025a]
* [hiraiwa-2001]
* [bejar-rezac-2003]
* [halpert-2012]
* [preminger-2014]
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

/-- A goal found under a key that refines another is found under that one: a goal closer under
the coarser key is closer under the finer. -/
theorem Finds.of_refines {γ : Type*} [Preorder γ] {key' : α → γ}
    (hk : ∀ ⦃a b⦄, key a < key b → key' a < key' b) (h : p.Finds s key' a) : p.Finds s key a :=
  finds_iff.2 ⟨⟨h.mem, fun _ hb hsb hlt ↦ h.inspects.2 hb hsb (hk hlt)⟩, h.sat⟩

/-- When every interacting goal satisfies the probe, it agrees with the goals it finds that
interact. -/
theorem agreesWith_iff_finds (hp : ∀ a, p.int a → p.sat a) :
    p.AgreesWith s key a ↔ p.Finds s key a ∧ p.int a := by
  rw [AgreesWith, finds_iff]
  exact ⟨fun ⟨h, hi⟩ ↦ ⟨⟨h, hp a hi⟩, hi⟩, fun ⟨⟨h, _⟩, hi⟩ ↦ ⟨h, hi⟩⟩

theorem agreesWith_relativized_iff {f : α → Prop} [DecidablePred f] :
    (relativized f).AgreesWith s key a ↔ (relativized f).Finds s key a := by
  rw [agreesWith_iff_finds fun _ h ↦ h]
  exact ⟨And.left, fun h ↦ ⟨h, h.sat⟩⟩

theorem inspects_insatiable_iff {f : α → Prop} [DecidablePred f] :
    (insatiable f).Inspects s key a ↔ a ∈ s := by
  simp [Inspects]

theorem agreesWith_insatiable_iff {f : α → Prop} [DecidablePred f] :
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

/-! ### Feature specifications: copying -/

namespace Spec

variable {F : Type*} [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

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

/-! ### Closeness in phrase structure -/

section Closeness

open PhraseStructure
open scoped SetRel

variable {α : Type*} [PartialOrder α] {P : Set α} {p : Probe α} {s : Set α} {a b x : α}

/-- Among satisfiers none of which dominates another, a probe finds those that no satisfier
commands without being commanded, the Minimal Link Condition. -/
theorem finds_ancestors_iff (hs : IsAntichain (· ≤ ·) {b | b ∈ s ∧ p.sat b}) :
    p.Finds s (ancestors P) a ↔ (a ∈ s ∧ p.sat a) ∧
      ∀ ⦃b⦄, b ∈ s → p.sat b → ¬ (Commands P b a ∧ ¬ Commands P a b) := by
  simpa only [Finds, and_imp, Set.mem_ofPred_eq] using minimalFor_ancestors_iff (P := P) hs

/-- A probe does not find a goal that a satisfier dominates through a generator: the container is
found before what it contains, as the A-over-A principle requires. -/
theorem not_finds_ancestors_of_lt (hb : b ∈ s) (hsb : p.sat b) (hbx : b ≤ x) (hxa : x < a)
    (hx : x ∈ P) : ¬ p.Finds s (ancestors P) a := fun h ↦
  h.inspects.2 hb hsb (ancestors_ssubset_ancestors_of_le_of_lt hbx hxa hx)

end Closeness

/-! ### The list search, keyed by position -/

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
        simp [Probe.inspected, search, hx]
      rw [hins, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨by simp, fun b _ _ ↦ by simp⟩
      · rintro ⟨-, h⟩
        by_contra hne
        exact h (List.mem_cons_self ..) hx (by simp [List.idxOf_cons_self, List.idxOf_cons_ne l
          (Ne.symm hne)])
    · have hins : p.inspected (x :: l) = x :: p.inspected l := by
        simp [Probe.inspected, search, hx]
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
  rw [agree_interacted, List.mem_filter, mem_inspected_iff_inspects, AgreesWith, decide_eq_true_iff]

end List

/-! ### Licensing -/

section Licensing

variable {γ : Type*} {q : Probe γ} {needs : γ → Prop} {goals : List γ}

/-- The goals that `needs` selects are all licensed when the probe Agrees with every position of
the sequence that holds one, since for [bejar-rezac-2003] licensing is an Agree relation with the
probe. The condition is on positions, so that a probe its goals satisfy does not license two
equal needy goals. Which goals need licensing and which satisfy the probe come apart in general,
as for [halpert-2012]'s Zulu L⁰, which every goal satisfies while only augmentless nominals need
it. -/
def AllLicensed (q : Probe γ) (needs : γ → Prop) (goals : List γ) : Prop :=
  ∀ i : Fin goals.length, needs (goals.get i) → (q.comap goals.get).AgreesWith Set.univ id i

/-- Over a goal sequence, every needy goal interacts with the probe and no goal before a needy
one satisfies it. -/
theorem allLicensed_iff :
    q.AllLicensed needs goals ↔
      (∀ a ∈ goals, needs a → q.int a) ∧ goals.Pairwise fun a b ↦ needs b → ¬ q.sat a := by
  simp only [AllLicensed, List.pairwise_iff_get, AgreesWith, Inspects, Set.mem_univ, true_and,
    forall_true_left, comap_sat, comap_int, id]
  refine ⟨fun h ↦ ⟨fun a ha hn ↦ ?_, fun i j hij hn hs ↦ (h j hn).1 hs hij⟩,
    fun ⟨h₁, h₂⟩ i hn ↦ ⟨fun b hb hlt ↦ h₂ b i hlt hn hb, h₁ _ (List.get_mem ..) hn⟩⟩
  obtain ⟨i, rfl⟩ := List.get_of_mem ha
  exact (h i hn).2

instance (q : Probe γ) (needs : γ → Prop) [DecidablePred needs] (goals : List γ) :
    Decidable (q.AllLicensed needs goals) :=
  decidable_of_iff _ allLicensed_iff.symm

@[simp] theorem allLicensed_nil : q.AllLicensed needs [] := allLicensed_iff.2 (by simp)

theorem allLicensed_cons {a : γ} :
    q.AllLicensed needs (a :: goals) ↔
      (needs a → q.int a) ∧ (∀ b ∈ goals, needs b → ¬ q.sat a) ∧
        q.AllLicensed needs goals := by
  simp only [allLicensed_iff, List.mem_cons, forall_eq_or_imp, List.pairwise_cons]
  tauto

/-- A licensed goal that satisfies the probe is the goal of Agree. -/
theorem AllLicensed.goal_eq_some (h : q.AllLicensed needs goals) {a : γ} (ha : a ∈ goals)
    (hn : needs a) (hs : q.sat a) : q.goal goals = some a := by
  obtain ⟨h₁, h₂⟩ := allLicensed_iff.1 h
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  exact goal_eq_some_iff.2 ⟨search_eq_some_iff_closest.2 ⟨hs, l₁, l₂, rfl,
    fun b hb ↦ (List.pairwise_append.1 h₂).2.2 b hb a List.mem_cons_self hn⟩, h₁ a ha hn⟩

theorem allLicensed_of_forall_not (h : ∀ a ∈ goals, ¬ needs a) : q.AllLicensed needs goals :=
  allLicensed_iff.2 ⟨fun a ha hn ↦ absurd hn (h a ha),
    List.pairwise_of_forall_mem_list fun _ _ b hb hn ↦ absurd hn (h b hb)⟩

/-- When the goals a probe interacts with halt it, one search licenses at most one needy goal. -/
theorem AllLicensed.countP_le_one [DecidablePred needs] (hq : ∀ a, q.int a → q.sat a)
    (h : q.AllLicensed needs goals) : goals.countP (needs ·) ≤ 1 := by
  induction goals with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl, h⟩ := allLicensed_cons.1 h
    rw [List.countP_cons]
    by_cases hn : needs a
    · rw [List.countP_eq_zero.2 fun b hb hb' ↦ hl b hb (of_decide_eq_true hb') (hq a (ha hn))]
      simp [hn]
    · simpa [hn] using ih h

/-- On the diagonal, where the goals that need licensing are exactly those that satisfy a probe
interacting with the goals that satisfy it, all of them are licensed iff at most one goal
satisfies the probe, the fact behind [preminger-2014]'s person restriction. -/
theorem allLicensed_sat_iff (hq : ∀ a, q.int a ↔ q.sat a) :
    q.AllLicensed q.sat goals ↔ goals.countP (q.sat ·) ≤ 1 := by
  refine ⟨AllLicensed.countP_le_one fun a ↦ (hq a).1, fun h ↦ ?_⟩
  induction goals with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons] at h
    refine allLicensed_cons.2 ⟨(hq a).2, fun b hb hfb ha ↦ ?_, ih (by split at h <;> omega)⟩
    have := List.countP_pos_iff (p := (q.sat ·)).2 ⟨b, hb, decide_eq_true hfb⟩
    simp only [show q.sat a from ha, decide_true, ite_true] at h
    omega

/-- Licensing by the indiscriminate probe allows no needy goal below the head of the sequence,
the highest-element condition of [halpert-2012]. -/
theorem indiscriminate_allLicensed_iff :
    (indiscriminate : Probe γ).AllLicensed needs goals ↔ ∀ a ∈ goals.tail, ¬ needs a := by
  rw [allLicensed_iff]
  cases goals with
  | nil => simp
  | cons a l =>
    simpa [indiscriminate, relativized] using
      fun h ↦ List.pairwise_of_forall_mem_list fun _ _ b hb ↦ h b hb

end Licensing

end Minimalist.Probe
