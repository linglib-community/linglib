/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.MinMax

/-!
# Best Match over equidistance classes

A probe's domain can be given as its equidistance classes, closest first, the goals of a class
being dominated by the same maximal projections, as the specifiers of one head are. The search
halts in the first class with a satisfier, and there it finds the goals bearing the most
satisfaction features, Best Match. Agree copies from the interacting goals of the earlier classes
and from the interacting best matches, so equidistant equal matches are agreed with together,
Multiple Agree. On singleton classes these are `Probe.search` and `Probe.Spec.agree`.

## Main definitions

* `Minimalist.Probe.Spec.bestMatches`: the goals a specification finds in a domain of classes.
* `Minimalist.Probe.Spec.interacted`, `Minimalist.Probe.Spec.copied`: the goals Agree flags as
  interacting and the features it copies.

## Main results

* `Minimalist.Probe.Spec.mem_bestMatches_iff`: Best Match as the closest class with a satisfier.
* `Minimalist.Probe.Spec.card_satFeatures_eq_of_mem_bestMatches`: best matches match equally.
* `Minimalist.Probe.Spec.mem_bestMatches_iff_finds`: Best Match is Relativized Minimality keyed by
  a goal's class and then by the satisfaction features it bears.
* `Minimalist.Probe.Spec.bestMatches_map_singleton`,
  `Minimalist.Probe.Spec.interacted_map_singleton`, `Minimalist.Probe.Spec.copied_map_singleton`:
  singleton classes give the linear search and Agree.

## References

* [hammerly-mathieu-2026]
* [hiraiwa-2001]
* [deal-2025a]
-/

@[expose] public section

namespace Minimalist.Probe.Spec

variable {α F : Type*} [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

/-- The goals of one class bearing the most satisfaction features. -/
def bestIn (c : List α) : List α :=
  c.filter fun a ↦ c.all fun b ↦ (sp.satFeatures feats b).card ≤ (sp.satFeatures feats a).card

/-- The best matches of a domain of equidistance classes, closest first: the goals of the first
class with a satisfier that bear the most satisfaction features ([hammerly-mathieu-2026]). -/
def bestMatches : List (List α) → List α
  | [] => []
  | c :: d => if c.any (sp.toProbe feats).sat then sp.bestIn feats c else bestMatches d

/-- The goals a specification inspects, every goal of the classes before the first class with a
satisfier and the best matches of that class. -/
def inspected (d : List (List α)) : List α :=
  (d.takeWhile fun c ↦ !c.any (sp.toProbe feats).sat).flatten ++ sp.bestMatches feats d

/-- The goals Agree flags as interacting, the inspected goals that interact, so that equidistant
equal matches are agreed with together, Multiple Agree ([hiraiwa-2001]). -/
def interacted (d : List (List α)) : List α :=
  (sp.inspected feats d).filter (sp.toProbe feats).int

/-- The features Agree copies, the interaction features of the goals it flags. -/
def copied (d : List (List α)) : Finset F :=
  ((sp.interacted feats d).map (sp.intFeatures feats)).foldr (· ∪ ·) ∅

variable {sp feats} {a b : α} {c : List α} {d : List (List α)}

theorem mem_bestIn_iff :
    a ∈ sp.bestIn feats c ↔
      a ∈ c ∧ ∀ b ∈ c, (sp.satFeatures feats b).card ≤ (sp.satFeatures feats a).card := by
  simp [bestIn]

/-- A class has a goal bearing the most satisfaction features iff it has a goal. -/
@[simp] theorem bestIn_eq_nil_iff : sp.bestIn feats c = [] ↔ c = [] := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, bestIn]⟩
  by_contra hc
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp
    (List.argmax_eq_none.not.mpr hc : c.argmax (fun b ↦ (sp.satFeatures feats b).card) ≠ none)
  have : m ∈ sp.bestIn feats c := mem_bestIn_iff.mpr ⟨List.argmax_mem (Option.mem_def.mpr hm),
    fun b hb ↦ List.le_of_mem_argmax (f := fun b ↦ (sp.satFeatures feats b).card) hb
      (Option.mem_def.mpr hm)⟩
  simp [h] at this

@[simp] theorem bestMatches_nil : sp.bestMatches feats [] = [] := rfl

theorem bestMatches_cons_of_any (h : c.any (sp.toProbe feats).sat) :
    sp.bestMatches feats (c :: d) = sp.bestIn feats c :=
  ite_eq_left h

theorem bestMatches_cons_of_not_any (h : ¬ c.any (sp.toProbe feats).sat) :
    sp.bestMatches feats (c :: d) = sp.bestMatches feats d :=
  ite_eq_right h

/-- In a class with a satisfier, a goal bearing the most satisfaction features satisfies. -/
private theorem sat_of_forall_card_le (h : c.any (sp.toProbe feats).sat)
    (ha : ∀ b ∈ c, (sp.satFeatures feats b).card ≤ (sp.satFeatures feats a).card) :
    (sp.toProbe feats).sat a := by
  obtain ⟨b, hb, hs⟩ := List.any_eq_true.mp h
  simp only [toProbe_sat, decide_eq_true_eq, ← Finset.card_pos] at hs ⊢
  exact hs.trans_le (ha b hb)

/-- Best Match: a goal is a best match iff it satisfies the probe, its class is the first with a
satisfier, and no goal of its class bears more satisfaction features. -/
theorem mem_bestMatches_iff :
    a ∈ sp.bestMatches feats d ↔ (sp.toProbe feats).sat a ∧ ∃ d₁ c d₂, d = d₁ ++ c :: d₂ ∧
      (∀ b ∈ d₁.flatten, !(sp.toProbe feats).sat b) ∧ a ∈ c ∧
        ∀ b ∈ c, (sp.satFeatures feats b).card ≤ (sp.satFeatures feats a).card := by
  induction d with
  | nil => simp
  | cons c d ih =>
    by_cases h : c.any (sp.toProbe feats).sat
    · rw [bestMatches_cons_of_any h, mem_bestIn_iff]
      constructor
      · rintro ⟨ha, hmax⟩
        exact ⟨sat_of_forall_card_le h hmax, [], c, d, rfl, by simp, ha, hmax⟩
      · rintro ⟨-, _ | ⟨c', d₁⟩, c'', d₂, he, hd₁, ha, hmax⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact ⟨ha, hmax⟩
        · obtain ⟨hc, -⟩ := List.cons.inj he
          subst hc
          obtain ⟨b, hb, hs⟩ := List.any_eq_true.mp h
          have := hd₁ b (List.mem_flatten.mpr ⟨c, List.mem_cons_self .., hb⟩)
          rw [hs] at this
          exact absurd this (by decide)
    · rw [bestMatches_cons_of_not_any h, ih]
      simp only [List.any_eq_true, not_exists, not_and] at h
      refine and_congr_right fun hs ↦ ⟨?_, ?_⟩
      · rintro ⟨d₁, c', d₂, rfl, hd₁, rest⟩
        refine ⟨c :: d₁, c', d₂, rfl, fun b hb ↦ ?_, rest⟩
        rcases List.mem_flatten.mp hb with ⟨l, hl, hbl⟩
        rcases List.mem_cons.mp hl with rfl | hl
        · simpa using h b hbl
        · exact hd₁ b (List.mem_flatten.mpr ⟨l, hl, hbl⟩)
      · rintro ⟨_ | ⟨c', d₁⟩, c'', d₂, he, hd₁, ha, hmax⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact absurd hs (h a ha)
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact ⟨d₁, c'', d₂, rfl, fun b hb ↦ hd₁ b (by simp_all), ha, hmax⟩

/-- A best match satisfies the probe. -/
theorem sat_of_mem_bestMatches (h : a ∈ sp.bestMatches feats d) : (sp.toProbe feats).sat a :=
  (mem_bestMatches_iff.mp h).1

/-- A best match is a goal of the domain. -/
theorem mem_flatten_of_mem_bestMatches (h : a ∈ sp.bestMatches feats d) : a ∈ d.flatten := by
  obtain ⟨-, d₁, c, d₂, rfl, -, ha, -⟩ := mem_bestMatches_iff.mp h
  simp [ha]

/-- Best matches bear equally many satisfaction features. -/
theorem card_satFeatures_eq_of_mem_bestMatches (ha : a ∈ sp.bestMatches feats d)
    (hb : b ∈ sp.bestMatches feats d) :
    (sp.satFeatures feats a).card = (sp.satFeatures feats b).card := by
  induction d with
  | nil => simp at ha
  | cons c d ih =>
    by_cases h : c.any (sp.toProbe feats).sat
    · rw [bestMatches_cons_of_any h, mem_bestIn_iff] at ha hb
      exact le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)
    · rw [bestMatches_cons_of_not_any h] at ha hb
      exact ih ha hb

/-- A specification finds nothing iff no goal of the domain satisfies it. -/
@[simp] theorem bestMatches_eq_nil_iff :
    sp.bestMatches feats d = [] ↔ ∀ a ∈ d.flatten, ¬ (sp.toProbe feats).sat a := by
  induction d with
  | nil => simp
  | cons c d ih =>
    by_cases h : c.any (sp.toProbe feats).sat
    · rw [bestMatches_cons_of_any h, bestIn_eq_nil_iff]
      obtain ⟨s, hs, hss⟩ := List.any_eq_true.mp h
      exact iff_of_false (List.ne_nil_of_mem hs) fun hall ↦ hall s (by simp [hs]) hss
    · rw [bestMatches_cons_of_not_any h, ih]
      simp only [List.any_eq_true, not_exists, not_and] at h
      simp only [List.flatten_cons, List.mem_append, or_imp, forall_and]
      exact ⟨fun h' ↦ ⟨fun a ha hs ↦ h a ha hs, h'⟩, And.right⟩

/-- On singleton classes Best Match is the linear search. -/
theorem bestMatches_map_singleton (l : List α) :
    sp.bestMatches feats (l.map ([·])) = ((sp.toProbe feats).search l).toList := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : (sp.toProbe feats).sat a
    · rw [List.map_cons, bestMatches_cons_of_any (by simpa using h), search,
        List.find?_cons_of_pos h]
      simp [bestIn]
    · rw [List.map_cons, bestMatches_cons_of_not_any (by simpa using h), ih, search, search,
        List.find?_cons_of_neg h]

/-- On singleton classes a specification inspects as the linear probe does. -/
theorem inspected_map_singleton (l : List α) :
    sp.inspected feats (l.map ([·])) = (sp.toProbe feats).inspected l := by
  rw [inspected, Probe.inspected, bestMatches_map_singleton]
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : (sp.toProbe feats).sat a <;>
      simp only [List.map_cons, List.takeWhile_cons, List.any_cons, List.any_nil, Bool.or_false,
        h, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.flatten_nil,
        List.flatten_cons, List.singleton_append, ih]

/-- On singleton classes Agree flags the inspected goals that interact, as the linear Agree does
(`Probe.agree_interacted`). -/
theorem interacted_map_singleton (l : List α) :
    sp.interacted feats (l.map ([·])) =
      ((sp.toProbe feats).inspected l).filter (sp.toProbe feats).int := by
  rw [interacted, inspected_map_singleton]

private theorem foldl_union_eq (f : α → Finset F) (l : List α) (s : Finset F) :
    l.foldl (fun s a ↦ s ∪ f a) s = s ∪ (l.map f).foldr (· ∪ ·) ∅ := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp [ih, Finset.union_assoc]

/-- A feature is copied iff some flagged goal bears it among its interaction features. -/
theorem mem_copied_iff {x : F} :
    x ∈ sp.copied feats d ↔ ∃ a ∈ sp.interacted feats d, x ∈ sp.intFeatures feats a := by
  rw [copied]
  induction sp.interacted feats d with
  | nil => simp
  | cons a l ih => simp [ih]

/-- On singleton classes Agree copies the features the Agree of [deal-2025a] copies without
dynamic interaction. -/
theorem copied_map_singleton [Preorder F] [LocallyFiniteOrderTop F] (l : List α) :
    sp.copied feats (l.map ([·])) = (sp.agree feats ∅ l).state.copied := by
  rw [agree_empty]
  dsimp only
  rw [agree_state, foldl_union_eq, Finset.empty_union, copied, agree_interacted,
    interacted_map_singleton]

/-- A best match that interacts is agreed with. -/
theorem mem_interacted_of_mem_bestMatches (ha : a ∈ sp.bestMatches feats d)
    (hi : (sp.toProbe feats).int a) : a ∈ sp.interacted feats d :=
  List.mem_filter.mpr ⟨List.mem_append_right _ ha, hi⟩

/-- A flagged goal is a goal of the domain. -/
theorem mem_flatten_of_mem_interacted (h : a ∈ sp.interacted feats d) : a ∈ d.flatten := by
  rcases List.mem_append.mp (List.mem_filter.mp h).1 with h | h
  · obtain ⟨c, hc, hac⟩ := List.mem_flatten.mp h
    exact List.mem_flatten.mpr ⟨c, List.takeWhile_subset _ hc, hac⟩
  · exact mem_flatten_of_mem_bestMatches h

@[simp] theorem bestMatches_bot : (⊥ : Spec F).bestMatches feats d = [] :=
  bestMatches_eq_nil_iff.mpr fun _ _ ↦ by simp [satFeatures]

@[simp] theorem interacted_bot : (⊥ : Spec F).interacted feats d = [] :=
  List.filter_eq_nil_iff.mpr fun _ _ ↦ by simp [intFeatures]

@[simp] theorem copied_bot : (⊥ : Spec F).copied feats d = ∅ := by
  simp [copied]

/-! ### Best Match as Relativized Minimality -/

/-- A best match is an inspected goal that satisfies the probe. -/
theorem mem_bestMatches_iff_mem_inspected :
    a ∈ sp.bestMatches feats d ↔ a ∈ sp.inspected feats d ∧ (sp.toProbe feats).sat a := by
  refine ⟨fun h ↦ ⟨List.mem_append_right _ h, sat_of_mem_bestMatches h⟩, fun ⟨h, hs⟩ ↦ ?_⟩
  rcases List.mem_append.mp h with h | h
  · obtain ⟨c, hc, hac⟩ := List.mem_flatten.mp h
    have := List.mem_takeWhile_imp hc
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at this
    exact absurd hs (by simpa using this a hac)
  · exact h

section Key

variable [DecidableEq α]

variable (sp feats) in
/-- The key of Best Match over a domain of classes: a goal's class, and then the satisfaction
features it bears, more features being closer. -/
def bestMatchKey (d : List (List α)) (a : α) : ℕ ×ₗ ℕᵒᵈ :=
  toLex (d.findIdx (a ∈ ·), OrderDual.toDual (sp.satFeatures feats a).card)

private theorem bestMatchKey_cons_of_not_mem (h : a ∉ c) :
    sp.bestMatchKey feats (c :: d) a =
      toLex (d.findIdx (a ∈ ·) + 1, OrderDual.toDual (sp.satFeatures feats a).card) := by
  simp [bestMatchKey, List.findIdx_cons, h]

private theorem bestMatchKey_cons_of_mem (h : a ∈ c) :
    sp.bestMatchKey feats (c :: d) a =
      toLex (0, OrderDual.toDual (sp.satFeatures feats a).card) := by
  simp [bestMatchKey, List.findIdx_cons, h]

/-- The goals a specification inspects are those no satisfier is closer than under the key of
Best Match. -/
theorem mem_inspected_iff_inspects :
    a ∈ sp.inspected feats d ↔
      (sp.toProbe feats).Inspects {b | b ∈ d.flatten} (sp.bestMatchKey feats d) a := by
  induction d with
  | nil => simp [inspected, Inspects]
  | cons c d ih =>
    by_cases h : c.any (sp.toProbe feats).sat
    · have hins : sp.inspected feats (c :: d) = sp.bestIn feats c := by
        simp [inspected, h, bestMatches_cons_of_any h]
      obtain ⟨s, hs, hss⟩ := List.any_eq_true.mp h
      rw [hins, mem_bestIn_iff]
      constructor
      · rintro ⟨ha, hmax⟩
        refine ⟨by simp [ha], fun b hb hsb hlt ↦ ?_⟩
        by_cases hbc : b ∈ c
        · rw [bestMatchKey_cons_of_mem hbc, bestMatchKey_cons_of_mem ha,
            Prod.Lex.toLex_lt_toLex] at hlt
          simp only [lt_self_iff_false, true_and, false_or, OrderDual.toDual_lt_toDual] at hlt
          exact absurd (hmax b hbc) (not_le.2 hlt)
        · rw [bestMatchKey_cons_of_not_mem hbc, bestMatchKey_cons_of_mem ha,
            Prod.Lex.toLex_lt_toLex] at hlt
          simp at hlt
      · rintro ⟨ha, hins⟩
        have hac : a ∈ c := by
          by_contra hac
          refine hins (by simp [hs]) hss ?_
          rw [bestMatchKey_cons_of_mem hs, bestMatchKey_cons_of_not_mem hac,
            Prod.Lex.toLex_lt_toLex]
          exact .inl (Nat.succ_pos _)
        refine ⟨hac, fun b hb ↦ le_of_not_gt fun hlt ↦ ?_⟩
        have hsb : (sp.toProbe feats).sat b := by
          simp only [toProbe_sat, decide_eq_true_eq, ← Finset.card_pos]
          exact (Nat.zero_le _).trans_lt hlt
        refine hins (by simp [hb]) hsb ?_
        rw [bestMatchKey_cons_of_mem hb, bestMatchKey_cons_of_mem hac, Prod.Lex.toLex_lt_toLex]
        exact .inr ⟨rfl, OrderDual.toDual_lt_toDual.2 hlt⟩
    · have hins : sp.inspected feats (c :: d) = c ++ sp.inspected feats d := by
        simp [inspected, h, bestMatches_cons_of_not_any h]
      simp only [List.any_eq_true, not_exists, not_and] at h
      rw [hins, List.mem_append, ih]
      by_cases hac : a ∈ c
      · simp only [hac, true_or, true_iff]
        refine ⟨by simp [hac], fun b hb hsb hlt ↦ ?_⟩
        have hbc : b ∉ c := fun hbc ↦ h b hbc hsb
        rw [bestMatchKey_cons_of_not_mem hbc, bestMatchKey_cons_of_mem hac,
          Prod.Lex.toLex_lt_toLex] at hlt
        simp at hlt
      · simp only [hac, false_or, Inspects, Set.mem_ofPred_eq, List.flatten_cons, List.mem_append]
        constructor
        · rintro ⟨ha, hins⟩
          refine ⟨ha, fun b hb hsb hlt ↦ ?_⟩
          have hbc : b ∉ c := fun hbc ↦ h b hbc hsb
          rw [bestMatchKey_cons_of_not_mem hbc, bestMatchKey_cons_of_not_mem hac,
            Prod.Lex.toLex_lt_toLex] at hlt
          refine hins (hb.resolve_left hbc) hsb ?_
          simp only [bestMatchKey, Prod.Lex.toLex_lt_toLex]
          simpa using hlt
        · rintro ⟨ha, hins⟩
          refine ⟨ha, fun b hb hsb hlt ↦ ?_⟩
          have hbc : b ∉ c := fun hbc ↦ h b hbc hsb
          refine hins (.inr hb) hsb ?_
          rw [bestMatchKey_cons_of_not_mem hbc, bestMatchKey_cons_of_not_mem hac,
            Prod.Lex.toLex_lt_toLex]
          simp only [bestMatchKey, Prod.Lex.toLex_lt_toLex] at hlt
          simpa using hlt

/-- Best Match is Relativized Minimality keyed by a goal's class and then by the satisfaction
features it bears. -/
theorem mem_bestMatches_iff_finds :
    a ∈ sp.bestMatches feats d ↔
      (sp.toProbe feats).Finds {b | b ∈ d.flatten} (sp.bestMatchKey feats d) a := by
  rw [mem_bestMatches_iff_mem_inspected, mem_inspected_iff_inspects, finds_iff]

/-- Agree over classes flags the goals the probe agrees with under the key of Best Match. -/
theorem mem_interacted_iff_agreesWith :
    a ∈ sp.interacted feats d ↔
      (sp.toProbe feats).AgreesWith {b | b ∈ d.flatten} (sp.bestMatchKey feats d) a := by
  rw [interacted, List.mem_filter, mem_inspected_iff_inspects, AgreesWith]

end Key

end Minimalist.Probe.Spec
