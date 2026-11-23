/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TierTree

/-!
# Bisimulation of representations along a tree of tiers

Two representations along a tree of tiers are bisimilar under a relation `R` between their
tokens, `AR.IsBisim T Y Z R`, when related tokens stand on the same tier with the same label and
each child of one is related to a child of the other. Related tokens then reach related tokens
by descending lines (`IsBisim.exists_mem_descendants`), so a slot of one representation reads
what the related slot of the other reads (`IsBisim.reads_iff`). Material that no slot dominates,
such as an autosegment left floating by delinking, plays no part.

In a realization by trees with at most one token on a tier, spreading a tier from one symbol
onto another by a change of lines, `AR.spreadTier`, is bisimilar to replacing the target symbol
by one that has the source's tokens on that tier and below it and the target's own elsewhere.
The two therefore read alike (`reads_spreadTier_iff`): linking shares what copying duplicates.

## TODO

* A representation and its OCP collapse are bisimilar.
* A representation along a tree of tiers is a Kripke model with `AR.children` as its
  accessibility, and `IsBisim` is bisimulation of such models (`Logic/Team/Bisimulation.lean`).
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] {T : ParentTree ι}
  {Y Z : AR τ}

/-- `R` relates tokens of `Y` to tokens of `Z` on the same tier, with the same label, and matches
their children in both directions. -/
structure IsBisim (T : ParentTree ι) (Y Z : AR τ) (R : ι → ℕ → ℕ → Prop) : Prop where
  /-- Related tokens carry the same label. -/
  label : ∀ ⦃j q q'⦄, R j q q' → (Y.word j)[q]? = (Z.word j)[q']?
  /-- A child of a token of `Y` is related to a child of the related token of `Z`. -/
  forth : ∀ ⦃i p p' j q⦄, R i p p' → (j, q) ∈ Y.children T (i, p) →
    ∃ q', (j, q') ∈ Z.children T (i, p') ∧ R j q q'
  /-- A child of a token of `Z` is related to a child of the related token of `Y`. -/
  back : ∀ ⦃i p p' j q'⦄, R i p p' → (j, q') ∈ Z.children T (i, p') →
    ∃ q, (j, q) ∈ Y.children T (i, p) ∧ R j q q'

theorem mem_descendants_succ_of_mem {X : AR τ} {d : ℕ} {v c u : ι × ℕ}
    (hc : c ∈ X.children T v) (hu : u ∈ X.descendants T d c) :
    u ∈ X.descendants T (d + 1) v := by
  rw [descendants]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨c, hc, hu⟩)

theorem IsBisim.exists_mem_descendants {R : ι → ℕ → ℕ → Prop} (h : IsBisim T Y Z R) (d : ℕ) :
    ∀ {i p p' j q}, R i p p' → (j, q) ∈ Y.descendants T d (i, p) →
      ∃ q', (j, q') ∈ Z.descendants T d (i, p') ∧ R j q q' := by
  induction d with
  | zero =>
    intro i p p' j q hR hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (by simpa [descendants] using hq : (j, q) = (i, p))
    exact ⟨p', by simp [descendants], hR⟩
  | succ d ih =>
    intro i p p' j q hR hq
    rw [descendants, Finset.mem_insert, Finset.mem_biUnion] at hq
    obtain hq | ⟨⟨i₁, p₁⟩, hc, hq⟩ := hq
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      exact ⟨p', mem_descendants_self _ _, hR⟩
    · obtain ⟨p₁', hc', hR'⟩ := h.forth hR hc
      obtain ⟨q', hq', hR''⟩ := ih hR' hq
      exact ⟨q', mem_descendants_succ_of_mem hc' hq', hR''⟩

/-- The converse of a bisimulation is a bisimulation. -/
theorem IsBisim.symm {R : ι → ℕ → ℕ → Prop} (h : IsBisim T Y Z R) :
    IsBisim T Z Y fun j q' q ↦ R j q q' :=
  ⟨fun _ _ _ hR ↦ (h.label hR).symm, fun _ _ _ _ _ hR hc ↦ h.back hR hc,
    fun _ _ _ _ _ hR hc ↦ h.forth hR hc⟩

/-- Reading does not tell bisimilar slots apart. -/
theorem IsBisim.reads_iff {R : ι → ℕ → ℕ → Prop} (h : IsBisim T Y Z R) {k k' : ℕ}
    (hR : R T.root k k') {j : ι} {b : τ j} : Y.Reads T k j b ↔ Z.Reads T k' j b := by
  have hsymm := h.symm
  constructor
  · rintro ⟨q, -, hq, hb⟩
    obtain ⟨q', hq', hR'⟩ := h.exists_mem_descendants _ hR hq
    have hb' : (Z.word j)[q']? = some b := (h.label hR').symm.trans hb
    exact ⟨q', Finset.mem_range.2 (List.getElem?_eq_some_iff.1 hb').1, hq', hb'⟩
  · rintro ⟨q', -, hq', hb'⟩
    obtain ⟨q, hq, hR'⟩ := hsymm.exists_mem_descendants _ hR hq'
    have hb : (Y.word j)[q]? = some b := (h.label hR').trans hb'
    exact ⟨q, Finset.mem_range.2 (List.getElem?_eq_some_iff.1 hb).1, hq, hb⟩

end Autosegmental.AR

/-! ### Spreading as a bisimulation -/

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*}

section Offset

variable {S : Type*} (g₀ : S → AR τ) (i : ι) (w : List S)

/-- A token of the `k`th symbol stands at that symbol's offset. -/
theorem getElem?_word_prod_map {k : ℕ} (hk : k < w.length) {r : ℕ}
    (hr : r < ((g₀ w[k]).word i).length) :
    ((w.map g₀).prod.word i)[tierOffset g₀ i w k + r]? = ((g₀ w[k]).word i)[r]? := by
  induction w generalizing k with
  | nil => simp at hk
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, word_mul]
    cases k with
    | zero =>
      simp only [tierOffset_zero, Nat.zero_add, List.getElem_cons_zero] at hr ⊢
      exact List.getElem?_append_left hr
    | succ k =>
      simp only [tierOffset_cons_succ, List.getElem_cons_succ] at hr ⊢
      rw [Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
      exact ih (Nat.lt_of_succ_lt_succ hk) hr

/-- Symbols with a token on a tier are told apart by their offsets there. -/
theorem eq_of_tierOffset_eq {k k' : ℕ} (hk : k < w.length) (hk' : k' < w.length)
    (h : (g₀ w[k]).word i ≠ []) (h' : (g₀ w[k']).word i ≠ [])
    (he : tierOffset g₀ i w k = tierOffset g₀ i w k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | rfl | hlt
  · have := tierOffset_add_length_le g₀ i w hlt hk
    have := List.length_pos_iff.2 h
    omega
  · rfl
  · have := tierOffset_add_length_le g₀ i w hlt hk'
    have := List.length_pos_iff.2 h'
    omega

end Offset

variable [Fintype ι] [DecidableEq ι] {T : ParentTree ι} {X : AR τ}

/-- A position past the end of its tier is linked to nothing below it. -/
theorem descendants_eq_singleton {v : ι × ℕ} (hv : (X.word v.1).length ≤ v.2) (d : ℕ) :
    X.descendants T d v = {v} := by
  have hc : X.children T v = ∅ := Finset.eq_empty_of_forall_notMem fun ⟨j, q⟩ h ↦
    absurd (mem_children.1 h).2.2.lt_left (not_lt.2 hv)
  cases d with
  | zero => rfl
  | succ d => simp [descendants, hc]

/-- A slot past the end of the slots reads nothing. -/
theorem not_reads_of_length_le {k : ℕ} (hk : (X.word T.root).length ≤ k) {j : ι} {b : τ j} :
    ¬ X.Reads T k j b := by
  rintro ⟨q, -, hq, hb⟩
  rw [Dominates, descendants_eq_singleton (v := (T.root, k)) hk, Finset.mem_singleton] at hq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
  exact absurd (List.getElem?_eq_some_iff.1 hb).1 (not_lt.2 hk)

section Graft

variable {S : Type*} (g₀ : S → AR τ)

/-- The tier `t` is `j` or hangs below it. -/
def Below (T : ParentTree ι) (j t : ι) : Prop := ∃ r, T.parent^[r] t = j

omit [Fintype ι] [DecidableEq ι] in
theorem below_iff {j t : ι} : Below T j t ↔ t = j ∨ Below T j (T.parent t) := by
  constructor
  · rintro ⟨r, hr⟩
    cases r with
    | zero => exact .inl hr
    | succ r => exact .inr ⟨r, by rwa [Function.iterate_succ_apply] at hr⟩
  · rintro (rfl | ⟨r, hr⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨r + 1, by rwa [Function.iterate_succ_apply]⟩

omit [Fintype ι] [DecidableEq ι] in
theorem not_below_parent {j : ι} (hj : j ≠ T.root) : ¬ Below T j (T.parent j) := fun ⟨r, hr⟩ ↦
  hj (T.eq_root_of_iterate_eq (n := r + 1) (Nat.succ_ne_zero r)
    (by rwa [Function.iterate_succ_apply]))

omit [Fintype ι] [DecidableEq ι] in
theorem tierOffset_lt_length (i : ι) (w : List S) {k : ℕ} (hk : k < w.length)
    (h : (g₀ w[k]).word i ≠ []) :
    tierOffset g₀ i w k < ((w.map g₀).prod.word i).length := by
  rw [← tierOffset_length]
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (List.length_pos_iff.2 h))
    (tierOffset_add_length_le g₀ i w hk hk)

omit [Fintype ι] in
theorem link_spreadTier {w : List S} {j : ι} {m n : ℕ} (hj : j ≠ T.root) (hm : m < w.length)
    (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ []) (hnp : (g₀ w[n]).word (T.parent j) ≠ [])
    {i' j' : ι} {p q : ℕ} :
    (spreadTier T g₀ w j m n).Link i' j' p q ↔
      ((w.map g₀).prod.Link i' j' p q ∧
        ¬ (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w n) ∧
        ¬ (i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w n ∧
          q = tierOffset g₀ (T.parent j) w n)) ∨
      (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w m ∨
        i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w m ∧
          q = tierOffset g₀ (T.parent j) w n) := by
  have hij : T.parent j ≠ j := fun h ↦ hj (T.eq_root_of_iterate_eq (n := 1) one_ne_zero h)
  rw [spreadTier, link_addLine, link_eraseLine, word_eraseLine]
  exact or_congr_right ((and_iff_right hij).trans
    ((and_iff_right (tierOffset_lt_length g₀ _ w hn hnp)).trans
      (and_iff_right (tierOffset_lt_length g₀ _ w hm hmj))))

/-- In a realization by trees with at most one token on a tier, the children of a token are the
tokens of its own symbol on the tiers hanging from its tier. -/
theorem mem_children_prod_map {w : List S} (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1)
    (htree : ∀ s t, t ≠ T.root → ((g₀ s).Link (T.parent t) t 0 0 ↔ (g₀ s).word t ≠ []))
    {i' t : ι} {p q : ℕ} :
    (t, q) ∈ (w.map g₀).prod.children T (i', p) ↔ T.parent t = i' ∧ t ≠ T.root ∧
      ∃ k, ∃ hk : k < w.length, p = tierOffset g₀ i' w k ∧ q = tierOffset g₀ t w k ∧
        (g₀ w[k]).word t ≠ [] := by
  rw [mem_children]
  constructor
  · rintro ⟨hp, hr, hl⟩
    obtain rfl : T.parent t = i' := hp
    replace hl : (w.map g₀).prod.Link (T.parent t) t p q := hl
    obtain ⟨k, hk, rfl, rfl, hl0⟩ :=
      (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hl
    exact ⟨rfl, hr, k, hk, rfl, rfl, (htree _ t hr).1 hl0⟩
  · rintro ⟨rfl, hr, k, hk, rfl, rfl, hne⟩
    exact ⟨rfl, hr, (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).2
      ⟨k, hk, rfl, rfl, (htree _ t hr).2 hne⟩⟩

/-- The tokens of the `k`th symbol of a word on a tier. -/
def tokens (v : List S) (k : ℕ) (t : ι) : List (τ t) :=
  if hk : k < v.length then (g₀ v[k]).word t else []

omit [Fintype ι] [DecidableEq ι] in
theorem tokens_of_lt {v : List S} {k : ℕ} (hk : k < v.length) (t : ι) :
    tokens g₀ v k t = (g₀ v[k]).word t := by simp [tokens, hk]

omit [Fintype ι] [DecidableEq ι] in
theorem tokens_ne_nil_iff {v : List S} {k : ℕ} {t : ι} :
    tokens g₀ v k t ≠ [] ↔ ∃ hk : k < v.length, (g₀ v[k]).word t ≠ [] := by
  unfold tokens
  constructor
  · intro h
    by_cases hk : k < v.length
    · exact ⟨hk, by simpa [hk] using h⟩
    · simp [hk] at h
  · rintro ⟨hk, h⟩
    simpa [hk] using h

omit [Fintype ι] [DecidableEq ι] in
theorem tokens_set (w : List S) {n : ℕ} (hn : n < w.length) (s' : S) (k : ℕ) (t : ι) :
    tokens g₀ (w.set n s') k t = if k = n then (g₀ s').word t else tokens g₀ w k t := by
  unfold tokens
  by_cases hkn : k = n
  · subst hkn
    simp [hn]
  · simp [hkn, Ne.symm hkn]

omit [Fintype ι] [DecidableEq ι] in
theorem getElem?_word_prod_map_tokens (v : List S) {k : ℕ} {t : ι} (h : tokens g₀ v k t ≠ []) :
    ((v.map g₀).prod.word t)[tierOffset g₀ t v k]? = (tokens g₀ v k t)[0]? := by
  obtain ⟨hk, h'⟩ := (tokens_ne_nil_iff g₀).1 h
  rw [tokens_of_lt g₀ hk]
  simpa using getElem?_word_prod_map g₀ t v hk (r := 0) (List.length_pos_iff.2 h')

omit [Fintype ι] [DecidableEq ι] in
theorem eq_of_tierOffset_eq_tokens (v : List S) {k k' : ℕ} {t : ι} (h : tokens g₀ v k t ≠ [])
    (h' : tokens g₀ v k' t ≠ []) (he : tierOffset g₀ t v k = tierOffset g₀ t v k') : k = k' := by
  obtain ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h
  obtain ⟨hk', h'⟩ := (tokens_ne_nil_iff g₀).1 h'
  exact eq_of_tierOffset_eq g₀ t v hk hk' h h' he

section Tree

variable (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1)
  (htree : ∀ s t, t ≠ T.root → ((g₀ s).Link (T.parent t) t 0 0 ↔ (g₀ s).word t ≠ []))
include h1 htree

theorem mem_children_prod_map_tokens {v : List S} {i' t : ι} {p q : ℕ} :
    (t, q) ∈ (v.map g₀).prod.children T (i', p) ↔ T.parent t = i' ∧ t ≠ T.root ∧
      ∃ k, p = tierOffset g₀ i' v k ∧ q = tierOffset g₀ t v k ∧ tokens g₀ v k t ≠ [] := by
  rw [mem_children_prod_map g₀ h1 htree]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ exists_congr fun k ↦
    ⟨fun ⟨hk, hp, hq, h⟩ ↦ ⟨hp, hq, (tokens_ne_nil_iff g₀).2 ⟨hk, h⟩⟩,
      fun ⟨hp, hq, h⟩ ↦ let ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h; ⟨hk, hp, hq, h⟩⟩

omit [Fintype ι] [DecidableEq ι] h1 in
theorem tokens_parent_ne_nil {v : List S} {k : ℕ} {t : ι} (hr : t ≠ T.root)
    (h : tokens g₀ v k t ≠ []) : tokens g₀ v k (T.parent t) ≠ [] := by
  obtain ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h
  exact (tokens_ne_nil_iff g₀).2
    ⟨hk, List.ne_nil_of_length_pos ((htree _ t hr).2 h).lt_left⟩

omit [Fintype ι] [DecidableEq ι] in
theorem link_prod_map_tokens {v : List S} {k : ℕ} {t : ι} (hr : t ≠ T.root)
    (h : tokens g₀ v k t ≠ []) :
    (v.map g₀).prod.Link (T.parent t) t (tierOffset g₀ (T.parent t) v k)
      (tierOffset g₀ t v k) := by
  obtain ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h
  exact (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).2
    ⟨k, hk, rfl, rfl, (htree _ t hr).2 h⟩

end Tree

/-- Where the token of the `k`th symbol on tier `t` stands after tier `j` is spread from the
`m`th symbol onto the `n`th: with the tokens of the `m`th symbol when it belongs to the `n`th
and `t` is `j` or below it. -/
noncomputable def spreadPos (T : ParentTree ι) (w : List S) (j : ι) (m n : ℕ) (t : ι) (k : ℕ) : ℕ :=
  open Classical in
  if k = n ∧ Below T j t then tierOffset g₀ t w m else tierOffset g₀ t w k

omit [Fintype ι] [DecidableEq ι] in
theorem spreadPos_of_below {w : List S} {j t : ι} {m n : ℕ} (h : Below T j t) :
    spreadPos g₀ T w j m n t n = tierOffset g₀ t w m := by simp [spreadPos, h]

omit [Fintype ι] [DecidableEq ι] in
theorem spreadPos_of_not_below {w : List S} {j t : ι} {m n : ℕ} (h : ¬ Below T j t) (k : ℕ) :
    spreadPos g₀ T w j m n t k = tierOffset g₀ t w k := by simp [spreadPos, h]

omit [Fintype ι] [DecidableEq ι] in
theorem spreadPos_of_ne {w : List S} {j : ι} {m n k : ℕ} (h : k ≠ n) (t : ι) :
    spreadPos g₀ T w j m n t k = tierOffset g₀ t w k := by simp [spreadPos, h]

/-- Spreading a tier by a change of lines reads as replacing the target symbol by one that has
the source's tokens on that tier and below it, and the target's own tokens elsewhere. -/
theorem reads_spreadTier_iff {w : List S} {j : ι} {m n : ℕ} {s' : S} (hj : j ≠ T.root)
    (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1) (hroot : ∀ s, ((g₀ s).word T.root).length = 1)
    (htree : ∀ s t, t ≠ T.root → ((g₀ s).Link (T.parent t) t 0 0 ↔ (g₀ s).word t ≠ []))
    (hm : m < w.length) (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ [])
    (hnp : (g₀ w[n]).word (T.parent j) ≠ [])
    (hbelow : ∀ t, Below T j t → (g₀ s').word t = (g₀ w[m]).word t)
    (hrest : ∀ t, ¬ Below T j t → (g₀ s').word t = (g₀ w[n]).word t) {k : ℕ} {t : ι}
    {b : τ t} :
    ((w.set n s').map g₀).prod.Reads T k t b ↔ (spreadTier T g₀ w j m n).Reads T k t b := by
  have tok_below : ∀ {t : ι}, Below T j t →
      tokens g₀ (w.set n s') n t = tokens g₀ w m t := fun {t} hb ↦ by
    rw [tokens_set g₀ w hn, ite_eq_left rfl, hbelow t hb, tokens_of_lt g₀ hm]
  have tok_not_below : ∀ {t : ι}, ¬ Below T j t → ∀ k,
      tokens g₀ (w.set n s') k t = tokens g₀ w k t := fun {t} hb k ↦ by
    rw [tokens_set g₀ w hn]
    by_cases hkn : k = n
    · rw [ite_eq_left hkn, hrest t hb, hkn, tokens_of_lt g₀ hn]
    · rw [ite_eq_right hkn]
  have tok_ne : ∀ {k : ℕ}, k ≠ n → ∀ t,
      tokens g₀ (w.set n s') k t = tokens g₀ w k t := fun {k} hkn t ↦ by
    rw [tokens_set g₀ w hn, ite_eq_right hkn]
  have hroot_nb : ¬ Below T j T.root := fun ⟨r, hr⟩ ↦ hj (hr.symm.trans (T.iterate_root r))
  have hoff : ∀ (v : List S) k, k ≤ v.length → tierOffset g₀ T.root v k = k := fun v k hk ↦ by
    simp [tierOffset, hroot, hk]
  have hlenroot : ∀ v : List S, ((v.map g₀).prod.word T.root).length = v.length := fun v ↦ by
    rw [← tierOffset_length, hoff v _ le_rfl]
  have child := @mem_children_prod_map_tokens ι τ _ _ T S g₀ h1 htree
  have hB : IsBisim T ((w.set n s').map g₀).prod (spreadTier T g₀ w j m n)
      fun t q q' ↦ ∃ k, tokens g₀ (w.set n s') k t ≠ [] ∧
        q = tierOffset g₀ t (w.set n s') k ∧ q' = spreadPos g₀ T w j m n t k :=
    { label := by
        rintro t q q' ⟨k, hk, rfl, rfl⟩
        rw [getElem?_word_prod_map_tokens g₀ _ hk]
        show _ = ((w.map g₀).prod.word t)[_]?
        by_cases hkn : k = n
        · subst hkn
          by_cases hb : Below T j t
          · rw [spreadPos_of_below g₀ hb, tok_below hb] at *
            rw [getElem?_word_prod_map_tokens g₀ _ hk]
          · rw [spreadPos_of_not_below g₀ hb, tok_not_below hb] at *
            rw [getElem?_word_prod_map_tokens g₀ _ hk]
        · rw [spreadPos_of_ne g₀ hkn, tok_ne hkn] at *
          rw [getElem?_word_prod_map_tokens g₀ _ hk]
      forth := by
        rintro i' p p' t q ⟨k, hk, rfl, rfl⟩ hc
        obtain ⟨rfl, hr, k₂, he, rfl, hk₂⟩ := child.1 hc
        obtain rfl : k = k₂ := eq_of_tierOffset_eq_tokens g₀ _ hk
          (tokens_parent_ne_nil g₀ htree hr hk₂) he
        refine ⟨_, mem_children.2 ⟨rfl, hr, ?_⟩, _, hk₂, rfl, rfl⟩
        show (spreadTier T g₀ w j m n).Link (T.parent t) t _ _
        rw [link_spreadTier g₀ hj hm hn hmj hnp]
        by_cases hkn : k = n
        · subst hkn
          by_cases hbt : Below T j t
          · by_cases htj : t = j
            · subst htj
              exact .inr (.inl ⟨rfl, rfl, spreadPos_of_not_below g₀ (not_below_parent hj) _,
                spreadPos_of_below g₀ hbt⟩)
            · have hbp : Below T j (T.parent t) := (below_iff.1 hbt).resolve_left htj
              refine .inl ⟨?_, fun h ↦ htj h.2.1, fun h ↦ not_below_parent hj (h.2.1 ▸ hbt)⟩
              rw [spreadPos_of_below g₀ hbp, spreadPos_of_below g₀ hbt]
              exact link_prod_map_tokens g₀ h1 htree hr (by rw [← tok_below hbt]; exact hk₂)
          · have hbp : ¬ Below T j (T.parent t) := fun h ↦ hbt (below_iff.2 (.inr h))
            refine .inl ⟨?_, fun h ↦ hbt (h.2.1 ▸ ⟨0, rfl⟩), fun h ↦ hbp (h.1 ▸ ⟨0, rfl⟩)⟩
            rw [spreadPos_of_not_below g₀ hbp, spreadPos_of_not_below g₀ hbt]
            exact link_prod_map_tokens g₀ h1 htree hr (by rw [← tok_not_below hbt]; exact hk₂)
        · refine .inl ⟨?_, ?_, fun h ↦ not_below_parent hj ⟨1, by rw [← h.2.1]; exact h.1⟩⟩
          · rw [spreadPos_of_ne g₀ hkn, spreadPos_of_ne g₀ hkn]
            exact link_prod_map_tokens g₀ h1 htree hr (by rw [← tok_ne hkn]; exact hk₂)
          · rintro ⟨-, rfl, h₃, -⟩
            rw [spreadPos_of_ne g₀ hkn] at h₃
            exact hkn (eq_of_tierOffset_eq_tokens g₀ w (by rw [← tok_ne hkn]; exact hk)
              ((tokens_ne_nil_iff g₀).2 ⟨hn, hnp⟩) h₃)
      back := by
        rintro i' p p' t q' ⟨k, hk, rfl, rfl⟩ hc
        obtain ⟨hp, hr, hl⟩ := mem_children.1 hc
        obtain rfl : T.parent t = i' := hp
        replace hl : (spreadTier T g₀ w j m n).Link (T.parent t) t
            (spreadPos g₀ T w j m n (T.parent t) k) q' := hl
        rw [link_spreadTier g₀ hj hm hn hmj hnp] at hl
        rcases hl with ⟨hx, hne₁, -⟩ | ⟨-, htj, hp', hq'⟩ | ⟨h₁, h₂, -, -⟩
        · obtain ⟨k₂, hk₂, he, rfl, hl0⟩ :=
            (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hx
          have hk₂t : tokens g₀ w k₂ t ≠ [] :=
            (tokens_ne_nil_iff g₀).2 ⟨hk₂, (htree _ t hr).1 hl0⟩
          have hk₂p := tokens_parent_ne_nil g₀ htree hr hk₂t
          by_cases hkn : k = n
          · subst hkn
            by_cases hbp : Below T j (T.parent t)
            · rw [spreadPos_of_below g₀ hbp] at he
              obtain rfl : m = k₂ := eq_of_tierOffset_eq_tokens g₀ w
                (by rw [← tok_below hbp]; exact hk) hk₂p he
              have hbt : Below T j t := below_iff.2 (.inr hbp)
              have hk't : tokens g₀ (w.set k s') k t ≠ [] := by rw [tok_below hbt]; exact hk₂t
              exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
                (spreadPos_of_below g₀ hbt).symm⟩
            · rw [spreadPos_of_not_below g₀ hbp] at he
              obtain rfl : k = k₂ := eq_of_tierOffset_eq_tokens g₀ w
                (by rw [← tok_not_below hbp]; exact hk) hk₂p he
              have htj : t ≠ j := fun h ↦ hne₁
                ⟨by rw [h], h, by rw [spreadPos_of_not_below g₀ hbp, h], by rw [h]⟩
              have hbt : ¬ Below T j t := fun h ↦ (below_iff.1 h).elim htj hbp
              have hk't : tokens g₀ (w.set k s') k t ≠ [] := by
                rw [tok_not_below hbt]; exact hk₂t
              exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
                (spreadPos_of_not_below g₀ hbt _).symm⟩
          · rw [spreadPos_of_ne g₀ hkn] at he
            obtain rfl : k = k₂ := eq_of_tierOffset_eq_tokens g₀ w
              (by rw [← tok_ne hkn]; exact hk) hk₂p he
            have hk't : tokens g₀ (w.set n s') k t ≠ [] := by rw [tok_ne hkn]; exact hk₂t
            exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
              (spreadPos_of_ne g₀ hkn t).symm⟩
        · subst htj
          have hnb := not_below_parent (T := T) hj
          rw [spreadPos_of_not_below g₀ hnb] at hp'
          obtain rfl : k = n := eq_of_tierOffset_eq_tokens g₀ w
            (by rw [← tok_not_below hnb]; exact hk) ((tokens_ne_nil_iff g₀).2 ⟨hn, hnp⟩) hp'
          have hbj : Below T t t := ⟨0, rfl⟩
          have hk't : tokens g₀ (w.set k s') k t ≠ [] := by
            rw [tok_below hbj]; exact (tokens_ne_nil_iff g₀).2 ⟨hm, hmj⟩
          exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
            by rw [hq', spreadPos_of_below g₀ hbj]⟩
        · exact absurd ⟨1, by rw [← h₂]; exact h₁⟩ (not_below_parent hj) }
  by_cases hk : k < w.length
  · refine hB.reads_iff ⟨k, (tokens_ne_nil_iff g₀).2 ⟨by simpa using hk, ?_⟩, ?_, ?_⟩
    · exact List.ne_nil_of_length_pos (by rw [hroot]; exact Nat.one_pos)
    · exact (hoff _ k (by simpa using hk.le)).symm
    · rw [spreadPos_of_not_below g₀ hroot_nb, hoff w k hk.le]
  · exact iff_of_false
      (not_reads_of_length_le (by rw [hlenroot]; simpa using not_lt.1 hk))
      (not_reads_of_length_le (X := spreadTier T g₀ w j m n) (by
        show ((w.map g₀).prod.word T.root).length ≤ k
        rw [hlenroot]; exact not_lt.1 hk))

end Graft

end Autosegmental.AR
