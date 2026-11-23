/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.SuccPred.Tree
public import Linglib.Phonology.Autosegmental.Edit
public import Linglib.Phonology.Autosegmental.Realization
public import Linglib.Phonology.Autosegmental.TwoTier
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Representations along a tree of tiers

The tiers of a representation often form a tree, with the timing slots at the root and each
other tier hanging from one tier above it: a melody over its slots, the planes of a multiplanar
representation around their slots, the class nodes and features of a feature geometry under the
root node. For a tree of tiers `T : ParentTree ι`, the tokens a token is linked to on the tiers
hanging from its own are its `children`, and slot `k` dominates the tokens it reaches by
descending lines, `X.Dominates T k j q`. The representation reads the label `b` on tier `j` at
slot `k`, `X.Reads T k j b`, when that slot dominates a token of the tier with that label.

A realization `(w.map g₀).prod` whose primitives have one slot each is read symbol by symbol:
reading it at slot `k` is reading the primitive of the `k`th symbol at its slot
(`reads_prod_map`). Spreading a tier from the `m`th symbol onto the `n`th is a change of lines,
`spreadTier`: the token of the `n`th symbol on the tier above is delinked from its own token and
linked to that of the `m`th. When the primitives have at most one token on the two tiers, the
result has no crossing lines exactly when no symbol strictly between the two has a line between
those tiers (`noCrossing_spreadTier_iff`): a symbol with a token there blocks, and one without
is transparent.

On two tiers, with the autosegments over their slots, `twoTier`, a slot reads the labels of the
autosegments linked to it, which is `AR.SurfacesWith` (`reads_twoTier_upper_iff`), and a
realization by `AR.primitive`s reads at each slot the melody of its symbol
(`reads_prod_map_primitive`).

## TODO

* `AR.hostedOn` on planes is `Reads` on a star of tiers, and the line edits of
  `Multiplanar.lean` are `addLine` and `eraseLine` there.
* The graph of a tree of tiers is acyclic, so by `AR.noCrossing_iff_hasIntervalOrder_of_isAcyclic`
  a representation whose lines run along it obeys the No-Crossing Constraint exactly when it has
  an interval order.
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] (T : ParentTree ι)

section Dominates

variable (X : AR τ)

/-- The tokens a token is linked to on the tiers hanging from its own. -/
def children (v : ι × ℕ) : Finset (ι × ℕ) :=
  Finset.univ.biUnion fun j ↦
    if T.parent j = v.1 ∧ j ≠ T.root then
      ((X.lines v.1 j).filter (·.1 = v.2)).image fun x ↦ (j, x.2)
    else ∅

/-- The tokens a token reaches through at most `d` descending lines. -/
def descendants : ℕ → ι × ℕ → Finset (ι × ℕ)
  | 0, v => {v}
  | d + 1, v => insert v ((X.children T v).biUnion (descendants d))

/-- Slot `k` dominates position `q` of tier `j`: descending lines lead from the slot to it. -/
def Dominates (k : ℕ) (j : ι) (q : ℕ) : Prop :=
  (j, q) ∈ X.descendants T (Fintype.card ι) (T.root, k)

instance (k : ℕ) (j : ι) (q : ℕ) : Decidable (X.Dominates T k j q) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- `X` reads the label `b` on tier `j` at slot `k`: the slot dominates a token of the tier with
that label. -/
def Reads (k : ℕ) (j : ι) (b : τ j) : Prop :=
  ∃ q ∈ Finset.range (X.word j).length, X.Dominates T k j q ∧ (X.word j)[q]? = some b

instance [∀ j, DecidableEq (τ j)] (k : ℕ) (j : ι) (b : τ j) : Decidable (X.Reads T k j b) :=
  inferInstanceAs (Decidable (∃ q ∈ Finset.range _, _))

variable {T X}

theorem mem_children {v : ι × ℕ} {j : ι} {q : ℕ} :
    (j, q) ∈ X.children T v ↔ T.parent j = v.1 ∧ j ≠ T.root ∧ X.Link v.1 j v.2 q := by
  simp only [children, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j', h⟩
    split_ifs at h with hc
    · obtain ⟨⟨x₁, x₂⟩, hx, he⟩ := Finset.mem_image.1 h
      obtain ⟨hx₁, hx₂⟩ := Finset.mem_filter.1 hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      obtain rfl : x₁ = v.2 := hx₂
      exact ⟨hc.1, hc.2, hx₁⟩
    · simp at h
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨j, ?_⟩
    split_ifs with hc
    · exact Finset.mem_image.2 ⟨(v.2, q), Finset.mem_filter.2 ⟨h₃, rfl⟩, rfl⟩
    · exact absurd ⟨h₁, h₂⟩ hc

/-- The tokens a token of the representation reaches are tokens of the representation. -/
theorem lt_length_of_mem_descendants {d : ℕ} {v u : ι × ℕ} (hv : v.2 < (X.word v.1).length)
    (hu : u ∈ X.descendants T d v) : u.2 < (X.word u.1).length := by
  induction d generalizing v with
  | zero =>
    obtain rfl : u = v := by simpa [descendants] using hu
    exact hv
  | succ d ih =>
    simp only [descendants, Finset.mem_insert, Finset.mem_biUnion] at hu
    obtain rfl | ⟨⟨j, q⟩, hc, hu⟩ := hu
    · exact hv
    · exact ih (mem_children.1 hc).2.2.lt_right hu

theorem mem_descendants_self (d : ℕ) (v : ι × ℕ) : v ∈ X.descendants T d v := by
  cases d <;> simp [descendants]

theorem descendants_subset_succ (d : ℕ) (v : ι × ℕ) :
    X.descendants T d v ⊆ X.descendants T (d + 1) v := by
  induction d generalizing v with
  | zero => simp [descendants]
  | succ d ih =>
    rw [descendants, descendants]
    exact Finset.insert_subset_insert _ (Finset.biUnion_mono fun c _ ↦ ih c)

theorem descendants_mono {d d' : ℕ} (h : d ≤ d') (v : ι × ℕ) :
    X.descendants T d v ⊆ X.descendants T d' v := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (descendants_subset_succ _ v)

/-- A child of a token reached in `d` descending lines is reached in `d + 1`. -/
theorem mem_descendants_succ_of_mem_children {d : ℕ} {v u u' : ι × ℕ}
    (hu : u ∈ X.descendants T d v) (hu' : u' ∈ X.children T u) :
    u' ∈ X.descendants T (d + 1) v := by
  induction d generalizing v with
  | zero =>
    obtain rfl : u = v := by simpa [descendants] using hu
    rw [descendants]
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u', hu', mem_descendants_self 0 u'⟩)
  | succ d ih =>
    rw [descendants, Finset.mem_insert, Finset.mem_biUnion] at hu
    rw [descendants]
    obtain rfl | ⟨c, hc, hu⟩ := hu
    · exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.2 ⟨u', hu', mem_descendants_self _ u'⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨c, hc, ih hu⟩)

end Dominates

/-! ### Concatenation -/

section Mul

variable {T} (X Y : AR τ)

theorem children_mul_left {v : ι × ℕ} (hv : v.2 < (X.word v.1).length) :
    (X * Y).children T v = X.children T v := by
  ext ⟨j, q⟩
  simp only [mem_children, link_mul]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ or_iff_left fun h ↦ not_le.2 hv h.1

theorem descendants_mul_left (d : ℕ) {v : ι × ℕ} (hv : v.2 < (X.word v.1).length) :
    (X * Y).descendants T d v = X.descendants T d v := by
  induction d generalizing v with
  | zero => rfl
  | succ d ih =>
    simp only [descendants]
    rw [children_mul_left X Y hv]
    congr 1
    exact Finset.biUnion_congr rfl fun ⟨_, _⟩ hu ↦ ih (mem_children.1 hu).2.2.lt_right

theorem children_mul_right (v : ι × ℕ) :
    (X * Y).children T (v.1, (X.word v.1).length + v.2) =
      (Y.children T v).image fun u ↦ (u.1, (X.word u.1).length + u.2) := by
  ext ⟨j, q⟩
  simp only [mem_children, link_mul, Finset.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨h₁, h₂, h | ⟨-, hq, h⟩⟩
    · exact absurd h.lt_left (by omega)
    · exact ⟨j, q - (X.word j).length, ⟨h₁, h₂, by simpa using h⟩, rfl, by omega⟩
  · rintro ⟨j', q', ⟨h₁, h₂, h⟩, rfl, rfl⟩
    exact ⟨h₁, h₂, .inr ⟨by omega, by omega, by simpa using h⟩⟩

theorem descendants_mul_right (d : ℕ) (v : ι × ℕ) :
    (X * Y).descendants T d (v.1, (X.word v.1).length + v.2) =
      (Y.descendants T d v).image fun u ↦ (u.1, (X.word u.1).length + u.2) := by
  induction d generalizing v with
  | zero => simp [descendants]
  | succ d ih =>
    simp only [descendants, children_mul_right, Finset.image_insert, Finset.biUnion_image,
      Finset.image_biUnion]
    congr 1
    exact Finset.biUnion_congr rfl fun u _ ↦ ih u

variable {X Y} {j : ι} {k : ℕ} {b : τ j}

/-- A concatenation reads at a slot of its left factor as that factor does. -/
theorem reads_mul_left (hk : k < (X.word T.root).length) :
    (X * Y).Reads T k j b ↔ X.Reads T k j b := by
  simp only [Reads, Dominates, descendants_mul_left X Y _ (v := (T.root, k)) hk, word_mul,
    List.length_append, Finset.mem_range]
  constructor
  · rintro ⟨q, -, hq, hb⟩
    have hq' := lt_length_of_mem_descendants (v := (T.root, k)) hk hq
    exact ⟨q, hq', hq, by rwa [List.getElem?_append_left hq'] at hb⟩
  · rintro ⟨q, hq', hq, hb⟩
    exact ⟨q, by omega, hq, by rwa [List.getElem?_append_left hq']⟩

/-- A concatenation reads at a slot of its right factor as that factor does. -/
theorem reads_mul_right :
    (X * Y).Reads T (k + (X.word T.root).length) j b ↔ Y.Reads T k j b := by
  have hd : (X * Y).descendants T (Fintype.card ι) (T.root, k + (X.word T.root).length) =
      (Y.descendants T (Fintype.card ι) (T.root, k)).image fun u ↦
        (u.1, (X.word u.1).length + u.2) := by
    rw [Nat.add_comm]
    exact descendants_mul_right X Y _ (T.root, k)
  simp only [Reads, Dominates, hd, word_mul, List.length_append, Finset.mem_range]
  constructor
  · rintro ⟨q, -, hq, hb⟩
    obtain ⟨⟨j', q'⟩, hq', he⟩ := Finset.mem_image.1 hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hb' : (Y.word j')[q']? = some b := by
      rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hb
    exact ⟨q', (List.getElem?_eq_some_iff.1 hb').1, hq', hb'⟩
  · rintro ⟨q, -, hq, hb⟩
    exact ⟨(X.word j).length + q, by have := (List.getElem?_eq_some_iff.1 hb).1; omega,
      Finset.mem_image.2 ⟨(j, q), hq, rfl⟩,
      by rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]⟩

end Mul

/-! ### Tier offsets -/

section Offset

omit [Fintype ι] [DecidableEq ι]

variable {S : Type*} (g₀ : S → AR τ) (i : ι) (w : List S)

theorem tierOffset_succ {k : ℕ} (hk : k < w.length) :
    tierOffset g₀ i w (k + 1) = tierOffset g₀ i w k + ((g₀ w[k]).word i).length := by
  unfold tierOffset
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton]

theorem tierOffset_mono : Monotone (tierOffset g₀ i w) :=
  monotone_nat_of_le_succ fun k ↦ by
    by_cases hk : k < w.length
    · rw [tierOffset_succ g₀ i w hk]
      exact Nat.le_add_right _ _
    · simp [tierOffset, List.take_of_length_le (not_lt.1 hk),
        List.take_of_length_le (Nat.le_succ_of_le (not_lt.1 hk))]

/-- The tokens of a symbol on a tier stand before those of every later symbol. -/
theorem tierOffset_add_length_le {k k' : ℕ} (h : k < k') (hk : k < w.length) :
    tierOffset g₀ i w k + ((g₀ w[k]).word i).length ≤ tierOffset g₀ i w k' := by
  rw [← tierOffset_succ g₀ i w hk]
  exact tierOffset_mono g₀ i w h

theorem tierOffset_length :
    tierOffset g₀ i w w.length = ((w.map g₀).prod.word i).length := by
  simp [tierOffset, word_prod, List.length_flatten, Function.comp_def]

variable {g₀ w} {i j : ι} {p q : ℕ}

/-- When the primitives have at most one token on each of two tiers, the lines of a
realization between them are the lines of its symbols, each at that symbol's offsets. -/
theorem link_prod_map_of_length_le_one (hi : ∀ s, ((g₀ s).word i).length ≤ 1)
    (hj : ∀ s, ((g₀ s).word j).length ≤ 1) :
    (w.map g₀).prod.Link i j p q ↔ ∃ k, ∃ hk : k < w.length,
      p = tierOffset g₀ i w k ∧ q = tierOffset g₀ j w k ∧ (g₀ w[k]).Link i j 0 0 := by
  rw [link_prod_map]
  constructor
  · rintro ⟨k, hk, hp, hq, h⟩
    have h₁ := h.lt_left
    have h₂ := h.lt_right
    have := hi w[k]
    have := hj w[k]
    obtain rfl : p = tierOffset g₀ i w k := by omega
    obtain rfl : q = tierOffset g₀ j w k := by omega
    exact ⟨k, hk, rfl, rfl, by simpa using h⟩
  · rintro ⟨k, hk, rfl, rfl, h⟩
    exact ⟨k, hk, le_rfl, le_rfl, by simpa using h⟩

end Offset

section Realization

variable {S : Type*} (g₀ : S → AR τ) {w : List S} {j : ι} {m n k : ℕ}

/-- Spreading tier `j` from the `m`th symbol of a realization onto the `n`th: the token of the
`n`th symbol on the tier above `j` is delinked from its own token on `j` and linked to that of
the `m`th symbol. -/
def spreadTier (w : List S) (j : ι) (m n : ℕ) : AR τ :=
  ((w.map g₀).prod.eraseLine (T.parent j) j (tierOffset g₀ (T.parent j) w n)
      (tierOffset g₀ j w n)).addLine
    (T.parent j) j (tierOffset g₀ (T.parent j) w n) (tierOffset g₀ j w m)

/-- Reading a realization at slot `k` is reading the primitive of its `k`th symbol. -/
theorem reads_prod_map (h : ∀ s, ((g₀ s).word T.root).length = 1) {b : τ j} :
    (w.map g₀).prod.Reads T k j b ↔ ∃ hk : k < w.length, (g₀ w[k]).Reads T 0 j b := by
  induction w generalizing k with
  | nil => simp [Reads]
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons]
    cases k with
    | zero =>
      rw [reads_mul_left (by rw [h]; exact Nat.one_pos)]
      exact ⟨fun hr ↦ ⟨Nat.succ_pos _, hr⟩, fun ⟨_, hr⟩ ↦ hr⟩
    | succ k =>
      have key : (g₀ a * (w.map g₀).prod).Reads T (k + 1) j b ↔
          (w.map g₀).prod.Reads T k j b := by
        have := reads_mul_right (T := T) (X := g₀ a) (Y := (w.map g₀).prod) (k := k) (b := b)
        rwa [h a] at this
      rw [key, ih]
      exact ⟨fun ⟨hk, hr⟩ ↦ ⟨Nat.succ_lt_succ hk, hr⟩,
        fun ⟨hk, hr⟩ ↦ ⟨Nat.lt_of_succ_lt_succ hk, hr⟩⟩

omit [Fintype ι] in
/-- Spreading a tier crosses no line exactly when no symbol strictly between the two has a line
between that tier and the one above it. -/
theorem noCrossing_spreadTier_iff (hj : j ≠ T.root)
    (hp : ∀ s, ((g₀ s).word (T.parent j)).length ≤ 1) (hc : ∀ s, ((g₀ s).word j).length ≤ 1)
    (hm : m < w.length) (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ [])
    (hnp : (g₀ w[n]).word (T.parent j) ≠ []) (hw : (w.map g₀).prod.NoCrossing) :
    (spreadTier T g₀ w j m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → ¬ (g₀ w[k]).Link (T.parent j) j 0 0 := by
  have hij : T.parent j ≠ j := fun h ↦ hj (T.eq_root_of_iterate_eq (n := 1) one_ne_zero h)
  have huIoo : ∀ k, k ∈ Set.uIoo m n ↔ m < k ∧ k < n ∨ n < k ∧ k < m := fun k ↦ by
    simp only [Set.uIoo, Set.mem_Ioo, inf_lt_iff, lt_sup_iff]
    omega
  have hX : ∀ {p q}, (w.map g₀).prod.Link (T.parent j) j p q ↔ ∃ k, ∃ hk : k < w.length,
      p = tierOffset g₀ (T.parent j) w k ∧ q = tierOffset g₀ j w k ∧
        (g₀ w[k]).Link (T.parent j) j 0 0 := link_prod_map_of_length_le_one hp hc
  have mono := fun i ↦ tierOffset_mono g₀ i w
  have strict : ∀ {i : ι} {k k' : ℕ} (hk : k < w.length), k < k' → (g₀ w[k]).word i ≠ [] →
      tierOffset g₀ i w k < tierOffset g₀ i w k' := fun {i k k'} hk hlt hne ↦
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (List.length_pos_iff.2 hne))
      (tierOffset_add_length_le g₀ i w hlt hk)
  have hpn : tierOffset g₀ (T.parent j) w n < ((w.map g₀).prod.word (T.parent j)).length := by
    rw [← tierOffset_length]
    exact strict hn hn hnp
  have hqm : tierOffset g₀ j w m < ((w.map g₀).prod.word j).length := by
    rw [← tierOffset_length]
    exact strict hm hm hmj
  have hZ : ∀ {i' j' p q}, (spreadTier T g₀ w j m n).Link i' j' p q ↔
      ((w.map g₀).prod.Link i' j' p q ∧
        ¬ (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w n) ∧
        ¬ (i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w n ∧
          q = tierOffset g₀ (T.parent j) w n)) ∨
      (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w m ∨
        i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w m ∧
          q = tierOffset g₀ (T.parent j) w n) := by
    intro i' j' p q
    rw [spreadTier, link_addLine, link_eraseLine, word_eraseLine]
    exact or_congr_right
      ((and_iff_right hij).trans ((and_iff_right hpn).trans (and_iff_right hqm)))
  constructor
  · intro hnc k hk hkmn hl
    have hki : (g₀ w[k]).word (T.parent j) ≠ [] := List.ne_nil_of_length_pos hl.lt_left
    have hkj : (g₀ w[k]).word j ≠ [] := List.ne_nil_of_length_pos hl.lt_right
    have nc := isNonCrossing_lines_iff.1 (hnc (T.parent j) j)
    have hnew : (spreadTier T g₀ w j m n).Link (T.parent j) j
        (tierOffset g₀ (T.parent j) w n) (tierOffset g₀ j w m) :=
      hZ.2 (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))
    rcases (huIoo k).1 hkmn with ⟨hmk, hkn⟩ | ⟨hnk, hkm⟩
    · have hold : (spreadTier T g₀ w j m n).Link (T.parent j) j
          (tierOffset g₀ (T.parent j) w k) (tierOffset g₀ j w k) :=
        hZ.2 (.inl ⟨hX.2 ⟨k, hk, rfl, rfl, hl⟩, fun h ↦ (strict hk hkn hki).ne h.2.2.1,
          fun h ↦ hij h.1⟩)
      exact absurd (nc hold hnew (strict hk hkn hki)) (not_le.2 (strict hm hmk hmj))
    · have hold : (spreadTier T g₀ w j m n).Link (T.parent j) j
          (tierOffset g₀ (T.parent j) w k) (tierOffset g₀ j w k) :=
        hZ.2 (.inl ⟨hX.2 ⟨k, hk, rfl, rfl, hl⟩, fun h ↦ (strict hn hnk hnp).ne' h.2.2.1,
          fun h ↦ hij h.1⟩)
      exact absurd (nc hnew hold (strict hn hnk hnp)) (not_le.2 (strict hk hkm hkj))
  · intro hR i' j'
    refine isNonCrossing_lines_iff.2 fun p q p' q' h₁ h₂ hlt ↦ ?_
    have key₁ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ (T.parent j) w k < tierOffset g₀ (T.parent j) w n →
          tierOffset g₀ j w k ≤ tierOffset g₀ j w m := fun {k} hk hl h ↦ by
      have hkn : k < n := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hmk ↦ hR k hk ((huIoo k).2 (.inl ⟨hmk, hkn⟩)) hl)
    have key₂ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ (T.parent j) w n < tierOffset g₀ (T.parent j) w k →
          tierOffset g₀ j w m ≤ tierOffset g₀ j w k := fun {k} hk hl h ↦ by
      have hnk : n < k := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hkm ↦ hR k hk ((huIoo k).2 (.inr ⟨hnk, hkm⟩)) hl)
    have key₃ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ j w k < tierOffset g₀ j w m →
          tierOffset g₀ (T.parent j) w k ≤ tierOffset g₀ (T.parent j) w n := fun {k} hk hl h ↦ by
      have hkm : k < m := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hnk ↦ hR k hk ((huIoo k).2 (.inr ⟨hnk, hkm⟩)) hl)
    have key₄ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ j w m < tierOffset g₀ j w k →
          tierOffset g₀ (T.parent j) w n ≤ tierOffset g₀ (T.parent j) w k := fun {k} hk hl h ↦ by
      have hmk : m < k := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hkn ↦ hR k hk ((huIoo k).2 (.inl ⟨hmk, hkn⟩)) hl)
    rcases hZ.1 h₁ with ⟨hx₁, -, -⟩ | ⟨hi₁, hj₁, hp₁, hq₁⟩ | ⟨hi₁, hj₁, hp₁, hq₁⟩ <;>
      rcases hZ.1 h₂ with ⟨hx₂, -, -⟩ | ⟨hi₂, hj₂, hp₂, hq₂⟩ | ⟨hi₂, hj₂, hp₂, hq₂⟩
    · exact isNonCrossing_lines_iff.1 (hw i' j') hx₁ hx₂ hlt
    · subst hi₂ hj₂ hp₂ hq₂
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₁
      exact key₁ hk hl hlt
    · subst hi₂ hj₂ hp₂ hq₂
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₁.symm
      exact key₃ hk hl hlt
    · subst hi₁ hj₁ hp₁ hq₁
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₂
      exact key₂ hk hl hlt
    · subst hp₁ hp₂
      exact absurd hlt (lt_irrefl _)
    · exact absurd (hi₁.symm.trans hi₂) hij
    · subst hi₁ hj₁ hp₁ hq₁
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₂.symm
      exact key₄ hk hl hlt
    · exact absurd (hi₂.symm.trans hi₁) hij
    · subst hp₁ hp₂
      exact absurd hlt (lt_irrefl _)

end Realization

/-! ### Two tiers -/

section TwoTier

open Tier

universe u

variable {α β : Type u} {X : AR (TwoTier α β)} {a : α} {j q : ℕ}

/-- The tree of two tiers, the autosegments over their slots. -/
def twoTier : ParentTree Tier := .ofIterate (fun _ ↦ lower) lower 1 fun _ ↦ rfl

theorem dominates_twoTier_upper_iff : X.Dominates twoTier j upper q ↔ X.Link upper lower q j := by
  rw [Dominates, Tier.card]
  simp only [descendants, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨⟨t, p⟩, hc, rfl | ⟨⟨t', p'⟩, hc', rfl⟩⟩)
    · exact absurd (congrArg Prod.fst h) (by decide)
    · exact (mem_children.1 hc).2.2.symm
    · exact absurd (mem_children.1 hc').1.symm (mem_children.1 hc).2.1
  · exact fun h ↦ .inr ⟨(upper, q), mem_children.2 ⟨rfl, by decide, h.symm⟩, .inl rfl⟩

/-- On two tiers, a slot reads the labels of the autosegments linked to it. -/
theorem reads_twoTier_upper_iff : X.Reads twoTier j upper a ↔ X.SurfacesWith a j := by
  simp only [Reads, dominates_twoTier_upper_iff, SurfacesWith, Finset.mem_range]
  exact ⟨fun ⟨q, -, h, hb⟩ ↦ ⟨q, h, hb⟩, fun ⟨q, h, hb⟩ ↦ ⟨q, h.lt_left, h, hb⟩⟩

theorem reads_primitive_iff {as : List α} {b : β} :
    (primitive as b).Reads twoTier 0 upper a ↔ a ∈ as := by
  rw [reads_twoTier_upper_iff, List.mem_iff_getElem?]
  simp only [SurfacesWith, link_primitive, word_primitive_upper]
  exact ⟨fun ⟨k, -, h⟩ ↦ ⟨k, h⟩,
    fun ⟨k, h⟩ ↦ ⟨k, ⟨(List.getElem?_eq_some_iff.1 h).1, rfl⟩, h⟩⟩

/-- A realization by primitives reads at each slot the melody of its symbol. -/
theorem reads_prod_map_primitive {S : Type*} (as : S → List α) (b : S → β) {w : List S}
    {k : ℕ} :
    (w.map fun s ↦ primitive (as s) (b s)).prod.Reads twoTier k upper a ↔
      ∃ hk : k < w.length, a ∈ as w[k] :=
  (reads_prod_map twoTier _ fun _ ↦ rfl).trans (exists_congr fun _ ↦ reads_primitive_iff)

end TwoTier

end Autosegmental.AR
