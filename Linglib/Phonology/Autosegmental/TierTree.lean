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
public import Mathlib.Data.List.Sigma
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Representations along a tree of tiers

The tiers of a representation often form a tree, with the timing slots at the root and each
other tier hanging from one tier above it: a melody over its slots, the planes of a multiplanar
representation around their slots, the class nodes and features of a feature geometry under the
root node. For a tree of tiers `T : ParentTree ι`, the tokens a token is linked to on the tiers
hanging from its own are its `children`, and slot `k` dominates the tokens it reaches by
descending lines, `X.Dominates T k j q`. The melody associated with slot `k` on tier `j`,
`X.melody T k j`, lists the labels of the tokens of the tier that the slot dominates, in the order
of the tier (`mem_melody_iff_exists_dominates`); it is the part of the tier's melody `X.word j`
that the slot bears.
Descending lines lead from one token to another, `X.Dom T v w`, exactly when the second is
reached in as many steps as there are tiers (`dom_iff_mem_descendants`), so `Dominates` is `Dom`
from a slot (`dominates_iff_dom`). A representation is functional, `X.IsFunctional T`, when
each token has at most one line to each tier hanging from its own; a slot then dominates at
most one token on each tier (`IsFunctional.eq_of_dom`) and bears at most one label there
(`IsFunctional.length_melody_le_one`), and a realization whose primitives have at most one
token on each tier is functional (`isFunctional_prod_map`).

A realization `(w.map g₀).prod` whose primitives have one slot each bears at slot `k` the
melody that the primitive of its `k`th symbol bears at its slot (`melody_prod_map`).

Spreading a tier from the `m`th symbol onto the `n`th is a change of lines, `spreadTier`: the
token of the `n`th symbol on the tier above is delinked from its own token and linked to that
of the `m`th. When the primitives have at most one token on the two tiers, the
result has no crossing lines exactly when no symbol strictly between the two has a line between
those tiers (`noCrossing_spreadTier_iff`): a symbol with a token there blocks, and one without
is transparent.

On two tiers, with the autosegments over their slots, `twoTier`, a slot bears the labels of the
autosegments linked to it, which is `AR.SurfacesWith` (`mem_melody_twoTier_upper_iff`), and a
realization by `AR.primitive`s bears at each slot the melody of its symbol
(`melody_prod_map_primitive`), so that taking melodies inverts realization.

## TODO

* The graph of a tree of tiers is acyclic, so by `AR.noCrossing_iff_hasIntervalOrder_of_isAcyclic`
  a representation whose lines run along it obeys the No-Crossing Constraint exactly when it has
  an interval order.

## References

* [mccarthy-1981]
* [sagey-1986]
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

/-- The melody associated with slot `k` on tier `j`: the labels of the tokens of the tier that
the slot dominates, in the order of the tier. The melody of the whole tier is `X.word j`. -/
def melody (k : ℕ) (j : ι) : List (τ j) :=
  ((X.word j).zipIdx.filter fun x ↦ X.Dominates T k j x.2).map Prod.fst

/-- Each token has at most one line to each tier hanging from its own. -/
def IsFunctional : Prop :=
  ∀ ⦃j p q q'⦄, j ≠ T.root → X.Link (T.parent j) j p q → X.Link (T.parent j) j p q' → q = q'

/-- Descending lines lead from the token `v` to the token `w`. -/
def Dom (v w : ι × ℕ) : Prop := Relation.ReflTransGen (fun v w ↦ w ∈ X.children T v) v w

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

/-- A slot bears a label on a tier when it dominates a token of the tier with that label. -/
theorem mem_melody_iff_exists_dominates {k : ℕ} {j : ι} {b : τ j} :
    b ∈ X.melody T k j ↔ ∃ q, X.Dominates T k j q ∧ (X.word j)[q]? = some b := by
  simp only [melody, List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?,
    decide_eq_true_eq, Prod.exists, exists_and_right, exists_eq_right]
  exact exists_congr fun q ↦ and_comm

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

/-! ### Domination -/

theorem depth_of_mem_children {v w : ι × ℕ} (h : w ∈ X.children T v) :
    T.depth w.1 = T.depth v.1 + 1 := by
  obtain ⟨j, q⟩ := w
  obtain ⟨hp, hr, -⟩ := mem_children.1 h
  rw [T.depth_eq_depth_parent_add_one hr, hp]

theorem Dom.eq_or_depth_lt {v w : ι × ℕ} (h : X.Dom T v w) : v = w ∨ T.depth v.1 < T.depth w.1 := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hc ih =>
    have := depth_of_mem_children hc
    rcases ih with rfl | ih <;> right <;> omega

theorem Dom.mem_descendants {v w : ι × ℕ} (h : X.Dom T v w) :
    w ∈ X.descendants T (T.depth w.1 - T.depth v.1) v := by
  induction h with
  | refl => simp [descendants]
  | @tail b c hd hc ih =>
    have h1 := depth_of_mem_children hc
    have h2 : T.depth c.1 - T.depth v.1 = (T.depth b.1 - T.depth v.1) + 1 := by
      rcases Dom.eq_or_depth_lt (T := T) (X := X) hd with rfl | h2 <;> omega
    rw [h2]
    exact mem_descendants_succ_of_mem_children ih hc

theorem dom_of_mem_descendants : ∀ (d : ℕ) {v w : ι × ℕ}, w ∈ X.descendants T d v → X.Dom T v w
  | 0, v, w, h => by
    obtain rfl : w = v := by simpa [descendants] using h
    exact .refl
  | d + 1, v, w, h => by
    rw [descendants, Finset.mem_insert, Finset.mem_biUnion] at h
    obtain rfl | ⟨c, hc, h⟩ := h
    · exact .refl
    · exact .head hc (dom_of_mem_descendants d h)

/-- Domination is decided by the tokens reached in as many steps as there are tiers. -/
theorem dom_iff_mem_descendants {v w : ι × ℕ} :
    X.Dom T v w ↔ w ∈ X.descendants T (Fintype.card ι) v :=
  ⟨fun h ↦ descendants_mono (by have := T.depth_lt_card w.1; omega) _ h.mem_descendants,
    dom_of_mem_descendants _⟩

instance {v w : ι × ℕ} : Decidable (X.Dom T v w) := decidable_of_iff _ dom_iff_mem_descendants.symm

/-- A slot dominates a token exactly when descending lines lead to it. -/
theorem dominates_iff_dom {k q : ℕ} {j : ι} : X.Dominates T k j q ↔ X.Dom T (T.root, k) (j, q) :=
  dom_iff_mem_descendants.symm

/-- Nothing but a slot itself leads to it by descending lines. -/
theorem Dom.eq_of_root {v : ι × ℕ} {q : ℕ} (h : X.Dom T v (T.root, q)) : v = (T.root, q) := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨u, -, hc⟩
  · exact h.symm
  · exact absurd rfl (mem_children.1 hc).2.1

/-- On a tier hanging from the slots, a slot dominates the tokens it has a line to. -/
theorem dom_root_iff_mem_children {j : ι} {k q : ℕ} (hp : T.parent j = T.root) :
    X.Dom T (T.root, k) (j, q) ↔ j = T.root ∧ q = k ∨ (j, q) ∈ X.children T (T.root, k) := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with he | ⟨⟨i, p⟩, hu, hc⟩
    · exact .inl (Prod.mk.inj he)
    · obtain rfl : T.parent j = i := (mem_children.1 hc).1
      rw [hp] at hu hc
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Dom.eq_of_root hu)
      exact .inr hc
  · rintro (⟨rfl, rfl⟩ | h)
    exacts [.refl, .single h]

/-- A slot bears a label on a tier when descending lines lead from it to a token of the tier
with that label. -/
theorem mem_melody_iff_exists_dom {k : ℕ} {j : ι} {b : τ j} :
    b ∈ X.melody T k j ↔ ∃ q, X.Dom T (T.root, k) (j, q) ∧ (X.word j)[q]? = some b :=
  mem_melody_iff_exists_dominates.trans
    (exists_congr fun _ ↦ and_congr_left fun _ ↦ dominates_iff_dom)

theorem IsFunctional.eq_of_mem_children (h : X.IsFunctional T) {v : ι × ℕ} {j : ι} {q q' : ℕ}
    (hq : (j, q) ∈ X.children T v) (hq' : (j, q') ∈ X.children T v) : q = q' := by
  obtain ⟨-, hr, hl⟩ := mem_children.1 hq
  obtain ⟨hp, -, hl'⟩ := mem_children.1 hq'
  obtain ⟨i, p⟩ := v
  obtain rfl : T.parent j = i := hp
  exact h hr hl hl'

/-- A slot dominates at most one token on each tier. -/
theorem IsFunctional.eq_of_dom (h : X.IsFunctional T) {k : ℕ} {v v' : ι × ℕ}
    (hv : X.Dom T (T.root, k) v) (hv' : X.Dom T (T.root, k) v') (he : v.1 = v'.1) : v = v' := by
  induction hv generalizing v' with
  | refl =>
    rcases Relation.ReflTransGen.cases_tail hv' with rfl | ⟨u, -, hc⟩
    · rfl
    · obtain ⟨j, q⟩ := v'
      exact absurd he.symm (mem_children.1 hc).2.1
  | @tail u w hu hc ih =>
    obtain ⟨j, q⟩ := w
    obtain ⟨hp, hr, -⟩ := mem_children.1 hc
    rcases Relation.ReflTransGen.cases_tail hv' with rfl | ⟨u', hu', hc'⟩
    · exact absurd he hr
    · obtain ⟨j', q'⟩ := v'
      obtain rfl : j = j' := he
      obtain rfl : u = u' := ih hu' (hp.symm.trans (mem_children.1 hc').1)
      rw [h.eq_of_mem_children hc hc']

/-- With at most one line from each token to each lower tier, a slot bears at most one label on
each tier. -/
theorem IsFunctional.length_melody_le_one (h : X.IsFunctional T) (k : ℕ) (j : ι) :
    (X.melody T k j).length ≤ 1 := by
  have hnd : (((X.word j).zipIdx.filter fun x ↦ X.Dominates T k j x.2).map Prod.snd).Nodup :=
    List.Nodup.sublist (List.filter_sublist.map Prod.snd) (List.nodup_zipIdx_map_snd _)
  rw [melody, List.length_map, ← List.length_map (f := Prod.snd),
    ← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_one.2 fun q hq q' hq' ↦ ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq)
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq')
  have hd := of_decide_eq_true (List.mem_filter.1 hx).2
  have hd' := of_decide_eq_true (List.mem_filter.1 hx').2
  exact (Prod.mk.inj (h.eq_of_dom (dominates_iff_dom.1 hd) (dominates_iff_dom.1 hd') rfl)).2

/-- A position past the end of its tier is linked to nothing below it. -/
theorem descendants_eq_singleton {v : ι × ℕ} (hv : (X.word v.1).length ≤ v.2) (d : ℕ) :
    X.descendants T d v = {v} := by
  have hc : X.children T v = ∅ := Finset.eq_empty_of_forall_notMem fun ⟨j, q⟩ h ↦
    absurd (mem_children.1 h).2.2.lt_left (not_lt.2 hv)
  cases d with
  | zero => rfl
  | succ d => simp [descendants, hc]

/-- A slot past the end of the slots bears no label. -/
theorem notMem_melody_of_length_le {k : ℕ} (hk : (X.word T.root).length ≤ k) {j : ι} {b : τ j} :
    b ∉ X.melody T k j := by
  intro h
  obtain ⟨q, hq, hb⟩ := mem_melody_iff_exists_dominates.1 h
  rw [Dominates, descendants_eq_singleton (v := (T.root, k)) hk, Finset.mem_singleton] at hq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
  exact absurd (List.getElem?_eq_some_iff.1 hb).1 (not_lt.2 hk)

/-- A slot past the end of the slots bears no melody. -/
theorem melody_eq_nil_of_length_le {k : ℕ} (hk : (X.word T.root).length ≤ k) (j : ι) :
    X.melody T k j = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun _ ↦ notMem_melody_of_length_le hk

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

/-- A concatenation bears at a slot of its left factor the melody that factor does. -/
theorem melody_mul_left (hk : k < (X.word T.root).length) :
    (X * Y).melody T k j = X.melody T k j := by
  have hdom (q : ℕ) : (X * Y).Dominates T k j q ↔ X.Dominates T k j q := by
    rw [Dominates, Dominates, descendants_mul_left X Y _ (v := (T.root, k)) hk]
  have h₁ : ((X.word j).zipIdx.filter fun x ↦ (X * Y).Dominates T k j x.2) =
      (X.word j).zipIdx.filter fun x ↦ X.Dominates T k j x.2 :=
    List.filter_congr fun x _ ↦ decide_eq_decide.2 (hdom x.2)
  have h₂ : (((Y.word j).zipIdx (0 + (X.word j).length)).filter
      fun x ↦ (X * Y).Dominates T k j x.2) = [] :=
    List.filter_eq_nil_iff.2 fun x hx hd ↦ by
      have h1 := List.le_snd_of_mem_zipIdx hx
      have h2 : x.2 < (X.word j).length := lt_length_of_mem_descendants (v := (T.root, k)) hk
        ((hdom x.2).1 (of_decide_eq_true hd))
      omega
  rw [melody, melody, word_mul, List.zipIdx_append, List.filter_append, h₁, h₂, List.append_nil]

/-- A concatenation bears at a slot of its right factor the melody that factor does. -/
theorem melody_mul_right :
    (X * Y).melody T (k + (X.word T.root).length) j = Y.melody T k j := by
  have hd : (X * Y).descendants T (Fintype.card ι) (T.root, k + (X.word T.root).length) =
      (Y.descendants T (Fintype.card ι) (T.root, k)).image fun u ↦
        (u.1, (X.word u.1).length + u.2) := by
    rw [Nat.add_comm]
    exact descendants_mul_right X Y _ (T.root, k)
  have hdom (q : ℕ) : (X * Y).Dominates T (k + (X.word T.root).length) j q ↔
      (X.word j).length ≤ q ∧ Y.Dominates T k j (q - (X.word j).length) := by
    rw [Dominates, hd, Finset.mem_image]
    constructor
    · rintro ⟨⟨j', q'⟩, hq', he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨Nat.le_add_right _ _, by rwa [Dominates, Nat.add_sub_cancel_left]⟩
    · rintro ⟨hle, hq⟩
      exact ⟨(j, q - (X.word j).length), hq, by rw [Nat.add_sub_cancel' hle]⟩
  have h₁ : ((X.word j).zipIdx.filter
      fun x ↦ (X * Y).Dominates T (k + (X.word T.root).length) j x.2) = [] :=
    List.filter_eq_nil_iff.2 fun x hx hd' ↦ by
      have h1 := List.snd_lt_of_mem_zipIdx hx
      have h2 := ((hdom x.2).1 (of_decide_eq_true hd')).1
      omega
  have hz : (Y.word j).zipIdx (0 + (X.word j).length) =
      (Y.word j).zipIdx.map (Prod.map id (· + (X.word j).length)) := by
    rw [List.map_snd_add_zipIdx_eq_zipIdx, Nat.zero_add, Nat.add_zero]
  have h₂ : (((Y.word j).zipIdx.map (Prod.map id (· + (X.word j).length))).filter
      fun x ↦ (X * Y).Dominates T (k + (X.word T.root).length) j x.2).map Prod.fst =
      ((Y.word j).zipIdx.filter fun x ↦ Y.Dominates T k j x.2).map Prod.fst := by
    rw [List.filter_map, List.map_map]
    have hf : List.filter ((fun x : τ j × ℕ ↦
          decide ((X * Y).Dominates T (k + (X.word T.root).length) j x.2)) ∘
          Prod.map id (· + (X.word j).length)) (Y.word j).zipIdx =
        List.filter (fun x ↦ decide (Y.Dominates T k j x.2)) (Y.word j).zipIdx :=
      List.filter_congr fun x _ ↦ decide_eq_decide.2 (by
        show (X * Y).Dominates T _ j (x.2 + (X.word j).length) ↔ _
        rw [hdom, Nat.add_sub_cancel]
        exact and_iff_right (Nat.le_add_left _ _))
    rw [hf]
    exact List.map_congr_left fun x _ ↦ rfl
  rw [melody, melody, word_mul, List.zipIdx_append, List.filter_append, h₁, List.nil_append, hz, h₂]

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

/-- On a tier where every primitive has one token, a symbol's offset is its index. -/
theorem tierOffset_of_length_eq_one (h : ∀ s, ((g₀ s).word i).length = 1) {k : ℕ}
    (hk : k ≤ w.length) : tierOffset g₀ i w k = k := by
  simp [tierOffset, h, hk]

theorem length_word_prod_map_of_length_eq_one (h : ∀ s, ((g₀ s).word i).length = 1) :
    ((w.map g₀).prod.word i).length = w.length := by
  rw [← tierOffset_length, tierOffset_of_length_eq_one g₀ i w h le_rfl]

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

theorem tierOffset_lt_length {k : ℕ} (hk : k < w.length)
    (h : (g₀ w[k]).word i ≠ []) :
    tierOffset g₀ i w k < ((w.map g₀).prod.word i).length := by
  rw [← tierOffset_length]
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (List.length_pos_iff.2 h))
    (tierOffset_add_length_le g₀ i w hk hk)

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

/-- A realization whose primitives have at most one token on each tier is functional. -/
theorem isFunctional_prod_map (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1) :
    (w.map g₀).prod.IsFunctional T := by
  intro j p q q' _ hl hl'
  obtain ⟨k, hk, rfl, rfl, hl0⟩ :=
    (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hl
  obtain ⟨k', hk', he, rfl, hl0'⟩ :=
    (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hl'
  rw [eq_of_tierOffset_eq g₀ _ w hk hk' (List.ne_nil_of_length_pos hl0.lt_left)
    (List.ne_nil_of_length_pos hl0'.lt_left) he]

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

/-- A realization whose primitives have one slot each bears at slot `k` the melody that the
primitive of its `k`th symbol bears. -/
theorem melody_prod_map (h : ∀ s, ((g₀ s).word T.root).length = 1) (hk : k < w.length) :
    (w.map g₀).prod.melody T k j = (g₀ w[k]).melody T 0 j := by
  induction w generalizing k with
  | nil => simp at hk
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons]
    cases k with
    | zero => exact melody_mul_left (by rw [h]; exact Nat.one_pos)
    | succ k =>
      have key := melody_mul_right (T := T) (X := g₀ a) (Y := (w.map g₀).prod) (k := k) (j := j)
      rw [h a] at key
      rw [key]
      exact ih (Nat.lt_of_succ_lt_succ hk)

/-- A realization bears a label at slot `k` exactly when the primitive of its `k`th symbol
does. -/
theorem mem_melody_prod_map (h : ∀ s, ((g₀ s).word T.root).length = 1) {b : τ j} :
    b ∈ (w.map g₀).prod.melody T k j ↔ ∃ hk : k < w.length, b ∈ (g₀ w[k]).melody T 0 j := by
  by_cases hk : k < w.length
  · rw [melody_prod_map T g₀ h hk]
    exact ⟨fun hb ↦ ⟨hk, hb⟩, fun ⟨_, hb⟩ ↦ hb⟩
  · refine iff_of_false (notMem_melody_of_length_le ?_) fun ⟨hk', _⟩ ↦ hk hk'
    rw [length_word_prod_map_of_length_eq_one g₀ T.root w h]
    exact not_lt.1 hk

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

omit [Fintype ι] in
theorem link_spreadTier (hj : j ≠ T.root) (hm : m < w.length)
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
theorem mem_children_prod_map (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1)
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
  · rintro (h | ⟨⟨t, p⟩, hc, h | ⟨⟨t', p'⟩, hc', h⟩⟩)
    · exact absurd (congrArg Prod.fst h) (show upper ≠ lower by decide)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact (mem_children.1 hc).2.2.symm
    · exact absurd (mem_children.1 hc').1.symm (mem_children.1 hc).2.1
  · exact fun h ↦ .inr ⟨(upper, q), mem_children.2 ⟨rfl, by decide, h.symm⟩, .inl rfl⟩

/-- On two tiers, a slot bears the labels of the autosegments linked to it. -/
theorem mem_melody_twoTier_upper_iff : a ∈ X.melody twoTier j upper ↔ X.SurfacesWith a j := by
  simp only [mem_melody_iff_exists_dominates, dominates_twoTier_upper_iff, SurfacesWith]

/-- A primitive bears its melody. -/
theorem melody_primitive {as : List α} {b : β} : (primitive as b).melody twoTier 0 upper = as := by
  have h : ((primitive as b).word upper).zipIdx.filter
      (fun x ↦ (primitive as b).Dominates twoTier 0 upper x.2) =
      ((primitive as b).word upper).zipIdx :=
    List.filter_eq_self.2 fun x hx ↦ decide_eq_true (dominates_twoTier_upper_iff.2
      (link_primitive.2 ⟨by simpa using List.snd_lt_of_mem_zipIdx hx, rfl⟩))
  rw [melody, h, List.zipIdx_map_fst]
  rfl

/-- A realization by primitives bears at each slot the labels of the melody of its symbol. -/
theorem mem_melody_prod_map_primitive {S : Type*} (as : S → List α) (b : S → β) {w : List S}
    {k : ℕ} :
    a ∈ (w.map fun s ↦ primitive (as s) (b s)).prod.melody twoTier k upper ↔
      ∃ hk : k < w.length, a ∈ as w[k] :=
  (mem_melody_prod_map twoTier _ fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ by rw [melody_primitive])

/-- A realization by primitives bears at each slot the melody of its symbol. -/
theorem melody_prod_map_primitive {S : Type*} (as : S → List α) (b : S → β) {w : List S}
    {k : ℕ} (hk : k < w.length) :
    (w.map fun s ↦ primitive (as s) (b s)).prod.melody twoTier k upper = as w[k] :=
  (melody_prod_map twoTier _ (fun _ ↦ rfl) hk).trans melody_primitive

end TwoTier

end Autosegmental.AR
