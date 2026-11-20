module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.RelClasses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Linglib.Core.Order.PiLex

/-!
# Constraint rankings

This file defines a [ranking](##Ranking.Enumeration) of the constraints `ι` as an enumeration
`r : Fin n ≃ ι` of them in rank order, position `0` the most dominant, which presents Prince's
total domination order. It defines the [strict dominance](##Ranking.Enumeration.Dominates) of a
ranking and its [reflexive closure](##Ranking.Enumeration.toRel), which
[determines the ranking](##Ranking.Enumeration.toRel_injective). A ranking reads a violation
vector `v` in rank order as `toLex (v ∘ r)`, so comparing two vectors under one ranking is
the lexicographic order `Pi.Lex r.Dominates (· < ·)` of the constraints under dominance
(`Pi.toLex_comp_lt_toLex_comp_iff`), and comparing them under every ranking is the product order
(`OptimalityTheory.Ranking.Enumeration.forall_profile_lt_iff`), which is harmonic bounding. Rankings carry the discrete
σ-algebra, so a distribution over rankings is a `Measure`.

## Implementation notes

A ranking is stored as an enumeration rather than as an order relation, so that rankings can be
enumerated and compared decidably. The length `n` is a parameter rather than `Fintype.card ι`, so
that a ranking of `Fin n` is literally a permutation, and `card_eq` recovers the cardinality.

## References

* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
-/

@[expose] public section

namespace OptimalityTheory

/-- A ranking of the constraints `ι` into `n` rank positions (Prince's total domination order
`≫`). Here `r p` is the constraint at rank position `p`, position `0` is the most dominant, and
`r.symm i` is the rank position of `i`. -/
abbrev Ranking.Enumeration (ι : Type*) (n : ℕ) := Fin n ≃ ι

variable {ι : Type*} {n : ℕ}

/-- There are finitely many rankings of `n` constraints, and every set of them is measurable. -/
instance : MeasurableSpace (Ranking.Enumeration ι n) := ⊤

instance : DiscreteMeasurableSpace (Ranking.Enumeration ι n) := ⟨fun _ ↦ trivial⟩

theorem total_eq_of_le {α : Type*} {r s : α → α → Prop}
    [ht : Std.Total r] [ha : Std.Antisymm s] (h : r ≤ s) : r = s := by
  refine le_antisymm h fun a b hs => ?_
  rcases ht.total a b with hr | hr
  · exact hr
  · obtain rfl := ha.antisymm _ _ hs (h b a hr)
    exact (ht.total a a).elim id id

/-- A ranking of the constraints `ι` is an enumeration of all of them, most dominant first, indexed
by `Fin (Fintype.card ι)`, so that what is proved of an arbitrary `Ranking.Enumeration ι n` holds of
it. -/
abbrev Ranking (ι : Type*) [Fintype ι] := Ranking.Enumeration ι (Fintype.card ι)

/-- The ranking a list of all the constraints enumerates, most dominant first. -/
def Ranking.ofList [Fintype ι] [DecidableEq ι] (l : List ι) (hl : l.Nodup := by decide)
    (hc : ∀ i, i ∈ l := by decide) : Ranking ι :=
  (finCongr ((Fintype.card_congr (hl.getEquivOfForallMemList l hc)).symm.trans
    (Fintype.card_fin _))).trans (hl.getEquivOfForallMemList l hc)

namespace Ranking.Enumeration

theorem card_eq [Fintype ι] (r : Ranking.Enumeration ι n) : Fintype.card ι = n := by
  simpa using Fintype.card_congr r.symm

/-- The ranking a list of all the constraints enumerates, most dominant first. -/
def ofList [DecidableEq ι] (l : List ι) (hl : l.Nodup := by decide)
    (hc : ∀ i, i ∈ l := by decide) : Ranking.Enumeration ι l.length :=
  hl.getEquivOfForallMemList l hc

@[simp] theorem ofList_apply [DecidableEq ι] {l : List ι} {hl : l.Nodup} {hc : ∀ i, i ∈ l}
    (p : Fin l.length) : ofList l hl hc p = l[p] :=
  rfl

variable (r : Ranking.Enumeration ι n)

/-- Constraint `i` dominates constraint `j` under `r` if `i` has a lower (more dominant) rank
position than `j`. -/
def Dominates (i j : ι) : Prop := r.symm i < r.symm j

instance (i j : ι) : Decidable (r.Dominates i j) :=
  inferInstanceAs (Decidable (r.symm i < r.symm j))

instance : IsStrictTotalOrder ι r.Dominates := InvImage.isStrictTotalOrder r.symm.injective

instance : WellFounded r.Dominates := InvImage.wf r.symm wellFounded_lt

@[simp] theorem dominates_apply_iff {p q : Fin n} : r.Dominates (r p) (r q) ↔ p < q := by
  simp [Dominates]

/-- A ranking acts on a lex-ordered vector by reordering it by rank, so that coordinate `p` of `r •
v` is the value of `v` at the constraint ranked `p`-th. With this convention the action of `Sₙ` is a
right action, `(r * s) • v = s • r • v`. -/
instance {α : Type*} : SMul (Ranking.Enumeration (Fin n) n) (Lex (Fin n → α)) :=
  ⟨fun r v => toLex fun p => ofLex v (r p)⟩

@[simp] theorem smul_apply {α : Type*} (r : Ranking.Enumeration (Fin n) n) (v : Lex (Fin n → α))
    (p : Fin n) :
    ofLex (r • v) p = ofLex v (r p) := rfl

@[simp] theorem one_smul {α : Type*} (v : Lex (Fin n → α)) : (1 : Ranking.Enumeration
    (Fin n) n) • v = v :=
  rfl

/-! ### Adjacent transpositions -/

section AdjacentTranspositions

/-- The ranking that transposes the constraints at the adjacent rank positions `k` and `k + 1`.
Two rankings related by an adjacent transposition are neighbours in the permutohedron of
rankings. -/
def swapAt (k : ℕ) (hk : k + 1 < n) : Ranking.Enumeration ι n :=
  (Equiv.swap ⟨k, Nat.lt_of_succ_lt hk⟩ ⟨k + 1, hk⟩).trans r

variable {r} {k : ℕ} {hk : k + 1 < n}

@[simp] theorem swapAt_apply_left : r.swapAt k hk ⟨k, Nat.lt_of_succ_lt hk⟩ = r ⟨k + 1, hk⟩ := by
  simp [swapAt]

@[simp] theorem swapAt_apply_right : r.swapAt k hk ⟨k + 1, hk⟩ = r ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  simp [swapAt]

theorem swapAt_apply_of_ne {j : Fin n} (h₁ : j.val ≠ k) (h₂ : j.val ≠ k + 1) :
    r.swapAt k hk j = r j := by
  rw [swapAt, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne h₁)
    (Fin.ne_of_val_ne h₂)]

@[simp] theorem swapAt_swapAt : (r.swapAt k hk).swapAt k hk = r := by
  ext j
  simp [swapAt]

end AdjacentTranspositions

/-! ### The top constraints of a ranking -/

/-- The top `k` constraints of a ranking. -/
def take (k : Fin (n + 1)) : Finset ι :=
  ({p : Fin n | (p : ℕ) < k} : Finset (Fin n)).map r.toEmbedding

@[simp] theorem mem_take {k : Fin (n + 1)} {i : ι} : i ∈ r.take k ↔ (r.symm i : ℕ) < k := by
  simp only [take, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem card_take (k : Fin (n + 1)) : (r.take k).card = k := by
  rw [take, Finset.card_map, Fin.card_filter_val_lt, min_eq_right (Nat.lt_succ_iff.mp k.isLt)]

@[simp] theorem take_zero : r.take 0 = ∅ := by
  ext; simp

@[simp] theorem take_last [Fintype ι] : r.take (Fin.last n) = Finset.univ := by
  ext; simp

theorem take_succ [DecidableEq ι] (k : Fin n) :
    r.take k.succ = insert (r k) (r.take k.castSucc) := by
  ext i
  simp only [mem_take, Finset.mem_insert, Fin.val_succ, Fin.val_castSucc]
  refine ⟨fun h ↦ (Nat.lt_succ_iff_lt_or_eq.mp h).symm.imp (fun h' ↦ ?_) id, ?_⟩
  · rw [← Fin.ext h', Equiv.apply_symm_apply]
  · rintro (rfl | h')
    · rw [Equiv.symm_apply_apply]; omega
    · omega

theorem apply_notMem_take (k : Fin n) : r k ∉ r.take k.castSucc := by
  simp

theorem mem_take_of_dominates {k : Fin (n + 1)} {i j : ι} (h : r.Dominates i j)
    (hj : j ∈ r.take k) : i ∈ r.take k := by
  rw [mem_take] at hj ⊢
  exact lt_trans (Fin.lt_def.mp h) hj

/-- A set of constraints that dominate every constraint outside it is a prefix. -/
theorem exists_take_eq (D : Finset ι) (hD : ∀ i ∈ D, ∀ j ∉ D, r.Dominates i j) :
    ∃ k, r.take k = D := by
  have hcard : D.card ≤ n :=
    (D.card_map r.symm.toEmbedding ▸ Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  refine ⟨⟨D.card, Nat.lt_succ_of_le hcard⟩, Finset.eq_of_subset_of_card_le (fun j hj ↦ ?_)
    (by rw [card_take])⟩
  by_contra hjD
  rw [mem_take] at hj
  have hsub : D ⊆ r.take ⟨r.symm j, by omega⟩ := fun i hi ↦
    (mem_take r).mpr (Fin.lt_def.mp (hD i hi j hjD))
  have := Finset.card_le_card hsub
  rw [card_take] at this
  exact absurd hj (not_lt.mpr this)

/-! ### The ranking as a total order -/

/-- The relation "`i` is ranked at least as high as `j`". It is the reflexive closure of
`Dominates` (`toRel_iff`) and a total order on the constraints. -/
def toRel : ι → ι → Prop := fun i j => r.symm i ≤ r.symm j

instance (i j : ι) : Decidable (r.toRel i j) :=
  inferInstanceAs (Decidable (r.symm i ≤ r.symm j))

instance : IsPartialOrder ι r.toRel where
  refl _ := le_refl _
  trans _ _ _ := le_trans
  antisymm _ _ h₁ h₂ := r.symm.injective (le_antisymm h₁ h₂)

instance : Std.Total r.toRel := ⟨fun _ _ => le_total _ _⟩

theorem toRel_iff {i j : ι} : r.toRel i j ↔ i = j ∨ r.Dominates i j := by
  unfold toRel Dominates
  rw [le_iff_lt_or_eq, or_comm, r.symm.injective.eq_iff]

theorem toRel_iff_dominates {i j : ι} (hij : i ≠ j) :
    r.toRel i j ↔ r.Dominates i j := by
  rw [toRel_iff]
  simp [hij]

variable {r} {σ τ : Ranking.Enumeration ι n}

theorem toRel_injective : Function.Injective (toRel (ι := ι) (n := n)) := by
  intro σ τ h
  have hmono : Monotone (⇑τ.symm ∘ ⇑σ) := by
    intro a b hab
    have hrel : σ.toRel (σ a) (σ b) := by
      show σ.symm (σ a) ≤ σ.symm (σ b)
      simpa using hab
    rw [h] at hrel
    exact hrel
  have hcomp := (hmono.strictMono_of_injective (τ.symm.injective.comp σ.injective)).eq_id
  exact Equiv.ext fun k => (Equiv.symm_apply_eq τ).mp (congr_fun hcomp k)

theorem toRel_le_toRel_iff : σ.toRel ≤ τ.toRel ↔ σ = τ :=
  ⟨fun h => toRel_injective (total_eq_of_le h), fun h => h ▸ le_refl _⟩

/-- Every linear order on the constraints is the order `toRel` of some ranking (compare
`toRel_injective`). -/
theorem exists_toRel_eq [Fintype ι] (s : ι → ι → Prop) [IsLinearOrder ι s]
    (h : Fintype.card ι = n := by simp) : ∃ σ : Ranking.Enumeration ι n, σ.toRel = s := by
  classical
  have hlen : (Finset.univ.sort s).length = n := by simp [h]
  let e : Fin (Finset.univ.sort s).length ≃ ι :=
    List.Nodup.getEquivOfForallMemList _ (Finset.sort_nodup _ _)
      fun x => by simp
  refine ⟨(finCongr hlen).symm.trans e, total_eq_of_le fun a b hab => ?_⟩
  have h := (Finset.pairwise_sort _ _).rel_get_of_le
    (show e.symm a ≤ e.symm b from hab)
  rwa [show (Finset.univ.sort s).get (e.symm a) = a from e.apply_symm_apply a,
    show (Finset.univ.sort s).get (e.symm b) = b from e.apply_symm_apply b] at h

/-- If `f` maps the constraints injectively into a linear order, some ranking orders them by their
values under `f`. -/
theorem exists_dominates_iff [Fintype ι] {β : Type*} [LinearOrder β] (f : ι → β)
    (hf : Function.Injective f) (h : Fintype.card ι = n := by simp) :
    ∃ σ : Ranking.Enumeration ι n, ∀ i j, σ.Dominates i j ↔ f i < f j := by
  let _ : LinearOrder ι := LinearOrder.lift' f hf
  obtain ⟨σ, hσ⟩ := exists_toRel_eq (ι := ι) (· ≤ ·) h
  refine ⟨σ, fun i j ↦ ?_⟩
  have := congrFun₂ hσ j i
  simp only [toRel] at this
  rw [Dominates, ← not_le, this, not_le]
  rfl

/-- Some ranking puts a given constraint above every other. -/
theorem exists_forall_dominates [Fintype ι] (i : ι) (hn : Fintype.card ι = n := by simp) :
    ∃ σ : Ranking.Enumeration ι n, ∀ j, j ≠ i → σ.Dominates i j := by
  classical
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  let σ : Fin n ≃ ι := (Equiv.swap ⟨0, (e.symm i).pos⟩ (e.symm i)).trans e
  have hi : σ.symm i = ⟨0, (e.symm i).pos⟩ := by simp [σ]
  refine ⟨σ, fun j hj ↦ ?_⟩
  rw [Dominates, hi, Fin.lt_def]
  exact Nat.pos_of_ne_zero fun h0 ↦ hj <| σ.symm.injective <|
    Fin.ext (h0.trans (congrArg Fin.val hi).symm)

/-- Any two distinct constraints are ranked in either order by some ranking. -/
theorem exists_dominates [Fintype ι] {i j : ι} (hij : i ≠ j)
    (hn : Fintype.card ι = n := by simp) : ∃ σ : Ranking.Enumeration ι n, σ.Dominates i j :=
  (exists_forall_dominates i hn).imp fun _ h ↦ h j hij.symm

end Ranking.Enumeration
end OptimalityTheory
