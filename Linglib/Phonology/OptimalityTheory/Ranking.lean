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

A ranking of a constraint set indexed by `ι` ([prince-2002]'s total domination order `≫`) is an
enumeration `r : Fin n ≃ ι` of the constraints in rank order: `r p` is the constraint at rank
position `p`, position `0` most dominant, and `r.symm i` is the rank position of `i`;
`Ranking.ofList l` enumerates them in the order of a list `l` of all of them. For
`ι = Fin n` a ranking is a permutation, `Equiv.Perm (Fin n)`. `Ranking.Dominates` is the induced
strict dominance relation, a strict total order on the constraints, and `Ranking.toRel` its
reflexive closure, from which the ranking is recoverable (`toRel_le_toRel_iff`); `Ranking.take r k`
is the set of its top `k` constraints, and `Ranking.swapAt` transposes two adjacent ones. A
ranking reads a violation vector `v` in rank order as `toLex (v ∘ r)`; comparing two such readings is the lexicographic order along an enumeration
(`Pi.toLex_comp_lt_iff_exists` in `Core/Order/PiLex`), and comparing them under every ranking is
the product order (`Pi.forall_toLex_comp_lt_iff`), which is harmonic bounding. The `Tableau`
machinery evaluates under a ranking, and the elementary-ranking-condition layer
(`ElementaryRankingCondition.lean`) infers rankings from winner–loser pairs. Rankings carry the
discrete σ-algebra, so that a distribution over rankings, a partially ordered grammar's or
stochastic OT's, is a `Measure`.

## Implementation notes

A ranking is stored as the enumeration rather than as the order relation, so that rankings can be
enumerated and compared decidably; the relation is derived (`Dominates`). The length `n` is a
parameter rather than `Fintype.card ι`, so that a ranking of `Fin n` is literally a permutation;
`card_eq` recovers `Fintype.card ι = n` from any ranking, and a statement quantifying over all
rankings is vacuous when `n` does not match.

## References

* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
-/

@[expose] public section

namespace OptimalityTheory

/-- A ranking of the constraints `ι` into `n` rank positions, Prince's total domination order
`≫`, is an enumeration of the constraints in rank order: `r p` is the constraint at rank position
`p`, position `0` being the most dominant, and `r.symm i` is the rank position of `i`. -/
abbrev Ranking (ι : Type*) (n : ℕ) := Fin n ≃ ι

variable {ι : Type*} {n : ℕ}

/-- There are finitely many rankings of `n` constraints, and every set of them is measurable. -/
instance : MeasurableSpace (Ranking ι n) := ⊤

instance : DiscreteMeasurableSpace (Ranking ι n) := ⟨fun _ ↦ trivial⟩

/-- A total relation is maximal among antisymmetric relations, so an antisymmetric relation
above it in the pointwise lattice equals it. -/
theorem total_eq_of_le {α : Type*} {r s : α → α → Prop}
    [ht : Std.Total r] [ha : Std.Antisymm s] (h : r ≤ s) : r = s := by
  refine le_antisymm h fun a b hs => ?_
  rcases ht.total a b with hr | hr
  · exact hr
  · obtain rfl := ha.antisymm _ _ hs (h b a hr)
    exact (ht.total a a).elim id id

namespace Ranking

/-- A ranking enumerates all the constraints, so their number is the number of rank positions. -/
theorem card_eq [Fintype ι] (r : Ranking ι n) : Fintype.card ι = n := by
  simpa using Fintype.card_congr r.symm

/-- The ranking a list of all the constraints enumerates, most dominant first. -/
def ofList [DecidableEq ι] (l : List ι) (hl : l.Nodup := by decide)
    (hc : ∀ i, i ∈ l := by decide) : Ranking ι l.length :=
  hl.getEquivOfForallMemList l hc

@[simp] theorem ofList_apply [DecidableEq ι] {l : List ι} {hl : l.Nodup} {hc : ∀ i, i ∈ l}
    (p : Fin l.length) : ofList l hl hc p = l[p] :=
  rfl

variable (r : Ranking ι n)

/-- Constraint `i` dominates constraint `j` under `r` when it sits at a lower, more dominant,
rank position. -/
def Dominates (i j : ι) : Prop := r.symm i < r.symm j

instance (i j : ι) : Decidable (r.Dominates i j) :=
  inferInstanceAs (Decidable (r.symm i < r.symm j))

instance : IsStrictTotalOrder ι r.Dominates := InvImage.isStrictTotalOrder r.symm.injective

/-- Dominance between ranked positions is position order. -/
@[simp] theorem dominates_apply_iff {p q : Fin n} : r.Dominates (r p) (r q) ↔ p < q := by
  simp [Dominates]

/-- Under the identity ranking `1`, dominance is index order. -/
@[simp] theorem one_dominates_iff {i j : Fin n} : (1 : Ranking (Fin n) n).Dominates i j ↔ i < j :=
  Iff.rfl

/-- A ranking reads a lex-ordered vector in rank order, so that coordinate `p` of `r • v` is the
value of `v` at the constraint ranked `p`-th. With this convention the action of `Sₙ` is a right
action, `(r * s) • v = s • r • v`. -/
instance {α : Type*} : SMul (Ranking (Fin n) n) (Lex (Fin n → α)) :=
  ⟨fun r v => toLex fun p => ofLex v (r p)⟩

@[simp] theorem smul_apply {α : Type*} (r : Ranking (Fin n) n) (v : Lex (Fin n → α)) (p : Fin n) :
    ofLex (r • v) p = ofLex v (r p) := rfl

@[simp] theorem one_smul {α : Type*} (v : Lex (Fin n → α)) : (1 : Ranking (Fin n) n) • v = v :=
  rfl

/-- Any two distinct constraints can be ranked either way, so some ranking makes `i` dominate
`j`. -/
theorem exists_dominates {i j : Fin n} (hij : i ≠ j) :
    ∃ r : Ranking (Fin n) n, r.Dominates i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨1, one_dominates_iff.mpr h⟩
  · exact ⟨Equiv.swap i j, by simpa [Dominates] using h⟩

/-! ### Adjacent transpositions -/

section AdjacentTranspositions

/-- The ranking that transposes the constraints at the adjacent rank positions `k` and `k + 1`.
Two rankings related by an adjacent transposition are neighbours in the permutohedron of
rankings. -/
def swapAt (k : ℕ) (hk : k + 1 < n) : Ranking ι n :=
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

/-- Passing from the top `k` constraints to the top `k + 1` adds the constraint ranked `k`. -/
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

/-- A constraint that dominates a member of a prefix is in the prefix. -/
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

/-- The dominance-or-equal relation of a ranking holds of `i` and `j` when `i` is ranked at least
as high as `j`; it is the reflexive closure of `Dominates` (`toRel_iff`) and a total order on the
constraints. -/
def toRel : ι → ι → Prop := fun i j => r.symm i ≤ r.symm j

instance (i j : ι) : Decidable (r.toRel i j) :=
  inferInstanceAs (Decidable (r.symm i ≤ r.symm j))

instance : IsPartialOrder ι r.toRel where
  refl _ := le_refl _
  trans _ _ _ := le_trans
  antisymm _ _ h₁ h₂ := r.symm.injective (le_antisymm h₁ h₂)

instance : Std.Total r.toRel := ⟨fun _ _ => le_total _ _⟩

/-- `toRel` is the reflexive closure of `Dominates`. -/
theorem toRel_iff {i j : ι} : r.toRel i j ↔ i = j ∨ r.Dominates i j := by
  unfold toRel Dominates
  rw [le_iff_lt_or_eq, or_comm, r.symm.injective.eq_iff]

/-- On distinct constraints, `toRel` is `Dominates`. -/
theorem toRel_iff_dominates {i j : ι} (hij : i ≠ j) :
    r.toRel i j ↔ r.Dominates i j := by
  rw [toRel_iff]
  simp [hij]

/-- Relabeling constraints by `g` pulls the induced order back along `g⁻¹`. -/
@[simp] theorem toRel_mul (g σ : Ranking (Fin n) n) (i j : Fin n) :
    (g * σ).toRel i j ↔ σ.toRel (g⁻¹ i) (g⁻¹ j) := Iff.rfl

variable {r} {σ τ : Ranking ι n}

/-- A ranking is recoverable from its induced total order. -/
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

/-- Total orders comparable in the relation lattice coincide, so nothing sits strictly between two
ranking-induced orders. -/
theorem toRel_le_toRel_iff : σ.toRel ≤ τ.toRel ↔ σ = τ :=
  ⟨fun h => toRel_injective (total_eq_of_le h), fun h => h ▸ le_refl _⟩

/-- Every linear order on the constraints is the induced order of a ranking, the surjectivity
companion to `toRel_injective`: enumerate the constraints in `s`-order (`Finset.sort`) and read
off the ranking. -/
theorem exists_toRel_eq [Fintype ι] (s : ι → ι → Prop) [IsLinearOrder ι s]
    (h : Fintype.card ι = n := by simp) : ∃ σ : Ranking ι n, σ.toRel = s := by
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

/-- Constraints keyed injectively into a linear order are ranked by their keys. -/
theorem exists_dominates_iff [Fintype ι] {β : Type*} [LinearOrder β] (f : ι → β)
    (hf : Function.Injective f) (h : Fintype.card ι = n := by simp) :
    ∃ σ : Ranking ι n, ∀ i j, σ.Dominates i j ↔ f i < f j := by
  let _ : LinearOrder ι := LinearOrder.lift' f hf
  obtain ⟨σ, hσ⟩ := exists_toRel_eq (ι := ι) (· ≤ ·) h
  refine ⟨σ, fun i j ↦ ?_⟩
  have := congrFun₂ hσ j i
  simp only [toRel] at this
  rw [Dominates, ← not_le, this, not_le]
  rfl

end Ranking
end OptimalityTheory
