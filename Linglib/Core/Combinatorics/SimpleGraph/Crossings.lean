/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Enumerative.PermutationPattern
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Ring

/-!
# Crossings of a graph on a linear order

Draw the vertices of a finite graph on a line in the order of a linear order on them, and the edges
as arcs above the line. Two edges cross when their endpoints alternate, which requires that they
share no vertex. This file counts the crossings of a graph, `SimpleGraph.crossings`, and the pairs
of edges sharing no vertex, `SimpleGraph.disjointEdgePairs`, which
[bound them](##SimpleGraph.crossings_le_disjointEdgePairs) and do not depend on the order.

Averaged over all relabellings of the vertices, the crossings are
[a third of the disjoint pairs](##SimpleGraph.three_mul_sum_crossings_comap):
four distinct vertices fall in each of their relative orders equally often, and a third of the
orders alternate the two edges. The disjoint pairs are all pairs of edges
[but those meeting at a vertex](##SimpleGraph.disjointEdgePairs_add_sum_choose_degree), so in a
tree they are fixed by the number of vertices and the sum of the squared degrees, and that
sum [ranges](##SimpleGraph.IsTree.le_sum_degree_sq) between its value on a
[path](##SimpleGraph.IsTree.sum_degree_sq_of_degree_le_two) and
[its value on a star](##SimpleGraph.IsTree.sum_degree_sq_le).

## Implementation notes

* A relabelling is `G.comap σ` for a permutation `σ`, whose adjacency is decidable by unfolding.
* `disjointEdgePairs` counts each pair once by a representative chosen with the order: both edges
  least endpoint first, the edge starting earlier first. `disjointEdgePairs_comap` shows that the
  count does not depend on the order.
* Averages over relabellings are stated as sums with the divisions cleared.

## TODO

* `disjointEdgePairs` is the number of edges of the complement of `SimpleGraph.lineGraph`.
* The counts of darts are stated on pairs of vertices, not on `SimpleGraph.Dart`.

## References

* [ferrer-i-cancho-2017]
* [ferrer-i-cancho-2013]
-/

@[expose] public section

open Finset Equiv Nat

/-- Four elements of an order alternate when `a < c < b < d`, so that the pairs `{a, b}` and
`{c, d}` strictly interleave. -/
abbrev Alternate {α : Type*} [LT α] (a b c d : α) : Prop := a < c ∧ c < b ∧ b < d

namespace SimpleGraph

section Order

variable {α : Type*} [Fintype α] [LinearOrder α] (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The number of crossing pairs of edges: the quadruples `a < c < b < d` with edges `{a, b}` and
`{c, d}`. Of the two ways to order a crossing pair of edges, one alternates. -/
def crossings : ℕ :=
  #{x : α × α × α × α | G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧
    Alternate x.1 x.2.1 x.2.2.1 x.2.2.2}

/-- The number of unordered pairs of edges sharing no vertex. Each pair is counted once, by the
representative with both edges least endpoint first and the edge starting earlier first. -/
def disjointEdgePairs : ℕ :=
  #{x : α × α × α × α | G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧
    x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2 ∧ x.1 < x.2.2.1 ∧ x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2}

variable {G}

/-- Crossing edges share no vertex. -/
theorem crossings_le_disjointEdgePairs : G.crossings ≤ G.disjointEdgePairs := by
  refine card_le_card fun x hx ↦ ?_
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨h1, h2, hac, hcb, hbd⟩ := hx
  exact ⟨h1, h2, hac.trans hcb, hcb.trans hbd, hac, hcb.ne', hbd.ne⟩

theorem disjointEdgePairs_eq_zero_of_forall_adj {h : α}
    (hh : ∀ ⦃a b⦄, G.Adj a b → a = h ∨ b = h) : G.disjointEdgePairs = 0 := by
  rw [disjointEdgePairs, Finset.card_eq_zero, filter_eq_empty_iff]
  rintro ⟨a, b, c, d⟩ - ⟨h1, h2, hab, hcd, hac, hbc, hbd⟩
  rcases hh h1 with e1 | e1 <;> rcases hh h2 with e2 | e2 <;> dsimp only at * <;> order

/-! ### Crossings under a relabelling -/

private theorem crossings_comap_symm (σ : Perm α) :
    (G.comap σ.symm).crossings = #{x : α × α × α × α |
      G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧
        σ x.1 < σ x.2.2.1 ∧ σ x.2.2.1 < σ x.2.1 ∧ σ x.2.1 < σ x.2.2.2} := by
  refine Finset.card_equiv
    (σ.symm.prodCongr (σ.symm.prodCongr (σ.symm.prodCongr σ.symm))) ?_
  rintro ⟨a, b, c, d⟩
  simp

/-! ### One relabelling in twenty-four alternates a distinct quadruple -/

omit [Fintype α] in
private theorem alternate_comp_iff {a b c d : α} (σ : Perm α)
    (hq : Function.Injective ![a, c, b, d]) :
    σ a < σ c ∧ σ c < σ b ∧ σ b < σ d ↔ Monotone (σ ∘ ![a, c, b, d]) :=
  .trans (by simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_succ])
    ⟨StrictMono.monotone, (·.strictMono_of_injective (σ.injective.comp hq))⟩

private theorem card_alternate {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    24 * #{σ : Perm α | σ a < σ c ∧ σ c < σ b ∧ σ b < σ d} = (Fintype.card α)! := by
  have hq : Function.Injective ![a, c, b, d] := List.nodup_ofFn.mp (by simp [*, hbc.symm])
  simpa only [Function.Embedding.coeFn_mk, ← alternate_comp_iff _ hq,
    show (4 : ℕ)! = 24 from rfl] using
    Perm.factorial_mul_card_monotone_comp (⟨_, hq⟩ : Fin 4 ↪ α)

private theorem card_alternate_eq_zero {a b c d : α}
    (h : ¬(a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)) :
    #{σ : Perm α | σ a < σ c ∧ σ c < σ b ∧ σ b < σ d} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro σ - ⟨h1, h2, h3⟩
  refine h ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> order

/-! ### Summing over relabellings, grouped by quadruple -/

private def distinct4 (x : α × α × α × α) : Prop :=
  x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2.1 ∧ x.1 ≠ x.2.2.2 ∧
    x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2 ∧ x.2.2.1 ≠ x.2.2.2

private instance : DecidablePred (distinct4 (α := α)) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

private theorem sum_crossings_comap_symm :
    ∑ σ : Perm α, (G.comap σ.symm).crossings =
      ∑ x ∈ univ.filter (fun x : α × α × α × α ↦ G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2),
        #{σ : Perm α | σ x.1 < σ x.2.2.1 ∧ σ x.2.2.1 < σ x.2.1 ∧ σ x.2.1 < σ x.2.2.2} := by
  simp only [crossings_comap_symm, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  by_cases h1 : G.Adj x.1 x.2.1 <;> by_cases h2 : G.Adj x.2.2.1 x.2.2.2 <;>
    simp [h1, h2]

private theorem mul_sum_crossings_comap_symm :
    24 * ∑ σ : Perm α, (G.comap σ.symm).crossings =
      (Fintype.card α)! * #(univ.filter (fun x : α × α × α × α ↦
        (G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2) ∧ distinct4 x)) := by
  rw [sum_crossings_comap_symm, Finset.mul_sum]
  have hcongr : ∀ x ∈ univ.filter (fun x : α × α × α × α ↦
      G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2),
      24 * #{σ : Perm α | σ x.1 < σ x.2.2.1 ∧ σ x.2.2.1 < σ x.2.1 ∧ σ x.2.1 < σ x.2.2.2} =
        if distinct4 x then (Fintype.card α)! else 0 := by
    intro x _
    by_cases hd : distinct4 x
    · rw [ite_eq_left hd]
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
      exact card_alternate d1 d2 d3 d4 d5 d6
    · rw [ite_eq_right hd, card_alternate_eq_zero hd, Nat.mul_zero]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter, Finset.filter_filter,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Eight ordered witnesses per unordered disjoint pair -/

private theorem card_filter_eq_two_mul {β : Type*} [Fintype β] [DecidableEq β]
    {P C : β → Prop} [DecidablePred P] [DecidablePred C] (e : β → β)
    (he : Function.Involutive e) (hP : ∀ x, P x → P (e x))
    (hC : ∀ x, P x → (C (e x) ↔ ¬ C x)) :
    #(univ.filter P) = 2 * #(univ.filter (fun x ↦ P x ∧ C x)) := by
  rw [← Finset.filter_filter,
    ← Finset.card_filter_add_card_filter_not (s := univ.filter P) C, two_mul]
  congr 1
  refine Finset.card_equiv (he.toPerm e) (fun x ↦ ?_)
  simp only [mem_filter, mem_univ, true_and, Function.Involutive.coe_toPerm]
  grind [Function.Involutive]

private theorem card_adj_distinct :
    #(univ.filter (fun x : α × α × α × α ↦
        (G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2) ∧ distinct4 x)) =
      8 * G.disjointEdgePairs := by
  rw [card_filter_eq_two_mul (C := fun x ↦ x.1 < x.2.1) (fun x ↦ (x.2.1, x.1, x.2.2))
      (fun _ ↦ rfl) ?_ ?_,
    card_filter_eq_two_mul (C := fun x ↦ x.2.2.1 < x.2.2.2)
      (fun x ↦ (x.1, x.2.1, x.2.2.2, x.2.2.1)) (fun _ ↦ rfl) ?_ ?_,
    card_filter_eq_two_mul (C := fun x ↦ x.1 < x.2.2.1)
      (fun x ↦ (x.2.2.1, x.2.2.2, x.1, x.2.1)) (fun _ ↦ rfl) ?_ ?_,
    ← Nat.mul_assoc, ← Nat.mul_assoc, disjointEdgePairs]
  · congr 2
    refine filter_congr fun x _ ↦ ?_
    simp only [distinct4]
    grind
  all_goals rintro ⟨a, b, c, d⟩; simp only [distinct4]; grind [SimpleGraph.adj_comm]

/-! ### The average number of crossings -/

/-- The pairs of edges sharing no vertex do not depend on the order of the vertices. -/
theorem disjointEdgePairs_comap (σ : Perm α) :
    (G.comap σ).disjointEdgePairs = G.disjointEdgePairs := by
  refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) ?_
  rw [← card_adj_distinct, ← card_adj_distinct]
  refine card_equiv (σ.prodCongr (σ.prodCongr (σ.prodCongr σ))) ?_
  rintro ⟨a, b, c, d⟩
  simp [distinct4]

/-- No relabelling has more crossings than there are pairs of edges sharing no vertex. -/
theorem crossings_comap_le_disjointEdgePairs (σ : Perm α) :
    (G.comap σ).crossings ≤ G.disjointEdgePairs :=
  crossings_le_disjointEdgePairs.trans_eq (disjointEdgePairs_comap σ)

/-- Summed over all relabellings of the vertices, three times the number of crossings is the
number of relabellings times the number of pairs of edges sharing no vertex: a uniformly random
relabelling expects a third of those pairs to cross. -/
theorem three_mul_sum_crossings_comap :
    3 * ∑ σ : Perm α, (G.comap σ).crossings = (Fintype.card α)! * G.disjointEdgePairs := by
  have key := mul_sum_crossings_comap_symm (G := G)
  rw [card_adj_distinct, Nat.mul_left_comm,
    Fintype.sum_equiv (Equiv.inv (Perm α)) (fun σ ↦ (G.comap σ.symm).crossings)
      (fun σ ↦ (G.comap σ).crossings) fun _ ↦ rfl] at key
  omega

end Order

/-! ### Disjoint pairs of edges from the degrees

Ordered pairs of darts number `(2m)²` for `m` edges. Those sharing a vertex are counted from
each dart's endpoints: a dart `(a, b)` meets `2 (k_a + k_b) - 2` darts, which sums to
`4 ∑ k² - 4m`. -/

section Darts

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem sum_adj_fst (f : V → ℕ) :
    ∑ p ∈ ({p | G.Adj p.1 p.2} : Finset (V × V)), f p.1 = ∑ v, f v * G.degree v := by
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ ↦ ?_
  rw [← sum_filter]
  dsimp only
  rw [sum_const, smul_eq_mul, mul_comm, ← G.card_neighborFinset_eq_degree,
    G.neighborFinset_eq_filter]

private theorem sum_adj_snd (f : V → ℕ) :
    ∑ p ∈ ({p | G.Adj p.1 p.2} : Finset (V × V)), f p.2 = ∑ v, f v * G.degree v := by
  rw [← sum_adj_fst G f]
  exact sum_equiv (Equiv.prodComm V V) (by simp [G.adj_comm]) (by simp)

private theorem mul_pred_eq (m : ℕ) : m * (m - 1) = (4 * m - 6) + (m - 2) * (m - 3) := by
  rcases m with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · have h1 : m + 3 - 1 = m + 2 := rfl
    have h2 : 4 * (m + 3) - 6 = 4 * m + 6 := by omega
    have h3 : m + 3 - 2 = m + 1 := rfl
    have h4 : m + 3 - 3 = m := rfl
    rw [h1, h2, h3, h4]
    ring

private theorem three_mul_le_sq_add_two (k : ℕ) : 3 * k ≤ k ^ 2 + 2 := by
  rcases k with _ | _ | k
  · simp
  · simp
  · have : (k + 1 + 1) ^ 2 = k ^ 2 + 4 * k + 4 := by ring
    omega

private theorem sq_eq_two_mul_choose_add (k : ℕ) : k ^ 2 = 2 * k.choose 2 + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hc : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    omega

/-- Six times the number of edges is at most the sum of the squared degrees plus twice the number
of vertices, since `3 k ≤ k ^ 2 + 2` for every degree `k`. -/
theorem six_mul_card_edgeFinset_le :
    6 * #G.edgeFinset ≤ ∑ v, G.degree v ^ 2 + 2 * Fintype.card V := by
  have h : ∑ v, 3 * G.degree v ≤ ∑ v, (G.degree v ^ 2 + 2) :=
    sum_le_sum fun v _ ↦ three_mul_le_sq_add_two _
  rw [← mul_sum, G.sum_degrees_eq_twice_card_edges, sum_add_distrib, sum_const, Finset.card_univ,
    smul_eq_mul] at h
  omega

/-- Equality in `six_mul_card_edgeFinset_le` when every degree is one or two. -/
theorem six_mul_card_edgeFinset_eq (h1 : ∀ v, 1 ≤ G.degree v) (h2 : ∀ v, G.degree v ≤ 2) :
    6 * #G.edgeFinset = ∑ v, G.degree v ^ 2 + 2 * Fintype.card V := by
  have h : ∑ v, 3 * G.degree v = ∑ v, (G.degree v ^ 2 + 2) := sum_congr rfl fun v _ ↦ by
    obtain h | h : G.degree v = 1 ∨ G.degree v = 2 := by have := h1 v; have := h2 v; omega
    all_goals rw [h]; norm_num
  rw [← mul_sum, G.sum_degrees_eq_twice_card_edges, sum_add_distrib, sum_const, Finset.card_univ,
    smul_eq_mul] at h
  omega

/-- Relabelling the vertices permutes the degrees. -/
theorem sum_degree_sq_comap (σ : Perm V) :
    ∑ v, (G.comap σ).degree v ^ 2 = ∑ v, G.degree v ^ 2 :=
  Fintype.sum_equiv σ _ _ fun v ↦ congrArg (· ^ 2) ((Iso.comap σ G).degree_eq v).symm

variable [DecidableEq V]

private theorem card_adj_fst (v : V) : #{q : V × V | G.Adj q.1 q.2 ∧ q.1 = v} = G.degree v := by
  rw [← G.card_neighborFinset_eq_degree,
    ← card_image_of_injective (G.neighborFinset v) (Prod.mk_right_injective v)]
  refine congrArg card (ext fun q ↦ ?_)
  obtain ⟨x, y⟩ := q
  simp only [mem_filter, mem_univ, true_and, mem_image, SimpleGraph.mem_neighborFinset,
    Prod.mk.injEq]
  aesop

private theorem card_adj_snd (v : V) : #{q : V × V | G.Adj q.1 q.2 ∧ q.2 = v} = G.degree v := by
  rw [← card_adj_fst G v]
  exact card_equiv (Equiv.prodComm V V) fun q ↦ by simp [G.adj_comm]

/-- The darts sharing no vertex with an edge `{a, b}`, with twice the degrees of `a` and `b`,
are all the darts and two more: an edge shares a vertex with `k_a + k_b - 1` edges. -/
theorem card_disjoint_darts_add_degree {a b : V} (h : G.Adj a b) :
    #{q : V × V | G.Adj q.1 q.2 ∧ q.1 ≠ a ∧ q.1 ≠ b ∧ q.2 ≠ a ∧ q.2 ≠ b} +
      2 * (G.degree a + G.degree b) = 2 * #G.edgeFinset + 2 := by
  have hab : a ≠ b := h.ne
  set A : Finset (V × V) := {q | G.Adj q.1 q.2 ∧ (q.1 = a ∨ q.1 = b)}
  set B : Finset (V × V) := {q | G.Adj q.1 q.2 ∧ (q.2 = a ∨ q.2 = b)}
  have hP : #({q | G.Adj q.1 q.2} : Finset (V × V)) = 2 * #G.edgeFinset :=
    G.two_mul_card_edgeFinset.symm
  have hA : #A = G.degree a + G.degree b := by
    rw [← card_adj_fst G a, ← card_adj_fst G b, ← card_union_of_disjoint]
    · exact congrArg card (ext fun q ↦ by simp [A, and_or_left])
    · rw [disjoint_filter]; rintro q - ⟨-, rfl⟩ ⟨-, rfl⟩; exact hab rfl
  have hB : #B = G.degree a + G.degree b := by
    rw [← card_adj_snd G a, ← card_adj_snd G b, ← card_union_of_disjoint]
    · exact congrArg card (ext fun q ↦ by simp [B, and_or_left])
    · rw [disjoint_filter]; rintro q - ⟨-, rfl⟩ ⟨-, rfl⟩; exact hab rfl
  have hAB : #(A ∩ B) = 2 := by
    rw [card_eq_two]
    refine ⟨(a, b), (b, a), by simp [hab], ext fun q ↦ ?_⟩
    obtain ⟨x, y⟩ := q
    simp only [A, B, mem_inter, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hxy, hx⟩, -, hy⟩
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [h, h.symm]
  have hU := card_union_add_card_inter A B
  have hD : #({q | G.Adj q.1 q.2 ∧ q.1 ≠ a ∧ q.1 ≠ b ∧ q.2 ≠ a ∧ q.2 ≠ b} : Finset (V × V)) +
      #(A ∪ B) = #({q | G.Adj q.1 q.2} : Finset (V × V)) := by
    rw [← card_union_of_disjoint]
    · refine congrArg card (ext fun q ↦ ?_)
      simp only [A, B, mem_union, mem_filter, mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_left]
      intro q
      simp only [A, B, mem_union, mem_filter, mem_univ, true_and]
      tauto
  omega

private theorem card_disjoint_darts_add :
    #{x : V × V × V × V | G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧ x.1 ≠ x.2.2.1 ∧
        x.1 ≠ x.2.2.2 ∧ x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2} + 4 * ∑ v, G.degree v ^ 2 =
      4 * (#G.edgeFinset * (#G.edgeFinset + 1)) := by
  set P : Finset (V × V) := {p | G.Adj p.1 p.2}
  have hP : #P = 2 * #G.edgeFinset := G.two_mul_card_edgeFinset.symm
  have hfib : #{x : V × V × V × V | G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧ x.1 ≠ x.2.2.1 ∧
        x.1 ≠ x.2.2.2 ∧ x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2} =
      ∑ p ∈ P, #{q : V × V | G.Adj q.1 q.2 ∧ q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2} := by
    rw [card_eq_sum_card_fiberwise (f := fun x ↦ (x.1, x.2.1)) (t := P)
      (fun x hx ↦ by simp only [P, coe_filter, mem_univ, true_and] at hx ⊢; exact hx.1)]
    refine sum_congr rfl fun p hp ↦
      card_nbij' (fun x ↦ x.2.2) (fun q ↦ (p.1, p.2, q)) ?_ ?_ ?_ fun _ _ ↦ rfl
    · rintro ⟨a, b, c, d⟩ h
      simp only [coe_filter, mem_filter, mem_univ, true_and] at h ⊢
      obtain ⟨⟨-, h2, h3, h4, h5, h6⟩, rfl⟩ := h
      exact ⟨h2, Ne.symm h3, Ne.symm h5, Ne.symm h4, Ne.symm h6⟩
    · rintro ⟨c, d⟩ h
      simp only [P, coe_filter, mem_filter, mem_univ, true_and] at h hp ⊢
      obtain ⟨h2, h3, h4, h5, h6⟩ := h
      exact ⟨⟨hp, h2, Ne.symm h3, Ne.symm h5, Ne.symm h4, Ne.symm h6⟩, rfl⟩
    · rintro ⟨a, b, c, d⟩ h
      simp only [coe_filter, mem_filter, mem_univ, true_and] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  have hsum : ∑ p ∈ P, (#{q : V × V | G.Adj q.1 q.2 ∧ q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧
        q.2 ≠ p.2} + 2 * (G.degree p.1 + G.degree p.2)) = ∑ _p ∈ P, (2 * #G.edgeFinset + 2) :=
    sum_congr rfl fun p hp ↦ card_disjoint_darts_add_degree G (by simpa [P] using hp)
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_adj_fst G (fun v ↦ G.degree v),
    sum_adj_snd G (fun v ↦ G.degree v), sum_const, smul_eq_mul, hP, ← hfib] at hsum
  simp only [sq]
  rw [show 4 * (#G.edgeFinset * (#G.edgeFinset + 1)) =
    2 * #G.edgeFinset * (2 * #G.edgeFinset + 2) by ring]
  omega

end Darts

section Order

variable {α : Type*} [Fintype α] [LinearOrder α] {G : SimpleGraph α} [DecidableRel G.Adj]

theorem two_mul_disjointEdgePairs_add_sum_degree_sq :
    2 * G.disjointEdgePairs + ∑ v, G.degree v ^ 2 = #G.edgeFinset * (#G.edgeFinset + 1) := by
  have h := card_disjoint_darts_add G
  have h8 : #{x : α × α × α × α | G.Adj x.1 x.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧ x.1 ≠ x.2.2.1 ∧
      x.1 ≠ x.2.2.2 ∧ x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2} = 8 * G.disjointEdgePairs := by
    rw [← card_adj_distinct]
    refine congrArg card (filter_congr fun x _ ↦ ?_)
    simp only [distinct4]
    exact ⟨fun ⟨h1, h2, h⟩ ↦ ⟨⟨h1, h2⟩, h1.ne, h.1, h.2.1, h.2.2.1, h.2.2.2, h2.ne⟩,
      fun ⟨⟨h1, h2⟩, _, h3, h4, h5, h6, _⟩ ↦ ⟨h1, h2, h3, h4, h5, h6⟩⟩
  omega

/-- The pairs of edges sharing no vertex are all the pairs of edges but those meeting at a
vertex, of which a vertex of degree `k` hosts `k.choose 2`. -/
theorem disjointEdgePairs_add_sum_choose_degree :
    G.disjointEdgePairs + ∑ v, (G.degree v).choose 2 = (#G.edgeFinset).choose 2 := by
  have h := two_mul_disjointEdgePairs_add_sum_degree_sq (G := G)
  have hd := G.sum_degrees_eq_twice_card_edges
  simp only [sq_eq_two_mul_choose_add, sum_add_distrib, ← mul_sum] at h
  rw [mul_add, mul_one, ← sq, sq_eq_two_mul_choose_add] at h
  omega

/-! ### Trees -/

namespace IsTree

variable (hG : G.IsTree)
include hG

/-- In a tree, twice the pairs of edges sharing no vertex and the sum of the squared degrees make
`n (n - 1)` for `n` vertices. -/
theorem two_mul_disjointEdgePairs_add_sum_degree_sq :
    2 * G.disjointEdgePairs + ∑ v, G.degree v ^ 2 =
      Fintype.card α * (Fintype.card α - 1) := by
  have hm := hG.card_edgeFinset
  rw [SimpleGraph.two_mul_disjointEdgePairs_add_sum_degree_sq]
  conv_rhs => rw [← hm]
  rw [Nat.add_sub_cancel, mul_comm]

/-- The sum of the squared degrees of a tree is at most its value `n (n - 1)` on a star. -/
theorem sum_degree_sq_le : ∑ v, G.degree v ^ 2 ≤ Fintype.card α * (Fintype.card α - 1) :=
  (Nat.le_add_left _ _).trans_eq hG.two_mul_disjointEdgePairs_add_sum_degree_sq

omit [LinearOrder α] in
/-- The sum of the squared degrees of a tree is at least its value `4 n - 6` on a path. -/
theorem le_sum_degree_sq : 4 * Fintype.card α - 6 ≤ ∑ v, G.degree v ^ 2 := by
  have h := six_mul_card_edgeFinset_le G
  have hm := hG.card_edgeFinset
  omega

/-- A tree whose degrees are at most two, a path, has squared degrees summing to `4 n - 6`. -/
theorem sum_degree_sq_of_degree_le_two (h2 : ∀ v, G.degree v ≤ 2) :
    ∑ v, G.degree v ^ 2 = 4 * Fintype.card α - 6 := by
  have hm := hG.card_edgeFinset
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hn | hn
  · have h := hG.sum_degree_sq_le
    have h0 : Fintype.card α * (Fintype.card α - 1) = 0 := by
      rw [show Fintype.card α - 1 = 0 by omega, mul_zero]
    omega
  · have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 hn
    have h := six_mul_card_edgeFinset_eq G
      (fun v ↦ hG.1.preconnected.degree_pos_of_nontrivial v) h2
    omega

/-- Summed over all relabellings of a tree on `n` vertices, six times the number of crossings and
`n !` times the sum of the squared degrees make `n ! * (n * (n - 1))`. -/
theorem six_mul_sum_crossings_comap_add :
    6 * ∑ σ : Perm α, (G.comap σ).crossings + (Fintype.card α)! * ∑ v, G.degree v ^ 2 =
      (Fintype.card α)! * (Fintype.card α * (Fintype.card α - 1)) := by
  have h3 := three_mul_sum_crossings_comap (G := G)
  rw [← hG.two_mul_disjointEdgePairs_add_sum_degree_sq, mul_add, mul_left_comm]
  omega

/-- A uniformly random relabelling of a tree on `n` vertices expects at most
`(n - 2) (n - 3) / 6` crossings. -/
theorem six_mul_sum_crossings_comap_le :
    6 * ∑ σ : Perm α, (G.comap σ).crossings ≤
      (Fintype.card α)! * ((Fintype.card α - 2) * (Fintype.card α - 3)) := by
  have h := six_mul_sum_crossings_comap_add hG
  have hk := Nat.mul_le_mul_left (Fintype.card α)! hG.le_sum_degree_sq
  rw [mul_pred_eq, mul_add] at h
  omega

/-- A uniformly random relabelling of a path on `n` vertices expects `(n - 2) (n - 3) / 6`
crossings. -/
theorem six_mul_sum_crossings_comap_of_degree_le_two (h2 : ∀ v, G.degree v ≤ 2) :
    6 * ∑ σ : Perm α, (G.comap σ).crossings =
      (Fintype.card α)! * ((Fintype.card α - 2) * (Fintype.card α - 3)) := by
  have h := six_mul_sum_crossings_comap_add hG
  rw [hG.sum_degree_sq_of_degree_le_two h2, mul_pred_eq, mul_add] at h
  omega

end IsTree

end Order

end SimpleGraph
