module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Length
public import Linglib.Syntax.DependencyGrammar.Catena
public import Linglib.Core.Combinatorics.Enumerative.PermutationPattern
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring

/-!
# Ferrer-i-Cancho (2017): Random crossings in dependency trees

Ferrer-i-Cancho asks how many crossings a sentence would show if its word order were lost and
replaced by a uniformly random one. Two links cross in a third of the linearizations when they
share no word and in none otherwise, so a random linearization
[expects a third](##FerrerICancho2017.three_mul_sum_crossings_map) of the potential crossings
$C_{pairs}$, the number of pairs of links sharing no word, which
[bounds the crossings](##FerrerICancho2017.crossings_map_le_disjointLinkPairs) of every
linearization. Potential crossings are all pairs of links
[but those meeting at a word](##FerrerICancho2017.disjointLinkPairs_add_sum_choose_degree), so in
a tree the sentence length $n$ and the second moment $⟨k^2⟩$ of the degrees
[fix them](##FerrerICancho2017.two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree), and the
[expected number of crossings](##FerrerICancho2017.six_mul_sum_crossings_map_add_of_isTree)
is $n (n - 1 - ⟨k^2⟩) / 6$. It vanishes for a star tree, where
[no linearization has a crossing](##FerrerICancho2017.crossings_map_eq_zero_of_forall_linked), and
is [greatest](##FerrerICancho2017.six_mul_sum_crossings_map_le_of_isTree) for a
[linear tree](##FerrerICancho2017.six_mul_sum_crossings_map_of_degree_le_two), at
$(n - 2) (n - 3) / 6$.

## Implementation notes

* Expectations are stated as counts over all $n!$ linearizations, with the divisions cleared, and
  the second moment as the sum $∑ k^2 = n ⟨k^2⟩$.
* Crossings are counted as ordered quadruples. Four distinct linked positions alternate in one of
  their $4!$ equally likely relative orders (`Equiv.Perm.factorial_mul_card_monotone_comp`), and
  each unordered pair of disjoint links has eight ordered witnesses.
* Potential crossings are counted for any link structure through ordered pairs of darts; a tree
  has $n - 1$ links because its undirected view is a tree
  (`DependencyGrammar.Graph.IsTree.isTree_toSimpleGraph`).
* The greatest expected number of crossings is stated as $(n - 2) (n - 3) / 6$, which equals the
  paper's $n (n - 5) / 6 + 1$.

## TODO

* The uniqueness of the star and the linear tree as the extremes of $⟨k^2⟩$.
* The expected dependency length $(n + 1) / 3$ of a random linearization.
* Potential crossings are the edges of the complement of `SimpleGraph.lineGraph`; the count is
  stated here on quadruples of positions instead.

## References

* [ferrer-i-cancho-2017]
* [ferrer-i-cancho-2013]
* [melcuk-1988]
-/

@[expose] public section

namespace FerrerICancho2017

open DependencyGrammar Morphology Finset Equiv Nat

variable {L : Type*} {n : ℕ} (g : Graph L n)

/-- The unordered pairs of links sharing no endpoint — the pairs that can
cross at all, [ferrer-i-cancho-2017]'s potential crossings. Each pair is
counted once, by the representative with both links least-endpoint-first
and the earlier-starting link first. -/
def disjointLinkPairs : ℕ :=
  #{x : Fin n × Fin n × Fin n × Fin n | g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
    x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2 ∧ x.1 < x.2.2.1 ∧ x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2}

variable {g}

/-! ### Crossings under a relabelling -/

theorem crossings_map (σ : Perm (Fin n)) :
    (g.map σ).crossings = #{x : Fin n × Fin n × Fin n × Fin n |
      g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
        Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} := by
  refine Finset.card_equiv
    (σ.symm.prodCongr (σ.symm.prodCongr (σ.symm.prodCongr σ.symm))) ?_
  rintro ⟨a, b, c, d⟩
  simp [Graph.Linked, Alternate]

/-! ### One linearization in twenty-four alternates a distinct quadruple -/

private theorem alternate_comp_iff {a b c d : Fin n} (σ : Perm (Fin n))
    (hq : Function.Injective ![a, c, b, d]) :
    Alternate (σ a) (σ b) (σ c) (σ d) ↔ Monotone (σ ∘ ![a, c, b, d]) :=
  .trans (by simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_succ])
    ⟨StrictMono.monotone, (·.strictMono_of_injective (σ.injective.comp hq))⟩

private theorem card_alternate {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    24 * #{σ : Perm (Fin n) | Alternate (σ a) (σ b) (σ c) (σ d)} = n ! := by
  have hq : Function.Injective ![a, c, b, d] := List.nodup_ofFn.mp (by simp [*, hbc.symm])
  simpa only [Fintype.card_fin, Function.Embedding.coeFn_mk, ← alternate_comp_iff _ hq,
    show (4 : ℕ)! = 24 from rfl] using
    Perm.factorial_mul_card_monotone_comp (⟨_, hq⟩ : Fin 4 ↪ Fin n)

private theorem card_alternate_eq_zero {a b c d : Fin n}
    (h : ¬(a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)) :
    #{σ : Perm (Fin n) | Alternate (σ a) (σ b) (σ c) (σ d)} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro σ - ⟨h1, h2, h3⟩
  refine h ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> omega

/-! ### Summing over linearizations, grouped by quadruple -/

private def distinct4 (x : Fin n × Fin n × Fin n × Fin n) : Prop :=
  x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2.1 ∧ x.1 ≠ x.2.2.2 ∧
    x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2 ∧ x.2.2.1 ≠ x.2.2.2

private instance : DecidablePred (distinct4 (n := n)) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

private theorem sum_crossings_map :
    ∑ σ : Perm (Fin n), (g.map σ).crossings =
      ∑ x ∈ univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
          g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2),
        #{σ : Perm (Fin n) | Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} := by
  simp only [crossings_map, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  by_cases h1 : g.Linked x.1 x.2.1 <;> by_cases h2 : g.Linked x.2.2.1 x.2.2.2 <;>
    simp [h1, h2]

private theorem mul_sum_crossings_map :
    24 * ∑ σ : Perm (Fin n), (g.map σ).crossings =
      n ! * #(univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
        (g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x)) := by
  rw [sum_crossings_map, Finset.mul_sum]
  have hcongr : ∀ x ∈ univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
      g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2),
      24 * #{σ : Perm (Fin n) |
        Alternate (σ x.1) (σ x.2.1) (σ x.2.2.1) (σ x.2.2.2)} =
        if distinct4 x then n ! else 0 := by
    intro x _
    by_cases hd : distinct4 x
    · rw [ite_eq_left hd]
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
      exact card_alternate d1 d2 d3 d4 d5 d6
    · rw [ite_eq_right hd, card_alternate_eq_zero hd, Nat.mul_zero]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter, Finset.filter_filter,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Eight ordered witnesses per unordered disjoint pair -/

private theorem card_filter_eq_two_mul {α : Type*} [Fintype α] [DecidableEq α]
    {P C : α → Prop} [DecidablePred P] [DecidablePred C] (e : α → α)
    (he : Function.Involutive e) (hP : ∀ x, P x → P (e x))
    (hC : ∀ x, P x → (C (e x) ↔ ¬ C x)) :
    #(univ.filter P) = 2 * #(univ.filter (fun x ↦ P x ∧ C x)) := by
  rw [← Finset.filter_filter,
    ← Finset.card_filter_add_card_filter_not (s := univ.filter P) C, two_mul]
  congr 1
  refine Finset.card_equiv (he.toPerm e) (fun x ↦ ?_)
  simp only [mem_filter, mem_univ, true_and, Function.Involutive.coe_toPerm]
  grind [Function.Involutive]

private theorem card_linked_distinct :
    #(univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
        (g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2) ∧ distinct4 x)) =
      8 * disjointLinkPairs g := by
  rw [card_filter_eq_two_mul (C := fun x ↦ x.1 < x.2.1) (fun x ↦ (x.2.1, x.1, x.2.2))
      (fun _ ↦ rfl) ?_ ?_,
    card_filter_eq_two_mul (C := fun x ↦ x.2.2.1 < x.2.2.2)
      (fun x ↦ (x.1, x.2.1, x.2.2.2, x.2.2.1)) (fun _ ↦ rfl) ?_ ?_,
    card_filter_eq_two_mul (C := fun x ↦ x.1 < x.2.2.1)
      (fun x ↦ (x.2.2.1, x.2.2.2, x.1, x.2.1)) (fun _ ↦ rfl) ?_ ?_,
    ← Nat.mul_assoc, ← Nat.mul_assoc, disjointLinkPairs]
  · congr 2
    refine filter_congr fun x _ ↦ ?_
    simp only [distinct4]
    grind
  all_goals rintro ⟨a, b, c, d⟩; simp only [distinct4, Graph.Linked]; grind

/-! ### The expected-crossings identity -/

/-- Summed over all `n !` linearizations, three times the crossing count is `n !` times the number
of disjoint link pairs ([ferrer-i-cancho-2017], eq. 13). -/
theorem three_mul_sum_crossings_map :
    3 * ∑ σ : Perm (Fin n), (g.map σ).crossings = n ! * disjointLinkPairs g := by
  have key := mul_sum_crossings_map (g := g)
  rw [card_linked_distinct, Nat.mul_left_comm] at key
  omega

/-! ### Potential crossings bound the crossings of every linearization -/

-- "C cannot exceed C_pairs"
theorem crossings_le_disjointLinkPairs : g.crossings ≤ disjointLinkPairs g := by
  refine card_le_card fun x hx ↦ ?_
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨h1, h2, hac, hcb, hbd⟩ := hx
  exact ⟨h1, h2, hac.trans hcb, hcb.trans hbd, hac, hcb.ne', hbd.ne⟩

theorem disjointLinkPairs_map (σ : Perm (Fin n)) :
    disjointLinkPairs (g.map σ) = disjointLinkPairs g := by
  refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) ?_
  rw [← card_linked_distinct, ← card_linked_distinct]
  refine card_equiv (σ.symm.prodCongr (σ.symm.prodCongr (σ.symm.prodCongr σ.symm))) ?_
  rintro ⟨a, b, c, d⟩
  simp [Graph.Linked, distinct4]

-- no linearization has more crossings than there are pairs of links sharing no word
theorem crossings_map_le_disjointLinkPairs (σ : Perm (Fin n)) :
    (g.map σ).crossings ≤ disjointLinkPairs g :=
  crossings_le_disjointLinkPairs.trans_eq (disjointLinkPairs_map σ)

theorem disjointLinkPairs_eq_zero_of_forall_linked {h : Fin n}
    (hh : ∀ ⦃a b⦄, g.Linked a b → a = h ∨ b = h) : disjointLinkPairs g = 0 := by
  rw [disjointLinkPairs, Finset.card_eq_zero, filter_eq_empty_iff]
  rintro ⟨a, b, c, d⟩ - ⟨h1, h2, hab, hcd, hac, hbc, hbd⟩
  rcases hh h1 with e1 | e1 <;> rcases hh h2 with e2 | e2 <;> dsimp only at * <;> omega

/-- When every link meets one word, as in a star tree, no linearization has a crossing
([ferrer-i-cancho-2017], after eq. 14). -/
theorem crossings_map_eq_zero_of_forall_linked {h : Fin n}
    (hh : ∀ ⦃a b⦄, g.Linked a b → a = h ∨ b = h) (σ : Perm (Fin n)) :
    (g.map σ).crossings = 0 :=
  Nat.eq_zero_of_le_zero <|
    (crossings_map_le_disjointLinkPairs σ).trans_eq (disjointLinkPairs_eq_zero_of_forall_linked hh)

/-! ### Potential crossings from the degree sequence

Ordered pairs of darts number `(2m)²` for `m` links. Those sharing a position are counted from
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

private theorem six_mul_card_edgeFinset_le :
    6 * #G.edgeFinset ≤ ∑ v, G.degree v ^ 2 + 2 * Fintype.card V := by
  have h : ∑ v, 3 * G.degree v ≤ ∑ v, (G.degree v ^ 2 + 2) :=
    sum_le_sum fun v _ ↦ three_mul_le_sq_add_two _
  rw [← mul_sum, G.sum_degrees_eq_twice_card_edges, sum_add_distrib, sum_const, Finset.card_univ,
    smul_eq_mul] at h
  omega

private theorem six_mul_card_edgeFinset_eq (h1 : ∀ v, 1 ≤ G.degree v)
    (h2 : ∀ v, G.degree v ≤ 2) :
    6 * #G.edgeFinset = ∑ v, G.degree v ^ 2 + 2 * Fintype.card V := by
  have h : ∑ v, 3 * G.degree v = ∑ v, (G.degree v ^ 2 + 2) := sum_congr rfl fun v _ ↦ by
    obtain h | h : G.degree v = 1 ∨ G.degree v = 2 := by have := h1 v; have := h2 v; omega
    all_goals rw [h]; norm_num
  rw [← mul_sum, G.sum_degrees_eq_twice_card_edges, sum_add_distrib, sum_const, Finset.card_univ,
    smul_eq_mul] at h
  omega

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

private theorem card_disjoint_add {a b : V} (h : G.Adj a b) :
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
    · rw [disjoint_left]
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
    sum_congr rfl fun p hp ↦ card_disjoint_add G (by simpa [P] using hp)
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_adj_fst G (fun v ↦ G.degree v),
    sum_adj_snd G (fun v ↦ G.degree v), sum_const, smul_eq_mul, hP, ← hfib] at hsum
  simp only [sq]
  rw [show 4 * (#G.edgeFinset * (#G.edgeFinset + 1)) =
    2 * #G.edgeFinset * (2 * #G.edgeFinset + 2) by ring]
  omega

end Darts

theorem two_mul_disjointLinkPairs_add_sum_degree_sq :
    2 * disjointLinkPairs g + ∑ v, g.toSimpleGraph.degree v ^ 2 =
      #g.toSimpleGraph.edgeFinset * (#g.toSimpleGraph.edgeFinset + 1) := by
  have h := card_disjoint_darts_add g.toSimpleGraph
  have h8 : #{x : Fin n × Fin n × Fin n × Fin n | g.toSimpleGraph.Adj x.1 x.2.1 ∧
      g.toSimpleGraph.Adj x.2.2.1 x.2.2.2 ∧ x.1 ≠ x.2.2.1 ∧ x.1 ≠ x.2.2.2 ∧
        x.2.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2} = 8 * disjointLinkPairs g := by
    rw [← card_linked_distinct]
    refine congrArg card (filter_congr fun x _ ↦ ?_)
    simp only [distinct4, Graph.toSimpleGraph_adj]
    tauto
  omega

-- all the pairs of links but those meeting at a word, `k.choose 2` at a word of degree `k`
theorem disjointLinkPairs_add_sum_choose_degree :
    disjointLinkPairs g + ∑ v, (g.toSimpleGraph.degree v).choose 2 =
      (#g.toSimpleGraph.edgeFinset).choose 2 := by
  have h := two_mul_disjointLinkPairs_add_sum_degree_sq (g := g)
  have hd := g.toSimpleGraph.sum_degrees_eq_twice_card_edges
  simp only [sq_eq_two_mul_choose_add, sum_add_distrib, ← mul_sum] at h
  rw [mul_add, mul_one, ← sq, sq_eq_two_mul_choose_add] at h
  omega

/-- A tree has `n (n - 1 - ⟨k²⟩) / 2` pairs of disjoint links ([ferrer-i-cancho-2017], eq. 3, from
[ferrer-i-cancho-2013]). -/
theorem two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree (hT : g.IsTree) :
    2 * disjointLinkPairs g + ∑ v, g.toSimpleGraph.degree v ^ 2 = n * (n - 1) := by
  have hm := hT.isTree_toSimpleGraph.card_edgeFinset
  rw [Fintype.card_fin] at hm
  rw [two_mul_disjointLinkPairs_add_sum_degree_sq]
  conv_rhs => rw [← hm]
  rw [Nat.add_sub_cancel, mul_comm]

/-- A uniformly random linearization of a tree expects `n (n - 1 - ⟨k²⟩) / 6` crossings
([ferrer-i-cancho-2017], eq. 14). -/
theorem six_mul_sum_crossings_map_add_of_isTree (hT : g.IsTree) :
    6 * ∑ σ : Perm (Fin n), (g.map σ).crossings + n ! * ∑ v, g.toSimpleGraph.degree v ^ 2 =
      n ! * (n * (n - 1)) := by
  have h3 := three_mul_sum_crossings_map (g := g)
  rw [← two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree hT, mul_add, mul_left_comm]
  omega

variable (g) in
/-- Relinearizing along `σ` is an isomorphism of the undirected views. -/
def mapIso (σ : Perm (Fin n)) : g.toSimpleGraph ≃g (g.map σ).toSimpleGraph where
  toEquiv := σ
  map_rel_iff' := by simp

@[simp] theorem mapIso_apply (σ : Perm (Fin n)) (v : Fin n) : mapIso g σ v = σ v := rfl

-- relinearizing preserves the tree, and so the second moment of the degrees
theorem sum_degree_sq_map (σ : Perm (Fin n)) :
    ∑ v, (g.map σ).toSimpleGraph.degree v ^ 2 = ∑ v, g.toSimpleGraph.degree v ^ 2 :=
  (Fintype.sum_equiv σ _ _ fun v ↦ by rw [← mapIso_apply, (mapIso g σ).degree_eq]).symm

/-! ### The range of the second moment and of the expected crossings -/

-- eq. 16, upper bound
theorem sum_degree_sq_le_of_isTree (hT : g.IsTree) :
    ∑ v, g.toSimpleGraph.degree v ^ 2 ≤ n * (n - 1) :=
  (Nat.le_add_left _ _).trans_eq (two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree hT)

-- eq. 16, lower bound
theorem le_sum_degree_sq_of_isTree (hT : g.IsTree) :
    4 * n - 6 ≤ ∑ v, g.toSimpleGraph.degree v ^ 2 := by
  have h := six_mul_card_edgeFinset_le g.toSimpleGraph
  have hm := hT.isTree_toSimpleGraph.card_edgeFinset
  rw [Fintype.card_fin] at h hm
  omega

-- a linear tree attains the lower bound of eq. 16
theorem sum_degree_sq_of_degree_le_two (hT : g.IsTree)
    (h2 : ∀ v, g.toSimpleGraph.degree v ≤ 2) :
    ∑ v, g.toSimpleGraph.degree v ^ 2 = 4 * n - 6 := by
  have hm := hT.isTree_toSimpleGraph.card_edgeFinset
  rw [Fintype.card_fin] at hm
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h := sum_degree_sq_le_of_isTree hT
    have h0 : n * (n - 1) = 0 := by rw [show n - 1 = 0 by omega, mul_zero]
    omega
  · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
    have h := six_mul_card_edgeFinset_eq g.toSimpleGraph
      (fun v ↦ hT.isTree_toSimpleGraph.1.preconnected.degree_pos_of_nontrivial v) h2
    rw [Fintype.card_fin] at h
    omega

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

/-- A uniformly random linearization of a tree expects at most `(n - 2) (n - 3) / 6` crossings
([ferrer-i-cancho-2017], eq. 17). -/
theorem six_mul_sum_crossings_map_le_of_isTree (hT : g.IsTree) :
    6 * ∑ σ : Perm (Fin n), (g.map σ).crossings ≤ n ! * ((n - 2) * (n - 3)) := by
  have h := six_mul_sum_crossings_map_add_of_isTree hT
  have hk := Nat.mul_le_mul_left (n !) (le_sum_degree_sq_of_isTree hT)
  rw [mul_pred_eq, mul_add] at h
  omega

-- eq. 15
theorem six_mul_sum_crossings_map_of_degree_le_two (hT : g.IsTree)
    (h2 : ∀ v, g.toSimpleGraph.degree v ≤ 2) :
    6 * ∑ σ : Perm (Fin n), (g.map σ).crossings = n ! * ((n - 2) * (n - 3)) := by
  have h := six_mul_sum_crossings_map_add_of_isTree hT
  rw [sum_degree_sq_of_degree_le_two hT h2, mul_pred_eq, mul_add] at h
  omega

-- the linear tree on four words: one potential crossing, a third of a crossing expected
example {g : Graph L 4} (hT : g.IsTree) (h2 : ∀ v, g.toSimpleGraph.degree v ≤ 2) :
    3 * ∑ σ : Perm (Fin 4), (g.map σ).crossings = 4 ! := by
  have h := six_mul_sum_crossings_map_of_degree_le_two hT h2
  have h4 : (4 : ℕ)! = 24 := rfl
  omega

/-! ### The paper's examples -/

/-- Fig. 1: *She loved me for the dangers I had passed* in [melcuk-1988]'s analysis, where the
preposition heads its object and the auxiliary heads the relative clause. Relations other than
the subject and object of *loved*, which the caption names, are `dep`. -/
def fig1 : Tree UD.DepRel 9 :=
  .mk' (.ofArcs [Word.mk' "She" .PRON, Word.mk' "loved" .VERB, Word.mk' "me" .PRON,
      Word.mk' "for" .ADP, Word.mk' "the" .DET, Word.mk' "dangers" .NOUN, Word.mk' "I" .PRON,
      Word.mk' "had" .AUX, Word.mk' "passed" .VERB]
    1 [(1, 0, .nsubj), (1, 2, .obj), (1, 3, .dep), (3, 5, .dep), (5, 4, .dep), (5, 7, .dep),
      (7, 6, .dep), (7, 8, .dep)])

-- Fig. 1: the sentence in its own order has no crossing
theorem fig1_crossings : fig1.toGraph.crossings = 0 := by decide +kernel

-- Fig. 1: mean dependency length 11 / 8
theorem fig1_totalLength : fig1.toGraph.totalLength = 11 := by decide +kernel

/-- Fig. 2: the order *loved had me for dangers I she the passed*, as the position each word of
Fig. 1 moves to. -/
def fig2 : Perm (Fin 9) :=
  ⟨![6, 0, 2, 3, 7, 4, 5, 1, 8], ![1, 7, 2, 3, 5, 6, 0, 4, 8], by decide, by decide⟩

-- Fig. 2
theorem fig2_crossings : (fig1.toGraph.map fig2).crossings = 9 := by decide +kernel

-- Fig. 1
theorem fig1_sum_degree_sq : ∑ v, fig1.toGraph.toSimpleGraph.degree v ^ 2 = 36 := by decide

-- Fig. 1
theorem fig1_disjointLinkPairs : disjointLinkPairs fig1.toGraph = 18 := by
  have h := two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree fig1.isTree
  rw [fig1_sum_degree_sq] at h
  omega

-- Fig. 1 expects six crossings under a random linearization, the value after eq. 14
theorem fig1_sum_crossings_map :
    ∑ σ : Perm (Fin 9), (fig1.toGraph.map σ).crossings = 6 * 9 ! := by
  have h := six_mul_sum_crossings_map_add_of_isTree fig1.isTree
  rw [fig1_sum_degree_sq] at h
  omega

end FerrerICancho2017
