module

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
share no endpoint and in none otherwise, so the expected number of crossings is a third of the
number of pairs of links that can cross (eq. 13, `three_mul_sum_crossings_map`), whatever the link
structure. In a tree that number is fixed by the sentence length and the second moment of the
degrees (eq. 3, `two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree`), so a random
linearization expects `n (n - 1 - ⟨k²⟩) / 6` crossings (eq. 14,
`six_mul_sum_crossings_map_add_of_isTree`): six for the sentence of Fig. 1
(`fig1_sum_crossings_map`), none in any order for a star tree (`star_crossings_map`).

## Implementation notes

* Expectations are stated as counts over all `n !` linearizations, with the divisions cleared.
* Crossings are counted as ordered quadruples. Four distinct linked positions alternate in one of
  their `4 !` equally likely relative orders (`Equiv.Perm.factorial_mul_card_monotone_comp`), and
  each unordered pair of disjoint links has eight ordered witnesses.
* Potential crossings are counted for any link structure, `2 · C_pairs + ∑ k² = m (m + 1)` for
  `m` links, through ordered pairs of darts; a tree has `n - 1` links because its undirected view
  is a tree (`DependencyGrammar.Graph.IsTree.isTree_toSimpleGraph`).

## References

* [ferrer-i-cancho-2017]
* [ferrer-i-cancho-2013]
* [melcuk-1988]
-/

@[expose] public section

namespace FerrerICancho2017

open DependencyGrammar Morphology Finset Equiv Nat

variable {n : ℕ} (g : Graph n)

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

/-- **Expected crossings under random linearization** ([ferrer-i-cancho-2017],
eq. 13): summed over all `n !` linearizations, three times the crossing
count is `n !` times the number of disjoint link pairs. So a uniformly
random ordering expects a third of a crossing per pair of links sharing no
endpoint, whatever the sentence's own order was. -/
theorem three_mul_sum_crossings_map :
    3 * ∑ σ : Perm (Fin n), (g.map σ).crossings = n ! * disjointLinkPairs g := by
  have key := mul_sum_crossings_map (g := g)
  rw [card_linked_distinct, Nat.mul_left_comm] at key
  omega

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

/-- **Potential crossings of a tree** ([ferrer-i-cancho-2017], eq. 3, from
[ferrer-i-cancho-2013]): `C_pairs = n (n - 1 - ⟨k²⟩) / 2`, where `⟨k²⟩ = ∑ k² / n`. -/
theorem two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree (hT : g.IsTree) :
    2 * disjointLinkPairs g + ∑ v, g.toSimpleGraph.degree v ^ 2 = n * (n - 1) := by
  have hm := hT.isTree_toSimpleGraph.card_edgeFinset
  rw [Fintype.card_fin] at hm
  rw [two_mul_disjointLinkPairs_add_sum_degree_sq]
  conv_rhs => rw [← hm]
  rw [Nat.add_sub_cancel, mul_comm]

/-- **Expected crossings of a tree** ([ferrer-i-cancho-2017], eq. 14): a uniformly random
linearization expects `n (n - 1 - ⟨k²⟩) / 6` crossings, a function of the sentence length and
the degree second moment alone. -/
theorem six_mul_sum_crossings_map_add_of_isTree (hT : g.IsTree) :
    6 * ∑ σ : Perm (Fin n), (g.map σ).crossings + n ! * ∑ v, g.toSimpleGraph.degree v ^ 2 =
      n ! * (n * (n - 1)) := by
  have h3 := three_mul_sum_crossings_map (g := g)
  rw [← two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree hT, mul_add, mul_left_comm]
  omega

/-! ### The paper's examples -/

/-- Fig. 1: *She loved me for the dangers I had passed* in [melcuk-1988]'s analysis, where the
preposition heads its object and the auxiliary heads the relative clause. Relations other than
the subject and object of *loved*, which the caption names, are `dep`. -/
def fig1 : Tree 9 :=
  .mk' (.ofArcs [Word.mk' "She" .PRON, Word.mk' "loved" .VERB, Word.mk' "me" .PRON,
      Word.mk' "for" .ADP, Word.mk' "the" .DET, Word.mk' "dangers" .NOUN, Word.mk' "I" .PRON,
      Word.mk' "had" .AUX, Word.mk' "passed" .VERB]
    1 [(1, 0, .nsubj), (1, 2, .obj), (1, 3, .dep), (3, 5, .dep), (5, 4, .dep), (5, 7, .dep),
      (7, 6, .dep), (7, 8, .dep)])

/-- Fig. 1 has `⟨k²⟩ = 4`. -/
theorem fig1_sum_degree_sq : ∑ v, fig1.toGraph.toSimpleGraph.degree v ^ 2 = 36 := by decide

/-- Eq. 3 gives Fig. 1 `C_pairs = 18`. -/
theorem fig1_disjointLinkPairs : disjointLinkPairs fig1.toGraph = 18 := by
  have h := two_mul_disjointLinkPairs_add_sum_degree_sq_of_isTree fig1.isTree
  rw [fig1_sum_degree_sq] at h
  omega

/-- Fig. 1 expects six crossings under a random linearization, the paper's value after eq. 14. -/
theorem fig1_sum_crossings_map :
    ∑ σ : Perm (Fin 9), (fig1.toGraph.map σ).crossings = 6 * 9 ! := by
  have h := six_mul_sum_crossings_map_add_of_isTree fig1.isTree
  rw [fig1_sum_degree_sq] at h
  omega

/-- A star tree, *John gave Mary books*: every link meets the head, so no pair of links can
cross. -/
def star : Tree 4 :=
  .mk' (.ofArcs [Word.mk' "John" .PROPN, Word.mk' "gave" .VERB, Word.mk' "Mary" .PROPN,
      Word.mk' "books" .NOUN]
    1 [(1, 0, .nsubj), (1, 2, .iobj), (1, 3, .obj)])

/-- No linearization of a star tree has a crossing ([ferrer-i-cancho-2017], after eq. 14). -/
theorem star_crossings_map (σ : Perm (Fin 4)) : (star.toGraph.map σ).crossings = 0 := by
  have h := three_mul_sum_crossings_map (g := star.toGraph)
  rw [show disjointLinkPairs star.toGraph = 0 by decide, mul_zero] at h
  have h0 : ∑ σ : Perm (Fin 4), (star.toGraph.map σ).crossings = 0 := by omega
  exact sum_eq_zero_iff.1 h0 σ (mem_univ σ)

end FerrerICancho2017
