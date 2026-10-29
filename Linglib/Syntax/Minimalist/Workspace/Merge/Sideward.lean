module

public import Linglib.Syntax.Minimalist.Workspace.Merge.External

/-!
# Sideward Merge

Sideward Merge is Merge `M_{S,S'}` where at least one of `S, S'` is an accessible term of a
component of the workspace, other than in Internal Merge. Marcolli, Chomsky and Berwick
distinguish three cases (their §1.4.1): in 2(b) `S` is a component and `S'` an accessible term
of another component; in 3(a) both are accessible terms of one component; in 3(b) they are
accessible terms of two different components. Lemmas 1.4.4 and 1.4.5 show that the Merge
operator of Definition 1.3.4 realizes all three, so Merge alone does not rule them out.

Each case evaluates the Merge formula `mergeOpG_apply_of'` on the workspace. On a single tree the
matching cuts are the cuts with crown `{S, S'}`, since the tree itself is a one-element crown. On
two trees the hypotheses force each matching forest cut to take `S` from the first tree and `S'`
from the second, so the sum factors through the two one-tree sums. A spectator workspace passes
through unchanged (`mergeOpG_of'_mul`).

## Main results

* `Minimalist.Merge.mergeOpG_sideward_2b`: a component merged with an accessible term of another
  component, beside the remainder of that component.
* `Minimalist.Merge.mergeOpG_sideward_3a`: two accessible terms of one component, beside its
  remainder after both are cut.
* `Minimalist.Merge.mergeOpG_sideward_3b`: accessible terms of two components, beside both
  remainders.

## Implementation notes

The book states each lemma for the term that extracts the matching objects. With several
occurrences Merge sums over them, as (1.3.11) does, so the results are sums over the cuts with
the matching crown, and a workspace without one is sent to `0`.

The lemmas hold over enumerations admitting Merge (`IsMergeCuts`), which the deletion cuts of the
book's `mergeOp` are not; on objects without unary vertices
`mergeOp_eq_rename_contractUnary_comp` carries them to `mergeOp`, contracting the trunks.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq (UnorderedTree α)]
  {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}

private theorem sum_filter_treeCutsG_of_ne {T : UnorderedTree α} {K : Forest (UnorderedTree α)}
    (h : {T} ≠ K) :
    (((treeCutsG cuts T).filter (·.1 = K)).map fun p ↦ of' (R := R) p.2).sum =
      (((cuts T).filter (·.1 = K)).map fun p ↦ ofTree (R := R) p.2).sum := by
  rw [treeCutsG, Multiset.filter_cons_of_neg (p := fun x : Forest _ × Forest _ ↦ x.1 = K) _ h,
    Multiset.filter_map, Multiset.map_map]
  rfl

/-- On a two-tree workspace whose matching cuts take the crown `A` from `T` and `B` from `T'`,
    Merge is the product of the two one-tree sums. -/
private theorem mergeOpG_pair_eq_mul (lbl : α) {S S' T T' : UnorderedTree α}
    {A B : Forest (UnorderedTree α)}
    (h : ∀ a ∈ treeCutsG cuts T, ∀ b ∈ treeCutsG cuts T',
      a.1 + b.1 = {S, S'} ↔ a.1 = A ∧ b.1 = B) :
    mergeOpG (R := R) cuts lbl S S' (of' {T, T'}) = of' {UnorderedTree.node lbl {S, S'}} *
      (((treeCutsG cuts T).filter (·.1 = A)).map fun p ↦ of' (R := R) p.2).sum *
      (((treeCutsG cuts T').filter (·.1 = B)).map fun p ↦ of' (R := R) p.2).sum := by
  rw [mergeOpG_apply_of', forestCutsG_pair, Multiset.conv, Multiset.filter_map,
    Multiset.filter_congr (q := fun x : (Forest _ × Forest _) × (Forest _ × Forest _) ↦
      x.1.1 = A ∧ x.2.1 = B) fun ⟨a, b⟩ hx ↦ h a (Multiset.mem_product.mp hx).1 b
        (Multiset.mem_product.mp hx).2,
    Multiset.filter_product (fun a : Forest (UnorderedTree α) × Forest (UnorderedTree α) ↦ a.1 = A)
      (fun b : Forest (UnorderedTree α) × Forest (UnorderedTree α) ↦ b.1 = B),
    Multiset.map_map, mul_assoc, ← Multiset.sum_map_product_mul]
  simp only [Function.comp_def, Prod.snd_add, of'_add]

/-- Merge on a one-tree workspace is Sideward Merge of type 3(a) ([marcolli-chomsky-berwick-2025]
Lemma 1.4.5). -/
theorem mergeOpG_sideward_3a (lbl : α) (S S' T : UnorderedTree α) :
    mergeOpG (R := R) cuts lbl S S' (of' {T}) = of' {UnorderedTree.node lbl {S, S'}} *
      (((cuts T).filter (·.1 = {S, S'})).map fun p ↦ ofTree (R := R) p.2).sum := by
  rw [mergeOpG_apply_of', forestCutsG_singleton,
    sum_filter_treeCutsG_of_ne fun h ↦ by simpa using congrArg Multiset.card h]

/-- Merging a component `T` with a term `S'` of another component is Sideward Merge of type 2(b)
([marcolli-chomsky-berwick-2025] Lemma 1.4.4). -/
theorem mergeOpG_sideward_2b [IsMergeCuts cuts] (lbl : α) {T T' S' : UnorderedTree α}
    (hT : T ∉ T'.subtrees) (hS' : S' ≠ T') :
    mergeOpG (R := R) cuts lbl T S' (of' {T, T'}) = of' {UnorderedTree.node lbl {T, S'}} *
      (((cuts T').filter (·.1 = {S'})).map fun p ↦ ofTree (R := R) p.2).sum := by
  rw [mergeOpG_pair_eq_mul lbl (A := {T}) (B := {S'}) fun a ha b hb ↦ ?_,
    sum_filter_treeCutsG_of_ne (Multiset.singleton_inj.not.mpr hS'.symm), treeCutsG,
    Multiset.filter_cons_of_pos (p := fun x : Forest _ × Forest _ ↦ x.1 = {T}) _ rfl,
    Multiset.filter_eq_nil.mpr fun p hp ↦ ?_]
  · simp
  · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact IsMergeCuts.crown_ne_singleton hq
  refine ⟨fun hab ↦ ?_, fun ⟨h1, h2⟩ ↦ by rw [h1, h2]; rfl⟩
  have hTa : T ∈ a.1 := (Multiset.mem_add.mp (hab ▸ Multiset.mem_cons_self _ _)).resolve_right
    fun h ↦ hT (IsMergeCuts.mem_subtrees_of_mem_treeCutsG hb h)
  have ha1 : a.1 = {T} := by
    rcases Multiset.mem_cons.mp ha with rfl | ha
    · rfl
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ha
      exact absurd hTa (IsMergeCuts.notMem_crown hp)
  exact ⟨ha1, Multiset.add_right_inj.mp (ha1 ▸ hab)⟩

/-- Merging terms `S` of `T` and `S'` of `T'` is Sideward Merge of type 3(b)
([marcolli-chomsky-berwick-2025] Lemma 1.4.4). -/
theorem mergeOpG_sideward_3b [IsMergeCuts cuts] (lbl : α) {T T' S S' : UnorderedTree α}
    (hST : S ≠ T) (hS'T' : S' ≠ T') (hST' : S ∉ T'.subtrees) (hS'T : S' ∉ T.subtrees) :
    mergeOpG (R := R) cuts lbl S S' (of' {T, T'}) = of' {UnorderedTree.node lbl {S, S'}} *
      (((cuts T).filter (·.1 = {S})).map fun p ↦ ofTree (R := R) p.2).sum *
      (((cuts T').filter (·.1 = {S'})).map fun p ↦ ofTree (R := R) p.2).sum := by
  rw [mergeOpG_pair_eq_mul lbl (A := {S}) (B := {S'}) fun a ha b hb ↦ ?_,
    sum_filter_treeCutsG_of_ne (Multiset.singleton_inj.not.mpr hST.symm),
    sum_filter_treeCutsG_of_ne (Multiset.singleton_inj.not.mpr hS'T'.symm)]
  refine ⟨fun hab ↦ ?_, fun ⟨h1, h2⟩ ↦ by rw [h1, h2]; rfl⟩
  have ha' : a.1 ≤ {S} := (Multiset.le_cons_of_notMem fun h ↦
    hS'T (IsMergeCuts.mem_subtrees_of_mem_treeCutsG ha h)).mp <| by
      rw [← Multiset.insert_eq_cons, ← Multiset.pair_comm, ← hab]; exact Multiset.le_add_right _ _
  have hb' : b.1 ≤ {S'} := (Multiset.le_cons_of_notMem fun h ↦
    hST' (IsMergeCuts.mem_subtrees_of_mem_treeCutsG hb h)).mp <| by
      rw [← Multiset.insert_eq_cons, ← hab]; exact Multiset.le_add_left _ _
  have hcard := congrArg Multiset.card hab
  rcases Multiset.le_singleton.mp ha' with h1 | h1 <;>
    rcases Multiset.le_singleton.mp hb' with h2 | h2 <;> simp_all

end Minimalist.Merge
