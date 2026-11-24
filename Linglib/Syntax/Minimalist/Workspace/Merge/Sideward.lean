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

Merge is multiplication by the grafted pair after contraction with `{S, S'}`
(`mergeOpOfCuts_eq_mul_contractForest`). On a single tree the contraction sums the trunks of the
cuts with crown `{S, S'}`, since the tree itself is a one-element crown. On two trees the product
rule (`ConnesKreimer.contractForest_mul`) splits `{S, S'}` between them, and the hypotheses leave
only the split taking `S` from the first tree and `S'` from the second, so the contraction is the
product of the two one-tree contractions. A spectator workspace passes through unchanged
(`mergeOpOfCuts_of'_mul`).

## Main results

* `Minimalist.Merge.mergeOpOfCuts_sideward_2b`: a component merged with an accessible term of
  another component, beside the remainder of that component.
* `Minimalist.Merge.mergeOpOfCuts_sideward_3a`: two accessible terms of one component, beside its
  remainder after both are cut.
* `Minimalist.Merge.mergeOpOfCuts_sideward_3b`: accessible terms of two components, beside both
  remainders.

## Implementation notes

The book states each lemma for the term that extracts the matching objects. With several
occurrences Merge sums over them, as (1.3.11) does, so the results are sums over the cuts with
the matching crown, and a workspace without one is sent to `0`.

The lemmas hold over enumerations admitting Merge (`IsMergeCuts`), which the deletion coproduct of
the book's `mergeOp` is not; on objects that are their own remainders
`mergeOp_eq_deletionProj_comp` carries them to `mergeOp`, projecting the trunks.

## References

* [marcolli-chomsky-berwick-2025]
-/

public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq (UnorderedTree α)]
  {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}

/-- Merge on a one-tree workspace is Sideward Merge of type 3(a) ([marcolli-chomsky-berwick-2025]
Lemma 1.4.5). -/
theorem mergeOpOfCuts_sideward_3a (lbl : α) (S S' T : UnorderedTree α) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' {T}) = of' {UnorderedTree.node lbl {S, S'}} *
      (((cuts T).filter (·.1 = {S, S'})).map fun p ↦ ofTree (R := R) p.2).sum := by
  rw [mergeOpOfCuts_eq_mul_contractForest, of'_singleton, of'_singleton,
    contractForest_ofTree_of_ne fun h ↦ by simpa using congrArg Multiset.card h]

/-- Merging a component `T` with a term `S'` of another component is Sideward Merge of type 2(b)
([marcolli-chomsky-berwick-2025] Lemma 1.4.4). -/
theorem mergeOpOfCuts_sideward_2b [IsMergeCuts cuts] (lbl : α) {T T' S' : UnorderedTree α}
    (hT : T ∉ T'.subtrees) (hS' : S' ≠ T') :
    mergeOpOfCuts (R := R) cuts lbl T S' (of' {T, T'}) = of' {UnorderedTree.node lbl {T, S'}} *
      (((cuts T').filter (·.1 = {S'})).map fun p ↦ ofTree (R := R) p.2).sum := by
  rw [mergeOpOfCuts_eq_mul_contractForest, show ({T, T'} : Forest (UnorderedTree α)) = {T} + {T'}
    from rfl, of'_add, of'_singleton, of'_singleton, of'_singleton, contractForest_mul,
    Finset.sum_eq_single (({T} : Forest (UnorderedTree α)), {S'})]
  · rw [contractForest_ofTree_self, one_mul,
      contractForest_ofTree_of_ne (Multiset.singleton_inj.not.mpr hS')]
  · rintro ⟨A, B⟩ hp hne
    have hAB : A + B = {T} + {S'} := Multiset.mem_antidiagonal.1 (Multiset.mem_toFinset.1 hp)
    rcases Multiset.mem_add.mp (hAB ▸ Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self T)))
      with h | h
    · rw [contractForest_ofTree_of_mem h (by
        rintro rfl; exact hne (Prod.ext rfl (Multiset.add_right_inj.mp hAB))), zero_mul]
    · rw [contractForest_ofTree_of_notMem h hT, mul_zero]
  · exact fun h ↦ absurd (by simp) h

/-- Merging terms `S` of `T` and `S'` of `T'` is Sideward Merge of type 3(b)
([marcolli-chomsky-berwick-2025] Lemma 1.4.4). -/
theorem mergeOpOfCuts_sideward_3b [IsMergeCuts cuts] (lbl : α) {T T' S S' : UnorderedTree α}
    (hST : S ≠ T) (hS'T' : S' ≠ T') (hST' : S ∉ T'.subtrees) (hS'T : S' ∉ T.subtrees) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' {T, T'}) = of' {UnorderedTree.node lbl {S, S'}} *
      (((cuts T).filter (·.1 = {S})).map fun p ↦ ofTree (R := R) p.2).sum *
      (((cuts T').filter (·.1 = {S'})).map fun p ↦ ofTree (R := R) p.2).sum := by
  rw [mergeOpOfCuts_eq_mul_contractForest, show ({T, T'} : Forest (UnorderedTree α)) = {T} + {T'}
    from rfl, of'_add, of'_singleton, of'_singleton, of'_singleton, contractForest_mul,
    Finset.sum_eq_single (({S} : Forest (UnorderedTree α)), {S'})]
  · rw [contractForest_ofTree_of_ne (Multiset.singleton_inj.not.mpr hST),
      contractForest_ofTree_of_ne (Multiset.singleton_inj.not.mpr hS'T'), mul_assoc]
  · rintro ⟨A, B⟩ hp hne
    have hAB : A + B = {S, S'} := Multiset.mem_antidiagonal.1 (Multiset.mem_toFinset.1 hp)
    by_cases hA : S' ∈ A
    · rw [contractForest_ofTree_of_notMem hA hS'T, zero_mul]
    by_cases hB : S ∈ B
    · rw [contractForest_ofTree_of_notMem hB hST', mul_zero]
    have ha' : A ≤ {S} := (Multiset.le_cons_of_notMem hA).mp <| by
      rw [← Multiset.insert_eq_cons, ← Multiset.pair_comm, ← hAB]; exact Multiset.le_add_right _ _
    have hb' : B ≤ {S'} := (Multiset.le_cons_of_notMem hB).mp <| by
      rw [← Multiset.insert_eq_cons, ← hAB]; exact Multiset.le_add_left _ _
    have hcard := congrArg Multiset.card hAB
    rcases Multiset.le_singleton.mp ha' with rfl | rfl <;>
      rcases Multiset.le_singleton.mp hb' with rfl | rfl
    · simp at hcard
    · simp at hcard
    · simp at hcard
    · exact absurd rfl hne
  · exact fun h ↦ absurd (by simp) h

end Minimalist.Merge
