/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Semantics.Focus.Unalternatives

/-!
# Büring 2015

Büring derives focal targets from metrical structure, without F-markers. This file runs his
calculus on *Smith ordered breakfast*, with Jones, paid for and lunch the only alternatives to its
words. Default stress on the object allows exactly the foci containing the object (Figure 2);
reversal on the verb allows the foci containing the verb but not the object, and reversal on the
subject only narrow subject focus (Figure 4). Reversal inside the demoted VP of a reversed clause
leaves no target (Figure 5), and after Focus Reset at the VP the clause allows only its literal
meaning (Figure 6).

## References

* [buring-2015]
-/

@[expose] public section

namespace Buring2015

open Set Focus WithAlternatives

/-- Individuals. -/
inductive Ent | smith | jones
  deriving DecidableEq, Repr, Fintype

/-- Transitive-verb meanings. -/
inductive Rel | ordered | paidFor
  deriving DecidableEq, Repr, Fintype

/-- Object meanings. -/
inductive Obj | breakfast | lunch
  deriving DecidableEq, Repr, Fintype

private theorem bijective_uncurry_mk {α β : Type*} :
    Function.Bijective (Function.uncurry (@Prod.mk α β)) :=
  Function.bijective_id

private theorem injective2_mk {α β : Type*} : Function.Injective2 (@Prod.mk α β) :=
  fun _ _ _ _ ↦ Prod.mk.inj

/-- The VP *ordered breakfast* with restriction `r` on the verb, weak under default stress on the
object and strong under reversal. -/
def vp (r : Restriction) : WithAlternatives (Rel × Obj) :=
  .node Prod.mk .left r (.focused .ordered) (.focused .breakfast)

/-- The clause *Smith ordered breakfast* with restriction `r` on the subject and `r'` on the
verb. -/
def clause (r r' : Restriction) : WithAlternatives (Ent × Rel × Obj) :=
  .node Prod.mk .left r (.focused .smith) (vp r')

/-! ### The VP -/

/-- Default *ordered BREAKfast* excludes the VP meanings composed of a relation other than
*ordered* and *breakfast*, Büring's (5). -/
theorem compl_alternatives_vp_weak :
    (vp .weak).alternativesᶜ = {Rel.ordered}ᶜ ×ˢ {Obj.breakfast} := by
  ext ⟨r, o⟩
  simp [vp, compl_alternatives_node, propagated, eq_comm]

/-- Reversed *ORDERED breakfast* allows only the VP meanings composed of a relation other than
*ordered* and *breakfast*, Büring's (10). -/
theorem alternatives_vp_strong : (vp .strong).alternatives = {Rel.ordered}ᶜ ×ˢ {Obj.breakfast} := by
  ext ⟨r, o⟩
  simp [vp, alternatives_node bijective_uncurry_mk, alternatives_map₂, eq_comm]

theorem isCompl_alternatives_vp : IsCompl (vp .weak).alternatives (vp .strong).alternatives :=
  ⟨disjoint_alternatives_node_weak_strong, codisjoint_iff.2 <| by
    change _ ∪ _ = univ
    rw [vp, vp, alternatives_node_weak_union_strong]
    simp [propagated]⟩

/-! ### The clause -/

/-- The words of the clause. -/
inductive Word | subj | verb | obj
  deriving DecidableEq, Repr, Fintype

/-- The focal target of a focus on the words `F` replaces each of them by its alternative. -/
def target (F : Finset Word) : Ent × Rel × Obj :=
  (if .subj ∈ F then .jones else .smith, if .verb ∈ F then .paidFor else .ordered,
    if .obj ∈ F then .lunch else .breakfast)

theorem wellFormed_clause_weak_weak : (clause .weak .weak).WellFormed :=
  .node_weak injective2_mk (.focused _) (.node_weak injective2_mk (.focused _) (.focused _))

/-- Default *Smith ordered BREAKfast* excludes the propositions composed of an individual, a
relation and *breakfast*, other than *Smith ordered breakfast* itself (Figure 2). -/
theorem compl_alternatives_clause_weak_weak :
    (clause .weak .weak).alternativesᶜ =
      {t | t.2.2 = .breakfast} \ {(.smith, .ordered, .breakfast)} := by
  ext ⟨x, r, o⟩
  simp [clause, vp, compl_alternatives_node, propagated]
  revert x r o
  decide

/-- Default stress on the object allows exactly the foci containing the object, and the literal
meaning (Figure 2). -/
theorem target_mem_clause_weak_weak (F : Finset Word) :
    target F ∈ (clause .weak .weak).alternatives ↔ .obj ∈ F ∨ F = ∅ := by
  rw [← compl_compl (clause .weak .weak).alternatives, compl_alternatives_clause_weak_weak]
  simp only [mem_compl_iff, mem_sdiff, mem_ofPred_eq, mem_singleton_iff]
  revert F
  decide

/-- *Smith ORDERED breakfast* allows the propositions in which any individual stands in a relation
other than *ordered* to *breakfast* (Figure 4). -/
theorem alternatives_clause_weak_strong :
    (clause .weak .strong).alternatives = univ ×ˢ ({Rel.ordered}ᶜ ×ˢ {Obj.breakfast}) := by
  rw [clause, alternatives_node bijective_uncurry_mk, alternatives_map₂, focused_alternatives,
    alternatives_vp_strong]
  ext ⟨x, r, o⟩
  simp [vp]
  revert x r o
  decide

/-- Reversal on the verb allows the foci containing the verb but not the object (Figure 4). -/
theorem target_mem_clause_weak_strong (F : Finset Word) :
    target F ∈ (clause .weak .strong).alternatives ↔ .verb ∈ F ∧ .obj ∉ F := by
  rw [alternatives_clause_weak_strong]
  simp only [mem_prod, mem_univ, mem_compl_iff, mem_singleton_iff, true_and]
  revert F
  decide

/-- *SMITH ordered breakfast* allows the propositions in which an individual other than Smith
ordered breakfast (Figure 4). -/
theorem alternatives_clause_strong_weak :
    (clause .strong .weak).alternatives = {Ent.smith}ᶜ ×ˢ {(Rel.ordered, Obj.breakfast)} := by
  rw [clause, alternatives_node bijective_uncurry_mk, alternatives_map₂, focused_alternatives]
  ext ⟨x, r, o⟩
  simp [vp, alternatives_node bijective_uncurry_mk]
  revert x r o
  decide

/-- Reversal on the subject allows only narrow subject focus (Figure 4). -/
theorem target_mem_clause_strong_weak (F : Finset Word) :
    target F ∈ (clause .strong .weak).alternatives ↔ F = {.subj} := by
  rw [alternatives_clause_strong_weak]
  simp only [mem_prod, mem_compl_iff, mem_singleton_iff]
  revert F
  decide

/-- Reversal inside the demoted VP of a reversed clause leaves no focal target (Figure 5). -/
theorem alternatives_clause_strong_strong : (clause .strong .strong).alternatives = ∅ :=
  alternatives_node_left_strong_eq_empty (not_wellFormed_node_strong injective2_mk)

/-- After Focus Reset at the VP, Propagation and the weak restriction on the subject leave the
clause only its literal meaning, as Büring's condition on root nodes demands (Figure 6). -/
theorem alternatives_reset_vp :
    (node Prod.mk .left .weak (.focused Ent.smith) (.unfeatured (vp .weak).ordinary)).alternatives =
      {(.smith, .ordered, .breakfast)} := by
  rw [alternatives_node bijective_uncurry_mk, alternatives_map₂, focused_alternatives,
    unfeatured_alternatives]
  ext ⟨x, r, o⟩
  simp [vp]
  revert x r o
  decide

end Buring2015
