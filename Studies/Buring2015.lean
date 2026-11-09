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
calculus on a transitive clause such as *Smith ordered breakfast*, for any meanings of its words
and any alternatives to them. Default stress on the object allows exactly the foci containing the
object (Figure 2); reversal on the verb allows the foci containing the verb but not the object,
and reversal on the subject only narrow subject focus (Figure 4). Reversal inside the demoted VP
of a reversed clause leaves no target (Figure 5), and after Focus Reset at the VP the clause
allows only its literal meaning (Figure 6).

## References

* [buring-2015]
-/

@[expose] public section

namespace Buring2015

open Set WithAlternatives UnalternativeSemantics

variable {E R O : Type*} (s : E) (v : R) (o : O) {s' : E} {v' : R} {o' : O}

/-- The VP of verb `v` and object `o` with restriction `r` on the verb, weak under default stress
on the object and strong under reversal. -/
def vp (r : Restriction) : WithAlternatives (R × O) :=
  .node Prod.mk .left r (.focused v) (.focused o)

/-- The clause of subject `s` and the VP of `v` and `o`, with restriction `r` on the subject and
`r'` on the verb. -/
def clause (r r' : Restriction) : WithAlternatives (E × R × O) :=
  .node Prod.mk .left r (.focused s) (vp v o r')

/-! ### The VP -/

-- (5)
theorem compl_alternatives_vp_weak : (vp v o .weak).alternativesᶜ = {v}ᶜ ×ˢ {o} := by
  rw [vp, alternatives_node_mk, focused_alternatives, focused_alternatives, univ_prod_univ,
    ← compl_eq_univ_sdiff, compl_compl, focused_ordinary, focused_ordinary, excluded_weak,
    narrow_left, image2_mk_eq_prod]

-- (10)
theorem alternatives_vp_strong : (vp v o .strong).alternatives = {v}ᶜ ×ˢ {o} := by
  rw [vp, alternatives_node_mk, focused_alternatives, focused_alternatives, univ_prod_univ,
    ← compl_eq_univ_sdiff, focused_ordinary, focused_ordinary, excluded_strong, compl_compl,
    narrow_left, image2_mk_eq_prod]

theorem isCompl_alternatives_vp :
    IsCompl (vp v o .weak).alternatives (vp v o .strong).alternatives := by
  rw [alternatives_vp_strong, ← compl_alternatives_vp_weak]
  exact isCompl_compl

/-! ### The clause -/

/-- The words of the clause. -/
inductive Word | subj | verb | obj
  deriving DecidableEq, Repr, Fintype

/-- The focal target of a focus on the words `F` of the clause `t` replaces each of them by its
alternative in `t'`. -/
def target (t t' : E × R × O) (F : Finset Word) : E × R × O :=
  (if .subj ∈ F then t'.1 else t.1, if .verb ∈ F then t'.2.1 else t.2.1,
    if .obj ∈ F then t'.2.2 else t.2.2)

private theorem eq_empty_iff {F : Finset Word} :
    F = ∅ ↔ .subj ∉ F ∧ .verb ∉ F ∧ .obj ∉ F := by
  revert F; decide

private theorem eq_singleton_subj_iff {F : Finset Word} :
    F = {.subj} ↔ .subj ∈ F ∧ .verb ∉ F ∧ .obj ∉ F := by
  revert F; decide

theorem wellFormed_clause_weak_weak : (clause s v o .weak .weak).WellFormed :=
  .node_weak (fun _ _ _ _ ↦ Prod.mk.inj) (.focused _)
    (.node_weak (fun _ _ _ _ ↦ Prod.mk.inj) (.focused _) (.focused _))

-- Figure 2
theorem compl_alternatives_clause_weak_weak :
    (clause s v o .weak .weak).alternativesᶜ = {t | t.2.2 = o} \ {(s, v, o)} := by
  ext ⟨x, y, z⟩
  simp only [clause, vp, alternatives_node_mk, focused_alternatives, ordinary_node,
    focused_ordinary, excluded_weak, narrow_left, image2_mk_eq_prod, mem_compl_iff, mem_sdiff,
    mem_prod, mem_univ, mem_singleton_iff, mem_ofPred_eq, Prod.mk.injEq]
  tauto

-- Figure 2
theorem target_mem_clause_weak_weak (hs : s' ≠ s) (hv : v' ≠ v) (ho : o' ≠ o) (F : Finset Word) :
    target (s, v, o) (s', v', o') F ∈ (clause s v o .weak .weak).alternatives ↔
      .obj ∈ F ∨ F = ∅ := by
  rw [← compl_compl (clause s v o .weak .weak).alternatives, compl_alternatives_clause_weak_weak,
    eq_empty_iff]
  by_cases hS : Word.subj ∈ F <;> by_cases hV : Word.verb ∈ F <;> by_cases hO : Word.obj ∈ F <;>
    simp [target, hS, hV, hO, hs, hv, ho]

-- Figure 4
theorem alternatives_clause_weak_strong :
    (clause s v o .weak .strong).alternatives = univ ×ˢ ({v}ᶜ ×ˢ {o}) := by
  rw [clause, alternatives_node_mk, focused_alternatives, alternatives_vp_strong]
  ext ⟨x, y, z⟩
  simp only [vp, ordinary_node, focused_ordinary, excluded_weak, narrow_left, image2_mk_eq_prod,
    mem_sdiff, mem_prod, mem_univ, mem_compl_iff, mem_singleton_iff, Prod.mk.injEq]
  tauto

-- Figure 4
theorem target_mem_clause_weak_strong (hv : v' ≠ v) (ho : o' ≠ o) (F : Finset Word) :
    target (s, v, o) (s', v', o') F ∈ (clause s v o .weak .strong).alternatives ↔
      .verb ∈ F ∧ .obj ∉ F := by
  rw [alternatives_clause_weak_strong]
  by_cases hV : Word.verb ∈ F <;> by_cases hO : Word.obj ∈ F <;> simp [target, hV, hO, hv, ho]

-- Figure 4
theorem alternatives_clause_strong_weak :
    (clause s v o .strong .weak).alternatives = {s}ᶜ ×ˢ {(v, o)} := by
  rw [clause, alternatives_node_mk, focused_alternatives]
  ext ⟨x, y, z⟩
  simp only [vp, alternatives_node_mk, ordinary_node, focused_ordinary, focused_alternatives,
    excluded_weak, excluded_strong, narrow_left, image2_mk_eq_prod, mem_sdiff, mem_prod, mem_univ,
    mem_compl_iff, mem_singleton_iff, Prod.mk.injEq]
  tauto

-- Figure 4
theorem target_mem_clause_strong_weak (hs : s' ≠ s) (hv : v' ≠ v) (ho : o' ≠ o)
    (F : Finset Word) :
    target (s, v, o) (s', v', o') F ∈ (clause s v o .strong .weak).alternatives ↔
      F = {.subj} := by
  rw [alternatives_clause_strong_weak, eq_singleton_subj_iff]
  by_cases hS : Word.subj ∈ F <;> by_cases hV : Word.verb ∈ F <;> by_cases hO : Word.obj ∈ F <;>
    simp [target, hS, hV, hO, hs, hv, ho]

-- Figure 5
theorem alternatives_clause_strong_strong : (clause s v o .strong .strong).alternatives = ∅ :=
  alternatives_node_left_strong_eq_empty (not_wellFormed_node_strong fun _ _ _ _ ↦ Prod.mk.inj)

-- Figure 6
theorem alternatives_reset_vp :
    (node Prod.mk .left .weak (.focused s) (.unfeatured (vp v o .weak).ordinary)).alternatives =
      {(s, v, o)} := by
  rw [alternatives_node_mk, focused_alternatives, unfeatured_alternatives]
  ext ⟨x, y, z⟩
  simp only [vp, ordinary_node, focused_ordinary, unfeatured_ordinary, excluded_weak,
    narrow_left, image2_mk_eq_prod, mem_sdiff, mem_prod, mem_univ, mem_compl_iff,
    mem_singleton_iff, Prod.mk.injEq]
  tauto

end Buring2015
