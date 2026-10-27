/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Clause.Spine

/-!
# Complement sizes

A clausal complement is measured by its highest projected head. Wurmbrand classifies infinitival
complements by the structure they project, a bare vP for restructuring, a TP for propositional
attitudes and a modal projection for future infinitives, beside the full CP of a finite clause,
and a complement is at most as large as another when its highest head is extended by the other's.
Two sizes with distinct heads at one level, tense and negation for instance, are then equivalent
but not equal, so the order is a preorder, and two sizes no source relates, a nominalized clause
and a CP, are incomparable. The size of a clause spine is its highest head. On extended
projections the extension order of spines, inclusion of labels, refines the size order, and the
standard sizes are those of the standard spines.

## Main definitions

* `Minimalist.ComplementSize`: a clausal complement measured by its highest head.
* `Minimalist.ClauseSpine.size`: the size of a spine, its highest head.
* `Minimalist.ComplementSize.vP`, `Minimalist.ComplementSize.tP`,
  `Minimalist.ComplementSize.modP`, `Minimalist.ComplementSize.finP`,
  `Minimalist.ComplementSize.cP`: the standard sizes.

## Main results

* `Minimalist.ComplementSize.le_def`: the order is the extension order of the highest heads.
* `Minimalist.ClauseSpine.size_le_size`: on extended projections, the extension order refines the
  size order, so that the standard sizes ascend as their spines do
  (`Minimalist.ComplementSize.vP_le_tP`, `Minimalist.ComplementSize.tP_le_cP`).

## References

* [wurmbrand-2014]
* [grimshaw-2005]
-/

@[expose] public section

namespace Minimalist

/-- A clausal complement measured by the highest head it projects. -/
structure ComplementSize where
  /-- The highest functional head in the complement. -/
  highestHead : Cat
  deriving DecidableEq, Repr

namespace ComplementSize

variable {a b : ComplementSize}

/-- Complement sizes are ordered by the extension order of their highest heads, so that a
complement is at most another when the other's highest head extends its own. -/
instance : Preorder ComplementSize where
  le a b := a.highestHead.ExtendsTo b.highestHead
  le_refl _ := refl_of Cat.ExtendsTo _
  le_trans _ _ _ := trans_of Cat.ExtendsTo

instance : DecidableLE ComplementSize := fun a b ↦
  inferInstanceAs (Decidable (a.highestHead.ExtendsTo b.highestHead))

instance : DecidableLT ComplementSize := fun a b ↦
  inferInstanceAs (Decidable (a.highestHead.ExtendsTo b.highestHead ∧
    ¬ b.highestHead.ExtendsTo a.highestHead))

theorem le_def : a ≤ b ↔ a.highestHead.ExtendsTo b.highestHead := Iff.rfl

end ComplementSize

/-! ### The size of a spine -/

namespace ClauseSpine

variable {s t : ClauseSpine} {c : Cat}

/-- The size of a spine is its highest head; the empty spine has the size of a bare lexical head,
the least size. -/
def size (s : ClauseSpine) : ComplementSize := ⟨s.heads.getLastD .V⟩

private theorem extendsTo_getLastD {l : List Cat} (hp : l.Pairwise Cat.ExtendsTo) (hc : c ∈ l) :
    c.ExtendsTo (l.getLastD .V) := by
  have hne : l ≠ [] := List.ne_nil_of_mem hc
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
  rw [← List.dropLast_append_getLast hne, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · rw [← List.dropLast_append_getLast hne, List.pairwise_append] at hp
    exact hp.2.2 c hc _ (List.mem_singleton_self _)
  · exact refl_of Cat.ExtendsTo _

/-- In an extended projection every head is extended by the highest one. -/
theorem IsExtendedProjection.extendsTo_size (hs : s.IsExtendedProjection) (hc : c ∈ s) :
    c.ExtendsTo s.size.highestHead :=
  extendsTo_getLastD hs.pairwise hc

/-- On extended projections, the extension order refines the size order: a nonempty spine whose
heads another projects is no larger. -/
theorem size_le_size (h : s ≤ t) (ht : t.IsExtendedProjection) (hs : s.heads ≠ []) :
    s.size ≤ t.size := by
  obtain ⟨l, c, hlc⟩ := (List.eq_nil_or_concat s.heads).resolve_left hs
  show (s.heads.getLastD .V).ExtendsTo t.size.highestHead
  rw [hlc, List.concat_eq_append, List.getLastD_concat]
  exact ht.extendsTo_size (le_iff_forall_mem.1 h c (by simp [hlc]))

end ClauseSpine

/-! ### The standard sizes -/

namespace ComplementSize

/-- The vP-sized complement of a restructuring infinitive, the size of the vP spine. -/
def vP : ComplementSize := ClauseSpine.vP.size

/-- The TP-sized complement of a propositional infinitive, the size of the TP spine. -/
def tP : ComplementSize := ClauseSpine.tP.size

/-- The modal complement of a future infinitive. -/
def modP : ComplementSize := ⟨.Mod⟩

/-- The FinP-sized complement, the lowest layer of the left periphery. -/
def finP : ComplementSize := ⟨.Fin⟩

/-- The CP-sized complement of a finite clause, the size of the CP spine. -/
def cP : ComplementSize := ClauseSpine.cP.size

/-- The standard sizes ascend as their spines do. -/
theorem vP_le_tP : vP ≤ tP :=
  ClauseSpine.size_le_size ClauseSpine.vP_le_tP (by decide +kernel) (List.cons_ne_nil _ _)

theorem tP_le_cP : tP ≤ cP :=
  ClauseSpine.size_le_size ClauseSpine.tP_le_cP ClauseSpine.cP_isExtendedProjection
    (List.cons_ne_nil _ _)

end ComplementSize

end Minimalist
