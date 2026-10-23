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
and a complement is at most as large as another when its highest head is no higher in the
functional sequence. Two sizes with distinct heads at one level, tense and negation for instance,
are then equivalent but not equal, so the order is a preorder. The size of a clause spine is its
highest head. On extended projections the extension order of spines, inclusion of labels, refines
the size order, and the standard sizes are those of the standard spines.

## Main definitions

* `Minimalist.ComplementSize`: a clausal complement measured by its highest head.
* `Minimalist.ComplementSize.fLevel`: the functional level of the highest head.
* `Minimalist.ClauseSpine.size`: the size of a spine, its highest head.
* `Minimalist.ComplementSize.vP`, `Minimalist.ComplementSize.tP`,
  `Minimalist.ComplementSize.modP`, `Minimalist.ComplementSize.finP`,
  `Minimalist.ComplementSize.cP`: the standard sizes.

## Main results

* `Minimalist.ComplementSize.le_def`, `Minimalist.ComplementSize.lt_def`: the order is that of
  functional levels.
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

/-- The functional level of a complement is that of its highest head. -/
def fLevel (cs : ComplementSize) : ℕ := cs.highestHead.fValue

/-- Complement sizes are ordered by functional level, so that a complement is at most another when
it projects no higher in the functional sequence. -/
instance : Preorder ComplementSize := Preorder.lift fLevel

instance : DecidableLE ComplementSize := fun a b ↦ inferInstanceAs (Decidable (a.fLevel ≤ b.fLevel))

instance : DecidableLT ComplementSize := fun a b ↦ inferInstanceAs (Decidable (a.fLevel < b.fLevel))

theorem le_def : a ≤ b ↔ a.fLevel ≤ b.fLevel := Iff.rfl

theorem lt_def : a < b ↔ a.fLevel < b.fLevel := Iff.rfl

end ComplementSize

/-! ### The size of a spine -/

namespace ClauseSpine

variable {s t : ClauseSpine} {c : Cat}

/-- The size of a spine is its highest head; the empty spine has the size of a bare lexical head,
the least size. -/
def size (s : ClauseSpine) : ComplementSize := ⟨s.heads.getLastD .V⟩

private theorem fValue_le_getLastD {l : List Cat} (hp : l.Pairwise Cat.ExtendsTo) (hc : c ∈ l) :
    c.fValue ≤ (l.getLastD .V).fValue := by
  have hne : l ≠ [] := List.ne_nil_of_mem hc
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
  rw [← List.dropLast_append_getLast hne, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · rw [← List.dropLast_append_getLast hne, List.pairwise_append] at hp
    exact (hp.2.2 c hc _ (List.mem_singleton_self _)).2
  · exact le_rfl

theorem IsExtendedProjection.fValue_le_fLevel (hs : s.IsExtendedProjection) (hc : c ∈ s) :
    c.fValue ≤ s.size.fLevel :=
  fValue_le_getLastD hs.pairwise hc

/-- On extended projections, the extension order refines the size order: a spine whose heads
another projects is no larger. -/
theorem size_le_size (h : s ≤ t) (ht : t.IsExtendedProjection) : s.size ≤ t.size := by
  rcases List.eq_nil_or_concat s.heads with hs | ⟨l, c, hs⟩
  · show (s.heads.getLastD .V).fValue ≤ t.size.fLevel
    simp [hs, Cat.fValue]
  · show (s.heads.getLastD .V).fValue ≤ t.size.fLevel
    rw [hs, List.concat_eq_append, List.getLastD_concat]
    exact ht.fValue_le_fLevel (le_iff_forall_mem.1 h c (by simp [hs]))

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
theorem vP_le_tP : vP ≤ tP := ClauseSpine.size_le_size ClauseSpine.vP_le_tP (by decide)

theorem tP_le_cP : tP ≤ cP := ClauseSpine.size_le_size ClauseSpine.tP_le_cP (by decide)

end ComplementSize

end Minimalist
