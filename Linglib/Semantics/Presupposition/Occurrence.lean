module

public import Linglib.Semantics.Presupposition.LocalContext
public import Mathlib.Data.ENat.Basic

/-!
# Occurrences of triggers

The theories of presupposition projection read three things off an occurrence of a trigger: its
presupposition and its assertion, as denotations of the gap the trigger fills, and at each parsing
point after it the continuations they consult, the functions from the gap's denotation to the
sentence's truth set (`Presupposition.Occurrence`). The parsing points run from the first, which
consults every good final of the string up to the trigger, to the last, `⊤`, which consults the
sentence itself, and a later parsing point consults fewer continuations.

A theory checks the presupposition at a parsing point: transparency (`Occurrence.Transparent`),
satisfaction in the local context (`Occurrence.Satisfied`), or stable transparency
(`Occurrence.StablyTransparent`). Since the continuations shrink along the parsing points,
transparency at a parsing point holds at every later one (`Occurrence.Transparent.mono`) and
implies stable transparency there (`Occurrence.Transparent.stablyTransparent`), and at the last
parsing point, where only the sentence itself is consulted, stable transparency is transparency
(`Occurrence.stablyTransparent_top_iff`).

Each sentence type lists the occurrences of its triggers: `Formula.occurrences` for the
propositional fragment and `QuantifiedClause.occurrences` for quantified clauses.

## References

* [schlenker-2009]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Presupposition

/-- An occurrence of a trigger: its presupposition and its assertion as denotations of its gap, and
the continuations consulted at each parsing point after it, which shrink from parsing point to
parsing point down to the sentence's own continuation at the last. -/
structure Occurrence (W α : Type*) where
  /-- The presupposition. -/
  presupposition : α
  /-- The assertion. -/
  assertion : α
  /-- The continuations consulted at each parsing point. -/
  continuations : ℕ∞ → Set (α → Set W)
  /-- The sentence's truth set as a function of the gap's denotation. -/
  truth : α → Set W
  antitone_continuations : Antitone continuations
  continuations_top : continuations ⊤ = {truth}

namespace Occurrence

variable {W α : Type*} (o : Occurrence W α)

/-- Every parsing point consults the sentence's own continuation. -/
theorem truth_mem_continuations (n : ℕ∞) : o.truth ∈ o.continuations n :=
  o.antitone_continuations le_top (o.continuations_top ▸ rfl)

section Tests

variable [SemilatticeInf α] (n : ℕ∞) (C : Set W)

/-- The presupposition is a transparent restriction at parsing point `n`. -/
protected def Transparent : Prop :=
  Presupposition.Transparent C (o.continuations n) o.presupposition

/-- The local context at parsing point `n` entails the presupposition. -/
protected def Satisfied : Prop := Presupposition.Satisfied C (o.continuations n) o.presupposition

/-- The presupposition is stably transparent at parsing point `n`. -/
protected def StablyTransparent : Prop :=
  Presupposition.StablyTransparent C (o.continuations n) o.presupposition

variable {o n C}

/-- Transparency at a parsing point holds at every later one. -/
theorem Transparent.mono {m : ℕ∞} (h : o.Transparent n C) (hnm : n ≤ m) : o.Transparent m C :=
  Presupposition.Transparent.anti (o.antitone_continuations hnm) h

theorem Satisfied.transparent (h : o.Satisfied n C) : o.Transparent n C :=
  Presupposition.Satisfied.transparent h

theorem Transparent.stablyTransparent (h : o.Transparent n C) : o.StablyTransparent n C :=
  Presupposition.Transparent.stablyTransparent h

/-- At the last parsing point, where only the sentence itself is consulted, stable transparency is
transparency. -/
theorem stablyTransparent_top_iff : o.StablyTransparent ⊤ C ↔ o.Transparent ⊤ C := by
  rw [Occurrence.StablyTransparent, Occurrence.Transparent, o.continuations_top]
  exact stablyTransparent_singleton_iff

end Tests

end Occurrence

end Presupposition
