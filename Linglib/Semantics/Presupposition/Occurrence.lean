module

public import Linglib.Semantics.Presupposition.LocalContext
public import Mathlib.Data.ENat.Basic

/-!
# Occurrences of triggers

The theories of presupposition projection read three things off an occurrence of a trigger: its
presupposition and its assertion, as denotations of the gap the trigger fills, and at each parse
point after it the continuations they consult, the functions from the gap's denotation to the
sentence's truth set (`Presupposition.Occurrence`). The parse points run from the first, which
consults every good final of the string up to the trigger, to the last, `⊤`, which consults the
sentence itself, and a later parse point consults fewer continuations.

A theory checks the presupposition at the gap: transparency at a parse point
(`Occurrence.Transparent`), satisfaction in the local context there (`Occurrence.Satisfied`), or
stable transparency at every parse point (`Occurrence.StablyTransparent`). Since the continuations
shrink along the parse points, transparency at a parse point holds at every later one
(`Occurrence.Transparent.mono`), transparency at the first implies stable transparency
(`Occurrence.Transparent.stablyTransparent`), and stable transparency implies transparency at the
last (`Occurrence.StablyTransparent.transparent_top`).

Each sentence type lists the occurrences of its triggers: `Occurrence.ofFormula` for the
propositional fragment and `Occurrence.ofClause` for quantified clauses.

## References

* [schlenker-2009]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Presupposition

/-- An occurrence of a trigger: its presupposition and its assertion as denotations of its gap, and
the continuations consulted at each parse point after it, which shrink from parse point to parse
point down to the sentence's own continuation at the last. -/
structure Occurrence (W α : Type*) where
  /-- The presupposition. -/
  presupposition : α
  /-- The assertion. -/
  assertion : α
  /-- The continuations consulted at each parse point. -/
  continuations : ℕ∞ → Set (α → Set W)
  /-- The sentence's own continuation. -/
  sentence : α → Set W
  antitone_continuations : Antitone continuations
  continuations_top : continuations ⊤ = {sentence}

namespace Occurrence

variable {W α : Type*} (o : Occurrence W α)

/-- Every parse point consults the sentence's own continuation. -/
theorem sentence_mem_continuations (n : ℕ∞) : o.sentence ∈ o.continuations n :=
  o.antitone_continuations le_top (o.continuations_top ▸ rfl)

section Tests

variable [SemilatticeInf α] (n : ℕ∞) (C : Set W)

/-- The presupposition is a transparent restriction at parse point `n`. -/
def Transparent : Prop := Presupposition.Transparent C (o.continuations n) o.presupposition

/-- The local context at parse point `n` entails the presupposition. -/
def Satisfied : Prop := Presupposition.Satisfied C (o.continuations n) o.presupposition

/-- The presupposition is stably transparent at every parse point. -/
def StablyTransparent : Prop :=
  ∀ n, Presupposition.StablyTransparent C (o.continuations n) o.presupposition

variable {o n C}

/-- Transparency at a parse point holds at every later one. -/
theorem Transparent.mono {m : ℕ∞} (h : o.Transparent n C) (hnm : n ≤ m) : o.Transparent m C :=
  Presupposition.Transparent.anti (o.antitone_continuations hnm) h

theorem Satisfied.transparent (h : o.Satisfied n C) : o.Transparent n C :=
  Presupposition.Satisfied.transparent h

/-- Transparency at the first parse point implies stable transparency at every parse point. -/
theorem Transparent.stablyTransparent (h : o.Transparent 0 C) : o.StablyTransparent C :=
  fun _ ↦ Presupposition.Transparent.stablyTransparent (h.mono bot_le)

/-- Stable transparency at the last parse point, where only the sentence itself is consulted, is
transparency. -/
theorem StablyTransparent.transparent_top (h : o.StablyTransparent C) : o.Transparent ⊤ C := by
  have := h ⊤
  rw [o.continuations_top] at this
  rw [Occurrence.Transparent, o.continuations_top]
  exact stablyTransparent_singleton_iff.1 this

end Tests

end Occurrence

end Presupposition
