module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Kinds of lexical entailment

The root typology of Beavers and Koontz-Garboden (§5.4.1) records which of four kinds of lexical
entailment a root carries, state, manner, result and cause, under two collocational restrictions:
a change entails a state, and a cause entails a change. The restrictions are the partial order
`state ≤ result ≤ cause` on `Root.Kind`, with `manner` isolated.

## References

* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure

/-- The kinds of lexical entailment in the root typology of
[beavers-koontz-garboden-2020]. -/
inductive Root.Kind where
  | state
  | manner
  | result
  | cause
  deriving DecidableEq, Fintype, Repr

namespace Root.Kind

/-- The collocational order, `state ≤ result ≤ cause` with `manner` isolated, since a
change entails a state and a cause entails a change. -/
protected inductive LE : Kind → Kind → Prop
  | refl (a) : Kind.LE a a
  | state_result : Kind.LE state result
  | state_cause : Kind.LE state cause
  | result_cause : Kind.LE result cause

instance : LE Kind := ⟨Kind.LE⟩

instance : DecidableLE Kind := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

instance : PartialOrder Kind where
  le_refl := .refl
  le_trans := by decide
  le_antisymm := by decide

theorem isMax_manner : IsMax manner := by unfold IsMax; decide

theorem isMax_cause : IsMax cause := by unfold IsMax; decide

end Root.Kind

end ArgumentStructure
