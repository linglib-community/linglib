module

public import Linglib.Semantics.Modification.Basic
public import Linglib.Semantics.Reference.Iota

/-!
# Referential support

In the Referential Theory of sentence processing, a context supports an analysis of a definite
noun phrase when the definite refers, and an analysis that adds a restrictive modifier to the head
noun only when the definite with the bare head does not refer. A definite with head `N` and an
intersective modifier `M`, if any, is [referentially supported](##ReferentiallySupported) under
this principle, and [with a modifier it is supported](##referentiallySupported_some_iff) exactly
when some individual is the modified definite's referent and not the bare one's.

## References

* [altmann-steedman-1988]
-/

@[expose] public section

variable {E : Type*} {N M : E → Prop}

/-- A definite with head `N` and the intersective modifier `M`, if any, is referentially supported
when it refers and, if modified, the definite with the bare head does not. -/
def ReferentiallySupported (N : E → Prop) : Option (E → Prop) → Prop
  | none => (iota N).isSome
  | some M => (iota (Modifier.intersective M N)).isSome ∧ iota N = none

@[simp]
theorem referentiallySupported_none : ReferentiallySupported N none ↔ (iota N).isSome :=
  Iff.rfl

/-- A modified definite is referentially supported exactly when some individual is its referent
and not the bare head's. -/
theorem referentiallySupported_some_iff :
    ReferentiallySupported N (some M) ↔
      ∃ e, iota (Modifier.intersective M N) = some e ∧ iota N ≠ some e := by
  refine ⟨fun ⟨h, hN⟩ ↦ ?_, fun ⟨e, he, hN⟩ ↦ ⟨by simp [he], ?_⟩⟩
  · obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h
    exact ⟨e, he, by simp [hN]⟩
  · refine Option.eq_none_iff_forall_ne_some.2 fun e' he' ↦ hN ?_
    obtain rfl := ((iota_eq_some_iff N).1 he').2 e ((iota_eq_some_iff _).1 he).1.2
    exact he'
