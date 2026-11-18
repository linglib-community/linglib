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

variable {E : Type*} {N M : Set E}

/-- A definite with head `N` and the intersective modifier `M`, if any, is referentially supported
when it refers and, if modified, the definite with the bare head does not. -/
def ReferentiallySupported (N : Set E) : Option (Set E) → Prop
  | none => (iota N).Dom
  | some M => (iota (Modifier.intersective M N)).Dom ∧ ¬ (iota N).Dom

@[simp]
theorem referentiallySupported_none : ReferentiallySupported N none ↔ (iota N).Dom :=
  Iff.rfl

/-- A modified definite is referentially supported exactly when some individual is its referent
and not the bare head's. -/
theorem referentiallySupported_some_iff :
    ReferentiallySupported N (some M) ↔
      ∃ e ∈ iota (Modifier.intersective M N), e ∉ iota N := by
  refine ⟨fun ⟨h, hN⟩ ↦ ?_, fun ⟨e, he, hN⟩ ↦ ⟨Part.dom_iff_mem.2 ⟨e, he⟩, fun hd ↦ hN ?_⟩⟩
  · obtain ⟨e, he⟩ := Part.dom_iff_mem.1 h
    exact ⟨e, he, fun h' ↦ hN (Part.dom_iff_mem.2 ⟨e, h'⟩)⟩
  · obtain ⟨e', he'⟩ := Part.dom_iff_mem.1 hd
    obtain rfl := (mem_iota.1 he').2 e (mem_iota.1 he).1.2
    exact he'
