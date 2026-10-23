module

public import Mathlib.Data.Set.Defs

/-!
# Degree movement

A degree quantifier, `-er` with its differential, is a quantificational argument of the gradable
predicate and takes scope by Quantifier Raising ([heim-2001]). The Heim–Kennedy constraint filters
the LFs this produces: if the scope of a quantificational DP contains the trace of a DegP, it also
contains that DegP ([heim-2001], [bhatt-pancheva-2004]), so no quantifier intervenes between a
degree abstraction and the variable it binds, the configuration `*λd … QP … d`. Scope is the
c-command domain, so on a scope relation `C` the constraint relates three positions, the quantifier
`q`, the DegP `δ` and its trace `t`: `IsHeimKennedy C q δ t`. [kennedy-1999] reads the absence of
the excluded readings as the absence of degree movement; [heim-2001] keeps the movement and the
filter, [bhatt-pancheva-2004] merges the degree clause at the DegP's scope position so that its
surface site marks the scope the filter constrains, and the than-phrase-internal scope
generalization of [bhatt-takahashi-2011] is the constraint evaluated at the quantifier's base
position.

## References

* [heim-2001]
* [bhatt-pancheva-2004]
* [bhatt-takahashi-2011]
* [kennedy-1999]
-/

@[expose] public section

namespace Degree

variable {Node : Type*} {C : Set (Node × Node)} {q δ t : Node}

/-- The Heim–Kennedy constraint on the scope relation `C`: a quantifier `q` whose scope contains the
trace `t` of the DegP `δ` has `δ` in its scope too. -/
def IsHeimKennedy (C : Set (Node × Node)) (q δ t : Node) : Prop := (q, t) ∈ C → (q, δ) ∈ C

instance [Decidable ((q, t) ∈ C)] [Decidable ((q, δ) ∈ C)] : Decidable (IsHeimKennedy C q δ t) :=
  inferInstanceAs (Decidable (_ → _))

theorem isHeimKennedy_of_not_mem (h : (q, t) ∉ C) : IsHeimKennedy C q δ t := fun h' ↦ absurd h' h

theorem isHeimKennedy_of_mem (h : (q, δ) ∈ C) : IsHeimKennedy C q δ t := fun _ ↦ h

theorem not_isHeimKennedy_iff : ¬ IsHeimKennedy C q δ t ↔ (q, t) ∈ C ∧ (q, δ) ∉ C :=
  Classical.not_imp

end Degree
