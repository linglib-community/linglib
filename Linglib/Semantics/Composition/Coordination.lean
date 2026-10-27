module

public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Semantics.Composition.Tree

/-!
# Coordination in the composition engine

Two sisters of the same conjoinable type, a type that ends in $t$, can combine by coordination:
their coordinator's denotation applies to the pair in the pointwise Boolean algebra of the type,
so that *and* conjoins truth values, predicates and quantifiers alike. Coordination is a mode
beside functional application, intensional application and predicate modification, and
predicate modification is
[the conjunctive case at the type of predicates](##combine?_eq_coordinate?_of_conjunctive), so
the engine's modification mode agrees with what *and* denotes.

## Main definitions

* `Coordinator.coordinate?`: the coordination mode.

## Implementation notes

The mode finds the Boolean algebra of its daughters' type at run time, through
`Ty.Domain.completeBooleanAlgebra?`; `Coordinator.denote` is the coordinator's denotation.

## References

* [heim-kratzer-1998]
* [partee-rooth-1983]
-/

@[expose] public section

namespace Coordinator

open Montague

/-- The coordination of two sisters of the same conjoinable type by what the coordinator `c`
denotes on the pair, in the complete Boolean algebra of their type and through the effect `M`;
`none` on sisters of different or non-conjoinable types. -/
def coordinate? {E W : Type} {M : Type → Type} [Applicative M] (c : Coordinator)
    (d1 d2 : Denotation E W M) : Option (Denotation E W M) :=
  if h : d1.1 = d2.1 then
    (Ty.Domain.completeBooleanAlgebra? E W d1.1).map
      fun (i : CompleteBooleanAlgebra (Ty.Domain E W d1.1)) =>
        ⟨d1.1, (fun p q ↦ letI := i; c.denote {p, q}) <$> d1.2 <*> (h ▸ d2.2)⟩
  else none

/-- Predicate modification is generalized conjunction at `⟨e,t⟩`. -/
theorem combine?_eq_coordinate?_of_conjunctive {E W : Type} {M : Type → Type}
    [Applicative M] {c : Coordinator} (hc : c.role = .conjunctive) (d1 d2 : Denotation E W M)
    (h1 : d1.1 = (.e ⇒ .t)) (h2 : d2.1 = (.e ⇒ .t)) :
    Mode.combine? Mode.evalM d1 d2 = coordinate? c d1 d2 := by
  obtain ⟨t1, v1⟩ := d1
  obtain ⟨t2, v2⟩ := d2
  subst h1; subst h2
  have h : (Modifier.intersective : Ty.Domain E W (.e ⇒ .t) → _) =
      fun p q ↦ c.denote {p, q} := by
    funext p q; simp [Modifier.intersective, Coordinator.denote_of_conjunctive hc]
  rw [Mode.combine?_predicateModification]
  exact congrArg (fun F ↦ some (⟨.e ⇒ .t, F <$> v1 <*> v2⟩ : Denotation E W M)) h

end Coordinator
