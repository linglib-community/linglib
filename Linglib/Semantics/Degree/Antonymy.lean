module

public import Mathlib.Algebra.Group.Action.Defs
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Degree.Comparison

/-!
# Antonymy on scales

The members of an antonym pair, *tall* and *short* or *happy* and *unhappy*, measure the same
degrees under inverse orderings, so an adjective's `Polarity` says which member it is, and
`negative * p` is the polarity of the antonym of a `p` adjective. Polarity acts on
[boundedness](##Boundedness.negative_smul) and on [comparisons](##Comparison.negative_smul) through
the order dual.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [cruse-1986]
-/

@[expose] public section

/-! ### Polarity -/

/-- The negative member of an antonym pair measures on the dual scale; two inversions restore the
ordering, so the antonym of *short* is *tall*. Markedness is a separate matter, since equipollent
pairs like *hot* and *cold* have no unmarked member. Sentential negation acts on the adjective's
denotation by complement instead, so *not short* is the contradictory of *short* and does not
entail *tall* (`AntonymForm.denotation`). -/
instance : MulAction Polarity Boundedness :=
  .ofEndHom (Polarity.lift ⟨Boundedness.dual, Boundedness.dual_involutive.comp_self⟩)

@[simp] theorem Boundedness.negative_smul (b : Boundedness) : Polarity.negative • b = b.dual :=
  rfl

/-- The negative member of an antonym pair compares on the reversed scale, so its comparison is
the dual one, so that *shorter* is `Polarity.negative • Comparison.gt`. -/
instance : MulAction Polarity Comparison :=
  .ofEndHom (Polarity.lift ⟨Comparison.dual, Comparison.dual_involutive.comp_self⟩)

@[simp] theorem Comparison.negative_smul (c : Comparison) : Polarity.negative • c = c.dual :=
  rfl
