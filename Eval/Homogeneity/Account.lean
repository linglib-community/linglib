module

public import Studies.KrizChemla2015

/-!
# Accounts of homogeneity

A sentence with a plural definite is homogeneous: *the triangles are blue* is true when all of
them are, false when none is, and neither true nor false in between. Each account gives the
sentence, under the quantifier that embeds the definite, a value on a display of each individual's
trivalent value (`Account.value`), and predicts a truth-value gap where the value is 0. The four
accounts are those [kriz-chemla-2015] assess, in that paper's statements: Spector's supervaluation
over the existential and the universal resolution of the definite, the same supervaluation over
each individual's resolution, the literal meaning against its global exhaustification after Magri,
and the universal projection of a homogeneity presupposition after Löbner and Gajewski.

## TODO

Bar-Lev's implicature account (`Studies.BarLev2021`) is stated on unembedded displays and under
negation only, so it is not registered: its value inside *all*, *no* and *exactly n* would have to
be stated first.

## References

* [kriz-chemla-2015]
* [spector-2013b]
* [magri-2014]
* [lobner-2000]
* [gajewski-2005]
* [bar-lev-2021]
-/

@[expose] public section

namespace Eval.Homogeneity

open _root_.KrizChemla2015 (Embedding Display)

/-- The accounts of homogeneity. -/
inductive Account where
  /-- [spector-2013b]'s supervaluation over the existential and the universal resolution. -/
  | supervaluation
  /-- The supervaluation over each individual's resolution. -/
  | pointwise
  /-- The literal meaning against its global exhaustification, after [magri-2014]. -/
  | implicature
  /-- The universal projection of a homogeneity presupposition, after [lobner-2000] and
  [gajewski-2005]. -/
  | presupposition
  deriving DecidableEq, Repr

/-- The value an account gives a sentence with a plural definite under an environment, on a
display of each individual's trivalent value, by the account's own definition. -/
def Account.value : Account → Embedding → Display → SignType
  | .supervaluation, e, d => _root_.KrizChemla2015.supervaluation e.tree d
  | .pointwise, e, d => _root_.KrizChemla2015.pointwise e.tree d
  | .implicature, e, d => _root_.KrizChemla2015.globalConstrual e.tree d
  | .presupposition, e, d => _root_.KrizChemla2015.universalPresupposition e.tree d

end Eval.Homogeneity
