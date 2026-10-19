module

public import Studies.AugurzkyEtAl2023

/-!
# Accounts of homogeneity

A sentence with a plural definite is homogeneous: *the triangles are blue* is true when all of
them are, false when none is, and neither true nor false in between. Each account gives a
sentence, under the quantifier that embeds the definite, a verdict on a display of each
individual's trivalent value. Four accounts are context-free, in the statements of
[kriz-chemla-2015], who assess them: Spector's supervaluation over the existential and the
universal resolution of the definite, the same supervaluation over each individual's resolution,
the literal meaning against its global exhaustification after Magri, and the universal
projection of a homogeneity presupposition after Löbner and Gajewski (`Account.value`). Three
depend on the question a context raises, in the statements of [augurzky-etal-2023]: Križ's
non-implicature approach, on which the context resolves the gap, Bar-Lev's implicature approach,
on which pruning the alternatives yields non-maximality outside downward-entailing scopes, and
that approach with the scalar implicature of *not every*, as Augurzky et al. amend it
(`Account.accepts`).

## TODO

Bar-Lev's own statement of his account (`Studies.BarLev2021`) reaches Križ and Chemla's displays
unembedded and under negation only, so his account is scored here as Augurzky et al. state it.

## References

* [kriz-chemla-2015]
* [augurzky-etal-2023]
* [spector-2013b]
* [magri-2014]
* [lobner-2000]
* [gajewski-2005]
* [kriz-2016]
* [bar-lev-2021]
-/

@[expose] public section

namespace Eval.Homogeneity

open _root_.KrizChemla2015 (Display)
open _root_.AugurzkyEtAl2023 (Quantifier Context)
open Quantifier (NumberTree)

/-- The accounts of homogeneity. -/
inductive Account where
  /-- [spector-2013b]'s supervaluation over the existential and the universal resolution. -/
  | supervaluation
  /-- The supervaluation over each individual's resolution. -/
  | pointwise
  /-- The literal meaning against its global exhaustification, after [magri-2014]. -/
  | exhaustification
  /-- The universal projection of a homogeneity presupposition, after [lobner-2000] and
  [gajewski-2005]. -/
  | presupposition
  /-- [kriz-2016]'s non-implicature approach, on which the question a context raises resolves
  the gap. -/
  | nonImplicature
  /-- [bar-lev-2021]'s implicature approach, on which pruning yields non-maximality outside
  downward-entailing scopes. -/
  | implicature
  /-- The implicature approach with the scalar implicature of *not every*, as
  [augurzky-etal-2023] amend it. -/
  | implicatureEnriched
  deriving DecidableEq, Repr

/-- The value a context-free account gives a sentence under a quantifier, on a display of each
individual's trivalent value, by the account's own definition; none for an account that needs a
context. -/
def Account.value (a : Account) (q : NumberTree) [DecidableRel q] (d : Display) :
    Option SignType :=
  match a with
  | .supervaluation => some (_root_.KrizChemla2015.supervaluation q d)
  | .pointwise => some (_root_.KrizChemla2015.pointwise q d)
  | .exhaustification => some (_root_.KrizChemla2015.globalConstrual q d)
  | .presupposition => some (_root_.KrizChemla2015.universalPresupposition q d)
  | _ => none

/-- Whether an account accepts a sentence under one of [augurzky-etal-2023]'s quantifiers, on a
display, in a context: a context-free account when it makes the sentence true, the others by their
own definitions. -/
def Account.accepts (a : Account) (q : Quantifier) (ctx : Context) (d : Display) : Prop :=
  match a with
  | .nonImplicature => _root_.AugurzkyEtAl2023.nonImplicature q.tree ctx d
  | .implicature => _root_.AugurzkyEtAl2023.implicature q.tree ctx d
  | .implicatureEnriched => _root_.AugurzkyEtAl2023.implicature q.enriched ctx d
  | a => a.value q.tree d = some 1

instance (a : Account) (q : Quantifier) (ctx : Context) (d : Display) :
    Decidable (a.accepts q ctx d) := by
  cases a <;> unfold Account.accepts <;> infer_instance

end Eval.Homogeneity
