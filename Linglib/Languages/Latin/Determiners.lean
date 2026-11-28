module

public import Linglib.Languages.Latin.Morphs
public import Linglib.Languages.Latin.Pronouns
public import Linglib.Syntax.Category.Determiner.IndeterminateQuantifier
public import Linglib.Semantics.Quantifier.Determiner
public import Linglib.Semantics.Quantifier.Global

/-!
# Latin quantifiers

Latin builds the distributive universal *quisque* 'each' on the interrogative *quis* 'who' with
the enclitic *-que*, which has the form of the coordinator 'and', as in Cicero's *quid quis-que senserit* 'what each
man's opinion was', which Mitrović and Sauerland cite for the quantificational use of the
enclitic coordinators of the old Indo-European languages.

## References

* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Latin.Determiners

open Quantifier
open scoped Denotes

universe u

/-- *Quisque* is 'each'. -/
def quisque : IndeterminateQuantifier :=
  { indeterminate := Pronouns.quis.toProForm, particle := Morphs.que, readings := {.every} }

theorem denote_quisque :
    (⟦quisque.toQuantifier⟧ : Set Det.Family.{u}) = {Det.Family.every} :=
  QuantificationalDeterminer.denote_eq_singleton (s := .every) rfl

end Latin.Determiners
