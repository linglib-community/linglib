module

public import Linglib.Languages.Latin.Coordination
public import Linglib.Languages.Latin.Pronouns
public import Linglib.Semantics.Quantifier.IndeterminateQuantifier

/-!
# Latin quantifiers

Latin builds the distributive universal *quisque* 'each' on the interrogative *quis* 'who' with
the enclitic *-que*, the coordinator 'and', as in Cicero's *quid quis-que senserit* 'what each
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
def quisque : IndeterminateQuantifier := ⟨Pronouns.quis.toProForm, Coordination.que, none⟩

theorem denote_quisque : ⟦quisque⟧ = ({Det.Family.every} : Set Det.Family.{u}) := by
  rw [← IndeterminateQuantifier.reading_of_conjunctive (q := quisque) rfl]; rfl

end Latin.Determiners
