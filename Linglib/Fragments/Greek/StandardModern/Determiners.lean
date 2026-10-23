module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Modern Greek determiners

The Standard Modern Greek articles in the nominative: the definite *o*, *i*, *to* of the
masculine, feminine and neuter singular and *oi*, *ta* of the plural, one syncretic definite
covering Schwarz's use types, and the indefinite *enas*, *mia*, *ena*.

## References

* [schwarz-2009]
-/

@[expose] public section

namespace Greek.StandardModern.Determiners

/-- The definite article with the given form. -/
def definite (form : String) : Article :=
  { form, definiteness := .definite, exponent := .dedicatedMorpheme
    uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- The indefinite article with the given form. -/
def indefinite (form : String) : Article :=
  { form, definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- *o* — the masculine singular definite article. -/
def o : Article := definite "o"

/-- *i* — the feminine singular definite article. -/
def i : Article := definite "i"

/-- *to* — the neuter singular definite article. -/
def to_ : Article := definite "to"

/-- *oi* — the masculine and feminine plural definite article. -/
def oi : Article := definite "oi"

/-- *ta* — the neuter plural definite article. -/
def ta : Article := definite "ta"

/-- *enas* — the masculine indefinite article. -/
def enas : Article := indefinite "enas"

/-- *mia* — the feminine indefinite article. -/
def mia : Article := indefinite "mia"

/-- *ena* — the neuter indefinite article. -/
def ena : Article := indefinite "ena"

/-- The Greek determiner inventory. -/
def inventory : Determiner.Inventory :=
  [o, i, to_, oi, ta, enas, mia, ena].map .article

theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end Greek.StandardModern.Determiners
