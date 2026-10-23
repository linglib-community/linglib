module

public import Linglib.Syntax.Comparative

/-!
# Swahili comparison

This file defines the Swahili comparative constructions as Stassen describes them. The
primary comparative takes the standard as the object of the exceed verb *-shinda* in the
infinitive, *mti huu ni mrefu ku-shinda ule* 'this tree is taller than that one', an exceed
comparative whose comparative predicate is the main verb. A second construction marks the
standard with *kuliko*, the infinitive of *-liko* 'be at', as in *nyumba yake nzuri sana
kuliko nyumba yangu* 'his house is better than my house', literally 'while there is my house',
which Stassen calls an indeterminate case, modelled on a chain but without an exceed verb.
Swahili also has a secondary conjoined comparative of the antonymous subtype, two juxtaposed
clauses, *jogoo wa Ali hodari, yule wa Juma dhaifu* 'Ali's rooster is stronger than Juma's',
which follows its balanced adversative chaining. The adjective carries no degree marking in
any of the three.

## Main definitions

* `Swahili.Comparison.kushinda`: the exceed comparative
* `Swahili.Comparison.kuliko`: the construction with the standard after *kuliko*
* `Swahili.Comparison.conjoined`: the conjoined comparative

## Main results

* `Swahili.Comparison.type_kushinda`, `Swahili.Comparison.type_conjoined`: the exceed and the
  conjoined constructions have the types their anatomy gives them

## Implementation notes

* The *kuliko* construction has a fixed adverbial standard in no spatial case, so the finer
  typology of `Studies/Stassen1985.lean` assigns it no type, which is Stassen's indeterminacy,
  while the typology of the atlas collapses it to locational.

## References

* [L. Stassen, *Comparison and Universal Grammar* (1985)][stassen-1985]
-/

@[expose] public section

namespace Swahili.Comparison

open Comparative

/-- The exceed comparative, whose standard is the object of the infinitive *ku-shinda*
'exceed' and whose adjective is unmarked for degree. -/
def kushinda : Comparative :=
  { standardMarker := [.pref "ku", .root "shinda"], caseAssignment := .fixed,
    fixedEncoding := some .directObject }

/-- The construction whose standard follows *kuliko*, the infinitive of *-liko* 'be at', an
adverbial standard in no spatial case. -/
def kuliko : Comparative :=
  { standardMarker := [.pref "ku", .root "liko"], caseAssignment := .fixed,
    fixedEncoding := some .adverbial }

/-- The conjoined comparative juxtaposes two clauses with antonymous predicates. -/
def conjoined : Comparative := { caseAssignment := .derived }

/-- The exceed construction is an exceed comparative. -/
theorem type_kushinda : kushinda.type = .exceed := rfl

/-- The juxtaposed construction is a conjoined comparative. -/
theorem type_conjoined : conjoined.type = .conjoined := rfl

end Swahili.Comparison
