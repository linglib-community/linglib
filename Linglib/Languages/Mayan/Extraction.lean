module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Mayan extraction morphology

In most Mayan languages the focusing, questioning or relativization of a transitive subject
changes the verb: it takes the Agent Focus form, which lacks the Set A marker and carries a
suffix of its own, so that a clause with two arguments is inflected like an intransitive, as
Stiebels and Polian describe it. The form is obligatory in the languages with the ergative
extraction constraint, optional in Tsotsil, and absent in Chol and Tseltal; Mam extracts a
transitive subject through its antipassive instead. Several languages also mark the extraction
of non-core arguments and adjuncts, K'iche' and Kaqchikel with the particle *wi* and Mam with
the enclitic =(y)a', and which classes of adjunct license the marker varies.

Each language's `Extraction.realize` records the reflexes an extraction from each site licenses,
as a finite set of `Reflex Mayan.Host`. The reflex of transitive-subject extraction is the
marker of the voice the verb switches to, Agent Focus or the antipassive. A fragment whose
sources leave some sites undescribed gives its values in `Option`, `none` at those sites and
`some ∅` where an extraction is documented as unmarked.

## Main declarations

* `Mayan.VerbForm`: the transitive and Agent Focus forms, with `Mayan.VerbForm.HasSetA`.
* `Mayan.Adjunct`, `Mayan.ExtractionSite`: the adjunct classes, and the extraction sites, an
  argument by its role or an adjunct by its class.
* `Mayan.Host`: the constituents an extraction reflex is hosted by.

## Implementation notes

The argument sites are the comparative roles, so a recipient is `.argument .R` however a
language codes it. The K'ichean languages and Mam code it as an oblique introduced by a relational
noun, the indirect object or dative of Mendes and Ranero and of Elkins, Torrence and Brown, and
its extraction is marked as a low adjunct's is. Chol and the Tseltalan languages make it the
primary object of the applicative *-be*, cross-referenced by Set B, and it extracts as the patient
does.

## References

* [elkins-torrence-brown-2026]
* [mendes-ranero-2021]
* [polian-2017]
* [stiebels-2006]
-/

@[expose] public section

namespace Mayan

/-- A transitive verb has the canonical transitive form and the Agent Focus form, which
transitive-subject extraction selects wherever a language has it. -/
inductive VerbForm where
  | transitive
  | agentFocus
  deriving DecidableEq, Repr, Fintype

/-- The form bears Set A: the canonical transitive does, while the Agent Focus form is
inflected as an intransitive and bears only Set B ([polian-2017]). -/
def VerbForm.HasSetA (f : VerbForm) : Prop := f = .transitive

instance : DecidablePred VerbForm.HasSetA := fun f ↦ inferInstanceAs (Decidable (f = _))

/-- The classes of adjunct that Mayan extraction morphology distinguishes. Comitatives, which the
K'ichean particle also tracks, are not carried. -/
inductive Adjunct where
  | instrument | benefactive | locative | reason | purpose | manner | temporal
  deriving DecidableEq, Repr, Fintype

/-- An extraction site is an argument, by its role, or an adjunct, by its class, the granularity
the marking distinguishes. -/
inductive ExtractionSite where
  | argument (r : ArgumentRole)
  | adjunct (a : Adjunct)
  deriving DecidableEq, Repr, Fintype

/-- An extraction reflex is hosted by the verb stem, which a voice suffix alters, by the verbal
complex, the word a particle or enclitic closes, by a directional auxiliary, or by the extracted
phrase itself. -/
inductive Host where
  | verb
  | verbalComplex
  | directional
  | phrase
  deriving DecidableEq, Repr, Fintype

end Mayan
