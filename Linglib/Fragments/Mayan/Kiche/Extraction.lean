module

public import Linglib.Syntax.Reflex
public import Linglib.Fragments.Mayan.Extraction
public import Linglib.Fragments.Mayan.Kiche.Voice

/-!
# K'iche' extraction marking

K'iche' (K'ichean Mayan) puts the verb in the Agent Focus voice when a transitive subject is
extracted, and adds the fronting particle *wi* to the verbal complex when a recipient, an
oblique introduced by a relational noun, or a locative, instrument or benefactive phrase is
extracted, comitatives too; the particle is obligatory in the varieties Mendes and Ranero
describe and absent or optional in others, and reasons, purposes, manners and temporals never
license it. Absolutive extraction is unmarked. The benefactive cell records the K'ichean pattern
as Elkins, Torrence and Brown summarize it, which they note varies by variety between recipients
and benefactives.

## Main declarations

* `Kiche.Extraction.wi`: the fronting particle.
* `Kiche.Extraction.realize`: the reflexes extraction from each `Mayan.ExtractionSite` licenses
  on a verb of each class, the Agent Focus marker taken from `Kiche.agentFocus`.
* `Kiche.Extraction.wi_mem_realize_iff`: *wi* marks the extraction of the recipient and of the
  low adjuncts.

## References

* [coon-mateo-pedro-preminger-2014]
* [elkins-torrence-brown-2026]
* [mendes-ranero-2021]
* [mondloch-2017]
-/

@[expose] public section

namespace Kiche.Extraction

/-- The fronting particle *wi*. -/
def wi : Morphology.Morph := .free "wi"

/-- Transitive-subject extraction takes the Agent Focus marker of the verb's class on the verb;
recipient and low-adjunct extraction adds *wi* to the verbal complex; everything else is
unmarked. -/
def realize (c : Mayan.VerbClass) : Mayan.ExtractionSite → Finset (Reflex Mayan.Host)
  | .argument .A => {.morpheme .verb (agentFocus c).marker}
  | .argument .R | .adjunct .instrument | .adjunct .benefactive | .adjunct .locative =>
      {.morpheme .verbalComplex [wi]}
  | _ => ∅

theorem wi_mem_realize_iff (c : Mayan.VerbClass) (s : Mayan.ExtractionSite) :
    Reflex.morpheme .verbalComplex [wi] ∈ realize c s ↔
      s = .argument .R ∨ s = .adjunct .instrument ∨ s = .adjunct .benefactive ∨
        s = .adjunct .locative := by
  decide +revert

end Kiche.Extraction
