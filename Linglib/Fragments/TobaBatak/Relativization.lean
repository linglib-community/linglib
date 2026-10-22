module

public import Linglib.Syntax.Clause.Relative

/-!
# Toba Batak relative clauses

Toba Batak has two postnominal relative-clause strategies, and neither relativizes direct
objects. The relativizer *na* introduces a clause with the relativized position left empty, as
in *boru-boru na manussi abit i* 'the woman who is washing clothes', and relativizes subjects
only. A direct object is relativized as the subject of the object voice
(`TobaBatak.objectVoice`), whose *di-* becomes *ni-* in a subordinate clause: *abit na nisussi
ni boru-boru i* 'the clothes that were washed by the woman'. No voice makes a noun phrase governed
by a preposition, an indirect object included, the subject, and these are relativized by *ima
na*, which retains a personal pronoun in the relativized position: *dakdanak i, ima- na nipaboa
ni si Rotua turi-turian-i tu ibana* 'the child that Rotua told the story to'. The data are
Keenan and Comrie's.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace TobaBatak

/-- The relativizer *na* leaves the relativized position empty and relativizes subjects only. -/
def relNa : Relativizer where
  form := "na"
  placement := .postNominal
  realize
    | .subject => {.gap}
    | _ => ∅

/-- The relativizer *ima na*, with a personal pronoun retained in the relativized position,
relativizes indirect objects, obliques and genitives. -/
def relImaNa : Relativizer where
  form := "ima na"
  placement := .postNominal
  realize
    | .indirectObject | .oblique | .genitive => {.resumptive}
    | _ => ∅

/-- The Toba Batak relativizers. -/
def relativizers : List Relativizer := [relNa, relImaNa]

end TobaBatak
