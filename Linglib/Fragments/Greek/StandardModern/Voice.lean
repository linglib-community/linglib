module

public import Linglib.Syntax.Voice.Basic

/-!
# Modern Greek voice

The nonactive endings mark the reflexive voice, cumulated with the person and number of the
subject: *xteníz-ome* 'I am combing (myself, my hair)', *xteníz-ese* 'you are combing'. The
first person singular *-ome* stands for the series.

## Main definitions

* `Greek.StandardModern.reflexive`: the reflexive voice.

## References

* [haspelmath-2023b]
-/

@[expose] public section

namespace Greek.StandardModern

/-- The nonactive reflexive cumulates the A and the P in one S. -/
def reflexive : Voice := Voice.reflexive.marked [.suff "ome"]

end Greek.StandardModern
