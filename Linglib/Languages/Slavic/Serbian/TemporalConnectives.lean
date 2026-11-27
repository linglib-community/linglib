module

public import Linglib.Semantics.Tense.Connective

/-!
# Serbian temporal connectives

Lexical entries for the Serbian temporal connectives *pre* 'before', which takes a clause as *pre
nego što*, and *posle* 'after'. The aspect of the embedded verb fixes which bound of the embedded
event the host precedes, the imperfective its onset and the perfective its culmination
([rett-2020a], the paper's (11)).

## References

* [rett-2020a]
-/

@[expose] public section

namespace Serbian.TemporalConnectives

open Tense

/-- *pre* 'before', with a clause as *pre nego što*. -/
def pre : Connective := { form := "pre", relation := .before }

/-- *posle* 'after'. -/
def posle : Connective := { form := "posle", relation := .after }

end Serbian.TemporalConnectives
