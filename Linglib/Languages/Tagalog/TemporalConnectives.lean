module

public import Linglib.Semantics.Tense.Connective

/-!
# Tagalog temporal connectives

Lexical entries for the Tagalog temporal connectives *bago* 'before' and *pagkatapos* 'after'.
The aspect of a *bago*-clause fixes which bound of the embedded event the host precedes, the
neutral perfective its onset and the ability-and-involuntary-action perfective its culmination
([dell-1983]; [rett-2020a], the paper's (12)).

## References

* [dell-1983]
* [rett-2020a]
-/

@[expose] public section

namespace Tagalog.TemporalConnectives

open Tense

/-- *bago* 'before'. -/
def bago : Connective := { form := "bago", relation := .before }

/-- *pagkatapos* 'after'. -/
def pagkatapos : Connective := { form := "pagkatapos", relation := .after }

end Tagalog.TemporalConnectives
