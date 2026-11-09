module

public import Linglib.Semantics.Evidential.Defs

/-!
# German evidentiality

German has no evidentials proper, but its modal verbs and its present subjunctive have evidential
extensions. *Sollen* reports a rumour, 'is said to', and *wollen* a claim of the subject's,
usually with the implication that the claim is false. The present subjunctive, the Konjunktiv I,
marks reported speech, and in free indirect speech, where a reported clause stands on its own,
it alone shows that the clause is someone else's claim. Aikhenvald counts the Konjunktiv I as an
evidentiality strategy and places the modal verbs on the borderline between lexical means and
strategies; she reads *sollen* as marking inference or assumption as well as report.

## References

* [aikhenvald-2004]
* [durrell-2011]
-/

@[expose] public section

namespace German.Evidentiality

/-- German has no evidentials proper. -/
def evidentials : List Evidential := []

/-- *Sollen* in its sense of rumour or report, 'is said to', the source left unnamed. -/
def sollen : Evidential := { morphs := [.free "sollen"], covers := {.hearsay} }

/-- *Wollen* in its sense of claim, 'claims to', a report whose source is the subject. -/
def wollen : Evidential := { morphs := [.free "wollen"], covers := {.quotative} }

/-- The Konjunktiv I in reported speech, cited by its ending, as in *habe* and *wisse*. -/
def konjunktivI : Evidential := { morphs := [.suff "e"], covers := {.hearsay, .quotative} }

/-- The evidentiality strategies. -/
def strategies : List Evidential := [sollen, wollen, konjunktivI]

end German.Evidentiality
