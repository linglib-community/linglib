module

public import Linglib.Fragments.German.Conjugation
public import Linglib.Fragments.German.Modals

/-!
# German evidentiality

German has no evidentials proper, but its modal verbs and its present subjunctive have evidential
extensions. *Sollen* reports a rumour, 'is said to', and *wollen* a claim of the subject's,
usually with the implication that the claim is false. The main use of the present subjunctive,
the Konjunktiv I, is to mark indirect speech, and in free indirect speech, where a reported
clause stands on its own, it alone shows that the clause is someone else's claim. Aikhenvald
counts the Konjunktiv I as an evidentiality strategy and places the modal verbs on the borderline
between lexical means and strategies; she reads *sollen* as marking inference or assumption as
well as report.

## Implementation notes

The strategies are read off the entries whose main meaning they extend: the modal verbs' from
their entries in `German.Modals`, and the Konjunktiv I's form from its paradigm in
`German.Conjugation`.

## References

* [aikhenvald-2004]
* [durrell-2011]
-/

@[expose] public section

namespace German.Evidentiality

/-- German has no evidentials proper. -/
def evidentials : List Evidential := []

/-- The Konjunktiv I in reported speech, cited by the ending of its third person singular, the
one form in which it differs in practice from the present indicative, as in *habe* and *wisse*. -/
def konjunktivI : Evidential :=
  { morphs := (Conjugation.konjunktivIEndings.realize (.personNumber .third .singular)).toList,
    covers := {.hearsay, .quotative} }

/-- The evidentiality strategies: the evidential extensions of the modal verbs that have one,
*sollen* and *wollen*, and the Konjunktiv I. -/
def strategies : List Evidential := ModalAuxiliary.strategies Modals.allModals ++ [konjunktivI]

end German.Evidentiality
