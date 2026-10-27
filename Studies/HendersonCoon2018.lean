module

public import Studies.CoonMateoPedroPreminger2014
public import Studies.Erlewine2016
public import Linglib.Data.Examples.HendersonCoon2018

/-!
# Henderson and Coon (2018): Adverbs and variability in Kaqchikel Agent Focus

Erlewine derives the Kaqchikel ban on extracting a transitive subject from anti-locality: the
subject sits in Spec,IP, one step below Spec,CP, so an adverb adding a projection between them
should make Agent Focus unnecessary. Henderson and Coon reply that a subject extracts with
ergative agreement and no Agent Focus when its object is a reflexive, an extended reflexive, a
clause or a light verb's complement, as accounts on which the object's Case traps the subject
expect, and that the adverb effect is not one: the same adverb occurs with Agent Focus and
without it, negation never removes it, and adverbs that cannot take a clause never do. A string
without Agent Focus is biclausal, an adverb predicated of a clause whose subject is a resumptive
pronoun, so nothing is extracted; an overt complementizer or pronoun forces that parse, and Agent
Focus then appears only when the pronoun is focused inside the lower clause.

## Main statements

* `rows_fit`: with the two parses and a case-based account of extraction, every example is
  grammatical exactly when one of its parses converges.
* `monoclausal_fits_iff`: with the monoclausal parse alone the case-based account fails exactly
  on the examples without Agent Focus whose subject seems to cross an adverb that takes a clause.
* `antiLocality_fits_iff`: Erlewine's grammar fits an example exactly when its object is a full DP
  and either nothing intervenes or a transitive verb follows an adverb that takes a clause.

## Implementation notes

* The case-based account is the convergence of `Studies/CoonMateoPedroPreminger2014.lean` with
  Infl licensing the object, as Kaqchikel's high absolutive has it. Henderson and Coon endorse no
  particular account of this kind, and that one was proposed for Q'anjob'al.
* Reflexive and extended reflexive objects are caseless, as in that study; the clausal complement
  and the light verb's complement are taken to need no Case either, the explanation Henderson and
  Coon suggest.
* The biclausal parse is available when the intervener is an adverb that takes a clause, the
  monoclausal parse when no overt complementizer or resumptive pronoun marks a lower clause.
  Erlewine's grammar reads any intervener, negation included, as one projection above TP.
* Example numbers are the published version's. The examples are `Data.Examples.HendersonCoon2018`;
  the attested (26), whose object may be a clause, and (44), whose verb is a perfect, are left out.

## References

* [henderson-coon-2018]
* [erlewine-2016]
* [coon-mateo-pedro-preminger-2014]
-/

@[expose] public section

namespace HendersonCoon2018

open HendersonCoon2018.Examples
open CoonMateoPedroPreminger2014 (Clause Converges voiceOf)

/-! ### Interveners -/

/-- The material between a preverbal phrase and the verb, the adverbs *kan qitzij* and *kan*
'truly', *k'a ri* 'then', *jantäq* 'sometimes' and *jumul* 'always', and negation *man*. -/
inductive Intervener
  | kanQitzij
  | kan
  | k'aRi
  | jantäq
  | jumul
  | negation
  deriving DecidableEq, Repr

/-- An intervener can be a predicate taking a clause, as *kan qitzij*, *kan* and *k'a ri* can
(§5.1) and *jantäq*, *jumul* (§5.3) and negation (§4) cannot. -/
def Intervener.TakesClause (i : Intervener) : Prop := i = .kanQitzij ∨ i = .kan ∨ i = .k'aRi

instance : DecidablePred Intervener.TakesClause := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-! ### Examples and their parses -/

/-- The objects of §3.2. -/
inductive ObjectKind
  | dp
  | reflexive
  | extendedReflexive
  | clause
  | lightVerb
  deriving DecidableEq, Repr

/-- The case-based account's object: a full DP needs Case and the others are caseless. -/
def ObjectKind.toObject : ObjectKind → CoonMateoPedroPreminger2014.Object
  | .dp => .dp
  | _ => .caseless

/-- What stands where an extracted subject would leave its trace, a gap, an overt resumptive
pronoun, or one focused inside its clause. -/
inductive Resumption
  | gap
  | pronoun
  | focused
  deriving DecidableEq, Repr

/-- An extraction example, with the argument that seems extracted, the form of the verb, the
object, what intervenes, whether a complementizer is overt, what stands at the subject position,
and the persons of the arguments. -/
structure Example where
  extracted : Erlewine2016.Arg
  form : Mayan.VerbForm
  object : ObjectKind
  intervener : Option Intervener
  complementizer : Bool
  resumption : Resumption
  subject : Person
  objectPerson : Person

/-- The two structures a string may have (§5), one clause with its phrase extracted past the
intervener, or an adverb predicated of a lower clause with a resumptive subject. -/
inductive Parse
  | monoclausal
  | biclausal
  deriving DecidableEq, Fintype, Repr

namespace Example

variable (e : Example)

/-- A string parses as one clause unless an overt complementizer or resumptive pronoun marks a
lower clause, and as two when the intervener takes a clause. -/
def Parses : Parse → Prop
  | .monoclausal => e.complementizer = false ∧ e.resumption = .gap
  | .biclausal => ∃ i ∈ e.intervener, i.TakesClause

instance : DecidablePred e.Parses
  | .monoclausal => inferInstanceAs (Decidable (_ ∧ _))
  | .biclausal => inferInstanceAs (Decidable (∃ i ∈ e.intervener, _))

/-- The role extracted in a parse's clause, the phrase itself in one clause and, in the lower
clause of two, only a focused resumptive pronoun. -/
def extractedRole : Parse → Option ArgumentRole
  | .monoclausal => some (e.extracted.role true)
  | .biclausal => if e.resumption = .focused then some (e.extracted.role true) else none

/-- The clause the case-based account judges for a parse: finite, Infl licensing the object, the
Voice of the attested form and the object's Case needs. -/
def clause (p : Parse) : Clause :=
  ⟨CoonMateoPedroPreminger2014.Language.kaqchikel.licenser, true,
    .transitive (voiceOf e.form) e.object.toObject,
    e.extractedRole p, false⟩

/-- Erlewine's input for the string as one clause, any intervener a projection above TP below
the landing site. -/
def erlewineInput : Erlewine2016.Input :=
  ⟨true, (if e.intervener.isSome then [.advP] else []) ++ [.cP],
    some (e.extracted, if e.intervener.isSome then 1 else 0), e.subject, e.objectPerson⟩

/-- Erlewine's grammar realizes the attested form in an optimal derivation. -/
def AntiLocality : Prop :=
  ∃ c ∈ (Erlewine2016.kaqchikel.tableau e.erlewineInput).optimal,
    c.form e.erlewineInput.args = e.form

instance : Decidable e.AntiLocality :=
  inferInstanceAs (Decidable (∃ c ∈ (Erlewine2016.kaqchikel.tableau e.erlewineInput).optimal, _))

end Example

/-! ### The examples -/

/-- The rows' labels for the interveners. -/
def intervenerTable : List (String × Intervener) :=
  [("kan qitzij", .kanQitzij), ("kan", .kan), ("k'a ri", .k'aRi), ("jantäq", .jantäq),
    ("jumul", .jumul), ("man", .negation)]

/-- The rows' labels for the objects. -/
def objectTable : List (String × ObjectKind) :=
  [("dp", .dp), ("reflexive", .reflexive), ("extendedReflexive", .extendedReflexive),
    ("clause", .clause), ("lightVerb", .lightVerb)]

/-- The example an extraction row describes. -/
def Example.ofDatum (d : Datum) : Option Example := do
  let extracted ← d.parse? "extracted" [("subject", Erlewine2016.Arg.subj), ("object", .obj)]
  let form ← d.parse? "verb" [("AF", Mayan.VerbForm.agentFocus), ("TV", .transitive)]
  let object ← d.parse? "objectKind" objectTable
  let subject ← d.parse? "subject" Erlewine2016.personTable
  let objectPerson ← d.parse? "object" Erlewine2016.personTable
  let resumption :=
    (d.parse? "resumptive" [("overt", Resumption.pronoun), ("focused", .focused)]).getD .gap
  pure ⟨extracted, form, object, d.parse? "intervener" intervenerTable,
    (d.feature? "complementizer").isSome, resumption, subject, objectPerson⟩

/-- An extraction row. -/
def IsExtraction (d : Datum) : Prop := d.feature? "construction" = some "extraction"

instance : DecidablePred IsExtraction := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- Every example is grammatical exactly when one of its parses converges under the case-based
account (§5). -/
theorem rows_fit : ∀ d ∈ Examples.all, IsExtraction d →
    ∃ e ∈ Example.ofDatum d,
      (d.judgment = .acceptable ↔ ∃ p, e.Parses p ∧ Converges (e.clause p)) := by
  decide

/-- Without the biclausal parse, the case-based account fails exactly on non-AF examples whose
subject seems to cross a clause-taking adverb, the minimal pairs of §4. -/
theorem monoclausal_fits_iff : ∀ d ∈ Examples.all, IsExtraction d →
    ∃ e ∈ Example.ofDatum d, e.Parses .monoclausal →
      ((d.judgment = .acceptable ↔ Converges (e.clause .monoclausal)) ↔
        ¬ (e.form = .transitive ∧ e.extracted = .subj ∧ ∃ i ∈ e.intervener, i.TakesClause)) := by
  decide

/-- Erlewine's grammar fits a monoclausal example iff its object is a full DP and nothing intervenes
or a transitive verb follows a clause-taking adverb (§3.2, §4, §5.3, (5), (6)). -/
theorem antiLocality_fits_iff : ∀ d ∈ Examples.all, IsExtraction d →
    ∃ e ∈ Example.ofDatum d, e.Parses .monoclausal →
      ((d.judgment = .acceptable ↔ e.AntiLocality) ↔
        e.object = .dp ∧
          (e.intervener = none ∨ (e.form = .transitive ∧ ∃ i ∈ e.intervener, i.TakesClause))) := by
  decide +kernel

-- §5.1, §5.3
theorem embedding_rows : ∀ d ∈ Examples.all, d.feature? "construction" = some "embedding" →
    ∃ i ∈ d.parse? "adverb" intervenerTable, (d.judgment = .acceptable ↔ i.TakesClause) := by
  decide

end HendersonCoon2018
