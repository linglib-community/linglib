module

public import Linglib.Languages.Slavic.Czech.Particles
public import Linglib.Languages.Slavic.Czech.PolarityItems
public import Linglib.Semantics.PolarityItem.Polarity
public import Linglib.Data.Examples.StankovaSimik2025
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Statistics.StankovaSimik2025
public import Studies.Simik2024

/-!
# Staňková and Šimík (2025): Negation in Czech Polar Questions

Staňková and Šimík analyse negation in Czech polar questions. The negative prefix moves with the
finite verb, so the position of the verb fixes the position of the negation. A clause-initial
verb sits above the canonical negation operator and is licensed by the commitment operator FALSUM
alone, the outer reading of the negation, while a verb in situ is licensed by FALSUM or by the
canonical operator, the inner reading. The clause under FALSUM is positive and the clause under
the canonical operator negative, so the first admits the positive polarity item *nějaký* and the
second the concord item *žádný*.

Two sources fix the contextual evidence a negative question is felicitous under. The canonical
operator needs evidence against the prejacent and FALSUM is indifferent to evidence, and
declarative word order needs evidence for the proposition the question expresses while
interrogative order needs none. We define the evidence a question admits as that of some
available reading that admits its indefinite, within what its word order admits. An
interrogative question with the polarity item then admits every evidence, which is more than
English high negation admits; one with the concord item admits none; and a declarative question
admits evidence against the prejacent alone, whichever its indefinite.

The paper tests these predictions in a naturalness study and reports nine tests of fixed effects.
The model predicts an effect exactly where the test is significant in six of them. It predicts
no effect of the indefinite in declarative questions, where concord items were rated higher, and
no dependence on context of the polarity item in interrogative questions, where the neutral
context was rated higher.

The particle *náhodou* is licensed by FALSUM alone, so it excludes the concord item at either
verb position. A question with *copak* needs evidence for the proposition it expresses and a
prior belief against it, the situation of a Russian *razve* question.

## Implementation notes

* The readings of negation are polarities of the proposition the question double-checks, as in
  `Studies/Simik2024.lean`: `.positive` for FALSUM and `.negative` for the canonical operator.
* The evidence of declarative order is stated for the negative questions the paper studies. It is
  the evidence with which Šimík's table of Czech lists a negative question of each word order.
* An effect of a factor is predicted when two of its tested levels differ in felicity. The main
  experiment tests the negative and the neutral context, and the *copak* experiment a context
  that matches the polarity of the question and a neutral one.

## TODO

* The paper attributes the lower rating of interrogative questions with a polarity item in
  negative contexts to competition with declarative questions. The competition is not modelled.

## References

* [stankova-simik-2025]
* [repp-2013]
* [zeijlstra-2004]
* [gunlogson-2002]
* [sudo-2013]
* [gartner-gyuris-2017]
* [buring-gunlogson-2000]
* [simik-2024]
-/

@[expose] public section

namespace StankovaSimik2025

open Question Quantifier PolarityItem
open Simik2024 (VerbPosition NahodouLicensed razveSituation distribution czechForms)
open scoped Denotes

/-! ### Verb position and the readings of negation -/

/-- The readings of negation available at a verb position, each given as the polarity of the
proposition the question double-checks, `.positive` for FALSUM, the outer reading, and
`.negative` for the canonical operator, the inner reading. The clause-initial verb raises above
the canonical operator and is licensed by FALSUM alone, the verb in situ by FALSUM or by the
canonical operator (the paper's (11) and (12)). -/
def _root_.Simik2024.VerbPosition.availableReadings : VerbPosition → Finset Polarity
  | .v1 => {.positive}
  | .nonV1 => {.negative, .positive}

theorem mem_availableReadings_iff (wp : VerbPosition) (n : Polarity) :
    n ∈ wp.availableReadings ↔ n = .positive ∨ wp = .nonV1 := by
  cases wp <;> cases n <;> decide

/-- The unmarked reading at a verb position is that of the lowest available operator. -/
def _root_.Simik2024.VerbPosition.defaultReading : VerbPosition → Polarity
  | .v1 => .positive
  | .nonV1 => .negative

theorem defaultReading_mem (wp : VerbPosition) : wp.defaultReading ∈ wp.availableReadings := by
  cases wp <;> decide

/-! ### Indefinites as proxies for the readings -/

/-- The determiner realizing each indefinite. -/
def Examples.Indefinite.word : Examples.Indefinite → QuantificationalDeterminer
  | .nci => Czech.Determiners.zadny
  | .ppi => Czech.Determiners.nejaky

/-- The polarity class of each indefinite: *žádný* is a negative concord item, which clausal
negation licenses, and *nějaký* is a positive polarity item. -/
def Examples.Indefinite.cls : Examples.Indefinite → PolarityItem.Class
  | .nci => .npi .antiMorphic
  | .ppi => .ppi .antiMorphic

/-- Of the readings of *žádný*, exactly the indefinite one yields *no* under the one negation of the
clause (p. 5). -/
theorem compl_eq_no_iff {d : Det.Family} (hd : d ∈ ⟦Examples.Indefinite.nci.word⟧) :
    dᶜ = Det.Family.no ↔ d = Det.Family.some := by
  obtain rfl | rfl : d = Det.Family.no ∨ d = Det.Family.some := by
    simpa [Examples.Indefinite.word, Czech.Determiners.zadny, eq_comm] using hd
  all_goals simp [Det.Family.some_ne_no, Det.Family.some_ne_no.symm]

-- the clause under each operator, as a licenser, admits an indefinite exactly when the reading does
theorem admits_ofPolarity_cls_iff (W : Type) [Nonempty W] (i : Examples.Indefinite)
    (n : Polarity) : (Licenser.ofPolarity W n).Admits i.cls ↔ n.Admits i.cls :=
  Licenser.admits_ofPolarity_iff

theorem admits_ppi_iff_not_admits_nci (n : Polarity) :
    n.Admits Examples.Indefinite.ppi.cls ↔ ¬ n.Admits Examples.Indefinite.nci.cls := by
  cases n <;> decide

/-! ### Evidence and felicity -/

/-- The contextual evidence each operator admits. The canonical operator needs evidence against
the prejacent, and FALSUM, which conveys epistemic bias, admits any evidence. -/
def readingEvidence : Polarity → BiasValue
  | .negative => .plus .negative
  | .positive => Finset.univ

/-- The contextual evidence the word order of a negative question admits. Declarative order
needs evidence for the proposition the question expresses, here the negative one
([gunlogson-2002]), and interrogative order admits any evidence. -/
def orderEvidence : VerbPosition → BiasValue
  | .v1 => Finset.univ
  | .nonV1 => .plus .negative

-- the evidence with which [simik-2024]'s table lists a negative question of each word order
theorem orderEvidence_eq_image_distribution (wp : VerbPosition) :
    orderEvidence wp = (distribution czechForms ⟨wp, .negative⟩).image Prod.fst := by
  cases wp <;> decide

/-- The contextual evidence under which a negative question with the given verb position and
indefinite is felicitous: the evidence of some available reading that admits the indefinite,
within what the word order admits. -/
def evidence (wp : VerbPosition) (i : Examples.Indefinite) : BiasValue :=
  {n ∈ wp.availableReadings | n.Admits i.cls}.biUnion readingEvidence ∩ orderEvidence wp

-- (14): FALSUM on a clause-initial verb is compatible with every evidence
theorem evidence_v1_ppi : evidence .v1 .ppi = Finset.univ := by decide

theorem evidence_v1_nci : evidence .v1 .nci = ∅ := by decide

-- a declarative question needs evidence against the prejacent on either reading
theorem evidence_nonV1 (i : Examples.Indefinite) : evidence .nonV1 i = .plus .negative := by
  cases i <;> decide

/-- Czech outer negation on a clause-initial verb admits more evidence than English outer
negation does in the sample of [gartner-gyuris-2017], which bars evidence for the prejacent. -/
theorem evidential_englishV1_ssubset_evidence_v1_ppi :
    (GartnerGyuris2017.biasProfile GartnerGyuris2017.englishV1 (some .positive)).evidential ⊂
      evidence .v1 .ppi := by
  decide

/-! ### The particles -/

/-- A question with *náhodou* is well formed when some reading available at its verb position
licenses the particle and admits the indefinite, if there is one. -/
def NahodouFelicitous (wp : VerbPosition) (pol : Polarity) (i : Option Examples.Indefinite) :
    Prop :=
  ∃ n ∈ wp.availableReadings, NahodouLicensed pol n ∧ ∀ j ∈ i, n.Admits j.cls

instance (wp : VerbPosition) (pol : Polarity) (i : Option Examples.Indefinite) :
    Decidable (NahodouFelicitous wp pol i) :=
  inferInstanceAs (Decidable (∃ n ∈ wp.availableReadings, _))

-- (17), (18): the particle needs FALSUM and the concord item the canonical operator
theorem nahodouFelicitous_negative_iff (wp : VerbPosition) (i : Examples.Indefinite) :
    NahodouFelicitous wp .negative (some i) ↔ i = .ppi := by
  cases wp <;> cases i <;> decide

/-- The verb position of an example. -/
def Examples.WordOrder.toVerbPosition : Examples.WordOrder → VerbPosition
  | .v1 => .v1
  | .nonV1 => .nonV1

/-- The polarity of an example's finite verb. -/
def Examples.QuestionPolarity.toPolarity : Examples.QuestionPolarity → Polarity
  | .positive => .positive
  | .negative => .negative

/-- The judged examples with *náhodou*, (16) and (18), are acceptable exactly when some reading
available at the verb position licenses the particle and admits the indefinite. -/
theorem nahodou_example (x : Examples.Example) (hm : x.datum.method = none)
    (hx : x.datum.feature? "particle" = some Czech.Particles.nahodou.form) :
    ∀ o ∈ x.order, ∀ s ∈ x.polarity,
      (x.datum.judgment = .acceptable ↔
        NahodouFelicitous o.toVerbPosition s.toPolarity x.indefinite) := by
  revert hm hx; cases x <;> decide

-- `nahodou_example` reads the four rows of (16) and (18)
theorem nahodou_example_count :
    (Examples.Example.all.filter fun x ↦ x.datum.method = none ∧
      x.datum.feature? "particle" = some Czech.Particles.nahodou.form).length = 4 := by
  decide

/-- The bias profile of a *copak* question of polarity `s`: evidence for the proposition it
expresses and a prior belief in the opposite one (the paper's (19)). -/
def copakProfile (s : Polarity) : BiasProfile := ⟨.plus s, .plus (.negative * s)⟩

-- the situation of a Russian *razve* question with VERUM over a clause of the same polarity
theorem felicity_copakProfile (s : Polarity) :
    (copakProfile s).felicity = {razveSituation ⟨.positive, s⟩} := by
  cases s <;> decide

/-! ### The tests of the naturalness study -/

/-- Whether the model predicts the effect a test is of. Two levels of a factor differ when one
is felicitous and the other is not: the two indefinites in a tested context, the negative and
the neutral context for an indefinite, or, for *copak*, the context that matches the polarity of
the question and the neutral one. -/
def Predicts : Model → Effect → Prop
  | .nahodou, .indefinite =>
    ¬ (NahodouFelicitous .v1 .negative (some .ppi) ↔ NahodouFelicitous .v1 .negative (some .nci))
  | .copak, .context =>
    ∃ s : Polarity, ¬ ((s : SignType) ∈ (copakProfile s).evidential ↔
      (0 : SignType) ∈ (copakProfile s).evidential)
  | .nahodou, _ | .copak, _ => False
  | m, e =>
    let wp : VerbPosition := if m = .v1 then .v1 else .nonV1
    let ctx (i : Examples.Indefinite) : Prop :=
      ¬ ((-1 : SignType) ∈ evidence wp i ↔ (0 : SignType) ∈ evidence wp i)
    match e with
    | .indefinite =>
      ∃ ev ∈ ({-1, 0} : Finset SignType), ¬ (ev ∈ evidence wp .ppi ↔ ev ∈ evidence wp .nci)
    | .context => ∃ i, ctx i
    | .interaction => ¬ (ctx .ppi ↔ ctx .nci)
    | .contextWithinPPI => ctx .ppi
    | .contextWithinNCI => ctx .nci

instance : ∀ m e, Decidable (Predicts m e) := by
  intro m e
  cases m <;> cases e <;> unfold Predicts <;> infer_instance

/-- The model predicts an effect exactly where the reported test is significant, for six of the
nine tests. The three it misses are significant effects it does not predict: the indefinite in
declarative questions, and the interaction with context and the effect of context on the polarity
item in interrogative questions. -/
theorem predicts_iff_significant :
    ∀ t ∈ tests, (Predicts t.model t.effect ↔ t.p.Significant (1 / 20)) ↔
      (t.model, t.effect) ∉
        [(Model.nonV1, Effect.indefinite), (.v1, .interaction), (.v1, .contextWithinPPI)] := by
  decide +kernel

end StankovaSimik2025
