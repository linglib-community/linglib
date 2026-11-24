module

public import Linglib.Syntax.Person.CaseConstraint
public import Linglib.Syntax.Feature.Person.Lattice
public import Linglib.Languages.Romance.Italian.Pronouns
public import Linglib.Languages.Romance.Spanish.Clitics
public import Linglib.Languages.German.Pronouns
public import Studies.Deal2024
public import Studies.CoonKeine2021
public import Studies.CharnavelMateu2015
public import Linglib.Data.Examples.AdamsonZompi2025
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Polite pronouns and the person-case constraint

The Italian polite pronoun LEI has the forms and the agreement of the third person feminine
singular and refers to the addressee. Adamson and Zompì give a polite pronoun two person values,
an uninterpretable one that agreement copies and an interpretable one read at LF, and ask which
of the two a person restriction on clitic clusters reads. A restriction that never bans a third
person accusative, read over the uninterpretable value,
[licenses a polite accusative under any dative](##AdamsonZompi2025.licit_formal_polite), and
this holds of the Strong constraint and the varieties it entails, of interaction and
satisfaction, and of feature gluttony alike. Read
over the interpretable value, a restriction
[bans a polite accusative wherever it bans a second
person](##AdamsonZompi2025.politeness_prediction),
which is [what the Italian, Spanish and German clusters show](##AdamsonZompi2025.rows_predicted).
German assumed-identity copulas go the other way: there
[polite SIE behaves as the third person plural it agrees as](##AdamsonZompi2025.assumed_identity).

## Implementation notes

A cluster is the scenario of the persons its two pronouns offer to Agree (`agreed`), each of
them optional, and a restriction licenses it when it licenses every scenario of persons the
cluster presents (`Licit`). A strong pronoun offers no person, since it is not cliticized and
enters no Agree relation with the applicative head; this is what makes a stressed pronoun or a
prepositional dative obviate the constraint. The causee of a *faire infinitif* causative enters
the Fancy Constraint as a third person whether or not it is a clitic.

A polite clitic is its third person counterpart denoting the addressee (`polite`), so Italian
*La* is `polite la`. The German pronouns of a Wackernagel cluster are weak; the fragment records
no strength for them, and they are read as offering their person.

The reader `scenario?` leaves out the rows whose gloss names two pronouns for one clitic. The
clitic logophoric restriction is stated on Charnavel and Mateu's hierarchy of logophoric centers,
which reads the person a clitic denotes; that some speakers reject a second person dative over
an accusative attitude holder is not derived. The Person Licensing Condition and the accounts of
polite pronouns by impoverishment or by recruitment of unmarked values have no formal
counterpart here.

## TODO

* The rejection by some Weak-PCC speakers of a first person dative over accusative LEI is not
  derived: the two constraints split on that cluster as they do on a first person dative over a
  second person accusative, where the paper finds the two judgments uncorrelated.

## References

* [adamson-zompi-2025]
* [deal-2024]
* [coon-keine-2021]
* [bejar-rezac-2003]
* [rezac-2011]
* [ackema-neeleman-2018]
* [wang-r-2023]
* [charnavel-mateu-2015]
* [adamson-anagnostopoulou-2025]
* [postal-1989]
-/

@[expose] public section

namespace AdamsonZompi2025

open PCC Italian.Pronouns Clause

/-! ### The two person values of a pronoun -/

/-- The polite counterpart of a third person pronoun: its form and agreement features, denoting
the addressee. -/
def polite (c : PersonalPronoun) : PersonalPronoun := { c with referential := {.addressee} }

/-- The person a pronoun offers to Agree, given the person value `person` that Agree copies.
A strong pronoun, which is not cliticized, offers none. -/
def agreed (person : PersonalPronoun → Option Person) (c : PersonalPronoun) : Option Person :=
  if c.strength = some .strong then none else person c

/-- The uninterpretable person value, the one agreement morphology realizes. -/
abbrev formal : PersonalPronoun → Option Person := agreed (·.person)

/-- The interpretable person value, the one read at LF. -/
abbrev interpretable : PersonalPronoun → Option Person := agreed PersonalPronoun.referentialPerson

variable {R R' : Scenario Person → Prop} {s : Scenario (Option Person)} {o : Option Person}
  {c : PersonalPronoun} {p q : Person} {person : PersonalPronoun → Option Person}

theorem agreed_of_strong (h : c.strength = some .strong) : agreed person c = none := by
  simp [agreed, h]

theorem agreed_of_ne_strong (h : c.strength ≠ some .strong) : agreed person c = person c := by
  simp [agreed, h]

@[simp] theorem formal_polite (c : PersonalPronoun) : formal (polite c) = formal c := rfl

theorem interpretable_polite (h : c.strength ≠ some .strong) :
    interpretable (polite c) = some .second := by
  rw [interpretable, agreed_of_ne_strong (c := polite c) h]
  exact Person.Category.sharedPerson_singleton .addressee

-- Italian LEI is the third person feminine singular *lei* denoting the addressee, capitalized
-- in writing.
theorem lei_formal_eq : lei_formal = { polite lei with form := "Lei" } := rfl

/-! ### Person restrictions on clusters -/

/-- The restriction `R` licenses a cluster when it licenses every scenario of persons the
cluster presents to Agree, the higher-ranked argument's over the accusative's. -/
def Licit (R : Scenario Person → Prop) (s : Scenario (Option Person)) : Prop :=
  ∀ p ∈ s.high, ∀ q ∈ s.low, R ⟨p, q⟩

instance [DecidablePred R] : DecidablePred (Licit R) :=
  fun _ ↦ inferInstanceAs (Decidable (∀ p ∈ _, ∀ q ∈ _, _))

@[simp] theorem licit_some : Licit R ⟨some p, some q⟩ ↔ R ⟨p, q⟩ := by simp [Licit]

@[simp] theorem licit_none_high : Licit R ⟨none, o⟩ := by simp [Licit]

@[simp] theorem licit_none_low : Licit R ⟨o, none⟩ := by simp [Licit]

theorem Licit.mono (h : ∀ t, R t → R' t) (hs : Licit R s) : Licit R' s :=
  fun p hp q hq ↦ h _ (hs p hp q hq)

/-- A restriction that never bans a third person accusative, read over the uninterpretable
person value, licenses a polite accusative under any higher argument. -/
theorem licit_formal_polite (hR : ∀ p, R ⟨p, .third⟩) (hc : c.person = some .third)
    (o : Option Person) : Licit R ⟨o, formal (polite c)⟩ := by
  intro p _ q hq
  obtain rfl : q = .third := by
    by_cases h : c.strength = some .strong <;> simp_all [agreed]
  exact hR p

/-- The PCC and politeness prediction: read over the interpretable person value, a restriction
that bans a second person accusative under a `p` bans a polite accusative clitic under it. -/
theorem politeness_prediction (hc : c.strength ≠ some .strong) (h : ¬ R ⟨p, .second⟩) :
    ¬ Licit R ⟨some p, interpretable (polite c)⟩ := by
  rwa [interpretable_polite hc, licit_some]

/-! ### The morphosyntactic accounts -/

-- The Strong constraint licenses a polite accusative, and with it every variety it entails.
theorem strong_licenses_polite (hc : c.person = some .third) (o : Option Person) :
    Licit Strong ⟨o, formal (polite c)⟩ :=
  licit_formal_polite strong_third hc o

-- Interaction and satisfaction: a grammar licensing anything licenses a polite accusative.
theorem deal_licenses_polite {g : Deal2024.Grammar} {t : Scenario Person}
    (h : Deal2024.Licit g t) (hc : c.person = some .third) (o : Option Person) :
    Licit (Deal2024.Licit g) ⟨o, formal (polite c)⟩ :=
  licit_formal_polite h.third hc o

-- Feature gluttony: no probe is gluttonous over a polite accusative.
theorem gluttony_licenses_polite (P : Finset Person.Segment) (ioOpaque : Bool)
    (hc : c.person = some .third) (o : Option Person) :
    Licit (¬ CoonKeine2021.PCCViolation P ioOpaque ·) ⟨o, formal (polite c)⟩ :=
  licit_formal_polite (CoonKeine2021.direct_never_banned P ioOpaque) hc o

/-! ### Italian -/

-- Dative LEI over a third person accusative is licit on either person value, under the Strong
-- constraint and so under the Weak one.
theorem lei_dative :
    Licit Strong ⟨formal (polite le_dat), formal la⟩ ∧
      Licit Strong ⟨interpretable (polite le_dat), interpretable la⟩ := by
  decide

-- A third person dative over accusative LEI is licensed on the uninterpretable value even by
-- the Strong constraint and banned on the interpretable one even by the Weak one.
theorem lei_accusative :
    Licit Strong ⟨formal gli, formal (polite la)⟩ ∧
      ¬ Licit Weak ⟨interpretable gli, interpretable (polite la)⟩ := by
  decide

-- Stressed LEI and a prepositional dative obviate the constraint.
theorem lei_repairs :
    Licit R ⟨interpretable gli, interpretable lei_formal⟩ ∧
      Licit R ⟨interpretable lui, interpretable (polite la)⟩ :=
  ⟨licit_none_low, licit_none_high⟩

-- The Fancy Constraint: under a third person causee a third person accusative clitic is licit
-- and second person and LEI are not.
theorem fancy_constraint :
    Licit Strong ⟨some .third, interpretable la⟩ ∧
      ¬ Licit Weak ⟨some .third, interpretable ti⟩ ∧
      ¬ Licit Weak ⟨some .third, interpretable (polite la)⟩ := by
  decide

-- Coordinated with a third person, LEI resolves to second person on its interpretable value and
-- to third on its uninterpretable one.
theorem resolved_person :
    lei_formal.referentialPerson.map (· ⊔ .third) = some .second ∧
      lei_formal.person.map (· ⊔ .third) = some .third := by
  decide

-- The two constraints split on a first person dative over accusative LEI.
theorem first_dative_lei :
    Licit Weak ⟨interpretable mi, interpretable (polite la)⟩ ∧
      ¬ Licit Strong ⟨interpretable mi, interpretable (polite la)⟩ := by
  decide

/-! ### Logophoric centers -/

-- On the hierarchy of logophoric centers a third person dative excludes accusative LEI as it
-- does a second person, and with an accusative attitude holder dative LEI is licit, as a second
-- person dative is, where a third person dative is not.
theorem logophoric_centers :
    CharnavelMateu2015.Licit ([gli, la].filterMap CharnavelMateu2015.center) ∧
      ¬ CharnavelMateu2015.Licit ([gli, ti].filterMap CharnavelMateu2015.center) ∧
      ¬ CharnavelMateu2015.Licit ([gli, polite la].filterMap CharnavelMateu2015.center) ∧
      ∀ d ∈ [gli, ti, polite le_dat],
        (CharnavelMateu2015.Licit ([d].filterMap CharnavelMateu2015.center ++ [.attitudeHolder]) ↔
          d ≠ gli) := by
  decide +kernel

/-! ### German assumed identity -/

open CoonKeine2021 in
/-- The goal a pronoun presents to the copula's probe, with its agreement person and number. -/
def goal (c : PersonalPronoun) : Option Goal :=
  c.person.map fun p ↦ if c.number = some .plural then dpPl p else dp p

open CoonKeine2021 in
/-- An assumed-identity copula is well formed when neither the person probe nor the number probe
is gluttonous over its two noun phrases. -/
def IdentityLicit (goals : List Goal) : Prop :=
  ¬ Gluttonous Goal.personSegments weakProbe goals ∧
    ¬ Gluttonous Goal.numberSegments (numberProbe weakProbe) goals

open CoonKeine2021 in
instance : DecidablePred IdentityLicit := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

open CoonKeine2021 in
/-- Under a third person plural subject, polite SIE is well formed where second person plural
*ihr* is not, and under a singular subject it is ill formed, as a third person plural is. -/
theorem assumed_identity :
    (∀ g ∈ goal German.Pronouns.sie_formal,
      IdentityLicit [dpPl .third, g] ∧ ¬ IdentityLicit [dp .third, g]) ∧
      ∀ g ∈ goal German.Pronouns.ihr, ¬ IdentityLicit [dpPl .third, g] := by
  decide +kernel

/-! ### The data -/

section Data

open Examples

/-- The scenario of a row under the person value `v`: the dative pronoun its features name,
or the third person causee of a causative, over the accusative pronoun. -/
def scenario? (v : PersonalPronoun → Option Person) (e : Datum) :
    Option (Scenario (Option Person)) := do
  let (dative, accusative) ← e.byLanguage
    [(.italian,
        ([("1", mi), ("2", ti), ("3", gli), ("LEI", polite le_dat), ("3 PP", lui)],
          [("1", mi), ("2", ti), ("3", la), ("LEI", polite la), ("2 stressed", te_tonic),
            ("LEI stressed", lei_formal), ("3 resuming camouflage nominal", lo),
            ("3 resuming imposter", lo)])),
      (.spanish,
        ([("3", Spanish.Clitics.se_dat)],
          [("3", Spanish.Clitics.lo), ("USTED", polite Spanish.Clitics.lo)])),
      (.german,
        ([("3", German.Pronouns.er)],
          [("2", German.Pronouns.du), ("3PL", German.Pronouns.sie_pl),
            ("SIE", German.Pronouns.sie_formal)]))]
  let low ← e.parse? "accusative" accusative
  let high ← (e.parse? "dative" dative).map v <|> e.parse? "causee" [("3", some .third)]
  pure ⟨high, v low⟩

/-- The band the Person Case Constraint predicts for a cluster: accepted where the Strong
constraint licenses it, divided where only the Weak one does, and rejected where neither does. -/
def predicted (s : Scenario (Option Person)) : Judgment.Band :=
  if Licit Strong s then .accepted
  else if Licit Weak s then .divided
  else .rejected

/-- Read over the interpretable person value, every cluster of the three languages lands in the
band the constraint predicts, the repairs and the causatives included. -/
theorem rows_predicted : Datum.Checks (scenario? interpretable) predicted Examples.all 25 := by
  decide

/-- Read over the uninterpretable person value, the constraint fits a row exactly when the row
is accepted or the two values present the same scenario: it misses every rejected and every
divided cluster with a polite clitic. -/
theorem formal_fits_iff : ∀ e ∈ Examples.all,
    (e.Fits (scenario? formal) predicted ↔
      e.judgment = .acceptable ∨ scenario? formal e = scenario? interpretable e) := by
  decide

open CoonKeine2021 in
/-- The two noun phrases of an assumed-identity row. -/
def goals? (e : Datum) : Option (List Goal) := do
  let table := [("2SG", some (dp .second)), ("3SG", some (dp .third)),
    ("3PL", some (dpPl .third)), ("SIE", goal German.Pronouns.sie_formal)]
  pure [← (e.parse? "DP1" table).join, ← (e.parse? "DP2" table).join]

-- Every assumed-identity copula is well formed exactly when no probe is gluttonous over it.
theorem identity_rows :
    Datum.Checks goals? (fun gs ↦ .ofProp (IdentityLicit gs)) Examples.all 7 := by
  decide +kernel

end Data

end AdamsonZompi2025
