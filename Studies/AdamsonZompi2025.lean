module

public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Linglib.Syntax.Person.Lattice
public import Linglib.Fragments.Romance.Italian.Pronouns
public import Linglib.Fragments.Romance.Spanish.Pronouns
public import Linglib.Fragments.German.Pronouns
public import Studies.Deal2024
public import Studies.CoonKeine2021
public import Linglib.Data.Examples.AdamsonZompi2025

/-!
# Polite pronouns and the person-case constraint

The Italian polite pronoun LEI is formally third person feminine singular but refers to the
addressee, and in a ditransitive clitic cluster it patterns with the second person. Adamson and
Zompì give polite pronouns two person values, an uninterpretable one read by agreement and an
interpretable one read at LF, and argue that the person-case constraint reads the interpretable
one. A person restriction is stated over a person valuation of pronoun entries (`Licit`): the
agreement valuation `Morphosyntactic` reads the fragments' `person` and the LF valuation
`Syntacticosemantic` their `referentialPerson`.

## Main results

* `morphosyntactic_iff_of_ordinary`: the two valuations coincide on ordinary pronouns.
* `morphosyntactic_lei_formal`, `syntacticosemantic_lei_formal`: agreement-keyed restrictions
  treat LEI as *lei*, interpretation-keyed ones as *tu*.
* `lei_accusative`: on the Weak and Strong grammars the interpretable valuation bans a third
  person dative over accusative LEI, which the agreement valuation licenses, as do the accounts of
  `deal_licenses_lei` and `gluttony_licenses_lei`.
* `fancy_constraint`: the Fancy Constraint of *faire*-causatives gives the same cells.
* `resolved_person`: coordination resolves LEI to second person on its interpretable value and to
  third on its agreement value.
* `usted_accusative`, `sie_accusative`: Spanish USTED and German SIE show the effect.
* `assumed_identity`: under the German assumed-identity restriction, an exponence effect, SIE
  behaves as third person plural.
* `rows_predicted`, `morphosyntactic_misses`: every clitic-cluster judgment follows from the
  interpretable valuation over the two grammars, while the agreement valuation licenses every
  rejected row with a polite accusative.

## Implementation notes

As in the paper, the rejection by some Weak-PCC speakers of a first person dative over accusative
LEI is left open (`first_dative_lei`). The Person Licensing Condition, the clitic logophoric
restriction, and the rival accounts of polite pronouns by impoverishment or by unmarked-value
recruitment have no formal counterpart here. The reader `pair?` reads only the rows whose
`dative` and `accusative` features name a single pronoun, which leaves out the repair rows
(stressed pronouns and prepositional datives obviate the constraint), the ambiguous clusters and
the camouflage resumptions.

## References

* [adamson-zompi-2025]
* [pancheva-zubizarreta-2018]
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

open PCC Italian.Pronouns

/-! ### Person restrictions over a person valuation -/

/-- `R` licenses the dative–accusative pair `dat`, `acc` under the person valuation `person`
when it licenses the scenario of the dative's person over the accusative's. -/
def Licit (R : Clause.Scenario Person → Prop) (person : PersonalPronoun → Option Person)
    (dat acc : PersonalPronoun) : Prop :=
  ∃ p q, person dat = some p ∧ person acc = some q ∧ R ⟨p, q⟩

instance (R : Clause.Scenario Person → Prop) [DecidablePred R]
    (person : PersonalPronoun → Option Person) (dat acc : PersonalPronoun) :
    Decidable (Licit R person dat acc) := by
  unfold Licit; infer_instance

/-- The morphosyntactic prediction has `R` read agreement person. -/
abbrev Morphosyntactic (R : Clause.Scenario Person → Prop) := Licit R (·.person)

/-- The syntacticosemantic prediction has `R` read referential person. -/
abbrev Syntacticosemantic (R : Clause.Scenario Person → Prop) :=
  Licit R PersonalPronoun.referentialPerson

variable {R : Clause.Scenario Person → Prop} {dat acc : PersonalPronoun}

/-- The two predictions coincide on ordinary pronouns, those denoting exactly the categories
their agreement features realize. -/
theorem morphosyntactic_iff_of_ordinary (hd : dat.IsOrdinary) (hd' : dat.referential.Nonempty)
    (ha : acc.IsOrdinary) (ha' : acc.referential.Nonempty) :
    Morphosyntactic R dat acc ↔ Syntacticosemantic R dat acc := by
  simp [Licit, PersonalPronoun.referentialPerson_eq_person hd hd',
    PersonalPronoun.referentialPerson_eq_person ha ha']

/-- Every restriction reading agreement person treats LEI as *lei*. -/
theorem morphosyntactic_lei_formal :
    (Morphosyntactic R dat lei_formal ↔ Morphosyntactic R dat lei) ∧
      (Morphosyntactic R lei_formal acc ↔ Morphosyntactic R lei acc) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Every restriction reading interpretable person treats LEI as *tu*. -/
theorem syntacticosemantic_lei_formal :
    (Syntacticosemantic R dat lei_formal ↔ Syntacticosemantic R dat tu) ∧
      (Syntacticosemantic R lei_formal acc ↔ Syntacticosemantic R tu acc) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! ### Italian -/

/-- The Italian grammars are Weak for most speakers and Strong for those rejecting 1>2 and 2>1. -/
def grammars : List Grammar := [weakGrammar, strongGrammar]

theorem baseline : ∀ g ∈ grammars,
    Syntacticosemantic (IsLicit g) tu lei ∧ Syntacticosemantic (IsLicit g) lui lei ∧
      ¬ Syntacticosemantic (IsLicit g) lui tu := by
  decide

theorem lei_dative : ∀ g ∈ grammars,
    Morphosyntactic (IsLicit g) lei_formal lei ∧
      Syntacticosemantic (IsLicit g) lei_formal lei := by
  decide

/-- A third person dative over accusative LEI is licensed on agreement person and banned on
interpretable person. -/
theorem lei_accusative : ∀ g ∈ grammars,
    Morphosyntactic (IsLicit g) lui lei_formal ∧
      ¬ Syntacticosemantic (IsLicit g) lui lei_formal := by
  decide

/-- The interaction–satisfaction grammars, read over agreement person, license accusative LEI. -/
theorem deal_licenses_lei : ∀ g ∈ [Deal2024.weak, Deal2024.strong],
    Morphosyntactic (Deal2024.Licit g) lui lei_formal := by
  decide

/-- Feature gluttony, read over agreement person, licenses accusative LEI, since a third person
dative and a third person accusative do not glutton the Weak probe. -/
theorem gluttony_licenses_lei :
    Morphosyntactic (¬ CoonKeine2021.PCCViolation CoonKeine2021.weakProbe false ·) lui
      lei_formal := by
  decide

/-- Under the Fancy Constraint with a third person causee as applied argument, a third person
accusative is licit and second person and LEI are not. -/
theorem fancy_constraint :
    Syntacticosemantic (IsLicit weakGrammar) lui lei ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) lui tu ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) lui lei_formal := by
  decide

/-- Coordinated with a third person, LEI resolves to second person on its interpretable value and
to third on its agreement value. -/
theorem resolved_person :
    lei_formal.referentialPerson.map (· ⊔ .third) = some .second ∧
      lei_formal.person.map (· ⊔ .third) = some .third :=
  ⟨rfl, rfl⟩

theorem first_dative_lei :
    Syntacticosemantic (IsLicit weakGrammar) io lei_formal ∧
      ¬ Syntacticosemantic (IsLicit strongGrammar) io lei_formal := by
  decide

/-! ### Spanish and German -/

/-- USTED as dative over a third person accusative is licit; a third person dative over
accusative USTED is not. -/
theorem usted_accusative :
    Syntacticosemantic (IsLicit weakGrammar) Spanish.Pronouns.usted Spanish.Pronouns.el ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) Spanish.Pronouns.el Spanish.Pronouns.usted := by
  decide

/-- A third person dative over accusative SIE is banned where over third plural *sie* it is
licit. -/
theorem sie_accusative :
    Syntacticosemantic (IsLicit weakGrammar) German.Pronouns.er German.Pronouns.sie_pl ∧
      ¬ Syntacticosemantic (IsLicit weakGrammar) German.Pronouns.er
          German.Pronouns.sie_formal := by
  decide

open CoonKeine2021 in
/-- Under assumed identity with a third plural subject, SIE, entering with its agreement person,
does not glutton the person probe where second plural *ihr* does, and a singular subject gluttons
the number probe against plural SIE. -/
theorem assumed_identity :
    (∀ p ∈ German.Pronouns.sie_formal.person,
      ¬ Gluttonous Goal.personSegments weakProbe [dpPl .third, dpPl p]) ∧
      (∀ p ∈ German.Pronouns.ihr.person,
        Gluttonous Goal.personSegments weakProbe [dpPl .third, dpPl p]) ∧
      Gluttonous Goal.numberSegments (numberProbe weakProbe) [dp .third, dpPl .third] := by
  decide +kernel

/-! ### The data

The clitic-cluster rows, Italian, Spanish and German alike, read as dative–accusative pronoun
pairs and checked against the interpretable valuation over both grammars. -/

section Data

open Examples

/-- The dative and accusative pronouns a row's features name, by digit for the ordinary persons
and by name for the polite pronouns, per language. -/
def pair? (e : Datum) : Option (PersonalPronoun × PersonalPronoun) := do
  let table ← match e.language with
    | "ital1282" => some [("1", io), ("2", tu), ("3", lui), ("LEI", lei_formal)]
    | "stan1288" => some [("3", Spanish.Pronouns.el), ("USTED", Spanish.Pronouns.usted)]
    | "stan1295" => some [("2", German.Pronouns.du), ("3", German.Pronouns.er),
        ("3PL", German.Pronouns.sie_pl), ("SIE", German.Pronouns.sie_formal)]
    | _ => none
  pure (← e.parse? "dative" table, ← e.parse? "accusative" table)

/-- The band the interpretable valuation predicts: accepted where both grammars license the
pair, divided where the Weak grammar licenses what the Strong grammar rejects, the speaker split
over a first person dative above accusative LEI, and rejected where neither licenses it. -/
def predicted (p : PersonalPronoun × PersonalPronoun) : Judgment.Band :=
  if ∀ g ∈ grammars, Syntacticosemantic (IsLicit g) p.1 p.2 then .accepted
  else if Syntacticosemantic (IsLicit weakGrammar) p.1 p.2 then .divided
  else .rejected

/-- Every clitic-cluster judgment lands in the band the interpretable valuation predicts. -/
theorem rows_predicted : ∀ e ∈ Examples.all, e.Fits pair? predicted := by decide

theorem rows_read : Datum.ReadCount pair? Examples.all 16 := by decide

/-- Read over agreement person instead, both grammars license every rejected row whose accusative
is polite, its agreement person differing from its interpretable person: the agreement valuation
misses the paradigm. -/
theorem morphosyntactic_misses : ∀ e ∈ Examples.all, ∀ p ∈ pair? e,
    e.judgment ≠ .acceptable → p.2.person ≠ p.2.referentialPerson →
    ∀ g ∈ grammars, Morphosyntactic (IsLicit g) p.1 p.2 := by
  decide

end Data

end AdamsonZompi2025
