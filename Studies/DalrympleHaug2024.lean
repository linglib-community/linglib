module

public import Linglib.Data.Examples.DalrympleHaug2024
public import Linglib.Semantics.Plurality.Reciprocal.Scope
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.Wan.Reciprocals
public import Studies.Landau2015
public import Studies.Rakosi2020

/-!
# Dalrymple and Haug, constraints on reciprocal scope (2024)

A reciprocal in a complement clause has a narrow-scope we-reading and a wide-scope I-reading,
and Dalrymple and Haug survey constructions in which properties of its local antecedent, the
embedded pronoun rather than the matrix subject, fix the scope. On the quantificational
analysis of Heim, Lasnik and May the reciprocal contains a distributive quantifier that raises
to the scope position and binds the local antecedent in situ; on the relational analysis of
Haug and Dalrymple it is a pronoun anaphoric on the local antecedent, so that under wide scope
the local antecedent is bound by the matrix subject and interpreted with the reciprocal in the
matrix clause. Bound and nonbound antecedents, collective conjuncts and control constructions
come out alike on both analyses; an explicit distributor on the antecedent and a logophoric
antecedent separate them, and only the relational analysis fits the data.

We state each analysis by its two commitments, where it interprets the local antecedent under
each reading and whether the reciprocal distributes, derive the readings each admits for each
construction, and check them against the paper's judgments.

## Implementation notes

* A construction is represented by its local antecedent alone: the denotation its form or
  predicate forces, whether it is a logophor, the locus of an explicit distributor, and the
  number of the matrix argument. Partial control forces no denotation, since PRO may properly
  include the controller or coincide with it.
* A simple sentence has only the in-situ reading, so (18b)–(20) are the narrow reading with the
  distributor at the low locus.

## TODO

* (17) is analysed, with the paper, as exhaustive control, but `Landau2015.derivedControlTier`
  puts *intend* (and *decide* of (14)) on the partial-control tier; a semantics for partial
  control would decide the case.
* (25) is headed wide scope but read by the paper as a crossed reading; a crossed value in
  `Scope` would make it a row and reach the substrate's `ScopeReading.crossed`.

## References

* [M. Dalrymple and D. T. T. Haug, *Constraints on reciprocal scope* (2024)][dalrymple-haug-2024]
* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
* [I. Heim, H. Lasnik and R. May, *Reciprocity and plurality* (1991)][heim-lasnik-may-1991]
* [J. Higginbotham, *Reciprocal interpretation* (1980)][higginbotham-1980]
* [T. Nishigauchi, *Syntax of reciprocals in Japanese* (1992)][nishigauchi-1992]
* [G. Rákosi, *Reciprocal anaphors in singular constructions in Hungarian*
  (2020)][rakosi-2020]
* [W. Tay, K. New, M. Dalrymple and D. Haug, *Reciprocal scope in Mandarin*
  (2021)][tay-new-dalrymple-haug-2021]
* [I. Landau, *Elements of control* (2000)][landau-2000]
* [I. Landau, *A two-tiered theory of control* (2015)][landau-2015]
* [K. Safir, *One true anaphor* (2014)][safir-2014]
* [L. Champollion, *Overt distributivity in algebraic event semantics*
  (2016)][champollion-2016]
-/

@[expose] public section

namespace DalrympleHaug2024

open Reciprocal

/-! ### Analyses and local antecedents -/

/-- What the local antecedent denotes under a reading ((5), (8)). -/
inductive Grain where
  /-- An individual, as a bound variable (`=`). -/
  | individual
  /-- The plurality, under group identity (`∪`) with the matrix subject. -/
  | plurality
  deriving DecidableEq, Repr

/-- The denotation of the local antecedent under a scope reading, read off the antecedent
    relation of its cell, bound under wide scope and group-identical under narrow scope on both
    analyses ((4), (6)–(8)). -/
def antecedentGrain (r : Scope) : Grain :=
  match r.reading.antecedentRel with
  | .binding => .individual
  | .groupIdentity | .reciprocity => .plurality

@[simp] theorem antecedentGrain_narrow : antecedentGrain .narrow = .plurality := rfl

@[simp] theorem antecedentGrain_wide : antecedentGrain .wide = .individual := rfl

/-- The denotation a pronoun's number forces: a singular pronoun denotes an individual and so
    must be bound, a plural pronoun may be bound or group-identical ((10b)). -/
def Grain.ofNumber? : Number → Option Grain
  | .singular => some .individual
  | _ => none

/-- The local antecedent of a reciprocal in a complement clause, by the properties the paper
    surveys. -/
structure Antecedent where
  /-- The denotation its form or its predicate forces, if any. -/
  grain : Option Grain := none
  /-- A logophor, interpreted inside the report (§6). -/
  logophoric : Bool := false
  /-- The locus of an explicit distributor on it, if any (§5). -/
  distributor : Option Locus := none
  /-- Whether the matrix argument it is anaphoric to is a plurality. -/
  matrixPlural : Bool := true
  deriving Repr

/-- A pronoun of number `n` as local antecedent. -/
def Antecedent.ofNumber (n : Option Number) : Antecedent := { grain := n.bind Grain.ofNumber? }

/-- A logophoric pronoun as local antecedent: its number, interpreted inside the report. -/
def Antecedent.ofLogophor (p : LogophoricPronoun) : Antecedent :=
  { Antecedent.ofNumber p.number with logophoric := true }

/-- An analysis of reciprocal scope, by what it commits the local antecedent to under each
    reading. -/
structure Analysis where
  /-- Where the local antecedent is interpreted under each reading. -/
  antecedentLocus : Scope → Locus
  /-- Whether the reciprocal contributes a distributive quantifier at the reading's locus. -/
  distributes : Bool

/-- On the quantificational analysis the quantifier part of the reciprocal raises to the
    reading's locus and binds the local antecedent in situ ((2), (4)). -/
def quantificational : Analysis := { antecedentLocus := fun _ ↦ .low, distributes := true }

/-- On the relational analysis the reciprocal is a pronoun anaphoric on the local antecedent,
    which is therefore interpreted where the reciprocal is ((3), (6)–(9)). -/
def relational : Analysis := { antecedentLocus := fun r ↦ r.reading.locus, distributes := false }

/-- Reading `r` is available for the local antecedent `a` on analysis `A`: `r` gives the local
    antecedent the denotation its form forces, a logophor stays inside the report, a
    distributing reciprocal scopes below any explicit distributor, and a wide-scope reciprocal
    takes the matrix argument as its plural antecedent. -/
def Available (A : Analysis) (a : Antecedent) (r : Scope) : Prop :=
  (∀ g ∈ a.grain, antecedentGrain r = g) ∧ (a.logophoric → A.antecedentLocus r = .low) ∧
    (A.distributes → ∀ d ∈ a.distributor, r.reading.locus < d) ∧ (r = .wide → a.matrixPlural)

instance (A : Analysis) (a : Antecedent) (r : Scope) : Decidable (Available A a r) := by
  unfold Available; infer_instance

/-- The label of a reading in `Data/Examples/DalrympleHaug2024.json`. -/
def label : Scope → String
  | .narrow => "narrow"
  | .wide => "wide"

/-- The paper records reading `r` of example `e` as available. -/
def Attested (e : Datum) (r : Scope) : Prop :=
  e.readings.lookup (label r) = some .acceptable

instance (e : Datum) (r : Scope) : Decidable (Attested e r) := by
  unfold Attested; infer_instance

/-- Every reading the paper records for `e` is available on `A` with local antecedent `a`. -/
def Covers (A : Analysis) (a : Antecedent) (e : Datum) : Prop :=
  ∀ r, Attested e r → Available A a r

instance (A : Analysis) (a : Antecedent) (e : Datum) : Decidable (Covers A a e) := by
  unfold Covers; infer_instance

/-- A reading is available on `A` with local antecedent `a` exactly when the paper records it
    for `e`. -/
def Fits (A : Analysis) (a : Antecedent) (e : Datum) : Prop :=
  ∀ r, Available A a r ↔ Attested e r

instance (A : Analysis) (a : Antecedent) (e : Datum) : Decidable (Fits A a e) := by
  unfold Fits; infer_instance

/-- A simple sentence has only the in-situ reading, and is acceptable on `A` exactly when that
    reading is available. -/
def FitsSimple (A : Analysis) (a : Antecedent) (e : Datum) : Prop :=
  Available A a .narrow ↔ e.judgment = .acceptable

instance (A : Analysis) (a : Antecedent) (e : Datum) :
    Decidable (FitsSimple A a e) := by
  unfold FitsSimple; infer_instance

/-! ### Where the analyses agree -/

/-- Without an explicit distributor or a logophoric antecedent the readings do not depend on
    the analysis: the constraints of §§2–4 are equally predicted by both. -/
theorem available_iff_of_none {A B : Analysis} {a : Antecedent} (hd : a.distributor = none)
    (hl : a.logophoric = false) (r : Scope) : Available A a r ↔ Available B a r := by
  simp [Available, hd, hl]

theorem fits_iff_of_none {A B : Analysis} {a : Antecedent} (hd : a.distributor = none)
    (hl : a.logophoric = false) (e : Datum) : Fits A a e ↔ Fits B a e :=
  forall_congr' fun r ↦ iff_congr (available_iff_of_none hd hl r) Iff.rfl

theorem covers_iff_of_none {A B : Analysis} {a : Antecedent} (hd : a.distributor = none)
    (hl : a.logophoric = false) (e : Datum) : Covers A a e ↔ Covers B a e :=
  forall_congr' fun r ↦ imp_congr Iff.rfl (available_iff_of_none hd hl r)

/-- Wide scope binds the local antecedent, so a form that must denote the plurality has narrow
    scope only ((11), (12)). -/
theorem narrow_of_plurality {A : Analysis} {a : Antecedent} (h : a.grain = some .plurality)
    {r : Scope} (hr : Available A a r) : r = .narrow := by
  cases r <;> simp_all [Available]

/-- Narrow scope makes the local antecedent the plurality, so a form that must denote an
    individual has wide scope only ((10)). -/
theorem wide_of_individual {A : Analysis} {a : Antecedent} (h : a.grain = some .individual)
    {r : Scope} (hr : Available A a r) : r = .wide := by
  cases r <;> simp_all [Available]

/-! ### Bound and nonbound antecedents (§2) -/

/-- The Hungarian complement subject, a null pronoun whose number is the agreement on its verb,
    Rákosi's bound-variable construction ((10)), his (17). -/
def hungarian : Antecedent :=
  .ofNumber <| (Rakosi2020.verbAgr? Rakosi2020.Examples.ex_17).map Prod.snd

/-- A singular null pronoun must be bound, so (10) has wide scope only on every analysis. -/
theorem hungarian_fits (A : Analysis) : Fits A hungarian Examples.ex_10 :=
  (fits_iff_of_none (B := relational) rfl rfl _).mpr (by decide)

/-- The plural reflexive *zibun-tati*, which resists a bound reading and takes group identity
    (Nishigauchi), so denotes the plurality ((11)). -/
def japanese : Antecedent := { grain := some .plurality }

/-- A plural reflexive that cannot be bound leaves narrow scope only on every analysis. -/
theorem japanese_fits (A : Analysis) : Fits A japanese Examples.ex_11 :=
  (fits_iff_of_none (B := relational) rfl rfl _).mpr (by decide)

/-! ### Collectivity (§3) -/

/-- The subject of a coordinated collective predicate, *meet at the tennis court*, which needs
    the plurality (Tay, New, Dalrymple and Haug) ((12)). -/
def collectiveConjunct : Antecedent := { grain := some .plurality }

/-- A bound local antecedent offers no plurality to the collective conjunct, so (12) has narrow
    scope only on every analysis. -/
theorem collectiveConjunct_fits (A : Analysis) : Fits A collectiveConjunct Examples.ex_12 :=
  (fits_iff_of_none (B := relational) rfl rfl _).mpr (by decide)

/-! ### Control (§4) -/

/-- PRO as local antecedent: a collectively read matrix predicate makes PRO the group, under
    exhaustive control with a distributive reading PRO is the individual controller, and under
    partial control PRO is semantically plural and may properly include the controller, so no
    denotation is forced. -/
def pro (exhaustive collective matrixPlural : Bool) : Antecedent :=
  { grain := if collective then some .plurality else if exhaustive then some .individual else none
    matrixPlural }

open English English.Verbs Landau2015 in
/-- Landau's tiers on the paper's control verbs: *want* of (13) and (15) selects an attitude
    complement and admits partial control, *try* and *manage* of (16) force exhaustive control,
    and *intend* of (17) and *decide* of (14) fall with *want*, although the paper's argument
    from (17) assumes exhaustive control. -/
theorem control_tiers :
    derivedControlTier want.toVerb = some .logophoric ∧
      derivedControlTier try_.toVerb = some .predicative ∧
      derivedControlTier manage.toVerb = some .predicative ∧
      derivedControlTier intend.toVerb = some .logophoric ∧
      derivedControlTier decide_.toVerb = some .logophoric :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- PRO of a partial-control verb with a plural matrix subject ((13)). -/
def partialPlural : Antecedent := pro false false true

/-- A partial-control verb makes a narrow reading available on every analysis, the paper's §4
    generalization applied to *want* ((13)). -/
theorem partial_narrow (A : Analysis) : Available A partialPlural .narrow := by
  simp [Available, partialPlural, pro]

/-- The wide-only judgment recorded for (13) since Higginbotham is therefore not what any
    analysis predicts for a partial-control verb. -/
theorem not_fits_received_judgment (A : Analysis) : ¬ Fits A partialPlural Examples.ex_13 :=
  fun h ↦ absurd ((h .narrow).mp (partial_narrow A)) (by decide)

/-- A collectively read matrix predicate leaves narrow scope only, whatever the control type,
    the first of the two readings Heim, Lasnik and May attribute to (14). -/
theorem collective_narrow (A : Analysis) (exhaustive : Bool) (r : Scope) :
    Available A (pro exhaustive true true) r ↔ r = .narrow := by
  cases r <;> simp [Available, pro]

/-- PRO of an exhaustive-control verb whose plural matrix subject is read distributively, the
    second reading of (14) and the paper's reading of (17), whose adjunct forces the
    distributive reading. -/
def exhaustiveDistributive : Antecedent := pro true false true

/-- Under exhaustive control a distributively read matrix subject leaves wide scope only. -/
theorem exhaustiveDistributive_wide (A : Analysis) (r : Scope) :
    Available A exhaustiveDistributive r ↔ r = .wide := by
  cases r <;> simp [Available, exhaustiveDistributive, pro]

/-- The paper's construal of (17) as exhaustive control fits on every analysis. -/
theorem intend_fits (A : Analysis) : Fits A exhaustiveDistributive Examples.ex_17 :=
  (fits_iff_of_none (B := relational) rfl rfl _).mpr (by decide)

/-- PRO of a partial-control verb with a singular matrix subject, a plurality including the
    subject that the reciprocal takes as antecedent in situ ((15)). -/
def partialSingular : Antecedent := pro false false false

/-- Every analysis fits (15): narrow scope, and no wide scope for want of a plural matrix
    antecedent. -/
theorem partialSingular_fits (A : Analysis) :
    Fits A partialSingular Examples.ex_15a ∧ Fits A partialSingular Examples.ex_15b :=
  ⟨(fits_iff_of_none (B := relational) rfl rfl _).mpr (by decide),
    (fits_iff_of_none (B := relational) rfl rfl _).mpr (by decide)⟩

/-- PRO of an exhaustive-control verb with a singular matrix subject, the subject itself
    ((16)). -/
def exhaustiveSingular : Antecedent := pro true false false

/-- An individual PRO cannot antecede a narrow reciprocal and a singular matrix subject cannot
    antecede a wide one, so (16) has no reading on any analysis. -/
theorem not_available_exhaustiveSingular (A : Analysis) (r : Scope) :
    ¬ Available A exhaustiveSingular r := by
  cases r <;> simp [Available, exhaustiveSingular, pro]

/-- Every analysis fits the ungrammaticality of (16). -/
theorem exhaustiveSingular_fits (A : Analysis) :
    Fits A exhaustiveSingular Examples.ex_16a ∧ Fits A exhaustiveSingular Examples.ex_16b := by
  constructor <;> intro r <;>
    simp [Attested, Examples.ex_16a, Examples.ex_16b, not_available_exhaustiveSingular]

/-! ### Distributive operators (§5) -/

/-- The plural pronoun *they* as local antecedent ((1)). -/
def plural : Antecedent := .ofNumber English.Pronouns.they.number

/-- (1) is ambiguous on every analysis. -/
theorem plural_fits (A : Analysis) : Fits A plural Examples.ex_1 :=
  (fits_iff_of_none (B := relational) rfl rfl _).mpr (by decide)

/-- The plural pronoun with an explicit distributor at locus `d`, *they each*, *each of them*,
    *neither of them* ((18)–(20), (24)–(26)). -/
def distributed (d : Locus) : Antecedent := { plural with distributor := some d }

/-- A distributing reciprocal cannot scope at or above an explicit distributor, so a matrix
    distributor leaves narrow scope only, the judgment of Heim, Lasnik and May on (18a) derived
    from their analysis. -/
theorem narrow_of_distributes_high {A : Analysis} (hA : A.distributes) {a : Antecedent}
    (hd : a.distributor = some .high) {r : Scope} (h : Available A a r) : r = .narrow := by
  cases r <;> simp_all [Available]

/-- A distributor in the clause of a distributing reciprocal leaves no reading, the
    ungrammaticality of (18b), and of (24)–(25), on the quantificational analysis. -/
theorem not_available_of_distributes_low {A : Analysis} (hA : A.distributes) {a : Antecedent}
    (hd : a.distributor = some .low) (r : Scope) : ¬ Available A a r := by
  cases r <;> simp_all [Available]

/-- A pronominal reciprocal is blind to explicit distributors, since it accesses the group
    denoted by the antecedent even when the antecedent is distributed on, so its readings are
    those of the undistributed antecedent ((27)). -/
theorem available_iff_of_not_distributes {A : Analysis} (hA : A.distributes = false)
    (a : Antecedent) (r : Scope) :
    Available A a r ↔ Available A { a with distributor := none } r := by
  simp [Available, hA]

/-- The quantificational analysis reproduces the judgments of Heim, Lasnik and May on (18). -/
theorem hlm_judgments :
    Fits quantificational (distributed .high) Examples.ex_18a ∧
      FitsSimple quantificational (distributed .low) Examples.ex_18b := by
  decide

/-- Simple sentences with a distributor on the reciprocal's antecedent are attested, admitted
    by the relational analysis and excluded by the quantificational one ((19)–(20)). -/
theorem simple_distributors :
    (FitsSimple relational (distributed .low) Examples.ex_19a ∧
        FitsSimple relational (distributed .low) Examples.ex_19b ∧
        FitsSimple relational (distributed .low) Examples.ex_20a ∧
        FitsSimple relational (distributed .low) Examples.ex_20b) ∧
      ¬ FitsSimple quantificational (distributed .low) Examples.ex_19a ∧
        ¬ FitsSimple quantificational (distributed .low) Examples.ex_19b ∧
        ¬ FitsSimple quantificational (distributed .low) Examples.ex_20a ∧
        ¬ FitsSimple quantificational (distributed .low) Examples.ex_20b := by
  decide

/-- Narrow scope is attested with the distributor in the complement clause and wide scope with
    a matrix distributor, which the relational analysis covers and the quantificational
    analysis does not ((24), (26)). -/
theorem corpus_distributors :
    (Covers relational (distributed .low) Examples.ex_24a ∧
        Covers relational (distributed .low) Examples.ex_24b ∧
        Covers relational (distributed .high) Examples.ex_26a ∧
        Covers relational (distributed .high) Examples.ex_26b) ∧
      ¬ Covers quantificational (distributed .low) Examples.ex_24a ∧
        ¬ Covers quantificational (distributed .low) Examples.ex_24b ∧
        ¬ Covers quantificational (distributed .high) Examples.ex_26a ∧
        ¬ Covers quantificational (distributed .high) Examples.ex_26b := by
  decide

/-! ### Logophoricity (§6) -/

/-- The Wan plural logophor *mɔ̄* as local antecedent, which can itself be bound, as (31)
    shows, but cannot leave the report with the reciprocal ((28)). -/
def logophor : Antecedent := .ofLogophor Wan.Reciprocals.logPl

/-- The ordinary plural pronoun *à̰* as local antecedent ((32)). -/
def ordinary : Antecedent := .ofNumber Wan.Reciprocals.ordinaryPl.number

/-- On an analysis that interprets the local antecedent where the reciprocal is, a logophoric
    antecedent leaves narrow scope only, since under wide scope the reciprocal would drag it
    out of the report ((29)). -/
theorem narrow_of_logophoric {A : Analysis} (hA : ∀ r, A.antecedentLocus r = r.reading.locus)
    {a : Antecedent} (ha : a.logophoric) {r : Scope} (h : Available A a r) :
    r = .narrow := by
  cases r <;> simp_all [Available]

/-- An analysis that binds the local antecedent in situ is blind to a logophoric antecedent,
    since logophoricity constrains only where the antecedent is interpreted, so its readings
    for a logophor are those for the ordinary pronoun ((30)). -/
theorem available_iff_of_in_situ {A : Analysis} (hA : ∀ r, A.antecedentLocus r = .low)
    (a : Antecedent) (r : Scope) :
    Available A a r ↔ Available A { a with logophoric := false } r := by
  simp [Available, hA]

/-- Only the relational analysis fits (28). -/
theorem logophor_fits :
    Fits relational logophor Examples.ex_28 ∧ ¬ Fits quantificational logophor Examples.ex_28 := by
  decide

/-- With the ordinary pronoun the wide reading of (32) is available on every analysis. -/
theorem ordinary_covers (A : Analysis) : Covers A ordinary Examples.ex_32 :=
  (covers_iff_of_none (B := relational) rfl rfl _).mpr (by decide)

end DalrympleHaug2024
