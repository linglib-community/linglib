module

public import Linglib.Data.Examples.MunozPerez2026
public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Linglib.Syntax.Minimalist.Verbal.Applicative
public import Linglib.Syntax.Minimalist.Verbal.LittleV
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Syntax.Person.Features
public import Linglib.Fragments.Romance.Spanish.Clitics
public import Linglib.Fragments.Romance.Spanish.Verbs
import all Init.Data.String.Defs  -- for unfolding `String.intercalate`

/-!
# Muñoz Pérez (2026): Stylistic Applicatives

This file formalizes Muñoz Pérez's analysis of the stylistic applicative of Chilean Spanish. A
marked anticausative with an affected dative surfaces in General Spanish
with the cluster *se me*. Chilean Spanish also has *me le* and *se me le*, with an invariable
*le* that refers to nothing, and the three are synonymous. The alternation is confined to first
and second person singular datives and to predicates that take the anticausative marker.

The paper takes the dative clitic to realize an applicative head and *se* to be an expletive in
the specifier of a Voice head that introduces no argument and has no meaning. A fission rule
splits an applicative head that is [+PART, +SING] into two exponents when the predicate is
inchoative: a clitic with the person and number of the head, and the inflectionless dative *le*.
At PF the Voice projection must be overtly marked by a reflexive clitic, and every head must be
pronounced. The first exponent of a fissioned head is syncretic with a reflexive, so it can mark
Voice while *le* pronounces the applicative head. This is why *se* is optional exactly where
fission applies, and since the three clusters spell out one clause under a meaningless Voice
head, they do not differ in meaning.

## Main declarations

* `Clause`, `Clause.site`, `marked`, `unmarked`: a clause by its Voice head, its verbal heads
  and the bundle of its applicative head, with the site of that head; the clauses of marked and
  unmarked anticausatives.
* `IsFissionApplicable`, `applExponents`: the fission rule and the exponents it gives the
  applicative head.
* `Converges`: the two PF conditions on the clitics of a clause.
* `clusters`: the clitic clusters a clause surfaces with.

## Main results

* `isFissionApplicable_iff`: fission applies to the speaker and the addressee alone.
* `clusters_marked`, `clusters_unmarked`: the typology of realizations. A marked anticausative
  has the marker with a plain dative and, where fission applies, the fissioned dative with and
  without the marker; an unmarked one has the plain dative alone.
* `marker_optional_iff`: the marker can be absent exactly where fission applies.
* `converges_of_fission`, `not_converges_singleton`: fission rescues a clause without the marker
  because the dative is syncretic with the reflexive outside the third person, and an unfissioned
  dative cannot, since it would leave the applicative head unpronounced.
* `anticausative_rows`, `other_rows`: the judgments on the paper's clitic clusters.
* `causer_reading_rows`: the unintentional causer reading arises only from the marked clause.
* `isLicit_me_iff_nos`: no person case constraint separates *me le* from *nos le*.

## Implementation notes

The verbal heads of a marked anticausative are a change and a result state and those of an
unmarked one a change alone, after the structures the paper adopts from Cuervo; the applicative
head merges as low as the structure allows, taking the result state as its complement where there
is one, Cuervo's affected applicative, and the theme otherwise (`Clause.site`);
the context of the fission rule, the change head over the applicative over the state head, is
that the site is affected. The paper leaves the structure of unmarked anticausatives open; all
that matters here is that they lack the result state and a Voice head that asks for a marker.
The optionality of the marker in the syntax, which the paper derives from a principle that lets
an unchecked feature fail, is built into `markers`.
The clauses given to *quejarse* and to impersonal *dar* say only that they are not inchoative.

## TODO

The paper's comparison with the two-flavour Voice of Martin, Schäfer and Kastner is not
formalized.

## References

* [M. C. Cuervo, *Datives at Large* (2003)][cuervo-2003]
* [A. Koontz-Garboden, *Anticausativization* (2009)][koontz-garboden-2009]
* [C. Muñoz Pérez, *Stylistic applicatives: A lens into the nature of anticausative SE*
  (2026)][munoz-perez-2026]
-/

@[expose] public section

namespace MunozPerez2026

open Minimalist Person Spanish.Verbs

/-! ### Clauses -/

/-- A clause as the clitic system sees it. -/
structure Clause where
  /-- The Voice head. -/
  voice : Minimalist.Voice.Head
  /-- The verbal heads below Voice, highest first. -/
  heads : List LittleV
  /-- The bundle of the high applicative head, if the clause has an affected dative. -/
  appl : Option Category

/-- The applicative head takes as its complement the result state where there is one, the
affected applicative of [cuervo-2003] the paper adopts for marked anticausatives, and the theme
otherwise, as under an unmarked anticausative, which lacks the state. -/
def Clause.site (k : Clause) : ApplSite :=
  ⟨k.heads.takeWhile (· != .vBE), k.heads.dropWhile (· != .vBE)⟩

/-- A marked anticausative is a change and its result state under a Voice head that introduces
no argument and asks for a specifier. -/
def marked (a : Option Category) : Clause := ⟨Minimalist.Voice.anticausative, [.vGO, .vBE], a⟩

/-- An unmarked anticausative is a change alone, under a Voice head that asks for nothing. -/
def unmarked (a : Option Category) : Clause :=
  ⟨Minimalist.Voice.middle, [.vGO], a⟩

/-- The applicative of a marked anticausative is affected, between the change and the state; that
of an unmarked one is low, the rule's context failing. -/
theorem site_marked_unmarked (a : Option Category) :
    (marked a).site.Affected ∧ (unmarked a).site.Low := by
  simp [marked, unmarked, Clause.site, ApplSite.Affected, ApplSite.Low]

/-- The Voice head of an anticausative has no meaning, marked or not, so the clitics that spell
a clause out cannot change what it means. -/
theorem not_hasSemantics (a : Option Category) :
    ¬ (marked a).voice.IsThematic ∧ ¬ (unmarked a).voice.IsThematic := by
  simp only [marked, unmarked]; decide

/-! ### The fission rule -/

/-- The bundle condition of the fission rule holds of an applicative head that is
[+PART, +SING]. -/
def IsFissionApplicable (c : Category) : Prop :=
  .participant ∈ c.toFeatures ∧ c.IsSingular

instance : DecidablePred IsFissionApplicable := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The bundle condition singles out the speaker and the addressee, since a third person lacks
[+PART] and a group lacks [+SING]. -/
theorem isFissionApplicable_iff (c : Category) :
    IsFissionApplicable c ↔ c = .speaker ∨ c = .addressee := by
  cases c <;> decide

/-- The dative clitics of a category. The form *se* that a third-person dative takes before an
accusative clitic is left out, no accusative clitic being present. -/
def datives : Category → Finset String :=
  PersonalPronoun.paradigm (Spanish.Clitics.dative.erase Spanish.Clitics.se_dat)

/-- The exponents of the applicative head. It is pronounced as a dative clitic of its category,
and when the head sits between the change and the result state and is [+PART, +SING] it may
instead split into that clitic and the inflectionless dative *le*. -/
def applExponents (k : Clause) : Finset (List String) :=
  match k.appl with
  | none => {[]}
  | some c =>
    (datives c).image ([·]) ∪
      if k.site.Affected ∧ IsFissionApplicable c then
        (datives c).image ([·, Spanish.Clitics.le.form])
      else ∅

/-! ### The conditions at PF -/

/-- A form counts as a reflexive clitic at PF when the reflexive series has it, syncretic
elements being indistinguishable there. -/
def IsReflexiveForm (f : String) : Prop := ∃ p ∈ Spanish.Clitics.reflexive, p.form = f

instance : DecidablePred IsReflexiveForm := fun _ ↦ inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- A Voice head must be marked at PF when it introduces no argument and asks for a
specifier. -/
def RequiresMarker (v : Minimalist.Voice.Head) : Prop := ¬ v.IsThematic ∧ v.HasD

instance : DecidablePred RequiresMarker := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The markers the syntax may supply. A Voice head that asks for a specifier gets a reflexive
or nothing, the feature being free to fail. -/
def markers (k : Clause) : Finset (Option String) :=
  if RequiresMarker k.voice then {none, some Spanish.Clitics.se.form} else {none}

/-- The clitics of a clause converge when Voice is marked by a reflexive clitic and the
applicative head is pronounced. Without a marker from the syntax, an exponent of the applicative
head that has the form of a reflexive can mark Voice, provided another exponent is left to
pronounce the head. -/
def Converges (marker : Option String) (appl : List String) : Prop :=
  marker.isSome ∨ ∃ f ∈ appl, IsReflexiveForm f ∧ appl.erase f ≠ []

instance (marker : Option String) (appl : List String) : Decidable (Converges marker appl) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The clitic clusters a clause surfaces with. -/
def clusters (k : Clause) : Finset (List String) :=
  ((markers k ×ˢ applExponents k).filter
    fun x ↦ RequiresMarker k.voice → Converges x.1 x.2).image fun x ↦ x.1.toList ++ x.2

/-! ### The typology of realizations -/

/-- A marked anticausative always has the marker with the plain dative. Where fission applies it
also has the fissioned dative, with the marker and without it. -/
theorem clusters_marked (c : Category) :
    clusters (marked (some c)) =
      (datives c).image (["se", ·]) ∪
        if IsFissionApplicable c then
          (datives c).image (["se", ·, "le"]) ∪ (datives c).image ([·, "le"])
        else ∅ := by
  cases c <;> decide +kernel

/-- An unmarked anticausative has the plain dative alone. -/
theorem clusters_unmarked (c : Category) :
    clusters (unmarked (some c)) = (datives c).image ([·]) := by
  cases c <;> decide +kernel

/-- Without a dative, a marked anticausative has the marker and an unmarked one has nothing. -/
theorem clusters_none : clusters (marked none) = {["se"]} ∧ clusters (unmarked none) = {[]} := by
  decide +kernel

/-- The three clusters of a first person singular dative. -/
theorem clusters_marked_speaker :
    clusters (marked (some .speaker)) = {["se", "me"], ["se", "me", "le"], ["me", "le"]} := by
  decide +kernel

/-- The marker can be absent from a marked anticausative exactly where fission applies. -/
theorem marker_optional_iff (c : Category) :
    (∃ l ∈ clusters (marked (some c)), "se" ∉ l) ↔ IsFissionApplicable c := by
  cases c <;> decide +kernel

/-! ### Why fission rescues the clause -/

/-- Outside the third person every dative clitic is a reflexive form, by the syncretism of the
two series. -/
theorem isReflexiveForm_of_mem_datives {c : Category} (hc : c.person ≠ .third) {f : String}
    (hf : f ∈ datives c) : IsReflexiveForm f := by
  have hf' := PersonalPronoun.paradigm_mono (Finset.erase_subset _ _) c hf
  rw [(Spanish.Clitics.paradigm_dative_eq_paradigm_reflexive_iff c).mpr hc] at hf'
  obtain ⟨p, hp, -, rfl⟩ := ReflexivePronoun.mem_paradigm.mp hf'
  exact ⟨p, hp, rfl⟩

/-- A fissioned head converges without a marker, since its first exponent marks Voice and *le*
pronounces the head. -/
theorem converges_of_fission {c : Category} (hc : IsFissionApplicable c) {f : String}
    (hf : f ∈ datives c) : Converges none [f, Spanish.Clitics.le.form] := by
  have hne : c.person ≠ .third := by
    rcases (isFissionApplicable_iff c).mp hc with rfl | rfl <;> decide
  exact .inr ⟨f, by simp, isReflexiveForm_of_mem_datives hne hf, by simp⟩

/-- An unfissioned dative does not converge without a marker, whatever its form. Taken as the
marker of Voice it leaves the applicative head unpronounced. -/
theorem not_converges_singleton (f : String) : ¬ Converges none [f] := by
  simp [Converges]

/-- The second exponent *le* is not a reflexive form, so the marking comes from the first. -/
theorem not_isReflexiveForm_le : ¬ IsReflexiveForm Spanish.Clitics.le.form := by
  decide +kernel

/-- Syncretism with the reflexive does not suffice for a stylistic clitic. The first person
plural *nos* is syncretic, and fission still skips it for want of [+SING]. -/
theorem syncretic_not_isFissionApplicable :
    (∀ f ∈ datives .speakerOthers, IsReflexiveForm f) ∧
      ¬ IsFissionApplicable .speakerOthers :=
  ⟨fun _ hf ↦ isReflexiveForm_of_mem_datives (by decide) hf, by decide⟩

/-! ### The examples -/

/-- The verb of an example, from the Fragment. -/
def verb? (e : Datum) : Option SpanishVerbEntry :=
  (e.feature? "verb").bind fun f ↦ allVerbs.find? (·.form = f)

/-- The bundle of the dative of an example, `none` where it has no dative. -/
def appl? (e : Datum) : Option (Option Category) :=
  e.parse? "dative" [("none", none), ("1SG", some .speaker), ("2SG", some .addressee),
    ("3SG", some .other), ("1PL", some .speakerOthers), ("3PL", some .others)]

/-- The clauses a verb's intransitive has, by its marking. -/
def clauses (a : Option Category) : AnticausativeMarking → List Clause
  | .marked => [marked a]
  | .unmarked => [unmarked a]
  | .optional => [marked a, unmarked a]

/-- An anticausative example is accepted exactly when its clitic cluster is one that a clause of
its verb surfaces with. This covers the three synonymous clusters, the restriction to first and
second person singular datives, the invariability of *le*, the ban on stylistic *le* with
unmarked anticausatives, and the marking of anticausatives without a dative. -/
theorem anticausative_rows : ∀ e ∈ Examples.all,
    e.feature? "construction" = some "anticausative" →
    ∃ v ∈ verb? e, ∃ a ∈ appl? e, ∃ s ∈ e.feature? "cluster",
      (.marginal ≤ e.judgment ↔
        ∃ m ∈ v.anticausativeMarking, ∃ k ∈ clauses a m, ∃ l ∈ clusters k,
          " ".intercalate l = s) := by
  decide +kernel

/-- The clause of an example that is not anticausative. *Quejarse* has an external argument and
impersonal *dar* is an activity under an impersonal Voice head. -/
def otherClause? (e : Datum) : Option Clause :=
  (appl? e).bind fun a ↦ e.parse? "construction"
    [("inherent", ⟨Minimalist.Voice.agentive, [.vDO], a⟩),
      ("impersonal", ⟨Minimalist.Voice.impersonal, [.vDO], a⟩)]

/-- Where *se* has another source and the clause is not inchoative, the applicative head has its
plain exponent alone, so stylistic *le* is out. -/
theorem other_rows : ∀ e ∈ Examples.all,
    e.feature? "construction" = some "inherent" ∨
      e.feature? "construction" = some "impersonal" →
    ∃ k ∈ otherClause? e, ∃ s ∈ e.feature? "cluster",
      (.marginal ≤ e.judgment ↔
        ∃ l ∈ applExponents k, " ".intercalate ("se" :: l) = s) := by
  decide +kernel

/-- An example with the unintentional causer reading has a cluster of the marked clause. The
cluster *me le* of *hervir* has the reading although it lacks *se*, since only the marked clause
fissions. -/
theorem causer_reading_rows : ∀ e ∈ Examples.all,
    e.readings.lookup "unintentional causer" = some .acceptable →
    ∃ a ∈ appl? e, ∃ s ∈ e.feature? "cluster",
      ∃ l ∈ clusters (marked a), " ".intercalate l = s := by
  decide +kernel

/-! ### Against a constraint on clitic clusters -/

/-- A person case constraint sees the persons of the two clitics, and *me* and *nos* have the
same person, so no such constraint separates *me le* from *nos le*. -/
theorem isLicit_me_iff_nos (g : PCC.Grammar) :
    (∃ io ∈ Spanish.Clitics.le.person, ∃ do_ ∈ Spanish.Clitics.me.person,
        PCC.IsLicit g ⟨io, do_⟩) ↔
      ∃ io ∈ Spanish.Clitics.le.person, ∃ do_ ∈ Spanish.Clitics.nos.person,
        PCC.IsLicit g ⟨io, do_⟩ :=
  Iff.rfl

/-- The weak constraint bans a third-person dative over a first-person accusative, as in the
ditransitive examples, so it would ban stylistic *me le* as well. -/
theorem weak_pcc_bans :
    ∃ io ∈ Spanish.Clitics.le.person, ∃ do_ ∈ Spanish.Clitics.me.person,
      ¬ PCC.IsLicit PCC.weakGrammar ⟨io, do_⟩ := by
  decide

/-- The fission rule does separate the two. -/
theorem fission_separates :
    IsFissionApplicable .speaker ∧ ¬ IsFissionApplicable .speakerOthers := by
  decide

/-! ### Against a null reflexive

On the reflexivization analysis of [koontz-garboden-2009] extended with a null reflexive, every
alternating verb has a reflexive in its anticausative, overt or silent, and an overt one is
always possible. -/

/-- The null-reflexive extension predicts that if a verb alternates, its intransitive can take
the clitic. -/
def seMarkedIfAlternating (v : SpanishVerbEntry) : Prop :=
  v.Alternates → v.anticausativeMarking ≠ some .unmarked

/-- *mejorar* alternates and rejects the clitic, against the prediction. -/
theorem not_seMarkedIfAlternating_mejorar : ¬ seMarkedIfAlternating mejorar := by
  unfold seMarkedIfAlternating; decide

end MunozPerez2026
