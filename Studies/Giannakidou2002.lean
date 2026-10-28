module

public import Linglib.Semantics.Aspect.SubintervalProperty
public import Linglib.Semantics.Polarity.Licensing
public import Studies.Karttunen1974
public import Linglib.Fragments.English.TemporalConnectives
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Fragments.Greek.StandardModern.PolarityItems
public import Linglib.Fragments.Icelandic.PolarityItems
public import Linglib.Fragments.Dutch.PolarityItems
public import Linglib.Fragments.Greek.StandardModern.TemporalConnectives
public import Linglib.Fragments.Icelandic.TemporalConnectives
public import Linglib.Fragments.Dutch.TemporalConnectives
public import Linglib.Data.Examples.Giannakidou2002
public import Linglib.Data.Examples.Gloss

/-!
# Giannakidou (2002): UNTIL, Aspect, and Negation

Giannakidou argues for Karttunen's two *until*s against the one-*until* analysis of Mittwoch
and de Swart, on which negation is an aspectual stativizer. Durative UNTIL asks its description
to hold at every subinterval of an interval ending at the until time, which [an imperfective,
progressive or perfect clause supplies, and a perfective one only for a
state](##admitsDurative_iff). So Greek, which marks aspect overtly, lets *mexri* combine with
imperfectives and not with a perfective achievement, negated or not, where the polarity item
*para monon* stands in. Under negation the analyses part ways: [the wide-scope reading holds when
nothing P-like ever happens](##wideScope_of_forall_not), whereas [eventive UNTIL is Karttunen's
*not until* with the actualization his presupposition supplies](##eventiveUntil_iff). The
paper's Greek, English, Icelandic and Dutch judgments [follow from the aspect of the main clause
and the fragment entries of the connectives and their polarity items](##rows_predicted), and its
stativity diagnostics [from homogeneity with negation playing no role](##diagnostics_predicted).

## Implementation notes

* The form of a main clause is a viewpoint over a predicate of events (`AspectForm.view`). The
  imperfective and the progressive put the reference interval within an event's run time, the
  perfective and the English simple past, which the paper takes to default to the perfective, put
  the run time within the reference interval, and the perfect is the perfect of the perfective. A
  stative predicate has the subinterval property, and an eventive one holds of a single event, as
  the paper's achievements and accomplishments with a definite subject do.
* Durative UNTIL is the durative reading `Aspect.durative` at a nondegenerate span ending at the
  until time, which keeps a single event from filling it at both endpoints. A clause is
  homogeneous when durative UNTIL holds of its description in some model (`AdmitsDurative`), and a
  form is stative when its clauses are homogeneous whatever their predicate (`StativeForm`). Each
  is decided through its characterization.
* The connective of a glossed row is read off its gloss line (`Data/Examples/Gloss.lean`): a
  wordform, or two adjacent ones, spelling the declared form of a fragment entry. The
  `connective` column remains only on the unglossed rows.
* The relation of each connective is read off its fragment entry. Which words are punctual
  *until*s, Greek *para monon*, Icelandic *fyrr en* and Dutch *pas*, is the paper's
  classification (`Connective.Punctual`). A row names the context the connective sits under, and
  whether that context admits the connective's polarity item is the library's licensing theory
  applied to the item's fragment entry (`PolarityItem.Licenser.Admits`).
* Giannakidou licenses *para monon* by antiveridical triggers only. The library licenses by
  Zwarts's strengths of negation, and *para monon*'s anti-additive licensor draws her line through
  the paper's contexts: negation and *xoris* 'without' carry anti-additivity, *amfivalo* 'I doubt'
  and the rhetorical question do not.
* The oddity of *Nancy didn't get married until she died* and of its Greek counterpart, which the
  actualization entailment explains, is pragmatic and is left in prose.

## TODO

* The preposing and continuation tests are read off `StativeForm`. Tying them to the entailments
  of the readings, `wideScope_of_forall_not` and `eventiveUntil_actualization`, needs rows that
  carry models.
* The English progressive lacks the wide-scope reading in (79), which the paper leaves open.
  `StativeForm` counts the progressive stative, and no row tests it.
* Antiveridicality is not a property the library states of an operator, so where it and
  anti-additivity part ways is not asked.
* English *until* survives in the rhetorical question of (42), which the paper credits to the
  question's negative implicature. The English entry's anti-additive licensor excludes questions
  and the library has no licensing by implicature, so the English row is not encoded.

## References

* [giannakidou-2002]
* [giannakidou-1998]
* [zwarts-1998]
* [karttunen-1974]
* [mittwoch-1977]
* [de-swart-1996]
-/

@[expose] public section

namespace Giannakidou2002

open Event (τ)

open Aspect Tense Karttunen1974 Heinamaki1974
open PolarityItem (LicensingContext)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### Durative UNTIL and homogeneity -/

/-- Durative UNTIL holds when the description holds throughout a nondegenerate interval ending at
the until time, at every one of its subintervals. -/
def durativeUntil (p : W → Set (NonemptyInterval T)) (w : W) (t' : T) : Prop :=
  ∃ i ∈ durative p w, i.fst < i.snd ∧ i.snd = t'

theorem durativeUntil_iff_of_isLowerSet {p : W → Set (NonemptyInterval T)} {w : W}
    (hp : IsLowerSet (p w)) (t' : T) :
    durativeUntil p w t' ↔ ∃ i ∈ p w, i.fst < i.snd ∧ i.snd = t' := by
  simp only [durativeUntil, durative_eq_of_isLowerSet hp]

theorem not_durativeUntil_prfv {P : W → E → Prop} {w : W}
    (hP : ∀ e e', P w e → P w e' → e = e') (t' : T) : ¬ durativeUntil (PRFV P) w t' := by
  rintro ⟨i, h, hi, -⟩
  obtain ⟨e₁, h₁, he₁⟩ := h (show NonemptyInterval.pure i.fst ∈ Set.Iic i from
    NonemptyInterval.le_def.2 ⟨le_rfl, i.fst_le_snd⟩)
  obtain ⟨e₂, h₂, he₂⟩ := h (show NonemptyInterval.pure i.snd ∈ Set.Iic i from
    NonemptyInterval.le_def.2 ⟨i.fst_le_snd, le_rfl⟩)
  obtain rfl := hP e₁ e₂ he₁ he₂
  exact absurd ((NonemptyInterval.le_def.mp h₂).1.trans
    ((τ e₁).fst_le_snd.trans (NonemptyInterval.le_def.mp h₁).2)) (not_le.mpr hi)

theorem durativeUntil_unbounded {P : W → E → Prop} {w : W} {e : E} (hP : P w e)
    (he : (τ e).fst < (τ e).snd) : durativeUntil (UNBOUNDED P) w (τ e).snd :=
  ⟨τ e, fun _ hj ↦ mem_unbounded.2 ⟨e, hj, hP⟩, he, rfl⟩

-- The homogeneous part of a perfective stative fills the until interval (p. 96).
theorem durativeUntil_prfv_of_unbounded {P : W → E → Prop} (hP : HasSubintervalProperty P)
    {w : W} {t : T} (h : durativeUntil (UNBOUNDED P) w t) : durativeUntil (PRFV P) w t :=
  let ⟨i, hi, h⟩ := h; ⟨i, hi.trans (hP.unbounded_subset_prfv w), h⟩

theorem durativeUntil_perfect_prfv {P : W → E → Prop} {w : W} {e : E} (hP : P w e) {t : T}
    (ht : (τ e).snd < t) : durativeUntil (perfect (PRFV P)) w t := by
  refine ⟨⟨((τ e).snd, t), ht.le⟩, fun j hj ↦ ?_, ht, rfl⟩
  have h₁ : (τ e).snd ≤ j.fst := (NonemptyInterval.le_def.1 hj).1
  exact ⟨⟨((τ e).fst, j.snd), (τ e).fst_le_snd.trans (h₁.trans j.fst_le_snd)⟩,
    mem_prfv.2 ⟨e, NonemptyInterval.le_def.2 ⟨le_rfl, h₁.trans j.fst_le_snd⟩, hP⟩,
    (τ e).fst_le_snd.trans h₁, rfl⟩

/-! ### Negation: wide scope, narrow scope and the eventive UNTIL -/

/-- The state of not-P-ing, which a stativizing negation would deliver, holds when no P-event
overlaps the interval. -/
def notState (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  fun w ↦ {i | ∀ e, P w e → ∀ a ∈ (τ e), a ∉ i}

theorem isLowerSet_notState (P : W → E → Prop) (w : W) :
    IsLowerSet (notState P w : Set (NonemptyInterval T)) :=
  fun _ _ hji h e he a ha haj ↦ h e he a ha (NonemptyInterval.coe_subset_coe.mpr hji haj)

/-- Mittwoch's wide-scope reading is durative UNTIL of the state of not-P-ing. -/
def wideScope (P : W → E → Prop) (w : W) (t' : T) : Prop := durativeUntil (notState P) w t'

/-- External negation denies the durative UNTIL claim. -/
def narrowScope (p : W → Set (NonemptyInterval T)) (w : W) (t' : T) : Prop :=
  ¬ durativeUntil p w t'

/-- Karttunen's scalar eventive UNTIL holds when a P-event occurs at the until time and none
starts earlier. -/
def eventiveUntil (P : W → E → Prop) (w : W) (t : T) : Prop :=
  (∃ e, P w e ∧ t ∈ (τ e)) ∧ ∀ e, P w e → t ≤ (τ e).fst

theorem eventiveUntil_actualization {P : W → E → Prop} {w : W} {t : T}
    (h : eventiveUntil P w t) : ∃ e, P w e :=
  let ⟨⟨e, he, _⟩, _⟩ := h; ⟨e, he⟩

/-- The wide-scope reading holds when nothing P-like ever happens, so it carries no
actualization. -/
theorem wideScope_of_forall_not {P : W → E → Prop} {w : W} (hP : ∀ e, ¬ P w e) {t t' : T}
    (h : t < t') : wideScope P w t' :=
  ⟨⟨(t, t'), h.le⟩, fun _ _ e he ↦ absurd he (hP e), h, rfl⟩

/-- Eventive UNTIL is Karttunen's *not until* together with the actualization his presupposition
supplies. -/
theorem eventiveUntil_iff (P : W → E → Prop) (w : W) (t : T) :
    eventiveUntil P w t ↔ notUntil (τ '' {e | P w e}) {NonemptyInterval.pure t} ∧
      when_ (τ '' {e | P w e}) {NonemptyInterval.pure t} := by
  constructor
  · rintro ⟨⟨e, he, ht⟩, hall⟩
    refine ⟨(notUntil_iff _ _).mpr fun s ⟨_, ⟨e', he', rfl⟩, hs⟩ ↦
      ⟨t, ⟨_, rfl, NonemptyInterval.mem_pure_self t⟩,
        (hall e' he').trans (NonemptyInterval.mem_def.mp hs).1⟩,
      t, ⟨τ e, ⟨e, he, rfl⟩, ht⟩, ⟨_, rfl, NonemptyInterval.mem_pure_self t⟩⟩
  · rintro ⟨hnu, s, ⟨_, ⟨e, he, rfl⟩, hs⟩, j, hj, hsj⟩
    obtain rfl := Set.mem_singleton_iff.mp hj
    rw [NonemptyInterval.mem_pure] at hsj
    subst hsj
    refine ⟨⟨e, he, hs⟩, fun e' he' ↦ ?_⟩
    obtain ⟨t', ⟨j, hj, ht'⟩, hle⟩ := mem_upperClosure.1 ((notUntil_iff _ _).mp hnu
      ⟨τ e', ⟨e', he', rfl⟩, NonemptyInterval.mem_def.mpr ⟨le_rfl, (τ e').fst_le_snd⟩⟩)
    obtain rfl := Set.mem_singleton_iff.mp hj
    rw [NonemptyInterval.mem_pure] at ht'
    exact ht' ▸ hle

theorem eventiveUntil_not_before {P : W → E → Prop} {w : W} {t : T}
    (h : eventiveUntil P w t) : ¬ before (τ '' {e | P w e}) t :=
  fun ⟨_, ⟨_, ⟨e, he, rfl⟩, hs⟩, hlt⟩ ↦
    absurd ((h.2 e he).trans (NonemptyInterval.mem_def.mp hs).1) (not_le.mpr hlt)

theorem not_before_of_forall_not {P : W → E → Prop} {w : W} (hP : ∀ e, ¬ P w e) (t : T) :
    ¬ before (τ '' {e | P w e}) t :=
  fun ⟨_, ⟨_, ⟨e, he, _⟩, _⟩, _⟩ ↦ hP e he

/-! ### The paper's sentences -/

/-- A `Connective` is one of the UNTIL words or *before* in the paper's four languages. -/
inductive Connective
  | until | mexri | paraMonon | prin | til | fyrrEn | tot | pas
  deriving DecidableEq, Repr

/-- The paper's connective entry lists Greek *para monon*, literally 'but only', as an *until*
word, as in *i prigipisa dhen eftase para monon ta mesanixta* 'the princess did not arrive until
midnight'. -/
def paraMononEntry : Tense.Connective :=
  { form := Greek.StandardModern.PolarityItems.paraMonon.form, relation := .until_ }

/-- `c.entry` is the connective entry of `c`, the fragment's, or the paper's own for *para
monon*. -/
def Connective.entry : Connective → Tense.Connective
  | .until => English.TemporalConnectives.until_
  | .mexri => Greek.StandardModern.TemporalConnectives.mexri
  | .paraMonon => paraMononEntry
  | .prin => Greek.StandardModern.TemporalConnectives.prin
  | .til => Icelandic.TemporalConnectives.thangadTil
  | .fyrrEn => Icelandic.TemporalConnectives.fyrrEn
  | .tot => Dutch.TemporalConnectives.tot
  | .pas => Dutch.TemporalConnectives.pas

/-- `c.polarityItem` is the polarity item that the connective `c` is or doubles as, for the Greek,
Icelandic and Dutch punctual *until* words, and English *until* in its eventive use. -/
def Connective.polarityItem : Connective → Option PolarityItem
  | .until => some English.PolarityItems.until_
  | .paraMonon => some Greek.StandardModern.PolarityItems.paraMonon
  | .fyrrEn => some Icelandic.PolarityItems.fyrrEn
  | .pas => some Dutch.PolarityItems.pas
  | _ => none

/-- The punctual *until*s, the words the paper takes to lexicalize Karttunen's eventive UNTIL, are
Greek *para monon*, Icelandic *fyrr en* and Dutch *pas*. -/
def Connective.Punctual (c : Connective) : Prop :=
  c = .paraMonon ∨ c = .fyrrEn ∨ c = .pas

instance : DecidablePred Connective.Punctual := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- A connective is durative UNTIL when it is an *until* entry that is not punctual. -/
abbrev Connective.Durative (c : Connective) : Prop :=
  c.entry.relation = .until_ ∧ ¬ c.Punctual

/-- A connective is eventive UNTIL when it is or doubles as a polarity item, since punctual
*until* is a polarity item; every punctual word is one. -/
abbrev Connective.Eventive (c : Connective) : Prop := c.polarityItem.isSome

/-- A connective is *before* when its entry relates the clauses by precedence. -/
abbrev Connective.Before (c : Connective) : Prop := c.entry.relation = .before

/-- An `AspectForm` is the viewpoint of the main clause. -/
inductive AspectForm
  | imperfective | perfective | progressive | perfect | simplePast
  deriving DecidableEq, Repr

/-- An `Eventuality` class separates states and activities from achievements and
accomplishments. -/
inductive Eventuality
  | stative | eventive
  deriving DecidableEq, Repr

/-- `a.view P` is the description of a main clause of form `a` over the predicate `P`. The
imperfective and the progressive put the reference interval within the run time of an event, the
perfective and the English simple past put the run time within the reference interval, and the
perfect is the perfect of the perfective. -/
def AspectForm.view : AspectForm → (W → E → Prop) → W → Set (NonemptyInterval T)
  | .imperfective | .progressive => UNBOUNDED
  | .perfective | .simplePast => PRFV
  | .perfect => fun P ↦ Aspect.perfect (PRFV P)

/-- The predicates of an eventuality class: a stative one has the subinterval property, and an
eventive one holds of a single event in a world. -/
def Eventuality.predicates : Eventuality → Set (W → E → Prop)
  | .stative => {P | HasSubintervalProperty P}
  | .eventive => {P | ∀ w e e', P w e → P w e' → e = e'}

/-- A model of the paper's sentences: worlds, a time line, and events with run times on it. -/
structure Model where
  /-- The worlds. -/
  W : Type
  /-- The times. -/
  T : Type
  /-- The events. -/
  E : Type
  /-- The times are linearly ordered. -/
  [ord : LinearOrder T]
  /-- Each event has a run time. -/
  [trace : Event.TemporalTrace E T]

attribute [instance] Model.ord Model.trace

/-- A main clause of form `a` over a predicate of class `c` is **homogeneous** in the paper's
sense, admitting durative UNTIL, when durative UNTIL holds of its description in some model. -/
def AdmitsDurative (a : AspectForm) (c : Eventuality) : Prop :=
  ∃ (M : Model) (P : M.W → M.E → Prop) (w : M.W) (t : M.T),
    P ∈ c.predicates ∧ durativeUntil (a.view P) w t

private def unitSpan : NonemptyInterval ℤ := ⟨⟨0, 1⟩, by decide⟩

/-- A state holding over the unit span and at each of its parts. -/
private def aState : Unit → NonemptyInterval ℤ → Prop := fun _ e ↦ e ≤ unitSpan

/-- A single event spanning the unit span. -/
private def anEvent : Unit → NonemptyInterval ℤ → Prop := fun _ e ↦ e = unitSpan

private theorem aState_mem : aState ∈ Eventuality.stative.predicates :=
  hasSubintervalProperty_iff_witnesses.2 fun _ _ he t ht ↦ ⟨t, rfl, ht.trans he⟩

private theorem anEvent_mem : anEvent ∈ Eventuality.eventive.predicates :=
  fun _ _ _ h h' ↦ h.trans h'.symm

private theorem admitsDurative_of {a : AspectForm} {c : Eventuality}
    {P : Unit → NonemptyInterval ℤ → Prop} (hP : P ∈ c.predicates) {t : ℤ}
    (h : durativeUntil (a.view P) () t) : AdmitsDurative a c :=
  ⟨⟨Unit, ℤ, NonemptyInterval ℤ⟩, P, (), t, hP, h⟩

/-- A main clause is homogeneous exactly when its form is imperfective, progressive or perfect, or
its predicate stative: the perfective of a single event cannot fill the until interval, while the
perfective of a state fills it with its homogeneous part. -/
theorem admitsDurative_iff {a : AspectForm} {c : Eventuality} :
    AdmitsDurative a c ↔ a = .imperfective ∨ a = .progressive ∨ a = .perfect ∨ c = .stative := by
  constructor
  · rintro ⟨M, P, w, t, hP, h⟩
    cases a <;> cases c <;> first | decide | exact absurd h (not_durativeUntil_prfv (hP w) t)
  · intro h
    have hs := durativeUntil_unbounded (P := aState) (w := ()) le_rfl (by decide)
    have he := durativeUntil_unbounded (P := anEvent) (w := ()) rfl (by decide)
    have hs' := durativeUntil_prfv_of_unbounded aState_mem hs
    have ps := durativeUntil_perfect_prfv (P := aState) (w := ()) le_rfl (t := 2) (by decide)
    have pe := durativeUntil_perfect_prfv (P := anEvent) (w := ()) rfl (t := 2) (by decide)
    cases c <;> cases a <;> simp at h <;>
      first
      | exact admitsDurative_of aState_mem hs
      | exact admitsDurative_of aState_mem hs'
      | exact admitsDurative_of aState_mem ps
      | exact admitsDurative_of anEvent_mem he
      | exact admitsDurative_of anEvent_mem pe

instance (a : AspectForm) (c : Eventuality) : Decidable (AdmitsDurative a c) :=
  decidable_of_iff' _ admitsDurative_iff

/-- A form is **stative** when a clause of that form is homogeneous whatever its predicate. -/
def StativeForm (a : AspectForm) : Prop := ∀ c, AdmitsDurative a c

theorem stativeForm_iff {a : AspectForm} :
    StativeForm a ↔ a = .imperfective ∨ a = .progressive ∨ a = .perfect :=
  ⟨fun h ↦ by simpa using admitsDurative_iff.1 (h .eventive),
    fun h _ ↦ admitsDurative_iff.2 (by rcases h with h | h | h <;> simp [h])⟩

instance : DecidablePred StativeForm := fun _ ↦ decidable_of_iff' _ stativeForm_iff

/-- A `Test` is what the sentence tests, acceptability, preposing of the UNTIL phrase, or a
continuation denying the event. -/
inductive Test
  | plain | preposed | noEventContinuation
  deriving DecidableEq, Repr

/-- A `Row` is a sentence of the paper: its connective, the form and class of its main clause,
the licensing context the connective sits under, and what it tests. -/
structure Row where
  connective : Connective
  aspect : AspectForm
  eventuality : Eventuality
  licenser : Option LicensingContext
  test : Test
  deriving DecidableEq, Repr

/-- The polarity item of a connective, if it has one, is admitted by the context the sentence puts
it under, and outside any context only if it needs no licenser. -/
def Licensed (c : Connective) : Option LicensingContext → Prop
  | some k => ∀ i ∈ c.polarityItem, k.licenser.Admits i
  | none => ∀ i ∈ c.polarityItem, ¬ (i.IsNPI ∨ i.IsFCI)

instance (c : Connective) : DecidablePred (Licensed c)
  | some _ => inferInstanceAs (Decidable (∀ _ ∈ _, _))
  | none => inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- `Predicted` is the judgment that the two-*until* analysis predicts for a row. A plain sentence
needs durative UNTIL over a homogeneous clause, eventive UNTIL whose polarity item is licensed, or
*before*. Preposing needs durative UNTIL over a stative form, and so does a continuation denying
the event, unless the connective is *before*. -/
def Predicted (r : Row) : Prop :=
  match r.test with
  | .plain => (r.connective.Durative ∧ AdmitsDurative r.aspect r.eventuality) ∨
      (r.connective.Eventive ∧ Licensed r.connective r.licenser) ∨ r.connective.Before
  | .preposed => r.connective.Durative ∧ StativeForm r.aspect
  | .noEventContinuation => (r.connective.Durative ∧ StativeForm r.aspect) ∨ r.connective.Before

instance : DecidablePred Predicted := fun _ ↦ by unfold Predicted; split <;> infer_instance

/-- The connectives of the paper. -/
def connectives : List Connective :=
  [.until, .mexri, .paraMonon, .prin, .til, .fyrrEn, .tot, .pas]

/-- The connective a row's gloss line shows: the earliest span of the gloss stream spelling the
declared form of a connective's fragment entry, multiword forms included. -/
def connectiveOfForm? (ex : Datum) : Option Connective :=
  Gloss.lookup? (connectives.map fun c ↦ (c.entry.form, c)) ex.glossStream

/-- The names of the viewpoints in the rows. -/
def aspectForms : List (String × AspectForm) :=
  [("imperfective", .imperfective), ("perfective", .perfective), ("progressive", .progressive),
    ("perfect", .perfect), ("simplePast", .simplePast)]

/-- The names of the eventuality classes in the rows. -/
def eventualities : List (String × Eventuality) :=
  [("stative", .stative), ("eventive", .eventive)]

/-- The names of the licensing contexts in the rows, `none` for an unembedded connective. -/
def licensers : List (String × Option LicensingContext) :=
  [("none", none), ("negation", some .negation), ("without", some .withoutClause),
    ("doubt", some .doubtVerb), ("question", some .question)]

/-- The row of a datum, its connective read off the gloss line where there is one. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let connective ← connectiveOfForm? ex <|>
    ex.parse? "connective" [("until", Connective.until), ("mexri", .mexri),
      ("paraMonon", .paraMonon), ("prin", .prin), ("til", .til), ("fyrrEn", .fyrrEn),
      ("tot", .tot), ("pas", .pas)]
  let aspect ← ex.parse? "aspect" aspectForms
  let eventuality ← ex.parse? "eventuality" eventualities
  let licenser ← ex.parse? "licenser" licensers
  let test ← ex.parse? "test" [("plain", Test.plain), ("preposed", .preposed),
    ("noEventContinuation", .noEventContinuation)]
  pure ⟨connective, aspect, eventuality, licenser, test⟩

/-- Every judgment on the UNTIL sentences follows from the connective's fragment entry, the
homogeneity of the main clause and the licensing of the polarity item. -/
theorem rows_predicted :
    Datum.Checks Row.ofDatum (fun r ↦ .ofProp (Predicted r)) Examples.all 37 := by decide

/-- A `Diagnostic` is one of the stativity diagnostics of the fifth section. -/
inductive Diagnostic
  | howLong | while | forAdverbial | imperative
  deriving DecidableEq, Repr

/-- A `DiagnosticRow` is a sentence of the stativity diagnostics: the diagnostic and the form and
class of the clause it applies to. Whether the clause is negated is not read, since the
prediction does not depend on it. -/
structure DiagnosticRow where
  diagnostic : Diagnostic
  aspect : AspectForm
  eventuality : Eventuality
  deriving DecidableEq, Repr

/-- The diagnostic row of a datum. -/
def DiagnosticRow.ofDatum (ex : Datum) : Option DiagnosticRow := do
  let diagnostic ← ex.parse? "diagnostic" [("howLong", Diagnostic.howLong), ("while", .while),
    ("forAdverbial", .forAdverbial), ("imperative", .imperative)]
  let aspect ← ex.parse? "aspect" aspectForms
  let eventuality ← ex.parse? "eventuality" eventualities
  pure ⟨diagnostic, aspect, eventuality⟩

/-- The stative diagnostics accept a homogeneous clause and the imperative rejects one, with
negation playing no role, so negation is no stativizer. -/
theorem diagnostics_predicted : Datum.Checks DiagnosticRow.ofDatum
    (fun r ↦ .ofProp ((r.diagnostic = .imperative → ¬ AdmitsDurative r.aspect r.eventuality) ∧
      (r.diagnostic ≠ .imperative → AdmitsDurative r.aspect r.eventuality)))
    Examples.all 12 := by
  decide

end Giannakidou2002
