module

public import Linglib.Semantics.Aspect.SubintervalProperty
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

/-!
# Giannakidou (2002): UNTIL, Aspect, and Negation

Giannakidou argues for Karttunen's two *until*s against the one-*until* analysis of Mittwoch
and de Swart, on which negation is an aspectual stativizer. Durative UNTIL asks its description
to hold at every subinterval of an interval ending at the until time, which a homogeneous
description, one with the subinterval property, supplies and a perfective description of a
single event cannot; since the imperfective is homogeneous, Greek, which marks aspect overtly,
lets *mexri* combine with imperfectives and not with negated perfectives, where the polarity item
*para monon* stands in. Under negation the analyses part ways: the wide-scope reading holds when
nothing P-like ever happens, whereas eventive UNTIL entails the event and is Karttunen's *not
until* with the actualization his presupposition supplies. The paper's Greek, English, Icelandic
and Dutch judgments follow from the fragment entries of the connectives and its classification of
the punctual words, and its stativity diagnostics from homogeneity with negation playing no role.

## Main statements

* `not_durativeUntil_prfv`: a perfective description of a single event rules out durative UNTIL.
* `wideScope_of_forall_not`: the wide-scope reading carries no actualization.
* `eventiveUntil_iff`: eventive UNTIL is *not until* with actualization.
* `rows_predicted`: every judgment on the UNTIL sentences is predicted.
* `diagnostics_predicted`: the stativity diagnostics follow from homogeneity alone.

## Implementation notes

* Descriptions are the interval properties of `Aspect`; events carry a run time and a
  perfective description places it within the reference interval, an imperfective one strictly
  around it. The until interval is required to be nondegenerate, which is what excludes a single
  event from satisfying the durative condition at both its endpoints.
* Homogeneity is the subinterval property of `Aspect/SubintervalProperty.lean`, and durative
  UNTIL is the durative reading `Aspect.durative` at a nondegenerate span ending at the until
  time.
* The relation of each connective is read off its fragment entry. Which words are punctual
  *until*s, Greek *para monon*, Icelandic *fyrr en* and Dutch *pas*, is the paper's
  classification (`Connective.Punctual`). The polarity of the eventive words is read off their
  polarity-item entries: *para monon*, *fyrr en* and English *until* are negative polarity items
  and need an antiveridical licenser, Dutch *pas* is a positive one.
* The oddity of *Nancy didn't get married until she died* and of its Greek counterpart, which the
  actualization entailment explains, is pragmatic and is left in prose.

## References

* [giannakidou-2002]
* [karttunen-1974]
* [mittwoch-1977]
* [de-swart-1996]
-/

@[expose] public section

namespace Giannakidou2002

open Event (τ)

open Aspect Tense Karttunen1974 Heinamaki1974

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

/-- A perfective description of a single event is incompatible with durative UNTIL, since an
achievement or accomplishment cannot lie within both endpoints of the until interval. -/
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
def paraMononEntry : Tense.Connective := { form := "para monon", relation := .until_ }

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

/-- A connective is eventive UNTIL when it is punctual or an *until* with a polarity-item
use. -/
abbrev Connective.Eventive (c : Connective) : Prop :=
  c.Punctual ∨ c.polarityItem.isSome = true

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

/-- A `Licenser` is what the sentence puts the connective under. -/
inductive Licenser
  | none | negation | without | nonveridical
  deriving DecidableEq, Repr

/-- Negation and *without* are the antiveridical licensers. -/
abbrev Licenser.Antiveridical (l : Licenser) : Prop := l = .negation ∨ l = .without

/-- A `Test` is what the sentence tests, acceptability, preposing of the UNTIL phrase, or a
continuation denying the event. -/
inductive Test
  | plain | preposed | noEventContinuation
  deriving DecidableEq, Repr

structure Row where
  connective : Connective
  aspect : AspectForm
  eventuality : Eventuality
  licenser : Licenser
  test : Test
  deriving DecidableEq, Repr

/-- A main clause is homogeneous when it has an imperfective, progressive or perfect form, or
is stative. -/
abbrev Homog (a : AspectForm) (e : Eventuality) : Prop :=
  a = .imperfective ∨ a = .progressive ∨ a = .perfect ∨ e = .stative

/-- The forms that admit the wide-scope reading are the imperfective and the perfect. -/
abbrev WideScopeForm (a : AspectForm) : Prop := a = .imperfective ∨ a = .perfect

/-- The polarity item of a connective demands an antiveridical licenser for a negative
item, none for a positive one. -/
abbrev Licensed (c : Connective) (l : Licenser) : Prop :=
  ∀ i ∈ c.polarityItem, (i.IsNPI → l.Antiveridical) ∧ (i.IsPPI → l = .none)

/-- `Predicted` is the judgment that the two-*until* analysis predicts for a row. -/
def Predicted (r : Row) : Prop :=
  (r.test = .plain → (r.connective.Durative ∧ Homog r.aspect r.eventuality) ∨
    (r.connective.Eventive ∧ Licensed r.connective r.licenser) ∨ r.connective.Before) ∧
  (r.test = .preposed → r.connective.Durative ∧ WideScopeForm r.aspect) ∧
  (r.test = .noEventContinuation →
    (r.connective.Durative ∧ WideScopeForm r.aspect) ∨ r.connective.Before)

instance : DecidablePred Predicted := fun _ ↦ by unfold Predicted; infer_instance

def Row.ofDatum (ex : Datum) : Option Row := do
  let connective ← ex.parse? "connective" [("until", Connective.until), ("mexri", .mexri),
    ("paraMonon", .paraMonon), ("prin", .prin), ("til", .til), ("fyrrEn", .fyrrEn), ("tot", .tot),
    ("pas", .pas)]
  let aspect ← ex.parse? "aspect" [("imperfective", AspectForm.imperfective),
    ("perfective", .perfective), ("progressive", .progressive), ("perfect", .perfect),
    ("simplePast", .simplePast)]
  let eventuality ← ex.parse? "eventuality" [("stative", Eventuality.stative),
    ("eventive", .eventive)]
  let licenser ← ex.parse? "licenser" [("none", Licenser.none), ("negation", .negation),
    ("without", .without), ("nonveridical", .nonveridical)]
  let test ← ex.parse? "test" [("plain", Test.plain), ("preposed", .preposed),
    ("noEventContinuation", .noEventContinuation)]
  pure ⟨connective, aspect, eventuality, licenser, test⟩

/-- Every judgment on the UNTIL sentences follows from the connective's fragment entry, the
homogeneity of the main clause and the licensing of the polarity item. -/
theorem rows_predicted :
    Datum.Checks Row.ofDatum (fun r ↦ .ofProp (Predicted r)) Examples.all 36 := by decide

/-- A `Diagnostic` is one of the stativity diagnostics of the fifth section. -/
inductive Diagnostic
  | howLong | while | forAdverbial | imperative
  deriving DecidableEq, Repr

structure DiagnosticRow where
  diagnostic : Diagnostic
  aspect : AspectForm
  eventuality : Eventuality
  licenser : Licenser
  deriving DecidableEq, Repr

def DiagnosticRow.ofDatum (ex : Datum) : Option DiagnosticRow := do
  let diagnostic ← ex.parse? "diagnostic" [("howLong", Diagnostic.howLong), ("while", .while),
    ("forAdverbial", .forAdverbial), ("imperative", .imperative)]
  let aspect ← ex.parse? "aspect" [("imperfective", AspectForm.imperfective),
    ("perfective", .perfective), ("progressive", .progressive), ("perfect", .perfect),
    ("simplePast", .simplePast)]
  let eventuality ← ex.parse? "eventuality" [("stative", Eventuality.stative),
    ("eventive", .eventive)]
  let licenser ← ex.parse? "licenser" [("none", Licenser.none), ("negation", .negation),
    ("without", .without), ("nonveridical", .nonveridical)]
  pure ⟨diagnostic, aspect, eventuality, licenser⟩

/-- The stative diagnostics accept a homogeneous clause and the imperative rejects one, with
negation playing no role, so negation is no stativizer. -/
theorem diagnostics_predicted : Datum.Checks DiagnosticRow.ofDatum
    (fun r ↦ .ofProp ((r.diagnostic = .imperative → ¬ Homog r.aspect r.eventuality) ∧
      (r.diagnostic ≠ .imperative → Homog r.aspect r.eventuality)))
    Examples.all 12 := by
  decide

end Giannakidou2002
