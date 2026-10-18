module

public import Linglib.Syntax.Category.Verb.Tense
public import Linglib.Semantics.Tense.Pronoun
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Fragments.English.Tense
public import Linglib.Fragments.German.Tense
public import Linglib.Data.Examples.Kratzer1998

/-!
# Kratzer (1998): More Structural Analogies between Pronouns and Tenses

Kratzer treats tenses as pronouns, after Partee. English has two indexical tenses, a present
defined when the context provides an interval including the utterance time and a past defined
when it provides one preceding it, and a zero tense with no presupposition that must be bound by
the next tense up. A zero tense with a binder index abstracts over the time, so attitude
complements denote properties of times, which derives Abusch's constraint from the verbs'
selection. What looks like a tense may spell out a tense together with one of Klein's three
aspects; since out of the blue only the present is defined and only the perfect places the
event before the reference time, a form describes a past event out of the blue just in case it
spells out present tense with perfect aspect. The paper's tables assign that combination to the
English simple past and the German *Perfekt* and never to the *Präteritum*.

## Main results

* `AspectHead.isAnterior_iff`: only the perfect is anterior.
* `describesPastOutOfTheBlue_iff`: describing a past event out of the blue is spelling out the
  present perfect.
* `rows_outOfTheBlue`: the out-of-the-blue judgments of the paper's examples.

## Implementation notes

An out-of-the-blue context is the temporal assignment sending every variable to the utterance time,
so a tense is defined there iff its cell admits coincidence, by the presupposition of
`Tense.pronoun`. The aspect operators take a reference interval; a tense supplies a point, embedded
as `NonemptyInterval.pure`. The aspects are instances of the library's `Aspect.ofRel`. The
imperfective and the perfective are the library's `Aspect.UNBOUNDED` and `Aspect.PRFV`, and the
perfect, with strict precedence, is stronger than the perfect viewpoint of `Aspect.ViewpointType`,
which admits an event abutting the reference time (`perfect_viewpointType`). The zero-pronoun
typology of §2–§3 and the locality argument from switch reference are prose. The French table is not
entered, since the library has no French tense forms.

## References

* [kratzer-1998]
* [partee-1973]
* [abusch-1997]
* [ogihara-1989]
* [ogihara-1996]
* [heim-kratzer-1998]
* [klein-1994]
-/

@[expose] public section

namespace Kratzer1998

open Event (τ)

open Semantics

open Tense
open Montague
open Aspect (ofRel ofRel_mono UNBOUNDED PRFV ViewpointType)

/-! ### The tenses (§4–§5) -/

section Tenses

variable {W T : Type*}

/-- The indexical tense with cell `C` is the variable `n` presupposing that its reference stands
to the utterance time, the time of the index `0`, in a position of `C`. The present and the past
are the tenses of the cells `present` and `past`. -/
abbrev tense [LT T] (C : Finset Ordering) (n : ℕ) : Reference.Nominal (Assignment T) W T :=
  pronoun C n 0

/-- The zero tense is a variable with no presupposition, bound by the next tense up. -/
abbrev zeroTense [LT T] (n : ℕ) : Reference.Nominal (Assignment T) W T := pronoun ⊤ n 0

/-- An out-of-the-blue context has no salient time but the utterance time, so every temporal
variable resolves to it. -/
def outOfTheBlue (t₀ : T) : Assignment T := Function.const ℕ t₀

/-- Out of the blue a tense is defined iff its cell admits coincidence with the utterance time,
as the present does and the past does not. -/
theorem tense_outOfTheBlue_iff [LinearOrder T] (C : Finset Ordering) (n : ℕ) (t₀ : T) (w : W) :
    (tense C n).presup (outOfTheBlue t₀) w ↔ .eq ∈ C :=
  pronoun_presup_const t₀

/-- The zero tense has no presupposition. -/
theorem zeroTense_presup [LinearOrder T] (n : ℕ) (g : Assignment T) (w : W) :
    (zeroTense n).presup g w := by
  simp

/-- A zero tense with a binder index makes its clause a property of times, (31). Whatever the
assignment, the tense under the abstract denotes the time the abstract is applied to. -/
theorem zeroTense_abstract [LT T] (n : ℕ) (g : Assignment T) (t : T) (w : W) :
    lambdaAbsG n (fun g ↦ (zeroTense n).selector g w) g t = some t := by
  simp

/-- An indexical tense cannot be abstracted over by another index. The binder leaves the tense
with its own reference, which is why an attitude verb forces a zero tense. -/
theorem tense_not_abstracted [LT T] (C : Finset Ordering) {m n : ℕ} (hn : n ≠ m)
    (g : Assignment T) (t : T) (w : W) :
    lambdaAbsG m (fun g ↦ (tense C n).selector g w) g t = some (g n) := by
  simp [Function.update_of_ne hn]

end Tenses

/-! ### The aspects (§6–§7) -/

/-- An aspect head is imperfective, perfective or perfect. These are the rows of the closing
tables. -/
inductive AspectHead where
  | imperfective
  | perfective
  | perfect
  deriving DecidableEq, Repr, Fintype

section Aspects

variable {T W E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-- The operator of (38) turns a property of times into the property of eventualities that
holds of `e`, at any world, iff the property of times holds of the running time of `e` at every
world. -/
def star (P : W → Set (NonemptyInterval T)) (_ : W) (e : E) : Prop :=
  ∀ w', τ e ∈ P w'

/-- The temporal de re is semantically forced, since `star P` does not depend on the evaluation
world. -/
theorem star_congr (P : W → Set (NonemptyInterval T)) (e : E) (w w' : W) :
    star P w e ↔ star P w' e := Iff.rfl

/-- `a.rel r s` is the relation of the aspect `a` between the reference time `r` and the event
time `s`. The
imperfective includes the reference time in the event time, the perfective includes the event
time in the reference time, and the perfect has the event over by the reference time. -/
def AspectHead.rel : AspectHead → NonemptyInterval T → NonemptyInterval T → Prop
  | .imperfective, r, s => r ≤ s
  | .perfective, r, s => s ≤ r
  | .perfect, r, s => s.Precedes r

/-- An aspect maps a property of events to the property of times that stand in the aspect's
relation to the time of some such event. -/
def AspectHead.denote (a : AspectHead) (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  ofRel a.rel P

theorem denote_imperfective (P : W → E → Prop) :
    AspectHead.imperfective.denote P = UNBOUNDED P := rfl

theorem denote_perfective (P : W → E → Prop) : AspectHead.perfective.denote P = PRFV P := rfl

/-- The perfect entails the perfect viewpoint of the library, whose relation also admits an
event that ends exactly when the reference time begins. -/
theorem perfect_viewpointType {P : W → E → Prop} {w : W} {r : NonemptyInterval T} :
    r ∈ AspectHead.perfect.denote P w → r ∈ ViewpointType.perfect.denote P w :=
  fun h ↦ ofRel_mono (fun _ _ h ↦ le_of_lt h) P w h

variable (T) in
/-- An anterior aspect places the event time before the reference time. -/
def AspectHead.IsAnterior (a : AspectHead) : Prop :=
  ∀ r s : NonemptyInterval T, a.rel r s → s.Precedes r

/-- Only the perfect is anterior, since the imperfective and the perfective relate a time to
itself. -/
theorem AspectHead.isAnterior_iff [Nonempty T] (a : AspectHead) :
    a.IsAnterior T ↔ a = .perfect := by
  obtain ⟨t⟩ := ‹Nonempty T›
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fun _ _ h ↦ h⟩
  cases a
  · exact absurd (h (.pure t) (.pure t) le_rfl) (NonemptyInterval.precedes_irrefl _)
  · exact absurd (h (.pure t) (.pure t) le_rfl) (NonemptyInterval.precedes_irrefl _)
  · rfl

/-- An anterior aspect describes an event that is over by the reference time. -/
theorem AspectHead.IsAnterior.precedes {a : AspectHead} (ha : a.IsAnterior T)
    {P : W → E → Prop} {w : W} {r : NonemptyInterval T} (h : r ∈ a.denote P w) :
    ∃ e : E, (τ e).Precedes r ∧ P w e :=
  let ⟨e, he, hP⟩ := h
  ⟨e, ha _ _ he, hP⟩

/-- Tense `C` on the variable `n` with aspect `a` is true of an event property when the tense is
defined and the aspect holds of the property at the tense's reference. -/
def denote (C : Finset Ordering) (a : AspectHead) (n : ℕ) (P : W → E → Prop)
    (g : Assignment T) (w : W) : Prop :=
  (tense C n).presup g w ∧ .pure (g n) ∈ a.denote P w

/-- Out of the blue a tense with an aspect is true iff the tense admits coincidence with the
utterance time and the aspect holds there. -/
theorem denote_outOfTheBlue_iff (C : Finset Ordering) (a : AspectHead) (n : ℕ)
    (P : W → E → Prop) (t₀ : T) (w : W) :
    denote C a n P (outOfTheBlue t₀) w ↔ .eq ∈ C ∧ .pure t₀ ∈ a.denote P w := by
  rw [denote, tense_outOfTheBlue_iff]; rfl

/-- Present tense with perfect aspect describes an event over by the utterance time, so a past
event can be described with no past tense. -/
theorem denote_present_perfect_outOfTheBlue_iff (n : ℕ) (P : W → E → Prop) (t₀ : T)
    (w : W) :
    denote ⟦present⟧ .perfect n P (outOfTheBlue t₀) w ↔ ∃ e : E, (τ e).snd < t₀ ∧ P w e := by
  simp [denote_outOfTheBlue_iff, AspectHead.denote, AspectHead.rel, NonemptyInterval.Precedes,
    denote_present]

end Aspects

/-! ### What the tense forms spell out (§7) -/

/-- A variety of a language, as the closing tables describe it, is a table of the tense forms
with the tenses and aspects they spell out. -/
structure Variety where
  /-- The entries of the table. -/
  table : List (Tense.Form × Finset Ordering × AspectHead)

/-- In English the progressive forms spell out the imperfective and the simple forms the
perfective, and the simple past also spells out the perfect, of the present as of the past. -/
def english : Variety where
  table :=
    [(.presentProgressive, ⟦present⟧, .imperfective), (.pastProgressive, ⟦past⟧, .imperfective),
      (.simplePresent, ⟦present⟧, .perfective), (.simplePast, ⟦past⟧, .perfective),
      (.simplePast, ⟦present⟧, .perfect), (.simplePast, ⟦past⟧, .perfect),
      (.pastPerfect, ⟦past⟧, .perfect)]

/-- In Standard German the synthetic forms spell out the imperfective and the perfective, and
their perfects the perfect. -/
def standardGerman : Variety where
  table :=
    [(.simplePresent, ⟦present⟧, .imperfective), (.simplePresent, ⟦present⟧, .perfective),
      (.simplePast, ⟦past⟧, .imperfective), (.simplePast, ⟦past⟧, .perfective),
      (.presentPerfect, ⟦present⟧, .perfect), (.pastPerfect, ⟦past⟧, .perfect)]

/-- In South German, with the simple past gone, the present perfect also spells out the past
with the imperfective and the perfective, and the double perfect the past with the perfect. -/
def southGerman : Variety where
  table :=
    [(.simplePresent, ⟦present⟧, .imperfective), (.simplePresent, ⟦present⟧, .perfective),
      (.presentPerfect, ⟦past⟧, .imperfective), (.presentPerfect, ⟦past⟧, .perfective),
      (.presentPerfect, ⟦present⟧, .perfect), (.doublePerfect, ⟦past⟧, .perfect)]

/-- The tables use the tense forms of the Fragments. -/
theorem table_forms :
    (∀ x ∈ english.table, x.1 ∈ English.Tense.tenseForms) ∧
      (∀ x ∈ standardGerman.table, x.1 ∈ German.tenseForms) ∧
      ∀ x ∈ southGerman.table, x.1 ∈ German.southernTenseForms := by
  decide

namespace Variety

variable (v : Variety)

/-- The form `f` spells out tense `C` with aspect `a`. -/
def SpellsOut (f : Tense.Form) (C : Finset Ordering) (a : AspectHead) : Prop := (f, C, a) ∈ v.table

instance (f : Tense.Form) (C : Finset Ordering) (a : AspectHead) : Decidable (v.SpellsOut f C a) :=
  inferInstanceAs (Decidable (_ ∈ _))

variable (T : Type*) [LinearOrder T] in
/-- A form can describe a past event out of the blue when it spells out a tense defined out of
the blue with an anterior aspect. -/
def DescribesPastOutOfTheBlue (f : Tense.Form) : Prop :=
  ∃ C a, v.SpellsOut f C a ∧
    (∀ t₀ : T, (tense (W := Unit) C 0).presup (outOfTheBlue t₀) ()) ∧ a.IsAnterior T

/-- A form can describe a past event out of the blue iff it spells out, with the perfect, a
tense that admits coincidence with the utterance time. -/
theorem describesPastOutOfTheBlue_iff (T : Type*) [LinearOrder T] [Nonempty T] (f : Tense.Form) :
    v.DescribesPastOutOfTheBlue T f ↔ ∃ x ∈ v.table, x.1 = f ∧ .eq ∈ x.2.1 ∧ x.2.2 = .perfect := by
  simp only [DescribesPastOutOfTheBlue, tense_outOfTheBlue_iff, forall_const,
    AspectHead.isAnterior_iff, SpellsOut]
  exact ⟨fun ⟨C, a, h, hC, ha⟩ ↦ ⟨_, h, rfl, hC, ha⟩,
    fun ⟨⟨_, C, a⟩, h, hf, hC, ha⟩ ↦ ⟨C, a, hf ▸ h, hC, ha⟩⟩

instance (T : Type*) [LinearOrder T] [Nonempty T] :
    DecidablePred (v.DescribesPastOutOfTheBlue T) :=
  fun f ↦ decidable_of_iff _ (v.describesPastOutOfTheBlue_iff T f).symm

/-- A table is tense-faithful when a form spells out only the tense its finite verb is
inflected for. -/
def IsTenseFaithful : Prop := ∀ x ∈ v.table, x.2.1 = ⟦x.1.finite⟧

/-- A table is perfect-compositional when the forms that spell out the perfect of a tense are
the perfects of the forms that spell out that tense with another aspect. -/
def IsPerfectCompositional : Prop :=
  (∀ x ∈ v.table, x.2.2 = .perfect →
      ∃ y ∈ v.table, x.1 = y.1.perfect ∧ x.2.1 = y.2.1 ∧ y.2.2 ≠ .perfect) ∧
    ∀ y ∈ v.table, y.2.2 ≠ .perfect → (y.1.perfect, y.2.1, .perfect) ∈ v.table

instance : Decidable v.IsTenseFaithful := by unfold IsTenseFaithful; infer_instance

instance : Decidable v.IsPerfectCompositional := by unfold IsPerfectCompositional; infer_instance

end Variety

/-- The Standard German table can be read off the make-up of the forms. -/
theorem standardGerman_transparent :
    standardGerman.IsTenseFaithful ∧ standardGerman.IsPerfectCompositional := by decide +kernel

/-- South German builds its perfects compositionally, the double perfect on the present perfect
as a past, but its present perfect, a present inflection, spells out the past. -/
theorem southGerman_transparent :
    ¬ southGerman.IsTenseFaithful ∧ southGerman.IsPerfectCompositional := by decide +kernel

/-- English is neither, since the simple past, a past inflection that is the perfect of no
form, spells out the present with the perfect. -/
theorem english_transparent :
    ¬ english.IsTenseFaithful ∧ ¬ english.IsPerfectCompositional := by decide +kernel

/-- The backward-shifted reading of a past under a past, (42), is the past with the perfect,
which the English simple past spells out and the German one does not, so that Standard German
needs the past perfect. -/
theorem backwardShifted :
    english.SpellsOut .simplePast ⟦past⟧ .perfect ∧
      ¬ standardGerman.SpellsOut .simplePast ⟦past⟧ .perfect ∧
      standardGerman.SpellsOut .pastPerfect ⟦past⟧ .perfect := by
  decide

/-- The language codes of the example rows name these varieties. -/
def varieties : List (String × Variety) := [("stan1293", english), ("stan1295", standardGerman)]

/-- The rows name these tense forms. -/
def forms : List (String × Tense.Form) :=
  [("simple past", .simplePast), ("Präteritum", .simplePast), ("Perfekt", .presentPerfect)]

/-- In (40) a form is acceptable out of the blue iff it can describe a past event there. The
English simple past and the German present perfect can, and the German simple past cannot. -/
theorem rows_outOfTheBlue :
    ∀ r ∈ Examples.all, r.feature? "context" = some "out of the blue" →
      ∃ v ∈ varieties.lookup r.language, ∃ f ∈ r.parse? "form" forms,
        (r.judgment = .acceptable ↔ v.DescribesPastOutOfTheBlue ℤ f) := by
  decide +kernel

/-- The German rows of (40) are in the form they are labelled with, since of the tense forms of
*bauen* exactly the labelled one has all its words in the row. -/
theorem rows_realize :
    ∀ r ∈ [Examples.ex40b, Examples.ex40c], ∀ f ∈ German.tenseForms,
      ((∃ ws ∈ German.Verbs.bauen.principalParts.tenseForm f, ws ⊆ r.surfaceTokens) ↔
        r.parse? "form" forms = some f) := by
  decide +kernel

end Kratzer1998
