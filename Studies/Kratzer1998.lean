module

public import Linglib.Logic.Assignment
public import Linglib.Syntax.Category.Verb.Tense
public import Linglib.Semantics.Tense.Pronoun
public import Linglib.Semantics.Aspect.Viewpoint.Basic
public import Linglib.Languages.English.Tense
public import Linglib.Languages.German.Tense
public import Linglib.Data.Examples.Kratzer1998
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Kratzer (1998): More Structural Analogies between Pronouns and Tenses

[kratzer-1998] treats tenses as pronouns. An indexical tense presupposes how its time stands to the
utterance time, so out of the blue [only a tense admitting coincidence is
defined](##tense_outOfTheBlue_iff); a zero tense presupposes nothing, and [with a binder index
abstracts over its time](##zeroTense_abstract), which [an indexical tense does
not](##tense_not_abstracted). A form may spell out a tense with one of Klein's aspects, [only the
perfect anterior](##AspectHead.isAnterior_iff), so a form [describes a past event out of the blue
iff it spells out such a tense with the perfect](##Variety.describesPastOutOfTheBlue_iff), as [the
English simple past and the German *Perfekt* do, not the *Präteritum*](##rows_outOfTheBlue).

## Implementation notes

An out-of-the-blue context is the temporal assignment sending every variable to the utterance time,
so a tense is defined there iff its cell admits coincidence, by the presupposition of
`Tense.pronoun`. The aspect operators take a reference interval; a tense supplies a point, embedded
as `NonemptyInterval.pure`. The aspects are possibility along their cells over the run times, as
`Aspect.ViewpointType.denote` is. The imperfective and the perfective are the library's
`Aspect.unbounded` and `Aspect.perfective`, and the perfect, with strict precedence, is stronger
than the perfect viewpoint of `Aspect.ViewpointType`, which admits an event abutting the
reference time (`perfect_viewpointType`). The zero-pronoun
typology of §2–§3 and the locality argument from switch reference are prose. The French table is not
entered, since the library has no French tense forms.

## TODO

Kratzer derives from the attitude verbs' selection of properties of times what von Stechow calls
Abusch's Constraint, that the highest tense of an attitude complement is controlled by the matrix
tense, a constraint distinct from Abusch's Upper Limit Constraint. The attitude verbs are not
encoded, so neither is the derivation.

## References

* [kratzer-1998]
* [partee-1973]
* [abusch-1997]
* [von-stechow-1995]
* [ogihara-1989]
* [ogihara-1996]
* [heim-kratzer-1998]
* [klein-1994]
-/

@[expose] public section

namespace Kratzer1998

open Event (τ)
open scoped Assignment

open scoped Denotes

open Tense PointAlgebra ModalLogic
open Aspect (unbounded ViewpointType)

/-! ### The tenses (§4–§5) -/

section Tenses

variable {W T : Type*}

/-- The indexical tense with cell `C` is the variable `n` presupposing that its reference stands
to the utterance time, the time of the index `0`, in a position of `C`. The present and the past
are the tenses of the cells `present` and `past`. -/
abbrev tense [LT T] (C : PointAlgebra) (n : ℕ) : Definite (ℕ → T) W T :=
  pronoun (toSetRel C) n 0

/-- The zero tense is a variable with no presupposition, bound by the next tense up. -/
abbrev zeroTense [LT T] (n : ℕ) : Definite (ℕ → T) W T := pronoun (toSetRel ⊤) n 0

/-- An out-of-the-blue context has no salient time but the utterance time, so every temporal
variable resolves to it. -/
def outOfTheBlue (t₀ : T) : ℕ → T := Function.const ℕ t₀

theorem tense_outOfTheBlue_iff [LinearOrder T] (C : PointAlgebra) (n : ℕ) (t₀ : T) (w : W) :
    (tense C n (outOfTheBlue t₀) w).Dom ↔ .eq ∈ C :=
  pronoun_dom_const t₀

theorem zeroTense_dom [LinearOrder T] (n : ℕ) (g : ℕ → T) (w : W) :
    (zeroTense n g w).Dom := by
  simp

-- (31)
theorem zeroTense_abstract [LinearOrder T] (n : ℕ) (g : ℕ → T) (t : T) (w : W) :
    t ∈ Λ[n] (fun g ↦ zeroTense n g w) g t := by
  simp

theorem tense_not_abstracted [LT T] (C : PointAlgebra) {m n : ℕ} (hn : n ≠ m)
    (g : ℕ → T) (t : T) (w : W) {s : T} (hs : s ∈ Λ[m] (fun g ↦ tense C n g w) g t) :
    s = g n := by
  simpa [Function.update_of_ne hn] using (mem_pronoun.1 hs).2.symm

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

variable {T W E : Type*} [LinearOrder T] [TemporalTrace E T]

/-- The operator of (38) turns a property of times into the property of eventualities that
holds of `e`, at any world, iff the property of times holds of the running time of `e` at every
world. -/
def star (P : W → NonemptyInterval T → Prop) (_ : W) (e : E) : Prop :=
  ∀ w', P w' (τ e)

theorem star_congr (P : W → NonemptyInterval T → Prop) (e : E) (w w' : W) :
    star P w e ↔ star P w' e := Iff.rfl

/-- The cell of an aspect says how the event time stands to the reference time. The
imperfective includes the reference time in the event time, the perfective includes the event
time in the reference time, and the perfect has the event over by the reference time. -/
def AspectHead.cell : AspectHead → IntervalAlgebra
  | .imperfective => IntervalAlgebra.le⁻¹
  | .perfective => IntervalAlgebra.le
  | .perfect => IntervalAlgebra.precedes

@[simp] theorem AspectHead.relation_mem_cell_imperfective {r s : NonemptyInterval T} :
    Allen.relation s r ∈ AspectHead.imperfective.cell ↔ r ≤ s := by
  simp [cell]

@[simp] theorem AspectHead.relation_mem_cell_perfective {r s : NonemptyInterval T} :
    Allen.relation s r ∈ AspectHead.perfective.cell ↔ s ≤ r := by
  simp [cell]

@[simp] theorem AspectHead.relation_mem_cell_perfect {r s : NonemptyInterval T} :
    Allen.relation s r ∈ AspectHead.perfect.cell ↔ s.Precedes r := by
  simp [cell]

/-- Against the library's viewpoints, the perfect is strictly stronger, excluding an event that
ends exactly when the reference time begins; the imperfective is strictly weaker, admitting a
reference time that is the whole event time; and the perfectives coincide. -/
theorem cell_viewpointType :
    AspectHead.perfect.cell < ViewpointType.perfect.cell ∧
      ViewpointType.imperfective.cell < AspectHead.imperfective.cell ∧
      AspectHead.perfective.cell = ViewpointType.perfective.cell := by
  decide +kernel

/-- An aspect maps a property of events to the property of times to which the time of some such
event stands in the aspect's cell. -/
def AspectHead.denote (a : AspectHead) (P : E → Prop) : NonemptyInterval T → Prop :=
  ◇[IntervalAlgebra.toSetRel a.cell] (Event.runTimes P)

theorem AspectHead.denote_iff {a : AspectHead} {P : E → Prop} {r : NonemptyInterval T} :
    a.denote P r ↔ ∃ e, Allen.relation (τ e) r ∈ a.cell ∧ P e := by
  simp [denote, Event.diamond_runTimes_iff]

theorem denote_imperfective (P : E → Prop) :
    AspectHead.imperfective.denote (T := T) P = unbounded P := by
  rw [AspectHead.denote, AspectHead.cell, IntervalAlgebra.toSetRel_inv]
  rfl

theorem denote_perfective (P : E → Prop) :
    AspectHead.perfective.denote (T := T) P = Aspect.perfective P := by
  rw [AspectHead.denote, AspectHead.cell, IntervalAlgebra.toSetRel_le]
  rfl

theorem perfect_viewpointType {P : E → Prop} {r : NonemptyInterval T} :
    AspectHead.perfect.denote P r → ViewpointType.perfect.denote P r :=
  diamond_le_diamond_iff.2 (IntervalAlgebra.toSetRel_mono cell_viewpointType.1.le) _ r

variable (T) in
/-- An anterior aspect places the event time before the reference time. -/
def AspectHead.IsAnterior (a : AspectHead) : Prop :=
  ∀ r s : NonemptyInterval T, Allen.relation s r ∈ a.cell → s.Precedes r

/-- Only the perfect is anterior, since the imperfective and the perfective relate a time to
itself. -/
theorem AspectHead.isAnterior_iff [Nonempty T] (a : AspectHead) :
    a.IsAnterior T ↔ a = .perfect := by
  obtain ⟨t⟩ := ‹Nonempty T›
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fun _ _ h ↦ relation_mem_cell_perfect.1 h⟩
  cases a
  · exact absurd (h (.pure t) (.pure t) (relation_mem_cell_imperfective.2 le_rfl))
      (NonemptyInterval.precedes_irrefl _)
  · exact absurd (h (.pure t) (.pure t) (relation_mem_cell_perfective.2 le_rfl))
      (NonemptyInterval.precedes_irrefl _)
  · rfl

theorem AspectHead.IsAnterior.precedes {a : AspectHead} (ha : a.IsAnterior T)
    {P : W → E → Prop} {w : W} {r : NonemptyInterval T} (h : a.denote (P w) r) :
    ∃ e : E, (τ e).Precedes r ∧ P w e :=
  let ⟨e, he, hP⟩ := AspectHead.denote_iff.1 h
  ⟨e, ha _ _ he, hP⟩

/-- Tense `C` on the variable `n` with aspect `a` is true of an event property when the tense is
defined and the aspect holds of the property at the tense's reference. -/
def denote (C : PointAlgebra) (a : AspectHead) (n : ℕ) (P : W → E → Prop)
    (g : ℕ → T) (w : W) : Prop :=
  (tense C n g w).Dom ∧ a.denote (P w) (.pure (g n))

theorem denote_iff_holdsAlong (C : PointAlgebra) (a : AspectHead) (n : ℕ)
    (P : W → E → Prop) (g : ℕ → T) (w : W) :
    denote C a n P g w ↔ ∃ e : E, P w e ∧
      IntervalAlgebra.HoldsAlong [IntervalAlgebra.pure C, a.cell] (.pure (g 0)) [.pure (g n),
        τ e] := by
  simp only [IntervalAlgebra.HoldsAlong, and_true, IntervalAlgebra.mem_toSetRel,
    IntervalAlgebra.relation_mem_pure]
  simp [denote, AspectHead.denote_iff, NonemptyInterval.IsPoint]
  exact ⟨fun ⟨hC, e, he, hP⟩ ↦ ⟨e, hP, hC, he⟩, fun ⟨e, hP, hC, he⟩ ↦ ⟨hC, e, he, hP⟩⟩

theorem denote_outOfTheBlue_iff (C : PointAlgebra) (a : AspectHead) (n : ℕ)
    (P : W → E → Prop) (t₀ : T) (w : W) :
    denote C a n P (outOfTheBlue t₀) w ↔ .eq ∈ C ∧ a.denote (P w) (.pure t₀) := by
  rw [denote, tense_outOfTheBlue_iff]; rfl

theorem denote_present_perfect_outOfTheBlue_iff (n : ℕ) (P : W → E → Prop) (t₀ : T)
    (w : W) :
    denote ⟦present⟧ .perfect n P (outOfTheBlue t₀) w ↔ ∃ e : E, (τ e).snd < t₀ ∧ P w e := by
  simp [denote_outOfTheBlue_iff, AspectHead.denote_iff, NonemptyInterval.Precedes,
    denote_present]

end Aspects

/-! ### What the tense forms spell out (§7) -/

/-- A variety of a language, as the closing tables describe it, is a table of the tense forms
with the tenses and aspects they spell out. -/
structure Variety where
  /-- The entries of the table. -/
  table : List (Tense.Form × PointAlgebra × AspectHead)

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

theorem table_forms :
    (∀ x ∈ english.table, x.1 ∈ English.Tense.tenseForms) ∧
      (∀ x ∈ standardGerman.table, x.1 ∈ German.tenseForms) ∧
      ∀ x ∈ southGerman.table, x.1 ∈ German.southernTenseForms := by
  decide

namespace Variety

variable (v : Variety)

/-- The form `f` spells out tense `C` with aspect `a`. -/
def SpellsOut (f : Tense.Form) (C : PointAlgebra) (a : AspectHead) : Prop := (f, C, a) ∈ v.table

instance (f : Tense.Form) (C : PointAlgebra) (a : AspectHead) : Decidable (v.SpellsOut f C a) :=
  inferInstanceAs (Decidable (_ ∈ _))

variable (T : Type*) [LinearOrder T] in
/-- A form can describe a past event out of the blue when it spells out a tense defined out of
the blue with an anterior aspect. -/
def DescribesPastOutOfTheBlue (f : Tense.Form) : Prop :=
  ∃ C a, v.SpellsOut f C a ∧
    (∀ t₀ : T, (tense (W := Unit) C 0 (outOfTheBlue t₀) ()).Dom) ∧ a.IsAnterior T

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

theorem standardGerman_transparent :
    standardGerman.IsTenseFaithful ∧ standardGerman.IsPerfectCompositional := by decide +kernel

theorem southGerman_transparent :
    ¬ southGerman.IsTenseFaithful ∧ southGerman.IsPerfectCompositional := by decide +kernel

theorem english_transparent :
    ¬ english.IsTenseFaithful ∧ ¬ english.IsPerfectCompositional := by decide +kernel

-- (42)
theorem backwardShifted :
    english.SpellsOut .simplePast ⟦past⟧ .perfect ∧
      ¬ standardGerman.SpellsOut .simplePast ⟦past⟧ .perfect ∧
      standardGerman.SpellsOut .pastPerfect ⟦past⟧ .perfect := by
  decide

/-- The language codes of the example rows name these varieties. -/
def varieties : List (Glottocode × Variety) := [(.english, english), (.german, standardGerman)]

/-- The rows name these tense forms. -/
def forms : List (String × Tense.Form) :=
  [("simple past", .simplePast), ("Präteritum", .simplePast), ("Perfekt", .presentPerfect)]

/-- In (40) a form is acceptable out of the blue iff it can describe a past event there. -/
theorem rows_outOfTheBlue :
    ∀ r ∈ Examples.all, r.feature? "context" = some "out of the blue" →
      ∃ v ∈ r.byLanguage varieties, ∃ f ∈ r.parse? "form" forms,
        (r.judgment = .acceptable ↔ v.DescribesPastOutOfTheBlue ℤ f) := by
  decide +kernel

-- (40)
theorem rows_realize :
    (∀ f ∈ English.Tense.tenseForms,
      ((∃ ws ∈ English.Verbs.build.tenseForm (English.Auxiliaries.cell .third .singular) f,
          ' ' :: [' '].intercalate (ws.map String.toList) ++ [' '] <:+:
            Examples.ex40a.primaryText.toList) ↔
        Examples.ex40a.parse? "form" forms = some f)) ∧
    ∀ r ∈ [Examples.ex40b, Examples.ex40c], ∀ f ∈ German.tenseForms,
      ((∃ ws ∈ German.Verbs.bauen.principalParts.tenseForm f, ws ⊆ r.surfaceTokens) ↔
        r.parse? "form" forms = some f) := by
  decide +kernel

end Kratzer1998
