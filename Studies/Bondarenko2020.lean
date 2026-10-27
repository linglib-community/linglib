module

public import Linglib.Semantics.Events.Lifespan
public import Linglib.Semantics.Attitudes.Anchor
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Events.Basic
public import Linglib.Data.Examples.Bondarenko2020

/-!
# Bondarenko (2020): factivity from pre-existence

Bondarenko accounts for the factivity alternation of Barguzin Buryat *hanaxa*, 'think' with a
finite CP and 'remember' with a nominalized clause. The nominalized clause presupposes that the
event it describes started before the thinking: a *began* continuation must place its start
before the matrix time, a future child or a fictional cat cannot be the object, and the
inference survives questions and negation. A CP modifies the thinking event, whose content its
complementizer fixes, and adds no presupposition. A nominalized clause saturates the internal
argument of the head θTh, which presupposes that this argument started before the matrix time;
closed by Fox's strong Kleene existential, the report presupposes exactly that, and the factive
inference follows.

## Main definitions

* `thetaTh`: the head θTh with *hanaxa*.
* `report`: the past-tense report with a nominalized clause.
* `reportThat`: the past-tense report with a CP.

## Implementation notes

* Pre-existence is `Event.PreExists` of `Semantics/Events/Lifespan.lean`. Time spans are a
  function `τ` into `NonemptyInterval`, the run time of an event or the life span of an entity,
  and the paper's `LB(τ(x)) < t` is `(τ x).fst < t.fst` (`Event.preExists_iff`). θTh's
  presupposition in (55) is the pre-existence of `Q`, and its assertion the pre-existence of the
  `Q`s that the `P`-event is about.
* Truth values are trivalent, as in the paper: a sentence is a trivalent proposition
  `W → SignType`, defined when it is true or false. The existential closure (58) and the past
  tense (60) are both the strong Kleene existential `Trivalent.existsStrong`, the tense over the
  subtype of past times `t' < t` (`t'.Precedes t`) within the contextual interval `g(1)`
  (`t' ≤ g₁`).
* The simplification from (57) and (58) to (59) assumes a nonempty domain of events, as the
  paper's fn. 36 says, and (62) follows from (61) only for a nonempty contextual past: over an
  empty one the falsity condition of (61) holds vacuously and the sentence is defined whatever
  the complement. Both are hypotheses here.
* The verb and the Voice head are one predicate of events `P` at a world and time, so the
  external argument joins θTh's assertion and leaves its presupposition, as in (57). This is the
  weak Kleene conjunction `SignType.meetWeak` with a presuppositionless conjunct, not the strong
  Kleene one the paper adopts elsewhere; the two differ only when the subject is the experiencer
  of no event. θTh's `about` is a function from contentful events to their topics, as in (46).
* A report with both a nominalized clause and a CP (21) is θTh with a `P` that includes the CP's
  content condition, and has the nominalized clause's presupposition.
* Not formalized: the *tuxai* 'about' phrases (7), (48), which carry no presupposition and get
  no formula in the paper; the allosemy of θTh (49); and the plan readings of the future
  participle -xA (70)–(73), which the paper leaves open.

## References

* [bondarenko-2020]
* [fox-2013]
* [kleene-1952]
-/

@[expose] public section

namespace Bondarenko2020

open Event

variable {W T X E I : Type*} [LinearOrder T]

/-! ### θTh and its presupposition, (55), (56) -/

open Classical in
/-- With *hanaxa*, θTh holds of an event `e` at the matrix time `t` when `e` is a `P`-event about
an individual of `Q` that pre-exists `t`, and presupposes that `Q` pre-exists `t`, (55), (56). -/
noncomputable def thetaTh (τ : X → NonemptyInterval T) (about : E → X)
    (P : W → NonemptyInterval T → E → Prop) (Q : W → NonemptyInterval T → X → Prop)
    (t : NonemptyInterval T) (e : E) : W → SignType :=
  {w | PreExists τ (Q w t) t}.indicator
    fun w ↦ SignType.ofProp (PreExists τ (fun x ↦ Q w t x ∧ P w t e ∧ about e = x) t)

/-- The report (61) is the past tense (60), within the contextual interval `g₁`, over the
existentially closed (58) θTh-report (57). -/
noncomputable def report (τ : X → NonemptyInterval T) (about : E → X)
    (P : W → NonemptyInterval T → E → Prop) (Q : W → NonemptyInterval T → X → Prop)
    (g₁ t : NonemptyInterval T) : W → SignType :=
  fun w ↦ Trivalent.existsStrong fun t' : {t' // t'.Precedes t ∧ t' ≤ g₁} ↦
    Trivalent.existsStrong fun e ↦ thetaTh τ about P Q t' e w

open Classical in
/-- A report with a CP, (29), is the past tense (28) over a thinking event whose content the
complementizer (25) fixes as `p`. -/
noncomputable def reportThat [Anchor E I] (P : W → NonemptyInterval T → E → Prop)
    (p : I → Prop) (g₁ t : NonemptyInterval T) : W → SignType :=
  fun w ↦ Trivalent.existsStrong fun t' : {t' // t'.Precedes t ∧ t' ≤ g₁} ↦
    SignType.ofProp (∃ e, P w t' e ∧ Anchor.comp p e)

variable {τ : X → NonemptyInterval T} {about : E → X} {P : W → NonemptyInterval T → E → Prop}
  {Q : W → NonemptyInterval T → X → Prop} {g₁ t : NonemptyInterval T} {w : W}

-- (55), (56)
theorem thetaTh_eq_one_iff {e : E} :
    thetaTh τ about P Q t e w = 1 ↔ PreExists τ (fun x ↦ Q w t x ∧ P w t e ∧ about e = x) t := by
  simp only [thetaTh, Trivalent.indicator_apply_eq_one_iff, Set.mem_ofPred_eq,
    SignType.ofProp_eq_one_iff, and_iff_right_iff_imp]
  exact PreExists.mono fun _ h ↦ h.1

theorem thetaTh_ne_zero_iff {e : E} : thetaTh τ about P Q t e w ≠ 0 ↔ PreExists τ (Q w t) t := by
  simp [thetaTh]

/-! ### A CP adds no presupposition, §3.1 -/

/-- A report with a CP is defined at every world, so it presupposes nothing about the
actual world, §3.1.2. -/
theorem reportThat_ne_zero [Anchor E I] (p : I → Prop) : reportThat P p g₁ t w ≠ 0 :=
  Trivalent.existsStrong_ne_zero_iff.2 (.inr fun _ ↦ by simp)

/-! ### A nominalized clause presupposes pre-existence, §3.2.3 -/

/-- The existentially closed θTh-report presupposes pre-existence, (59). -/
theorem existsStrong_thetaTh_ne_zero_iff [Nonempty E] :
    Trivalent.existsStrong (fun e ↦ thetaTh τ about P Q t e w) ≠ 0 ↔
      PreExists τ (Q w t) t := by
  rw [Trivalent.existsStrong_ne_zero_iff]
  refine ⟨?_, fun h ↦ .inr fun _ ↦ thetaTh_ne_zero_iff.2 h⟩
  rintro (⟨e, he⟩ | h)
  · exact thetaTh_ne_zero_iff.1 (he ▸ one_ne_zero)
  · exact thetaTh_ne_zero_iff.1 (h (Classical.arbitrary E))

/-- Over a nonempty contextual past, the report presupposes that the complement describes
something that started before a past thinking time, (62). -/
theorem exists_preExists_of_report_ne_zero [Nonempty E]
    (hpast : ∃ t', t'.Precedes t ∧ t' ≤ g₁) (h : report τ about P Q g₁ t w ≠ 0) :
    ∃ t', t'.Precedes t ∧ t' ≤ g₁ ∧ PreExists τ (Q w t') t' := by
  obtain ⟨⟨t', hprec, hle⟩, hp⟩ | h := Trivalent.existsStrong_ne_zero_iff.1 h
  · exact ⟨t', hprec, hle, existsStrong_thetaTh_ne_zero_iff.1 (hp ▸ one_ne_zero)⟩
  · obtain ⟨t', ht'⟩ := hpast
    exact ⟨t', ht'.1, ht'.2, existsStrong_thetaTh_ne_zero_iff.1 (h ⟨t', ht'⟩)⟩

-- (62)
theorem report_ne_zero_of_not_exists (hpast : ¬ ∃ t', t'.Precedes t ∧ t' ≤ g₁) :
    report τ about P Q g₁ t w ≠ 0 :=
  Trivalent.existsStrong_ne_zero_iff.2 (.inr fun ⟨t', ht'⟩ ↦ absurd ⟨t', ht'⟩ hpast)

/-- The report presupposes that the complement describes something in the world of evaluation,
the factive inference (2b), (3). -/
theorem exists_of_report_ne_zero [Nonempty E] (hpast : ∃ t', t'.Precedes t ∧ t' ≤ g₁)
    (h : report τ about P Q g₁ t w ≠ 0) : ∃ t' x, t'.Precedes t ∧ Q w t' x :=
  let ⟨t', hprec, _, hpre⟩ := exists_preExists_of_report_ne_zero hpast h
  let ⟨x, hx⟩ := hpre.exists
  ⟨t', x, hprec, hx⟩

-- (15)
theorem support_neg_report :
    Function.support (-report τ about P Q g₁ t) = Function.support (report τ about P Q g₁ t) := by
  ext; simp

-- (64), (65)
theorem existsStrong_thetaTh_comp_ne_zero_iff [Nonempty E] [Anchor X I] (p : I → Prop) :
    Trivalent.existsStrong (fun e ↦ thetaTh τ about P (fun _ _ ↦ Anchor.comp p) t e w) ≠ 0 ↔
      PreExists τ (Anchor.comp p) t :=
  existsStrong_thetaTh_ne_zero_iff

/-- A report with a CP can be true while its content is false, (1b). One thinking event, at
the past time `1` and with the content that the world is `true`, makes the report true at the
world `false`. -/
example :
    letI : Anchor Unit (Bool × NonemptyInterval ℤ) := ⟨fun _ i ↦ i.1 = true⟩
    reportThat (I := Bool × NonemptyInterval ℤ) (fun (_ : Bool) _ (_ : Unit) ↦ True)
      (fun i ↦ i.1 = true) (.pure 1) (.pure 2) false = 1 := by
  simp only [reportThat, Trivalent.existsStrong_eq_one_iff, SignType.ofProp_eq_one_iff]
  exact ⟨⟨.pure 1, by decide, le_rfl⟩, (), trivial, rfl⟩

/-! ### The judgments

Days are integers, Monday `1`, Tuesday `2`, Wednesday `3` (fn. 3), and the thinking is on
Tuesday. -/

/-- A breaking begun on Monday is one Sajana can remember on Tuesday, (4b). -/
example : PreExists Event.τ (· = (.pure 1 : NonemptyInterval ℤ)) (.pure 2) := by
  simp

/-- A breaking begun on Wednesday is not, (4c). -/
example : ¬ PreExists Event.τ (· = (.pure 3 : NonemptyInterval ℤ)) (.pure 2) := by
  simp

/-- A child conceived before the time talked about, here `0`, can be remembered, and
neither it nor Badma need have stopped existing; a child not yet conceived cannot, (5), (8). -/
example : PreExists (fun (x : NonemptyInterval ℤ) ↦ x) (· = ⟨(-1, 10), by decide⟩) (.pure 0) ∧
    ¬ PreExists (fun (x : NonemptyInterval ℤ) ↦ x) (· = ⟨(2, 10), by decide⟩) (.pure 0) := by
  simp

end Bondarenko2020
