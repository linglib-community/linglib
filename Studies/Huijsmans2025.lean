module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Tense.Evidential

/-!
# Huijsmans (2025): Timing of evidence and epistemic modal claims

This file formalizes Huijsmans's account of the ʔayʔaǰuθəm future clitic *səm* and
inferential *č̓ɛ* and of English *will* and *must* as strong epistemic necessity modals that
differ in a presupposition on the timing of the evidence. The modal base is a set of
propositions each with an earliest moment at which it holds (`IsEarliest`); *səm* and *will*
presuppose that every modal-base proposition holds before the earliest moment of the
prejacent (`FuturePresup`), *č̓ɛ* that at least one holds at or after it
(`InferentialPresup`), and *must* presupposes nothing. Where the earliest moments exist, the
two presuppositions are complementary (`futurePresup_iff_not_inferentialPresup`), which is
the distribution of Section 4: contexts with all the evidence in place before the prejacent
take *səm* and *will*, and contexts with evidence arising at or after it take *č̓ɛ*, with
*must* felicitous in both. An empty modal base falsifies the inferential's presupposition
(`not_inferentialPresup_empty`), the prediction the paper checks against the cat that has
gone missing.

The rival analysis in terms of an evidence acquisition time relates that time to the event
time on the library's `Tense.EvidentialFrame`. Evidence that has become true can
be acquired only afterwards, so the inferential's presupposition entails downstream evidence
(`downstream_of_inferentialPresup`); the converse fails, and the contexts where the speaker
learns of rain or of a night's clam-digging after the wetting or the cold are the wedge:
the modal-base timing licenses *will*, and the acquisition timing does not
(`felipe_future`, `felipe_not_eatFuture`).

## Implementation notes

* The earliest moment of a proposition is taken in the evaluation world rather than in a
  maximally similar one, and the modal-base propositions are already shifted to untensed
  ones, so the reference-time index and the abstraction rule are not represented.
* The contexts of Section 4 are stated by the onset times of the eventualities, following
  the remark that a proposition describing an eventuality holds forever after it; the at-issue
  content is Kratzer necessity over the best worlds with the non-past orientation of the
  future morphemes.

## References

* [huijsmans-2025]
* [kratzer-1981]
* [condoravdi-2002]
* [beaver-condoravdi-2003]
-/

@[expose] public section

namespace Huijsmans2025

open Modality Semantics Tense

variable {T W : Type*} [LinearOrder T]

/-! ### Earliest moments and the presuppositions -/

/-- The earliest moment at which an untensed proposition holds in a world, the function of (63), is
a time at which it holds that precedes every other. -/
def IsEarliest (p : T → W → Prop) (w : W) (m : T) : Prop := p m w ∧ ∀ t, p t w → m ≤ t

theorem IsEarliest.unique {p : T → W → Prop} {w : W} {m m' : T} (h : IsEarliest p w m)
    (h' : IsEarliest p w m') : m = m' :=
  le_antisymm (h.2 _ h'.1) (h'.2 _ h.1)

/-- The presupposition of *səm* and *will*, (65), is that every modal-base proposition has its
earliest moment before the earliest moment of the prejacent. -/
def FuturePresup (mb : Set (T → W → Prop)) (p : T → W → Prop) (w : W) : Prop :=
  ∀ q ∈ mb, ∃ mq mp, IsEarliest q w mq ∧ IsEarliest p w mp ∧ mq < mp

/-- The presupposition of *č̓ɛ*, (87), is that some modal-base proposition has its earliest moment
at or after the earliest moment of the prejacent. -/
def InferentialPresup (mb : Set (T → W → Prop)) (p : T → W → Prop) (w : W) : Prop :=
  ∃ q ∈ mb, ∃ mq mp, IsEarliest q w mq ∧ IsEarliest p w mp ∧ mp ≤ mq

/-- Where the earliest moments exist, the two presuppositions are complementary, so the contexts of
Section 4 split between *səm* and *č̓ɛ*. -/
theorem futurePresup_iff_not_inferentialPresup {mb : Set (T → W → Prop)} {p : T → W → Prop}
    {w : W} (hmb : ∀ q ∈ mb, ∃ m, IsEarliest q w m) (hp : ∃ m, IsEarliest p w m) :
    FuturePresup mb p w ↔ ¬ InferentialPresup mb p w := by
  obtain ⟨mp, hmp⟩ := hp
  constructor
  · rintro h ⟨q, hq, mq, mp', hmq, hmp', hle⟩
    obtain ⟨mq', mp'', hmq', hmp'', hlt⟩ := h q hq
    rw [hmq.unique hmq', hmp'.unique hmp''] at hle
    exact absurd hlt (not_lt.2 hle)
  · intro h q hq
    obtain ⟨mq, hmq⟩ := hmb q hq
    refine ⟨mq, mp, hmq, hmp, not_le.1 fun hle ↦ h ⟨q, hq, mq, mp, hmq, hmp, hle⟩⟩

/-- An inference from no evidence cannot be an inferential, as in (56). -/
theorem not_inferentialPresup_empty (p : T → W → Prop) (w : W) :
    ¬ InferentialPresup (∅ : Set (T → W → Prop)) p w := by
  rintro ⟨q, hq, _⟩
  exact hq

/-! ### The at-issue content -/

/-- The modal base at a reference time, as the world-propositions of the untensed ones. -/
def modalBaseAt (mb : Set (T → W → Prop)) (t : T) : Background W :=
  fun _ ↦ (fun q w ↦ q t w) '' mb

/-- The at-issue content of *səm* and *will*, (62), is that the prejacent holds at or after the
reference time in every best world. -/
def futureClaim (mb : Set (T → W → Prop)) (h : Background W) (p : T → W → Prop)
    (t : T) (w : W) : Prop :=
  necessity (modalBaseAt mb t) h (fun w' ↦ ∃ t', t ≤ t' ∧ p t' w') w

/-- The at-issue content of *č̓ɛ* and *must*, (87) and (96), is that the prejacent holds at the
reference time in every best world. -/
def necessityClaim (mb : Set (T → W → Prop)) (h : Background W) (p : T → W → Prop)
    (t : T) (w : W) : Prop :=
  necessity (modalBaseAt mb t) h (fun w' ↦ p t w') w

/-- Present orientation is a case of the future morphemes' non-past orientation. -/
theorem futureClaim_of_necessityClaim {mb : Set (T → W → Prop)} {h : Background W}
    {p : T → W → Prop} {t : T} {w : W} (hc : necessityClaim mb h p t w) :
    futureClaim mb h p t w :=
  fun w' hw' ↦ ⟨t, le_rfl, hc w' hw'⟩

/-! ### The evidence acquisition time -/

/-- On the rival analysis (39), the future morphemes require the evidence to be acquired before the
event, and the inferential at or after it, the frame's `Downstream`. -/
def EatFuture (f : EvidentialFrame T) : Prop :=
  ({ eventToAcquisition := ⟦future⟧ } : EvidentialFrame.Constraint).Holds f

instance (f : EvidentialFrame T) : Decidable (EatFuture f) :=
  inferInstanceAs (Decidable (EvidentialFrame.Constraint.Holds _ f))

/-- The evidence is acquired before the event. -/
theorem eatFuture_iff {f : EvidentialFrame T} : EatFuture f ↔ f.acquisitionTime < f.eventTime := by
  simp [EatFuture, EvidentialFrame.Constraint.Holds]

/-- A modal-base proposition can be acquired only once it holds. -/
def AcquiredAfterOnset (mb : Set (T → W → Prop)) (w : W) (f : EvidentialFrame T) : Prop :=
  ∀ q ∈ mb, ∀ m, IsEarliest q w m → m ≤ f.acquisitionTime

/-- The inferential's presupposition entails downstream evidence when the prejacent's earliest
moment is the event time, the remark of Section 4.2 that the two analyses agree on *č̓ɛ* in
one direction. -/
theorem downstream_of_inferentialPresup {mb : Set (T → W → Prop)} {p : T → W → Prop} {w : W}
    {f : EvidentialFrame T} (hacq : AcquiredAfterOnset mb w f)
    (hev : IsEarliest p w f.eventTime) (h : InferentialPresup mb p w) : f.Downstream := by
  obtain ⟨q, hq, mq, mp, hmq, hmp, hle⟩ := h
  rw [hmp.unique hev] at hle
  exact hle.trans (hacq q hq mq hmq)

/-! ### The contexts of Section 4 -/

/-- A proposition describing an eventuality holds from its onset on. -/
def from' (o : ℤ) : ℤ → Unit → Prop := fun t _ ↦ o ≤ t

theorem isEarliest_from' (o : ℤ) : IsEarliest (from' o) () o :=
  ⟨le_rfl, fun _ h ↦ h⟩

theorem isEarliest_from'_iff {o m : ℤ} : IsEarliest (from' o) () m ↔ m = o :=
  ⟨fun h ↦ h.unique (isEarliest_from' o), fun h ↦ h ▸ isEarliest_from' o⟩

/-- A context gives the onsets of the modal-base eventualities, the onset of the prejacent
eventuality, and the times of the evidence's acquisition and of the utterance. -/
structure Context where
  onsets : List ℤ
  prejacent : ℤ
  acquisition : ℤ
  speech : ℤ

namespace Context

variable (c : Context)

def mb : Set (ℤ → Unit → Prop) := {q | ∃ o ∈ c.onsets, q = from' o}

def frame : EvidentialFrame ℤ :=
  { speechTime := c.speech, eventTime := c.prejacent, acquisitionTime := c.acquisition }

/-- In the form of the diagrams, (35) says that every onset precedes the prejacent's. -/
theorem futurePresup_iff :
    FuturePresup c.mb (from' c.prejacent) () ↔ ∀ o ∈ c.onsets, o < c.prejacent := by
  constructor
  · intro h o ho
    obtain ⟨mq, mp, hmq, hmp, hlt⟩ := h (from' o) ⟨o, ho, rfl⟩
    rwa [isEarliest_from'_iff.1 hmq, isEarliest_from'_iff.1 hmp] at hlt
  · rintro h q ⟨o, ho, rfl⟩
    exact ⟨o, c.prejacent, isEarliest_from' o, isEarliest_from' _, h o ho⟩

/-- In the form of the diagrams, (36) says that some onset is at or after the prejacent's. -/
theorem inferentialPresup_iff :
    InferentialPresup c.mb (from' c.prejacent) () ↔ ∃ o ∈ c.onsets, c.prejacent ≤ o := by
  constructor
  · rintro ⟨q, ⟨o, ho, rfl⟩, mq, mp, hmq, hmp, hle⟩
    exact ⟨o, ho, by rwa [isEarliest_from'_iff.1 hmq, isEarliest_from'_iff.1 hmp] at hle⟩
  · rintro ⟨o, ho, hle⟩
    exact ⟨from' o, ⟨o, ho, rfl⟩, o, c.prejacent, isEarliest_from' o, isEarliest_from' _, hle⟩

instance : Decidable (FuturePresup c.mb (from' c.prejacent) ()) :=
  decidable_of_iff _ c.futurePresup_iff.symm

instance : Decidable (InferentialPresup c.mb (from' c.prejacent) ()) :=
  decidable_of_iff _ c.inferentialPresup_iff.symm

end Context

/-- In (40)–(41) the fish went into the oven and past occasions are known before it is cooked, and
the watch is checked before the cooking is complete. -/
def cooking : Context := ⟨[0, 0], 2, 1, 2⟩

/-- In (42)–(43) Daniel's leaving and the length of the trip precede his getting home. -/
def daniel : Context := ⟨[0, 0], 2, 1, 3⟩

/-- In (44)–(45) the poisoning precedes the death. -/
def poison : Context := ⟨[0, 0], 2, 0, 3⟩

/-- In (46)–(47) the rain and the coat left behind precede Felipe's wetting at five, but the speaker
sees the rain only at six. -/
def felipe : Context := ⟨[4, 0], 5, 6, 6⟩

/-- In (48)–(49) the cold night and the clam-digging precede the friend's getting cold, and the
speaker learns of the clam-digging the next day. -/
def clamDigging : Context := ⟨[0, 0], 1, 2, 2⟩

/-- In (50)–(51) the smell of the fish arises as it is cooked. -/
def smell : Context := ⟨[1], 1, 1, 1⟩

/-- In (52)–(53) and (83) the car is in the driveway from the arrival home on. -/
def driveway : Context := ⟨[1], 1, 2, 2⟩

/-- In (54)–(55) the bear stops moving as it dies. -/
def bear : Context := ⟨[1], 1, 2, 2⟩

/-- In (57)–(58) evidence both before and at the prejacent, the time of day and the car and lights,
is taken together. -/
def homeFromWork : Context := ⟨[0, 1, 1], 1, 2, 2⟩

/-- In (59)–(60) there are twenty minutes in the oven and the smell, and the smell may be set aside.
-/
def ovenAndSmell : Context := ⟨[0, 1], 1, 1, 1⟩

def ovenOnly : Context := ⟨[0], 1, 1, 1⟩

/-- In (56) there is no evidence at all. -/
def missingCat : Context := ⟨[], 1, 0, 0⟩

theorem cooking_future : FuturePresup cooking.mb (from' cooking.prejacent) () := by decide

theorem cooking_not_inferential : ¬ InferentialPresup cooking.mb (from' cooking.prejacent) () := by
  decide

theorem felipe_future : FuturePresup felipe.mb (from' felipe.prejacent) () := by decide

theorem felipe_not_inferential : ¬ InferentialPresup felipe.mb (from' felipe.prejacent) () := by
  decide

/-- The evidence is acquired after the event, so the acquisition analysis rejects *will* and *səm*
here, against the judgments. -/
theorem felipe_not_eatFuture : ¬ EatFuture felipe.frame := by decide

theorem felipe_downstream : felipe.frame.Downstream := by decide

theorem clamDigging_future : FuturePresup clamDigging.mb (from' clamDigging.prejacent) () := by
  decide

theorem clamDigging_not_eatFuture : ¬ EatFuture clamDigging.frame := by decide

theorem smell_inferential : InferentialPresup smell.mb (from' smell.prejacent) () := by decide

theorem smell_not_future : ¬ FuturePresup smell.mb (from' smell.prejacent) () := by decide

theorem driveway_inferential : InferentialPresup driveway.mb (from' driveway.prejacent) () := by
  decide

theorem bear_not_future : ¬ FuturePresup bear.mb (from' bear.prejacent) () := by decide

/-- In (57) evidence on both sides of the prejacent forces the inferential. -/
theorem homeFromWork_inferential :
    InferentialPresup homeFromWork.mb (from' homeFromWork.prejacent) () := by decide

theorem homeFromWork_not_future :
    ¬ FuturePresup homeFromWork.mb (from' homeFromWork.prejacent) () := by decide

/-- In (59)–(60), with the smell in the modal base the inferential is licensed, and with it set
aside the future is. -/
theorem ovenAndSmell_inferential :
    InferentialPresup ovenAndSmell.mb (from' ovenAndSmell.prejacent) () := by decide

theorem ovenOnly_future : FuturePresup ovenOnly.mb (from' ovenOnly.prejacent) () := by decide

theorem missingCat_not_inferential :
    ¬ InferentialPresup missingCat.mb (from' missingCat.prejacent) () := by decide

end Huijsmans2025
