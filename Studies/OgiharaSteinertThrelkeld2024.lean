module

public import Studies.BeaverCondoravdi2003
public import Linglib.Semantics.Events.Basic
public import Linglib.Data.Examples.OgiharaSteinertThrelkeld2024

/-!
# Ogihara and Steinert-Threlkeld (2024): Limitations of a Modal Analysis of Before and After

Ogihara and Steinert-Threlkeld argue against Beaver and Condoravdi's branching-time analysis of
*before* and propose an eventuality-based revision. *After* is veridical and *before* is not:
*Mozart died before he finished the Requiem* is true although he never finished it. Alternatives
that branch only after the main-clause time cannot place a complement whose window closes at or
before that time, as with Ohtani's tenth win, the first snow of 2020 and Nostradamus's prophecy.
The revision relativizes world equivalence to an interval and an eventuality, and states the
truth conditions of *before* as three cases, veridical, false and modal.

## Main definitions

* `equivIE`: event-relative equivalence of worlds.
* `OST.before`: the revamped truth conditions of *before*.

## Main results

* `bc_cannot_place_bounded_complement`: forward-branching alternatives cannot place a bounded
  complement.
* `histAlt_subset_altIE_trivial`: the event-relative alternatives contain the branching ones.
* `beforeCase_modal_nonveridical`: the modal case is not veridical.
* `mozart_is_case_iii`: *Mozart died before he finished the Requiem* falls under the modal case.

## Implementation notes

The paper's third section draws a parallel between the modal case of *before* and the
English progressive under the imperfective paradox; the parallel is not formalized here,
the subinterval lemmas of `Aspect` stating the aspectual side on their own. The truth
conditions of the fourth section are, in the paper's words, very weak and in need of
strengthening by contextual and pragmatic factors; the fifth section's remaining problems
for the revamped proposal, the non-committal readings that contextual plausibility governs,
are recorded in the example rows only.

## References

* [ogihara-steinert-threlkeld-2024]
* [beaver-condoravdi-2003]
* [anscombe-1964]
* [heinamaki-1974]
* [landman-1992]
-/

@[expose] public section

namespace OgiharaSteinertThrelkeld2024

open Event (τ)

open OgiharaSteinertThrelkeld2024.Examples
open BeaverCondoravdi2003

/-- A counterexample to Beaver and Condoravdi's branching-time analysis has a complement bounded to
an interval that ends at or before the A-time, where alternatives branching only after that time
cannot place it. -/
structure BCCounterexampleDatum where
  /-- The example sentence. -/
  sentence : String
  /-- The A-clause time, such as the end of the season. -/
  aTime : ℤ
  /-- The upper bound of the complement's temporal window. -/
  complementUpperBound : ℤ
  /-- The complement is bounded before the A-time. -/
  boundedBefore : complementUpperBound ≤ aTime
  /-- The reading of Beaver and Condoravdi at issue. -/
  reading : BeforeReading

/-- When the complement is bounded at or before the A-time in every alternative at that time, no
alternative instantiates it after the A-time, so Beaver and Condoravdi's forward branching cannot
place a complement whose window closes before the A-time. -/
theorem bc_cannot_place_bounded_complement
    {W : Type*} (alt : HistoricalAlternatives W ℤ)
    (B : Set (W × ℤ)) (w : W) (tA hi : ℤ)
    (hBound : hi ≤ tA)
    (_hBounded : ∀ w' t, (w', t) ∈ B → t ≤ hi)
    (hNoFuture : ∀ w' ∈ alt ⟨w, tA⟩, ∀ t, (w', t) ∈ B → t ≤ hi) :
    ∀ te ∈ instTimes (alt ⟨w, tA⟩) B, te ≤ tA := by
  intro te ⟨w', _, hw'B⟩
  exact le_trans (hNoFuture w' ‹_› te hw'B) hBound

/-- In (20a), *Unfortunately, the 2021 MLB season will be over before Shohei Ohtani earns his 10th
win of the season*, uttered in mid-September 2021, the A-time is the end of the season, day 276,
and Ohtani's tenth win can only occur before it. -/
def ost_counterexample_ohtani : BCCounterexampleDatum where
  sentence := ost2024_ohtani.primaryText
  aTime := 276
  complementUpperBound := 275
  boundedBefore := by omega
  reading := .counterfactual

/-- In (20b), *2020 might come to an end before it snows for the first time this year*, uttered on
Christmas Day 2020, *this year* refers back to 2020, so the first snow can only occur in 2020 and
no snow after the end of the year can witness the modal reading. -/
def ost_counterexample_snow : BCCounterexampleDatum where
  sentence := ost2024_snow.primaryText
  aTime := 366
  complementUpperBound := 366
  boundedBefore := le_refl _
  reading := .nonCommittal

/-- In (20c), *July 1999 will come to an end before Nostradamus' prophecy about the end of the world
comes true*, uttered minutes before the end of July 1999, the prophecy can only come true in July
1999. -/
def ost_counterexample_nostradamus : BCCounterexampleDatum where
  sentence := ost2024_nostradamus.primaryText
  aTime := 31
  complementUpperBound := 31
  boundedBefore := le_refl _
  reading := .counterfactual

/-! ### The event-relative equivalence and alternatives (defs 17–18)

The paper's positive proposal replaces [beaver-condoravdi-2003]'s world–time
equivalence with one relative to an interval `I` and an eventuality `e`:
alternative worlds must contain a counterpart of `e` that co-occurs with it up
to `I`, and be identical at all earlier times. -/

section EventRelative

variable {W T : Type*} [LinearOrder T]

/-- A counterpart relation relates eventualities across worlds that share essential properties
such as starting time and thematic participants (fn. 18). -/
abbrev Counterpart (W T : Type*) := W → T → W → T → Prop

/-- Event-relative equivalence ≃_{I,e₁} (def 17) holds when a counterpart of `e₁` exists in `w₂`,
the two co-occur throughout [START(e₁), START(I)), and the worlds are identical at all earlier
times. -/
def equivIE (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI : T) (e₁_start : T) : Prop :=
  counterpart w₁ e₁_start w₂ e₁_start ∧
  coOccur w₁ e₁_start w₂ e₁_start e₁_start startI ∧
  (∀ t', t' < e₁_start → agree t' w₁ w₂)

/-- The event-relative alternatives alt(w, I, e) (def 18a) are the worlds event-relatively
equivalent to `w`. -/
def altIE (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (agree : T → W → W → Prop)
    (w : W) (startI : T) (e_start : T) : Set W :=
  { w' | equivIE counterpart coOccur agree w w' startI e_start }

/-- Event continuation (def 18b) keeps only the alternatives in which the
counterpart eventuality develops beyond `I`. -/
def eventContinuation (alt : Set W) (continues : W → Prop) : Set W :=
  { w' ∈ alt | continues w' }

/-- Event-relative equivalence is downward closed (def 18c), equivalence at `I` implying
equivalence at any earlier `I'`. -/
theorem equivIE_downward_closed (counterpart : Counterpart W T)
    (coOccur : W → T → W → T → T → T → Prop)
    (coOccur_mono : ∀ w₁ e₁ w₂ e₂ s₁ s₂ s₂',
      s₂' ≤ s₂ → coOccur w₁ e₁ w₂ e₂ s₁ s₂ → coOccur w₁ e₁ w₂ e₂ s₁ s₂')
    (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI startI' : T) (e_start : T)
    (hle : startI' ≤ startI)
    (h : equivIE counterpart coOccur agree w₁ w₂ startI e_start) :
    equivIE counterpart coOccur agree w₁ w₂ startI' e_start :=
  ⟨h.1, coOccur_mono w₁ e_start w₂ e_start e_start startI startI' hle h.2.1, h.2.2⟩

/-- With trivial counterpart and co-occurrence, ≃_{I,e} is agreement at all earlier times, Beaver
and Condoravdi's initial branch point condition for a pair of worlds. -/
theorem equivIE_trivial_iff_agree (agree : T → W → W → Prop)
    (w₁ w₂ : W) (startI e_start : T) :
    equivIE (fun _ _ _ _ ↦ True) (fun _ _ _ _ _ _ ↦ True) agree w₁ w₂ startI e_start ↔
    (∀ t', t' < e_start → agree t' w₁ w₂) := by
  simp [equivIE]

/-- Beaver and Condoravdi's alternatives over a T × W frame land inside the trivial event-relative
alternatives for agreement by the frame, so the event-relative equivalence generalizes Beaver and
Condoravdi's. -/
theorem histAlt_subset_altIE_trivial {F : Temporal.TWFrame W T} {B : Set (W × T)}
    (a : BeaverCondoravdi2003.Alternatives F B) (w : W) (t : T) :
    a.alt ⟨w, t⟩ ⊆ altIE (fun _ _ _ _ ↦ True) (fun _ _ _ _ _ _ ↦ True) (fun t ↦ F.sim t) w t t := by
  intro w' hw'
  rw [altIE, Set.mem_ofPred_eq, equivIE_trivial_iff_agree]
  exact fun _ ht' ↦ F.antitone_sim ht'.le (a.subset_alternatives _ hw')

end EventRelative

/-! The revamped truth conditions for *before* (def 19) use the event-relative alternatives and a
CAUSE relation. At ⟨w₀, I₀, e₀⟩ where A holds, ⟦A before B⟧ is true when B holds at a later
interval in w₀ (case i), false when B holds at an interval at or before I₀ in w₀ (case ii), and
otherwise true when I₀ precedes an interval at which, in an alternative for an eventuality
ongoing at I₀, the continuation of its counterpart causes a B-eventuality (case iii). -/

section Def19

variable {W T E : Type*} [LinearOrder T]

/-- Two intervals abut when the first ends where the second begins. -/
def abuts (I₀ I₁ : NonemptyInterval T) : Prop :=
  I₀.snd = I₁.fst

/-- `holdsAtAbutting e₁ I₀` says that the run time of `e₁` contains the start of `I₀`, so that `e₁`
is ongoing at `I₀`. -/
def holdsAtAbutting [Event.TemporalTrace E T] (e₁ : E) (I₀ : NonemptyInterval T) : Prop :=
  (τ e₁).fst ≤ I₀.fst ∧ I₀.fst ≤ (τ e₁).snd

/-- A situation denotation is a set of world–interval–eventuality triples. -/
abbrev SitDenot (W T E : Type*) [LinearOrder T] := Set (W × NonemptyInterval T × E)

/-- In case (i), ⟦A before B⟧ is true because B holds at some interval after I₀ in the actual
world w₀. -/
def beforeCase_veridical
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : NonemptyInterval T, I₀.snd < I₂.fst ∧
    ∃ e₄ : E, (w₀, I₂, e₄) ∈ B

/-- In case (ii), ⟦A before B⟧ is false because B holds at some interval at or before I₀ in the
actual world w₀. -/
def beforeCase_false
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : NonemptyInterval T, I₂.snd ≤ I₀.fst ∧
    ∃ e₅ : E, (w₀, I₂, e₅) ∈ B

/-- In the modal case (iii), ⟦A before B⟧ is true when A holds at ⟨w₀,I₀,e₀⟩ and I₀ precedes an
interval I₁ at which, in an alternative w₁ for an eventuality e₁ ongoing at I₀, a counterpart of
e₁ causes an eventuality e₃ with ⟨w₁, I₁, e₃⟩ ∈ ⟦B⟧. -/
def beforeCase_modal [Event.TemporalTrace E T]
    (A B : SitDenot W T E)
    (alt : W → NonemptyInterval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧
  ∃ I₁ : NonemptyInterval T,
    I₀.snd < I₁.fst ∧  -- I₀ precedes I₁
    ∃ e₁ : E,
      holdsAtAbutting e₁ I₀ ∧  -- e₁ ongoing at I₀
      ∃ w₁ ∈ alt w₀ I₀ e₁,  -- alternative world
        ∃ e₂ : E,
          counterpart w₀ e₁ w₁ e₂ ∧  -- e₂ is counterpart of e₁
          ∃ e₃ : E,
            cause w₁ e₂ e₃ ∧  -- continuation of e₂ CAUSES e₃
            (w₁, I₁, e₃) ∈ B  -- B holds at ⟨w₁, I₁, e₃⟩

/-- The revamped *before* (def 19) holds when case (ii) fails and case (i) or the modal case (iii)
holds. -/
def OST.before [Event.TemporalTrace E T]
    (A B : SitDenot W T E)
    (alt : W → NonemptyInterval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  ¬beforeCase_false A B w₀ I₀ e₀ ∧
  (beforeCase_veridical A B w₀ I₀ e₀ ∨
   beforeCase_modal A B alt cause counterpart w₀ I₀ e₀)

/-- Case (i) is veridical, the complement occurring after I₀ in the actual world. -/
theorem beforeCase_veridical_entails_complement
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) :
    beforeCase_veridical A B w₀ I₀ e₀ → ∃ I e, (w₀, I, e) ∈ B := by
  rintro ⟨_, I₂, _, e₄, hB⟩
  exact ⟨I₂, e₄, hB⟩

/-- The modal case is not veridical, as a model shows in which the main clause holds only at the
actual world `false` and the complement only at the alternative `true`. -/
theorem beforeCase_modal_nonveridical :
    ∃ (A B : SitDenot Bool ℤ (NonemptyInterval ℤ))
      (alt : Bool → NonemptyInterval ℤ → NonemptyInterval ℤ → Set Bool)
      (cause : Bool → NonemptyInterval ℤ → NonemptyInterval ℤ → Prop)
      (counterpart : Bool → NonemptyInterval ℤ → Bool → NonemptyInterval ℤ → Prop)
      (w₀ : Bool) (I₀ e₀ : NonemptyInterval ℤ),
    beforeCase_modal A B alt cause counterpart w₀ I₀ e₀ ∧ ¬∃ I e, (w₀, I, e) ∈ B := by
  refine ⟨{(false, .pure 0, .pure 0)}, {(true, .pure 2, .pure 2)}, fun _ _ _ ↦ {true},
    fun _ _ _ ↦ True, fun _ _ _ _ ↦ True, false, .pure 0, .pure 0, ?_, ?_⟩
  · exact ⟨rfl, .pure 2, by decide, ⟨(-1, 0), by decide⟩, ⟨by decide, by decide⟩, true, rfl,
      .pure 2, trivial, .pure 2, trivial, rfl⟩
  · rintro ⟨I, e, hB⟩
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hB
    exact absurd hB.1 Bool.false_ne_true

/-- Cases (i) and (ii) exclude each other for a complement at a single interval, which cannot lie
both after and before I₀. -/
theorem cases_i_ii_exclusive
    (I₀ I_B : NonemptyInterval T)
    (hAfter : I₀.snd < I_B.fst)
    (hBefore : I_B.snd ≤ I₀.fst) :
    False := by
  have : I_B.snd < I_B.fst := lt_of_le_of_lt hBefore (lt_of_le_of_lt I₀.fst_le_snd hAfter)
  exact absurd this (not_lt.mpr I_B.fst_le_snd)

/-- With no finishing in the actual world and the modal case holding, the revamped *before* holds,
so *Mozart died before he finished the Requiem* has the anti-veridical reading of case (iii). -/
theorem mozart_is_case_iii
    {W E : Type*} [Event.TemporalTrace E ℤ]
    (A B : SitDenot W ℤ E)
    (alt : W → NonemptyInterval ℤ → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval ℤ) (e₀ : E)
    (hNoFinish : ¬∃ I e, (w₀, I, e) ∈ B)
    (hModal : beforeCase_modal A B alt cause counterpart w₀ I₀ e₀) :
    OST.before A B alt cause counterpart w₀ I₀ e₀ := by
  refine ⟨?_, Or.inr hModal⟩
  intro ⟨_, I₂, _, e₅, hB⟩
  exact hNoFinish ⟨I₂, e₅, hB⟩

end Def19

end OgiharaSteinertThrelkeld2024
