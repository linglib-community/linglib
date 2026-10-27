module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Data.Examples.Dowty1979

/-!
# Dowty (1979): the progressive and the imperfective paradox

In interval semantics a sentence is true at an interval of a world, and the progressive of a
sentence is true at an interval that a longer interval of the sentence's truth extends into the
future. On Bennett and Partee's analysis the longer interval lies in the same world, so *John was
drawing a circle* entails *John drew a circle*, [the imperfective
paradox](##exists_mem_of_mem_bennettPartee), and *John was watching television when he fell asleep*
(28) requires the watching to have gone on after he fell asleep. Dowty makes the progressive
modal. A first version (24) asks for some world exactly like the actual one up to the interval
where the sentence is true at the longer interval, which [gets (28) right](##truthValue_rows) but
makes both *the coin is coming up heads* and *the coin is coming up tails* true of a coin in the
air. The final version (25) quantifies over the inertia worlds, a primitive of the model: worlds
exactly like the actual one up to the interval, in which events then take their natural course. A
single longer interval must be one of the sentence's truth in every inertia world, so the coin
comes up neither heads nor tails, and Bennett and Partee's progressive is [the case where the
actual world is the only inertia world](##prog_singleton).

For activities, true at every subinterval larger than a moment of an interval of their truth,
the progressive at an interval larger than a moment [entails the activity
there](##mem_of_mem_prog), since the inertia worlds agree with the actual one up to it. Dowty
observes that the entailment from *x is V-ing* to *x has V-ed* still fails for activities, like
waltzing, whose shortest intervals are long, since the progressive holds within the first of
them.

## Implementation notes

* Dowty's relation of an interval to a longer one, "`I ⊂ I'` and `I` is not a final subinterval for
  `I'`", is `NonemptyInterval.NonfinalSubinterval` (`NonemptyInterval.nonfinalSubinterval_iff`).
* Sentences are sets of intervals at each world, the interval properties the aspect operators of
  the event semantics produce. Time is a linear order; the scenarios use the natural numbers, where
  Dowty takes the reals.
* *Exactly like up to a time* is `HistoricalAlternatives`. Inertia worlds are an arbitrary
  function of a world and an interval; the theorems that need them to be historical alternatives
  take that as a hypothesis, together with the agreement of the sentence on intervals up to the
  time.
* Dowty's branching-time progressive (p. 152) is stated over histories, which p. 153 lets take the
  role of worlds; `branchingProg` reads it so.

## Errata

* The branching-time progressive (p. 152) takes, for each inertia history, some longer interval of
  the sentence's truth, while (25) fixes one longer interval for every inertia world. The first is
  strictly weaker ([they differ](##not_branchingProg_subset_prog)): when the inertia worlds
  complete a circle at different times, it makes *John is drawing a circle* true and (25) false.
  So the choice between the two formalizations matters for the progressive, contrary to p. 154.
  The branching definition also drops (25)'s requirement that the interval not be a final
  subinterval of the longer one, which its own gloss on p. 151 ("extending into some ... possible
  future") presupposes.

## TODO

* BECOME (11), (11'), Cresswell's AND (19), the futurate progressive of §3.7 and the stative
  progressives of §3.8.2 are not formalized.

## References

* [dowty-1979]
* [bennett-partee-1972]
* [taylor-1977]
-/

@[expose] public section

namespace Dowty1979

/-! ### Interval semantics -/

section Defs

variable {W T : Type*} [LinearOrder T]

/-- A sentence is true at some intervals of each world. -/
abbrev Sentence (W T : Type*) [LE T] := W → Set (NonemptyInterval T)

/-- Bennett and Partee's progressive (p. 145): some longer interval of the sentence's truth extends
the interval into the future. -/
def bennettPartee (φ : Sentence W T) : Sentence W T :=
  fun w ↦ {I | ∃ I', I.NonfinalSubinterval I' ∧ I' ∈ φ w}

/-- The progressive (24): the sentence is true at a longer interval of some world exactly like the
actual one up to the interval. -/
def possibleProg (history : HistoricalAlternatives W T) (φ : Sentence W T) : Sentence W T :=
  fun w ↦ {I | ∃ I', I.NonfinalSubinterval I' ∧ ∃ w' ∈ history.metaphysicalBase w I.snd, I' ∈ φ w'}

/-- The progressive (25): some longer interval is one of the sentence's truth in every inertia
world for the world and the interval. -/
def prog (inertia : W → NonemptyInterval T → Set W) (φ : Sentence W T) : Sentence W T :=
  fun w ↦ {I | ∃ I', I.NonfinalSubinterval I' ∧ ∀ w' ∈ inertia w I, I' ∈ φ w'}

/-- The branching-time progressive (p. 152), histories read as worlds: in each inertia world some
interval of which the interval is a proper subinterval is one of the sentence's truth. -/
def branchingProg (inertia : W → NonemptyInterval T → Set W) (φ : Sentence W T) :
    Sentence W T :=
  fun w ↦ {I | ∀ w' ∈ inertia w I, ∃ I', I < I' ∧ I' ∈ φ w'}

variable {φ : Sentence W T} {w : W} {I : NonemptyInterval T}

/-- Bennett and Partee's progressive is (25) with the actual world as its only inertia world. -/
theorem prog_singleton (φ : Sentence W T) : prog (fun w _ ↦ {w}) φ = bennettPartee φ := by
  ext w I
  simp [prog, bennettPartee]

/-- On Bennett and Partee's analysis the progressive of a sentence entails that the sentence is
true at some interval of the actual world. -/
theorem exists_mem_of_mem_bennettPartee (h : I ∈ bennettPartee φ w) : ∃ I', I' ∈ φ w :=
  let ⟨I', _, hI'⟩ := h; ⟨I', hI'⟩

theorem prog_subset_branchingProg (inertia : W → NonemptyInterval T → Set W) :
    prog inertia φ w ⊆ branchingProg inertia φ w :=
  fun _ ⟨I', hI', h⟩ w' hw' ↦ ⟨I', hI'.lt, h w' hw'⟩

/-- An activity true at an interval is true at its subintervals larger than a moment (Taylor's
(57), p. 166). When the inertia worlds are exactly like the actual one up to an interval larger
than a moment, and the activity's truth at that interval is a fact of history, the progressive of
the activity there entails the activity. -/
theorem mem_of_mem_prog {history : HistoricalAlternatives W T}
    {inertia : W → NonemptyInterval T → Set W}
    (hInr : ∀ w I, inertia w I ⊆ history.metaphysicalBase w I.snd)
    (hagree : ∀ v ∈ history.metaphysicalBase w I.snd, I ∈ φ v ↔ I ∈ φ w)
    (hsub : ∀ v J J', J ≤ J' → ¬ J.IsPoint → J' ∈ φ v → J ∈ φ v)
    (hne : (inertia w I).Nonempty) (hI : ¬ I.IsPoint) (h : I ∈ prog inertia φ w) : I ∈ φ w :=
  let ⟨v, hv⟩ := hne
  let ⟨_, hI', hall⟩ := h
  (hagree v (hInr w I hv)).1 (hsub v I _ hI'.1 hI (hall v hv))

end Defs

/-! ### Scenarios

Time is the natural numbers, and worlds are `Bool`. -/

/-- The interval `[a, b]` of natural numbers. -/
def iv (a b : ℕ) (h : a ≤ b := by decide) : NonemptyInterval ℕ := ⟨(a, b), h⟩

@[simp] theorem iv_fst (a b : ℕ) (h : a ≤ b) : (iv a b h).fst = a := rfl

@[simp] theorem iv_snd (a b : ℕ) (h : a ≤ b) : (iv a b h).snd = b := rfl

theorem nonfinalSubinterval_iv {a b c d : ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) (hca : c ≤ a)
    (hbd : b < d) : (iv a b h₁).NonfinalSubinterval (iv c d h₂) :=
  ⟨NonemptyInterval.le_def.2 ⟨hca, hbd.le⟩, hbd⟩

/-- Worlds alike up to time `0` and different afterwards. -/
def splitAfterZero : HistoricalAlternatives Bool ℕ :=
  fun i ↦ if i.2 = 0 then Set.univ else {i.1}

/-! #### A coin in the air (pp. 147–148)

In world `true` the coin comes up heads over `[0, 1]`, in world `false` tails. Both worlds are
alike at `0`, and both outcomes are a natural course of events, so both are inertia worlds. -/

/-- *The coin comes up heads* is true of `[0, 1]` in the heads world. -/
def heads : Sentence Bool ℕ := fun w ↦ {I | w = true ∧ I = iv 0 1}

/-- *The coin comes up tails* is true of `[0, 1]` in the tails world. -/
def tails : Sentence Bool ℕ := fun w ↦ {I | w = false ∧ I = iv 0 1}

theorem possibleProg_heads (w : Bool) : iv 0 0 ∈ possibleProg splitAfterZero heads w :=
  ⟨iv 0 1, nonfinalSubinterval_iv _ _ le_rfl (by decide), true,
    by simp [HistoricalAlternatives.metaphysicalBase, splitAfterZero], rfl, rfl⟩

theorem not_prog_heads (w : Bool) : iv 0 0 ∉ prog (fun _ _ ↦ Set.univ) heads w :=
  fun ⟨_, _, h⟩ ↦ absurd (h false trivial).1 (by decide)

theorem not_prog_tails (w : Bool) : iv 0 0 ∉ prog (fun _ _ ↦ Set.univ) tails w :=
  fun ⟨_, _, h⟩ ↦ absurd (h true trivial).1 (by decide)

/-! #### Falling asleep in front of the television (28)

In world `true` John watches television over `[0, 1]` and falls asleep at `1`; in world `false`,
exactly like it up to `1`, he watches on until `3`. Watching is true at every subinterval of the
watching. -/

/-- *John watches television* is true at the intervals within the watching. -/
def watch : Sentence Bool ℕ := fun w ↦ {I | I.snd ≤ if w then 1 else 3}

/-- Worlds alike up to time `1`. -/
def splitAfterOne : HistoricalAlternatives Bool ℕ :=
  fun i ↦ if i.2 ≤ 1 then Set.univ else {i.1}

theorem not_bennettPartee_watch : iv 1 1 ∉ bennettPartee watch true :=
  fun ⟨_, hI', h⟩ ↦ absurd (hI'.2.trans_le h) (by simp)

theorem possibleProg_watch : iv 1 1 ∈ possibleProg splitAfterOne watch true :=
  ⟨iv 0 3, nonfinalSubinterval_iv _ _ (by decide) (by decide), false, by
    simp [HistoricalAlternatives.metaphysicalBase, splitAfterOne], by simp [watch]⟩

/-! #### A circle completed at different times

Both worlds are inertia worlds, and the drawing of the circle is completed over `[0, 1]` in one
and over `[0, 2]` in the other. -/

/-- *John draws a circle* is true of the whole drawing only. -/
def drawCircle : Sentence Bool ℕ := fun w ↦ {I | I = if w then iv 0 1 else iv 0 2}

/-- The branching-time progressive is strictly weaker than (25). -/
theorem not_branchingProg_subset_prog :
    ¬ branchingProg (fun _ _ ↦ Set.univ) drawCircle true ⊆
      prog (fun _ _ ↦ Set.univ) drawCircle true := by
  intro h
  have hb : iv 0 0 ∈ branchingProg (fun _ _ ↦ Set.univ) drawCircle true := by
    rintro (_ | _) -
    · exact ⟨iv 0 2, (nonfinalSubinterval_iv _ _ le_rfl (by decide)).lt, rfl⟩
    · exact ⟨iv 0 1, (nonfinalSubinterval_iv _ _ le_rfl (by decide)).lt, rfl⟩
  obtain ⟨I', -, hall⟩ := h hb
  have h1 : I' = iv 0 1 := hall true trivial
  have h2 : I' = iv 0 2 := hall false trivial
  exact absurd (h1.symm.trans h2) (by decide)

/-! #### Waltzing (p. 172)

Waltzing is true only of intervals of at least three steps, within the waltz from `0` to `6`. -/

/-- *x waltzes* is true of the intervals of at least three steps within `[0, 6]`. -/
def waltz : Sentence Unit ℕ := fun _ ↦ {I | I.fst + 3 ≤ I.snd ∧ I.snd ≤ 6}

theorem prog_waltz_not_past :
    iv 0 1 ∈ prog (fun w _ ↦ {w}) waltz () ∧ ∀ J, J.snd ≤ 1 → J ∉ waltz () := by
  refine ⟨⟨iv 0 3, nonfinalSubinterval_iv _ _ (by decide) (by decide),
    fun _ _ ↦ ⟨le_rfl, by decide⟩⟩, fun J hJ h ↦ ?_⟩
  have := h.1
  omega

/-! ### The paper's judgments -/

/-- (24) gets the television right where Bennett and Partee's analysis does not, and (25) gets the
coin right where (24) does not. -/
theorem truthValue_rows :
    (iv 0 0 ∈ prog (fun _ _ ↦ Set.univ) heads true ↔
        Examples.coin_heads.feature? "truthValue" = some "true") ∧
      (iv 0 0 ∈ prog (fun _ _ ↦ Set.univ) tails true ↔
        Examples.coin_tails.feature? "truthValue" = some "true") ∧
      (iv 1 1 ∈ possibleProg splitAfterOne watch true ↔
        Examples.ex28.feature? "truthValue" = some "true") ∧
      ¬ (iv 0 0 ∈ possibleProg splitAfterZero heads true ↔
        Examples.coin_heads.feature? "truthValue" = some "true") ∧
      ¬ (iv 1 1 ∈ bennettPartee watch true ↔
        Examples.ex28.feature? "truthValue" = some "true") :=
  ⟨iff_of_false (not_prog_heads true) (by decide), iff_of_false (not_prog_tails true) (by decide),
    iff_of_true possibleProg_watch (by decide),
    fun h ↦ absurd (h.1 (possibleProg_heads true)) (by decide),
    fun h ↦ not_bennettPartee_watch (h.2 (by decide))⟩

end Dowty1979
