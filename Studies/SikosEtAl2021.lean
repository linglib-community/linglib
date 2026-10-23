module

public import Studies.FrankGoodman2012

/-!
# Sikos, Venhuizen, Drenhaus and Crocker (2021): Reevaluating Pragmatic Reasoning in Language Games

Sikos and colleagues compare Frank and Goodman's rational speech act model with a baseline in
one-shot reference games. The baseline keeps the Bayesian listener but replaces the informative
speaker by literal meaning alone, a uniform choice among the words true of the referent, so it
weighs the objects a word is true of by the prior alone. The two models differ only in the
pragmatic conditions, the pairs of a context and a word in which the informative speaker's use
of the word varies across the objects it is true of. A pragmatic condition is solvable when the
listener then has a single favourite and reducible when it only excludes a competitor.

## Main statements

* `tendsto_speaker_baselineSpeaker`: the baseline speaker is the informative speaker's limit as
  the rationality goes to zero, the sense in which the baseline is the model at `α = 0`.
* `baselineListener_real_singleton_lt_iff`: among the objects a word is true of, the baseline
  listener follows the prior.
* `pragmatic_iff`, `not_pragmatic_iff`: a condition is pragmatic exactly when two objects the
  word is true of share their other feature with different numbers of objects, and otherwise a
  listener with a uniform prior is as indifferent as the baseline.
* `solvable_blue`, `solvable_boot`, `reducible_blue`: the conditions of the paper's tables are
  solvable and reducible at every positive rationality, and `not_pragmatic_boot` is an ambiguous
  one.

## Implementation notes

* Fit statistics stay in prose. Across three experiments the baseline fit listener choices at
  least as well as the model overall; the model fit better only for a colour word in
  pragmatically solvable contexts (Experiments 2 and 3), and in the pragmatically reducible
  contexts listeners chose the salient competitor, which the model predicts only because the
  prior reverses its speaker's preference. The theory predicts where the models can differ, not
  which fits better.
* The model's listener at a prior is `FrankGoodman2012.listener`, and its preference between
  two objects compares prior mass times speaker probability (`RSA.listener_real_singleton_lt_iff`),
  so a salient competitor wins exactly when its prior advantage exceeds the speaker's ratio.
* The condition types are defined at a uniform prior, as the paper's figure of conditions is.

## References

* [sikos-etal-2021]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Semantics Filter
open FrankGoodman2012 (Attribute Colour Word speaker listener)
open scoped ENNReal Topology Semantics.Superscript

namespace SikosEtAl2021

variable {E C S : Type} [DecidableEq C] [DecidableEq S] [Fintype E] [Fintype C] [Fintype S]
  [MeasurableSpace E] [DiscreteMeasurableSpace E] (M : E → (a : Attribute) → a.Value C S)

/-! ### The baseline -/

section Baseline

variable [DecidableEq E] {w : Word C S} {r r' : E}

/-- The baseline speaker (4) uses literal meaning alone, a uniform choice among the words true
of the referent. -/
noncomputable def baselineSpeaker : Kernel E (Word C S) :=
  Kernel.ofWeights fun r w ↦ if r ∈ ⟦w⟧ᴹ then 1 else 0

instance : IsFiniteKernel (baselineSpeaker M) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The baseline listener (4) inverts the baseline speaker against the prior. -/
noncomputable def baselineListener (P : Measure E) : Kernel (Word C S) E :=
  RSA.listener P (baselineSpeaker M)

theorem baselineSpeaker_real_singleton (r : E) (w : Word C S) :
    (baselineSpeaker M r).real {w} = (if r ∈ ⟦w⟧ᴹ then 1 else 0) / 2 := by
  have hsum : (∑ w' : Word C S, if r ∈ ⟦w'⟧ᴹ then (1 : ℝ≥0∞) else 0) = 2 := by
    rw [Finset.sum_boole, FrankGoodman2012.filter_mem_denote, Finset.card_pair (by simp)]
    rfl
  rw [measureReal_def, baselineSpeaker, Kernel.ofWeights_apply_singleton, hsum,
    ENNReal.toReal_div]
  split_ifs <;> simp

/-- The baseline speaker is the informative speaker's limit as the rationality goes to zero. -/
theorem tendsto_speaker_baselineSpeaker (r : E) (w : Word C S) :
    Tendsto (fun α : ℝ ↦ (speaker M α r).real {w}) (𝓝[>] 0)
      (𝓝 ((baselineSpeaker M r).real {w})) := by
  have h := RSA.tendsto_speaker_uniformOn_dirac_real_singleton_nhdsGT_zero
    (fun w : Word C S ↦ ⟦w⟧ᴹ) r w
  rwa [FrankGoodman2012.filter_mem_denote, Finset.card_pair (by simp), Nat.cast_ofNat,
    ← baselineSpeaker_real_singleton] at h

/-- Among the objects a word is true of, the baseline listener follows the prior. -/
theorem baselineListener_real_singleton_lt_iff (P : Measure E) [IsFiniteMeasure P]
    (h : r ∈ ⟦w⟧ᴹ) (h' : r' ∈ ⟦w⟧ᴹ) :
    (baselineListener M P w).real {r'} < (baselineListener M P w).real {r} ↔
      P.real {r'} < P.real {r} := by
  rw [baselineListener, RSA.listener_real_singleton_lt_iff, baselineSpeaker_real_singleton,
    baselineSpeaker_real_singleton, ite_eq_left h, ite_eq_left h']
  exact mul_lt_mul_iff_of_pos_right (by norm_num)

end Baseline

/-! ### The pragmatic conditions -/

variable {α : ℝ} {w : Word C S}

/-- A condition, a word in a context, is pragmatic when a listener with a uniform prior is not
indifferent among the objects the word is true of. -/
def Pragmatic (α : ℝ) (w : Word C S) : Prop :=
  ∃ r ∈ ⟦w⟧ᴹ, ∃ r' ∈ ⟦w⟧ᴹ,
    (listener M Measure.count α w).real {r'} < (listener M Measure.count α w).real {r}

/-- A pragmatic condition is solvable when the listener has a single favourite among the objects
the word is true of. -/
def PragmaticallySolvable (α : ℝ) (w : Word C S) : Prop :=
  Pragmatic M α w ∧ ∃ r ∈ ⟦w⟧ᴹ, ∀ r' ∈ ⟦w⟧ᴹ, r' ≠ r →
    (listener M Measure.count α w).real {r'} < (listener M Measure.count α w).real {r}

/-- A pragmatic condition is reducible when it is not solvable, so that the listener excludes a
competitor and stays undecided among the rest. -/
def PragmaticallyReducible (α : ℝ) (w : Word C S) : Prop :=
  Pragmatic M α w ∧ ¬ PragmaticallySolvable M α w

/-- Outside the pragmatic conditions a listener with a uniform prior is indifferent among the
objects the word is true of, as the baseline listener is. -/
theorem not_pragmatic_iff :
    ¬ Pragmatic M α w ↔ ∀ r ∈ ⟦w⟧ᴹ, ∀ r' ∈ ⟦w⟧ᴹ,
      (listener M Measure.count α w).real {r'} = (listener M Measure.count α w).real {r} := by
  simp only [Pragmatic, not_exists, not_and, not_lt]
  exact ⟨fun h r hr r' hr' ↦ le_antisymm (h r' hr' r hr) (h r hr r' hr'),
    fun h r hr r' hr' ↦ (h r hr r' hr').ge⟩

section Characterization

variable [DecidableEq E] {r r' : E}

private theorem listener_count_lt_iff (hα : 0 < α) (h : r ∈ ⟦w⟧ᴹ) (h' : r' ∈ ⟦w⟧ᴹ)
    {b : Attribute} (hb : b ≠ w.1) :
    (listener M Measure.count α w).real {r'} < (listener M Measure.count α w).real {r} ↔
      ⟦(⟨b, M r' b⟩ : Word C S)⟧ᴹ.card < ⟦(⟨b, M r b⟩ : Word C S)⟧ᴹ.card :=
  FrankGoodman2012.listener_real_singleton_lt_iff M hα Measure.count h h' (by simp) (by simp) hb

/-- A condition is pragmatic exactly when two objects the word is true of share their other
feature with different numbers of objects. -/
theorem pragmatic_iff (hα : 0 < α) {b : Attribute} (hb : b ≠ w.1) :
    Pragmatic M α w ↔ ∃ r ∈ ⟦w⟧ᴹ, ∃ r' ∈ ⟦w⟧ᴹ,
      ⟦(⟨b, M r' b⟩ : Word C S)⟧ᴹ.card < ⟦(⟨b, M r b⟩ : Word C S)⟧ᴹ.card := by
  refine exists_congr fun r ↦ and_congr_right fun h ↦ exists_congr fun r' ↦
    and_congr_right fun h' ↦ listener_count_lt_iff M hα h h' hb

theorem pragmaticallySolvable_iff (hα : 0 < α) {b : Attribute} (hb : b ≠ w.1) :
    PragmaticallySolvable M α w ↔ Pragmatic M α w ∧ ∃ r ∈ ⟦w⟧ᴹ, ∀ r' ∈ ⟦w⟧ᴹ, r' ≠ r →
      ⟦(⟨b, M r' b⟩ : Word C S)⟧ᴹ.card < ⟦(⟨b, M r b⟩ : Word C S)⟧ᴹ.card := by
  refine and_congr_right fun _ ↦ exists_congr fun r ↦ and_congr_right fun h ↦
    forall_congr' fun r' ↦ forall_congr' fun h' ↦ forall_congr' fun _ ↦
      listener_count_lt_iff M hα h h' hb

end Characterization

/-! ### The conditions of the tables -/

/-- The shapes of the examples. -/
inductive Shape
  | boot | mitt
  deriving DecidableEq, Fintype, Repr

/-- The objects of a pragmatically solvable context (Tables 5 and 9). -/
inductive SolvableObject
  | referent | colourCompetitor | shapeCompetitor
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace SolvableObject := ⊤
instance : DiscreteMeasurableSpace SolvableObject := ⟨fun _ ↦ trivial⟩

/-- The pragmatically solvable context of Tables 5 and 9 has a blue boot, the pragmatic
referent, a blue mitt and a green boot. -/
def solvable : SolvableObject → (a : Attribute) → a.Value Colour Shape
  | .referent, .colour => Colour.blue
  | .referent, .shape => Shape.boot
  | .colourCompetitor, .colour => Colour.blue
  | .colourCompetitor, .shape => Shape.mitt
  | .shapeCompetitor, .colour => Colour.green
  | .shapeCompetitor, .shape => Shape.boot

/-- On hearing *blue* the listener singles out the blue boot, since for the blue mitt the speaker
had the more informative *mitt*. -/
theorem solvable_blue (hα : 0 < α) :
    PragmaticallySolvable solvable α (⟨.colour, Colour.blue⟩ : Word Colour Shape) :=
  (pragmaticallySolvable_iff solvable hα (b := .shape) (by decide)).2
    ⟨(pragmatic_iff solvable hα (b := .shape) (by decide)).2 (by decide), by decide⟩

/-- On hearing *boot* the listener singles out the blue boot as well. -/
theorem solvable_boot (hα : 0 < α) :
    PragmaticallySolvable solvable α (⟨.shape, Shape.boot⟩ : Word Colour Shape) :=
  (pragmaticallySolvable_iff solvable hα (b := .colour) (by decide)).2
    ⟨(pragmatic_iff solvable hα (b := .colour) (by decide)).2 (by decide), by decide⟩

/-- The objects of a pragmatically reducible context (Tables 4 and 8). -/
inductive ReducibleObject
  | referent₁ | referent₂ | competitor
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace ReducibleObject := ⊤
instance : DiscreteMeasurableSpace ReducibleObject := ⟨fun _ ↦ trivial⟩

/-- The pragmatically reducible context of Tables 4 and 8 has two blue boots, the pragmatic
referents, and a blue mitt. -/
def reducible : ReducibleObject → (a : Attribute) → a.Value Colour Shape
  | .referent₁, .colour => Colour.blue
  | .referent₁, .shape => Shape.boot
  | .referent₂, .colour => Colour.blue
  | .referent₂, .shape => Shape.boot
  | .competitor, .colour => Colour.blue
  | .competitor, .shape => Shape.mitt

/-- On hearing *blue* the listener excludes the blue mitt and stays undecided between the two
boots. -/
theorem reducible_blue (hα : 0 < α) :
    PragmaticallyReducible reducible α (⟨.colour, Colour.blue⟩ : Word Colour Shape) :=
  ⟨(pragmatic_iff reducible hα (b := .shape) (by decide)).2 (by decide),
    fun h ↦ absurd ((pragmaticallySolvable_iff reducible hα (b := .shape) (by decide)).1 h).2
      (by decide)⟩

/-- On hearing *boot* the listener is indifferent between the two boots, an ambiguous condition
in which the model and the baseline agree. -/
theorem not_pragmatic_boot (hα : 0 < α) :
    ¬ Pragmatic reducible α (⟨.shape, Shape.boot⟩ : Word Colour Shape) :=
  fun h ↦ absurd ((pragmatic_iff reducible hα (b := .colour) (by decide)).1 h) (by decide)

end SikosEtAl2021
