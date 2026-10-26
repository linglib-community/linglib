module

public import Linglib.Data.Examples.KehlerRohde2013
public import Linglib.Data.Experiments.KehlerRohde2013
public import Linglib.Data.UD.UPOS
public import Linglib.Data.UD.Features
public import Linglib.Discourse.Coherence
public import Linglib.Discourse.Centering.Basic
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Discourse.Accessibility
public import Linglib.Fragments.English.Pronouns
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Kehler and Rohde (2013): A Probabilistic Reconciliation of Coherence-Driven and Centering-Driven Theories of Pronoun Interpretation

This file formalizes the Bayesian model of pronoun interpretation of [kehler-rohde-2013]: the
interpreter's bias `P(referent | pronoun)` is proportional to the speaker's production bias
`P(pronoun | referent)` times the next-mention prior `P(referent)` (the paper's (11) and (13)),
the prior is the mixture of the relation-conditioned biases weighted by the expected coherence
relations ((9)), and coherence expectations are in turn the mixture over the referent mentioned
next ((12)). The consequences the paper draws are proved once: a shift in the expected relations
with the conditional biases held fixed shifts the prior (`mixture_sub`), and only then
(`mixture_const`); a referent pronominalized above the overall rate is the pronoun's referent
above its prior, the overlaid subject bias (`posterior_gt_iff`); and raising a referent's
next-mention probability raises the expectation of the relations that favor it
(`relationExpectation_sub`).

The paper's passage-completion results (Tables 1–10, `Data/Experiments/KehlerRohde2013`) then
instantiate the model. The instruction manipulation's mixtures computed from Tables 3 and 4 fall
on the sides of chance Table 5 observes (`instruction_mixtures`); the pronoun prompt raises
subject mentions and shifts the continuations toward the Source-biased relations (Table 6); the
voice manipulation's Bayesian predictions computed from Tables 7 and 9 favor the subject in both
voices, more in the active, as Table 10 observes (`voice_predictions`), though below the
predictions Table 10 prints (`bayesSubject_lt_predicted`); and the pronominalization
rates of Table 9 increase with topichood, the passive subject above the active subject above the
non-subjects, a gradient the backward-looking center of a grammatical-role Centering cannot see
(`cb_topichood_dissociation_under_voice`).

## Implementation notes

The tables are `Data/Experiments/KehlerRohde2013`, whose proportions are printed to two places
and read here in percent (`Decimal.hundredths`); computed quantities are compared through their
integer numerators. The mixtures (9) range over the five relations the paper codes, whose
frequencies fall short of one by the continuations coded otherwise.

## References

* [kehler-rohde-2013]
* [hobbs-1979]
* [grosz-joshi-weinstein-1995]
* [davison-1984]
-/

@[expose] public section

namespace KehlerRohde2013

open Discourse.Centering Finset
open Discourse.AccessibilityLevel (Head)
open Morphology (Word Features)

/-! ### The Bayesian model -/

section Model

variable {C R : Type*}

/-- (9): the next-mention probability of a referent as the mixture of its relation-conditioned
probabilities, weighted by the probabilities of the relations. -/
def mixture [Fintype C] (pCR bias : C → ℚ) : ℚ := ∑ c, pCR c * bias c

theorem mixture_sub [Fintype C] (p q bias : C → ℚ) :
    mixture q bias - mixture p bias = ∑ c, (q c - p c) * bias c := by
  simp only [mixture, ← sum_sub_distrib, sub_mul]

theorem mixture_const [Fintype C] (p : C → ℚ) (hp : ∑ c, p c = 1) (b : ℚ) :
    mixture p (fun _ ↦ b) = b := by
  simp only [mixture, ← sum_mul, hp, one_mul]

/-- (12): the probability of a coherence relation as the mixture over the referent mentioned
next. -/
def relationExpectation [Fintype R] (pRef : R → ℚ) (crGiven : R → C → ℚ) (c : C) : ℚ :=
  ∑ r, pRef r * crGiven r c

theorem relationExpectation_sub [Fintype R] (p q : R → ℚ) (crGiven : R → C → ℚ) (c : C) :
    relationExpectation q crGiven c - relationExpectation p crGiven c =
      ∑ r, (q r - p r) * crGiven r c := by
  simp only [relationExpectation, ← sum_sub_distrib, sub_mul]

/-- (11), (13): the interpreter's posterior over referents, the production bias times the
next-mention prior, normalized by the overall probability of a pronoun. -/
def posterior [Fintype R] (pRef pPron : R → ℚ) (r : R) : ℚ :=
  pPron r * pRef r / ∑ r', pPron r' * pRef r'

theorem posterior_gt_iff [Fintype R] (pRef pPron : R → ℚ) (r : R) (hr : 0 < pRef r)
    (hZ : 0 < ∑ r', pPron r' * pRef r') :
    pRef r < posterior pRef pPron r ↔ ∑ r', pPron r' * pRef r' < pPron r := by
  rw [posterior, lt_div_iff₀ hZ, mul_comm (pPron r), mul_lt_mul_iff_right₀ hr]

end Model

/-! ### The data -/

/-- The voice as UD codes it. -/
def Voice.toUD : Voice → UD.Voice
  | .active => .Act
  | .passive => .Pass

/-- A function on positions by its two values. -/
def Position.select {α : Type*} (s n : α) : Position → α
  | .subject => s
  | .nonSubject => n

private theorem sum_position (f : Position → ℚ) : ∑ p, f p = f .subject + f .nonSubject := by
  rw [show (univ : Finset Position) = {.subject, .nonSubject} from by decide,
    sum_pair (by decide)]

/-! ### Coherence-conditioned biases (Tables 1–5) -/

/-- Table 1: the Source interpretation rate by aspect. -/
def aspectSource (a : Aspect) : ℕ := (sourceByAspect a).sourceInterpretation.hundredths.toNat

theorem imperfective_more_source : aspectSource .perfective < aspectSource .imperfective := by
  decide

/-- Table 2: the frequency of a relation in the perfective continuations. -/
def perfectiveFrequency (c : Relation) : ℕ := (relationsPerfective c).frequency.hundredths.toNat

/-- Table 2: the Source bias of a relation in the perfective continuations. -/
def perfectiveSourceGiven (c : Relation) : ℕ :=
  (relationsPerfective c).biasToSource.hundredths.toNat

private theorem mixture_div (p b : Relation → ℕ) :
    mixture (fun c ↦ (p c : ℚ) / 100) (fun c ↦ (b c : ℚ) / 100) =
      ((∑ c, p c * b c : ℕ) : ℚ) / 10000 := by
  rw [eq_div_iff (by norm_num), mixture, sum_mul]
  push_cast
  refine sum_congr rfl fun c _ ↦ ?_
  ring

/-- The near-chance overall perfective bias is the mixture (9) of strongly opposed
relation-conditioned biases, Occasion favoring the Goal and Elaboration the Source. -/
theorem perfective_mixture_masks_biases :
    2 / 5 < mixture (fun c ↦ (perfectiveFrequency c : ℚ) / 100)
        (fun c ↦ (perfectiveSourceGiven c : ℚ) / 100) ∧
      mixture (fun c ↦ (perfectiveFrequency c : ℚ) / 100)
        (fun c ↦ (perfectiveSourceGiven c : ℚ) / 100) < 3 / 5 ∧
      perfectiveSourceGiven .occasion < 20 ∧ 90 < perfectiveSourceGiven .elaboration ∧
      ∀ c, perfectiveFrequency c ≤ perfectiveFrequency .occasion := by
  have h : ∑ c, perfectiveFrequency c * perfectiveSourceGiven c = 5524 := by decide
  refine ⟨?_, ?_, by decide, by decide, by decide⟩ <;> rw [mixture_div, h] <;> norm_num

/-- Table 3: the frequency of a relation under an instruction. -/
def frequency (i : Instruction) (c : Relation) : ℕ :=
  (relationsByInstruction c i).frequency.hundredths.toNat

/-- Table 4: the Source bias of a relation in the instruction experiment. -/
def sourceGiven (c : Relation) : ℕ := (biasesByRelation c).instructionManipulation.hundredths.toNat

/-- Table 4 repeats the biases of Table 2 as those of the original experiment. -/
theorem biasesByRelation_original (c : Relation) :
    (biasesByRelation c).original = (relationsPerfective c).biasToSource := by
  cases c <;> rfl

/-- Table 5: the observed Source interpretation rate under an instruction. -/
def observedSource (i : Instruction) : ℕ :=
  (sourceByInstruction i).sourceInterpretation.hundredths.toNat

/-- (9) on Tables 3 and 4: the next-mention probability of the Source under an instruction. -/
def predictedSource (i : Instruction) : ℚ :=
  mixture (fun c ↦ (frequency i c : ℚ) / 100) (fun c ↦ (sourceGiven c : ℚ) / 100)

/-- Under the expectations of Table 3 and the biases of Table 4, the *Why?* mixture favors the
Source and the *What happened next?* mixture the Goal, as in Table 5. -/
theorem instruction_mixtures :
    (1 / 2 < predictedSource .why ∧ 50 < observedSource .why) ∧
      predictedSource .whatNext < 1 / 2 ∧ observedSource .whatNext < 50 := by
  have hw : ∑ c, frequency .why c * sourceGiven c = 8363 := by decide
  have hn : ∑ c, frequency .whatNext c * sourceGiven c = 3136 := by decide
  refine ⟨⟨?_, by decide⟩, ?_, by decide⟩
  · rw [predictedSource, mixture_div, hw]; norm_num
  · rw [predictedSource, mixture_div, hn]; norm_num

/-! ### Bidirectionality (Table 6) -/

/-- Table 6: the frequency of a relation by prompt type. -/
def promptFrequency (p : Prompt) (c : Relation) : ℕ :=
  (relationsByPrompt c p).frequency.hundredths.toNat

/-- The share of first mentions to the Goal by prompt type, in percent. -/
def goalMention (p : Prompt) : ℕ := (goalFirstMentions p).percent

/-- The ambiguous pronoun prompt shifts first mentions from Goal to Source and continuations toward
the Source-biased Elaboration and Explanation, as (12) predicts. -/
theorem prompt_shifts_relations :
    goalMention .pronoun < goalMention .noPronoun ∧
      promptFrequency .noPronoun .elaboration + promptFrequency .noPronoun .explanation <
        promptFrequency .pronoun .elaboration + promptFrequency .pronoun .explanation ∧
      promptFrequency .pronoun .occasion + promptFrequency .pronoun .result <
        promptFrequency .noPronoun .occasion + promptFrequency .noPronoun .result := by
  decide

/-! ### The voice manipulation (Tables 7–10) -/

/-- Table 7: the rate of next mention of the causally implicated referent by voice and prompt. -/
def causalMention (v : Voice) (p : Prompt) : ℕ := (causalMentions v p).proportion.hundredths.toNat

/-- Table 8: the rate of Explanation continuations by voice and prompt. -/
def explanationRate (v : Voice) (p : Prompt) : ℕ := (explanations v p).proportion.hundredths.toNat

/-- Table 9: the pronominalization rate of a position by voice, without a pronoun prompt. -/
def pronominalized (v : Voice) (pos : Position) : ℕ :=
  (pronominalizations v pos).proportion.hundredths.toNat

/-- Table 10: the observed bias of the pronoun toward the subject by voice. -/
def actualSubject (v : Voice) : ℕ := (subjectBiases v).actual.hundredths.toNat

/-- Table 7 without a pronoun prompt as the next-mention rate of the subject: the causally
implicated referent is the subject of the active and the by-phrase of the passive. -/
def subjectMention : Voice → ℕ
  | .active => causalMention .active .noPronoun
  | .passive => 100 - causalMention .passive .noPronoun

/-- With the propositions constant, the passive lowers both reference to the causally implicated
referent (Table 7) and the rate of Explanations (Table 8). -/
theorem voice_shifts_interpretation_and_coherence :
    causalMention .passive .pronoun < causalMention .active .pronoun ∧
      explanationRate .passive .pronoun < explanationRate .active .pronoun := by
  decide

/-- (13) from Tables 7 and 9: the predicted bias of an ambiguous pronoun toward the subject. -/
def bayesSubject (v : Voice) : ℚ :=
  posterior
    (Position.select ((subjectMention v : ℚ) / 100) (((100 - subjectMention v : ℕ) : ℚ) / 100))
    (Position.select ((pronominalized v .subject : ℚ) / 100)
      ((pronominalized v .nonSubject : ℚ) / 100))
    .subject

private theorem posterior_select (s a b : ℕ) :
    posterior (Position.select ((s : ℚ) / 100) (((100 - s : ℕ) : ℚ) / 100))
        (Position.select ((a : ℚ) / 100) ((b : ℚ) / 100)) .subject =
      ((a * s : ℕ) : ℚ) / ((a * s + b * (100 - s) : ℕ) : ℚ) := by
  have hnum : (a : ℚ) / 100 * ((s : ℚ) / 100) = ((a * s : ℕ) : ℚ) / 10000 := by
    push_cast; ring
  have hden : (a : ℚ) / 100 * ((s : ℚ) / 100) + (b : ℚ) / 100 * (((100 - s : ℕ) : ℚ) / 100) =
      ((a * s + b * (100 - s) : ℕ) : ℚ) / 10000 := by
    push_cast; ring
  simp only [posterior, sum_position, Position.select]
  rw [hden, hnum, div_div_div_cancel_right₀ (by norm_num)]

private theorem bayesSubject_eq :
    bayesSubject .active = 3658 / 4642 ∧ bayesSubject .passive = 2088 / 3836 := by
  have hA : subjectMention .active = 59 := by decide
  have hP : subjectMention .passive = 24 := by decide
  have haA : pronominalized .active .subject = 62 := by decide
  have hbA : pronominalized .active .nonSubject = 24 := by decide
  have haP : pronominalized .passive .subject = 87 := by decide
  have hbP : pronominalized .passive .nonSubject = 23 := by decide
  simp only [bayesSubject, hA, hP, haA, hbA, haP, hbP]
  rw [posterior_select, posterior_select]
  norm_num

/-- The Bayesian predictions of Table 10, from Table 7 and Table 9, favor the subject in both voices
and more strongly in the active, as observed. -/
theorem voice_predictions :
    (1 / 2 < bayesSubject .active ∧ 1 / 2 < bayesSubject .passive ∧
        bayesSubject .passive < bayesSubject .active) ∧
      50 < actualSubject .active ∧ 50 < actualSubject .passive ∧
        actualSubject .passive < actualSubject .active := by
  obtain ⟨hA, hP⟩ := bayesSubject_eq
  refine ⟨?_, by decide, by decide, by decide⟩
  rw [hA, hP]
  norm_num

/-- Table 10's predictions are not the posterior of the aggregate rates of Tables 7 and 9, which
fall below them in both voices (0.79 against 0.81 in the active, 0.54 against 0.59 in the
passive); the paper does not say how it estimated them. -/
theorem bayesSubject_lt_predicted (v : Voice) :
    bayesSubject v < (subjectBiases v).predicted.toRat := by
  obtain ⟨hA, hP⟩ := bayesSubject_eq
  cases v
  · rw [hA]; decide +kernel
  · rw [hP]; decide +kernel

/-- In both voices (13) puts the pronoun's subject bias above the subject's next-mention prior, and
the pronoun prompt raises subject mentions in the active (Table 7). -/
theorem overlaid_subject_bias :
    ((subjectMention .active : ℚ) / 100 < bayesSubject .active ∧
        (subjectMention .passive : ℚ) / 100 < bayesSubject .passive) ∧
      causalMention .active .noPronoun < causalMention .active .pronoun := by
  obtain ⟨hA, hP⟩ := bayesSubject_eq
  have hsA : subjectMention .active = 59 := by decide
  have hsP : subjectMention .passive = 24 := by decide
  refine ⟨⟨?_, ?_⟩, by decide⟩
  · rw [hA, hsA]; norm_num
  · rw [hP, hsP]; norm_num

/-! ### Production tracks topichood, not expectancy -/

/-- How strongly a referent is signalled as the sentence topic: the subject of a passive,
promoted by a marked construction, more strongly than the subject of an active
([davison-1984]), and non-subjects not at all. -/
inductive TopichoodLevel where
  | low
  | default_
  | strong
  deriving DecidableEq, Repr, Fintype

def TopichoodLevel.rank : TopichoodLevel → Fin 3
  | .low => 0
  | .default_ => 1
  | .strong => 2

instance : LinearOrder TopichoodLevel := LinearOrder.lift' TopichoodLevel.rank (by decide)

/-- The topichood of a grammatical role by voice. -/
def topichood : UD.Voice → GrammaticalRole → TopichoodLevel
  | .Pass, .subject => .strong
  | _, .subject => .default_
  | _, _ => .low

/-- Table 9 by grammatical role: the object of the active and the by-phrase of the passive are
the non-subjects. -/
def pronounRate (v : Voice) : GrammaticalRole → ℕ
  | .subject => pronominalized v .subject
  | _ => pronominalized v .nonSubject

/-- Across the voices and roles of Table 9, the pronominalization rate strictly increases with
topichood. -/
theorem pronounRate_strictMono : ∀ (v v' : Voice) r r',
    topichood v.toUD r < topichood v'.toUD r' → pronounRate v r < pronounRate v' r' := by
  decide

theorem production_not_expectancy :
    subjectMention .passive < 100 - subjectMention .passive ∧
      pronominalized .passive .nonSubject < pronominalized .passive .subject := by
  decide

/-! ### The design premise and the Centering term

The stimuli pair same-gender characters, so the prompt pronoun φ-agrees with both and the model
must decide between them; and under the grammatical-role ranking of forward-looking centers the
backward-looking center is the same in both voices, so the voice-induced gradient of Table 9
lives in the topichood term rather than in Centering's center. -/

/-- The two characters of (20), both third-person singular feminine. -/
def amanda : Word :=
  ⟨"Amanda", .PROPN,
    Features.of (person := some .third) (number := some .singular) (gender := some .Fem)⟩

def brittany : Word :=
  ⟨"Brittany", .PROPN,
    Features.of (person := some .third) (number := some .singular) (gender := some .Fem)⟩

theorem she_ambiguous_over_stimuli :
    English.Pronouns.she.toPronoun.CandidateAntecedent amanda ∧
      English.Pronouns.she.toPronoun.CandidateAntecedent brittany := by
  decide

/-- The context sentence of (20a): Amanda the subject, Brittany the object. -/
def prevAmandaActive : Utterance Word GrammaticalRole Head :=
  { realizations := [⟨amanda, .subject, .name⟩, ⟨brittany, .object, .name⟩] }

/-- An active continuation pronominalizing both. -/
def curActive : Utterance Word GrammaticalRole Head :=
  { realizations := [⟨amanda, .subject, .pronoun⟩, ⟨brittany, .object, .pronoun⟩] }

/-- The passive continuation: Amanda promoted to subject, Brittany in the by-phrase. -/
def curPassive : Utterance Word GrammaticalRole Head :=
  { realizations := [⟨amanda, .subject, .pronoun⟩, ⟨brittany, .other, .name⟩] }

theorem cb_invariant_under_voice :
    cb prevAmandaActive curActive = cb prevAmandaActive curPassive := by
  decide

theorem topichood_distinguishes_voice : topichood .Act .subject < topichood .Pass .subject := by
  decide

/-- The dissociation: Centering's center is voice-blind where the topichood term is
voice-sensitive, which is where the 87% against 62% of Table 9 lives. -/
theorem cb_topichood_dissociation_under_voice :
    cb prevAmandaActive curActive = cb prevAmandaActive curPassive ∧
      topichood .Act .subject < topichood .Pass .subject :=
  ⟨cb_invariant_under_voice, topichood_distinguishes_voice⟩

end KehlerRohde2013
