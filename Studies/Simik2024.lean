module

public import Studies.BuringGunlogson2000
public import Studies.GartnerGyuris2017
public import Studies.RomeroHan2004
public import Linglib.Syntax.Negation
public import Linglib.Semantics.Questions.Hamblin.Modal
public import Linglib.Logic.Trivalent.Proposition
public import Linglib.Discourse.CommonGround
public import Linglib.Logic.Modal.Defs
public import Linglib.Languages.Slavic.Russian.QuestionParticles
public import Linglib.Languages.Slavic.Bulgarian.QuestionParticles
public import Linglib.Languages.Slavic.Ukrainian.QuestionParticles
public import Linglib.Languages.Slavic.Polish.QuestionParticles
public import Linglib.Languages.Slavic.Slovenian.QuestionParticles
public import Linglib.Languages.Slavic.Serbian.QuestionParticles
public import Linglib.Languages.Slavic.Macedonian.QuestionParticles
public import Linglib.Languages.Slavic.Czech.Particles
public import Linglib.Languages.Slavic.Czech.PolarityItems
public import Linglib.Data.Examples.Simik2024
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Šimík (2024): Polar question semantics and bias: Lessons from Slavic/Czech

A polar question over a prejacent `p` is asked in a *situation*: the contextual evidence supports
`p`, supports `¬p` or supports neither, and so does what the speaker believed beforehand
([sudo-2013]). This file formalizes Šimík's survey of how the forms of a polar question in the
Slavic languages are distributed over these nine situations.

The Czech forms cross the position of the finite verb, clause-initial in an interrogative question
and in situ in a declarative one, with polarity. The chapter's table of Czech lists the forms that
are natural in each situation, and we define the *distribution* of a form as the set of situations
that list it. A declarative question of either polarity occurs exactly where the evidence
supports the proposition it expresses and the speaker did not already believe that proposition.
An interrogative positive question occurs exactly where there is no evidence and no prior belief
against `p`. An interrogative negative question occurs with a prior belief in `p` and no evidence
for it, or with evidence for `p` and no prior belief. This last distribution is not the set of
situations of any pair of an evidential and an epistemic bias value. It strictly contains the
distribution of English high negation in the sample of [gartner-gyuris-2017], which strictly
contains that of Serbian high negation in the table the chapter reports from [todorovic-2023].
The judgments of the cleaning-service scenarios and of the Czech quiz questions are those the
table predicts.

In the quiz scenario a moderator who knows the answer asks for it. The positive questions that are
felicitous there are marked by verb movement, by an utterance-initial particle or by a
verb-attached particle, in the languages that the chapter's summary lists for each strategy. A
declarative question is never felicitous there, and a negated one only with Polish *czy* and
Macedonian *dali*. Of the two Serbian forms natural in the neutral situation, *je li* is
infelicitous in the quiz. The chapter hypothesizes that such a form embeds the question under a
covert 'wonder', read as 'want to know' applied to the true answer; on that reading it is false of
a speaker who knows the answer, provided that nobody wants to know what they know.

A question with Russian *razve* resolves a conflict between evidence for the proposition it
expresses and a prior belief against it. With a negated verb the particle sits under VERUM over
the negation or under FALSUM, and in the calculus of polarities of [romero-han-2004] the two
logical forms ask for the same evidence and implicate the same belief.

The chapter's Czech FALSUM is defined at a world where its bearer considers the prejacent
possible, and it is true there when the prejacent is not in the common ground. It is undefined
exactly where the bearer believes the prejacent false, so belief in the prejacent suffices for it
when the bearer's beliefs are consistent, and the prior beliefs with which an interrogative
negative question occurs in the table are exactly those that do not support `¬p`. Where
[repp-2013]'s FALSUM holds along a reflexive relation, the Czech operator is true if defined. The
particle *náhodou* requires this operator, that is a negated verb on its outer reading.

## Implementation notes

* The table of Czech stars the declarative positive question of the neutral situation as
  conditioned by information structure. It is admitted in scenario (18) alone, where a contrastive
  topic claims the initial position.
* The evidence and the prior belief of a scenario are the chapter's description of the scenario,
  so they are a function of the scenario and no row records them.
* A row records two strategies where the question uses both: Slovenian (28a) fronts the auxiliary
  after an optional *ali*, and Macedonian (32b) fronts the verb before *li*.
* The two readings of negation are polarities of the proposition the question double-checks,
  as in [buring-gunlogson-2000]: inner negation checks `¬p`, the negative polarity, and outer
  negation checks `p`, the positive one.
* In the logical form of a *razve* question, FALSUM is the negative polarity over VERUM of
  [romero-han-2004]. The two operators differ in strength, and the bias depends on the polarities
  alone.
* `wonder` takes 'want to know' as a parameter, and the only property used of it is that it
  excludes knowing.

## TODO

* The condition of [korotkova-2023] that the prejacent of a *razve* question be an abductive
  inference from the evidence is not formalized.
* The chapter's hypothesis that *náhodou* widens the ordering source of the modal in FALSUM, and
  its corpus examples of interrogative negative questions, are not formalized.

## References

* [simik-2024]
* [sudo-2013], [buring-gunlogson-2000], [romero-han-2004], [gartner-gyuris-2017]
* [romero-2024], [repp-2013], [repp-geist-2022], [korotkova-2023]
* [todorovic-2023], [stankova-2023], [ladd-1981]
* [hamblin-1973b], [karttunen-1977], [dayal-1996]
-/

@[expose] public section

namespace Simik2024

open Question
open scoped ModalLogic

/-! ### The Czech forms (§3.2) -/

/-- The finite verb of a Czech polar question is clause-initial, in interrogative word order,
or in situ, in declarative word order. The negative prefix is inseparable from the finite verb,
so verb position fixes the position of negation. -/
inductive VerbPosition
  | v1
  | nonV1
  deriving DecidableEq, Repr, Fintype

/-- The position of a negation on the finite verb, in [romero-2024]'s forms: the clause-initial
verb preposes it, giving a high negation question, and the verb in situ does not, a low one. -/
def VerbPosition.negationPosition : VerbPosition → Negation.Position
  | .v1 => .preposed
  | .nonV1 => .nonPreposed

/-- The chapter's grid of Czech polar-question forms, which crosses interrogative
(verb-initial) or declarative word order with polarity. -/
structure CzechPQForm where
  /-- The position of the finite verb. -/
  verb : VerbPosition
  /-- The polarity of the question. -/
  polarity : Polarity
  deriving DecidableEq, Repr, Fintype

namespace CzechPQForm

/-- The interrogative positive question, InterPPQ. -/
def interPPQ : CzechPQForm := ⟨.v1, .positive⟩

/-- The interrogative negative question, InterNPQ. -/
def interNPQ : CzechPQForm := ⟨.v1, .negative⟩

/-- The declarative positive question, DeclPPQ. -/
def declPPQ : CzechPQForm := ⟨.nonV1, .positive⟩

/-- The declarative negative question, DeclNPQ. -/
def declNPQ : CzechPQForm := ⟨.nonV1, .negative⟩

/-- The position of the negation of a form, `none` for a positive question. -/
def negation (f : CzechPQForm) : Option Negation.Position :=
  if f.polarity = .negative then some f.verb.negationPosition else none

end CzechPQForm

/-! ### The distribution of a form (Table 2) -/

/-- Table 2: the Czech forms natural in each situation of contextual evidence and prior belief,
without the starred declarative of the neutral situation. -/
def czechForms : Situation → Finset CzechPQForm
  | (.pos, .pos) => ∅
  | (.pos, .zero) => {.declPPQ, .interNPQ}
  | (.pos, .neg) => {.declPPQ}
  | (.zero, .pos) => {.interPPQ, .interNPQ}
  | (.zero, .zero) => {.interPPQ}
  | (.zero, .neg) => ∅
  | (.neg, .pos) => {.declNPQ, .interNPQ}
  | (.neg, .zero) => {.declNPQ}
  | (.neg, .neg) => ∅

section Distribution

variable {F : Type*} [DecidableEq F] {T : Situation → Finset F} {f : F} {s : Situation}

/-- The distribution of a form in a table: the situations whose cell lists it. -/
def distribution (T : Situation → Finset F) (f : F) : Finset Situation := {s | f ∈ T s}

@[simp] theorem mem_distribution : s ∈ distribution T f ↔ f ∈ T s := by simp [distribution]

end Distribution

-- a declarative question needs evidence for the proposition it expresses and no prior belief in it
theorem distribution_declarative (s : Polarity) :
    distribution czechForms ⟨.nonV1, s⟩ = (⟨.plus s, .minus s⟩ : BiasProfile).felicity := by
  cases s <;> decide

-- (11), (12)
theorem distribution_interPPQ :
    distribution czechForms .interPPQ = (⟨.neutral, .minus .negative⟩ : BiasProfile).felicity := by
  decide

-- (12), (16), (17)
theorem distribution_interNPQ :
    distribution czechForms .interNPQ =
      (⟨.minus .positive, .plus .positive⟩ : BiasProfile).felicity ∪
        (⟨.plus .positive, .neutral⟩ : BiasProfile).felicity := by
  decide

/-- The interrogative negative question does not have the distribution of any pair of an
evidential and an epistemic bias value. It occurs with evidence for `p` and with a prior belief
in `p`, but not with both. -/
theorem felicity_ne_distribution_interNPQ (b : BiasProfile) :
    b.felicity ≠ distribution czechForms .interNPQ := fun h ↦ by
  have h₁ : ((1, 0) : Situation) ∈ b.felicity := h ▸ by decide
  have h₂ : ((0, 1) : Situation) ∈ b.felicity := h ▸ by decide
  have h₃ : ((1, 1) : Situation) ∈ b.felicity := by
    simp only [BiasProfile.mem_felicity] at h₁ h₂ ⊢
    exact ⟨h₁.1, h₂.2⟩
  exact absurd (h ▸ h₃) (by decide)

-- a positive question is barred by evidence against the prejacent, as in [buring-gunlogson-2000]
theorem mem_evidential_none_of_mem_distribution {v : VerbPosition} {ev ob : SignType}
    (h : (ev, ob) ∈ distribution czechForms ⟨v, .positive⟩) :
    ev ∈ BuringGunlogson2000.evidential none := by
  decide +revert

/-! ### The scenarios (11)–(18) and the quiz (24) -/

/-- The situation a scenario sets up: its contextual evidence and the speaker's prior belief. -/
def Examples.Scenario.situation : Examples.Scenario → Situation
  | .plan | .newCleaners | .quiz => (0, 0)
  | .request => (0, 1)
  | .report => (-1, 1)
  | .earbud => (1, 0)

/-- The Czech forms natural in a scenario: those of Table 2 at its situation, and in (18) also
the declarative positive question, which Table 2 stars as conditioned by information
structure. -/
def Examples.Scenario.forms (c : Examples.Scenario) : Finset CzechPQForm :=
  if c = .newCleaners then insert .declPPQ (czechForms c.situation) else czechForms c.situation

/-- The polarity of an example's finite verb. -/
def Examples.QuestionPolarity.toPolarity : Examples.QuestionPolarity → Polarity
  | .positive => .positive
  | .negative => .negative

/-- The form of an example marked by verb movement alone or by declarative word order alone. -/
def Examples.Example.form? (x : Examples.Example) : Option CzechPQForm :=
  match x.strategy, x.polarity with
  | [.verbMovement], some s => some ⟨.v1, s.toPolarity⟩
  | [.declarative], some s => some ⟨.nonV1, s.toPolarity⟩
  | _, _ => none

/-- Table 2 predicts the Czech judgments. In the scenarios (11)–(18) and in the quiz, a form is
rejected exactly when the cell of the scenario's situation does not list it. -/
theorem czech_example (x : Examples.Example) (hx : x.datum.language = .czech) :
    ∀ c ∈ x.scenario, ∀ f ∈ x.form?, (x.datum.judgment.band = .rejected ↔ f ∉ c.forms) := by
  revert hx; cases x <;> decide

-- `czech_example` reads the twenty rows of (11)–(18) and the four of (25)
theorem czech_example_count :
    (Examples.Example.all.filter fun x ↦
      x.datum.language = .czech ∧ x.scenario.isSome ∧ x.form?.isSome).length = 24 := by
  decide

/-! ### Default strategies under the quiz scenario (§4.1) -/

/-- The ten surveyed languages, in the chapter's order. -/
def sample : List Glottocode :=
  [.czech, .slovak, .upperSorbian, .slovenian, .ukrainian, .polish, .serbianStandard, .macedonian,
    .bulgarian, .russian]

/-- The quiz questions (25)–(34) of a language. -/
def quiz (g : Glottocode) : List Examples.Example :=
  Examples.Example.all.filter fun x ↦ x.scenario = some .quiz ∧ x.datum.language = g

/-- A strategy is a default of a language when a positive question marked by it is felicitous in
the quiz. -/
def IsDefault (g : Glottocode) (s : Examples.Strategy) : Prop :=
  ∃ x ∈ quiz g, s ∈ x.strategy ∧ x.polarity = some .positive ∧ x.datum.judgment = .acceptable

instance (g : Glottocode) (s : Examples.Strategy) : Decidable (IsDefault g s) :=
  inferInstanceAs (Decidable (∃ x ∈ quiz g, _))

-- the summary of §4.1
theorem isDefault_verbMovement :
    sample.filter (IsDefault · .verbMovement) =
      [.czech, .slovak, .upperSorbian, .slovenian, .macedonian] := by
  decide

theorem isDefault_clauseInitialParticle :
    sample.filter (IsDefault · .clauseInitialParticle) =
      [.slovenian, .ukrainian, .polish, .serbianStandard, .macedonian] := by
  decide

theorem isDefault_verbAttachedParticle :
    sample.filter (IsDefault · .verbAttachedParticle) = [.macedonian, .bulgarian, .russian] := by
  decide

-- declarative and intonation questions are never felicitous in the quiz
theorem rejected_of_declarative (x : Examples.Example) (hx : x.scenario = some .quiz)
    (h : .declarative ∈ x.strategy ∨ .intonation ∈ x.strategy) :
    x.datum.judgment.band = .rejected := by
  revert hx h; cases x <;> decide

/-- Negation triggers bias in a language when no negated interrogative question is felicitous in
the quiz. -/
def NegationTriggersBias (g : Glottocode) : Prop :=
  ∀ x ∈ quiz g, x.polarity = some .negative → .declarative ∉ x.strategy →
    x.datum.judgment ≠ .acceptable

instance (g : Glottocode) : Decidable (NegationTriggersBias g) :=
  inferInstanceAs (Decidable (∀ x ∈ quiz g, _))

-- (30b), (32a)
theorem not_negationTriggersBias :
    sample.filter (¬ NegationTriggersBias ·) = [.polish, .macedonian] := by
  decide

theorem exists_negative_interrogative :
    ∀ g ∈ sample, ∃ x ∈ quiz g, x.polarity = some .negative ∧ .declarative ∉ x.strategy := by
  decide

/-- The question particles of each language's file. -/
def particles : List (Glottocode × List Clause.Marker) :=
  [(.slovenian,
      [Slovenian.QuestionParticles.ali, Slovenian.QuestionParticles.a,
        Slovenian.QuestionParticles.kaj]),
    (.ukrainian, [Ukrainian.QuestionParticles.cy, Ukrainian.QuestionParticles.xiba]),
    (.polish, [Polish.QuestionParticles.czy, Polish.QuestionParticles.czyzby]),
    (.serbianStandard,
      [Serbian.QuestionParticles.li, Serbian.QuestionParticles.daLi,
        Serbian.QuestionParticles.jeLi, Serbian.QuestionParticles.zar]),
    (.macedonian,
      [Macedonian.QuestionParticles.dali, Macedonian.QuestionParticles.li,
        Macedonian.QuestionParticles.zar]),
    (.bulgarian,
      [Bulgarian.QuestionParticles.li, Bulgarian.QuestionParticles.dali,
        Bulgarian.QuestionParticles.nima]),
    (.russian,
      [Russian.QuestionParticles.li, Russian.QuestionParticles.razve,
        Russian.QuestionParticles.neuzeli])]

-- the particle of a quiz question is an entry of its language's file, and the entry is placed
-- clause-initially exactly when the question is marked by an utterance-initial particle
theorem particle_example (x : Examples.Example) (hx : x.scenario = some .quiz) :
    ∀ w ∈ x.datum.feature? "particle", ∃ p ∈ (x.datum.byLanguage particles).getD [],
      p.form = w ∧ (.initial ∈ p.placements ↔ .clauseInitialParticle ∈ x.strategy) := by
  revert hx; cases x <;> decide

theorem root_polar_mem_possible :
    ∀ p ∈ (particles.map Prod.snd).flatten, Clause.root .polar ∈ p.distribution.possible := by
  decide

/-! ### The Serbian strategies (§4.2.2, Table 1) -/

/-- The Serbian strategies of (31) and Table 1, which are the two positive particle
strategies, high negation (*nije li*), and low negation (*je l' … nije*). -/
inductive SerbianPQForm
  | daLiPPQ
  | jeLiPPQ
  | hnpq
  | lnpq
  deriving DecidableEq, Repr, Fintype

namespace SerbianPQForm

/-- The language file marker of each strategy. -/
def particle : SerbianPQForm → Clause.Marker
  | .daLiPPQ => Serbian.QuestionParticles.daLi
  | .jeLiPPQ | .lnpq => Serbian.QuestionParticles.jeLi
  | .hnpq => Serbian.QuestionParticles.li

/-- The [romero-2024] form of each strategy. -/
def negation : SerbianPQForm → Option Negation.Position
  | .daLiPPQ | .jeLiPPQ => none
  | .hnpq => some .preposed
  | .lnpq => some .nonPreposed

/-- The quiz question of (31) that exemplifies each strategy. -/
def quizExample : SerbianPQForm → Examples.Example
  | .daLiPPQ => .ex31a
  | .jeLiPPQ => .ex31b
  | .hnpq => .ex31c
  | .lnpq => .ex31d

end SerbianPQForm

/-- Table 1: the Serbian strategies natural in each situation, after [todorovic-2023]. -/
def serbianForms : Situation → Finset SerbianPQForm
  | (.pos, .pos) => ∅
  | (.pos, .zero) => {.jeLiPPQ}
  | (.pos, .neg) => ∅
  | (.zero, .pos) => {.jeLiPPQ}
  | (.zero, .zero) => {.daLiPPQ, .jeLiPPQ}
  | (.zero, .neg) => {.lnpq}
  | (.neg, .pos) => {.lnpq, .hnpq}
  | (.neg, .zero) => {.lnpq}
  | (.neg, .neg) => ∅

-- *da li* questions are limited to the neutral situation
theorem distribution_daLiPPQ :
    distribution serbianForms .daLiPPQ = (⟨.neutral, .neutral⟩ : BiasProfile).felicity := by
  decide

-- *je li* questions also occur with a positive bias of either kind
theorem distribution_daLiPPQ_ssubset_jeLiPPQ :
    distribution serbianForms .daLiPPQ ⊂ distribution serbianForms .jeLiPPQ := by
  decide

-- positive questions are incompatible with negative biases
theorem distribution_subset_of_negation_eq_none {f : SerbianPQForm} (hf : f.negation = none) :
    distribution serbianForms f ⊆
      (⟨.minus .negative, .minus .negative⟩ : BiasProfile).felicity := by
  revert hf; cases f <;> decide

-- high negation resolves a conflict of a prior belief in `p` with evidence against it
theorem distribution_hnpq : distribution serbianForms .hnpq = {(-1, 1)} := by decide

theorem distribution_hnpq_ssubset_lnpq :
    distribution serbianForms .hnpq ⊂ distribution serbianForms .lnpq := by
  decide

/-- Serbian high negation is narrower than English high negation, which is narrower than the
Czech interrogative negative question. English adds the neutral evidence of a suggestion to the
Serbian conflict, and Czech adds evidence for `p` without a prior belief. -/
theorem distribution_hnpq_ssubset_english_ssubset_interNPQ :
    distribution serbianForms .hnpq ⊂
        (GartnerGyuris2017.biasProfile GartnerGyuris2017.englishV1 (some .positive)).felicity ∧
      (GartnerGyuris2017.biasProfile GartnerGyuris2017.englishV1 (some .positive)).felicity ⊂
        distribution czechForms .interNPQ := by
  decide

-- (31), Table 1
theorem feature?_particle_quizExample (f : SerbianPQForm) :
    f.quizExample.datum.feature? "particle" = some f.particle.form := by
  cases f <;> decide

-- of the two strategies natural in the neutral situation, only *da li* is felicitous in the quiz
theorem quizExample_acceptable_iff {f : SerbianPQForm} (hf : f ∈ serbianForms (0, 0)) :
    f.quizExample.datum.judgment = .acceptable ↔ f = .daLiPPQ := by
  revert hf; cases f <;> decide

/-! ### Information-seeking questions (§2, §4.2.1) -/

section Wonder

variable {W : Type*} (p : Set W) (w : W)

-- (10): exactly one of the two answers is true, so the description of the true answer is defined
theorem karttunen_polar_existsUnique : ∃! q, q ∈ karttunen {p, pᶜ} w := by
  by_cases hw : w ∈ p
  · exact ⟨p, ⟨by simp, hw⟩, by rintro q ⟨rfl | rfl, hwq⟩ <;> simp_all⟩
  · exact ⟨pᶜ, ⟨by simp, hw⟩, by rintro q ⟨rfl | rfl, hwq⟩ <;> simp_all⟩

/-- (36): the speaker wants to know the true answer to the polar question over `p`, where
`wantToKnow q` holds at the worlds in which the speaker wants to know `q`. -/
def wonder (wantToKnow : Set W → Set W) : Set W :=
  {w | ∃ q ∈ karttunen {p, pᶜ} w, w ∈ wantToKnow q}

variable {p w}

/-- A speaker who knows the answer does not wonder, if nobody wants to know what they know. This
is why the chapter takes a form with a covert 'wonder' to be infelicitous from a quiz master. -/
theorem notMem_wonder_of_knowsAnswer {wantToKnow : Set W → Set W} {Dox : SetRel W W}
    (h : ∀ q, Disjoint (wantToKnow q) (Dox.core q)) (hk : KnowsAnswer {p, pᶜ} w Dox) :
    w ∉ wonder p wantToKnow := by
  rintro ⟨q, hq, hw⟩
  exact Set.disjoint_left.1 (h q) hw
    (SetRel.core_subset_core (weakAnswer_subset _ w hq.1 hq.2) hk)

end Wonder

/-! ### Russian *razve* (§4.2.4) -/

open RomeroHan2004 (LF)

/-- The situation a *razve* question with the logical form `l` is asked in: the evidence
supports the proposition for which the question asks evidence, and the speaker believed the
opposite one (the conflict-resolving question of §3.1). -/
def razveSituation (l : LF) : Situation :=
  (((l.outer * l.inner : Polarity) : SignType), ((l.implicature : Polarity) : SignType))

-- (39b), (40a), (40b): a negated *razve* question has one bias under FALSUM and under VERUM
theorem razveSituation_of_outer_mul_inner {l : LF} (h : l.outer * l.inner = .negative) :
    razveSituation l = (-1, 1) := by
  rw [razveSituation, l.implicature_of_outer_mul_inner h, h]; rfl

-- (39a), (40c)
theorem razveSituation_really : razveSituation .really = (1, -1) := rfl

-- *neuželi* lexicalizes VERUM, which leaves a negated question the inner reading alone
theorem eq_ni_of_outer_eq_positive {l : LF} (ho : l.outer = .positive)
    (h : l.outer * l.inner = .negative) : l = .ni := by
  obtain ⟨o, i⟩ := l
  obtain rfl : o = .positive := ho
  obtain rfl : i = .negative := by simpa using h
  rfl

-- *razve* is confined to root questions, and embedded polar interrogatives take *li*
theorem razve_root_li_embedded :
    .subordinated ∉ Russian.QuestionParticles.razve.distribution.contexts ∧
      Clause.embedded .polar ∈ Russian.QuestionParticles.li.distribution.possible := by
  decide

/-! ### FALSUM and the Czech outer negation (§3.3.2, §5) -/

section Falsum

open scoped SetRel

variable {W : Type*} (epi conv : SetRel W W) (cg : W → Filter W) (p : Set W)

open Classical in
/-- (44): the Czech FALSUM is defined where its bearer considers the prejacent possible, and it
is true there when the prejacent is not in the common ground. -/
noncomputable def falsumCz : W → Trivalent := fun w ↦
  Trivalent.transplication (.ofProp (◇[epi] (· ∈ p) w)) (.ofProp (p ∉ cg w))

variable {epi conv cg p} {w : W}

-- the Czech FALSUM is undefined exactly where its bearer believes the prejacent false
theorem falsumCz_eq_undefined_iff :
    falsumCz epi cg p w = .undefined ↔ □[epi] (· ∉ p) w := by
  simp [falsumCz, ModalLogic.Box, ModalLogic.Diamond]

-- (45): where defined, the question asks whether the prejacent is outside the common ground
theorem falsumCz_eq_true_iff :
    falsumCz epi cg p w = .true ↔ ◇[epi] (· ∈ p) w ∧ p ∉ cg w := by
  simp [falsumCz]

theorem falsumCz_eq_false_iff :
    falsumCz epi cg p w = .false ↔ ◇[epi] (· ∈ p) w ∧ p ∈ cg w := by
  simp [falsumCz]

-- belief in the prejacent suffices for the presupposition of epistemic possibility
theorem falsumCz_ne_undefined_of_box [ModalLogic.IsSerial epi] (h : □[epi] (· ∈ p) w) :
    falsumCz epi cg p w ≠ .undefined := by
  have ⟨v, hv, hp⟩ := ModalLogic.box_D h
  exact fun hu ↦ falsumCz_eq_undefined_iff.1 hu v hv hp

-- (22b): where [repp-2013]'s FALSUM holds, the Czech operator is true if defined
theorem falsumCz_eq_true_of_falsum [(epi ○ conv).IsRefl]
    (h : □[epi ○ conv] (p ∉ cg ·) w) (hw : falsumCz epi cg p w ≠ .undefined) :
    falsumCz epi cg p w = .true := by
  simp_all [falsumCz, ModalLogic.box_T h]

end Falsum

/-- The prior beliefs with which the interrogative negative question occurs in Table 2 are those
that do not support `¬p`, the stances at which the Czech FALSUM is defined. -/
theorem image_snd_distribution_interNPQ :
    (distribution czechForms .interNPQ).image Prod.snd = BiasValue.minus .negative := by
  decide

/-- *Náhodou* is licensed by outer negation and by nothing else (43): the verb is negated, and
the question double-checks the prejacent itself. -/
def NahodouLicensed (pol r : Polarity) : Prop :=
  pol = .negative ∧ r = .positive

instance (pol r : Polarity) : Decidable (NahodouLicensed pol r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The language file entry of the indefinite of an example. -/
def Examples.Indefinite.entry : Examples.Indefinite → PolarityItem
  | .ppi => Czech.PolarityItems.nejaky
  | .nci => Czech.PolarityItems.zadny

-- (43d), (43e): a question with *náhodou* is acceptable exactly when some reading of its negation
-- licenses the particle and suits the indefinite, a positive polarity item escaping the negation
-- and a negative one falling under it
theorem nahodou_example (x : Examples.Example)
    (hx : x.datum.feature? "particle" = some Czech.Particles.nahodou.form) :
    ∀ s ∈ x.polarity, ∀ i ∈ x.indefinite,
      (x.datum.judgment = .acceptable ↔
        ∃ r, NahodouLicensed s.toPolarity r ∧ r.Admits i.entry) := by
  revert hx; cases x <;> decide

-- `nahodou_example` reads the three rows of (43d) and (43e)
theorem nahodou_example_count :
    (Examples.Example.all.filter fun x ↦
      x.datum.feature? "particle" = some Czech.Particles.nahodou.form).length = 3 := by
  decide

end Simik2024
