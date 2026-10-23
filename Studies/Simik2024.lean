module

public import Studies.BuringGunlogson2000
public import Linglib.Syntax.Negation
public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Questions.Exhaustivity
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Discourse.CommonGround
public import Linglib.Logic.Modal.Defs
public import Linglib.Fragments.Slavic.Russian.QuestionParticles
public import Linglib.Fragments.Slavic.Bulgarian.QuestionParticles
public import Linglib.Fragments.Slavic.Ukrainian.QuestionParticles
public import Linglib.Fragments.Slavic.Polish.QuestionParticles
public import Linglib.Fragments.Slavic.Slovenian.QuestionParticles
public import Linglib.Fragments.Slavic.Serbian.QuestionParticles
public import Linglib.Fragments.Slavic.Macedonian.QuestionParticles
public import Linglib.Fragments.Slavic.Czech.Particles
public import Linglib.Data.Examples.Simik2024

/-!
# Šimík (2024): Polar question semantics and bias: Lessons from Slavic/Czech

This file formalizes Šimík's survey of polar-question bias in Slavic. A question
form's bias profile is the set of cells, contextual evidence by prior epistemic bias
(after Sudo), in which it is felicitous: Table 2 gives the profile of the four Czech forms,
interrogative and declarative crossed with polarity (`czechBiasProfile`), and Table 1 the
profile of the Serbian strategies reported from Todorović (`serbianBiasProfile`).
The Czech cleaning-service scenarios (11)–(18) are typed rows, and the table predicts each
judgment (`cleaning_examples_match_table2`); declaratives need evidence
(`declarative_requires_evidence`) and Czech InterNPQ, unlike English high negation, is
felicitous under positive evidence (`interNPQ_broader_than_english_outer`), while Serbian
high negation is narrower than English (`serbian_hnpq_narrower_than_english`). The quiz
scenario (24) diagnoses each of ten languages' default strategy: its positive form is the
quiz-felicitous one (`default_quiz_felicitous`), declaratives never are
(`declarative_quiz_infelicitous`), and negation triggers bias except under Polish *czy*
and Macedonian *dali* (`negationTriggersBias_iff`). Serbian *je li* is neutral in Table 1 yet
quiz-infelicitous (`jeLi_neutral_yet_quiz_infelicitous`), the contrast the chapter
attributes to a covert 'wonder' selecting the question (`wonderLF`), which denotes the
unique true answer (`trueAnswers_polar_existsUnique`). Russian *razve* resolves a conflict
between evidence for the prejacent and a prior against it (`razveProfile`), invariantly
across inner and outer negation (`razveProfile_negation_invariant`), and is a root
phenomenon while *li* embeds (`razve_root_li_embedded`). The chapter's Czech FALSUM
(`falsumCz`) presupposes only epistemic possibility of the prejacent, weaker than
Repp's operator, the necessity `□[epi ○ conv] (p ∉ cg ·)` along the
knowledge and conversational goals of its bearer (`falsumCz_eq_one_of_falsum`), and licenses
the particle *náhodou* under outer negation alone (`NahodouLicensed`, `nahodou_examples`).

## Implementation notes

Table 2's starred DeclPPQ of the neutral cell, conditioned on a contrastive topic, is
admitted by `czechFelicitous` and read off the row feature `contrastiveTopic`. The
language rows carry the paper's own strategy labels; the derived predicates read the
normalized `strategy` and `polarity` features. The kin of *razve* across Slavic are listed
(`razveKin`) without a profile, as the chapter leaves their semantics open. Bulgarian *dali*,
which footnote 40 reports quiz-infelicitous for its 'wondering' component, has no example
sentence and so no quiz row.

## References

* [simik-2024]
* [sudo-2013], [buring-gunlogson-2000], [romero-han-2004], [gartner-gyuris-2017]
* [romero-2024], [repp-2013], [repp-geist-2022], [korotkova-2023]
* [todorovic-2023], [stankova-2023], [esipova-romero-2023]
* [hamblin-1973b], [karttunen-1977], [dayal-1996]
-/

@[expose] public section

namespace Simik2024

open Question
open scoped ModalLogic

/-! ### Bias and the polarity of the prejacent (§3.1) -/

/-- The contextual evidence a conflict-resolving question of the given polarity rests on,
which is evidence for the prejacent as asked. -/
def evidence (s : Polarity) : SignType := s

/-- The prior epistemic bias a conflict-resolving question of the given polarity
double-checks, which is against the prejacent as asked. -/
def prior (s : Polarity) : SignType := -(s : SignType)

/-- The polarity of a question with the given reading of negation, which is positive without
negation and negative with either reading of it. -/
def polarityOf : Option Polarity → Polarity
  | none => .positive
  | some _ => .negative

/-! ### The Czech forms and their bias profile (§3.2, Table 2) -/

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

/-- The forms natural in each cell of contextual evidence by prior epistemic bias (Table 2),
with the starred DeclPPQ of the neutral cell left to `czechFelicitous`. -/
def czechBiasProfile : SignType → SignType → Finset CzechPQForm
  | .pos, .pos => ∅
  | .pos, .zero => {.declPPQ, .interNPQ}
  | .pos, .neg => {.declPPQ}
  | .zero, .pos => {.interPPQ, .interNPQ}
  | .zero, .zero => {.interPPQ}
  | .zero, .neg => ∅
  | .neg, .pos => {.declNPQ, .interNPQ}
  | .neg, .zero => {.declNPQ}
  | .neg, .neg => ∅

/-- The forms felicitous in a cell, admitting the unbiased declarative of (18) when a
contrastive topic claims the initial position. -/
def czechFelicitous (ev ob : SignType) (ct : Bool) :
    Finset CzechPQForm :=
  if ct ∧ ev = 0 ∧ ob = 0 then insert .declPPQ (czechBiasProfile ev ob)
  else czechBiasProfile ev ob

variable (ev ob : SignType)

theorem interPPQ_mem_iff :
    .interPPQ ∈ czechBiasProfile ev ob ↔ ev = 0 ∧ ob ≠ -1 := by
  decide +revert

theorem declPPQ_mem_iff :
    .declPPQ ∈ czechBiasProfile ev ob ↔ ev = 1 ∧ ob ≠ 1 := by
  decide +revert

theorem declNPQ_mem_iff :
    .declNPQ ∈ czechBiasProfile ev ob ↔ ev = -1 ∧ ob ≠ -1 := by
  decide +revert

/-- InterNPQ conveys a prior for the prejacent, with neutral or conflicting evidence, or
else positive evidence without a prior (the explanation-seeking (17)). -/
theorem interNPQ_mem_iff :
    .interNPQ ∈ czechBiasProfile ev ob ↔
      ob = 1 ∧ ev ≠ 1 ∨ ev = 1 ∧ ob = 0 := by
  decide +revert

theorem declarative_requires_evidence (f : CzechPQForm) (hf : f.verb = .nonV1)
    (h : f ∈ czechBiasProfile ev ob) : ev ≠ 0 := by
  revert hf h; decide +revert

theorem interNPQ_broader_than_english_outer :
    .interNPQ ∈ czechBiasProfile 1 0 ∧
      ¬ BuringGunlogson2000.Felicitous (some .positive) 1 := by
  decide

/-! ### The cleaning scenarios (11)–(18) -/

/-- The grid form a row instantiates. -/
def form? (e : Datum) : Option CzechPQForm :=
  e.parse? "form"
    [("interPPQ", .interPPQ), ("interNPQ", .interNPQ), ("declPPQ", .declPPQ),
     ("declNPQ", .declNPQ)]

/-- The contextual evidence of a row's scenario. -/
def evidence? (e : Datum) : Option SignType :=
  e.parse? "evidence" [("forP", (1 : SignType)), ("neutral", 0), ("againstP", -1)]

/-- The speaker's prior epistemic bias in a row's scenario. -/
def epistemic? (e : Datum) : Option SignType :=
  e.parse? "epistemic" [("forP", (1 : SignType)), ("neutral", 0), ("againstP", -1)]

/-- Whether a row's scenario places a contrastive topic clause-initially. -/
def contrastiveTopic (e : Datum) : Bool :=
  e.feature? "contrastiveTopic" == some "true"

/-- Table 2 predicts the scenarios. A form is judged infelicitous exactly when its cell
excludes it, the degraded InterPPQ of (18) counting as admitted. -/
theorem cleaning_examples_match_table2 :
    ∀ e ∈ Examples.all, ∀ f ∈ form? e, ∀ ev ∈ evidence? e, ∀ ob ∈ epistemic? e,
      e.judgment = .unacceptable ↔ f ∉ czechFelicitous ev ob (contrastiveTopic e) := by
  decide

/-! ### Default strategies under the quiz scenario (§4.1) -/

/-- The ten surveyed languages. -/
inductive Language
  | czech
  | slovak
  | upperSorbian
  | slovenian
  | ukrainian
  | polish
  | serbian
  | macedonian
  | bulgarian
  | russian
  deriving DecidableEq, Repr, Fintype

/-- Glottocode, the key of the example rows. -/
def Language.glottocode : Language → String
  | .czech => "czec1258"
  | .slovak => "slov1269"
  | .upperSorbian => "uppe1395"
  | .slovenian => "slov1268"
  | .ukrainian => "ukra1253"
  | .polish => "poli1260"
  | .serbian => "serb1264"
  | .macedonian => "mace1250"
  | .bulgarian => "bulg1262"
  | .russian => "russ1263"

/-- The formal means of marking a polar question. -/
inductive Strategy
  | verbMovement
  | clauseInitialParticle
  | verbAttachedParticle
  | declarative
  | intonation
  deriving DecidableEq, Repr, Fintype

/-- The chapter's summary classification of each language's default strategy as verb or
auxiliary movement, an utterance-initial particle, or a verb-attached particle. -/
def Language.defaultStrategy : Language → Strategy
  | .czech | .slovak | .upperSorbian | .slovenian => .verbMovement
  | .ukrainian | .polish | .serbian | .macedonian => .clauseInitialParticle
  | .bulgarian | .russian => .verbAttachedParticle

/-- The question particles of each language's fragment. -/
def Language.particles : Language → List Particle
  | .czech | .slovak | .upperSorbian => []
  | .slovenian =>
    [Slovenian.QuestionParticles.ali, Slovenian.QuestionParticles.a,
     Slovenian.QuestionParticles.kaj]
  | .ukrainian => [Ukrainian.QuestionParticles.cy, Ukrainian.QuestionParticles.xiba]
  | .polish => [Polish.QuestionParticles.czy, Polish.QuestionParticles.czyzby]
  | .serbian =>
    [Serbian.QuestionParticles.li, Serbian.QuestionParticles.daLi,
     Serbian.QuestionParticles.jeLi, Serbian.QuestionParticles.zar]
  | .macedonian =>
    [Macedonian.QuestionParticles.dali, Macedonian.QuestionParticles.li,
     Macedonian.QuestionParticles.zar]
  | .bulgarian =>
    [Bulgarian.QuestionParticles.li, Bulgarian.QuestionParticles.dali,
     Bulgarian.QuestionParticles.nima]
  | .russian =>
    [Russian.QuestionParticles.li, Russian.QuestionParticles.razve,
     Russian.QuestionParticles.neuzeli]

/-- The strategy a quiz row instantiates. -/
def strategy? (e : Datum) : Option Strategy :=
  e.parse? "strategy"
    [("verbMovement", .verbMovement), ("clauseInitialParticle", .clauseInitialParticle),
     ("verbAttachedParticle", .verbAttachedParticle), ("declarative", .declarative),
     ("intonation", .intonation)]

/-- The polarity of a quiz row. -/
def polarity? (e : Datum) : Option Polarity :=
  e.parse? "polarity" [("positive", .positive), ("negative", .negative)]

/-- The quiz rows (25)–(34) of a language. -/
def quizRows (l : Language) : List Datum :=
  Examples.all.filter fun e ↦ e.language == l.glottocode && (e.feature? "strategy").isSome

variable (l : Language)

theorem default_quiz_felicitous :
    ∃ e ∈ quizRows l, strategy? e = some l.defaultStrategy ∧ polarity? e = some .positive ∧
      e.judgment = .acceptable := by
  cases l <;> decide

theorem declarative_quiz_infelicitous :
    ∀ e ∈ Examples.all, strategy? e = some .declarative → e.judgment = .unacceptable := by
  decide

/-- Negation triggers bias in a language when no negated interrogative form is
quiz-felicitous. -/
def NegationTriggersBias : Prop :=
  ∀ e ∈ quizRows l, polarity? e = some .negative → strategy? e ≠ some .declarative →
    e.judgment ≠ .acceptable

instance : Decidable (NegationTriggersBias l) :=
  inferInstanceAs (Decidable (∀ e ∈ quizRows l, _))

theorem negated_interrogative_attested :
    ∃ e ∈ quizRows l, polarity? e = some .negative ∧ strategy? e ≠ some .declarative := by
  cases l <;> decide

/-- Negation triggers bias everywhere except under Polish *czy* (30b) and Macedonian
*dali* (32a). -/
theorem negationTriggersBias_iff :
    NegationTriggersBias l ↔ l ≠ .polish ∧ l ≠ .macedonian := by
  cases l <;> decide

theorem quiz_particles_in_fragment :
    ∀ e ∈ quizRows l, ∀ f ∈ e.feature? "particle", f ∈ l.particles.map (·.form) := by
  cases l <;> decide

theorem particles_licensed_polar :
    ∀ p ∈ l.particles, Clause.root .polar ∈ p.distribution.possible := by
  cases l <;> decide

/-! ### The Serbian strategies and Todorović's bias profile (§4.2.2, Table 1) -/

/-- The Serbian strategies of (31) and Table 1, which are the two positive particle
strategies, high negation (*nije li*), and low negation (*je l' … nije*). -/
inductive SerbianPQForm
  | daLiPPQ
  | jeLiPPQ
  | hnpq
  | lnpq
  deriving DecidableEq, Repr, Fintype

/-- The fragment marker of each strategy. -/
def SerbianPQForm.particle : SerbianPQForm → Particle
  | .daLiPPQ => Serbian.QuestionParticles.daLi
  | .jeLiPPQ | .lnpq => Serbian.QuestionParticles.jeLi
  | .hnpq => Serbian.QuestionParticles.li

/-- The [romero-2024] form of each strategy. -/
def SerbianPQForm.negation : SerbianPQForm → Option Negation.Position
  | .daLiPPQ | .jeLiPPQ => none
  | .hnpq => some .preposed
  | .lnpq => some .nonPreposed

/-- The Serbian strategies natural in each cell (Table 1), after [todorovic-2023]. -/
def serbianBiasProfile : SignType → SignType → Finset SerbianPQForm
  | .pos, .pos => ∅
  | .pos, .zero => {.jeLiPPQ}
  | .pos, .neg => ∅
  | .zero, .pos => {.jeLiPPQ}
  | .zero, .zero => {.daLiPPQ, .jeLiPPQ}
  | .zero, .neg => {.lnpq}
  | .neg, .pos => {.lnpq, .hnpq}
  | .neg, .zero => {.lnpq}
  | .neg, .neg => ∅

theorem daLiPPQ_mem_iff :
    .daLiPPQ ∈ serbianBiasProfile ev ob ↔ ev = 0 ∧ ob = 0 := by
  decide +revert

theorem jeLiPPQ_of_daLiPPQ (h : .daLiPPQ ∈ serbianBiasProfile ev ob) :
    .jeLiPPQ ∈ serbianBiasProfile ev ob := by
  revert h; decide +revert

theorem ppq_no_negative_bias (f : SerbianPQForm) (hf : f.negation = none)
    (h : f ∈ serbianBiasProfile ev ob) : ev ≠ -1 ∧ ob ≠ -1 := by
  revert hf h; decide +revert

theorem hnpq_mem_iff :
    .hnpq ∈ serbianBiasProfile ev ob ↔ ev = -1 ∧ ob = 1 := by
  decide +revert

theorem lnpq_of_hnpq (h : .hnpq ∈ serbianBiasProfile ev ob) :
    .lnpq ∈ serbianBiasProfile ev ob := by
  revert h; decide +revert

theorem serbian_hnpq_narrower_than_english :
    BuringGunlogson2000.Felicitous (some .positive) 0 ∧ ∀ ob, .hnpq ∉ serbianBiasProfile 0 ob := by
  decide

/-- The quiz rows of (31) carry the markers of the Table 1 strategies. -/
theorem ex31_markers :
    Examples.ex31a.feature? "particle" = some SerbianPQForm.daLiPPQ.particle.form ∧
    Examples.ex31b.feature? "particle" = some SerbianPQForm.jeLiPPQ.particle.form ∧
    Examples.ex31c.feature? "particle" = some SerbianPQForm.hnpq.particle.form ∧
    Examples.ex31d.feature? "particle" = some SerbianPQForm.lnpq.particle.form := by
  decide

/-- *Je li* is natural in the neutral cell of Table 1 yet infelicitous in the quiz (31b), where *da
li* is felicitous (31a). -/
theorem jeLi_neutral_yet_quiz_infelicitous :
    .jeLiPPQ ∈ serbianBiasProfile 0 0 ∧
      Examples.ex31b.judgment = .unacceptable ∧ Examples.ex31a.judgment = .acceptable := by
  decide

/-! ### Information-seeking questions (§2, §4.2.1)

The chapter hypothesizes that the strategies that are neutral yet quiz-infelicitous
(Serbian *je li*, Slovenian *a*, possibly Russian intonation questions) embed the Hamblin
question under a covert 'wonder', modelled as 'want to know' applied to the true answer
([karttunen-1977], [dayal-1996]); a quiz master knows the answer and so cannot want to
know it. -/

section Wonder

variable {W : Type*} (p : Set W) (w : W)

theorem trueAnswers_polar_existsUnique : ∃! q, q ∈ trueAnswers {p, pᶜ} w := by
  by_cases hw : w ∈ p
  · exact ⟨p, ⟨by simp, hw⟩, by rintro q ⟨rfl | rfl, hwq⟩ <;> simp_all⟩
  · exact ⟨pᶜ, ⟨by simp, hw⟩, by rintro q ⟨rfl | rfl, hwq⟩ <;> simp_all⟩

/-- The speaker wants to know the true answer to the polar question over `p` (the chapter's
(36)); the embedded (10b) is the same form with the attitude holder in place of the
speaker. -/
def wonderLF {E : Type*} (wantToKnow : E → Set W → Set W) (x : E) : Set W :=
  {w | ∃ q ∈ trueAnswers {p, pᶜ} w, w ∈ wantToKnow x q}

end Wonder

/-! ### Russian *razve* and its kin (§4.2.4) -/

/-- The bias profile of a *razve* question on each reading, which pairs evidence for the
prejacent as asked with a prior for its negation (the conflict-resolving profile of §3.1). -/
def razveProfile (r : Option Polarity) : SignType × SignType :=
  (evidence (polarityOf r), prior (polarityOf r))

theorem razveProfile_negation_invariant :
    razveProfile (some .negative) = razveProfile (some .positive) ∧
      razveProfile (some .positive) = (-1, 1) :=
  ⟨rfl, rfl⟩

/-- *Razve* is compatible with both negations ([repp-geist-2022]'s LFs (40), diagnosed
by the polarity items in (41)), *neuželi* with inner negation only. The two readings
double-check the negation of the prejacent, `some .negative`, and the prejacent itself,
`some .positive`. -/
def razveNegations : Finset (Option Polarity) := {some .negative, some .positive}

/-- *Neuželi* lexicalizes VERUM and so tolerates inner negation only. -/
def neuzeliNegations : Finset (Option Polarity) := {some .negative}

theorem neuzeliNegations_ssubset : neuzeliNegations ⊂ razveNegations := by decide

theorem razve_root_li_embedded :
    .subordinated ∉ Russian.QuestionParticles.razve.distribution.possible.cod ∧
      Clause.embedded .polar ∈ Russian.QuestionParticles.li.distribution.possible := by
  decide

/-- The kin of *razve* the chapter lists across Slavic, whose semantics it leaves open. -/
def razveKin : List Particle :=
  [Ukrainian.QuestionParticles.xiba, Polish.QuestionParticles.czyzby,
   Bulgarian.QuestionParticles.nima, Macedonian.QuestionParticles.zar,
   Serbian.QuestionParticles.zar, Czech.Particles.copak]

/-! ### FALSUM and the Czech outer negation (§3.3.2, §5) -/

section Falsum

open scoped SetRel

variable {W : Type*} (epi conv : SetRel W W) (cg : W → Filter W) (p : Set W)

open Classical in
/-- The chapter's Czech FALSUM (44) is defined when the attitude holder considers the
prejacent possible, and true when it is not in the common ground. -/
noncomputable def falsumCz : W → SignType :=
  {w | ModalLogic.Diamond epi (· ∈ p) w}.indicator fun w ↦ SignType.ofProp (p ∉ cg w)

/-- The question (45) over the Czech FALSUM asks whether the prejacent is outside the common
ground. -/
def falsumCzQuestion : Question W := polar {w | p ∉ cg w}

theorem falsumCz_eq_zero_iff (w : W) :
    falsumCz epi cg p w = 0 ↔ ModalLogic.Box epi (· ∉ p) w := by
  simp [falsumCz, ModalLogic.Box, ModalLogic.Diamond]

/-- [repp-2013]'s FALSUM (22b) makes the Czech operator true wherever defined when the
knowledge-then-goals relation is reflexive. -/
theorem falsumCz_eq_one_of_falsum [(epi ○ conv).IsRefl] {w : W}
    (h : □[epi ○ conv] (p ∉ cg ·) w) (hw : falsumCz epi cg p w ≠ 0) :
    falsumCz epi cg p w = 1 := by
  simp_all [falsumCz, ModalLogic.box_T h]

end Falsum

/-- *Náhodou* is licensed by outer negation and by nothing else (43). The two readings of negation
in a polar question (the chapter's (14), after [ladd-1981] and [repp-2013]) are polarities of the
proposition the question double-checks. Inner negation, the classical propositional operator
diagnosed by negative polarity items, double-checks the negation of the prejacent, `.negative`;
outer negation, the non-propositional FALSUM diagnosed by positive polarity items, the prejacent
itself, `.positive`. -/
def NahodouLicensed (pol r : Polarity) : Prop :=
  pol = .negative ∧ r = .positive

instance (pol r : Polarity) : Decidable (NahodouLicensed pol r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The reading of negation an indefinite diagnoses, the polarity item diagnosing the outer
one and the concord item the inner one. -/
def indefiniteReading? (e : Datum) : Option Polarity :=
  e.parse? "indefinite" [("ppi", .positive), ("nci", .negative)]

/-- The (43) rows with *náhodou* are acceptable exactly when the particle is licensed by
the polarity and the reading the indefinite diagnoses. -/
theorem nahodou_examples :
    ∀ e ∈ Examples.all, e.feature? "nahodou" = some "true" →
      ∀ pol ∈ polarity? e, ∀ r ∈ indefiniteReading? e,
        (e.judgment = .acceptable ↔ NahodouLicensed pol r) := by
  decide

end Simik2024
