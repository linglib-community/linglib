module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Dayal2025
public import Linglib.Fragments.English.Particles
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.HindiUrdu.Particles
public import Linglib.Fragments.Japanese.Particles
public import Linglib.Semantics.Questions.HamblinSet
public import Linglib.Semantics.Presupposition.Verb
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Dayal (2025): The interrogative left periphery

Question meaning is built at three points of the left periphery. At C a
proposition becomes a set of propositions; at PerspP a perspectival center is
introduced for whom the question is potentially active, which presupposes that
the center may not know the answer; at SAP the speaker puts the addressee under
an obligation to answer. Embedding predicates select up to one of the layers,
and the middle one, quasi-subordination with matrix syntax and intonation,
carries a semantic filter: *know* and *remember* assert knowledge of the answer
and so cannot host it, negation or questioning of them and *forget* leave the
center's ignorance open and can, which is McCloskey's shiftiness. Boundary
tones realize the features of the two upper layers, so a declarative question
is biased in English, where C is typed early, and can be neutral in Hindi-Urdu
and Italian, where typing is delayed; and a bare polar clause can only be
subordinated where a complementizer or Q-morpheme types it, which Hindi-Urdu
lacks. Question particles sit at the layer their embedding distribution shows.

## Implementation notes

* Predicates enter through their at-issue content as a set of worlds: *know*
  and *remember* are the center's knowledge of the answer at the evaluation
  time and *forget* its negation (43b), the past presuppositions set aside as
  the paper does.
* Boundary tones stand in for the features they realize: Persp_CQ and SA_ASK
  rise, Persp_CP and SA_ASSERT fall, the combined act of a biased question
  licenses both (§4.3).

## TODO

* The de se requirement of §3.3, disjoined questions (§4.2), imperatives,
  sentience and rhetorical questions (§5), and selection (§6) are not
  formalized. The centering condition alone licenses *Have you forgotten [was
  Henry a communist]*, which the paper marks unacceptable and attributes to
  who is invested in the answer (`possiblyIgnorant_forgets_question_iff`).

## References

* [V. Dayal, *The interrogative left periphery* (2025)][dayal-2025]
* [J. McCloskey, *Questions and questioning in a local English*
  (2006)][mccloskey-2006]
* [R. Bhatt and V. Dayal, *Polar question particles* (2020)][bhatt-dayal-2020]
* [U. Sauerland and K. Yatsushiro, *Remind-me presuppositions and speech-act
  decomposition* (2017)][sauerland-yatsushiro-2017]
* [C. Gunlogson, *True to form* (2004)][gunlogson-2004]
* [D. Büring and C. Gunlogson, *Aren't positive and negative polar questions
  the same?* (2000)][buring-gunlogson-2000]
* [D. Büring, *Intonation and meaning* (2016)][buring-2016]
* [L. Cheng, *On the typology of wh-questions* (1991)][cheng-1991]
* [M. Speas and C. Tenny, *Configurational properties of point of view roles*
  (2003)][speas-tenny-2003]
* [M. Krifka, *Embedding illocutionary acts* (2014)][krifka-2014]
* [V. Dayal, *Locality in WH quantification* (1996)][dayal-1996]
* [X. V. Zu, *Discourse participants and the structural representation of the
  context* (2018)][zu-2018]
-/

@[expose] public section

namespace Dayal2025

open Question Clause
open English English.Particles HindiUrdu.Particles Japanese.Particles English.Verbs

/-! ### The left periphery

The WH-feature on C, the three layers ordered by height, and the classes of embedding predicates
by the largest layer they select. -/

/-- The WH-feature on C is interrogative, declarative, or unspecified with typing delayed to a
higher layer (Hindi-Urdu polar clauses, [dayal-2025] §4.4). -/
inductive WHFeature where
  | plusWH
  | minusWH
  | alphaWH
  deriving DecidableEq, Repr, Fintype

/-- The interrogative left periphery has three layers, clause typing at C, centering at PerspP,
and the speech act at SAP. -/
inductive PeripheryLayer where
  | cp
  | perspP
  | sap
  deriving DecidableEq, Repr, Fintype

/-- The height of a layer in the periphery. -/
def PeripheryLayer.height : PeripheryLayer → ℕ
  | .cp => 0
  | .perspP => 1
  | .sap => 2

/-- Layers ordered by height. -/
instance : LinearOrder PeripheryLayer := LinearOrder.lift' PeripheryLayer.height (by decide)

/-- Embedding predicates are classed by the largest left-peripheral structure they select
([dayal-2025] §1.2). Uninterrogatives take no interrogative; rogatives take CP only
(*depend on*, *investigate*), PerspP (*wonder*, *want to know*) or SAP (*ask*); responsives
(*know*, *remember*, *forget*) take CP and, where their meaning leaves the center's ignorance
open, PerspP. -/
inductive SelectionClass where
  | uninterrogative
  | rogativeCP
  | rogativePerspP
  | rogativeSAP
  | responsive
  deriving DecidableEq, Repr, Fintype

/-- The largest layer a class selects. -/
def SelectionClass.layer : SelectionClass → Option PeripheryLayer
  | .uninterrogative => none
  | .rogativeCP => some .cp
  | .rogativePerspP => some .perspP
  | .rogativeSAP => some .sap
  | .responsive => some .perspP

/-- The selection class of a lexical entry. Question-taking factives are responsive,
non-veridical doxastic attitudes uninterrogative, question-taking speech-act verbs select SAP,
opaque question-taking verbs PerspP, and other question-taking verbs CP. -/
def deriveSelectionClass (v : _root_.Verb) : SelectionClass :=
  if ¬ v.TakesQuestion then .uninterrogative
  else if v.IsFactive then .responsive
  else if ∃ a ∈ v.attitude, ¬ a.IsPreferential ∧ ¬ a.IsVeridical v.factivity then .uninterrogative
  else if v.speechActVerb && citationQuestion v then .rogativeSAP
  else if v.opaqueContext && citationQuestion v then .rogativePerspP
  else if citationQuestion v then .rogativeCP
  else .uninterrogative
where
  /-- The basic frame is an embedded question. -/
  citationQuestion (v : _root_.Verb) : Bool :=
    decide (∃ fr ∈ v.valency.frames.head?, ∃ t, t.IsInterrogative ∧ fr.hasType t)

/-! ### The three layers (7), (20) -/

/-- The layer an embedding context reaches is CP under subordination, PerspP under
quasi-subordination, and SAP for a matrix clause, a quotation or an insubordinated root
utterance. -/
def layerOfContext : EmbeddingContext → PeripheryLayer
  | .subordinated => .cp
  | .quasiSubordinated => .perspP
  | .matrix | .quotation | .insubordinated => .sap

/-- A class takes an embedding context when the context's layer is within what it
selects. -/
def Selects (cls : SelectionClass) (e : EmbeddingContext) : Prop :=
  match cls.layer with
  | none => False
  | some l => layerOfContext e ≤ l

instance (cls : SelectionClass) (e : EmbeddingContext) : Decidable (Selects cls e) := by
  unfold Selects
  split <;> infer_instance

/-! ### Question particles (§1.3) -/

/-- A particle's layer is read off its embedding distribution (20): CP if it is licensed in
subordination, otherwise PerspP if it is licensed in quasi-subordination, otherwise SAP if it is
licensed in matrix clauses. -/
def layerOf (p : Particle) : Option PeripheryLayer :=
  if .subordinated ∈ p.distribution.possible.cod then some .cp
  else if .quasiSubordinated ∈ p.distribution.possible.cod then some .perspP
  else if .matrix ∈ p.distribution.possible.cod then some .sap
  else none

-- (15), (19)
theorem layers_derived :
    layerOf ka = some .cp ∧ layerOf kya = some .perspP ∧
      layerOf kke = some .sap ∧ layerOf quick = some .sap := by
  decide

/-! ### Centering (25)–(26), (42)–(43) -/

variable {W : Type*} {c : Set W} (H : Set (Set W)) (Dox : SetRel W W)

/-- The at-issue content of *x knows Q* and of *x remembers Q* is knowledge of the answer at
the evaluation time, through the center's doxastic alternatives `Dox`. -/
def knows : Set W := {w | KnowsAnswer H w Dox}

/-- In (43b), *x forgets Q* is ignorance of the answer, its past-knowledge presupposition set
aside. -/
def forgets : Set W := (knows H Dox)ᶜ

-- (26d), (42a)
theorem not_possiblyIgnorant_knows : ¬ PossiblyIgnorant H (c ∩ knows H Dox) Dox :=
  not_possiblyIgnorant_inter_of_subset subset_rfl

-- (42b), (43)
theorem possiblyIgnorant_forgets_iff :
    PossiblyIgnorant H (c ∩ forgets H Dox) Dox ↔ PossiblyIgnorant H c Dox :=
  possiblyIgnorant_inter_compl_iff

-- (42c)
theorem possiblyIgnorant_knows_question_iff :
    PossiblyIgnorant H (c ∩ (knows H Dox ∪ (knows H Dox)ᶜ)) Dox ↔ PossiblyIgnorant H c Dox :=
  possiblyIgnorant_inter_union_compl_iff

/-- The computation licenses *Have you forgotten [was Henry a communist]* (46b), which §3.3 excludes
on grounds of who is invested in the answer. -/
theorem possiblyIgnorant_forgets_question_iff :
    PossiblyIgnorant H (c ∩ (forgets H Dox ∪ (forgets H Dox)ᶜ)) Dox ↔
      PossiblyIgnorant H c Dox :=
  possiblyIgnorant_inter_union_compl_iff

/-! ### Boundary tones and the features they realize (§4.3–4.4) -/

inductive Tone where
  | rise
  | fall
  deriving DecidableEq, Repr

/-- The feature on Persp marks a centered question or a centered proposition. -/
inductive PerspFeature where
  | cq
  | cp
  deriving DecidableEq, Repr, Fintype

/-- The tone a Persp feature is realized as. -/
def PerspFeature.tone : PerspFeature → Tone
  | .cq => .rise
  | .cp => .fall

/-- The illocutionary head is asking, asserting, or the combined act of a biased question
(64b). -/
inductive Illocution where
  | ask
  | assert
  | assertAsk
  deriving DecidableEq, Repr

/-- The tones an illocution licenses. -/
def Illocution.licenses : Illocution → Tone → Prop
  | .ask, .rise => True
  | .assert, .fall => True
  | .assertAsk, _ => True
  | _, _ => False

instance (sa : Illocution) (t : Tone) : Decidable (sa.licenses t) := by
  cases sa <;> cases t <;> simp only [Illocution.licenses] <;> infer_instance

/-- The tone C demands of Persp, if C is typed. -/
def demand : WHFeature → Option Tone
  | .plusWH => some .rise
  | .minusWH => some .fall
  | .alphaWH => none

/-- Persp agrees with C when C, if typed, demands Persp's tone (75). -/
def AgreesC (f : WHFeature) (p : PerspFeature) : Prop :=
  demand f = none ∨ demand f = some p.tone

instance (f : WHFeature) (p : PerspFeature) : Decidable (AgreesC f p) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A full left periphery is derivable when Persp agrees with C and SAP licenses Persp's
tone (75). -/
def Derivable (f : WHFeature) (p : PerspFeature) (sa : Illocution) : Prop :=
  AgreesC f p ∧ sa.licenses p.tone

instance (f : WHFeature) (p : PerspFeature) (sa : Illocution) : Decidable (Derivable f p sa) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- (64)
theorem english_declarative_biased :
    Derivable .plusWH .cq .ask ∧ Derivable .minusWH .cp .assertAsk ∧
      ∀ p, ¬ Derivable .minusWH p .ask := by
  decide

-- (66)
theorem delayed_typing_neutral :
    Derivable .alphaWH .cq .ask ∧ Derivable .alphaWH .cp .assertAsk := by
  decide

-- (67)
theorem no_quasi_declarative_question : ¬ AgreesC .minusWH .cq := by decide

/-- A language may type a bare polar clause at C (§4.4) by a polar complementizer
(*whether*, *se*) or by a clause-typing Q-morpheme (*ka*). -/
structure PolarTyping where
  polarComplementizer : Bool
  qMorpheme : Bool
  deriving DecidableEq, Repr, Fintype

/-- A simplex polar clause is clause-typed in a context when a lexical resource types it
or the context supplies Persp_CQ above C ((72)). -/
def Typed (L : PolarTyping) (e : EmbeddingContext) : Prop :=
  L.polarComplementizer = true ∨ L.qMorpheme = true ∨ .perspP ≤ layerOfContext e

instance (L : PolarTyping) (e : EmbeddingContext) : Decidable (Typed L e) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def english : PolarTyping := ⟨true, false⟩
def italian : PolarTyping := ⟨true, false⟩
def japanese : PolarTyping := ⟨false, true⟩
def hindiUrdu : PolarTyping := ⟨false, false⟩

-- (69), (71)
theorem simplex_polar :
    (∀ e, Typed english e ∧ Typed italian e ∧ Typed japanese e) ∧
      ¬ Typed hindiUrdu .subordinated ∧ Typed hindiUrdu .quasiSubordinated ∧
        Typed hindiUrdu .matrix := by
  decide

-- (71)
theorem ya_nahi_obligatory_iff :
    ∀ e, ya_nahi.distribution .polar e = some .obligatory ↔ ¬ Typed hindiUrdu e := by
  decide

/-! ### The paper's judgments -/

/-- The English predicates of the paper, from the fragment. -/
def verbs : List English.Verbs.Verb :=
  [know, believe, wonder, ask, investigate, depend_on, remember_rog, forget_rog]

/-- The embedding context a row's `embedding` feature names. -/
def contextOf : String → Option EmbeddingContext
  | "subordination" => some .subordinated
  | "quasi" => some .quasiSubordinated
  | "quotation" => some .quotation
  | "matrix" => some .matrix
  | _ => none

/-- A judgment counts as licensed when it is acceptable or marginal, so that McCloskey's `?`
on (40b) is licensed. -/
def Fine (j : Judgment) : Prop := j = .acceptable ∨ j = .marginal

instance (j : Judgment) : Decidable (Fine j) := inferInstanceAs (Decidable (_ ∨ _))

-- (8), (9), (11), (24), (84), (85)
theorem selection_rows :
    ∀ row ∈ Examples.all, ∀ v ∈ verbs, ∀ e,
      row.feature? "verb" = some v.form → (row.feature? "embedding").bind contextOf = some e →
      e ≠ .quasiSubordinated →
      (Fine row.judgment ↔ Selects (deriveSelectionClass v.toVerb) e) := by
  decide

/-- In the at-issue content of a responsive (43b), *know* and *remember* assert knowledge of
the answer and *forget* asserts ignorance. -/
def assertsKnowledge : String → Bool
  | "know" => true
  | "remember" => true
  | _ => false

-- §3.3, (8), (9), (38), (40), (43), (45), (46), (84), (85)
theorem quasi_rows :
    ∀ row ∈ Examples.all, ∀ v ∈ verbs,
      row.feature? "verb" = some v.form →
      (row.feature? "embedding").bind contextOf = some .quasiSubordinated →
      row.feature? "invested" = none →
      (Fine row.judgment ↔
        Selects (deriveSelectionClass v.toVerb) .quasiSubordinated ∧
          (deriveSelectionClass v.toVerb = .responsive →
            assertsKnowledge v.form = false ∨ row.feature? "negated" = some "true" ∨
              row.feature? "questioned" = some "true")) := by
  decide

/-- Declarative syntax leaves the WH-feature on C typed early in English and delayable in
Hindi-Urdu and Italian (§4.4). -/
def declarativeC (l : Glottocode) : Option WHFeature :=
  List.lookup l [(.english, .minusWH), (.hindi, .alphaWH), (.italian, .alphaWH)]

-- (62), (63)
theorem declarative_question_rows :
    ∀ row ∈ Examples.all, ∀ f, row.feature? "syntax" = some "declarative" →
      row.feature? "embedding" = some "matrix" → declarativeC row.language = some f →
      (row.readings.lookup "neutral" = some .acceptable ↔ ∃ p, Derivable f p .ask) ∧
        row.readings.lookup "biased" = some .acceptable := by
  decide

/-- A language's polar typing resources, by glottocode. -/
def typingOf (l : Glottocode) : Option PolarTyping :=
  List.lookup l [(.english, english), (.italian, italian), (.japanese, japanese),
    (.hindi, hindiUrdu)]

-- (69), (71)
theorem simplex_rows :
    ∀ row ∈ Examples.all, ∀ L e, row.feature? "simplex" = some "true" →
      typingOf row.language = some L → (row.feature? "embedding").bind contextOf = some e →
      (Fine row.judgment ↔ Typed L e) := by
  decide

end Dayal2025
