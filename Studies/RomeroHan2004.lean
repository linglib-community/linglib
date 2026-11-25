module

public import Linglib.Data.Examples.RomeroHan2004
public import Linglib.Discourse.CommonGround
public import Linglib.Languages.English.PolarityItems
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.PolarityItem.Polarity
public import Linglib.Semantics.Questions.Bias
public import Linglib.Semantics.Questions.Inquisitive.Polar
public import Linglib.Syntax.Negation
public import Linglib.Data.Examples.Readers

/-!
# Romero and Han (2004): On negative yes/no questions

This file formalizes yes/no questions over the conversational epistemic operator VERUM. For an
individual `x` with epistemic accessibility `epi` and conversational goals `conv`, and a common
ground `cg w` at each world, VERUM of a proposition `q` holds at `w` when `q` is in the common
ground at every world satisfying the goals of `x` at every world conforming to the knowledge of
`x` at `w`, which is the necessity `□[epi ○ conv] (q ∈ cg ·) w`.

A logical form `l : LF` places a polarity `l.inner` on the clause under VERUM and a polarity
`l.outer` over VERUM. The question pronounces the cell `l.outer • VERUM (l.inner • p)` and denotes
the polar question over it, which does not depend on `l.outer` (`LF.denotation_eq`). Preposed
negation is one negation in either position, `LF.pi` and `LF.ni`, and a *really*-question is
`LF.really`. When the relation is serial and every common ground is consistent, certainty of
`pᶜ` excludes certainty of `p`, so the cell `LF.ni` pronounces lies inside the cell `LF.pi`
pronounces (`LF.pronounced_ni_subset_pronounced_pi`).

The cell that is pronounced fixes what the question asks of the addressee's evidence, a set of
propositions `ev`. We write `Must ev q` when `ev` contains `q` and not `qᶜ`. A question
pronouncing certainty asks whether `Must ev (l.inner • p)`, and a question pronouncing doubt asks
whether `ev` contains `(l.inner • p)ᶜ` (`LF.Intent`). An addressee who asserted a proposition
has `Must` of it, so some evidence answers the question after the addressee contradicted the
speaker exactly when the speaker believed `l.implicature • p`
(`LF.felicitous_contradiction_iff`). An addressee who raised a question without answering it has
`Must` of none of its answers, so some evidence answers a question over one of those answers
exactly when it pronounces doubt (`LF.felicitous_suggestion_iff`).

A polarity item in the clause under VERUM is licensed by the polarity of that clause alone, the
classical licenser of `(l.inner • ·)`, which admits positive items when the clause is positive and
negative items when it is negative (`LF.admits_iff`).

## Implementation notes

The common ground at a world is a filter of propositions, so acceptance is closed under entailment
and conjunction where the paper speaks of a set of propositions. VERUM is not a named operator of
its own: other analyses built on it, Repp's FALSUM among them, are necessities along the same
relation of the common ground's acceptance of a proposition or its failure to.

The paper grades belief by the amount of evidence for and against a proposition. Only two grades
are formalized, having evidence for a proposition and having evidence for it and none against it,
and evidence against a proposition is evidence for its complement. Conclusive evidence, knowing
an answer and the belief the Maxim of Quality requires of an assertion are all the second grade.

A question with focused *NOT* has the logical form of the negative reading of preposed negation,
`LF.ni`. The Principle of Economy, which makes a question over VERUM require a prior bias, and the
polarity of the implicature in suggestion contexts are stated in the paper in prose and are not
formalized.

## References

* [M. Romero, C.-H. Han, *On negative yes/no questions* (2004)][romero-han-2004]
* [D. R. Ladd, *A first look at the semantics and pragmatics of negative questions and tag
  questions* (1981)][ladd-1981]
* [T. N. Höhle, *Über Verum-Fokus im Deutschen* (1992)][hohle-1992]
* [S. Repp, *Common ground management: Modal particles, illocutionary negation and VERUM*
  (2013)][repp-2013]
-/

@[expose] public section

namespace RomeroHan2004

open scoped ModalLogic SetRel
open NaturalLogic PolarityItem
open Inquisitive.Proposition (polar polar_smul)

variable {W : Type*} (epi conv : SetRel W W) (cg : W → Filter W) (p : Set W)

/-! ### Questions over VERUM -/

/-- The logical form of a yes/no question over VERUM, by the polarity over VERUM and the polarity
of the clause under it. -/
structure LF where
  /-- The polarity over VERUM, negative when negation takes scope over it. -/
  outer : Polarity
  /-- The polarity of the clause under VERUM. -/
  inner : Polarity
  deriving DecidableEq, Fintype

namespace LF

/-- (101): the positive reading of preposed negation, with negation over VERUM. -/
def pi : LF := ⟨.negative, .positive⟩

/-- (68): the negative reading of preposed negation, with VERUM over negation. -/
def ni : LF := ⟨.positive, .negative⟩

/-- (47): a positive question with *really*. -/
def really : LF := ⟨.positive, .positive⟩

variable (l : LF)

/-- The cell a question pronounces, VERUM of the clause under it or the complement. -/
def pronounced : Set W := l.outer • {w | □[epi ○ conv] (l.inner • p ∈ cg ·) w}

/-- The question a logical form denotes is the polar question over the pronounced cell. -/
def denotation : Inquisitive.Proposition (Set W) := polar (l.pronounced epi conv cg p)

/-- A question over VERUM denotes the partition on certainty about the clause under VERUM,
whichever cell it pronounces. -/
theorem denotation_eq :
    l.denotation epi conv cg p = polar {w | □[epi ○ conv] (l.inner • p ∈ cg ·) w} :=
  polar_smul _ _

-- (84), (85)
theorem denotation_pi_eq_denotation_really :
    pi.denotation epi conv cg p = really.denotation epi conv cg p := by
  rw [denotation_eq, denotation_eq]; rfl

-- the doubt cell holds every other degree of certainty, certainty of the negation among them
theorem pronounced_ni_subset_pronounced_pi [ModalLogic.IsSerial (epi ○ conv)]
    (h : ∀ w, (cg w).NeBot) : ni.pronounced epi conv cg p ⊆ pi.pronounced epi conv cg p :=
  fun w hn hp ↦
    have ⟨v, hv⟩ := ModalLogic.IsSerial.serial (R := epi ○ conv) w
    have := h v
    Filter.compl_notMem (hp v hv) (hn v hv)

end LF

/-! ### The intent of a question -/

/-- (91b): the evidence `ev` holds evidence for `q` and none against it. -/
def Must (ev : Set (Set W)) (q : Set W) : Prop := q ∈ ev ∧ qᶜ ∉ ev

-- on a consistent body of evidence closed under entailment, (91b) is positive bias
theorem must_sets_iff_bias {F : Filter W} [F.NeBot] {q : Set W} :
    Must F.sets q ↔ Question.bias F q = 1 :=
  Question.bias_eq_one_iff.trans ⟨fun h ↦ ⟨h, Filter.compl_notMem h⟩, fun h ↦ h.1⟩ |>.symm

/-- The contexts in which a question over a proposition is asked. -/
inductive Scenario where
  /-- The speaker believed the proposition of the given polarity and the addressee asserted or
  implied the opposite one. -/
  | contradiction (speaker : Polarity)
  /-- The addressee raised a question he cannot answer, to which the proposition of the given
  polarity is a possible answer. -/
  | suggestion (answer : Polarity)
  deriving DecidableEq

/-- What a scenario tells the speaker about the addressee's evidence: by the Maxim of Quality the
addressee has `Must` of what he asserted, and by the Maxim of Quantity he has `Must` of no answer
to a question he left open. -/
def Scenario.Premise (ev : Set (Set W)) : Scenario → Prop
  | .contradiction s => Must ev ((.negative * s) • p)
  | .suggestion a => ¬Must ev (a • p)

namespace LF

variable (l : LF)

/-- (98), (103): what a question asks of the addressee's evidence, conclusive evidence for the
clause under VERUM if it pronounces certainty and evidence against that clause if it pronounces
doubt. -/
def Intent (ev : Set (Set W)) : Prop :=
  match l.outer with
  | .positive => Must ev (l.inner • p)
  | .negative => (l.inner • p)ᶜ ∈ ev

/-- A question is felicitous in a scenario when some evidence the addressee may have there meets
its intent. -/
def Felicitous (σ : Scenario) : Prop := ∃ ev, σ.Premise p ev ∧ l.Intent p ev

/-- The polarity of the epistemic implicature, the opposite of the proposition for which the
question asks evidence. -/
def implicature : Polarity := .negative * l.outer * l.inner

-- (99), (104), (114)
theorem exists_must_and_intent_iff [Nonempty W] (s : Polarity) :
    (∃ ev, Must ev (s • p) ∧ l.Intent p ev) ↔ s = l.outer * l.inner := by
  obtain ⟨o, i⟩ := l
  have hc : pᶜ ≠ p := compl_ne_self
  refine ⟨fun ⟨ev, hs, hi⟩ ↦ ?_, ?_⟩
  · cases o <;> cases s <;> cases i <;> simp_all [Intent, Must]
  · rintro rfl
    refine ⟨{(o * i) • p}, ⟨rfl, ?_⟩, ?_⟩ <;>
      cases o <;> cases i <;> simp [Intent, Must, hc, hc.symm]

/-- After the addressee contradicted the speaker, a question over VERUM is felicitous exactly
when the speaker believed the proposition of the polarity it implicates. -/
theorem felicitous_contradiction_iff [Nonempty W] (s : Polarity) :
    l.Felicitous p (.contradiction s) ↔ s = l.implicature := by
  refine (l.exists_must_and_intent_iff p _).trans ?_
  rw [implicature]
  cases s <;> cases l.outer <;> cases l.inner <;> decide

/-- Where the addressee left a question open, a question over VERUM of one of its answers is
felicitous exactly when it pronounces doubt. -/
theorem felicitous_suggestion_iff [Nonempty W] (a : Polarity) :
    l.Felicitous p (.suggestion a) ↔ ¬(l.outer = .positive ∧ l.inner = a) := by
  obtain ⟨o, i⟩ := l
  have hc : pᶜ ≠ p := compl_ne_self
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨ev, hs, hi⟩ ⟨rfl, rfl⟩
    exact hs hi
  · cases o
    · refine ⟨{i • p}, ?_, rfl, ?_⟩ <;>
        cases i <;> cases a <;> simp_all [Scenario.Premise, Must, hc.symm]
    · exact ⟨Set.univ, fun h ↦ h.2 trivial, trivial⟩

-- (81), (82), (117): one negation, in either position, implicates the proposition
theorem implicature_of_outer_mul_inner (h : l.outer * l.inner = .negative) :
    l.implicature = .positive := by
  rw [implicature, mul_assoc, h]; rfl

end LF

/-! ### Polarity items -/

section Licensing

variable (W : Type) (l : LF)

/-- The licenser of a polarity item in the clause under VERUM is the polarity of that clause,
VERUM standing between the item and whatever is over it. -/
def LF.licenser : Licenser := .ofPolarity W l.inner

variable {W}

/-- The clause under VERUM admits positive polarity items when it is positive and negative
polarity items when it is negative. -/
theorem LF.admits_iff [Nonempty W] {e : PolarityItem} (hf : ¬e.IsFCI) :
    (l.licenser W).Admits e ↔
      (e.IsPPI → l.inner = .positive) ∧ (e.IsNPI → l.inner = .negative) :=
  Licenser.admits_ofPolarity_iff hf

end Licensing

/-! ### The paper's examples -/

open Examples (all form scenario bias negation)

/-- The logical form of each question the paper classes. -/
def _root_.RomeroHan2004.Examples.Form.lf : Examples.Form → LF
  | .pi => .pi
  | .ni | .notFocus => .ni
  | .really => .really

/-- The scenario a row records. -/
def _root_.RomeroHan2004.Examples.Scenario.toScenario : Examples.Scenario → Scenario
  | .contradictionP => .contradiction .positive
  | .contradictionNotP => .contradiction .negative
  | .suggestionP => .suggestion .positive
  | .suggestionNotP => .suggestion .negative

/-- The reported implicature as the sign of the proposition the speaker believed. -/
def _root_.RomeroHan2004.Examples.Bias.toSign : Examples.Bias → SignType
  | .positive => 1
  | .negative => -1
  | .absent => 0

/-- The position of a question's negation, if it has one. -/
def _root_.RomeroHan2004.Examples.NegationPlacement.position :
    Examples.NegationPlacement → Option Negation.Position
  | .preposed => some .preposed
  | .nonPreposed => some .nonPreposed
  | .absent => none

/-- The polarity item a row tests. -/
def item (e : Datum) : Option PolarityItem :=
  e.parse? "item" [("too", English.PolarityItems.too), ("either", English.PolarityItems.either)]

/-- The questions the paper judges in a contradiction or a suggestion context are acceptable
exactly where their logical form is felicitous. -/
theorem felicitous_iff_acceptable :
    ∀ e ∈ all, ∀ f ∈ (form e).toList, ∀ σ ∈ (scenario e).toList, ∀ (W : Type) [Nonempty W]
      (p : Set W), f.lf.Felicitous p σ.toScenario ↔ e.judgment = .acceptable := by
  have h : ∀ e ∈ all, ∀ f ∈ (form e).toList, ∀ σ ∈ (scenario e).toList,
      (∀ s, σ.toScenario = .contradiction s →
        (s = f.lf.implicature ↔ e.judgment = .acceptable)) ∧
      ∀ a, σ.toScenario = .suggestion a →
        (¬(f.lf.outer = .positive ∧ f.lf.inner = a) ↔ e.judgment = .acceptable) := by decide
  intro e he f hf σ hσ W _ p
  obtain ⟨h₁, h₂⟩ := h e he f hf σ hσ
  cases hτ : σ.toScenario with
  | contradiction s => rw [← h₁ s hτ, LF.felicitous_contradiction_iff]
  | suggestion a => rw [← h₂ a hτ, LF.felicitous_suggestion_iff]

-- (6), (7), (77)–(80)
theorem admits_iff_acceptable :
    ∀ e ∈ all, ∀ f ∈ (form e).toList, ∀ i ∈ (item e).toList, ∀ (W : Type) [Nonempty W],
      (f.lf.licenser W).Admits i ↔ e.judgment = .acceptable := by
  have h : ∀ e ∈ all, ∀ f ∈ (form e).toList, ∀ i ∈ (item e).toList, ¬i.IsFCI ∧
      (((i.IsPPI → f.lf.inner = .positive) ∧ (i.IsNPI → f.lf.inner = .negative)) ↔
        e.judgment = .acceptable) := by decide
  intro e he f hf i hi W _
  rw [← (h e he f hf i hi).2, LF.admits_iff _ (h e he f hf i hi).1]

example : Datum.ReadCount item all 6 := by decide

-- (37), (110), (117)
theorem bias_eq_implicature :
    ∀ e ∈ all, ∀ f ∈ (form e).toList, ∀ b ∈ (bias e).toList, b.toSign = f.lf.implicature := by
  decide

-- (1), (5), (14)–(18): Generalization 1 for preposed negation, under assumption (64)
theorem bias_of_preposed :
    ∀ e ∈ all, ∀ n ∈ (negation e).toList, n.position = some .preposed →
      ∀ b ∈ (bias e).toList, ∀ l : LF, l.outer * l.inner = .negative →
        b.toSign = l.implicature := by
  decide

end RomeroHan2004
