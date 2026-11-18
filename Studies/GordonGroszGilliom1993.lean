module

public import Linglib.Data.Statistics.GordonGroszGilliom1993
public import Linglib.Discourse.Accessibility
public import Linglib.Discourse.Centering.Basic
public import Linglib.Discourse.Centering.GrammaticalRole
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Gordon, Grosz, and Gilliom (1993): Pronouns, Names, and the Centering of Attention in Discourse

This file treats the repeated-name penalty, the slower reading of an utterance that realizes its
backward-looking center by a repeated name, as a marker of that center. Where a passage uses no
pronoun, [only the unconditional form of Rule 1 predicts it](##rule1_nameName). Grosz, Joshi, and
Weinstein's center, the highest-ranked forward-looking center of the previous utterance that the
current one realizes, [mispredicts three of the twelve tested
entities](##cbPenalty_mispredictions); the paper's revision, the current utterance's subject,
[mispredicts one](##subjectPenalty_mispredictions), and that subject when it was surface-initial
or the subject before [none](##penalty_iff_observed). [Grammatical roles alone cannot separate
Experiments 4 and 5](##not_roleFactored).

## Implementation notes

* An utterance lists, in surface order, the named entities and the new subjects of the critical
  sentences. A possessor and the object of a preposition are other roles, and Tommy is an object
  in sentences 2 to 4 of Experiment 1, as the paper describes him. Realization is direct: the
  painting that Experiment 2A's *painted* implies is not among the forward-looking centers.
* A tested entity is a cell: the critical sentence in a condition that names it, after the
  sentence before it. Sentences 3 and 4 of Experiment 1 share an analysis.
* A test finds its effect when its by-subjects and by-passages p-values are below .05, and a
  statistic printed as less than 1 finds none. Experiment 2B's test of its three conditions
  speaks for both of its entities. Experiment 5 prints no test per condition, and the paper
  reads a main effect of pronominalization without an interaction as a penalty in both.

## References

* [gordon-grosz-gilliom-1993]
* [grosz-joshi-weinstein-1995]
-/

@[expose] public section

namespace GordonGroszGilliom1993

open Discourse.Centering Data.Statistics
open Discourse.AccessibilityLevel (Head)

/-- The named entities of the sample passages, and the subjects new to the critical sentences of
Experiment 2. -/
inductive Entity
  | bruno | tommy | lisa | joe | painting | elizabeth | tom | goodThings | susan | fred | george
  | debbie
  deriving DecidableEq, Repr

abbrev Utt := Utterance Entity GrammaticalRole Head

/-- The forms Rule 1 governs, the pronouns. -/
abbrev pronouns : Set Head := {.pronoun}

/-! ### The sample passages

The critical sentences realize each named entity by form `f` or `g`, a pronoun or a repeated
name. -/

namespace Exp1

/-- (2) *He chased Tommy all the way home from school one day*, Tommy introduced by name. -/
def s2 (f : Head) : Utt := ⟨[⟨.bruno, .subject, f⟩, ⟨.tommy, .object, .name⟩]⟩

/-- (3) *He watched him hide behind a big tree and start to cry*; (4) *He yelled at him so
loudly that all the neighbors came outside* is alike. -/
def s3 (f g : Head) : Utt := ⟨[⟨.bruno, .subject, f⟩, ⟨.tommy, .object, g⟩]⟩

/-- The pro-pro, pro-name, and name-name conditions: the forms of Bruno and Tommy. -/
def conditions : List (Head × Head) := [(.pronoun, .pronoun), (.pronoun, .name), (.name, .name)]

end Exp1

namespace Exp2A

/-- (3) *She painted him in an abstract, geometric style.* -/
def s3 : Utt := ⟨[⟨.lisa, .subject, .pronoun⟩, ⟨.joe, .object, .pronoun⟩]⟩

/-- (4) *In her/Lisa's opinion, the painting captured his/Joe's mood exactly.* -/
def s4 (f g : Head) : Utt :=
  ⟨[⟨.lisa, .other, f⟩, ⟨.painting, .subject, .description⟩, ⟨.joe, .other, g⟩]⟩

end Exp2A

namespace Exp2B

/-- (1) *Elizabeth read Tom's palm the other day.* -/
def s1 : Utt := ⟨[⟨.elizabeth, .subject, .name⟩, ⟨.tom, .other, .name⟩]⟩

/-- (2) *According to her/Elizabeth, good things were in store for him/Tom.* -/
def s2 (f g : Head) : Utt :=
  ⟨[⟨.elizabeth, .other, f⟩, ⟨.goodThings, .subject, .description⟩, ⟨.tom, .other, g⟩]⟩

end Exp2B

namespace Exp3

/-- (1) *Susan gave Fred a pet hamster*, which also opens the passages of Experiment 5. -/
def s1 : Utt := ⟨[⟨.susan, .subject, .name⟩, ⟨.fred, .object, .name⟩]⟩

/-- (2) *In his/Fred's opinion, she/Susan shouldn't have done that.* -/
def s2 (f g : Head) : Utt := ⟨[⟨.fred, .other, f⟩, ⟨.susan, .subject, g⟩]⟩

end Exp3

namespace Exp4

/-- (2) *He was surprised at her hysterical reaction*, after (1) *George jumped out from behind
a tree and frightened Debbie*. -/
def s2 : Utt := ⟨[⟨.george, .subject, .pronoun⟩, ⟨.debbie, .other, .pronoun⟩]⟩

/-- (3) *He/George never thinks about how others might feel*, the continue condition. -/
def s3 (f : Head) : Utt := ⟨[⟨.george, .subject, f⟩]⟩

/-- (3') *She/Debbie screamed loudly and ran away*, the shift condition. -/
def s3' (f : Head) : Utt := ⟨[⟨.debbie, .subject, f⟩]⟩

end Exp4

namespace Exp5

/-- (2) *In his opinion, she shouldn't have done that*, after (1) of Experiment 3. -/
def s2 : Utt := Exp3.s2 .pronoun .pronoun

/-- (3) *She/Susan just assumed that anyone would love a hamster*, the continue condition. -/
def s3 (f : Head) : Utt := ⟨[⟨.susan, .subject, f⟩]⟩

/-- (3') *He/Fred doesn't have anywhere to put a hamster cage*, the shift condition. -/
def s3' (f : Head) : Utt := ⟨[⟨.fred, .subject, f⟩]⟩

end Exp5

/-! ### The tested entities -/

/-- An entity whose realization by a pronoun or a repeated name a test compares. -/
inductive Cell
  | bruno | tommy | lisa | joe | elizabeth | tom | susan3 | fred3 | george | debbie | susan5
  | fred5
  deriving DecidableEq, Repr, Fintype

namespace Cell

/-- The sentence before the critical sentence. -/
def prev : Cell → Utt
  | .bruno => Exp1.s2 .name
  | .tommy => Exp1.s2 .pronoun
  | .lisa | .joe => Exp2A.s3
  | .elizabeth | .tom => Exp2B.s1
  | .susan3 | .fred3 => Exp3.s1
  | .george | .debbie => Exp4.s2
  | .susan5 | .fred5 => Exp5.s2

/-- The critical sentence, in a condition that names the entity. -/
def cur : Cell → Utt
  | .bruno => Exp1.s3 .name .name
  | .tommy => Exp1.s3 .pronoun .name
  | .lisa => Exp2A.s4 .name .pronoun
  | .joe => Exp2A.s4 .pronoun .name
  | .elizabeth => Exp2B.s2 .name .name
  | .tom => Exp2B.s2 .pronoun .name
  | .susan3 => Exp3.s2 .pronoun .name
  | .fred3 => Exp3.s2 .name .pronoun
  | .george => Exp4.s3 .name
  | .debbie => Exp4.s3' .name
  | .susan5 => Exp5.s3 .name
  | .fred5 => Exp5.s3' .name

/-- The entity. -/
def entity : Cell → Entity
  | .bruno => .bruno
  | .tommy => .tommy
  | .lisa => .lisa
  | .joe => .joe
  | .elizabeth => .elizabeth
  | .tom => .tom
  | .susan3 | .susan5 => .susan
  | .fred3 | .fred5 => .fred
  | .george => .george
  | .debbie => .debbie

end Cell

/-! ### The findings -/

/-- A test finds its effect when its by-subjects and by-passages p-values are below .05. -/
def Test.Found (t : Test) : Prop :=
  (∃ p ∈ t.pSubjects, p.Significant (1 / 20)) ∧ ∃ p ∈ t.pPassages, p.Significant (1 / 20)

instance : DecidablePred Test.Found := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The paper finds an effect in an experiment when it prints a test of it that finds it. -/
def Found (x : Experiment) (e : Effect) : Prop :=
  ∃ t ∈ tests, t.experiment = x ∧ t.effect = e ∧ t.Found

instance (x : Experiment) (e : Effect) : Decidable (Found x e) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A repeated-name penalty was observed for the entity of a cell, by the test the paper reads
it from. -/
def Cell.Observed : Cell → Prop
  | .bruno => Found .exp1 .nameNameVsOthers
  | .tommy => Found .exp1 .proNameVsProPro
  | .lisa => Found .exp2A .entity1
  | .joe => Found .exp2A .entity2
  | .elizabeth | .tom => Found .exp2B .numberOfPronouns
  | .susan3 => Found .exp3 .subject
  | .fred3 => Found .exp3 .fronted
  | .george => Found .exp4 .penaltyContinue
  | .debbie => Found .exp4 .penaltyShift
  | .susan5 | .fred5 => Found .exp5 .pronominalization ∧ ¬ Found .exp5 .interaction

instance : DecidablePred Cell.Observed
  | .bruno | .tommy | .lisa | .joe | .elizabeth | .tom | .susan3 | .fred3 | .george | .debbie =>
    inferInstanceAs (Decidable (Found _ _))
  | .susan5 | .fred5 => inferInstanceAs (Decidable (_ ∧ _))

/-! ### Rule 1 -/

/-- In every condition of Experiment 1, Rule 1 holds of the third sentence, and its
unconditional form fails exactly in the name-name condition, whose passages showed the penalty
(p. 341). -/
theorem rule1_nameName : ∀ fg ∈ Exp1.conditions,
    PronominalizationConstraint pronouns (Exp1.s2 fg.1) (Exp1.s3 fg.1 fg.2) ∧
      (¬ CbPronominalized pronouns (Exp1.s2 fg.1) (Exp1.s3 fg.1 fg.2) ↔ fg = (.name, .name)) := by
  decide +kernel

/-! ### Which entity is the backward-looking center -/

/-- The account of Grosz, Joshi, and Weinstein: the penalty falls on the backward-looking center,
the highest-ranked forward-looking center of the previous sentence that the critical one
realizes. -/
def Cell.CbPenalty (c : Cell) : Prop := cb c.prev c.cur = some c.entity

instance : DecidablePred Cell.CbPenalty := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The backward-looking center of Grosz, Joshi, and Weinstein mispredicts the penalty exactly for
the fronted centers of Experiment 2 and the shifted subject of Experiment 4: it is the fronted
entity of Experiment 2 and Debbie after a sentence that realized her as a possessor (p. 342). -/
theorem cbPenalty_mispredictions :
    ({c | ¬ (c.CbPenalty ↔ c.Observed)} : Finset Cell) = {.lisa, .elizabeth, .debbie} := by
  decide +kernel

/-- The subject of `cur`, if `prev` realizes it: the backward-looking center on the paper's
revision, the grammatical subject if possible (p. 342). -/
def subjectCb (prev cur : Utt) : Option Entity :=
  (cur.realizations.find? (·.role = .subject)).bind fun r ↦
    if r.entity ∈ prev then some r.entity else none

/-- The penalty falls on the subject of the critical sentence, if the previous one realizes it. -/
def Cell.SubjectPenalty (c : Cell) : Prop := subjectCb c.prev c.cur = some c.entity

instance : DecidablePred Cell.SubjectPenalty := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- Taking the center to be the subject mispredicts the penalty only for Debbie, the subject of
the shift in Experiment 4. -/
theorem subjectPenalty_mispredictions :
    ({c | ¬ (c.SubjectPenalty ↔ c.Observed)} : Finset Cell) = {.debbie} := by
  decide +kernel

/-! ### Prominence in the previous sentence -/

/-- `e` is prominent among the forward-looking centers of `u` when `u` realizes it first or as its
subject (pp. 343-344). -/
def Prominent (u : Utt) (e : Entity) : Prop :=
  u.realizations.head?.map (·.entity) = some e ∨
    ∃ r ∈ u.realizations, r.entity = e ∧ r.role = .subject

instance (u : Utt) : DecidablePred (Prominent u) := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The paper's account: the penalty falls on the subject of the critical sentence, if the
previous sentence realized it first or as its subject. -/
def Cell.Penalty (c : Cell) : Prop := c.SubjectPenalty ∧ Prominent c.prev c.entity

instance : DecidablePred Cell.Penalty := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The paper's account predicts the penalty for exactly the twelve tested entities on which it
was observed. -/
theorem penalty_iff_observed (c : Cell) : c.Penalty ↔ c.Observed := by
  revert c; decide +kernel

/-- Debbie in Experiment 4 and Fred in Experiment 5 have the same roles in both sentences, a
possessor in the earlier and the subject of the critical one, but only Fred bears the penalty, so
no account that reads only an entity's grammatical roles in the two sentences fits both. -/
theorem not_roleFactored :
    ¬ ∃ f : WithBot GrammaticalRole → WithBot GrammaticalRole → Prop,
      ∀ c ∈ [Cell.debbie, .fred5],
        f (c.prev.rank c.entity) (c.cur.rank c.entity) ↔ c.Observed := by
  rintro ⟨f, hf⟩
  have hd := hf .debbie (by simp)
  have hr := hf .fred5 (by simp)
  have hprev : Cell.debbie.prev.rank Cell.debbie.entity =
      Cell.fred5.prev.rank Cell.fred5.entity := by decide +kernel
  have hcur : Cell.debbie.cur.rank Cell.debbie.entity =
      Cell.fred5.cur.rank Cell.fred5.entity := by decide +kernel
  have hobs : ¬ Cell.debbie.Observed ∧ Cell.fred5.Observed := by decide +kernel
  rw [hprev, hcur] at hd
  exact hobs.1 (hd.mp (hr.mpr hobs.2))

end GordonGroszGilliom1993
