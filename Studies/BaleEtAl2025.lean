module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Core.Data.Fintype.Sets
public import Studies.GoodmanStuhlmuller2013
public import Linglib.Data.Examples.BaleEtAl2025

/-!
# Bale, Noguchi, Rolland and Barner (2025): Competence by Default: Do Listeners Assume That Speakers Are Knowledgeable When Computing Conversational Inferences?

A strong scalar implicature needs more than the weak one. From *some* the hearer infers that the
speaker does not know that *all* holds, and only with competence, the speaker knowing whether
*all* holds, does this become knowledge that *all* is false. Bale, Noguchi, Rolland and Barner
test two hypotheses about competence. Under competence by default, after Geurts and after van
Rooij and Schulz, the hearer assumes it and cancels it when the speaker's contextual knowledge
state contradicts it. Under contextual licensing, after Soames and Horn, it is adopted only when
the context supplies it. Farmer Brown opens two of three boxes, both with red cubes, looks or
does not look into the third, and says that some or all of the boxes have red cubes; the
participant is asked whether the third box has red cubes. The speaker's knowledge states are the
observation states of Goodman and Stuhlmüller.

Integrating the speaker's state, the two hypotheses give the same answers. They come apart only
when integration fails, where a hearer who keeps the default derives the strong implicature from
an ignorant speaker. Participants under cognitive load answered no to the ignorant speaker's
*some* more than twice as often as those without load, while the knowledgeable speaker's *some*
showed only the usual small reduction.

## Main statements

* `competent_iff_looked`: the speaker is competent about *all* exactly when he looked into the
  third box.
* `competenceDefault_eq_contextual`: with integration the default is cancelled exactly where the
  context contradicts it, so the two hypotheses agree.
* `load_diverges`, `load_agrees_of_knowledgeable`: without integration the default yields the
  strong implicature from the ignorant speaker and nothing new from the knowledgeable one.
* `rows_expected`: the expected response in each trial type is the contextual-licensing answer.

## References

* [bale-etal-2025]
* [geurts-2010]
* [soames-1982]
* [horn-1989]
* [vanrooij-schulz-2004]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

namespace BaleEtAl2025

open GoodmanStuhlmuller2013 NeoGricean Set

attribute [local instance] Set.decidableSubsetOfFintype Set.decidableSSubsetOfFintype
  Set.decidableEqOfFintype

/-! ### Worlds, evidence and knowledge states -/

/-- The proposition a quantified statement about the three boxes expresses. -/
def prop (q : QUtt) : Set (Fin 4) := ↑q.extension

instance (q : QUtt) : DecidablePred (· ∈ prop q) :=
  fun w ↦ decidable_of_iff (w ∈ q.extension) Finset.mem_coe.symm

/-- The statement *all of the boxes have red cubes* is the alternative, and the question asked. -/
abbrev all : Set (Fin 4) := prop .all

/-- The participant sees that boxes 1 and 2 have red cubes. -/
def seen : Set (Fin 4) := {w | 2 ≤ w.val}

instance : DecidablePred (· ∈ seen) := fun w ↦ inferInstanceAs (Decidable (2 ≤ w.val))

/-- After looking into `a` boxes, boxes 1 and 2 among them, Farmer Brown knows in world `w` that
the world is one of those compatible with the red cubes he saw. -/
def speakerState (a w : Fin 4) : Set (Fin 4) :=
  ↑(compatible a (⟨min a.val w.val, lt_of_le_of_lt (Nat.min_le_left ..) a.isLt⟩ : Fin 4))

instance (a w : Fin 4) : DecidablePred (· ∈ speakerState a w) :=
  fun _ ↦ decidable_of_iff _ (mem_compatible.symm.trans Finset.mem_coe.symm)

instance (S : Finset (Fin 4)) : DecidablePred (· ∈ (↑S : Set (Fin 4))) :=
  fun w ↦ decidable_of_iff (w ∈ S) Finset.mem_coe.symm

instance (S : Set (Fin 4)) [DecidablePred (· ∈ S)] :
    Decidable (S ∈ (Question.polar all : Set (Set (Fin 4)))) :=
  decidable_of_iff (S ⊆ all ∨ S ⊆ allᶜ) Question.mem_polar.symm

/-- The speaker is competent about *all* exactly when he looked into the third box. -/
theorem competent_iff_looked (a w : Fin 4) (hw : w ∈ seen) :
    speakerState a w ∈ Question.polar all ↔ a = 3 := by
  rw [← SetLike.mem_coe]; revert a w; decide

/-! ### The recipe and its integration with context -/

/-- An utterance conveys Quality and the weak implicatures of its stronger scalar alternatives,
so the speaker knows the statement and does not know any stronger one. -/
def uttered (q : QUtt) : Set (Set (Fin 4)) := commitment (prop q) (range prop)

instance (S : Set (Fin 4)) [DecidablePred (· ∈ S)] (q : QUtt) : Decidable (S ∈ uttered q) :=
  decidable_of_iff (S ⊆ prop q ∧ ∀ q', prop q' ⊂ prop q → ¬ S ⊆ prop q') (by simp [uttered])

/-- With the speaker's contextual knowledge state integrated, the hearer keeps the worlds in
which what the speaker saw satisfies the epistemic constraints. -/
def integrated (a : Fin 4) (E : Set (Set (Fin 4))) : Set (Fin 4) :=
  {w ∈ seen | speakerState a w ∈ E}

instance (a : Fin 4) (E : Set (Set (Fin 4))) [∀ w, Decidable (speakerState a w ∈ E)] :
    DecidablePred (· ∈ integrated a E) :=
  fun w ↦ inferInstanceAs (Decidable (w ∈ seen ∧ speakerState a w ∈ E))

/-- Without that integration the hearer keeps the worlds that some knowledge state satisfying
the constraints contains, knowledge being factive. -/
def unintegrated (E : Set (Set (Fin 4))) : Set (Fin 4) :=
  {w ∈ seen | ∃ S : Finset (Fin 4), (↑S : Set (Fin 4)) ∈ E ∧ w ∈ S}

instance (E : Set (Set (Fin 4)))
    [∀ S : Finset (Fin 4), Decidable ((↑S : Set (Fin 4)) ∈ E)] :
    DecidablePred (· ∈ unintegrated E) :=
  fun w ↦ inferInstanceAs
    (Decidable (w ∈ seen ∧ ∃ S : Finset (Fin 4), (↑S : Set (Fin 4)) ∈ E ∧ w ∈ S))

/-! ### The two hypotheses -/

/-- Contextual licensing grants competence only as the speaker's contextual knowledge state
supplies it. -/
def contextual (a : Fin 4) (q : QUtt) : Set (Fin 4) := integrated a (uttered q)

instance (a : Fin 4) (q : QUtt) : DecidablePred (· ∈ contextual a q) :=
  fun w ↦ inferInstanceAs (Decidable (w ∈ integrated a (uttered q)))

/-- Competence by default with integration keeps the default where the speaker's contextual
state bears it out and cancels it where that state contradicts it everywhere. -/
def competenceDefault (a : Fin 4) (q : QUtt) : Set (Fin 4) :=
  {w | w ∈ integrated a (uttered q ∩ Question.polar all) ∨
    ((∀ w', w' ∉ integrated a (uttered q ∩ Question.polar all)) ∧ w ∈ contextual a q)}

instance (a : Fin 4) (q : QUtt) : DecidablePred (· ∈ competenceDefault a q) :=
  fun w ↦ inferInstanceAs (Decidable (w ∈ integrated a (uttered q ∩ Question.polar all) ∨
    ((∀ w', w' ∉ integrated a (uttered q ∩ Question.polar all)) ∧ w ∈ contextual a q)))

/-- The default with integration blocked, as under cognitive load. -/
def competenceDefaultLoad (q : QUtt) : Set (Fin 4) :=
  unintegrated (uttered q ∩ Question.polar all)

instance (q : QUtt) : DecidablePred (· ∈ competenceDefaultLoad q) :=
  fun w ↦ inferInstanceAs (Decidable (w ∈ unintegrated (uttered q ∩ Question.polar all)))

/-- A participant answers *Do you think there are red cubes in this box?* with one of these. -/
inductive Answer
  | yes
  | no
  | dontKnow
  deriving DecidableEq, Repr

/-- The remaining worlds support the answer yes if the third box has red cubes in all of them,
and no if in none. -/
def answer (worlds : Set (Fin 4)) [DecidablePred (· ∈ worlds)] : Answer :=
  if worlds ⊆ all then .yes else if worlds ⊆ allᶜ then .no else .dontKnow

/-- With integration the default is cancelled exactly where the context contradicts it, so the
two hypotheses agree. -/
theorem competenceDefault_eq_contextual (a : Fin 4) (q : QUtt) :
    competenceDefault a q = contextual a q := by
  revert a q; decide

/-- Without integration the default yields the strong implicature from the ignorant speaker,
where contextual licensing leaves the third box open. -/
theorem load_diverges :
    answer (competenceDefaultLoad .some_) = .no ∧
      answer (contextual 2 .some_) = .dontKnow := by
  decide

/-- For the knowledgeable speaker the blocked default changes nothing. -/
theorem load_agrees_of_knowledgeable (q : QUtt) :
    answer (competenceDefaultLoad q) = answer (contextual 3 q) := by
  revert q; decide

/-! ### The trial types -/

/-- How many boxes Farmer Brown looked into. -/
def access? (r : Datum) : Option (Fin 4) :=
  match r.feature? "boxesSeen" with
  | some "2" => some 2
  | some "3" => some 3
  | _ => none

/-- The quantifier of his statement. -/
def quantifier? (r : Datum) : Option QUtt :=
  match r.feature? "quantifier" with
  | some "some" => some .some_
  | some "all" => some .all
  | _ => none

/-- The response the paper expects. -/
def expected? (r : Datum) : Option Answer :=
  match r.feature? "expectedResponse" with
  | some "yes" => some .yes
  | some "no" => some .no
  | some "dontKnow" => some .dontKnow
  | _ => none

/-- The expected response in each trial type is the contextual-licensing answer. -/
theorem rows_expected :
    ∀ r ∈ Examples.all, ∀ a ∈ access? r, ∀ q ∈ quantifier? r, ∀ e ∈ expected? r,
      answer (contextual a q) = e := by
  decide

end BaleEtAl2025
