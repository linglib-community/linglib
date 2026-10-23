module

public import Studies.Yalcin2007

/-!
# Klinedinst and Rothschild (2012): Connectives without Truth Tables

This file formalizes Klinedinst and Rothschild's parameter treatment of the dynamic effects
of *and* and *or*. Truth is relative to a world and to an information parameter, the set of
worlds that epistemic modals quantify over, (46) and (47), the domain semantics of
Yalcin (`Yalcin2007.Sentence`), and the connectives shift that parameter for their
second clause: *a and b* evaluates *b* against the parameter updated with *a*, (49), and
*a or b* against the parameter updated with the negation of *a*, (50) (`conj`, `disj`). This
is what lets an epistemic modal sit in a disjunct: *the dog is in the backyard or it must be
in the kitchen*, (36), says that the dog is in the backyard or that the information, given
that it is not, puts it in the kitchen (`disj_must_iff`), disjunctive syllogism fails for it,
(38)–(40) (`not_disjunctive_syllogism`), and so does commutation, (104) (`disj_not_comm`).
The non-truth-tabular uses of §1 are the assertion forms of (60) that keep only the dynamic
effect: *and* with its first clause shifting the parameter alone is the conditional of (52),
(61) and (62), and *or* with both clauses entailed asserts its first disjunct and the second
under the negation of the first, (66) and (67) (`Use.interpret`); the other two forms collapse
into the normal connectives (`doubleEntailment_and`, `shift_disj`). A normal conjunction whose
second conjunct needs worlds where the first fails is a contradiction, (68)
(`not_conj_might_compl`).

## Implementation notes

* The context parameter and the presuppositional definedness of (48) are omitted, as is the
  inner and outer sphere refinement of §4.2 for counterfactual morphology; a sentence is a
  function of the information parameter and the world.

## References

* [klinedinst-rothschild-2012]
* [yalcin-2007]
-/

@[expose] public section

namespace KlinedinstRothschild2012

open Yalcin2007

variable {W : Type*} (a b : Sentence W)

/-- The information parameter updated with `a`, the `sᵃ` of §4. -/
def update (s : Set W) : Set W := {w' ∈ s | a s w'}

/-- Conjunction, (49), evaluates the second conjunct against the parameter updated with the
first. -/
def conj : Sentence W := fun s w ↦ a s w ∧ b (update a s) w

/-- Disjunction, (50), evaluates the second disjunct against the parameter updated with the
negation of the first. -/
def disj : Sentence W := fun s w ↦ a s w ∨ b (update aᶜ s) w

/-- In the conditional, (52), the antecedent shifts the parameter, and a modal in the consequent
quantifies over the result. -/
def ifThen : Sentence W := fun s w ↦ b (update a s) w

/-! ### Epistemic modals under *or*, §3.2 -/

/-- *The dog is in the backyard or it must be in the kitchen* holds iff it is in the backyard or the
information puts it in the kitchen otherwise (36). -/
theorem disj_must_iff (p q : Set W) (s : Set W) (w : W) :
    disj (Sentence.ofProp p) (Sentence.ofProp q).must s w ↔
      w ∈ p ∨ ∀ w' ∈ s, w' ∉ p → w' ∈ q := by
  simp [disj, Sentence.must, Sentence.ofProp, update]

theorem disjunctive_syllogism (p q : Set W) :
    StandardConsequence [disj (Sentence.ofProp p) (Sentence.ofProp q), (Sentence.ofProp q)ᶜ]
      (Sentence.ofProp p) := by
  intro s w h
  rcases h _ List.mem_cons_self with hp | hq
  · exact hp
  · exact absurd hq (h _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Disjunctive syllogism fails with a modal disjunct ((38)–(40)). -/
theorem not_disjunctive_syllogism :
    ¬ StandardConsequence
      [disj (Sentence.ofProp {true}) (Sentence.ofProp {false}).must,
        (Sentence.ofProp {false}).mustᶜ]
      (Sentence.ofProp ({true} : Set Bool)) := by
  intro h
  have := h Set.univ false
    (by simp [disj, Sentence.must, Sentence.ofProp, update, Set.mem_singleton_iff])
  simp [Sentence.ofProp, Set.mem_singleton_iff] at this

/-- (104): the dynamic effect is asymmetric, so the disjuncts do not commute: with the modal
disjunct first, the same model falsifies the disjunction. -/
theorem disj_not_comm :
    ¬ ∀ (a b : Sentence Bool) (s : Set Bool) (w : Bool), disj a b s w ↔ disj b a s w := by
  intro h
  have := (h (Sentence.ofProp {true}) (Sentence.ofProp {false}).must Set.univ false).1
    (by simp [disj, Sentence.must, Sentence.ofProp, update, Set.mem_singleton_iff])
  simp [disj, Sentence.must, Sentence.ofProp, Set.mem_singleton_iff] at this

/-! ### The assertion forms of (60), §5 -/

/-- The connective whose dynamic effect is kept. -/
inductive Connective
  | and
  | or
  deriving DecidableEq, Repr

/-- The three assertion forms of `a ∗ b`, (60), are the normal connective, both clauses entailed
with the second under the shifted parameter, or the first clause used only to shift the
parameter of the second. -/
inductive Use
  | normal
  | doubleEntailment
  | shift
  deriving DecidableEq, Repr

/-- The parameter the second clause is evaluated under, (49) and (50). -/
def Connective.shift : Connective → Sentence W → Set W → Set W
  | .and, a, s => update a s
  | .or, a, s => update aᶜ s

/-- The content of `a ∗ b` on each assertion form, the table of (60). -/
def Use.interpret : Use → Connective → Sentence W → Sentence W → Sentence W
  | .normal, .and, a, b => conj a b
  | .normal, .or, a, b => disj a b
  | .doubleEntailment, c, a, b => fun s w ↦ a s w ∧ b (c.shift a s) w
  | .shift, c, a, b => fun s w ↦ b (c.shift a s) w

theorem doubleEntailment_and : Use.doubleEntailment.interpret .and a b = conj a b := rfl

theorem shift_disj : Use.shift.interpret .or a b = ifThen aᶜ b := rfl

/-- The non-truth-tabular *and*, (1): the first conjunct only shifts the parameter, which is
the conditional of (52). -/
theorem shift_and : Use.shift.interpret .and a b = ifThen a b := rfl

/-- The non-truth-tabular *or*, (2) and (66): the first disjunct is asserted, and the second
under the parameter updated with its negation, (67). -/
theorem doubleEntailment_disj :
    Use.doubleEntailment.interpret .or a b = fun s w ↦ a s w ∧ b (update aᶜ s) w := rfl

/-- *The police show up, and there might be trouble* is true iff some parameter world where the
police show up has trouble ((61) and (62)). -/
theorem cond_might_iff (p t : Set W) (s : Set W) (w : W) :
    ifThen (Sentence.ofProp p) (Sentence.ofProp t).might s w ↔
      ∃ w' ∈ s, w' ∈ p ∧ w' ∈ t := by
  simp [ifThen, Sentence.might, Sentence.ofProp, update, and_assoc]

/-- (68): *John is here and he might not be* is a contradiction, the second conjunct needing
a parameter with worlds in which the first fails. -/
theorem not_conj_might_compl (p : Set W) (s : Set W) (w : W) :
    ¬ conj (Sentence.ofProp p) (Sentence.ofProp p)ᶜ.might s w := by
  simp [conj, Sentence.might, Sentence.ofProp, update]

end KlinedinstRothschild2012
