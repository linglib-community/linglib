module

public import Linglib.Logic.Trivalent.Pointwise

/-!
# Presupposition in trivalent semantics

A sentence with a presupposition denotes a trivalent proposition `W → Trivalent`, true or false
where its presupposition holds and undefined where it fails. A trigger presupposing `A` and
asserting `B` is the conditional event `Trivalent.condEvent A B`, its
presupposition is where it is defined, `(Trivalent.gapExt p)ᶜ`, and it holds at `w` when
`p w = .true`. Theories of projection differ in their
connectives: the classical connectives are Weak Kleene (`Trivalent.meetWeak`), Karttunen's filtering
connectives are Peters' Middle Kleene (`Trivalent.meetMiddle`, `Trivalent.joinMiddle`), Bochvar's
truth operator is `fun w ↦ ofProp (p w = .true)`, and the rival Strong Kleene and Belnap connectives
are `⊓`, `⊔`, `Trivalent.meetBelnap` and `Trivalent.joinBelnap`. Each projection rule is a
characterization of its connective (`Trivalent.meetMiddle_eq_undefined_iff` for Karttunen's
filtering conjunction), and quantified presuppositions project by the trivalent quantifiers of
`Logic/Trivalent/Pointwise.lean`. Two-dimensional accounts, which read an assertion where its
presupposition fails, use `TwoDim` (`Semantics/Presupposition/TwoDimensional.lean`).

## Main definitions

* `Presupposition.strawsonEntails`: von Fintel's entailment, with the conclusion's presupposition
  as a premise.
* `Presupposition.presupOfReferent`: the definite-description combinator.
* `Presupposition.factive`: the sentence of a factive predicate over any attitude.

## Main results

* `Presupposition.strawsonEntails_iff_disjoint`: Strawson entailment is the disjointness of the
  premise's truth and the conclusion's falsity.
* `Presupposition.strawsonEntails_not_trans`: Strawson entailment is not transitive.

## References

* [heim-1983]
* [karttunen-1973]
* [peters-1979]
* [bochvar-1938]
* [von-fintel-1999]
* [kiparsky-kiparsky-1970]
-/

@[expose] public section

namespace Presupposition

open Classical Trivalent

variable {W : Type*}

/-! ### Strawson entailment -/

/-- Strawson entailment ([von-fintel-1999]) requires `q` to be true wherever `p` is true and `q`
is defined, the conclusion's presupposition being a premise added to the entailment rather than
something the entailment delivers. -/
def strawsonEntails (p q : W → Trivalent) : Prop :=
  ∀ w, p w = .true → q w ≠ .undefined → q w = .true

/-- Strawson entailment is the disjointness of the premise's truth and the conclusion's falsity. -/
theorem strawsonEntails_iff_disjoint {p q : W → Trivalent} :
    strawsonEntails p q ↔ Disjoint (Trivalent.posExt p) (Trivalent.negExt q) := by
  rw [Set.disjoint_left]
  refine forall_congr' fun w ↦ ⟨fun h hp hq ↦ ?_, fun h hp hq ↦ ?_⟩
  · simp only [Trivalent.mem_posExt, Trivalent.mem_negExt] at hp hq
    simp [hq] at h; exact h hp
  · simp only [Trivalent.mem_posExt, Trivalent.mem_negExt] at h
    cases hw : q w <;> simp_all

/-- Strawson entailment is not transitive, since an undefined middle term discharges both premises
vacuously, the well-known failure of [von-fintel-1999]'s notion; so it supports no `Preorder`. -/
theorem strawsonEntails_not_trans :
    ¬ ∀ p q r : Unit → Trivalent,
      strawsonEntails p q → strawsonEntails q r → strawsonEntails p r := by
  intro h
  have := h (fun _ ↦ .true) (fun _ ↦ .undefined) (fun _ ↦ .false) (fun _ _ h ↦ absurd rfl h)
    (fun _ h ↦ by simp at h) () rfl (by simp)
  simp at this

/-! ### Definite descriptions -/

/-- The definite-description combinator, for a partial selector `referent` returning the referent
at each world (or `none` where none is determined) and a `scope` asserted of it, is the scope's
value at the referent where one is selected and undefined elsewhere. Every definite denotation
instantiates the selector, with the Russellian iota `iota` over a restrictor, over the
restrictor conjoined with identity to an antecedent, or with Donnellan's attributive use. -/
noncomputable def presupOfReferent {E : Type*} (referent : W → Option E) (scope : E → W → Prop) :
    W → Trivalent :=
  fun w ↦ (referent w).elim .undefined fun e ↦ Trivalent.ofProp (scope e w)

section PresupOfReferent

variable {E : Type*} {referent : W → Option E} {scope : E → W → Prop} {w : W}

@[simp] theorem presupOfReferent_eq_undefined_iff :
    presupOfReferent referent scope w = .undefined ↔ referent w = none := by
  cases h : referent w <;> simp [presupOfReferent, h]

@[simp] theorem presupOfReferent_eq_true_iff :
    presupOfReferent referent scope w = .true ↔ ∃ e, referent w = some e ∧ scope e w := by
  cases h : referent w <;> simp [presupOfReferent, h]

@[simp] theorem presupOfReferent_eq_false_iff :
    presupOfReferent referent scope w = .false ↔ ∃ e, referent w = some e ∧ ¬ scope e w := by
  cases h : referent w <;> simp [presupOfReferent, h]

/-- Negation is a hole for the presupposition of a definite. -/
theorem presupOfReferent_not :
    presupOfReferent referent (fun e w ↦ ¬ scope e w) w = (presupOfReferent referent scope w)ᶜ :=
  Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff (by simp) (by simp)

theorem presupOfReferent_of_some {e : E} (h : referent w = some e) :
    presupOfReferent referent scope w = Trivalent.ofProp (scope e w) := by
  simp [presupOfReferent, h]

theorem presupOfReferent_of_none (h : referent w = none) :
    presupOfReferent referent scope w = .undefined := by
  simp [presupOfReferent, h]

end PresupOfReferent

/-! ### Factive predicates

A factive predicate, *know* or *regret that p*, presupposes its complement and asserts an attitude
toward it. The attitude is arbitrary, the doxastic box of *know* or the preference of *regret*.
An attitude `att` entails its complement when `att ≤ id`, and the predicate that asserts the
complement beside the attitude is `att ⊓ id`; a factive sentence is true where that predicate is
and false, by `Trivalent.negExt_condEvent`, only where the complement is true besides. -/

/-- The sentence of a factive predicate presupposes the complement `p` and asserts the attitude
`att` toward it ([kiparsky-kiparsky-1970]). -/
noncomputable def factive (att : (W → Prop) → W → Prop) (p : W → Prop) : W → Trivalent :=
  condEvent p (att p)

section Factive

variable {att : (W → Prop) → W → Prop} {p : W → Prop} {w : W}

@[simp] theorem factive_eq_true_iff : factive att p w = .true ↔ p w ∧ att p w := by
  simp [factive]

@[simp] theorem factive_eq_false_iff : factive att p w = .false ↔ p w ∧ ¬ att p w := by
  simp [factive]

@[simp] theorem factive_eq_undefined_iff : factive att p w = .undefined ↔ ¬ p w := by
  simp [factive]

/-- A factive sentence is true where the predicate that asserts its complement holds. -/
theorem posExt_factive (att : (W → Prop) → W → Prop) (p : W → Prop) :
    posExt (factive att p) = {w | (att ⊓ id) p w} := by
  ext w
  simp [and_comm]

end Factive

end Presupposition
