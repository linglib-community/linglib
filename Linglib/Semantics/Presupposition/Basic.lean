module

public import Linglib.Logic.Trivalent.Pointwise

/-!
# Presupposition in trivalent semantics

A sentence with a presupposition denotes a trivalent proposition `W → SignType`, true or false
where its presupposition holds and `0` where it fails. A trigger presupposing `A` and asserting
`B` is the indicator `{w | A w}.indicator fun w ↦ ofProp (B w)`, its presupposition is its support
`Function.support p`, and it holds at `w` when `p w = 1`. Theories of projection differ in their
connectives: the classical connectives are Weak Kleene (`SignType.meetWeak`), Karttunen's filtering
connectives are Peters' Middle Kleene (`SignType.meetMiddle`, `SignType.joinMiddle`), Bochvar's
truth operator is `fun w ↦ ofProp (p w = 1)`, and the rival Strong Kleene and Belnap connectives
are `⊓`, `⊔`, `SignType.meetBelnap` and `SignType.joinBelnap`. Each projection rule is a
characterization of its connective (`SignType.meetMiddle_eq_zero_iff` for Karttunen's filtering
conjunction), and quantified presuppositions project by the trivalent quantifiers of
`Logic/Trivalent/Pointwise.lean`. Two-dimensional accounts, which read an assertion where its
presupposition fails, use `TwoDim` (`Semantics/ConventionalImplicature.lean`).

## Main definitions

* `Presupposition.strawsonEntails`: von Fintel's entailment, with the conclusion's presupposition
  as a premise.
* `Presupposition.presupOfReferent`: the definite-description combinator.

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
-/

@[expose] public section

namespace Presupposition

open Classical Trivalent

variable {W : Type*}

/-! ### Strawson entailment -/

/-- Strawson entailment ([von-fintel-1999]) requires `q` to be true wherever `p` is true and `q`
is defined, the conclusion's presupposition being a premise added to the entailment rather than
something the entailment delivers. -/
def strawsonEntails (p q : W → SignType) : Prop := ∀ w, p w = 1 → q w ≠ 0 → q w = 1

/-- Strawson entailment is the disjointness of the premise's truth and the conclusion's falsity. -/
theorem strawsonEntails_iff_disjoint {p q : W → SignType} :
    strawsonEntails p q ↔ Disjoint (posSupport p) (negSupport q) := by
  rw [Set.disjoint_left]
  refine forall_congr' fun w ↦ ⟨fun h hp hq ↦ ?_, fun h hp hq ↦ ?_⟩
  · simp only [mem_posSupport, mem_negSupport] at hp hq
    simp [hq] at h; exact h hp
  · simp only [mem_posSupport, mem_negSupport] at h
    cases hw : q w <;> simp_all

/-- Strawson entailment is not transitive, since an undefined middle term discharges both premises
vacuously, the well-known failure of [von-fintel-1999]'s notion; so it supports no `Preorder`. -/
theorem strawsonEntails_not_trans :
    ¬ ∀ p q r : Unit → SignType,
      strawsonEntails p q → strawsonEntails q r → strawsonEntails p r := by
  intro h
  have := h 1 0 (-1) (fun _ _ h ↦ absurd rfl h) (fun _ h ↦ by simp at h) () rfl (by simp)
  simp at this

/-! ### Definite descriptions -/

/-- The definite-description combinator, for a partial selector `referent` returning the referent
at each world (or `none` where none is determined) and a `scope` asserted of it, is the scope's
value at the referent where one is selected and undefined elsewhere. Every definite denotation
instantiates the selector, with the Russellian iota `iota` over a restrictor, over the
restrictor conjoined with identity to an antecedent, or with Donnellan's attributive use. -/
noncomputable def presupOfReferent {E : Type*} (referent : W → Option E) (scope : E → W → Prop) :
    W → SignType :=
  fun w ↦ (referent w).elim 0 fun e ↦ SignType.ofProp (scope e w)

section PresupOfReferent

variable {E : Type*} {referent : W → Option E} {scope : E → W → Prop} {w : W}

@[simp] theorem presupOfReferent_eq_zero_iff :
    presupOfReferent referent scope w = 0 ↔ referent w = none := by
  cases h : referent w <;> simp [presupOfReferent, h]

theorem presupOfReferent_of_some {e : E} (h : referent w = some e) :
    presupOfReferent referent scope w = SignType.ofProp (scope e w) := by
  simp [presupOfReferent, h]

theorem presupOfReferent_of_none (h : referent w = none) :
    presupOfReferent referent scope w = 0 := by
  simp [presupOfReferent, h]

end PresupOfReferent

end Presupposition
