module

public import Mathlib.Data.Set.Insert
public import Linglib.Data.Examples.Yalcin2007
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Modality.DomainSemantics

/-!
# Yalcin (2007): Epistemic Modals

This file formalizes Yalcin's argument for domain semantics, whose sentences, modals and acceptance
are `DomainSemantics`, from the puzzle of epistemic contradictions, sentences of the form *it is
raining and it might not be raining* or *it is not raining and it might be raining*. Unlike
Moore-paradoxical sentences, which are unassertable but embed happily under *suppose* and in
conditional antecedents, epistemic contradictions are unsupposable, and a relational semantics
cannot explain this, since it makes them true at some world (`exists_relational_contra`). Domain
semantics evaluates a sentence at an index of an information parameter, a set of worlds, and a
world, with the epistemic possibility modal quantifying existentially over the parameter. Attitude
verbs shift the parameter to the attitude state and quantify over it (`supposes`), so the universal
quantifier of *suppose* is trumped by an embedded modal (`supposes_might_iff`), an attitude with an
embedded possibility modal is the attitude's dual (`supposes_might_iff_not_supposes_compl`), and no
state of supposition accepts an epistemic contradiction (`not_supposes_contra`). An indicative
conditional shifts the parameter to the largest nonempty substate accepting its antecedent and
quantifies over it (`ifThen`), so conditionals with an epistemic contradiction as antecedent are
never true (`ifThen_contra_false`), and the conditional with an epistemic necessity in its
consequent is equivalent to the plain one (`ifThen_must_iff`). Three notions of consequence are
compared. Standard and diagonal consequence preserve truth at points, the latter at points whose
world lies in the information state; informational consequence preserves acceptance, truth
throughout a state evaluated at that state. Informational consequence validates Łukasiewicz's
principle, epistemic contradiction, and the nonfactivity of epistemic possibility together
(`lukasiewicz`, `epistemic_contradiction`, `nonfactivity`), which no classical consequence relation
can, while diagonal consequence rejects epistemic contradiction
(`not_diagonal_epistemic_contradiction`); on factual sentences informational consequence is
classical (`factual_classical`). The dual necessity modal yields the same results
(`not_accepted_neg_must`).

## Implementation notes

Sentences form a Boolean algebra pointwise: negation is the complement `φᶜ`, conjunction the meet
`φ ⊓ ψ`, and the absurd sentence `⊥`. The relational semantics is Kripke's diamond `◇[R]`. The
largest nonempty substate accepting the antecedent is characterized rather than constructed, and a
conditional is true only if it exists. The probabilistic extension of the information parameter in
the paper's seventh section is not modelled.

## References

* [yalcin-2007]
* [kaplan-1989]
* [veltman-1996]
* [stephenson-2007]
-/

@[expose] public section

namespace Yalcin2007

open DomainSemantics Sentence ModalLogic

variable {W : Type*}

/-- The epistemic contradiction *not p and it might be that p*. -/
def contra (p : Set W) : Sentence W := (ofProp p)ᶜ ⊓ (ofProp p).might

/-- The epistemic contradiction *p and it might be that not p*. -/
def contra' (p : Set W) : Sentence W := ofProp p ⊓ (ofProp p)ᶜ.might

theorem not_accepted_contra {p s : Set W} (hs : s.Nonempty) : ¬ (contra p).AcceptedIn s := by
  intro h
  obtain ⟨w, hw⟩ := hs
  obtain ⟨-, w', hw', hp⟩ := h w hw
  exact (h w' hw').1 hp

theorem not_accepted_contra' {p s : Set W} (hs : s.Nonempty) : ¬ (contra' p).AcceptedIn s := by
  intro h
  obtain ⟨w, hw⟩ := hs
  obtain ⟨-, w', hw', hp⟩ := h w hw
  exact hp (h w' hw').1

/-! ### Relational semantics -/

theorem exists_relational_contra :
    ∃ (R : SetRel Bool Bool) (p : Set Bool) (w : Bool), w ∉ p ∧ ◇[R] (· ∈ p) w :=
  ⟨Set.univ, {true}, false, by simp, true, trivial, rfl⟩

/-! ### Attitudes -/

variable {φ ψ : Sentence W} {s : Set W} {w : W}

/-- *x supposes φ*: φ holds at every world compatible with the supposition, relative to the
state of supposition, which the verb makes the information parameter. -/
def supposes (S : W → Set W) (φ : Sentence W) : Sentence W :=
  fun _ w ↦ ∀ w' ∈ S w, φ (S w) w'

theorem supposes_iff_accepted {S : W → Set W} : supposes S φ s w ↔ φ.AcceptedIn (S w) :=
  Iff.rfl

theorem supposes_might_iff {S : W → Set W} (hne : (S w).Nonempty) :
    supposes S φ.might s w ↔ ∃ w' ∈ S w, φ (S w) w' := by
  constructor
  · intro h; obtain ⟨v, hv⟩ := hne; exact h v hv
  · intro h _ _; exact h

theorem supposes_might_iff_not_supposes_compl {S : W → Set W} (hne : (S w).Nonempty) :
    supposes S φ.might s w ↔ ¬ supposes S φᶜ s w := by
  rw [supposes_might_iff hne]
  simp [supposes]

theorem not_supposes_contra {S : W → Set W} {p : Set W} (hne : (S w).Nonempty) :
    ¬ supposes S (contra p) s w :=
  not_accepted_contra hne

/-! ### Indicative conditionals -/

/-- `s'` is the largest nonempty substate of `s` accepting `α`. -/
def IsMaxAccepting (s : Set W) (α : Sentence W) (s' : Set W) : Prop :=
  s' ⊆ s ∧ s'.Nonempty ∧ α.AcceptedIn s' ∧
    ∀ t ⊆ s, t.Nonempty → α.AcceptedIn t → t ⊆ s'

/-- The indicative conditional: the consequent holds throughout the largest nonempty substate
accepting the antecedent, relative to that substate. -/
def ifThen (α ψ : Sentence W) : Sentence W :=
  fun s _ ↦ ∃ s', IsMaxAccepting s α s' ∧ ψ.AcceptedIn s'

theorem isMaxAccepting_ofProp (p : Set W) (hne : (s ∩ p).Nonempty) :
    IsMaxAccepting s (ofProp p) (s ∩ p) :=
  ⟨Set.inter_subset_left, hne, fun _ hw ↦ hw.2, fun _ ht _ hacc w hw ↦ ⟨ht hw, hacc w hw⟩⟩

theorem ifThen_contra_false {p : Set W} : ¬ ifThen (contra p) ψ s w := by
  rintro ⟨s', ⟨-, hne, hacc, -⟩, -⟩
  exact not_accepted_contra hne hacc

theorem ifThen_must_iff {α : Sentence W} : ifThen α ψ.must s w ↔ ifThen α ψ s w := by
  constructor
  · rintro ⟨s', hmax, h⟩
    obtain ⟨v, hv⟩ := hmax.2.1
    exact ⟨s', hmax, h v hv⟩
  · rintro ⟨s', hmax, h⟩
    exact ⟨s', hmax, fun _ _ ↦ h⟩

/-! ### Consequence -/

theorem lukasiewicz (p : Set W) : InformationalConsequence [(ofProp p)ᶜ] (ofProp p).mightᶜ := by
  intro s h w hw ⟨w', hw', hp⟩
  exact h _ List.mem_cons_self w' hw' hp

theorem epistemic_contradiction (p : Set W) : InformationalConsequence [contra p] ⊥ := by
  intro s h w hw
  exact absurd (h _ List.mem_cons_self) (not_accepted_contra ⟨w, hw⟩)

theorem nonfactivity :
    ¬ InformationalConsequence [(ofProp {true}).might] (ofProp ({true} : Set Bool)) := by
  intro h
  have := h Set.univ (by
    simp only [List.mem_singleton, forall_eq]
    intro _ _; exact ⟨true, trivial, rfl⟩) false trivial
  simp [ofProp] at this

theorem not_diagonal_epistemic_contradiction :
    ¬ DiagonalConsequence [contra ({true} : Set Bool)] ⊥ := by
  intro h
  have := h Set.univ false trivial (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨by simp [ofProp], true, trivial, rfl⟩)
  simp at this

theorem not_diagonal_factivity :
    ¬ DiagonalConsequence [(ofProp {true}).might] (ofProp ({true} : Set Bool)) := by
  intro h
  have := h Set.univ false trivial (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨true, trivial, rfl⟩)
  simp [ofProp] at this

theorem factual_classical (p q : Set W) :
    InformationalConsequence [(ofProp p)ᶜ ⊓ ofProp q] ⊥ ↔
      InformationalConsequence [ofProp q] (ofProp p) := by
  constructor
  · intro h s hq w hw
    by_contra hp
    have := h {w} (by
      simp only [List.mem_singleton, forall_eq]
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      exact ⟨hp, hq _ List.mem_cons_self w hw⟩) w rfl
    simp at this
  · intro h s hs w hw
    have hc := hs _ List.mem_cons_self
    refine absurd (h s ?_ w hw) (hc w hw).1
    simp only [List.mem_singleton, forall_eq]
    exact fun v hv ↦ (hc v hv).2

theorem not_classical :
    InformationalConsequence [contra ({true} : Set Bool)] ⊥ ∧
      ¬ InformationalConsequence [(ofProp {true}).might] (ofProp ({true} : Set Bool)) :=
  ⟨epistemic_contradiction _, nonfactivity⟩

/-! ### Epistemic necessity -/

theorem not_accepted_neg_must {p : Set W} (hs : s.Nonempty) :
    ¬ ((ofProp p)ᶜ ⊓ (ofProp p).must).AcceptedIn s := by
  intro h
  obtain ⟨w, hw⟩ := hs
  exact (h w hw).1 ((h w hw).2 w hw)

end Yalcin2007
