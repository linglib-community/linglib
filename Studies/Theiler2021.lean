module

public import Linglib.Logic.Modal.Basic
public import Linglib.Discourse.SpeechAct
public import Linglib.Semantics.Questions.Polar
public import Linglib.Data.Examples.Theiler2021

/-!
# Theiler (2021): Denn as a Highlighting-Sensitive Particle

This file formalizes [theiler-2021]'s account of the German discourse particle *denn* in polar
questions, wh-questions and conditional antecedents. The particle is discourse-anaphoric: it
picks up a salient previous move or piece of contextual information, (6)–(9). It is sensitive
not to the answerhood conditions of its clause but to the clause's highlighted content in the
sense of [roelofsen-farkas-2015], the n-place property with n the number of wh-elements: in
the Two Annas scenario, (4), a wh-question and a polar question with the same answerhood
conditions differ in whether *denn* is felicitous. The felicity condition, (19) and (37), is
that the speaker considers learning an instantiation of a highlighted property a necessary
precondition for proceeding from the previous move, where proceeding from an imperative is
carrying it out, from a question answering it, and from an assertion accepting it (section 3.3).

The account is formalized over information states. A proposition's instantiations are the
values of the highlighted property, `instantiations`, a single proposition for a declarative or
polar question, `instantiations_zero`; `Denn` states that every state from which the speaker
proceeds has learned one of the highlighted instantiations. For a polar question this is
necessity of the highlighted proposition itself, `denn_singleton`, so two questions with the
same resolution conditions can differ, `denn_pair_not_denn_singleton`: the wh-question of Two
Annas is felicitous where the polar question, which shares its meaning `polar_eq_sup`, is
not. Disjoined *denn*-questions, (32a), are infelicitous because each disjunct signals that
learning it suffices and a sufficient precondition is not necessary,
`not_denn_of_sufficient_of_sufficient`, while conjoined ones, (32c), name two necessary
preconditions, `denn_singleton_and_denn_singleton_iff`; an alternative question, which
highlights both disjuncts, licenses *denn* more demandingly than the polar disjunctive question
highlighting their disjunction, `denn_pair_imp_denn_union`. In a conditional antecedent *denn*
marks the antecedent as necessary for the consequent, which the conditional makes sufficient,
so the conditional is perfected, `perfection`, and a disjunctive antecedent cannot carry
*denn*, `subset_of_disjunctive_antecedent`. The modalized condition (73), that the speaker
considers it possible that learning an instantiation is necessary for the recipient, reduces to
(19) in questions, where the recipient is the speaker, because possible necessity is necessity
over the speaker's doxastic accessibility, `felicity_question`.

## Implementation notes

Proceeding is a predicate on information states, the states from which the speaker can act
as the previous move indicated; the paper's five clauses defining it by the form of the move
are left to prose. Learning a proposition is the state's entailing it. The modalized condition
is stated over the accessibility relations of the interlocutors' doxastic states, assumed to be
KD45 frames as in doxastic logic, whence the collapse of `◇□` to `□` that the paper assumes as
full introspection. The treatment of *überhaupt* (section 5), the causal conjunction (section
6) and the comparison with Csipak and Zobel are not formalized beyond the modalized condition.
The examples are the rows of `Data.Examples.Theiler2021`.

## References

* [theiler-2021]
* [roelofsen-farkas-2015]
* [gutzmann-2015]
* [csipak-zobel-2014]
* [csipak-zobel-2016]
* [farkas-bruce-2010]
-/

@[expose] public section

namespace Theiler2021

open ModalLogic Question

/-! ### Highlighted content (section 3.1) -/

section Highlighting

variable {D W : Type*} {n : ℕ}

/-- An n-place property over worlds: the content a clause with n wh-elements highlights. -/
abbrev Property (D W : Type*) (n : ℕ) := (Fin n → D) → Set W

/-- The instantiations of a property: the propositions it yields for tuples of individuals. -/
def instantiations (f : Property D W n) : Set (Set W) := Set.range f

theorem instantiations_zero (f : Property D W 0) : instantiations f = {f default} :=
  Set.range_unique

theorem mem_instantiations (f : Property D W n) (d : Fin n → D) : f d ∈ instantiations f :=
  Set.mem_range_self d

end Highlighting

/-! ### Preconditions for proceeding (sections 3.2–3.3) -/

section Precondition

variable {W : Type*}

/-- Learning the proposition is a necessary precondition for proceeding: every state from
which the speaker proceeds has learned it. -/
def Necessary (Proceed : Set W → Prop) (E : Set W → Prop) : Prop := ∀ s, Proceed s → E s

/-- Learning the proposition is a sufficient precondition for proceeding. -/
def Sufficient (Proceed : Set W → Prop) (E : Set W → Prop) : Prop := ∀ s, E s → Proceed s

/-- The felicity condition for *denn*, (19) and (37): learning an instantiation of a
highlighted property, one of the propositions in `H`, is a necessary precondition. -/
def Denn (Proceed : Set W → Prop) (H : Set (Set W)) : Prop :=
  Necessary Proceed λ s => ∃ p ∈ H, s ⊆ p

variable {Proceed : Set W → Prop} {p q : Set W} {H : Set (Set W)}

theorem denn_singleton : Denn Proceed {p} ↔ Necessary Proceed (· ⊆ p) := by
  simp [Denn, Necessary]

theorem denn_pair_not_denn_singleton (h : ∀ s, Proceed s ↔ s ⊆ p ∨ s ⊆ q) (hq : ¬ q ⊆ p) :
    Denn Proceed {p, q} ∧ ¬ Denn Proceed {p} := by
  refine ⟨λ s hs => ?_, λ hd => hq (denn_singleton.1 hd q ((h q).2 (Or.inr subset_rfl)))⟩
  rcases (h s).1 hs with hp | hq'
  · exact ⟨p, by simp, hp⟩
  · exact ⟨q, by simp, hq'⟩

-- (4), (20)
theorem twoAnnas (hp : p ≠ Set.univ) :
    Denn (· ∈ polar p) {p, pᶜ} ∧ ¬ Denn (· ∈ polar p) {p} :=
  denn_pair_not_denn_singleton (λ _ => mem_polar)
    λ h => hp (by simpa using Set.compl_subset_iff_union.1 h)

theorem not_necessary_of_sufficient (h : Sufficient Proceed (· ⊆ p)) (hpq : ¬ p ⊆ q) :
    ¬ Necessary Proceed (· ⊆ q) :=
  λ hn => hpq (hn p (h p subset_rfl))

/-- Disjoined *denn*-questions, (32a): disjoining signals that a positive answer to either
question suffices, and then neither highlighted proposition is necessary. -/
theorem not_denn_of_sufficient_of_sufficient (h₁ : Sufficient Proceed (· ⊆ p))
    (h₂ : Sufficient Proceed (· ⊆ q)) (hpq : ¬ p ⊆ q) (hqp : ¬ q ⊆ p) :
    ¬ Denn Proceed {p} ∧ ¬ Denn Proceed {q} :=
  ⟨λ h => not_necessary_of_sufficient h₂ hqp (denn_singleton.1 h),
    λ h => not_necessary_of_sufficient h₁ hpq (denn_singleton.1 h)⟩

/-- Conjoined *denn*-questions, (32c): two necessary preconditions, the conjunction of which
is necessary. -/
theorem denn_singleton_and_denn_singleton_iff :
    Denn Proceed {p} ∧ Denn Proceed {q} ↔ Denn Proceed {p ∩ q} := by
  simp only [denn_singleton, Necessary, Set.subset_inter_iff, imp_and, forall_and]

/-- If an alternative question (35) licenses *denn*, so does the corresponding polar disjunctive
question (36). -/
theorem denn_pair_imp_denn_union (h : Denn Proceed {p, q}) : Denn Proceed {p ∪ q} :=
  λ s hs => by
    obtain ⟨r, hr, hsr⟩ := h s hs
    refine ⟨p ∪ q, rfl, ?_⟩
    rcases hr with rfl | rfl
    · exact hsr.trans Set.subset_union_left
    · exact hsr.trans Set.subset_union_right

/-! ### Conditional antecedents (section 4.5) -/

theorem necessary_subset_iff : Necessary (· ⊆ q) (· ⊆ p) ↔ q ⊆ p :=
  ⟨λ h => h q subset_rfl, λ h _ hs => hs.trans h⟩

theorem sufficient_subset_iff : Sufficient (· ⊆ q) (· ⊆ p) ↔ p ⊆ q :=
  ⟨λ h => h p subset_rfl, λ h _ hs => hs.trans h⟩

/-- Conditional perfection, (47): the conditional makes the antecedent sufficient and *denn*
marks it necessary, so the two are equivalent. -/
theorem perfection : Sufficient (· ⊆ q) (· ⊆ p) ∧ Denn (· ⊆ q) {p} ↔ p = q := by
  rw [sufficient_subset_iff, denn_singleton, necessary_subset_iff, Set.Subset.antisymm_iff]

/-- A disjunctive antecedent, (48b): two sufficient conditions, of which *denn* on one would
make it entailed by the other. -/
theorem subset_of_disjunctive_antecedent {p₁ p₂ : Set W} (h : Sufficient (· ⊆ q) (· ⊆ p₁ ∪ p₂))
    (hd : Denn (· ⊆ q) {p₁}) : p₂ ⊆ p₁ :=
  Set.subset_union_right.trans
    ((sufficient_subset_iff.1 h).trans (necessary_subset_iff.1 (denn_singleton.1 hd)))

end Precondition

/-! ### The interrogative flip (section 6.2) -/

section Flip

variable {W : Type*}

open Discourse.SpeechAct (Force)

/-- The recipient of information in a move of Table 1 is the participant without epistemic
authority over its content, the speaker of a question and the hearer of an assertion. -/
def recipient (f : Force) : Discourse.Role := f.authority.other

/-- The modalized felicity condition (73): the speaker considers it possible that `φ`, that
learning an instantiation of the highlighted property is a precondition for proceeding, holds
necessarily for the recipient, over the interlocutors' doxastic accessibility relations. -/
def Felicity (acc : Discourse.Role → SetRel W W) (f : Force) (φ : W → Prop) :
    W → Prop :=
  ◇[acc .speaker] (□[acc (recipient f)] φ)

/-- In a question the recipient is the speaker, and over a doxastic frame possible necessity is
necessity: the modalized condition is the felicity condition (19). -/
theorem felicity_question (acc : Discourse.Role → SetRel W W) [IsKD45Frame (acc .speaker)]
    (φ : W → Prop) : Felicity acc .interrogative φ = □[acc .speaker] φ :=
  funext λ _ => propext (diamond_box_iff (acc .speaker))

end Flip

end Theiler2021
