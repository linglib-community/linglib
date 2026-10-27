module

public import Linglib.Data.Examples.Zheng2025
public import Linglib.Fragments.Mandarin.QuestionParticles
public import Linglib.Pragmatics.DecisionTheoretic.Basic
public import Linglib.Semantics.Modality.Kernel
public import Linglib.Semantics.Questions.Bias
public import Studies.Theiler2021
public import Mathlib.Tactic.DeriveFintype

/-!
# Zheng (2025): Nandao-Qs, When Surprise Sparks Inquiry

Zheng gives Mandarin *nandao* questions felicity conditions on unexpected contextual evidence
rather than on the speaker's epistemic bias. Over von Fintel and Gillies's kernel `K`, the
propositions directly available in the context, *nandao φ?* needs evidence positively relevant
to `φ` in Merin's sense, evidence that conflicts with the prior state `U`, and `φ` not directly
settled in `K`, (11). A question needs evidence relevant to every instantiation of its
highlighted property in Theiler's sense, (13), and §4 adds that learning each instantiation be
necessary for resolving the conflict, Theiler's condition on *denn* with resolving for
proceeding. In the dripping-raincoat scenario of (2), (3) and (5), each context is placed in
Sudo's grid by the relevance signs of the evidence and of A's beliefs.

## Implementation notes

The paper's "significantly raises" is Merin's positive relevance under a prior, the counting
measure in the scenario, whose worlds are rain, a sprinkler that wets the coat, and a dry day.
The prior state of a context is A's beliefs with the default expectations, and only the beliefs
are its epistemic coordinate, the paper not counting the default state as epistemic bias
(fn. 6). Xu judges the context and sentence of (3) infelicitous, his (12) on p. 55. `Closed`
reads the closed-question condition relative to the speaker's doxastic state, as §5.1
paraphrases it.

## Errata

* Footnote 9 calls a closed polar question unresolved in the common ground impossible, since
  `p` and `¬p` would both be doxastically inconsistent with it. That holds for consistency with a
  doxastic state (`resolved_of_closed_polar`) but not for Farkas's d-consistency (12), which is
  stronger than consistency (13), and under which such an issue is unresolvable (15).

## TODO

* Farkas's projection (52c) requires d-consistency where `Commitment.Table.project` requires
  consistency; once it does, `Closed` is the Table's.

## References

* [zheng-2025]
* [von-fintel-gillies-2010]
* [merin-1999-relevance]
* [theiler-2021]
* [sudo-2013]
* [xu-2012]
* [xu-2017]
* [farkas-2025]
-/

@[expose] public section

namespace Zheng2025

open MeasureTheory Modality DTS Question
open Theiler2021 (Property instantiations instantiations_zero Necessary Sufficient)

/-! ### Felicity conditions, (11) and (13) -/

section Felicity

variable {W : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W] (μ : Measure W)
  (k : Kernel W) (u : Set (W → Prop)) {D : Type*} {n : ℕ}

/-- The evidence in `K` is unexpected given the prior state `U`, (11ii). -/
def unexpected : Prop :=
  Disjoint k.base {w | sInf u w}

/-- *Nandao φ?* is felicitous iff some evidence in `K` is positively relevant to `φ` under the
prior `μ`, the evidence is unexpected given `U`, and `φ` is not directly settled in `K`, (11). -/
def nandaoFelicitous (φ : Set W) : Prop :=
  (∃ p ∈ k.props, posRelevant ⟨φ, .of_discrete, μ⟩ {w | p w}) ∧ unexpected k u ∧
    ¬ k.directlySettles (· ∈ φ)

/-- *Nandao Q?* is felicitous iff some evidence in `K` is positively relevant to every
instantiation of the highlighted property `f` of `Q`, the evidence is unexpected, and no
instantiation is directly settled in `K`, (13). -/
def nandaoQFelicitous (f : Property D W n) : Prop :=
  (∃ p ∈ k.props, ∀ φ ∈ instantiations f, posRelevant ⟨φ, .of_discrete, μ⟩ {w | p w}) ∧
    unexpected k u ∧ ∀ φ ∈ instantiations f, ¬ k.directlySettles (· ∈ φ)

/-- (13) for a polar question is (11), and §4 excludes a why-question with another sufficient
answer. -/
theorem nandaoQFelicitous_zero (f : Property D W 0) :
    nandaoQFelicitous μ k u f ↔ nandaoFelicitous μ k u (f default) := by
  simp [nandaoQFelicitous, nandaoFelicitous, instantiations_zero]

theorem not_nandaoQFelicitous_of_not_posRelevant {f : Property D W n} {φ : Set W}
    (hφ : φ ∈ instantiations f) (h : ∀ p ∈ k.props, ¬ posRelevant ⟨φ, .of_discrete, μ⟩ {w | p w}) :
    ¬ nandaoQFelicitous μ k u f := by
  rintro ⟨⟨p, hp, hall⟩, -, -⟩
  exact h p hp (hall φ hφ)

/-- Where a context sits in Sudo's grid for `φ`: the relevance signs of the evidence and of the
speaker's beliefs. -/
noncomputable def situation (φ : Set W) (beliefs : Set (W → Prop)) : Situation :=
  (relevanceSign ⟨φ, .of_discrete, μ⟩ k.base,
    relevanceSign ⟨φ, .of_discrete, μ⟩ {w | sInf beliefs w})

end Felicity

/-! ### Resolving the conflict, §4 -/

section Resolution

variable {W D : Type*} {n : ℕ} {resolve : Set W → Prop}

/-- §4's requirement that learning each instantiation of the highlighted property be a
necessary precondition for resolving the conflict between the evidence and the prior state,
`resolve` holding of the states from which it is resolved: Theiler's condition on *denn* with
resolving for proceeding. -/
def NecessaryToResolve (resolve : Set W → Prop) (f : Property D W n) : Prop :=
  ∀ φ ∈ instantiations f, Necessary resolve (· ⊆ φ)

theorem necessaryToResolve_zero (f : Property D W 0) :
    NecessaryToResolve resolve f ↔ Necessary resolve (· ⊆ f default) := by
  simp [NecessaryToResolve, instantiations_zero]

/-- A question with an answer that suffices to resolve the conflict without entailing one of
its instantiations fails §4's requirement, as a why-question does. -/
theorem not_necessaryToResolve_of_sufficient {f : Property D W n} {p q : Set W}
    (hq : q ∈ instantiations f) (hp : Sufficient resolve (· ⊆ p)) (hpq : ¬ p ⊆ q) :
    ¬ NecessaryToResolve resolve f :=
  fun h ↦ Theiler2021.not_necessary_of_sufficient hp hpq (h q hq)

example (p : Set W) : NecessaryToResolve (· ⊆ p) (fun _ : Fin 0 → D ↦ p) :=
  (necessaryToResolve_zero _).2 fun _ ↦ id

end Resolution

/-! ### The distribution of *nandao*, (12) -/

open Mandarin.QuestionParticles (nandao) in
/-- *Nandao* selects polar questions only, (12). -/
theorem nandao_distribution : nandao.distribution.possible.dom = {.polar} := by
  ext t; cases t <;> decide

/-- The sentence type of a row, the polar question of the nandao-questions and the declarative
and wh-question of (12). -/
def sentenceType? (e : Datum) : Option Clause.SentenceType :=
  e.parse? "clause_type"
    [("declarative", .declarative), ("polar", .polar), ("wh-question", .constituent)]

open Mandarin.QuestionParticles (nandao) in
theorem nandao_distribution_judgments : ∀ e ∈ Examples.all, ∀ t ∈ sentenceType? e,
    (t ∈ nandao.distribution.possible.dom ↔ e.judgment ≠ .ungrammatical) := by
  decide

/-! ### Bias profiles -/

/-- The paper's profile of *nandao*: evidence for the prejacent, with any prior belief (§2.2). -/
def nandaoProfile : BiasProfile := ⟨.plus .positive, Finset.univ⟩

/-- Xu's profile of *nandao*, which §2.1 argues against: a prior belief in the negation of the
prejacent, with any evidence ([xu-2017] pp. 56-57). -/
def xuProfile : BiasProfile := ⟨Finset.univ, .plus .negative⟩

/-! ### The dripping-raincoat scenario, (2), (3) and (5) -/

/-- The worlds of the scenario: it rains, a sprinkler wets the coat without rain, or it is
dry. -/
inductive World
  | rain | sprinkler | dry
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace World := ⊤

instance : DiscreteMeasurableSpace World := ⟨fun _ ↦ trivial⟩

/-- B's coat drips. -/
abbrev wetCoat : World → Prop := fun w ↦ w = .rain ∨ w = .sprinkler

/-- It is raining outside, the prejacent. -/
abbrev isRaining : World → Prop := (· = .rain)

/-- A's belief that it is not raining. -/
abbrev notRaining : World → Prop := fun w ↦ w ≠ .rain

/-- The default expectation that coats are dry. -/
abbrev dryCoat : World → Prop := fun w ↦ ¬ wetCoat w

/-- The kernel carrying the direct evidence of the wet coat. -/
def raincoatK : Kernel World := ⟨{wetCoat}⟩

/-- A context of the scenario: the evidence, A's beliefs, and the default expectations, which
with the beliefs are the prior state. -/
structure RaincoatContext where
  evidence : Kernel World
  beliefs : Set (World → Prop)
  defaults : Set (World → Prop)

namespace RaincoatContext

/-- *Nandao waimian xiayu-le ma?* is felicitous in the context. -/
def Felicitous (c : RaincoatContext) : Prop :=
  nandaoFelicitous .count c.evidence (c.beliefs ∪ c.defaults) {w | isRaining w}

/-- The context's place in Sudo's grid. -/
noncomputable def situation (c : RaincoatContext) : Situation :=
  Zheng2025.situation .count c.evidence {w | isRaining w} c.beliefs

end RaincoatContext

/-- (2): A believes it is not raining, and B enters in a dripping raincoat. -/
def believesDry : RaincoatContext := ⟨raincoatK, {notRaining}, {dryCoat}⟩

/-- (3) and context 1 of (5): A expects nothing about the weather. -/
def noBelief : RaincoatContext := ⟨raincoatK, ∅, {dryCoat}⟩

/-- Context 2 of (5): B enters without the raincoat. -/
def noEvidence : RaincoatContext := ⟨⟨∅⟩, ∅, {dryCoat}⟩

/-- Context 3 of (5): A thinks it will not rain, and B enters without the raincoat. -/
def believesDryNoEvidence : RaincoatContext := ⟨⟨∅⟩, {notRaining}, {dryCoat}⟩

/-- The dripping raincoat when A already expects a wet coat, as in context 2 of (6). -/
def expectsWet : RaincoatContext := ⟨raincoatK, ∅, {wetCoat}⟩

private theorem relevanceSign_isRaining (e : Set World) :
    relevanceSign ⟨{w | isRaining w}, .of_discrete, .count⟩ e =
      SignType.sign (({w | isRaining w} ∩ e).ncard * {w | isRaining w}ᶜ.ncard -
        ({w | isRaining w}ᶜ ∩ e).ncard * {w | isRaining w}.ncard : ℤ) :=
  relevanceSign_count_eq (topic := {w | isRaining w}) e ⟨.rain, rfl⟩ ⟨.dry, by simp⟩

private theorem posRelevant_wetCoat :
    posRelevant ⟨{w | isRaining w}, .of_discrete, .count⟩ {w | wetCoat w} := by
  rw [← relevanceSign_eq_one_iff, relevanceSign_isRaining]
  simp only [Set.ncard_eq_toFinset_card']
  decide

private theorem felicitous_of_unexpected {c : RaincoatContext} (hk : c.evidence = raincoatK)
    (hu : ∀ w, wetCoat w → ¬ sInf (c.beliefs ∪ c.defaults) w) : c.Felicitous := by
  refine ⟨⟨wetCoat, by simp [hk, raincoatK], posRelevant_wetCoat⟩, ?_, ?_⟩
  · simp only [unexpected, hk, raincoatK, Kernel.base_singleton, Set.disjoint_left]
    exact fun w hw ↦ hu w hw
  · simp only [hk, raincoatK, Kernel.directlySettles_singleton, Set.mem_ofPred_eq,
      Set.ofPred_subset_ofPred, Set.disjoint_left]
    decide

private theorem not_felicitous_of_empty {c : RaincoatContext} (hk : c.evidence = ⟨∅⟩) :
    ¬ c.Felicitous := by
  rintro ⟨⟨p, hp, -⟩, -, -⟩
  simp [hk] at hp

theorem felicitous_believesDry : believesDry.Felicitous :=
  felicitous_of_unexpected rfl fun w hw h ↦ by
    simp only [believesDry, Set.singleton_union, sInf_insert, sInf_singleton, Pi.inf_apply,
      inf_Prop_eq] at h
    exact h.2 hw

theorem felicitous_noBelief : noBelief.Felicitous :=
  felicitous_of_unexpected rfl fun w hw h ↦ by
    simp only [noBelief, Set.empty_union, sInf_singleton] at h
    exact h hw

theorem not_felicitous_expectsWet : ¬ expectsWet.Felicitous := by
  rintro ⟨-, hInc, -⟩
  exact Set.disjoint_left.mp hInc (show World.rain ∈ raincoatK.base by simp [raincoatK, wetCoat])
    (by simp [expectsWet, wetCoat])

theorem situation_believesDry : believesDry.situation = (1, -1) := by
  simp only [RaincoatContext.situation, situation, believesDry, raincoatK, Kernel.base_singleton,
    sInf_singleton, relevanceSign_isRaining, Set.ncard_eq_toFinset_card']
  decide

theorem situation_noBelief : noBelief.situation = (1, 0) := by
  simp only [RaincoatContext.situation, situation, noBelief, raincoatK, Kernel.base_singleton,
    sInf_empty, relevanceSign_isRaining, Set.ncard_eq_toFinset_card']
  decide

theorem situation_noEvidence : noEvidence.situation = (0, 0) := by
  simp only [RaincoatContext.situation, situation, noEvidence, Kernel.base, sInf_empty,
    relevanceSign_isRaining, Set.ncard_eq_toFinset_card']
  decide

theorem situation_believesDryNoEvidence : believesDryNoEvidence.situation = (0, -1) := by
  simp only [RaincoatContext.situation, situation, believesDryNoEvidence, Kernel.base,
    sInf_empty, sInf_singleton, relevanceSign_isRaining, Set.ncard_eq_toFinset_card']
  decide

/-- In the contexts of (2), (3) and (5), the question is felicitous exactly when the context's
situation lies in the paper's profile. -/
theorem felicitous_iff_mem_nandaoProfile :
    ∀ c ∈ [believesDry, noBelief, noEvidence, believesDryNoEvidence],
      c.Felicitous ↔ c.situation ∈ nandaoProfile.felicity := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    situation_believesDry, situation_noBelief, situation_noEvidence,
    situation_believesDryNoEvidence]
  exact ⟨iff_of_true felicitous_believesDry (by decide),
    iff_of_true felicitous_noBelief (by decide),
    iff_of_false (not_felicitous_of_empty rfl) (by decide),
    iff_of_false (not_felicitous_of_empty rfl) (by decide)⟩

/-- Negative epistemic bias is not necessary, (3) being felicitous outside Xu's profile, and not
sufficient, context 3 of (5) being infelicitous inside it (§2.2). -/
theorem xuProfile_not_necessary_not_sufficient :
    (noBelief.Felicitous ∧ noBelief.situation ∉ xuProfile.felicity) ∧
      (¬ believesDryNoEvidence.Felicitous ∧
        believesDryNoEvidence.situation ∈ xuProfile.felicity) := by
  rw [situation_noBelief, situation_believesDryNoEvidence]
  exact ⟨⟨felicitous_noBelief, by decide⟩, not_felicitous_of_empty rfl, by decide⟩

/-- Evidence that the prior state expects sits where the evidence of (3) does and is
infelicitous, so the grid does not determine felicity (§2.3). -/
theorem situation_expectsWet :
    expectsWet.situation = noBelief.situation ∧ noBelief.Felicitous ∧ ¬ expectsWet.Felicitous :=
  ⟨rfl, felicitous_noBelief, not_felicitous_expectsWet⟩

/-- The rows of (2), (3) and (5) with their contexts. -/
def rowContexts : List (Datum × RaincoatContext) :=
  [(Examples.ex2, believesDry), (Examples.ex3, noBelief), (Examples.ex5_ctx1, noBelief),
    (Examples.ex5_ctx2, noEvidence), (Examples.ex5_ctx3, believesDryNoEvidence)]

theorem judgments_rowContexts :
    ∀ x ∈ rowContexts, x.1.judgment = .acceptable ↔ x.2.Felicitous := by
  simp only [rowContexts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨iff_of_true rfl felicitous_believesDry, iff_of_true rfl felicitous_noBelief,
    iff_of_true rfl felicitous_noBelief, iff_of_false (by decide) (not_felicitous_of_empty rfl),
    iff_of_false (by decide) (not_felicitous_of_empty rfl)⟩

/-! ### Closed questions and rhetorical use, §5 -/

section Closed

variable {W : Type*}

/-- The closed-question condition of [farkas-2025], relative to the speaker's doxastic state
`dox`: every alternative of the issue not entailed by the common ground is inconsistent with it
and with `dox`. -/
def Closed (issue : Set (Set W)) (cg dox : Set W) : Prop :=
  ∀ p ∈ issue, ¬ cg ⊆ p → Disjoint (cg ∩ p) dox

theorem resolved_of_closed_polar {p cg dox : Set W} (hcons : (cg ∩ dox).Nonempty)
    (h : Closed {p, pᶜ} cg dox) : cg ⊆ p ∨ cg ⊆ pᶜ := by
  by_contra hn
  rw [not_or] at hn
  have h₁ := h p (by simp) hn.1
  have h₂ := h pᶜ (by simp) hn.2
  obtain ⟨w, hw⟩ := hcons
  by_cases hp : w ∈ p
  · exact Set.disjoint_left.mp h₁ ⟨hw.1, hp⟩ hw.2
  · exact Set.disjoint_left.mp h₂ ⟨hw.1, hp⟩ hw.2

end Closed

end Zheng2025
