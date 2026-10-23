module

public import Linglib.Fragments.Mandarin.QuestionParticles
public import Linglib.Semantics.Modality.Kernel
public import Linglib.Semantics.Questions.Bias
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.DeriveFintype

/-!
# Zheng (2025): Nandao-Qs, When Surprise Sparks Inquiry

This file formalizes Zheng's felicity conditions for Mandarin *nandao* questions, which
are driven by unexpected contextual evidence rather than by the speaker's epistemic bias. The
conditions are stated over von Fintel and Gillies's kernel, the set of propositions directly
available in the context: some piece of evidence in the kernel raises the probability of the
prejacent (`evidenceSupports`), the kernel conflicts with the information state `U` in place
before the evidence, the beliefs, norms, desires or default expectations of the speaker
(`unexpected`), and the prejacent is not itself directly settled in the kernel
(`nandaoFelicitous`, the final condition (11)). Generalized to questions through the
instantiations of the question's highlighted property, (13), the first condition requires
every instantiation to follow from the evidence (`nandaoQFelicitous`), which reduces to (11)
for a polar question (`nandaoQFelicitous_singleton`) and excludes a wh-question one of whose
instantiations no evidence supports (`not_nandaoQFelicitous_of_unsupported`), the paper's
derivation of the distribution recorded in the fragment (`nandao_distribution`, (12)).

The dripping-raincoat scenario of (2), (3) and (5) is a four-world model: the question is
felicitous whether the conflicting state is a belief that it is not raining or the default
expectation that people do not wear raincoats (`raincoat_nandao_felicitous`,
`raincoat_default_felicitous`), and infelicitous without the evidence
(`no_evidence_infelicitous`) or when the evidence is expected
(`expected_evidence_infelicitous`), which is (6). The link to rhetorical questions in §5 runs
through Farkas's closed-question condition: a closed polar question is resolved in the
common ground whenever the speaker's beliefs are consistent with it (`resolved_of_closed_polar`),
the argument of the paper's footnote on (17).

## Implementation notes

* The paper's "significantly raises" is sharpened to strict raising of the conditional
  probability under the uniform counting measure on a finite set of worlds
  (`evidenceRaises`).
* The information state `U` is a list of propositions, like the kernel; the default state of the
  paper's footnote is one such proposition.
* Highlighted properties enter only through their set of instantiations.

## References

* [zheng-2025]
* [von-fintel-gillies-2010]
* [xu-2012]
* [farkas-2025]
-/

@[expose] public section

namespace Zheng2025

open Modality (Kernel)
open Modality

variable {W : Type*}

/-! ### Kernel-theoretic felicity conditions -/

/-- Evidence `p` raises the probability of `φ` under the uniform counting measure on a finite
`W`: `P(φ | p) > P(φ)`. -/
def evidenceRaises (p φ : Set W) : Prop :=
  (p ∩ φ).ncard * Nat.card W > φ.ncard * p.ncard

instance (p φ : W → Prop) [Fintype W] [DecidablePred p] [DecidablePred φ] :
    Decidable (evidenceRaises p φ) :=
  decidable_of_iff
    ((Finset.univ.filter λ w => p w ∧ φ w).card * Fintype.card W >
      (Finset.univ.filter φ).card * (Finset.univ.filter p).card) <| by
    show _ ↔ {w | p w ∧ φ w}.ncard * Nat.card W > {w | φ w}.ncard * {w | p w}.ncard
    simp [Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card]

section

variable (k : Kernel W) (u : Set (W → Prop)) (φ : W → Prop)

/-- Some proposition in `K` raises the probability of `φ`, (11i). -/
def evidenceSupports : Prop :=
  ∃ p ∈ k.props, evidenceRaises p φ

/-- The evidence in `K` is unexpected given the prior information state `U`, (11ii). -/
def unexpected : Prop :=
  Disjoint k.base {w | sInf u w}

/-- *Nandao φ?* is felicitous iff some evidence in `K` raises the probability of `φ`, the
evidence is unexpected given the prior state `U`, and `φ` is not directly settled in `K`,
(11). -/
def nandaoFelicitous : Prop :=
  evidenceSupports k φ ∧ unexpected k u ∧ ¬ k.directlySettles φ

end

/-! ### Questions through their highlighted property, (13) -/

/-- *Nandao Q?* is felicitous iff some evidence in `K` raises the probability of every
instantiation of the question's highlighted property, the evidence is unexpected, and no
instantiation is directly settled in `K`. -/
def nandaoQFelicitous (k : Kernel W) (u : Set (W → Prop)) (f : Set (W → Prop)) : Prop :=
  (∃ p ∈ k.props, ∀ φ ∈ f, evidenceRaises p φ) ∧ unexpected k u ∧
    ∀ φ ∈ f, ¬ k.directlySettles φ

/-- For a polar question, whose highlighted property has the prejacent as its one
instantiation, (13) is (11). -/
theorem nandaoQFelicitous_singleton (k : Kernel W) (u : Set (W → Prop)) (φ : W → Prop) :
    nandaoQFelicitous k u {φ} ↔ nandaoFelicitous k u φ := by
  simp [nandaoQFelicitous, nandaoFelicitous, evidenceSupports]

theorem not_nandaoQFelicitous_of_unsupported {k : Kernel W} {u : Set (W → Prop)}
    {f : Set (W → Prop)} {φ : W → Prop} (hφ : φ ∈ f)
    (h : ∀ p ∈ k.props, ¬ evidenceRaises p φ) : ¬ nandaoQFelicitous k u f := by
  rintro ⟨⟨p, hp, hall⟩, -, -⟩
  exact h p hp (hall φ hφ)

/-- *Nandao* combines with polar questions only, (12), as the fragment records. -/
theorem nandao_distribution :
    .declarative ∉ Mandarin.QuestionParticles.nandao.distribution.possible.dom ∧
      .polar ∈ Mandarin.QuestionParticles.nandao.distribution.possible.dom ∧
      .constituent ∉ Mandarin.QuestionParticles.nandao.distribution.possible.dom := by
  decide

/-- The bias profile of *nandao* requires contextual evidence for the prejacent, the paper's
evidential bias, and places no requirement on the prior state of the speaker, so that a neutral
prior state is compatible with it, (3). -/
def nandaoProfile : Question.BiasProfile := ⟨.plus .positive, Finset.univ⟩

/-! ### The dripping-raincoat scenario, (2), (3) and (5) -/

/-- The worlds of the scenario, in which it rains, the sprinkler ran and the coat is wet without
rain, it is dry, or the weather is unknown. -/
inductive World
  | rain | sprinkler | dry | unknown
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- B enters wearing a dripping raincoat. -/
abbrev wearingRaincoat : World → Prop := λ w => w = .rain ∨ w = .sprinkler

/-- A's belief that it is not raining, (2). -/
abbrev expectDry : World → Prop := λ w => w = .dry ∨ w = .unknown

/-- The default expectation that people do not wear raincoats, the state of (3) and of
context 1 of (5). -/
abbrev expectNoRaincoat : World → Prop := λ w => ¬ wearingRaincoat w

/-- It is raining outside, the prejacent. -/
abbrev isRaining : World → Prop := (· = .rain)

/-- The kernel carrying the direct evidence of the wet coat. -/
def raincoatK : Kernel World := ⟨{wearingRaincoat}⟩

private theorem raincoat_unexpected_of {u : World → Prop} (h : ∀ w, wearingRaincoat w → ¬ u w) :
    unexpected raincoatK {u} := by
  simp only [unexpected, raincoatK, Kernel.base_singleton, sInf_singleton,
    Set.disjoint_left]
  exact λ w hw => h w hw

private theorem raincoat_not_settled : ¬ raincoatK.directlySettles isRaining := by
  simp only [raincoatK, Kernel.directlySettles_singleton, Set.ofPred_subset_ofPred,
    Set.disjoint_left]
  decide

/-- *Nandao waimian xiayu-le ma?* is felicitous when A believes it is not raining, (2). -/
theorem raincoat_nandao_felicitous : nandaoFelicitous raincoatK {expectDry} isRaining :=
  ⟨⟨wearingRaincoat, Set.mem_singleton _, by decide⟩,
    raincoat_unexpected_of (by decide), raincoat_not_settled⟩

/-- The question is equally felicitous when A has no belief about the weather and only the
default expectation that people do not wear raincoats, (3) and context 1 of (5): epistemic
bias is not necessary. -/
theorem raincoat_default_felicitous :
    nandaoFelicitous raincoatK {expectNoRaincoat} isRaining :=
  ⟨⟨wearingRaincoat, Set.mem_singleton _, by decide⟩,
    raincoat_unexpected_of (by decide), raincoat_not_settled⟩

/-- Without the evidence the question is infelicitous, whatever A believes, contexts 2 and 3
of (5): epistemic bias is not sufficient. -/
theorem no_evidence_infelicitous (u : Set (World → Prop)) :
    ¬ nandaoFelicitous ⟨∅⟩ u isRaining := by
  rintro ⟨⟨p, hp, -⟩, -, -⟩
  exact hp

/-- When the evidence is expected, the prior state already allowing wet coats, the question is
infelicitous, as in context 2 of (6). -/
theorem expected_evidence_infelicitous :
    ¬ nandaoFelicitous raincoatK {wearingRaincoat} isRaining := by
  rintro ⟨-, hInc, -⟩
  have h1 : World.rain ∈ raincoatK.base :=
    Kernel.mem_base.mpr (by simp [raincoatK, wearingRaincoat])
  have h2 : World.rain ∈ {w | sInf ({wearingRaincoat} : Set (World → Prop)) w} := by
    simp [wearingRaincoat]
  exact Set.disjoint_left.mp hInc h1 h2

/-! ### Closed questions and rhetorical use, §5 -/

/-- [farkas-2025]'s closed-question condition: every alternative of the issue not already
entailed by the common ground is doxastically inconsistent with it, given the speaker's
doxastic state `dox`. -/
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

end Zheng2025
