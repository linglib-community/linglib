module

public import Linglib.Semantics.Questions.Basic
public import Linglib.Semantics.Questions.Hamblin
public import Mathlib.Order.Filter.Ker

/-!
# Answerhood predicates on questions

This file defines the answerhood predicates over the inquisitive substrate `Question W`, with
the question as subject so that dot notation reads in the right direction. Resolution is
membership, `σ ∈ Q`, the support relation of [ciardelli-groenendijk-roelofsen-2018],
which on normal questions is settling some alternative
(`mem_iff_exists_alt_subset`), the mention-some reading of [groenendijk-stokhof-1984]. A state
completely answers a question when it decides every alternative (`CompletelyAnsweredBy`), the
mention-all reading, and partially answers it when it decides some alternative
(`PartiallyAnsweredBy`), the non-contextual core of [roberts-2012]'s partial answer. The
notions form the quantifier × polarity square of answerhood: resolution (∃, positive),
`PartiallyAnsweredBy` (∃, either), `CompletelyAnsweredBy` (∀, either). A question is a
contextual subquestion of another when its complete answers, cut to the context, partially
answer it (`IsSubquestionOf`), and a move is relevant to a set of questions when some
alternative of it partially answers one of them (`IsRelevantTo`). A common ground, a filter of
propositions, decides a question when it entails a complete answer (`DecidedBy`), which on a
principal filter is resolution.

## Implementation notes

`CompletelyAnsweredBy` decides each alternative rather than entailing every one, which would
collapse to `σ ⊆ ⋂ alt Q` and is incoherent for partition questions with disjoint
alternatives; the decided form is [groenendijk-stokhof-1984]'s strong exhaustivity on
partition questions, and `Exhaustivity.lean` builds the weak / intermediate / strong /
relativized ladder on it ([heim-1994], [george-2011], [xiang-2022]). Mention-some answerhood
is resolution itself: an added "and not all alternatives" conjunct would rule out
singleton-world states as mention-some answers to *Where can I get coffee?*. `∅` vacuously
answers everything, as in [roberts-2012].

## References

* [ciardelli-groenendijk-roelofsen-2018]
* [farkas-bruce-2010]
* [groenendijk-stokhof-1984]
* [roberts-2012]
* [theiler-etal-2018]
-/

@[expose] public section

namespace Question

variable {W : Type*}

/-- `σ` partially answers `Q` if it settles some alternative positively
(`σ ⊆ p`) or negatively (`σ ⊆ pᶜ`). -/
def PartiallyAnsweredBy (Q : Question W) (σ : Set W) : Prop :=
  ∃ p ∈ alt Q, σ ⊆ p ∨ σ ⊆ pᶜ

/-- `σ` mention-all answers `Q` if it decides every alternative, either
entailing it or ruling it out. -/
def CompletelyAnsweredBy (Q : Question W) (σ : Set W) : Prop :=
  ∀ p ∈ alt Q, σ ⊆ p ∨ σ ⊆ pᶜ

/-- `P` is a subquestion of `Q` relative to the context `C` ([roberts-2012]): every complete
answer to `P` contextually partially answers `Q`. The entailment is contextual, not question
entailment, so the relation is not transitive in general. -/
def IsSubquestionOf (C : Set W) (P Q : Question W) : Prop :=
  ∀ a ∈ alt P, PartiallyAnsweredBy Q (C ∩ a)

theorem isSubquestionOf_of_alt_subset (C : Set W) {P Q : Question W} (h : alt P ⊆ alt Q) :
    IsSubquestionOf C P Q :=
  fun a ha ↦ ⟨a, h ha, Or.inl Set.inter_subset_right⟩

theorem IsSubquestionOf.refl (C : Set W) (P : Question W) : IsSubquestionOf C P P :=
  isSubquestionOf_of_alt_subset C subset_rfl

theorem isSubquestionOf_of_le (C : Set W) {P Q : Question W} (hQ : Q.IsNormal)
    (h : P ≤ Q) : IsSubquestionOf C P Q := fun _ ha ↦
  let ⟨q, hq, haq⟩ := hQ _ (le_def.mp h (alt_subset_props P ha))
  ⟨q, hq, Or.inl (Set.inter_subset_right.trans haq)⟩

theorem partiallyAnsweredBy_inter_iff {Q : Question W} {C σ : Set W} :
    PartiallyAnsweredBy Q (C ∩ σ) ↔
      ∃ p ∈ alt Q, σ ∈ (ofSet p).relativeTo C ∨ σ ∈ (ofSet pᶜ).relativeTo C := by
  simp only [PartiallyAnsweredBy, mem_relativeTo, mem_ofSet]

theorem isSubquestionOf_iff {C : Set W} {P Q : Question W} :
    IsSubquestionOf C P Q ↔
      ∀ a ∈ alt P, ∃ p ∈ alt Q, a ∈ (ofSet p).relativeTo C ∨ a ∈ (ofSet pᶜ).relativeTo C := by
  simp only [IsSubquestionOf, partiallyAnsweredBy_inter_iff]

variable {σ : Set W} {Q : Question W}

/-! ### Basic relationships -/

theorem mem_of_exists_alt_subset (h : ∃ p ∈ alt Q, σ ⊆ p) : σ ∈ Q :=
  let ⟨p, hp, hsub⟩ := h
  Q.downward_closed p (alt_subset_props _ hp) σ hsub

theorem mem_iff_exists_alt_subset (hQ : Q.IsNormal) : σ ∈ Q ↔ ∃ p ∈ alt Q, σ ⊆ p :=
  ⟨hQ σ, mem_of_exists_alt_subset⟩

theorem partiallyAnsweredBy_of_mem (hQ : Q.IsNormal) (h : σ ∈ Q) :
    PartiallyAnsweredBy Q σ :=
  let ⟨p, hp, hsub⟩ := hQ σ h
  ⟨p, hp, Or.inl hsub⟩

theorem partiallyAnsweredBy_of_mem_alt {p : Set W} (h : p ∈ alt Q) :
    PartiallyAnsweredBy Q p :=
  ⟨p, h, Or.inl subset_rfl⟩

theorem partiallyAnsweredBy_compl_of_mem_alt {p : Set W} (h : p ∈ alt Q) :
    PartiallyAnsweredBy Q pᶜ :=
  ⟨p, h, Or.inr subset_rfl⟩

/-! ### Answerhood transmission -/

theorem CompletelyAnsweredBy.mono {P : Question W} (h : CompletelyAnsweredBy Q σ)
    (hsub : alt P ⊆ alt Q) : CompletelyAnsweredBy P σ :=
  fun p hp => h p (hsub hp)

/-- The set of complete answers to `Q` — [roberts-2012]'s `Ans(q)`: the
states that decide every alternative. Her question entailment (8), after
[groenendijk-stokhof-1984], is `completeAnswers P ⊆ completeAnswers Q`,
diverging from the lattice order off partition-shaped alternatives (see
`Entailment.lean`). -/
def completeAnswers (Q : Question W) : Set (Set W) := {σ | CompletelyAnsweredBy Q σ}

@[simp] theorem mem_completeAnswers {Q : Question W} :
    σ ∈ completeAnswers Q ↔ CompletelyAnsweredBy Q σ := Iff.rfl

theorem completeAnswers_anti {P Q : Question W} (h : alt Q ⊆ alt P) :
    completeAnswers P ⊆ completeAnswers Q :=
  fun _ hσ => CompletelyAnsweredBy.mono hσ h

theorem completelyAnsweredBy_iff_of_alt_eq_range {ι : Type*} {P : ι → Set W}
    (h : alt Q = Set.range P) :
    CompletelyAnsweredBy Q σ ↔ ∀ i, σ ⊆ P i ∨ σ ⊆ (P i)ᶜ := by
  unfold CompletelyAnsweredBy
  rw [h]
  exact Set.forall_mem_range

@[simp] theorem completeAnswers_top :
    completeAnswers (⊤ : Question W) = Set.univ := by
  ext σ; simp [completeAnswers, CompletelyAnsweredBy, alt_top]

@[simp] theorem completeAnswers_bot :
    completeAnswers (⊥ : Question W) = Set.univ := by
  ext σ
  simp only [completeAnswers, CompletelyAnsweredBy, alt_bot, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true, Set.mem_singleton_iff]
  rintro p rfl
  exact Or.inr (by simp)

theorem completelyAnsweredBy_ofSet_iff {p : Set W} :
    CompletelyAnsweredBy (ofSet p) σ ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  unfold CompletelyAnsweredBy
  rw [alt_ofSet]
  simp

theorem completeAnswers_ofSet (p : Set W) :
    completeAnswers (ofSet p) = {σ | σ ⊆ p ∨ σ ⊆ pᶜ} := by
  ext σ; simp [completeAnswers, completelyAnsweredBy_ofSet_iff]

/-- The complete answers to a join of point-questions are the joint
complete answers to each — [roberts-2012]'s (11) in general form. -/
theorem completeAnswers_iSup_ofSet {ι : Type*} [Nonempty ι] {P : ι → Set W}
    (hP : ∀ i j, P i ⊆ P j → P i = P j) :
    completeAnswers (⨆ i, ofSet (P i)) =
      ⋂ i, completeAnswers (ofSet (P i)) := by
  ext σ
  simp [completelyAnsweredBy_iff_of_alt_eq_range (alt_iSup_ofSet hP),
    completelyAnsweredBy_ofSet_iff]

/-! ### Polar reduction

Iff lemmas reducing the square on nontrivial `polar p` to plain `Set`
inclusions — the joints consumer-side study files build on; resolution
itself reduces without nontriviality, `mem_polar`. -/

theorem partiallyAnsweredBy_polar_iff {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    PartiallyAnsweredBy (polar p) σ ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  simp only [PartiallyAnsweredBy, alt_polar_of_nontrivial hne hnu,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left, compl_compl]
  tauto

theorem completelyAnsweredBy_polar_iff {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    CompletelyAnsweredBy (polar p) σ ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  unfold CompletelyAnsweredBy
  constructor
  · intro h
    have hp_mem : p ∈ alt (polar p) :=
      (mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl)
    exact h p hp_mem
  · rintro hor q hq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact hor
    · rcases hor with h | h
      · right; rw [compl_compl]; exact h
      · left; exact h

/-! ### Decidability for polar questions -/

/-- `CompletelyAnsweredBy (polar p) σ` is decidable when the two inclusions are: on polar
questions it coincides with resolution, `mem_polar`. -/
def decidableCompletelyAnsweredByPolar {p σ : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    [Decidable (σ ⊆ p)] [Decidable (σ ⊆ pᶜ)] :
    Decidable (CompletelyAnsweredBy (polar p) σ) :=
  decidable_of_iff _ (completelyAnsweredBy_polar_iff hne hnu).symm

/-! ### Relevance to a question set -/

/-- A move with denotation `den` is **relevant** to the questions in
`qs` when some alternative of `den` partially answers some question in
`qs` — the assertion clause of [roberts-2012]'s Relevance, existentially
weakened and extended to a question set (see `Discourse/QUD/Basic.lean`
for the fidelity discussion). -/
def IsRelevantTo (den : Question W) (qs : Set (Question W)) : Prop :=
  ∃ a ∈ alt den, ∃ q ∈ qs, PartiallyAnsweredBy q a

theorem isRelevantTo_polar_iff {p : Set W} {qs : Set (Question W)}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    (polar p).IsRelevantTo qs ↔
      (∃ q ∈ qs, PartiallyAnsweredBy q p) ∨
        ∃ q ∈ qs, PartiallyAnsweredBy q pᶜ := by
  simp only [IsRelevantTo, alt_polar_of_nontrivial hne hnu,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left]

/-! ### Decision by a common ground -/

section DecidedBy

open Filter

variable {f g : Filter W} {p : Set W} {P : Question W}

/-- The common ground `f` decides the issue `P` when it entails one of its complete answers. -/
def DecidedBy (P : Question W) (f : Filter W) : Prop := ∃ q ∈ alt P, q ∈ f

theorem DecidedBy.mono (h : f ≤ g) : P.DecidedBy g → P.DecidedBy f :=
  Exists.imp fun _ ⟨hq, hg⟩ ↦ ⟨hq, h hg⟩

theorem DecidedBy.ker_mem (h : P.DecidedBy f) : f.ker ∈ P :=
  let ⟨q, hq, hf⟩ := h
  P.downward_closed q (mem_of_mem_alt hq) _ (Set.sInter_subset_of_mem hf)

theorem decidedBy_principal (hQ : Q.IsNormal) : Q.DecidedBy (𝓟 σ) ↔ σ ∈ Q :=
  (mem_iff_exists_alt_subset hQ).symm

@[simp] theorem decidedBy_top : (⊤ : Question W).DecidedBy f := ⟨_, by simp, univ_mem⟩

@[simp] theorem decidedBy_ofSet : (ofSet p).DecidedBy f ↔ p ∈ f := by simp [DecidedBy]

@[simp] theorem decidedBy_polar : (polar p).DecidedBy f ↔ p ∈ f ∨ pᶜ ∈ f := by
  by_cases h : p = ∅ ∨ p = Set.univ
  · rcases h with rfl | rfl <;> simp [polar_empty, polar_univ]
  · simp [DecidedBy, mem_alt_polar_of_nontrivial (not_or.1 h).1 (not_or.1 h).2]

end DecidedBy

end Question
