module

public import Linglib.Semantics.Questions.Inquisitive.Polar
public import Linglib.Semantics.Questions.Inquisitive.Constituent
public import Mathlib.Order.Filter.Ker

/-!
# Answerhood predicates on questions

Let `Q : Question W` be a question and `σ` an information state, a set of worlds. This file defines
three senses in which `σ` answers `Q`.

* `σ` resolves `Q` when `σ ∈ Q`. For a normal question this means that `σ` is included in some
  alternative.
* `σ` completely answers `Q` when it decides every alternative, either entailing it or excluding it.
  This is `CompletelyAnsweredBy Q σ`.
* `σ` partially answers `Q` when it decides at least one alternative. This is
  `PartiallyAnsweredBy Q σ`.

Resolution is the mention-some reading of a question, and complete answerhood is the mention-all
reading.

## Implementation notes

`CompletelyAnsweredBy` decides each alternative rather than entailing every one, which would
collapse to `σ ⊆ ⋂ alt Q` and is incoherent for partition questions with disjoint
alternatives; the decided form is [groenendijk-stokhof-1984]'s strong exhaustivity on
partition questions, and `Hamblin/Basic.lean` relates it to the weak and strong answers on Hamblin
sets ([heim-1994]). Mention-some answerhood
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

variable {σ : Set W} {Q : Question W}

/-! ### Basic relationships -/

theorem mem_of_exists_alt_subset (h : ∃ p ∈ alt Q, σ ⊆ p) : σ ∈ Q :=
  let ⟨p, hp, hsub⟩ := h
  Q.downward_closed p (alt_subset_props _ hp) σ hsub

theorem mem_iff_exists_alt_subset (hQ : Q.IsNormal) : σ ∈ Q ↔ ∃ p ∈ alt Q, σ ⊆ p :=
  ⟨fun h ↦ hQ h, mem_of_exists_alt_subset⟩

theorem partiallyAnsweredBy_of_mem (hQ : Q.IsNormal) (h : σ ∈ Q) :
    PartiallyAnsweredBy Q σ :=
  let ⟨p, hp, hsub⟩ := hQ h
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

/-! ### Contextual subquestions -/

/-- `P` is a subquestion of `Q` relative to the context `C` ([roberts-2012]): every complete
answer to `P` contextually partially answers `Q`. The entailment is contextual, not question
entailment, so the relation is not transitive in general. -/
def IsSubquestionOf (C : Set W) (P Q : Question W) : Prop :=
  ∀ σ ∈ completeAnswers P, PartiallyAnsweredBy Q (C ∩ σ)

/-- A question with an alternative is a subquestion of any question whose alternatives include
its own, since each of its complete answers decides one of them. -/
theorem isSubquestionOf_of_alt_subset (C : Set W) {P Q : Question W} (hP : (alt P).Nonempty)
    (h : alt P ⊆ alt Q) : IsSubquestionOf C P Q := fun _ hσ ↦
  let ⟨a, ha⟩ := hP
  ⟨a, h ha, (hσ a ha).imp (Set.inter_subset_right.trans ·) (Set.inter_subset_right.trans ·)⟩

theorem IsSubquestionOf.refl (C : Set W) {P : Question W} (hP : (alt P).Nonempty) :
    IsSubquestionOf C P P :=
  isSubquestionOf_of_alt_subset C hP subset_rfl

theorem partiallyAnsweredBy_inter_iff {Q : Question W} {C σ : Set W} :
    PartiallyAnsweredBy Q (C ∩ σ) ↔
      ∃ p ∈ alt Q, σ ∈ (ofSet p).relativeTo C ∨ σ ∈ (ofSet pᶜ).relativeTo C := by
  simp only [PartiallyAnsweredBy, mem_relativeTo, mem_ofSet]

theorem isSubquestionOf_iff {C : Set W} {P Q : Question W} :
    IsSubquestionOf C P Q ↔ ∀ σ ∈ completeAnswers P,
      ∃ p ∈ alt Q, σ ∈ (ofSet p).relativeTo C ∨ σ ∈ (ofSet pᶜ).relativeTo C := by
  simp only [IsSubquestionOf, partiallyAnsweredBy_inter_iff]

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
