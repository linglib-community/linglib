module

public import Linglib.Phonology.OptimalityTheory.Grammar

/-!
# Realization problems

A realization problem is a constraint system with a target output for each of finitely many
inputs: the tableaux of an analysis with their winners. A ranking realizes it when it picks the
target on every input. Provided no competitor ties a target, that is to
[satisfy its ERCs](##OptimalityTheory.RealizationProblem.realizedByRanking_iff_satisfiedBy), and
a relation on the constraints realizes it iff its grammar
[lies below the problem's](##OptimalityTheory.RealizationProblem.realizedByPartialOrder_iff_le).

## References

* [prince-2002]
* [tesar-smolensky-1995]
-/

@[expose] public section

namespace OptimalityTheory

variable {Input Output ι : Type*} {n : ℕ}

/-- A realization problem is a constraint system with a target output for each of finitely many
    inputs, which a single grammar must select on every input at once. For OT it is the data of
    [tesar-smolensky-1995]'s ranking problem. -/
structure RealizationProblem (Input : Type*) (Output : Type*) (ι : Type*)
    extends ConstraintSystem Input Output ι where
  /-- The grammar handles a finite set of inputs. -/
  inputs : Finset Input
  /-- The grammar must select the target output on each input. -/
  target : Input → Output
  /-- Each target output is a candidate of its input. -/
  target_mem : ∀ i ∈ inputs, target i ∈ gen i

namespace RealizationProblem

/-- The ranking `σ` *OT-realizes* the target when on every input it picks the target, the sole
    winner of the input's tableau under `σ`. -/
def realizedByRanking (P : RealizationProblem Input Output ι)
    (σ : Ranking.Enumeration ι n) : Prop :=
  ∀ i ∈ P.inputs, P.toConstraintSystem.PicksAt σ i (P.target i)

instance [DecidableEq Output] (P : RealizationProblem Input Output ι)
    (σ : Ranking.Enumeration ι n) :
    Decidable (P.realizedByRanking σ) := by
  unfold realizedByRanking; infer_instance

/-! ### OT-realization is ERC satisfaction -/

/-- The winner–loser ERCs of a problem are those of each input's target against its rivals
    ([prince-2002]). -/
def ercs (P : RealizationProblem Input Output ι) : Set (ERC ι) :=
  ⋃ i ∈ P.inputs, P.toConstraintSystem.ercs i (P.target i)

theorem mem_ercs {P : RealizationProblem Input Output ι} {α : ERC ι} :
    α ∈ P.ercs ↔ ∃ i ∈ P.inputs, ∃ o ∈ P.gen i, o ≠ P.target i ∧
      ercOfProfiles (P.marks i (P.target i)) (P.marks i o) = α := by
  simp only [ercs, Set.mem_iUnion, exists_prop]
  rfl

/-- Provided no competitor ties the target's violation profile, `σ` realizes the target iff `σ`
    satisfies every winner–loser ERC ([prince-2002]). -/
theorem realizedByRanking_iff_satisfiedBy {P : RealizationProblem Input Output ι}
    {σ : Ranking.Enumeration ι n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.gen i, o ≠ P.target i →
      (P.marks i (P.target i)) ≠ (P.marks i o)) :
    P.realizedByRanking σ ↔ ∀ α ∈ P.ercs, α.SatisfiedBy σ := by
  refine ⟨fun h α hα ↦ ?_, fun h i hi ↦ ?_⟩
  · obtain ⟨i, hi, hα⟩ := mem_ercs.1 hα
    exact (ConstraintSystem.picksAt_iff_forall_ercs_satisfiedBy (P.target_mem i hi)
      (hvp i hi)).1 (h i hi) α hα
  · exact (ConstraintSystem.picksAt_iff_forall_ercs_satisfiedBy (P.target_mem i hi)
      (hvp i hi)).2 fun α hα ↦ h α (mem_ercs.2 ⟨i, hi, hα⟩)

/-- The grammar of a problem is the grammar that its winner–loser ERCs present. -/
def grammar (P : RealizationProblem Input Output ι) : Grammar.Enumeration ι n := .ofERCs P.ercs

/-- Provided no competitor ties the target's violation profile, the rankings of a problem's
    grammar are those that realize its target. -/
theorem mem_extent_grammar {P : RealizationProblem Input Output ι}
    {σ : Ranking.Enumeration ι n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.gen i, o ≠ P.target i →
      (P.marks i (P.target i)) ≠ (P.marks i o)) :
    σ ∈ (P.grammar (n := n)).extent ↔ P.realizedByRanking σ :=
  (realizedByRanking_iff_satisfiedBy hvp).symm

/-- A problem is OT-realizable when some constraint ranking realizes its target. -/
def IsOTRealizable [Fintype ι] (P : RealizationProblem Input Output ι) : Prop :=
  ∃ σ : Ranking ι, P.realizedByRanking σ

instance [Fintype ι] [DecidableEq ι] [DecidableEq Output]
    (P : RealizationProblem Input Output ι) :
    Decidable P.IsOTRealizable := by
  unfold IsOTRealizable; infer_instance

/-- A problem is OT-realizable iff its grammar has a ranking. -/
theorem isOTRealizable_iff_extent_nonempty [Fintype ι]
    {P : RealizationProblem Input Output ι}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.gen i, o ≠ P.target i →
      (P.marks i (P.target i)) ≠ (P.marks i o)) :
    P.IsOTRealizable ↔ (P.grammar : Grammar ι).extent.Nonempty :=
  exists_congr fun _ ↦ (mem_extent_grammar hvp).symm

/-! ### Realization by a partial order -/

/-- A grammar `r` **POC-realizes** the target if every consistent extension
    realizes it. Since consistent extensions always exist
    (`Ranking.Enumeration.exists_isLinearExtension`), this is never vacuous. -/
def realizedByPartialOrder (n : ℕ) (P : RealizationProblem Input Output ι) (r : ι → ι → Prop) :
    Prop :=
  ∀ σ : Ranking.Enumeration ι n, σ.IsLinearExtension r → P.realizedByRanking σ

/-- A partial order realizes the target iff its grammar lies below the problem's: every one of
    its linear extensions is a ranking that realizes the target. -/
theorem realizedByPartialOrder_iff_le [DecidableEq ι] {P : RealizationProblem Input Output ι}
    {r : ι → ι → Prop}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.gen i, o ≠ P.target i →
      (P.marks i (P.target i)) ≠ (P.marks i o)) :
    P.realizedByPartialOrder n r ↔ Grammar.Enumeration.ofRel r ≤ P.grammar (n := n) := by
  rw [← Concept.extent_subset_extent_iff]
  exact ⟨fun h σ hσ ↦ (mem_extent_grammar hvp).2 (h σ (Grammar.Enumeration.mem_extent_ofRel.1 hσ)),
    fun h σ hσ ↦ (mem_extent_grammar hvp).1 (h (Grammar.Enumeration.mem_extent_ofRel.2 hσ))⟩

/-- A problem is realizable by a partial order when every ranking extending some partial order
on the constraints realizes its target. -/
def IsPartialOrderRealizable [Fintype ι] (P : RealizationProblem Input Output ι) : Prop :=
  ∃ r : ι → ι → Prop, IsPartialOrder ι r ∧ P.realizedByPartialOrder (Fintype.card ι) r

variable [Fintype ι] {P : RealizationProblem Input Output ι}

theorem IsPartialOrderRealizable.isOTRealizable (h : P.IsPartialOrderRealizable) :
    P.IsOTRealizable := by
  obtain ⟨r, hpo, hreal⟩ := h
  have := hpo
  obtain ⟨σ, hσ⟩ := Ranking.Enumeration.exists_isLinearExtension r rfl
  exact ⟨σ, hreal σ hσ⟩

theorem IsOTRealizable.isPartialOrderRealizable (h : P.IsOTRealizable) :
    P.IsPartialOrderRealizable := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.toRel, inferInstance, fun τ hτ ↦ Ranking.Enumeration.toRel_le_toRel_iff.mp hτ ▸ hσ⟩

/-- A problem that some ranking realizes is one that some partial order realizes, and
conversely: a partial order differs from a ranking in the measure on its linear extensions. -/
theorem isOTRealizable_iff_isPartialOrderRealizable :
    P.IsOTRealizable ↔ P.IsPartialOrderRealizable :=
  ⟨IsOTRealizable.isPartialOrderRealizable, IsPartialOrderRealizable.isOTRealizable⟩

end RealizationProblem

end OptimalityTheory
