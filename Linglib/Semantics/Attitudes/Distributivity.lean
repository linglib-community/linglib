module

public import Mathlib.Order.SetNotation
import Linglib.Core.Data.Set.Lattice.Order

/-!
# Clausal distributivity

A clause-embedding predicate relates an entity at a world to a set of propositions: the answers of
a question, or the singleton of a declarative's proposition. On a class of questions it is Q-to-P
entailing when relating an entity to a question relates it to some answer, P-to-Q entailing when
relating it to an answer relates it to the question, and clausally distributive when it is both.
On all sets of propositions, a predicate is clausally distributive exactly when
[it quantifies existentially over answers](##isClausallyDistributive_univ_iff_exists), equivalently
when [it distributes over unions of questions](##isClausallyDistributive_univ_iff_sUnion).

## Implementation notes

The class of questions is an argument because the definitions in the literature differ in it, and
the difference matters: false-answer-sensitive *know* is clausally distributive only on questions
whose answers do not overlap.

## TODO

* Strawson clausal distributivity, on which *care* is distributive, needs presuppositions.

## References

* [belnap-1982]
* [spector-egre-2015]
* [theiler-etal-2018]
* [uegaki-2022]
* [qing-uegaki-2025]
-/

@[expose] public section

variable {W E : Type*}

/-- `V` is Q-to-P entailing on `𝒬` when relating an entity to a question of `𝒬` relates it to one
of the question's answers, [uegaki-2022]'s Q-to-P entailment, (3) of chapter 4. -/
def IsQToPEntailing (𝒬 : Set (Set (Set W))) (V : E → Set (Set W) → W → Prop) : Prop :=
  ∀ Q ∈ 𝒬, ∀ x w, V x Q w → ∃ p ∈ Q, V x {p} w

/-- `V` is P-to-Q entailing on `𝒬` when relating an entity to an answer of a question of `𝒬` relates
it to the question, [uegaki-2022]'s P-to-Q entailment, (27) of chapter 8. -/
def IsPToQEntailing (𝒬 : Set (Set (Set W))) (V : E → Set (Set W) → W → Prop) : Prop :=
  ∀ Q ∈ 𝒬, ∀ x w, ∀ p ∈ Q, V x {p} w → V x Q w

/-- `V` is clausally distributive on `𝒬` when it relates an entity to a question of `𝒬` exactly when
it relates it to some answer, [belnap-1982]'s distributivity principle. [qing-uegaki-2025]'s (15)
takes `𝒬` to be any embedded question and [theiler-etal-2018]'s Definition 8 those without
overlapping answers. -/
def IsClausallyDistributive (𝒬 : Set (Set (Set W))) (V : E → Set (Set W) → W → Prop) : Prop :=
  ∀ Q ∈ 𝒬, ∀ x w, V x Q w ↔ ∃ p ∈ Q, V x {p} w

variable {𝒬 : Set (Set (Set W))} {V : E → Set (Set W) → W → Prop}

theorem IsClausallyDistributive.isQToPEntailing (h : IsClausallyDistributive 𝒬 V) :
    IsQToPEntailing 𝒬 V :=
  fun Q hQ x w ↦ (h Q hQ x w).1

theorem IsClausallyDistributive.isPToQEntailing (h : IsClausallyDistributive 𝒬 V) :
    IsPToQEntailing 𝒬 V :=
  fun Q hQ x w p hp hV ↦ (h Q hQ x w).2 ⟨p, hp, hV⟩

theorem isClausallyDistributive_iff :
    IsClausallyDistributive 𝒬 V ↔ IsQToPEntailing 𝒬 V ∧ IsPToQEntailing 𝒬 V :=
  ⟨fun h ↦ ⟨h.isQToPEntailing, h.isPToQEntailing⟩,
    fun ⟨h₁, h₂⟩ Q hQ x w ↦ ⟨h₁ Q hQ x w, fun ⟨p, hp, hV⟩ ↦ h₂ Q hQ x w p hp hV⟩⟩

/-- A predicate quantifying existentially over answers is clausally distributive. -/
theorem IsClausallyDistributive.of_forall_iff_exists (R : E → Set W → W → Prop)
    (h : ∀ x Q w, V x Q w ↔ ∃ p ∈ Q, R x p w) : IsClausallyDistributive 𝒬 V :=
  fun Q _ x w ↦ by simp [h]

/-- A predicate is clausally distributive on all sets of propositions exactly when it is existential
quantification over answers of a relation to propositions, as proposition-oriented theories have
it. -/
theorem isClausallyDistributive_univ_iff_exists :
    IsClausallyDistributive Set.univ V ↔
      ∃ R : E → Set W → W → Prop, ∀ x Q w, V x Q w ↔ ∃ p ∈ Q, R x p w :=
  ⟨fun h ↦ ⟨fun x p w ↦ V x {p} w, fun x Q w ↦ h Q trivial x w⟩,
    fun ⟨R, h⟩ ↦ .of_forall_iff_exists R h⟩

/-- A predicate is clausally distributive on all sets of propositions exactly when it distributes
over unions of questions: as a map into `Prop` it preserves suprema, like a distributive context
change potential, `DynamicSemantics.CCP.isDistributive_iff_map_sSup`. -/
theorem isClausallyDistributive_univ_iff_sUnion :
    IsClausallyDistributive Set.univ V ↔
      ∀ x w (𝒯 : Set (Set (Set W))), V x (⋃₀ 𝒯) w ↔ ∃ Q ∈ 𝒯, V x Q w := by
  have h := fun x w ↦ Set.forall_map_sSup_iff (f := fun Q ↦ V x Q w)
  simp only [Set.sSup_eq_sUnion, iSup_Prop_eq, eq_iff_iff, exists_prop] at h
  exact ⟨fun hV x w ↦ (h x w).2 fun Q ↦ hV Q trivial x w,
    fun hV Q _ x w ↦ (h x w).1 (hV x w) Q⟩
