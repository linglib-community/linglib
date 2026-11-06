module

public import Linglib.Semantics.Quantification.Individual

/-!
# Intensional quantifiers

A property is a set of individuals at each index, `W → Set E`, and a noun phrase denotes at an
index a set of properties, an intensional quantifier. Its extensional quantifier is its value on
the rigid properties, the constant intensions `Function.const W B`, Montague's `δ*`; reading an
extensional quantifier at an index `w` is a section of that projection. An intensional quantifier
is extensional at `w` when it sees a property only through its extension there, and these are
[exactly the quantifiers read at `w`](##Quantifier.Intensional.isExtensionalAt_iff). The lift of
an individual concept is extensional, and Montague's *be*, which asks of each individual whether
the rigid property of being it is in the quantifier, [is `BE` of the
projection](##Quantifier.Intensional.be_eq_BE_proj) whether or not the quantifier is extensional.

## Implementation notes

Partee's extensional fragment is this layer read at an index: her lift, `BE`, `A` and *the* are
the projections of Montague's, and the shifts that do not factor through the extension are where
she says properties rather than sets are needed (`Studies/Partee1987.lean`). In the composition
engine the constant intension is the unit of the reader of worlds.

## References

* [montague-1973]
* [partee-1987]
-/

@[expose] public section

namespace Quantifier

/-- An intensional quantifier, a set of properties, each a set of individuals at every index. -/
abbrev Intensional (W E : Type*) := (W → Set E) → Prop

namespace Intensional

variable {W E : Type*} {w : W} {𝒬 : Intensional W E}

/-- Montague's `δ*`: the extensional quantifier true of `B` when `𝒬` holds of the rigid
property `B`. -/
def proj : CompleteLatticeHom (Intensional W E) (Quantifier E) where
  toFun 𝒬 B := 𝒬 (Function.const W B)
  map_sInf' _ := funext fun _ ↦ by simp
  map_sSup' _ := funext fun _ ↦ by simp

@[simp] theorem proj_apply (𝒬 : Intensional W E) (B : Set E) :
    proj 𝒬 B ↔ 𝒬 (Function.const W B) := .rfl

/-- The extensional quantifier `q` read at the index `w`. -/
def atIndex (w : W) : CompleteLatticeHom (Quantifier E) (Intensional W E) where
  toFun q P := q (P w)
  map_sInf' _ := funext fun _ ↦ by simp
  map_sSup' _ := funext fun _ ↦ by simp

@[simp] theorem atIndex_apply (w : W) (q : Quantifier E) (P : W → Set E) :
    atIndex w q P ↔ q (P w) := .rfl

@[simp] theorem proj_atIndex (w : W) (q : Quantifier E) : proj (atIndex w q) = q := rfl

/-- `𝒬` is extensional at `w` when it sees a property only through its extension at `w`. -/
def IsExtensionalAt (w : W) (𝒬 : Intensional W E) : Prop :=
  ∀ ⦃P P' : W → Set E⦄, P w = P' w → (𝒬 P ↔ 𝒬 P')

theorem isExtensionalAt_iff : IsExtensionalAt w 𝒬 ↔ atIndex w (proj 𝒬) = 𝒬 := by
  refine ⟨fun h ↦ funext fun P ↦ propext (h (P := Function.const W (P w)) rfl), fun h P P' hP ↦ ?_⟩
  rw [← h]
  exact Iff.of_eq (congrArg (proj 𝒬) hP)

theorem isExtensionalAt_atIndex (w : W) (q : Quantifier E) : IsExtensionalAt w (atIndex w q) :=
  fun _ _ h ↦ Iff.of_eq (congrArg q h)

theorem isExtensionalAt_iff_mem_range : IsExtensionalAt w 𝒬 ↔ 𝒬 ∈ Set.range (atIndex w) :=
  ⟨fun h ↦ ⟨_, isExtensionalAt_iff.1 h⟩, fun ⟨_, h⟩ ↦ h ▸ isExtensionalAt_atIndex w _⟩

theorem IsExtensionalAt.apply_iff (h : IsExtensionalAt w 𝒬) (P : W → Set E) :
    𝒬 P ↔ proj 𝒬 (P w) :=
  Iff.of_eq (congrFun (isExtensionalAt_iff.1 h) P).symm

/-- The lift of an individual concept `c` at `w`, the properties `c` has there. -/
def lift (c : W → E) (w : W) : Intensional W E := fun P ↦ c w ∈ P w

theorem lift_eq_atIndex (c : W → E) (w : W) : lift c w = atIndex w (individual (c w)) := rfl

@[simp] theorem proj_lift (c : W → E) (w : W) : proj (lift c w) = individual (c w) := rfl

/-- Montague's *be*: the individuals whose rigid property of being them is in `𝒬`. -/
def be : CompleteLatticeHom (Intensional W E) (Set E) := BE.comp proj

theorem mem_be (𝒬 : Intensional W E) (x : E) : x ∈ be 𝒬 ↔ 𝒬 (Function.const W {x}) := .rfl

theorem be_eq_BE_proj (𝒬 : Intensional W E) : be 𝒬 = BE (proj 𝒬) := rfl

@[simp] theorem be_atIndex (w : W) (q : Quantifier E) : be (atIndex w q) = BE q := rfl

@[simp] theorem be_lift (c : W → E) (w : W) : be (lift c w) = {c w} := BE_individual (c w)

end Intensional

end Quantifier
