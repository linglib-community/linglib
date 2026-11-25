module

public import Linglib.Semantics.Quantifier.Continuation
public import Linglib.Semantics.Quantifier.Individual
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Predicative content

`BE` is Montague's translation of *be*, which Partee recast as a type shift. It takes a quantifier
`Q` to its predicative content, the set of the entities whose singleton `Q` holds of:
`BE Q = {x | Q {x}}`. This file defines `BE` as a complete lattice homomorphism and relates it to
the existential determiner denotation `Det.some`, Partee's `A`, which is a section of it.

## Main definitions

* `Quantifier.BE`: the complete lattice homomorphism taking `Q` to `{x | Q {x}}`.
* `Quantifier.gciSomeBE`: the Galois coinsertion that `Det.some` and `BE` form on the monotone
  quantifiers.
* `Quantifier.mapHom`: the image of a quantifier under a function, as a complete lattice
  homomorphism.

## Main results

* `Quantifier.BE_unique`: `BE` is the only complete lattice homomorphism that takes each individual
  to its singleton.
* `Quantifier.eq_some_of_leftInverse`: `Det.some` is the only conservative, symmetric, monotone
  determiner denotation that is a section of `BE`.
* `Quantifier.Det.Intersective.mem_BE`: for an intersective `D`, `x ∈ BE (D A)` if and only if
  `D (A ∩ {x}) (A ∩ {x})`.
* `Quantifier.mem_BE_the`: `x ∈ BE (the A)` if and only if `A = {x}`.
* `Quantifier.BE_the_not_mem_range_const`: if `P` has different single members at two indices, then
  `BE (the (P w))` is not constant in `w`.

## Implementation notes

Fact 2 of [partee-1987], the uniqueness of `BE`, is stated for complete homomorphisms: on an
infinite domain a Boolean homomorphism can agree with `BE` on the individuals and differ
elsewhere (`Studies/Partee1987.lean`).

## References

* [partee-1987]
-/

@[expose] public section

namespace Quantifier

open Quantifier.Det

variable {E : Type*}

/-! ### `BE` and its sections -/

/-- `BE Q` is the predicative content of the quantifier `Q`, `BE(Q) = {x | Q {x}}`, which
preserves arbitrary meets and joins. -/
def BE : CompleteLatticeHom (Quantifier E) (Set E) where
  toFun Q := {x | Q {x}}
  map_sInf' _ := Set.ext fun _ ↦ by simp
  map_sSup' _ := Set.ext fun _ ↦ by simp

@[simp] theorem mem_BE (Q : Quantifier E) (x : E) : x ∈ BE Q ↔ Q {x} := .rfl

@[simp] theorem BE_individual (j : E) : BE (individual j) = {j} :=
  Set.ext fun _ ↦ eq_comm

/-- `BE ∘ A` is the identity: *be a man* is *man*. -/
@[simp] theorem BE_some (A : Set E) : BE (Det.some A) = A :=
  Set.ext fun _ ↦ Set.inter_singleton_nonempty

theorem some_injective : Function.Injective (Det.some : Det E) :=
  Function.LeftInverse.injective BE_some

theorem some_BE_eq_self_iff {Q : Quantifier E} : Det.some (BE Q) = Q ↔ ∃ A, Det.some A = Q :=
  ⟨fun h ↦ ⟨_, h⟩, fun ⟨A, h⟩ ↦ h ▸ congrArg Det.some (BE_some A)⟩

/-- `BE` is the only complete homomorphism taking each individual to its singleton, Fact 2 of
[partee-1987]. -/
theorem BE_unique {f : CompleteLatticeHom (Quantifier E) (Set E)}
    (h : ∀ a, f (individual a) = {a}) : f = BE :=
  completeLatticeHom_ext fun a ↦ (h a).trans (BE_individual a).symm

/-- Among the conservative determiner denotations, `Det.some` is the only symmetric, monotone
section of `BE` ([partee-1987], §3.3). -/
theorem eq_some_of_leftInverse [Nonempty E] {D : Det E} (hc : D.Conservative) [Std.Symm D]
    (hm : D.ScopeMonotone) (h : Function.LeftInverse BE D) : D = Det.some := by
  ext A B
  change _ ↔ (A ∩ B).Nonempty
  rw [hc.iff_inter_inter]
  refine ⟨fun hAB ↦ Set.nonempty_iff_ne_empty.2 fun he ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty E›
    have : x ∈ BE (D ∅) := hm ∅ (Set.empty_subset {x}) (he ▸ hAB)
    rwa [h ∅] at this
  · exact hm _ (Set.singleton_subset_iff.2 hx) ((h (A ∩ B)).symm ▸ hx : x ∈ BE (D (A ∩ B)))

/-- For an intersective determiner denotation `D`, an entity `x` is in `BE (D A)` if and only if `D`
holds of `A ∩ {x}` and `A ∩ {x}`. -/
theorem Det.Intersective.mem_BE {D : Det E} (hD : D.Intersective) {A : Set E} {x : E} :
    x ∈ BE (D A) ↔ D (A ∩ {x}) (A ∩ {x}) :=
  hD _ _ _ _ (Set.inter_self _).symm

theorem iota_BE_individual (a : E) : iota (BE (individual a)) = Part.some a := by
  rw [BE_individual, iota_singleton]

/-! ### The definite article -/

/-- *Be the `A`* holds of `x` when `x` is the only `A` ([partee-1987], §3.2). -/
theorem mem_BE_the {A : Set E} {x : E} : x ∈ BE (the A) ↔ A = {x} :=
  ⟨fun ⟨_, hz, hzx⟩ ↦ Set.ext fun z ↦ (hz z).trans (by rw [hzx]; rfl),
    fun h ↦ ⟨x, fun z ↦ h ▸ Iff.rfl, rfl⟩⟩

/-- On a restrictor with at most one member, *be the `A`* is `A` ([partee-1987], §3.2). -/
theorem BE_the_of_subsingleton {A : Set E} (hA : A.Subsingleton) : BE (the A) = A :=
  Set.ext fun _ ↦ mem_BE_the.trans ⟨fun h ↦ h ▸ rfl, hA.eq_singleton_of_mem⟩

/-- On a nonempty restrictor, *be every `A`* is *be the `A`* ([partee-1987], §3.3). -/
theorem BE_every_of_nonempty {A : Set E} (hA : A.Nonempty) : BE (every A) = BE (the A) :=
  Set.ext fun _ ↦ hA.subset_singleton_iff.trans mem_BE_the.symm

/-- If `P` has different single members at two indices, then the predicative definite
`BE (the (P w))` is not constant in `w` ([partee-1987], fn. 16). -/
theorem BE_the_not_mem_range_const {W : Type*} {P : W → Set E} {w₀ w₁ : W} {a b : E}
    (h₀ : P w₀ = {a}) (h₁ : P w₁ = {b}) (hab : a ≠ b) :
    (fun w ↦ BE (the (P w))) ∉ Set.range (Function.const W) := by
  rintro ⟨B, hB⟩
  have h₀' := congrFun hB w₀
  have h₁' := congrFun hB w₁
  simp only [Function.const_apply, h₀, h₁,
    BE_the_of_subsingleton Set.subsingleton_singleton] at h₀' h₁'
  exact hab (Set.singleton_injective (h₀'.symm.trans h₁'))

/-! ### The Galois coinsertion on monotone quantifiers -/

theorem individual_le_iff {Q : Quantifier E} (hQ : Monotone Q) {x : E} :
    individual x ≤ Q ↔ x ∈ BE Q :=
  ⟨fun h ↦ h _ rfl, fun h _ hB ↦ hQ (Set.singleton_subset_iff.2 hB) h⟩

theorem some_le_iff {Q : Quantifier E} (hQ : Monotone Q) {A : Set E} :
    Det.some A ≤ Q ↔ A ⊆ BE Q := by
  simp only [some_eq_iSup_individual, iSup₂_le_iff, individual_le_iff hQ]
  rfl

/-- On the monotone quantifiers `Det.some` and `BE` form a Galois coinsertion. -/
def gciSomeBE :
    GaloisCoinsertion (fun A ↦ (⟨Det.some A, monotone_some A⟩ : Set E →o Prop)) fun Q ↦ BE Q :=
  GaloisConnection.toGaloisCoinsertion (fun _ Q ↦ some_le_iff Q.monotone) fun A ↦ (BE_some A).le

/-! ### Images -/

section Map

variable {F : Type*} (f : E → F)

/-- `Quantifier.map` as a complete lattice homomorphism. -/
def mapHom : CompleteLatticeHom (Quantifier E) (Quantifier F) where
  toFun := map f
  map_sInf' _ := funext fun _ ↦ by simp [map]
  map_sSup' _ := funext fun _ ↦ by simp [map]

@[simp] theorem mapHom_apply (Q : Quantifier E) : mapHom f Q = Q.map f := rfl

theorem map_some (A : Set E) : (Det.some A).map f = Det.some (f '' A) :=
  funext fun B ↦ propext <| by
    change (A ∩ f ⁻¹' B).Nonempty ↔ (f '' A ∩ B).Nonempty
    rw [← Set.image_inter_preimage, Set.image_nonempty]

theorem map_every (A : Set E) : (every A).map f = every (f '' A) :=
  funext fun _ ↦ propext Set.image_subset_iff.symm

theorem map_no (A : Set E) : (no A).map f = no (f '' A) :=
  funext fun B ↦ propext <| by
    change A ⊆ f ⁻¹' Bᶜ ↔ f '' A ⊆ Bᶜ
    exact Set.image_subset_iff.symm

end Map

end Quantifier
