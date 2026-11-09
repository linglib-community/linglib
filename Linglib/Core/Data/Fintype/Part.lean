/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Linglib.Core.Data.Part

/-!
# Finitely many partial values

`Part α` is finite when `α` is, its elements being the images of `Option α` under
`Part.ofOption` (`Part.fintype`, computable without `DecidableEq`). A claim about every family of
partial values, or about some family, is decided over the families of options
(`Part.forall_pi_iff`, `Part.exists_pi_iff`); the classical step stays in the proof of the
equivalence, so the decision procedure computes. Equality and the order of two families over a
finite index type are decided pointwise from decidable domains. [UPSTREAM]
-/

@[expose] public section

namespace Part

variable {α : Type*}

/-- The partial values of a finite type are the images of its options. -/
instance fintype [Fintype α] : Fintype (Part α) where
  elems := Finset.univ.map ⟨Part.ofOption, fun a b h ↦ Option.ext fun x ↦ by
    rw [← Option.mem_def, ← Option.mem_def, ← Part.mem_ofOption, h, Part.mem_ofOption]⟩
  complete o := by
    classical
    exact Finset.mem_map.2 ⟨o.toOption, Finset.mem_univ _, Part.of_toOption o⟩

end Part

section Pi

variable {ι : Type*} {β : ι → Type*}

instance Pi.partDecidableEq [Fintype ι] [∀ i, DecidableEq (β i)] (f g : ∀ i, Part (β i))
    [∀ i, Decidable (f i).Dom] [∀ i, Decidable (g i).Dom] : Decidable (f = g) :=
  decidable_of_iff (∀ i, f i = g i) funext_iff.symm

instance Pi.partDecidableLE [Fintype ι] [∀ i, DecidableEq (β i)] (f g : ∀ i, Part (β i))
    [∀ i, Decidable (f i).Dom] [∀ i, Decidable (g i).Dom] : Decidable (f ≤ g) :=
  decidable_of_iff (∀ i, f i ≤ g i) Iff.rfl

/-- Every family of partial values is the image of a family of options. -/
theorem Part.forall_pi_iff {P : (∀ i, Part (β i)) → Prop} :
    (∀ g, P g) ↔ ∀ g : ∀ i, Option (β i), P fun i ↦ ↑(g i) := by
  classical
  exact ⟨fun h g ↦ h _, fun h g ↦ by simpa using h fun i ↦ (g i).toOption⟩

theorem Part.exists_pi_iff {P : (∀ i, Part (β i)) → Prop} :
    (∃ g, P g) ↔ ∃ g : ∀ i, Option (β i), P fun i ↦ ↑(g i) := by
  classical
  exact ⟨fun ⟨g, h⟩ ↦ ⟨fun i ↦ (g i).toOption, by simpa using h⟩, fun ⟨g, h⟩ ↦ ⟨_, h⟩⟩

instance Part.decidableForallPi [Fintype ι] [DecidableEq ι] [∀ i, Fintype (β i)]
    (P : (∀ i, Part (β i)) → Prop) [∀ g : ∀ i, Option (β i), Decidable (P fun i ↦ ↑(g i))] :
    Decidable (∀ g, P g) :=
  decidable_of_iff _ Part.forall_pi_iff.symm

instance Part.decidableExistsPi [Fintype ι] [DecidableEq ι] [∀ i, Fintype (β i)]
    (P : (∀ i, Part (β i)) → Prop) [∀ g : ∀ i, Option (β i), Decidable (P fun i ↦ ↑(g i))] :
    Decidable (∃ g, P g) :=
  decidable_of_iff _ Part.exists_pi_iff.symm

/-- The families defined exactly where `p` holds are the restrictions of total families to `p`,
pointwise mathlib's `PFun.res`. -/
theorem Part.forall_dom_iff_forall_pi [∀ i, Nonempty (β i)] {p : ι → Prop}
    {P : (∀ i, Part (β i)) → Prop} :
    (∀ g : ∀ i, Part (β i), (∀ i, (g i).Dom ↔ p i) → P g) ↔
      ∀ f : ∀ i, β i, P fun i ↦ ⟨p i, fun _ ↦ f i⟩ := by
  classical
  refine ⟨fun h f ↦ h _ fun _ ↦ .rfl, fun h g hg ↦ ?_⟩
  convert h (fun i ↦ if hi : (g i).Dom then (g i).get hi else Classical.arbitrary _) using 1
  funext i
  exact Part.ext' (hg i) fun h₁ _ ↦ by simp [h₁]

/-- Over a finite index type, a claim about every family defined exactly where a decidable `p`
holds is decided over the total families. -/
instance Part.decidableForallDomPi [Fintype ι] [DecidableEq ι] [∀ i, Fintype (β i)]
    [∀ i, Nonempty (β i)] {p : ι → Prop} (P : (∀ i, Part (β i)) → Prop)
    [∀ f : ∀ i, β i, Decidable (P fun i ↦ ⟨p i, fun _ ↦ f i⟩)] :
    Decidable (∀ g : ∀ i, Part (β i), (∀ i, (g i).Dom ↔ p i) → P g) :=
  decidable_of_iff _ Part.forall_dom_iff_forall_pi.symm

end Pi
