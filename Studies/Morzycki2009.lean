module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Degree.Comparison

/-!
# Morzycki (2009): Degree Modification of Gradable Nouns

This file formalizes Morzycki's account of the degree readings of size adjectives, *big idiot*
as a very idiotic person. A gradable noun denotes a measure function from individuals to
degrees, and its positive form holds of the individuals that reach the noun's standard `s`, the
preimage of `Set.Ici s`. A size adjective in a degree reading is the argument of an adnominal
degree head, the nominal counterpart of the head that combines an adjective with a measure phrase
(`meas`): the individual's degree must reach the least degree the size adjective is true of, and
also the noun's standard (`measN`). The resulting predicate is the positive form with the
standard raised to that least degree (`measN_eq_preimage_Ici_sup`).

The Bigness Generalization, that only adjectives of bigness license degree readings, follows.
Antonyms measure along oppositely ordered scales, so the bottom of the noun's scale counts as
small wherever the standard of smallness lies, the least small degree is the bottom, and
*small idiot* is *idiot* (`measN_small`), whereas the least big degree properly raises a lower
standard (`measN_ssubset_preimage_Ici`). The degree head *complete* requires the maximum of the
noun's scale and so combines only with nouns whose scales have one
(`hasMax_of_complete_nonempty`).

## Implementation notes

The scale of a gradable noun is the whole degree type, so the restriction of the least degree
to the noun's scale is left implicit. The Position Generalization, that degree readings arise
only attributively, is imposed by the syntax of the nominal degree projection and is not
represented, and neither are the degree heads *real*, *true*, *total* and *absolute*.

## References

* [morzycki-2009]
* [kennedy-mcnally-2005]
-/

@[expose] public section

namespace Morzycki2009

open Degree

variable {E D S : Type*}

/-! ### Positive forms and degree heads -/

section Preorder
variable [Preorder D]

/-- The head that combines a gradable predicate with a measure phrase `m`, a property of
degrees, requires the individual's degree to reach the least degree that `m` is true of, as in
*six feet tall*. -/
def meas (g : E → D) (m : Set D) : Set E := {x | ∃ d, IsLeast m d ∧ d ≤ g x}

/-- The adnominal head that combines a gradable noun with a size adjective requires in addition
that the noun's standard be reached, since a big idiot is an idiot while someone six feet tall
need not be tall. -/
def measN (g : E → D) (s : D) (m : Set D) : Set E := meas g m ∩ g ⁻¹' Set.Ici s

/-- The degree head *complete* holds of the individuals at the maximum of the scale. -/
def complete (g : E → D) : Set E := {x | IsTop (g x)}

variable {g : E → D} {s d : D} {m : Set D} {x : E}

theorem mem_meas_iff (hd : IsLeast m d) : x ∈ meas g m ↔ d ≤ g x :=
  ⟨fun ⟨_, hd', h⟩ ↦ (hd.2 hd'.1).trans h, fun h ↦ ⟨d, hd, h⟩⟩

theorem meas_eq_preimage (hm : IsUpperSet m) (hd : IsLeast m d) : meas g m = g ⁻¹' m :=
  Set.ext fun _ ↦ (mem_meas_iff hd).trans ⟨fun h ↦ hm h hd.1, fun h ↦ hd.2 h⟩

theorem measN_subset_preimage_Ici : measN g s m ⊆ g ⁻¹' Set.Ici s := Set.inter_subset_right

theorem complete_subset_preimage_Ici : complete g ⊆ g ⁻¹' Set.Ici s := fun _ h ↦ h s

theorem hasMax_of_complete_nonempty (h : (complete g).Nonempty) :
    (Boundedness.ofOrder D).HasMax :=
  Boundedness.hasMax_ofOrder.2 <| h.elim fun x hx ↦ ⟨g x, hx⟩

end Preorder

/-! ### The Bigness Generalization -/

section Sup
variable [SemilatticeSup D] {g : E → D} {s d : D} {m : Set D}

theorem measN_eq_preimage_Ici_sup (hd : IsLeast m d) : measN g s m = g ⁻¹' Set.Ici (s ⊔ d) :=
  Set.ext fun _ ↦ by
    simp only [measN, Set.mem_inter_iff, mem_meas_iff hd, Set.mem_preimage, Set.mem_Ici,
      sup_le_iff, and_comm]

theorem measN_eq_preimage_Ici_of_bot_mem [OrderBot D] (h : ⊥ ∈ m) :
    measN g s m = g ⁻¹' Set.Ici s := by
  rw [measN_eq_preimage_Ici_sup ⟨h, fun _ _ ↦ bot_le⟩, sup_bot_eq]

theorem measN_small [OrderBot D] [Preorder S] {big : D → S} (hbig : Monotone big) {θ : Sᵒᵈ}
    (h : ((OrderDual.toDual ∘ big) ⁻¹' Set.Ici θ).Nonempty) :
    measN g s ((OrderDual.toDual ∘ big) ⁻¹' Set.Ici θ) = g ⁻¹' Set.Ici s :=
  measN_eq_preimage_Ici_of_bot_mem <| h.elim fun _ hd ↦
    show θ ≤ _ from le_trans hd (hbig.dual_right bot_le)

theorem measN_ssubset_preimage_Ici (hd : IsLeast m d) (hsd : s < d) {x : E} (hx : g x = s) :
    measN g s m ⊂ g ⁻¹' Set.Ici s :=
  ⟨measN_subset_preimage_Ici, fun h ↦ by
    have := h (show x ∈ g ⁻¹' Set.Ici s from hx.ge)
    rw [measN_eq_preimage_Ici_sup hd, Set.mem_preimage, Set.mem_Ici, hx, sup_le_iff] at this
    exact hsd.not_ge this.2⟩

/-- With the standard of idiocy at 3 and *big* true of the degrees from 5, a degree of 8 is that
of a big idiot, and a degree of 4 that of an idiot who is not a big one. -/
example : 8 ∈ measN (id : ℕ → ℕ) 3 (Set.Ici 5) ∧ 4 ∈ (id : ℕ → ℕ) ⁻¹' Set.Ici 3 ∧
    4 ∉ measN (id : ℕ → ℕ) 3 (Set.Ici 5) := by
  simp [measN_eq_preimage_Ici_sup isLeast_Ici]

end Sup

end Morzycki2009
