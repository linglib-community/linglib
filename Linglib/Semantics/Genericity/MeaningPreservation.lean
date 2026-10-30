module

public import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Meaning Preservation

This file defines Meaning Preservation, the ranking of covert type shifts that decides which of
the shifts available to a bare nominal it takes. Chierchia restricts covert type shifting
in two ways: the Blocking Principle bars a shift that a determiner of the language lexicalizes,
and Meaning Preservation ranks the shifts, so that a bare nominal takes the highest-ranked of
those available to it. Both rankings in the literature have two tiers, and a two-tier ranking is
the predicate of its upper tier, `Prop` ordered by implication. A shift applies when it is
`MaximalFor` the ranking among the available shifts, that is, when it is available and in the
upper tier unless no available shift is.

Chierchia ranks ∩ alone above ι and ∃, (39b) in Dayal's rendering, so his ranking is
`(· = .down)`. Dayal revises it to {∩, ι} > ∃, (39c), on Chierchia's own rationale that ∩
is preferred because it changes the type without introducing quantificational force, which holds
of ι as well, so hers is `(· ≠ .exists)`. The two rankings choose alike wherever no definite
shift is available, as in a language whose definite article blocks ι and ι^x, and part ways where
ι is available: under Dayal's ranking ι applies whenever it is unblocked, under Chierchia's only
where ∩ is undefined.

## Main definitions

* `Determiner.Inventory.Available`: the covert shifts available to a bare nominal, those defined
  for it and not blocked.

## Main results

* `CovertShift.maximalFor_eq_down_iff`, `CovertShift.maximalFor_ne_exists_iff`: which available
  shifts each ranking selects.
* `CovertShift.maximalFor_available_ne_exists_down`, `…_iota`, `…_exists`: under Dayal's ranking
  ∩ and ι apply wherever available and ∃ only as a last resort.
* `CovertShift.maximalFor_available_eq_down_down`, `…_iota`, `…_exists`: under Chierchia's
  ranking ι and ∃ apply only where ∩ is undefined.
* `CovertShift.maximalFor_available_eq_down_iff_ne_exists`: the rankings agree where no definite
  shift is available.

## Implementation notes

ι^x, the anaphoric definite of Jenks, postdates both rankings, and Moroney is the first to make
it a covert shift. It introduces no quantificational force, so Dayal's ranking puts
it with ∩ and ι, and Chierchia's with ι.

## References

* [chierchia-1998]
* [dayal-2004]
* [jenks-2018]
* [moroney-2021]
-/

@[expose] public section

open Genericity

namespace Determiner.Inventory

/-- A covert shift is available to a bare nominal of number `num` in a language with the
determiners `ds` when it is defined for the nominal, ∩ only where `down` holds (for Chierchia's ∩,
`Kind.down P ∈ K`), and no determiner blocks it for that number. ∩ is undefined for a singular
count noun and for a property anchored to particular entities such as *parts of this machine*
([dayal-2004]'s fn. 1). -/
def Available (ds : Inventory) (num : Number) (down : Prop) (τ : CovertShift) : Prop :=
  (τ = .down → down) ∧ ¬ ds.Blocks num τ

instance (ds : Inventory) (num : Number) (down : Prop) [Decidable down] :
    DecidablePred (ds.Available num down) :=
  fun _ ↦ by unfold Available; infer_instance

variable {ds : Inventory} {num : Number} {down : Prop} {τ : CovertShift}

/-- A shift other than ∩ is available exactly when it is not blocked. -/
theorem available_iff_of_ne_down (h : τ ≠ .down) : ds.Available num down τ ↔ ¬ ds.Blocks num τ :=
  and_iff_right fun h' ↦ absurd h' h

end Determiner.Inventory

namespace Genericity.CovertShift

private theorem maximalFor_prop_iff {ι : Type*} {P T : ι → Prop} {i : ι} :
    MaximalFor P T i ↔ P i ∧ (T i ∨ ∀ j, P j → ¬ T j) :=
  ⟨fun ⟨hi, h⟩ ↦ ⟨hi, or_iff_not_imp_left.2 fun hT _ hj hTj ↦ hT (h hj (fun _ ↦ hTj) hTj)⟩,
    fun ⟨hi, h⟩ ↦ ⟨hi, fun j hj _ hTj ↦ h.resolve_right fun h' ↦ h' j hj hTj⟩⟩

variable {A : CovertShift → Prop} {τ : CovertShift}

/-- Under Chierchia's ranking an available shift applies when it is ∩ or ∩ is unavailable. -/
theorem maximalFor_eq_down_iff :
    MaximalFor A (· = .down) τ ↔ A τ ∧ (τ = .down ∨ ¬ A .down) := by
  rw [maximalFor_prop_iff]
  exact and_congr_right fun _ ↦ or_congr_right
    ⟨fun h hd ↦ h _ hd rfl, fun h _ hj hd ↦ h (hd ▸ hj)⟩

/-- Under Dayal's ranking an available shift applies when it is not ∃ or only ∃ is available. -/
theorem maximalFor_ne_exists_iff :
    MaximalFor A (· ≠ .exists) τ ↔ A τ ∧ (τ ≠ .exists ∨ ∀ σ, A σ → σ = .exists) := by
  simp [maximalFor_prop_iff]

instance [DecidablePred A] : DecidablePred (MaximalFor A (· = CovertShift.down)) := fun _ ↦
  decidable_of_iff _ maximalFor_eq_down_iff.symm

instance [DecidablePred A] : DecidablePred (MaximalFor A (· ≠ CovertShift.exists)) := fun _ ↦
  decidable_of_iff _ maximalFor_ne_exists_iff.symm

open Determiner.Inventory

variable {ds : Determiner.Inventory} {num : Number} {down : Prop}

/-- Under Dayal's ranking ∩ applies wherever it is defined, since no determiner blocks it. -/
@[simp] theorem maximalFor_available_ne_exists_down :
    MaximalFor (ds.Available num down) (· ≠ .exists) .down ↔ down := by
  simp [maximalFor_ne_exists_iff, Available, not_blocks_down]

@[simp] theorem maximalFor_available_ne_exists_iota :
    MaximalFor (ds.Available num down) (· ≠ .exists) .iota ↔ ¬ ds.Blocks num .iota := by
  simp [maximalFor_ne_exists_iff, Available]

@[simp] theorem maximalFor_available_ne_exists_exists :
    MaximalFor (ds.Available num down) (· ≠ .exists) .exists ↔
      ¬ ds.Blocks num .exists ∧ ¬ down ∧ ds.Blocks num .iota ∧ ds.Blocks num .iotaAnaphoric := by
  simp only [maximalFor_ne_exists_iff, Available, ne_eq, not_true_eq_false, false_or]
  refine ⟨fun ⟨⟨_, h⟩, h'⟩ ↦ ⟨h, fun hd ↦ ?_, not_not.1 fun hι ↦ ?_, not_not.1 fun hx ↦ ?_⟩,
    fun ⟨h, hd, hι, hx⟩ ↦ ⟨⟨nofun, h⟩, fun σ ⟨hσ, hb⟩ ↦ ?_⟩⟩
  · exact absurd (h' .down ⟨fun _ ↦ hd, ds.not_blocks_down num⟩) nofun
  · exact absurd (h' .iota ⟨nofun, hι⟩) nofun
  · exact absurd (h' .iotaAnaphoric ⟨nofun, hx⟩) nofun
  · cases σ <;> simp_all

/-- Under Chierchia's ranking, too, ∩ applies wherever it is defined. -/
@[simp] theorem maximalFor_available_eq_down_down :
    MaximalFor (ds.Available num down) (· = .down) .down ↔ down := by
  simp [maximalFor_eq_down_iff, Available, not_blocks_down]

@[simp] theorem maximalFor_available_eq_down_iota :
    MaximalFor (ds.Available num down) (· = .down) .iota ↔ ¬ ds.Blocks num .iota ∧ ¬ down := by
  simp [maximalFor_eq_down_iff, Available, not_blocks_down]

@[simp] theorem maximalFor_available_eq_down_exists :
    MaximalFor (ds.Available num down) (· = .down) .exists ↔ ¬ ds.Blocks num .exists ∧ ¬ down := by
  simp [maximalFor_eq_down_iff, Available, not_blocks_down]

/-- Where the determiners block ι and ι^x, as a definite article used anaphorically does, the two
rankings select the same shifts. -/
theorem maximalFor_available_eq_down_iff_ne_exists (hι : ds.Blocks num .iota)
    (hx : ds.Blocks num .iotaAnaphoric) :
    MaximalFor (ds.Available num down) (· = .down) τ ↔
      MaximalFor (ds.Available num down) (· ≠ .exists) τ := by
  cases τ
  case iotaAnaphoric =>
    simp [maximalFor_eq_down_iff, maximalFor_ne_exists_iff, Available, hx]
  all_goals simp [hι, hx]

end Genericity.CovertShift
