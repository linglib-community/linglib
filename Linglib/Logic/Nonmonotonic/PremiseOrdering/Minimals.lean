module

public import Linglib.Core.Order.Minimals
public import Linglib.Logic.Nonmonotonic.PremiseOrdering.Defs

/-!
# Minimal points of the ordering a family of sets induces

Under `≤[A]` the minimal points of a set are those in every member of `A`, when some point of
the set is.

## Main results

* `Preorder.minimals_ofLowerSets_eq`: the minimal points are those in every member of `A`, when
  some point is.

## References

* [kratzer-1981]
* [lewis-1981]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Preorder

variable {α : Type*} {A B : Set (Set α)}

/-! ### Minimal points -/

section Minimals

variable {s : Set α}

/-- Under the ordering of `A`, when some element of the set lies in every member of `A`, the
minimal elements are exactly those that do. -/
theorem minimals_ofLowerSets_eq (hex : ∃ a ∈ s, ∀ t ∈ A, a ∈ t) :
    (≤[A]).minimals s = {a ∈ s | ∀ t ∈ A, a ∈ t} :=
  let ⟨_, hb, hsat⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, fun c hc ↦ hmin hb (fun c' hc' _ ↦ hsat c' hc') c hc (hsat c hc)⟩,
      fun ⟨ha, hall⟩ ↦ ⟨ha, fun _ _ _ c hc _ ↦ hall c hc⟩⟩

/-- Under the preorder of a predicate, when some element of the set satisfies the predicate, the
minimal elements are exactly those that do. -/
theorem minimals_ofCriterion {P : α → Prop} (hex : ∃ a ∈ s, P a) :
    (ofCriterion P).minimals s = {a ∈ s | P a} :=
  let ⟨_, hb, hPb⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, hmin hb (fun _ ↦ hPb) hPb⟩, fun ⟨ha, hPa⟩ ↦ ⟨ha, fun _ _ _ _ ↦ hPa⟩⟩

end Minimals

end Preorder
