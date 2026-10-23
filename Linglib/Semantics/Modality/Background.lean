module

public import Linglib.Core.Order.Minimals
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# Conversational backgrounds

A premise set is a set of propositions `A : Set (W → Prop)`. In the complete Boolean algebra
`W → Prop` its infimum `sInf A` holds at the worlds verifying every premise, so `p` follows from
`A` when `sInf A ≤ p`, and `A` is consistent when `sInf A ≠ ⊥`. A premise set also ranks worlds:
`w` is at least as good as `z` when `w` verifies every premise `z` does, a preorder that is in
general not total, whose minimal elements in a domain are its best worlds.

A conversational background assigns each world a premise set. Kratzer's modal base and ordering
source are both conversational backgrounds, told apart only by their role: the premises of a
modal base at `w` fix the worlds accessible from `w`, and those of an ordering source rank them.

## Main definitions

* `Background W`: the backgrounds over `W`, a complete lattice pointwise, with `⊥` the empty
  background.
* `Background.accessibleWorlds f w`: the worlds verifying every premise of `f w`.
* `Background.IsRealistic`, `Background.IsTotallyRealistic`.
* `Background.restrict f α`: `f` with the premise `α` added at every world.
* `premisePreorder A`, `w ≤[A] z`, `w <[A] z`: the ordering a premise set induces.
* `bestWorlds f g w`: the minimal worlds accessible under `f` ranked by `g`.

## Implementation notes

* `w ≤[A] z` and `w <[A] z` are notation for the order of `premisePreorder A`. A `DecidableRel`
  instance on that order would be keyed on every `≤`-goal downstream, so a study that decides a
  premise ordering supplies a local instance for its own ordering source.

## References

* [kratzer-1977]
* [kratzer-1981]
* [kratzer-2012]
-/

@[expose] public section

namespace Modality

variable {W : Type*}

/-- A conversational background assigns each world a premise set. -/
abbrev Background (W : Type*) := W → Set (W → Prop)

namespace Background

variable {f f' : Background W} {w v : W}

/-- The worlds accessible from `w` under `f` are those verifying every premise of `f w`,
Kratzer's `⋂f(w)`. -/
def accessibleWorlds (f : Background W) (w : W) : Set W := {v | sInf (f w) v}

@[simp] theorem mem_accessibleWorlds : v ∈ f.accessibleWorlds w ↔ ∀ p ∈ f w, p v := by
  simp [accessibleWorlds]

theorem accessibleWorlds_anti (h : f w ⊆ f' w) : f'.accessibleWorlds w ⊆ f.accessibleWorlds w :=
  fun v hv ↦ sInf_le_sInf h v hv

@[simp] theorem accessibleWorlds_bot (w : W) : (⊥ : Background W).accessibleWorlds w = .univ :=
  Set.eq_univ_of_forall fun _ ↦ by simp [accessibleWorlds]

theorem accessibleWorlds_sup (f g : Background W) (w : W) :
    (f ⊔ g).accessibleWorlds w = {v ∈ f.accessibleWorlds w | ∀ p ∈ g w, p v} := by
  ext v
  simp [or_imp, forall_and]

/-- A background is realistic when every world is accessible from itself, verifying its own
premises. -/
def IsRealistic (f : Background W) : Prop := ∀ w, w ∈ f.accessibleWorlds w

/-- A background is totally realistic when its premises at a world single out that world. -/
def IsTotallyRealistic (f : Background W) : Prop := ∀ w, f.accessibleWorlds w = {w}

/-- The background `f` restricted by `α`, the premise a conditional antecedent adds, so that
*if α, must β* is `must_{f + α} β`. -/
def restrict (f : Background W) (α : W → Prop) : Background W := fun w ↦ insert α (f w)

@[simp] theorem mem_accessibleWorlds_restrict {α : W → Prop} :
    v ∈ (f.restrict α).accessibleWorlds w ↔ v ∈ f.accessibleWorlds w ∧ α v := by
  simp [restrict, and_comm]

theorem accessibleWorlds_restrict (f : Background W) (α : W → Prop) (w : W) :
    (f.restrict α).accessibleWorlds w = {v ∈ f.accessibleWorlds w | α v} :=
  Set.ext fun _ ↦ mem_accessibleWorlds_restrict

/-- A stronger antecedent leaves fewer accessible worlds. -/
theorem accessibleWorlds_restrict_mono {α₁ α₂ : W → Prop} (h : α₂ ≤ α₁) :
    (f.restrict α₂).accessibleWorlds w ⊆ (f.restrict α₁).accessibleWorlds w := fun v hv ↦
  mem_accessibleWorlds_restrict.2 ⟨(mem_accessibleWorlds_restrict.1 hv).1,
    h v (mem_accessibleWorlds_restrict.1 hv).2⟩

end Background

/-! ### The ordering -/

/-- The preorder that an ordering source induces ranks `w` below `z` when every proposition of `A`
true at `z` is true at `w`. It is the criteria-derived preorder with truth as satisfaction. -/
abbrev premisePreorder (A : Set (W → Prop)) : Preorder W :=
  Preorder.ofCriteria (fun w p ↦ p w) A

/-- `w ≤[A] z` says that `w` is at least as good as `z` under the ordering source `A`, verifying
every premise of `A` that `z` verifies. -/
notation:50 w " ≤[" A "] " z => @LE.le _ (@Preorder.toLE _ (premisePreorder A)) w z

/-- `w <[A] z` says that `w` is strictly better than `z` under the ordering source `A`. -/
notation:50 w " <[" A "] " z => @LT.lt _ (@Preorder.toLT _ (premisePreorder A)) w z

/-! ### Best worlds -/

/-- The best accessible worlds from `w` are the minimal accessible worlds under the ordering
source at `w`, the members that no other member strictly betters. The dominance form, at least as
good as every member, is empty on an ordering that is not total, such as Kratzer's
practical-inference example, so minimality is the faithful reading. Kratzer's official necessity
is the limit-free `humanNecessity`, which quantifies over exactly this set under the Limit
Assumption (`humanNecessity_iff_necessity`). -/
def bestWorlds (f g : Background W) (w : W) : Set W :=
  (premisePreorder (g w)).minimals (f.accessibleWorlds w)

theorem mem_bestWorlds {f g : Background W} {w u : W} :
    u ∈ bestWorlds f g w ↔
      u ∈ f.accessibleWorlds w ∧ ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → (u ≤[g w] v) :=
  Iff.rfl

@[simp] theorem bestWorlds_bot (f : Background W) (w : W) :
    bestWorlds f ⊥ w = f.accessibleWorlds w := by
  simp [bestWorlds]

theorem bestWorlds_eq_accessibleWorlds_sup {f g : Background W} {w : W}
    (h : ((f ⊔ g).accessibleWorlds w).Nonempty) :
    bestWorlds f g w = (f ⊔ g).accessibleWorlds w := by
  rw [Background.accessibleWorlds_sup] at h ⊢
  exact Preorder.minimals_ofCriteria_eq h

theorem mem_bestWorlds_insert {f g : Background W} {p q : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u) :
    u ∈ bestWorlds f (fun v ↦ insert p (g v)) w := by
  refine ⟨hu.1, fun v hv hvu ↦ ?_⟩
  have hvq : q v := hvu q (Set.mem_insert_of_mem p hq) huq
  intro r hr
  rcases hr with rfl | hr
  · exact fun hrv ↦ absurd hrv (hpq v hvq)
  · exact hu.2 hv (fun r' hr' ↦ hvu r' (Set.mem_insert_of_mem p hr')) r hr

theorem mem_bestWorlds_of_subset {f f' g : Background W} {w u : W}
    (h : f'.accessibleWorlds w ⊆ f.accessibleWorlds w) (hu : u ∈ bestWorlds f g w)
    (hu' : u ∈ f'.accessibleWorlds w) : u ∈ bestWorlds f' g w :=
  Preorder.mem_minimals_of_subset h hu hu'

end Modality
