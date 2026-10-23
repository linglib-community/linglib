/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Composition.WithAlternatives
public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype

/-!
# Focus marking

A focus indicates the presence of alternatives that are relevant to interpretation, Krifka's
definition of the notion after Rooth's alternative semantics. A constituent is F-marked or
unfeatured (`Focus.Mark`). An F-marked constituent keeps its ordinary value and evokes every value
of its type, and an unfeatured one evokes what its parts compose (`WithAlternatives.mark`), so the
two marks are ordered by the alternatives they evoke, unfeatured below F-marked. Where a language
realizes a focus is a separate matter, and one cut is whether the focused constituent stays in
its base position or is fronted (`Focus.Strategy`).

## Main definitions

* `Focus.Mark`: F-marked or unfeatured, a two-element linear order.
* `WithAlternatives.mark`: the meaning of a constituent bearing a mark.
* `Focus.Strategy`: a focus realized in place or fronted.

## Main results

* `WithAlternatives.alternatives_mark_subset_alternatives_mark_iff`: unless a constituent already
  evokes its whole type, its alternatives grow exactly along the order of the marks.
* `WithAlternatives.mark_eq_bind`: on a well-formed meaning a mark is a continuation.
* `WithAlternatives.ordinary_eq_of_given_mark_focused_bind`: an F-marked constituent under a
  continuation is Given only if the continuation's ordinary values ignore it.

## References

* [krifka-2008]
* [rooth-1992]
* [hartmann-zimmermann-2007]
-/

@[expose] public section

namespace Focus

/-- A constituent is F-marked or unfeatured. -/
inductive Mark where
  /-- The constituent bears no focus feature. -/
  | unfeatured
  /-- The constituent bears the focus feature. -/
  | focused
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder Mark := LinearOrder.lift' Mark.ctorIdx (by decide)

instance : BoundedOrder Mark where
  top := .focused
  le_top := by decide
  bot := .unfeatured
  bot_le := by decide

instance : IsSimpleOrder Mark where
  exists_pair_ne := ⟨.unfeatured, .focused, by decide⟩
  eq_bot_or_eq_top := by decide

/-- A focused constituent is realized in its base position or fronted to the left periphery of
its clause. -/
inductive Strategy where
  /-- The focus stays in its base position. -/
  | inSitu
  /-- The focus is fronted. -/
  | exSitu
  deriving DecidableEq, Repr, Inhabited

end Focus

namespace WithAlternatives

open Focus (Mark)

variable {α β γ : Type*} {d : WithAlternatives α}

/-- The meaning of a constituent bearing a mark. F-marking keeps the ordinary value and makes
the alternatives the whole type; an unfeatured constituent keeps the alternatives of its parts. -/
def mark (d : WithAlternatives α) : Mark → WithAlternatives α
  | .unfeatured => d
  | .focused => .focused d.ordinary

@[simp] theorem mark_unfeatured (d : WithAlternatives α) : d.mark .unfeatured = d := rfl

@[simp] theorem mark_focused (d : WithAlternatives α) : d.mark .focused = .focused d.ordinary :=
  rfl

@[simp] theorem ordinary_mark (d : WithAlternatives α) (m : Mark) :
    (d.mark m).ordinary = d.ordinary := by
  cases m <;> rfl

theorem WellFormed.mark (hd : d.WellFormed) (m : Mark) : (d.mark m).WellFormed := by
  cases m
  exacts [hd, WellFormed.focused _]

theorem nontrivial_alternatives_mark_focused [Nontrivial α] (d : WithAlternatives α) :
    (d.mark .focused).alternatives.Nontrivial :=
  Set.nontrivial_univ

@[simp] theorem alternatives_map₂_focused_unfeatured (f : α → β → γ) (x : α) (y : β) :
    (map₂ f ((unfeatured x).mark .focused) ((unfeatured y).mark .unfeatured)).alternatives =
      Set.range (f · y) := by
  simp [Set.image2_singleton_right]

@[simp] theorem alternatives_map₂_unfeatured_focused (f : α → β → γ) (x : α) (y : β) :
    (map₂ f ((unfeatured x).mark .unfeatured) ((unfeatured y).mark .focused)).alternatives =
      Set.range (f x) := by
  simp [Set.image2_singleton_left]

theorem alternatives_mark_subset_alternatives_mark_iff (hd : d.alternatives ≠ .univ)
    {m m' : Mark} : (d.mark m).alternatives ⊆ (d.mark m').alternatives ↔ m ≤ m' := by
  cases m <;> cases m' <;> simp [Set.univ_subset_iff, hd] <;> decide

section Bind

universe u

variable {σ τ : Type u}

theorem mark_eq_bind {d : WithAlternatives σ} (hd : d.WellFormed) (m : Mark) :
    d.mark m = d >>= fun a ↦ (pure a : WithAlternatives σ).mark m := by
  cases m
  · exact (bind_pure d).symm
  · refine WithAlternatives.ext rfl (Set.ext fun x ↦ ?_)
    rw [alternatives_bind]
    exact ⟨fun _ ↦ ⟨_, hd, Set.mem_univ x⟩, fun _ ↦ Set.mem_univ x⟩

theorem ordinary_eq_of_given_mark_focused_bind {d : WithAlternatives σ}
    {k : σ → WithAlternatives τ} (hk : ∀ a, (k a).WellFormed) {c : τ}
    (h : (d.mark .focused >>= k).Given c) (a : σ) : (k a).ordinary = c := by
  have : (k a).ordinary ∈ (d.mark .focused >>= k).alternatives := by
    rw [alternatives_bind]
    exact ⟨a, Set.mem_univ a, hk a⟩
  rwa [h] at this

end Bind

end WithAlternatives
