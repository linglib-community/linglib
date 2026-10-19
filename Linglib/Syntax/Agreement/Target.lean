module

public import Linglib.Core.Logic.Function.DependsOn
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Agreement.Hierarchy

/-!
# Agreement targets

An agreement target is an element whose form agreement determines. This file records a target
by the positions of the Agreement Hierarchy at which it occurs, its form in each cell of a
paradigm, and the dimensions it inflects for.

A cell gives each dimension a value a language distinguishes, so a target's form is a function
on a product, and the target inflects for a dimension when that function does not ignore it:
changing that value alone changes the form somewhere. These dimensions are the least set the
form depends on, so what a target agrees in is read off its forms, and the targets of one
language may differ in it, as Corbett shows of the Upper Sorbian finite verb and participle.

## Main definitions

* `Agreement.Target`: an agreement target.
* `Agreement.Target.ofDependsOn`: the target whose form depends on a set of dimensions each of
  which changes the form somewhere.

## Main results

* `Agreement.Target.isLeast_inflection`: the inflection is the least set the form depends on.
* `Agreement.Target.mem_inflection_iff`: a target inflects for a dimension when two cells
  differing there alone take different forms.

## Implementation notes

The inflection is a finset, certified against the form by `mem_inflection`, so that it can be
computed with, as `Fintype.elems` is certified by `Fintype.complete`.

## References

* [corbett-1998]
* [corbett-2006]
-/

@[expose] public section

open Function

namespace Agreement

/-- An agreement target over the values `V d` of each dimension `d` records the positions of the
Agreement Hierarchy at which it occurs, its form in each cell, and the dimensions it inflects for,
those its form does not ignore. -/
structure Target (V : Dimension → Type*) (F : Type*) where
  /-- The positions of the Agreement Hierarchy at which the target occurs. -/
  positions : Finset Position
  /-- The form of the target in each cell. -/
  form : (Π d, V d) → F
  /-- The dimensions the target inflects for. -/
  inflection : Finset Dimension
  /-- The target inflects for a dimension exactly when its form does not ignore it. -/
  mem_inflection : ∀ d, d ∈ inflection ↔ ¬ DependsOn form {d}ᶜ

namespace Target

variable {V : Dimension → Type*} {F : Type*}

/-- The target with the given positions and form that inflects for `s`, given that the form
depends on `s` and that each dimension of `s` changes it somewhere. -/
def ofDependsOn (positions : Finset Position) (form : (Π d, V d) → F) (s : Finset Dimension)
    (h : DependsOn form s) (hs : ∀ d ∈ s, ∃ x a, form (update x d a) ≠ form x) :
    Target V F where
  positions := positions
  form := form
  inflection := s
  mem_inflection d := by
    rw [dependsOn_compl_singleton_iff]
    refine ⟨fun hd h' ↦ ?_, fun hd ↦ by_contra fun hds ↦ hd ?_⟩
    · obtain ⟨x, a, hx⟩ := hs d hd
      exact hx (h' x a)
    · exact dependsOn_compl_singleton_iff.1 (h.mono (Set.subset_compl_singleton_iff.2 hds))

variable (t : Target V F)

/-- The inflection is the set of dimensions the form does not ignore. -/
theorem coe_inflection : (t.inflection : Set Dimension) = {d | ¬ DependsOn t.form {d}ᶜ} :=
  Set.ext t.mem_inflection

/-- The inflection is the least set of dimensions the form depends on. -/
theorem isLeast_inflection : IsLeast {s | DependsOn t.form s} t.inflection :=
  t.coe_inflection ▸ isLeast_dependsOn_of_finite t.form

/-- The form depends on the dimensions the target inflects for. -/
theorem dependsOn_inflection : DependsOn t.form t.inflection :=
  t.isLeast_inflection.1

/-- The form depends on a set of dimensions exactly when it contains the inflection. -/
theorem dependsOn_form_iff {s : Set Dimension} : DependsOn t.form s ↔ ↑t.inflection ⊆ s :=
  ⟨fun h ↦ t.isLeast_inflection.2 h, t.dependsOn_inflection.mono⟩

/-- A target inflects for a dimension when two cells differing there alone take different
forms. -/
theorem mem_inflection_iff {d : Dimension} :
    d ∈ t.inflection ↔ ∃ x a, t.form (update x d a) ≠ t.form x := by
  simp [t.mem_inflection, dependsOn_compl_singleton_iff]

end Target

end Agreement
