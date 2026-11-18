module

public import Linglib.Core.Logic.Function.DependsOn
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Agreement.Hierarchy

/-!
# Agreement targets

An agreement target is an element whose form agreement determines. A cell of its paradigm gives
each dimension a value a language distinguishes, so the form is a function of several variables,
and the target inflects for a dimension when the dimension is an essential variable of that
function: [changing that value alone changes the form
somewhere](##Agreement.Target.mem_inflection_iff). The inflection is [the least set of dimensions
the form depends on](##Agreement.Target.isLeast_inflection), and a target whose forms distinguish
no more cells than another's [inflects for no
more](##Agreement.Target.inflection_subset_of_factorsThrough). What a target agrees in is thus
read off its forms, and the targets of one language may differ in it, as the two tenses of the
Russian verb do.

## Implementation notes

The inflection is a finset, certified against the form by `mem_inflection`, so that it can be
computed with, as the support of a `Finsupp` is certified by `Finsupp.mem_support_toFun`. It
carries no information: a target [is its positions and its form](##Agreement.Target.ext).

## References

* [corbett-1998]
* [corbett-2006]
-/

@[expose] public section

open Function

namespace Agreement

/-- An agreement target over the values `V d` of each dimension `d` records the positions of the
Agreement Hierarchy at which it occurs, its form in each cell, and the dimensions it inflects for,
the essential variables of its form. -/
structure Target (V : Dimension → Type*) (F : Type*) where
  /-- The positions of the Agreement Hierarchy at which the target occurs. -/
  positions : Finset Position
  /-- The form of the target in each cell. -/
  form : (Π d, V d) → F
  /-- The dimensions the target inflects for. -/
  inflection : Finset Dimension
  /-- The target inflects for a dimension exactly when its form does not ignore it. -/
  mem_inflection : ∀ d, d ∈ inflection ↔ d ∈ essentialVars form

namespace Target

variable {V : Dimension → Type*} {F F' : Type*}

/-- The target with the given positions and form that inflects for `s`, given that the form
depends on `s` and that each dimension of `s` changes it somewhere. -/
@[simps]
def ofDependsOn (positions : Finset Position) (form : (Π d, V d) → F) (s : Finset Dimension)
    (h : DependsOn form s) (hs : ∀ d ∈ s, ∃ x a, form (update x d a) ≠ form x) :
    Target V F where
  positions := positions
  form := form
  inflection := s
  mem_inflection _ :=
    ⟨fun hd ↦ mem_essentialVars_iff_exists_update.2 (hs _ hd), fun hd ↦ h.essentialVars_subset hd⟩

variable (t : Target V F)

@[simp, norm_cast]
theorem coe_inflection : (t.inflection : Set Dimension) = essentialVars t.form :=
  Set.ext t.mem_inflection

/-- A target is its positions and its form. -/
@[ext]
theorem ext {t u : Target V F} (hp : t.positions = u.positions) (hf : t.form = u.form) :
    t = u := by
  obtain ⟨p, f, s, hs⟩ := t
  obtain ⟨p', f', s', hs'⟩ := u
  obtain rfl : p = p' := hp
  obtain rfl : f = f' := hf
  obtain rfl : s = s' := Finset.ext fun d ↦ (hs d).trans (hs' d).symm
  rfl

/-- The inflection is the least set of dimensions the form depends on. -/
theorem isLeast_inflection : IsLeast {s | DependsOn t.form s} t.inflection :=
  t.coe_inflection ▸ isLeast_dependsOn_of_finite t.form

theorem dependsOn_inflection : DependsOn t.form t.inflection :=
  t.isLeast_inflection.1

theorem dependsOn_form_iff {s : Set Dimension} : DependsOn t.form s ↔ ↑t.inflection ⊆ s :=
  t.coe_inflection ▸ dependsOn_iff_essentialVars_subset

/-- A target inflects for a dimension when two cells differing there alone take different
forms. -/
theorem mem_inflection_iff {d : Dimension} :
    d ∈ t.inflection ↔ ∃ x a, t.form (update x d a) ≠ t.form x :=
  (t.mem_inflection d).trans mem_essentialVars_iff_exists_update

variable {t} in
/-- A target whose forms distinguish only cells that another's distinguish inflects for no
dimension the other does not. -/
theorem inflection_subset_of_factorsThrough {u : Target V F'}
    (h : FactorsThrough t.form u.form) : t.inflection ⊆ u.inflection :=
  Finset.coe_subset.1 <| by simpa using h.essentialVars_subset

end Target

end Agreement
