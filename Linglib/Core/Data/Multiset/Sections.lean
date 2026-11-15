/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Multiset.Sections

/-!
# Sections of a mapped family of multisets

Mapping every multiset of a family maps every section of the family: `Multiset.Sections` commutes
with `Multiset.map`. An `[UPSTREAM]` candidate; eventual mathlib home
`Mathlib.Data.Multiset.Sections`.
-/

public section

namespace Multiset

variable {α β : Type*}

theorem sections_map (f : α → β) (s : Multiset (Multiset α)) :
    (s.map (map f)).Sections = s.Sections.map (map f) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons m s ih =>
    simp only [map_cons, sections_cons, ih, bind_map, map_bind, map_map, Function.comp_def]

end Multiset
