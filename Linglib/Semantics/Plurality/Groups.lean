module

public import Mathlib.Data.Finset.Sum
public import Linglib.Semantics.Plurality.Algebra

/-!
# Groups

This file defines Landman's domain with groups on a join semilattice `E` of individuals or
events. Its atoms are sorted into individuals and groups. Group formation `up` sends a sum of two
or more individuals to a group and an individual to itself, and membership specification `down`
sends an atom to the sum of its members, recovering the sum a group was formed from.

## Main definitions

* `Plurality.GroupStructure E`: a domain with groups, its individual atoms, group formation `up`
  and membership specification `down`.
* `Plurality.GroupStructure.sums`, `Plurality.GroupStructure.groups`: the sums of individuals and
  the atoms that are not individuals.
* `Plurality.GroupStructure.finsetModel ι`: the model on finite sets of individuals and groups.

## Main results

* `Plurality.GroupStructure.injOn_up`, `Plurality.GroupStructure.surjOn_down`,
  `Plurality.GroupStructure.down_eq_self`: group formation is one-one, and membership
  specification is onto and fixes the individuals. Landman states these as conditions; they
  follow from the others.
* `Plurality.infinite_of_injective_atom`: iterated group formation has no finite models.

## Implementation notes

* `up` and `down` are total, with their laws stated on Landman's domains of the two operations,
  the sums of individuals for `up` and the atoms for `down`. Sums are finite.
* The definition is Landman's of 2000. His group formation of 1989 applies to every element,
  groups and mixed sums included, and forms a new group even from an individual, so it maps the
  whole domain one-one into its atoms and the domain is infinite (`infinite_of_injective_atom`).
  The 2000 definition forms groups from sums of individuals only and lets an individual form
  itself, so its domains can be finite (`finsetModel`).

## References

* [F. Landman, *Groups, I* (1989)][landman-1989]
* [F. Landman, *Events and plurality* (2000)][landman-2000]
-/

@[expose] public section

namespace Plurality

open Mereology

variable {E : Type*} [SemilatticeSup E]

/-- Landman's domain with groups ([landman-2000], p. 100): individual atoms, group formation `up`
and membership specification `down`. -/
structure GroupStructure (E : Type*) [SemilatticeSup E] where
  /-- The individual atoms. -/
  individuals : Set E
  /-- Group formation. -/
  up : E → E
  /-- Membership specification. -/
  down : E → E
  /-- An individual is an atom. -/
  atom_of_mem ⦃a : E⦄ : a ∈ individuals → Atom a
  /-- A sum of two or more individuals forms a group, an atom that is not an individual. -/
  mapsTo_up : Set.MapsTo up (supClosure individuals \ individuals) ({a | Atom a} \ individuals)
  /-- An individual forms itself. -/
  eqOn_up : Set.EqOn up id individuals
  /-- The members of an atom are a sum of individuals. -/
  mapsTo_down : Set.MapsTo down {a | Atom a} (supClosure individuals)
  /-- The members of a group are the sum it is formed from. -/
  leftInvOn : Set.LeftInvOn down up (supClosure individuals)

namespace GroupStructure

variable (G : GroupStructure E) {a x : E}

/-- The sums of individuals. -/
def sums : Set E := supClosure G.individuals

/-- The groups are the atoms that are not individuals. -/
def groups : Set E := {a | Atom a} \ G.individuals

theorem subset_sums : G.individuals ⊆ G.sums := subset_supClosure

theorem supClosed_sums : SupClosed G.sums := supClosed_supClosure

theorem sup_mem_sums {b : E} (ha : a ∈ G.individuals) (hb : b ∈ G.individuals) :
    a ⊔ b ∈ G.sums :=
  sup_mem_supClosure ha hb

theorem up_eq_self (ha : a ∈ G.individuals) : G.up a = a := G.eqOn_up ha

theorem down_up (hx : x ∈ G.sums) : G.down (G.up x) = x := G.leftInvOn hx

theorem up_mem_groups (hx : x ∈ G.sums) (hx' : x ∉ G.individuals) : G.up x ∈ G.groups :=
  G.mapsTo_up ⟨hx, hx'⟩

theorem atom_up (hx : x ∈ G.sums) : Atom (G.up x) := by
  by_cases hx' : x ∈ G.individuals
  · rw [G.up_eq_self hx']
    exact G.atom_of_mem hx'
  · exact (G.up_mem_groups hx hx').1

theorem injOn_up : Set.InjOn G.up G.sums := G.leftInvOn.injOn

theorem surjOn_down : Set.SurjOn G.down {a | Atom a} G.sums :=
  G.leftInvOn.surjOn fun _ ↦ G.atom_up

theorem down_eq_self (ha : a ∈ G.individuals) : G.down a = a := by
  simpa only [G.up_eq_self ha] using G.down_up (G.subset_sums ha)

/-! ### A model

Finite sets of individuals and groups under union, with a group for each set of two or more
individuals. [landman-2000]'s example (p. 101) is the model on three individuals, with four
groups and seven atoms. -/

section Model

variable {ι β : Type*} {u : Finset (ι ⊕ β)}

private theorem toLeft_singleton_inl (i : ι) : ({.inl i} : Finset (ι ⊕ β)).toLeft = {i} := by
  ext; simp

private theorem toLeft_singleton_inr (b : β) : ({.inr b} : Finset (ι ⊕ β)).toLeft = ∅ := by
  ext; simp

private theorem toRight_singleton_inr (b : β) : ({.inr b} : Finset (ι ⊕ β)).toRight = {b} := by
  ext; simp

private theorem toRight_map_inl (s : Finset ι) : (s.map .inl : Finset (ι ⊕ β)).toRight = ∅ := by
  ext; simp

private theorem map_inl_toLeft (h : u.toRight = ∅) : u.toLeft.map .inl = u := by
  rw [← Finset.disjSum_empty, ← h, Finset.toLeft_disjSum_toRight]

variable [DecidableEq ι] [DecidableEq β]

private theorem mem_supClosure_iff :
    u ∈ supClosure (Set.range fun i ↦ ({.inl i} : Finset (ι ⊕ β))) ↔
      u.Nonempty ∧ u.toRight = ∅ := by
  have h : u ∈ supClosure (({·} : ι ⊕ β → Finset (ι ⊕ β)) '' Set.range .inl) ↔ _ :=
    (Set.ext_iff.1 (setOf_algClosure _) u).symm.trans
      (algClosure_image_singleton (Set.range (Sum.inl : ι → ι ⊕ β)) u)
  rw [← Set.range_comp] at h
  refine h.trans (and_congr_right fun _ ↦ ?_)
  simp [Set.subset_def, Finset.eq_empty_iff_forall_notMem]

variable (ι)

/-- The model: the individuals are the singletons of `ι`, a set of two or more individuals forms
the group it indexes, and the members of an element are its individuals and their groups'
members. -/
def finsetModel : GroupStructure (Finset (ι ⊕ {s : Finset ι // s.Nontrivial})) where
  individuals := Set.range fun i ↦ {.inl i}
  up x := if h : x.toLeft.Nontrivial then {.inr ⟨x.toLeft, h⟩} else x
  down x := (x.toLeft ∪ x.toRight.biUnion (↑)).map .inl
  atom_of_mem := by
    rintro _ ⟨i, rfl⟩
    exact atom_iff_isAtom.2 (Finset.isAtom_singleton _)
  mapsTo_up x hx := by
    obtain ⟨hne, hr⟩ := mem_supClosure_iff.1 hx.1
    have hN : x.toLeft.Nontrivial := by
      rw [← map_inl_toLeft hr, Finset.map_nonempty] at hne
      refine hne.exists_eq_singleton_or_nontrivial.resolve_left ?_
      rintro ⟨i, hi⟩
      exact hx.2 ⟨i, by rw [← map_inl_toLeft hr, hi, Finset.map_singleton]; rfl⟩
    simp only [hN, ↓reduceDIte]
    refine ⟨atom_iff_isAtom.2 (Finset.isAtom_singleton _), ?_⟩
    rintro ⟨i, hi⟩
    simp at hi
  eqOn_up := by
    rintro _ ⟨i, rfl⟩
    simp [toLeft_singleton_inl]
  mapsTo_down a ha := by
    obtain ⟨z, rfl⟩ := Finset.isAtom_iff.1 (atom_iff_isAtom.1 ha)
    refine mem_supClosure_iff.2 ?_
    rcases z with i | g
    · simp [toLeft_singleton_inl, toRight_map_inl]
    · simpa [toLeft_singleton_inr, toRight_singleton_inr, toRight_map_inl] using g.2.nonempty
  leftInvOn x hx := by
    have hr := (mem_supClosure_iff.1 hx).2
    by_cases h : x.toLeft.Nontrivial
    · simp [h, toLeft_singleton_inr, toRight_singleton_inr, map_inl_toLeft hr]
    · simp [h, hr, map_inl_toLeft hr]

end Model

example : Fintype.card (Fin 3 ⊕ {s : Finset (Fin 3) // s.Nontrivial}) = 7 := by
  decide

end GroupStructure

/-- A domain mapped one-one into its own atoms, as by iterated group formation, has no finite
models ([landman-1989], p. 580). -/
theorem infinite_of_injective_atom [Nonempty E] {f : E → E} (hf : Function.Injective f)
    (h : ∀ x, Atom (f x)) : Infinite E := by
  by_contra hfin
  have : Finite E := not_infinite_iff_finite.1 hfin
  have hall (x : E) : Atom x :=
    let ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hf x
    hy ▸ h y
  obtain ⟨x⟩ := ‹Nonempty E›
  refine (hall x).not_isBot fun y ↦ (?_ : x = y).le
  exact ((hall _).eq le_sup_left (hall x).not_isBot).trans
    ((hall _).eq le_sup_right (hall y).not_isBot).symm

end Plurality
