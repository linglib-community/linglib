module

public import Linglib.Core.Order.Minimal
public import Linglib.Semantics.Mereology.Atomic
public import Linglib.Syntax.Feature.Number.Bivalent

/-!
# Number features as region operators

Harbour decomposes grammatical number into three features acting on a region of a
join-semilattice of individuals. `[±atomic]` keeps the region's atoms or the rest, `[±minimal]`
its minimal elements or the rest, and `[±additive]` the elements whose join with any element of a
subregion stays in it. Features compose by application, so the dual is `[+minimal]` applied to
`[−atomic]`, and the trial `[+minimal]` applied to `[−minimal]` applied to `[−atomic]`. Which
bundle a value names depends on the number system: the plural of English is `[−atomic]`, that of
a language with a dual `[−atomic, −minimal]`. The systems a parameter setting generates, and the
cells of their bundles, are computed in `Studies/Harbour2014.lean`.

## Main definitions

* `Number.Feature.restrict`: the region a valued feature selects from a region.
* `Number.additiveIn`: the `[+additive]` elements of a subregion.

## Main results

* `Number.additive_subregion_is_cum`: the `[+additive]` elements form a cumulative region.
* `Number.singular_subset_minimal`: in a region without the null individual an atom is minimal,
  so `[+atomic]` entails `[+minimal]`.
* `Number.atomize_eq_of_atoms`: `[+minimal]` applied to a region of atoms changes nothing.
* `Number.not_restrict_minimal_false_atomize`: `[−minimal]` applied after `[+minimal]` is empty.
* `Number.Feature.restrict_grade_preimage`: in a part structure graded by `ℕ`, a feature acts on
  the individuals of given grades as it acts on the grades.
* `Number.Feature.restrict_inter_of_isLowerSet`: a feature's selection restricts to a lower set.

## Implementation notes

Harbour presupposes that the element lies in the region (`[±minimal]`) and in the subregion
(`[±additive]`); here these are conjuncts. Minimality is mathlib's `Minimal`, exposed as
`Mereology.atomize`. With a null individual in the region an atom has a proper part, so
`[+atomic]` no longer entails `[+minimal]`; Martí's revision of `[±minimal]` for that case, which
counts only parts of nonzero numerosity, is not modelled. `[−atomic]` gives the exclusive plural.
Whether the inclusive reading in downward-entailing contexts is a second meaning or an implicature
is open: Martí argues for the former within Harbour's typology, an inclusive-only plural lacking the
`[−atomic]` that duals and paucals are built on, and the experiments of Tieu, Bill, Romoli and Crain
favour the latter (`Studies/TieuEtAl2020.lean`). `Number.dom` states the inclusive-only reading of
a bundle, and competition recovers these regions from it for the singular and plural alone
(`Number.strengthen_plural`). The operators apply to events as well as individuals.

## References

* [harbour-2014] (9) and (10), p. 195; (20) and (21), p. 202; (30), p. 210
* [marti-2020a]
* [marti-2020b] pp. 3:30–3:31
* [marti-2022] (8) and (9), pp. 217–218; (40), p. 224
* [tieu-etal-2020]
* [link-1983]
-/

@[expose] public section

namespace Number

open Mereology (CUM atomize atomize_subset)

variable {D : Type*}

section Additive

variable [SemilatticeSup D] {Q : Set D} {x y : D}

/-- `x` is additive in the region `Q` if it lies in `Q` and so does `x ⊔ y` for every `y` in `Q`,
Harbour's `[+additive]`. -/
def additiveIn (Q : Set D) : Set D := {x | x ∈ Q ∧ ∀ y ∈ Q, x ⊔ y ∈ Q}

@[simp] theorem mem_additiveIn : x ∈ additiveIn Q ↔ x ∈ Q ∧ ∀ y ∈ Q, x ⊔ y ∈ Q := Iff.rfl

theorem additiveIn_subset (Q : Set D) : additiveIn Q ⊆ Q := fun _ h ↦ h.1

theorem additiveIn_sup (hx : x ∈ additiveIn Q) (hy : y ∈ additiveIn Q) :
    x ⊔ y ∈ additiveIn Q := by
  refine ⟨hx.2 y hy.1, fun z hz ↦ ?_⟩
  rw [sup_assoc]
  exact hx.2 (y ⊔ z) (hy.2 z hz)

/-- The additive elements of a region form a cumulative region. -/
theorem additive_subregion_is_cum (Q : Set D) : CUM (additiveIn Q) :=
  fun _ hx _ hy ↦ additiveIn_sup hx hy

instance [Fintype D] [DecidablePred (· ∈ Q)] : DecidablePred (· ∈ additiveIn Q) := fun x ↦
  decidable_of_iff (x ∈ Q ∧ ∀ y ∈ Q, x ⊔ y ∈ Q) Iff.rfl

end Additive

variable [PartialOrder D] [OrderBot D] {P : Set D} {x : D}

/-- The region a valued feature selects from the region `P`: `[+atomic]` its atoms and
`[−atomic]` the rest, `[+minimal]` its minimal elements and `[−minimal]` the rest. `[±additive]`
cuts a region at a height the region does not fix, and leaves it. -/
def Feature.restrict : Feature → Bool → Set D → Set D
  | .atomic, true, P => P ∩ {x | IsAtom x}
  | .atomic, false, P => P \ {x | IsAtom x}
  | .minimal, true, P => atomize P
  | .minimal, false, P => P \ atomize P
  | .additive, _, P => P

@[simp] theorem Feature.mem_restrict_atomic_true :
    x ∈ Feature.restrict .atomic true P ↔ x ∈ P ∧ IsAtom x := Iff.rfl

@[simp] theorem Feature.mem_restrict_atomic_false :
    x ∈ Feature.restrict .atomic false P ↔ x ∈ P ∧ ¬ IsAtom x := Iff.rfl

@[simp] theorem Feature.restrict_minimal_true (P : Set D) :
    Feature.restrict .minimal true P = atomize P := rfl

@[simp] theorem Feature.mem_restrict_minimal_false :
    x ∈ Feature.restrict .minimal false P ↔ x ∈ P ∧ x ∉ atomize P := Iff.rfl

@[simp] theorem Feature.restrict_additive (v : Bool) (P : Set D) :
    Feature.restrict .additive v P = P := rfl

theorem Feature.restrict_le (f : Feature) (v : Bool) (P : Set D) : f.restrict v P ⊆ P :=
  match f, v with
  | .atomic, true => Set.inter_subset_left
  | .atomic, false | .minimal, false => Set.sdiff_subset
  | .minimal, true => atomize_subset P
  | .additive, _ => subset_rfl

/-- The minimal elements of a region of minimal elements are all of them, so
`(−minimal(+minimal(P)))` is empty. -/
theorem not_restrict_minimal_false_atomize (P : Set D) (x : D) :
    x ∉ Feature.restrict .minimal false (atomize P) :=
  fun h ↦ h.2 ⟨h.1, fun _ hy hyx ↦ h.1.2 hy.1 hyx⟩

/-- An atom of a region excluding the null individual is minimal in it, so
`[+atomic]` entails `[+minimal]`. -/
theorem singular_subset_minimal (hP : ∀ y ∈ P, y ≠ ⊥)
    (hx : x ∈ Feature.restrict .atomic true P) : x ∈ atomize P :=
  ⟨hx.1, fun _ hy hle ↦ ((hx.2.le_iff_eq (hP _ hy)).1 hle).ge⟩

/-- Over a region of atoms `[+minimal]` selects everything, so `(+minimal(+atomic(P)))` is
`(+atomic(P))`, the singular. -/
theorem atomize_eq_of_atoms (hAll : ∀ x ∈ P, IsAtom x) : atomize P = P :=
  (atomize_subset P).antisymm fun x hPx ↦
    singular_subset_minimal (fun y hy ↦ (hAll y hy).1) ⟨hPx, hAll x hPx⟩

/-! ### Regions of numerosities

In a part structure graded by `ℕ` the features act on the regions cut out by sets of grades as
they act on the sets of grades. -/

section Grade

variable [GradeMinOrder ℕ D]

omit [OrderBot D] in
theorem atomize_grade_preimage (S : Set ℕ) :
    atomize (grade ℕ ⁻¹' S : Set D) = grade ℕ ⁻¹' atomize S :=
  Set.ext fun _ ↦ minimal_comp_iff_of_strictMono grade_strictMono fun _ _ ↦ exists_le_grade_eq

/-- The region a valued feature selects from the individuals of the grades `S` is that of the
grades it selects from `S`. -/
theorem Feature.restrict_grade_preimage (f : Feature) (v : Bool) (S : Set ℕ) :
    f.restrict v (grade ℕ ⁻¹' S : Set D) = grade ℕ ⁻¹' f.restrict v S := by
  match f, v with
  | .atomic, true => ext x; simp [isAtom_grade_iff]
  | .atomic, false => ext x; simp [isAtom_grade_iff]
  | .minimal, true => exact atomize_grade_preimage S
  | .minimal, false =>
    ext x
    simp only [Feature.mem_restrict_minimal_false, atomize_grade_preimage, Set.mem_preimage]
  | .additive, _ => rfl

end Grade

/-- A valued feature selects from the part of a region inside a lower set the part of its
selection inside that set. -/
theorem Feature.restrict_inter_of_isLowerSet (f : Feature) (v : Bool) (P : Set D) {L : Set D}
    (hL : IsLowerSet L) : f.restrict v (P ∩ L) = f.restrict v P ∩ L := by
  have key : atomize (P ∩ L) = atomize P ∩ L := Set.ext fun x ↦
    ⟨fun h ↦ ⟨⟨h.1.1, fun y hy hyx ↦ h.2 ⟨hy, hL hyx h.1.2⟩ hyx⟩, h.1.2⟩,
      fun h ↦ ⟨⟨h.1.1, h.2⟩, fun y hy hyx ↦ h.1.2 hy.1 hyx⟩⟩
  match f, v with
  | .atomic, true => ext x; simp only [mem_restrict_atomic_true, Set.mem_inter_iff]; tauto
  | .atomic, false => ext x; simp only [mem_restrict_atomic_false, Set.mem_inter_iff]; tauto
  | .minimal, true => exact key
  | .minimal, false =>
    ext x
    simp only [mem_restrict_minimal_false, key, Set.mem_inter_iff]
    tauto
  | .additive, _ => rfl

end Number
