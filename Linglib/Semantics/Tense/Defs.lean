module

public import Linglib.Core.Order.Compare
public import Linglib.Semantics.Denotation
public import Linglib.Syntax.Category.Verb.Tense
public import Mathlib.Basic.Rel
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.Defs.LinearOrder

/-!
# Grammatical tense

A tense, past, present or future (`Tense`, from `Syntax/Category/Verb/Tense.lean`), denotes a
comparison cell, a `Finset Ordering` of the positions in which a reference time may stand to a
perspective time, so the constraint a tense imposes on times `r` and `p` is
`compare r p ∈ ⟦t⟧`. Following Kiparsky, tense locates the reference time relative to the
perspective time, not the speech time. Cells are the elements of the Boolean algebra
`𝒫 {lt, eq, gt}`, so the derived categories are joins and complements of tense denotations
rather than further tenses: Klecha's nonpast is `⟦present⟧ ⊔ ⟦future⟧`, the nonfuture is
`⟦future⟧ᶜ`, and the unconstrained cell is `⊤`.

Cells compose: `comp R S` collects the positions of `a` to `c` compatible with `a` to `b` in `R`
and `b` to `c` in `S`. A cell is also a relation between times (`toSetRel`), the union of the
relations `<`, `=` and `>` of its positions. The relation is defined on any order, so the past
relates a moment of branching time to the moments below it. On linear time it is the constraint
`compare r p ∈ C`, and the relation of a composed cell contains the composite of the relations,
with equality when time is dense and has no first or last moment.

## Main declarations

* `Tense.denote`: the cell a tense denotes, written `⟦t⟧`.
* `Tense.nonpast`: the cell of the present or future.
* `Tense.comp`: the composition of two cells.
* `Tense.toSetRel`: a cell as a relation between times.

## Main statements

* `Tense.inv_toSetRel`: the converse of a cell's relation is the relation of its mirror image.
* `Tense.toSetRel_comp_subset`, `Tense.toSetRel_comp`: the composite of two cells' relations
  lies in the relation of the composed cell, and is that relation on dense time without
  endpoints.

## References

* [kiparsky-2002]
* [klecha-2016]
-/

@[expose] public section

namespace Tense

open SetRel
open scoped Denotes

/-- A tense denotes the cell of orderings in which the reference time may stand to the perspective
time, before it for the past, at it for the present and after it for the future. -/
def denote : Tense → Finset Ordering
  | past => {.lt}
  | present => {.eq}
  | future => {.gt}

instance : Denotes Tense (Finset Ordering) := ⟨denote⟩

theorem denote_past : ⟦past⟧ = ({.lt} : Finset Ordering) := rfl

theorem denote_present : ⟦present⟧ = ({.eq} : Finset Ordering) := rfl

theorem denote_future : ⟦future⟧ = ({.gt} : Finset Ordering) := rfl

/-- The nonpast is the cell of a reference time at or after the perspective time. -/
def nonpast : Finset Ordering := {.eq, .gt}

theorem nonpast_eq_present_sup_future : nonpast = ⟦present⟧ ⊔ ⟦future⟧ := by decide

theorem nonpast_eq_compl_past : nonpast = ⟦past⟧ᶜ := by decide

theorem past_sup_present : ⟦past⟧ ⊔ ⟦present⟧ = ⟦future⟧ᶜ := by decide

/-- The composition of two cells collects the orderings of `a` to `c` compatible with `a` to
`b` in `R` and `b` to `c` in `S`. -/
def comp (R S : Finset Ordering) : Finset Ordering :=
  R.biUnion fun r ↦ S.biUnion r.comp

theorem mem_comp {R S : Finset Ordering} {o : Ordering} :
    o ∈ comp R S ↔ ∃ r ∈ R, ∃ s ∈ S, o ∈ r.comp s := by
  simp [comp]

theorem comp_sup_left (R R' S : Finset Ordering) : comp (R ⊔ R') S = comp R S ⊔ comp R' S :=
  Finset.union_biUnion ..

theorem comp_sup_right (R S S' : Finset Ordering) : comp R (S ⊔ S') = comp R S ⊔ comp R S' := by
  simp only [comp, Finset.sup_eq_union, Finset.union_biUnion, Finset.biUnion_union]

@[simp] theorem comp_present_left (S : Finset Ordering) : comp ⟦present⟧ S = S := by
  ext o
  simp [mem_comp, Denotes.denote, denote, Ordering.comp]

@[simp] theorem comp_present_right (R : Finset Ordering) : comp R ⟦present⟧ = R := by
  ext o
  simp only [mem_comp, Denotes.denote, denote, Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨r, hr, h⟩
    cases r <;> simp only [Ordering.comp, Finset.mem_singleton] at h <;> exact h ▸ hr
  · exact fun h ↦ ⟨o, h, by cases o <;> simp [Ordering.comp]⟩

@[simp] theorem comp_past_past : comp ⟦past⟧ ⟦past⟧ = ⟦past⟧ := by decide

@[simp] theorem comp_future_future : comp ⟦future⟧ ⟦future⟧ = ⟦future⟧ := by decide

@[simp] theorem comp_past_future : comp ⟦past⟧ ⟦future⟧ = ⊤ := by decide

@[simp] theorem comp_future_past : comp ⟦future⟧ ⟦past⟧ = ⊤ := by decide

@[simp] theorem comp_compl_future_compl_future : comp ⟦future⟧ᶜ ⟦future⟧ᶜ = ⟦future⟧ᶜ := by
  decide

variable {T : Type*} {C D : Finset Ordering} {p r : T}

/-! ### Cells on linear time -/

section LinearOrder

variable [LinearOrder T]

@[simp] theorem compare_mem_past (r p : T) : compare r p ∈ ⟦past⟧ ↔ r < p := by
  simp [Denotes.denote, denote, compare_lt_iff_lt]

@[simp] theorem compare_mem_present (r p : T) : compare r p ∈ ⟦present⟧ ↔ r = p := by
  simp [Denotes.denote, denote]

@[simp] theorem compare_mem_future (r p : T) : compare r p ∈ ⟦future⟧ ↔ p < r := by
  simp [Denotes.denote, denote, compare_gt_iff_gt]

@[simp] theorem compare_mem_nonpast (r p : T) : compare r p ∈ nonpast ↔ p ≤ r := by
  rw [nonpast_eq_compl_past, Finset.mem_compl, compare_mem_past, not_lt]

@[simp] theorem compare_mem_compl_future (r p : T) : compare r p ∈ ⟦future⟧ᶜ ↔ r ≤ p := by
  rw [Finset.mem_compl, compare_mem_future, not_lt]

theorem compare_mem_comp {R S : Finset Ordering} {a b c : T} (h₁ : compare a b ∈ R)
    (h₂ : compare b c ∈ S) : compare a c ∈ comp R S :=
  mem_comp.2 ⟨_, h₁, _, h₂, Ordering.compare_mem_comp a b c⟩

theorem compare_mem_comp_iff [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] {a c : T} :
    compare a c ∈ comp C D ↔ ∃ b, compare a b ∈ C ∧ compare b c ∈ D := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h₁, h₂⟩ ↦ compare_mem_comp h₁ h₂⟩
  obtain ⟨o₁, h₁, o₂, h₂, h⟩ := mem_comp.1 h
  obtain ⟨b, rfl, rfl⟩ := Ordering.exists_compare_eq_of_mem_comp h
  exact ⟨b, h₁, h₂⟩

end LinearOrder

/-! ### The relation of a cell -/

section LT

variable [LT T]

/-- The relation of a cell relates a perspective time to the reference times that stand to it
in one of the cell's positions. -/
def toSetRel (C : Finset Ordering) : SetRel T T := {x | ∃ o ∈ C, o.Compares x.2 x.1}

theorem mem_toSetRel : p ~[toSetRel C] r ↔ ∃ o ∈ C, o.Compares r p := .rfl

@[simp] theorem mem_toSetRel_past : p ~[toSetRel ⟦past⟧] r ↔ r < p := by
  simp [mem_toSetRel, Denotes.denote, denote]

@[simp] theorem mem_toSetRel_present : p ~[toSetRel ⟦present⟧] r ↔ r = p := by
  simp [mem_toSetRel, Denotes.denote, denote]

@[simp] theorem mem_toSetRel_future : p ~[toSetRel ⟦future⟧] r ↔ p < r := by
  simp [mem_toSetRel, Denotes.denote, denote]

@[simp] theorem toSetRel_bot : (toSetRel ⊥ : SetRel T T) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, ho, _⟩ ↦ Finset.notMem_empty _ ho

theorem toSetRel_sup (C D : Finset Ordering) :
    (toSetRel (C ⊔ D) : SetRel T T) = toSetRel C ∪ toSetRel D := by
  ext ⟨p, r⟩
  simp [mem_toSetRel, or_and_right, exists_or]

@[gcongr] theorem toSetRel_subset_toSetRel (h : C ⊆ D) : (toSetRel C : SetRel T T) ⊆ toSetRel D :=
  fun _ ⟨o, ho, hc⟩ ↦ ⟨o, h ho, hc⟩

/-- The converse of a cell's relation is the relation of its mirror image, which exchanges the
past with the future. -/
theorem inv_toSetRel (C : Finset Ordering) :
    (toSetRel C : SetRel T T).inv = toSetRel (C.image .swap) := by
  ext ⟨r, p⟩
  simp only [mem_inv, mem_toSetRel, Finset.mem_image, exists_exists_and_eq_and,
    Ordering.compares_swap]

@[simp] theorem inv_toSetRel_past : (toSetRel ⟦past⟧ : SetRel T T).inv = toSetRel ⟦future⟧ :=
  inv_toSetRel _

@[simp] theorem inv_toSetRel_future : (toSetRel ⟦future⟧ : SetRel T T).inv = toSetRel ⟦past⟧ :=
  inv_toSetRel _

end LT

theorem toSetRel_past_comp_self [Preorder T] [DenselyOrdered T] :
    (toSetRel ⟦past⟧ ○ toSetRel ⟦past⟧ : SetRel T T) = toSetRel ⟦past⟧ := by
  ext ⟨p, r⟩
  simp only [SetRel.mem_comp, mem_toSetRel_past]
  exact ⟨fun ⟨_, h₁, h₂⟩ ↦ h₂.trans h₁,
    fun h ↦ let ⟨u, hu, hu'⟩ := exists_between h; ⟨u, hu', hu⟩⟩

section LinearOrder

variable [LinearOrder T]

@[simp] theorem mem_toSetRel_iff : p ~[toSetRel C] r ↔ compare r p ∈ C :=
  ⟨fun ⟨_, ho, hc⟩ ↦ (compare_iff r p).2 hc ▸ ho, fun h ↦ ⟨_, h, (compare_iff r p).1 rfl⟩⟩

instance : Decidable (p ~[toSetRel C] r) := decidable_of_iff _ mem_toSetRel_iff.symm

@[simp] theorem toSetRel_top : (toSetRel ⊤ : SetRel T T) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_toSetRel_iff.2 (Finset.mem_univ _)

theorem toSetRel_compl (C : Finset Ordering) : (toSetRel Cᶜ : SetRel T T) = (toSetRel C)ᶜ := by
  ext ⟨p, r⟩
  simp

theorem toSetRel_comp_subset (C D : Finset Ordering) :
    toSetRel C ○ toSetRel D ⊆ (toSetRel (comp D C) : SetRel T T) :=
  fun _ ⟨_, h₁, h₂⟩ ↦
    mem_toSetRel_iff.2 (compare_mem_comp (mem_toSetRel_iff.1 h₂) (mem_toSetRel_iff.1 h₁))

/-- On dense time without endpoints the composite of two cells' relations is the relation of
the composed cell. -/
theorem toSetRel_comp [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] (C D : Finset Ordering) :
    toSetRel C ○ toSetRel D = (toSetRel (comp D C) : SetRel T T) := by
  ext ⟨p, r⟩
  simp only [SetRel.mem_comp, mem_toSetRel_iff, compare_mem_comp_iff]
  exact exists_congr fun _ ↦ and_comm

end LinearOrder

end Tense
