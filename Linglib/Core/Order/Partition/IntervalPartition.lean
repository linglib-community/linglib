module

public import Linglib.Core.Order.OrdConnected
public import Mathlib.Data.Finset.Sort

/-!
# Interval partitions

`[UPSTREAM]` candidate beside `Mathlib/Order/Partition/Finpartition.lean`. An interval partition
of a finite subset of a linear order lists the subset's parts from the bottom up, each nonempty and
lying wholly below the next. Each part is then a run of the subset, the parts are the fibres of a
contiguous map on it, and the partition is determined by the part each element lies in.

## Main definitions

* `IntervalPartition`: the parts of a finite subset of a linear order, from the bottom up.
* `IntervalPartition.support`, `IntervalPartition.part`: the subset, and the part of an element.
* `IntervalPartition.discrete`, `IntervalPartition.indiscrete`: singleton parts, and one part.

## Main statements

* `IntervalPartition.mem_of_le_of_le`: a part is a run of the support.
* `IntervalPartition.isContiguous_part`: the parts are the fibres of a contiguous map.
* `IntervalPartition.ext_part`: a partition is determined by the parts of its elements.
-/

@[expose] public section

/-- An interval partition of a finite subset of `α`: its parts from the bottom up, each nonempty
and lying wholly below the next. -/
@[ext]
structure IntervalPartition (α : Type*) [LinearOrder α] where
  /-- The parts, from the bottom up. -/
  parts : List (Finset α)
  /-- Every part is nonempty. -/
  nonempty_of_mem_parts ⦃A : Finset α⦄ : A ∈ parts → A.Nonempty
  /-- Each part lies wholly below every later one. -/
  pairwise : parts.Pairwise fun A B ↦ ∀ a ∈ A, ∀ b ∈ B, a < b
  deriving DecidableEq

namespace IntervalPartition

variable {α : Type*} [LinearOrder α] (P : IntervalPartition α) {A B s : Finset α} {x y z : α}

/-- The elements the parts cover. -/
def support : Finset α := P.parts.toFinset.biUnion id

@[simp] theorem mem_support : x ∈ P.support ↔ ∃ A ∈ P.parts, x ∈ A := by simp [support]

/-- Of two distinct parts one lies wholly below the other. -/
theorem lt_or_gt_of_ne (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    (∀ a ∈ A, ∀ b ∈ B, a < b) ∨ ∀ a ∈ A, ∀ b ∈ B, b < a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hB
  have hP := List.pairwise_iff_getElem.1 P.pairwise
  rcases lt_trichotomy i j with h | rfl | h
  exacts [.inl (hP i j hi hj h), absurd rfl hAB, .inr fun a ha b hb ↦ hP j i hj hi h b hb a ha]

/-- Parts that share an element are equal. -/
theorem eq_of_mem_parts (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hxA : x ∈ A) (hxB : x ∈ B) :
    A = B := by
  by_contra hAB
  rcases P.lt_or_gt_of_ne hA hB hAB with h | h <;> exact (h x hxA x hxB).false

theorem nodup_parts : P.parts.Nodup :=
  P.pairwise.imp_of_mem fun hA _ h hAB ↦ by
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hA
    exact (h a ha a (hAB ▸ ha)).false

/-- A part is a run of the support: an element of the support between two elements of a part
lies in that part. -/
theorem mem_of_le_of_le (hA : A ∈ P.parts) (hx : x ∈ A) (hz : z ∈ A) (hy : y ∈ P.support)
    (hxy : x ≤ y) (hyz : y ≤ z) : y ∈ A := by
  obtain ⟨B, hB, hyB⟩ := P.mem_support.1 hy
  obtain rfl | hAB := eq_or_ne A B
  · exact hyB
  rcases P.lt_or_gt_of_ne hA hB hAB with h | h
  exacts [absurd hyz (h z hz y hyB).not_ge, absurd hxy (h x hx y hyB).not_ge]

/-! ### The part of an element -/

/-- The part containing `x`, or `∅` if no part does. -/
def part (x : α) : Finset α := (P.parts.find? (x ∈ ·)).getD ∅

theorem part_eq_of_mem (hA : A ∈ P.parts) (hx : x ∈ A) : P.part x = A := by
  obtain ⟨B, hB⟩ : ∃ B, P.parts.find? (x ∈ ·) = some B :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨A, hA, by simpa using hx⟩)
  rw [part, hB, Option.getD_some]
  exact P.eq_of_mem_parts (List.mem_of_find?_eq_some hB) hA (by simpa using List.find?_some hB) hx

theorem mem_part_iff_exists : y ∈ P.part x ↔ ∃ A ∈ P.parts, y ∈ A ∧ x ∈ A := by
  by_cases hx : x ∈ P.support
  · obtain ⟨A, hA, hxA⟩ := P.mem_support.1 hx
    rw [P.part_eq_of_mem hA hxA]
    exact ⟨fun hy ↦ ⟨A, hA, hy, hxA⟩, fun ⟨B, hB, hyB, hxB⟩ ↦ P.eq_of_mem_parts hB hA hxB hxA ▸ hyB⟩
  · rw [part, List.find?_eq_none.2 fun A hA hxA ↦ hx (P.mem_support.2 ⟨A, hA, by simpa using hxA⟩),
      Option.getD_none]
    exact iff_of_false (Finset.notMem_empty y) fun ⟨A, hA, _, hxA⟩ ↦
      hx (P.mem_support.2 ⟨A, hA, hxA⟩)

@[simp] theorem mem_part_self : x ∈ P.part x ↔ x ∈ P.support := by simp [mem_part_iff_exists]

alias ⟨_, mem_part⟩ := mem_part_self

@[simp] theorem part_mem : P.part x ∈ P.parts ↔ x ∈ P.support := by
  refine ⟨fun h ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts h
    obtain ⟨A, hA, -, hxA⟩ := P.mem_part_iff_exists.1 ha
    exact P.mem_support.2 ⟨A, hA, hxA⟩
  · obtain ⟨A, hA, hxA⟩ := P.mem_support.1 hx
    exact P.part_eq_of_mem hA hxA ▸ hA

@[simp] theorem part_eq_empty : P.part x = ∅ ↔ x ∉ P.support :=
  ⟨fun h hx ↦ by simpa [h] using P.mem_part hx, fun hx ↦ by
    ext y; simpa [mem_part_iff_exists] using fun A hA _ hxA ↦ hx (P.mem_support.2 ⟨A, hA, hxA⟩)⟩

/-- The parts are the fibres of a contiguous map on the support. -/
theorem isContiguous_part : IsContiguous fun x : P.support ↦ P.part x := by
  intro x y z hxy hyz (hxz : P.part x = P.part z)
  have hA := P.part_mem.2 x.2
  exact (P.part_eq_of_mem hA (P.mem_of_le_of_le hA (P.mem_part x.2)
    (hxz ▸ P.mem_part z.2) y.2 hxy hyz)).symm

/-- A partition is determined by the parts of its elements. -/
theorem ext_part {Q : IntervalPartition α} (h : ∀ x, P.part x = Q.part x) : P = Q := by
  have hmem {P Q : IntervalPartition α} (h : ∀ x, P.part x = Q.part x) {A : Finset α}
      (hA : A ∈ P.parts) : A ∈ Q.parts := by
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hA
    have hQa : Q.part a = A := (h a).symm.trans (P.part_eq_of_mem hA ha)
    exact hQa ▸ Q.part_mem.2 (Q.mem_part_self.1 (hQa ▸ ha))
  refine IntervalPartition.ext (List.Perm.eq_of_pairwise (le := fun A B ↦ ∀ a ∈ A, ∀ b ∈ B, a < b)
    (fun A B hA hB hAB hBA ↦ ?_) P.pairwise Q.pairwise
    ((List.perm_ext_iff_of_nodup P.nodup_parts Q.nodup_parts).2 fun A ↦
      ⟨hmem h, hmem fun x ↦ (h x).symm⟩))
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hA
  obtain ⟨b, hb⟩ := Q.nonempty_of_mem_parts hB
  exact absurd (hAB a ha b hb) (hBA b hb a ha).asymm

/-! ### Singleton parts, and one part -/

/-- The partition of `s` into singletons. -/
def discrete (s : Finset α) : IntervalPartition α where
  parts := (s.sort (· ≤ ·)).map singleton
  nonempty_of_mem_parts := by simp
  pairwise := List.pairwise_map.2 <| (Finset.sortedLT_sort s).pairwise.imp fun h a ha b hb ↦ by
    rw [Finset.mem_singleton] at ha hb
    exact ha ▸ hb ▸ h

/-- The partition of a nonempty `s` into one part. -/
def indiscrete (s : Finset α) (hs : s.Nonempty) : IntervalPartition α :=
  ⟨[s], by simpa using hs, List.pairwise_singleton _ _⟩

@[simp] theorem support_discrete : (discrete s).support = s := by ext; simp [discrete]

@[simp] theorem support_indiscrete (hs : s.Nonempty) : (indiscrete s hs).support = s := by
  ext; simp [indiscrete]

@[simp] theorem part_discrete (hx : x ∈ s) : (discrete s).part x = {x} :=
  part_eq_of_mem _ (by simpa [discrete]) (Finset.mem_singleton_self x)

@[simp] theorem part_indiscrete (hs : s.Nonempty) (hx : x ∈ s) : (indiscrete s hs).part x = s :=
  part_eq_of_mem _ (List.mem_singleton_self s) hx

end IntervalPartition
