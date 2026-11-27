/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.DropRight
public import Mathlib.Order.Hom.Basic

/-!
# The label of a spine and the complements of its heads

Where equality of heads is decidable, a head of a spine can be addressed by its value. The label
of a spine is the set of heads it projects, and spines are preordered by inclusion of labels. The
height of a head is the position of its first occurrence. A head divides a spine into its
complement, the spine below its first occurrence, and its shell, the heads above its last.

These operations read a value of the type of heads as one head of the spine. They are meant for
a spine on which no head recurs, as the categories of one extended projection do not.

## Main definitions

* `Spine.label`: the finset of heads a spine projects, and `Spine.labelHom`, the same as an order
  homomorphism.
* `Spine.mapHom`: `Spine.map` as an order homomorphism.
* `Spine.height`: the position of the first occurrence of a head.
* `Spine.below`, `Spine.above`: the spine below the first occurrence of a head, its complement,
  and the heads above the last, the shell over it.

## Main results

* `Spine.le_def`: the extension order is inclusion of labels.
* `Spine.mem_take_iff`: a head is among the lowest `n` exactly when it is projected below height
  `n`.
* `Spine.below_eq_take_height`: the complement of a head is the truncation at its height.
* `Spine.below_le_below`: the complement of a head lies inside the complement of every head
  above it.
* `Spine.notMem_iff_le_below`: a truncation of a spine lacks a head exactly when it lies inside
  that head's complement.
* `Spine.mem_below_or_rel`, `Spine.rel_of_mem_below`: on a spine whose heads are pairwise
  related from the bottom up, a head is in the complement of another or related to it from
  above, and the heads of a complement are related to its head.

## Implementation notes

The order on spines is inclusion of labels, which forgets the order of the heads and how often
each occurs. A truncation of a spine lies below it, and a spine lies below any other that
projects the same heads; the relation of a spine to its truncations is `<+:` on the lists of
heads.

## References

* [grimshaw-2000]
* [keine-2020]
-/

@[expose] public section

namespace Spine

variable {H : Type*} [DecidableEq H] {s t : Spine H} {c d : H} {l : List H}

/-! ### Labels, the extension order and complements -/

/-- The bilateral label of a spine is the set of heads it projects. -/
def label (s : Spine H) : Finset H := s.heads.toFinset

@[simp] theorem mem_label : c ∈ s.label ↔ c ∈ s := List.mem_toFinset

/-- The extension order. A spine lies below another when the other projects every head it does,
as the clause sizes of one extended projection do. -/
instance : Preorder (Spine H) := Preorder.lift label

theorem le_def : s ≤ t ↔ s.label ⊆ t.label := Iff.rfl

theorem le_iff_forall_mem : s ≤ t ↔ ∀ c ∈ s, c ∈ t := by simp [le_def, Finset.subset_iff]

instance : DecidableLE (Spine H) := fun s t ↦ inferInstanceAs (Decidable (s.label ⊆ t.label))

instance : DecidableLT (Spine H) := fun s t ↦ inferInstanceAs (Decidable (s.label ⊂ t.label))

/-- `Spine.label` as an order homomorphism. -/
def labelHom : Spine H →o Finset H := ⟨label, fun _ _ h ↦ h⟩

@[simp] theorem coe_labelHom : ⇑(labelHom (H := H)) = label := rfl

theorem map_mono {K : Type*} [DecidableEq K] (f : H → K) : Monotone (map f) := fun _ _ h ↦
  le_iff_forall_mem.2 fun _ hk ↦ by
    obtain ⟨c, hc, rfl⟩ := mem_map.1 hk
    exact mem_map.2 ⟨c, le_iff_forall_mem.1 h c hc, rfl⟩

/-- `Spine.map` as an order homomorphism. -/
def mapHom {K : Type*} [DecidableEq K] (f : H → K) : Spine H →o Spine K := ⟨map f, map_mono f⟩

@[simp] theorem coe_mapHom {K : Type*} [DecidableEq K] (f : H → K) : ⇑(mapHom f) = map f := rfl

/-- A truncation of a spine lies below it. -/
theorem le_of_prefix (h : t.heads <+: s.heads) : t ≤ s :=
  le_iff_forall_mem.2 fun _ hx ↦ h.subset hx

theorem le_append (s : Spine H) (l : List H) : s ≤ s.append l :=
  le_iff_forall_mem.2 fun _ hc ↦ mem_append.2 (Or.inl hc)

/-! ### The height of a head -/

/-- The height of a head, the position of its first occurrence, and the length of the spine for
a head it does not project. -/
def height (s : Spine H) (c : H) : ℕ := s.heads.idxOf c

theorem height_lt_length_iff : s.height c < s.heads.length ↔ c ∈ s := List.idxOf_lt_length_iff

/-- A head is among the lowest `n` exactly when the spine projects it below height `n`. -/
theorem mem_take_iff {n : ℕ} : c ∈ s.take n ↔ c ∈ s ∧ s.height c < n :=
  ⟨fun h ↦ have hc := List.mem_of_mem_take h; ⟨hc, (List.mem_take_iff_idxOf_lt hc).1 h⟩,
    fun ⟨h, h'⟩ ↦ (List.mem_take_iff_idxOf_lt h).2 h'⟩

/-- A truncation projects every head lower than one it projects. -/
theorem mem_take_of_height_lt {n : ℕ} (hc : c ∈ s.take n) (hd : d ∈ s)
    (h : s.height d < s.height c) : d ∈ s.take n :=
  mem_take_iff.2 ⟨hd, h.trans (mem_take_iff.1 hc).2⟩

/-- A longer truncation lies above a shorter one. -/
theorem take_mono (s : Spine H) : Monotone s.take := fun _ _ h ↦
  le_iff_forall_mem.2 fun _ hc ↦
    mem_take_iff.2 ⟨(mem_take_iff.1 hc).1, (mem_take_iff.1 hc).2.trans_le h⟩

/-! ### Complements of a head -/

/-- The complement of the first occurrence of `c`, the spine of the heads strictly below it, so
that `s.below .C` is the TP a finite clause's C⁰ selects. A spine that does not project `c` is its
own complement. -/
def below (s : Spine H) (c : H) : Spine H := ⟨s.heads.takeWhile (· != c)⟩

@[simp] theorem heads_below (s : Spine H) (c : H) :
    (s.below c).heads = s.heads.takeWhile (· != c) :=
  rfl

/-- The complement of a head is the truncation of the spine at its height. -/
theorem below_eq_take_height (s : Spine H) (c : H) : s.below c = s.take (s.height c) := by
  have h : (fun a : H ↦ !(a != c)) = (· == c) := funext fun a ↦ by simp [bne]
  simp [below, take, height, List.takeWhile_eq_take_findIdx_not, List.idxOf, h]

/-- The heads strictly above the last occurrence of `c`, so that `s.above .C` is the shell over the
CP of `s` and `[]` for a bare CP. -/
def above (s : Spine H) (c : H) : List H := s.heads.rtakeWhile (· != c)

theorem notMem_below_self (s : Spine H) (c : H) : c ∉ s.below c := fun h ↦ by
  simpa using List.mem_takeWhile_imp h

theorem below_le (s : Spine H) (c : H) : s.below c ≤ s :=
  le_iff_forall_mem.2 fun _ h ↦ (List.takeWhile_prefix _).subset h

/-- A truncation of a spine that does not project `c` is a truncation of the complement of
`c`. -/
theorem prefix_below_of_notMem (h : t.heads <+: s.heads) (hc : c ∉ t) :
    t.heads <+: (s.below c).heads := by
  obtain ⟨r, hr⟩ := h
  have ht : ∀ x ∈ t.heads, (x != c) = true := fun x hx ↦ bne_iff_ne.2 fun hxc ↦ hc (hxc ▸ hx)
  rw [heads_below, ← hr, List.takeWhile_append_of_pos ht]
  exact List.prefix_append _ _

/-- A truncation of a spine that projects `c` contains the complement of `c`. -/
theorem below_prefix_of_mem (h : t.heads <+: s.heads) (hc : c ∈ t) :
    (s.below c).heads <+: t.heads :=
  (List.prefix_or_prefix_of_prefix (List.takeWhile_prefix _) h).resolve_right fun h' ↦
    s.notMem_below_self c (h'.subset hc)

/-- A truncation of a spine lacks a head exactly when it lies inside that head's complement. -/
theorem notMem_iff_le_below (h : t.heads <+: s.heads) : c ∉ t ↔ t ≤ s.below c :=
  ⟨fun hc ↦ le_of_prefix (prefix_below_of_notMem h hc),
    fun ht hc ↦ s.notMem_below_self c (le_iff_forall_mem.1 ht c hc)⟩

/-- The complement of a head lies inside the complement of every head above it. -/
theorem below_prefix (h : c ∈ s.below d) : (s.below c).heads <+: (s.below d).heads :=
  below_prefix_of_mem (List.takeWhile_prefix _) h

theorem below_le_below (h : c ∈ s.below d) : s.below c ≤ s.below d :=
  le_of_prefix (below_prefix h)

/-! ### Pairwise related heads -/

private theorem mem_takeWhile_or_rel {r : H → H → Prop} [Std.Refl r] :
    ∀ {l : List H}, l.Pairwise r → c ∈ l → d ∈ l → d ∈ l.takeWhile (· != c) ∨ r c d
  | x :: l, hp, hc, hd => by
    obtain ⟨hx, hl⟩ := List.pairwise_cons.1 hp
    by_cases hxc : x = c
    · subst hxc
      rcases List.mem_cons.1 hd with rfl | hd
      · exact .inr (refl _)
      · exact .inr (hx d hd)
    · have hc' : c ∈ l := (List.mem_cons.1 hc).resolve_left (Ne.symm hxc)
      rw [List.takeWhile_cons_of_pos (by simpa using hxc)]
      rcases List.mem_cons.1 hd with rfl | hd
      · exact .inl List.mem_cons_self
      · exact (mem_takeWhile_or_rel hl hc' hd).imp (List.mem_cons_of_mem _) id

private theorem rel_of_mem_takeWhile {r : H → H → Prop} :
    ∀ {l : List H}, l.Pairwise r → c ∈ l → d ∈ l.takeWhile (· != c) → r d c
  | x :: l, hp, hc, hd => by
    obtain ⟨hx, hl⟩ := List.pairwise_cons.1 hp
    by_cases hxc : x = c
    · simp [hxc] at hd
    · have hc' : c ∈ l := (List.mem_cons.1 hc).resolve_left (Ne.symm hxc)
      rw [List.takeWhile_cons_of_pos (by simpa using hxc)] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hx c hc'
      · exact rel_of_mem_takeWhile hl hc' hd

/-- On a spine whose heads are pairwise related from the bottom up, a head lies in the complement
of another or is related to it from above. -/
theorem mem_below_or_rel {r : H → H → Prop} [Std.Refl r] (hs : s.heads.Pairwise r) (hc : c ∈ s)
    (hd : d ∈ s) : d ∈ s.below c ∨ r c d :=
  mem_takeWhile_or_rel hs hc hd

/-- On a spine whose heads are pairwise related from the bottom up, the heads of the complement
of a head are related to it. -/
theorem rel_of_mem_below {r : H → H → Prop} (hs : s.heads.Pairwise r) (hc : c ∈ s)
    (hd : d ∈ s.below c) : r d c :=
  rel_of_mem_takeWhile hs hc hd

/-! ### Shells of a head -/

theorem above_append (s : Spine H) (h : c ∉ l) : (s.append l).above c = s.above c ++ l := by
  induction l using List.reverseRecOn with
  | nil => simp [above]
  | append_singleton l x ih =>
    simp only [List.mem_append, List.mem_singleton, not_or] at h
    rw [above, heads_append, ← List.append_assoc,
      List.rtakeWhile_concat_pos (· != c) _ x (bne_iff_ne.2 (Ne.symm h.2)), ← List.append_assoc]
    exact congrArg (· ++ [x]) (ih h.1)

end Spine
