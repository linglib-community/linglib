module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.RelClasses

/-!
# Neighborhoods

A neighborhood is the local environment a postsyntactic rule inspects, a focus terminal with the
terminals to either side, nearest first. Vocabulary Items and Impoverishment rules are stated over
the same neighborhoods. A terminal of features bears each feature at its offset from the focus, so
a neighborhood presents a finite set of positioned features (`toFinset`), and one neighborhood is
included in another, `⊆`, when every positioned feature of the one is one of the other. Every
finite set of positioned features has a least presentation (`ofFinset`), a Galois connection that
makes the Subset Principle's inclusion of sites an inclusion of finite sets.

## Main definitions

* `Neighborhood`: focus, left context, right context.
* `Neighborhood.nth`: the terminal at an integer offset from the focus.
* `(i, f) ∈ n`: the terminal at offset `i` bears the feature `f`; `s ⊆ n` when
  every positioned feature of `s` is one of `n`.
* `Neighborhood.toFinset`, `Neighborhood.ofFinset`: the positioned features as a finite set,
  and the least neighborhood bearing a finite set of them.
* `Neighborhood.project`, `Neighborhood.window`: the neighborhood on a tier, and the focus with
  the terminals within a radius of it.
* `Neighborhood.around`, `Neighborhood.along`: the neighborhood of a position of
  a string, and each terminal of a string in its neighborhood.

## Main results

* `Neighborhood.subset_iff_nth`: inclusion compares terminal by terminal.
* `Neighborhood.ofBundle_subset_iff`: a bundle is included where its features are on the
  focus.
* `Neighborhood.gc_ofFinset_toFinset`: `ofFinset` and `toFinset` form a Galois connection, and
  `toFinset ∘ ofFinset` is the identity.
* `Neighborhood.toList_of_mem_along`, `Neighborhood.nth_around`: each
  neighborhood of a string reassembles to it, and terminal `k` stands at offset
  `k - i` from position `i`.

## Implementation notes

Offsets are integers, indexed as for `Turing.Tape.nth`: `0` is the focus,
`-(k + 1)` the `k`-th terminal to the left (toward the root), `k + 1` the `k`-th
to the right (toward the clause), and past either end `nth` returns `default`,
for a terminal of features `∅`. Inclusion ignores empty terminals past the ends, so it is a
preorder and not a partial order; as for `PSet`, the preorder is written `⊆`.

A bare bundle coerces to the neighborhood with nothing to either side.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
* [D. Embick, *Localism versus Globalism in Morphology and Phonology*][embick-2010]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
-/

@[expose] public section

namespace DistributedMorphology

variable {Bundle F : Type*}

/-- A neighborhood is the local context a postsyntactic rule may inspect, the
`focus` terminal and the terminals to either side, nearest first. A condition that only
inspects `focus` is paradigmatic; one that reads `leftCtx` or `rightCtx` is
syntagmatic. -/
@[use_set_notation_for_order]
structure Neighborhood (Bundle : Type*) where
  /-- The terminal the rule inspects. -/
  focus    : Bundle
  /-- The terminals to its left, nearest first. -/
  leftCtx  : List Bundle := []
  /-- The terminals to its right, nearest first. -/
  rightCtx : List Bundle := []
  deriving Repr, DecidableEq

namespace Neighborhood

/-- A bundle, viewed as a context-free neighborhood. -/
@[coe] def ofBundle (fb : Bundle) : Neighborhood Bundle := { focus := fb }

instance : Coe Bundle (Neighborhood Bundle) := ⟨ofBundle⟩

instance [EmptyCollection Bundle] : EmptyCollection (Neighborhood Bundle) := ⟨ofBundle ∅⟩

@[simp] theorem focus_ofBundle (fb : Bundle) : (ofBundle fb).focus = fb := rfl

@[simp] theorem leftCtx_ofBundle (fb : Bundle) : (ofBundle fb).leftCtx = [] := rfl

@[simp] theorem rightCtx_ofBundle (fb : Bundle) : (ofBundle fb).rightCtx = [] := rfl

@[simp] theorem ofBundle_empty : ofBundle (∅ : Finset F) = ∅ := rfl

/-! ### Offsets -/

/-- `n.nth i` is the terminal at offset `i` from the focus, where `0` is the
focus, `-(k + 1)` the `k`-th terminal to the left, `k + 1` the `k`-th to the
right, and `default` lies past either end. -/
def nth [Inhabited Bundle] (n : Neighborhood Bundle) : ℤ → Bundle
  | 0 => n.focus
  | (k + 1 : ℕ) => n.rightCtx.getD k default
  | -(k + 1 : ℕ) => n.leftCtx.getD k default

section nth

variable [Inhabited Bundle] (n : Neighborhood Bundle) (k : ℕ)

@[simp] theorem nth_zero : n.nth 0 = n.focus := rfl

@[simp] theorem nth_natCast_add_one : n.nth (k + 1) = n.rightCtx.getD k default := rfl

@[simp] theorem nth_neg_natCast_add_one : n.nth (-(k + 1)) = n.leftCtx.getD k default := rfl

@[simp] theorem nth_one : n.nth 1 = n.rightCtx.getD 0 default := rfl

@[simp] theorem nth_neg_one : n.nth (-1) = n.leftCtx.getD 0 default := rfl

theorem nth_ofBundle (fb : Bundle) (i : ℤ) :
    (ofBundle fb).nth i = if i = 0 then fb else default := by
  rcases i with (_ | k) | k <;> rfl

end nth

/-! ### Tiers and windows -/

/-- The projection onto the tier `T` keeps the focus and the terminals on either side that `T`
keeps, nearest first. Pruning null terminals is the projection onto the overt ones. -/
def project (T : Bundle → Prop) [DecidablePred T] (n : Neighborhood Bundle) :
    Neighborhood Bundle :=
  ⟨n.focus, n.leftCtx.filter T, n.rightCtx.filter T⟩

@[simp] theorem focus_project (T : Bundle → Prop) [DecidablePred T] (n : Neighborhood Bundle) :
    (n.project T).focus = n.focus := rfl

@[simp] theorem leftCtx_project (T : Bundle → Prop) [DecidablePred T] (n : Neighborhood Bundle) :
    (n.project T).leftCtx = n.leftCtx.filter T := rfl

@[simp] theorem rightCtx_project (T : Bundle → Prop) [DecidablePred T] (n : Neighborhood Bundle) :
    (n.project T).rightCtx = n.rightCtx.filter T := rfl

/-- The window of radius `k` keeps the focus and the `k` terminals nearest it on either side. A
condition is adjacent on the tier `T` when it factors through `window 1 ∘ project T`; the linear
adjacency of [embick-2010] and [arregi-nevins-2012] is adjacency on the tier of overt
terminals. -/
def window (k : ℕ) (n : Neighborhood Bundle) : Neighborhood Bundle :=
  ⟨n.focus, n.leftCtx.take k, n.rightCtx.take k⟩

@[simp] theorem window_window (k m : ℕ) (n : Neighborhood Bundle) :
    (n.window m).window k = n.window (min k m) := by
  simp [window, List.take_take]

theorem nth_window [Inhabited Bundle] (n : Neighborhood Bundle) {k : ℕ} {i : ℤ}
    (hi : i.natAbs ≤ k) : (n.window k).nth i = n.nth i := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rcases m with _ | m
    · rfl
    · rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by omega]
      simp only [window, nth_natCast_add_one, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt (show m < k by omega)]
  · rcases m with _ | m
    · rfl
    · rw [show -((m + 1 : ℕ) : ℤ) = -((m : ℤ) + 1) by omega]
      simp only [window, nth_neg_natCast_add_one, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt (show m < k by omega)]

/-! ### Neighborhoods of a string -/

section String

variable (d : List Bundle) (i : ℕ) (b : Bundle)

/-- The terminals of a neighborhood, in linear order. -/
def toList (n : Neighborhood Bundle) : List Bundle := n.leftCtx.reverse ++ n.focus :: n.rightCtx

/-- `around d i b` is the neighborhood of position `i` of the string `d` with `b`
in focus, the earlier terminals to its left and the later ones to its right,
nearest first. -/
def around : Neighborhood Bundle := ⟨b, (d.take i).reverse, d.drop (i + 1)⟩

/-- Each terminal of the string `d` in its neighborhood, in order. -/
def along : List (Neighborhood Bundle) := d.mapIdx (around d)

@[simp] theorem toList_ofBundle : (ofBundle b).toList = [b] := rfl

@[simp] theorem focus_around : (around d i b).focus = b := rfl

theorem toList_around (h : i < d.length) : (around d i b).toList = d.set i b := by
  simp [toList, around, List.set_eq_take_append_cons_drop, h]

theorem nth_around [Inhabited Bundle] {k : ℕ} (hi : i ≤ d.length) (hk : k ≠ i) :
    (around d i b).nth (k - i) = d.getD k default := by
  rcases Nat.lt_or_gt_of_ne hk with hk | hk
  · obtain ⟨m, rfl⟩ : ∃ m, i = k + m + 1 := ⟨i - k - 1, by omega⟩
    rw [show (k - ↑(k + m + 1) : ℤ) = -(m + 1) by omega, nth_neg_natCast_add_one]
    simp only [around, List.getD_eq_getElem?_getD]
    rw [List.getElem?_reverse (by simp; omega), List.length_take_of_le hi,
      List.getElem?_take_of_lt (by omega), show k + m + 1 - 1 - m = k by omega]
  · obtain ⟨m, rfl⟩ : ∃ m, k = i + m + 1 := ⟨k - i - 1, by omega⟩
    rw [show (↑(i + m + 1) - i : ℤ) = m + 1 by omega, nth_natCast_add_one]
    simp only [around, List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [show i + 1 + m = i + m + 1 by omega]

@[simp] theorem length_along : (along d).length = d.length := List.length_mapIdx

@[simp] theorem getElem_along (h : i < (along d).length) :
    (along d)[i] = around d i (d[i]'(by simpa using h)) :=
  List.getElem_mapIdx

@[simp] theorem map_focus_along : (along d).map focus = d :=
  List.ext_getElem (by simp) fun _ _ _ ↦ by simp

theorem toList_of_mem_along {n : Neighborhood Bundle} (h : n ∈ along d) : n.toList = d := by
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp h
  rw [toList_around _ _ _ hi, List.set_getElem_self]

end String

/-! ### Positioned features -/

variable {s n : Neighborhood (Finset F)} {x : ℤ × F}

/-- `(i, f) ∈ n` holds when the terminal at offset `i` from the focus bears the feature `f`. -/
instance : Membership (ℤ × F) (Neighborhood (Finset F)) := ⟨fun n x ↦ x.2 ∈ n.nth x.1⟩

theorem mem_def : x ∈ n ↔ x.2 ∈ n.nth x.1 := Iff.rfl

instance [DecidableEq F] (x : ℤ × F) (n : Neighborhood (Finset F)) : Decidable (x ∈ n) :=
  inferInstanceAs (Decidable (x.2 ∈ n.nth x.1))

@[simp] theorem mem_ofBundle {fs : Finset F} :
    x ∈ (fs : Neighborhood (Finset F)) ↔ x.1 = 0 ∧ x.2 ∈ fs := by
  rw [mem_def, nth_ofBundle]
  split_ifs with h
  · simp [h]
  · exact iff_of_false (Finset.notMem_empty _) fun h' ↦ h h'.1

@[simp] theorem notMem_empty : x ∉ (∅ : Neighborhood (Finset F)) :=
  fun h ↦ Finset.notMem_empty _ (mem_ofBundle (fs := ∅).1 h).2

/-- The positioned features of a neighborhood, as a set. -/
def toSet (n : Neighborhood (Finset F)) : Set (ℤ × F) := {x | x ∈ n}

@[simp] theorem mem_toSet : x ∈ n.toSet ↔ x ∈ n := Iff.rfl

/-! ### Inclusion -/

/-- A neighborhood is included in another when every positioned feature it bears is one of the
other's; a terminal it leaves empty is unconstrained. This is the Subset Principle's inclusion,
the order of the positioned features lifted to neighborhoods. -/
instance : Preorder (Neighborhood (Finset F)) := Preorder.lift toSet

theorem subset_iff : s ⊆ n ↔ ∀ ⦃x⦄, x ∈ s → x ∈ n := Iff.rfl

theorem mem_of_subset (h : s ⊆ n) (hx : x ∈ s) : x ∈ n := h hx

theorem subset_iff_nth : s ⊆ n ↔ ∀ i, s.nth i ⊆ n.nth i :=
  ⟨fun h i _ hf ↦ subset_iff.1 h (x := (i, _)) hf, fun h ↦ subset_iff.2 fun x hx ↦ h x.1 hx⟩

theorem focus_subset_focus (h : s ⊆ n) : s.focus ⊆ n.focus := subset_iff_nth.mp h 0

@[simp] theorem empty_subset (n : Neighborhood (Finset F)) : ∅ ⊆ n :=
  subset_iff.2 fun _ h ↦ absurd h notMem_empty

@[simp] theorem ofBundle_subset_iff {fs : Finset F} :
    (fs : Neighborhood (Finset F)) ⊆ n ↔ fs ⊆ n.focus :=
  ⟨fun h _ hf ↦ subset_iff.1 h (x := (0, _)) (mem_ofBundle.mpr ⟨rfl, hf⟩),
    fun h ↦ subset_iff.2 fun _ hx ↦ by
      obtain ⟨hi, hf⟩ := mem_ofBundle.mp hx; exact mem_def.mpr (hi ▸ h hf)⟩

/-! ### Finite sets of positioned features -/

private theorem getD_map_range {N k : ℕ} (g : ℕ → Finset F) :
    ((List.range N).map g).getD k default = if k < N then g k else ∅ := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]
    rfl

section toFinset

variable [DecidableEq F]

/-- The positioned features a list of terminals puts at the offsets `g 0`, `g 1`, …. -/
def positionsOf (g : ℕ → ℤ) (l : List (Finset F)) : Finset (ℤ × F) :=
  l.zipIdx.toFinset.biUnion fun p ↦ p.1.map (.sectR (g p.2) F)

theorem mem_positionsOf {g : ℕ → ℤ} {l : List (Finset F)} {i : ℤ} {f : F} :
    (i, f) ∈ positionsOf g l ↔ ∃ k, g k = i ∧ f ∈ l.getD k default := by
  simp only [positionsOf, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_map,
    Function.Embedding.sectR_apply, Prod.mk.injEq, Prod.exists, List.mem_zipIdx_iff_getElem?,
    List.getD_eq_getElem?_getD]
  constructor
  · rintro ⟨a, k, hk, c, hc, hgi, rfl⟩
    exact ⟨k, hgi, by rw [hk]; exact hc⟩
  · rintro ⟨k, hgi, hf⟩
    cases hk : l[k]? with
    | none => rw [hk] at hf; exact absurd hf (Finset.notMem_empty f)
    | some a => rw [hk] at hf; exact ⟨a, k, hk, f, hf, hgi, rfl⟩

/-- The positioned features of a neighborhood, as a finite set. -/
def toFinset (n : Neighborhood (Finset F)) : Finset (ℤ × F) :=
  n.focus.map (.sectR 0 F) ∪ positionsOf (fun k ↦ -(k + 1 : ℤ)) n.leftCtx ∪
    positionsOf (fun k ↦ (k + 1 : ℤ)) n.rightCtx

@[simp] theorem mem_toFinset : x ∈ n.toFinset ↔ x ∈ n := by
  obtain ⟨i, f⟩ := x
  simp only [toFinset, Finset.mem_union, mem_positionsOf, Finset.mem_map,
    Function.Embedding.sectR_apply, Prod.mk.injEq]
  rw [mem_def]
  constructor
  · rintro ((⟨a, ha, rfl, rfl⟩ | ⟨k, rfl, hf⟩) | ⟨k, rfl, hf⟩)
    · exact ha
    · rwa [nth_neg_natCast_add_one]
    · rwa [nth_natCast_add_one]
  · rcases i with (_ | k) | k <;> intro hf
    · exact .inl (.inl ⟨f, hf, rfl, rfl⟩)
    · exact .inr ⟨k, rfl, hf⟩
    · exact .inl (.inr ⟨k, (Int.negSucc_eq k).symm, hf⟩)

@[simp] theorem coe_toFinset : (n.toFinset : Set (ℤ × F)) = n.toSet := by ext; simp

theorem toFinset_subset_toFinset : s.toFinset ⊆ n.toFinset ↔ s ⊆ n := by
  simp [Finset.subset_iff, subset_iff]

instance : DecidableLE (Neighborhood (Finset F)) :=
  fun _ _ ↦ decidable_of_iff _ toFinset_subset_toFinset

/-- The features a finite set of positioned features puts at offset `i`. -/
def atOffset (t : Finset (ℤ × F)) (i : ℤ) : Finset F := (t.filter (·.1 = i)).image Prod.snd

@[simp] theorem mem_atOffset {t : Finset (ℤ × F)} {i : ℤ} {f : F} :
    f ∈ atOffset t i ↔ (i, f) ∈ t := by
  simp [atOffset]

/-- The neighborhood bearing exactly the positioned features of a finite set, out to the largest
offset among them. -/
def ofFinset (t : Finset (ℤ × F)) : Neighborhood (Finset F) :=
  ⟨atOffset t 0, (List.range (t.sup (·.1.natAbs))).map fun k : ℕ ↦ atOffset t (-((k : ℤ) + 1)),
    (List.range (t.sup (·.1.natAbs))).map fun k : ℕ ↦ atOffset t ((k : ℤ) + 1)⟩

@[simp] theorem mem_ofFinset {t : Finset (ℤ × F)} : x ∈ ofFinset t ↔ x ∈ t := by
  obtain ⟨i, f⟩ := x
  have hb {j : ℤ} (h : (j, f) ∈ t) : j.natAbs ≤ t.sup (·.1.natAbs) :=
    Finset.le_sup (f := fun y : ℤ × F ↦ y.1.natAbs) h
  rw [mem_def]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rcases m with _ | m
    · simp [ofFinset]
    · rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by omega, nth_natCast_add_one]
      simp only [ofFinset, getD_map_range]
      split_ifs with hm
      · exact mem_atOffset
      · exact iff_of_false (Finset.notMem_empty _) fun h ↦ hm (by have := hb h; omega)
  · rcases m with _ | m
    · simp [ofFinset]
    · rw [show -((m + 1 : ℕ) : ℤ) = -((m : ℤ) + 1) by omega, nth_neg_natCast_add_one]
      simp only [ofFinset, getD_map_range]
      split_ifs with hm
      · exact mem_atOffset
      · exact iff_of_false (Finset.notMem_empty _) fun h ↦ hm (by have := hb h; omega)

@[simp] theorem toFinset_ofFinset (t : Finset (ℤ × F)) : (ofFinset t).toFinset = t := by
  ext; simp

theorem gc_ofFinset_toFinset :
    GaloisConnection (ofFinset : Finset (ℤ × F) → Neighborhood (Finset F)) toFinset :=
  fun _ _ ↦ by simp [subset_iff, Finset.subset_iff]

theorem ofFinset_subset_ofFinset {s t : Finset (ℤ × F)} : ofFinset s ⊆ ofFinset t ↔ s ⊆ t :=
  gc_ofFinset_toFinset.le_iff_le.trans (by rw [toFinset_ofFinset])

end toFinset

end Neighborhood

end DistributedMorphology
