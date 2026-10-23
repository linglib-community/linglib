module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.Interval.Finset.Defs
public import Linglib.Core.Data.List.Infix
public import Linglib.Core.Order.LeftLinear

/-!
# Tree positions

A `TreePath` is a position in a rose tree, written as its Gorn address: the list of child indices
on the way down from the root. Under the prefix order, with `p ≤ q` when `p` dominates `q`, the
positions form the rooted tree in which every node has a child for each natural number. It carries
the order structure of `Mathlib/Order/SuccPred/Tree.lean`: the root `⊥` is the empty address,
`Order.pred` drops the last index, `p ⊓ q` is the longest common prefix, and strict dominance is
well founded, so ancestor chains are finite. The positions of a concrete tree form a prefix-closed
subset (`RoseTree.validPaths`).

`p` precedes `q` when the two part at some position with `p` taking the earlier child. Precedence
is lexicographic order between positions neither of which dominates the other. It is a decidable
strict order, it passes to dominated positions, and any two positions are related by dominance or
by precedence.

Two positions are left-aligned when their addresses differ only in trailing first-daughter steps,
so that the subtrees at them begin with the same leaf. Left-alignment is a decidable equivalence
relation, and left-aligned positions lie on one branch.

## Main definitions

* `Core.Order.TreePath`: Gorn addresses under the prefix order.
* `Core.Order.TreePath.Precedes`: linear precedence of positions.
* `Core.Order.TreePath.LeftAligned`: positions sharing a left edge.

## Main results

* `TreePath.covBy_iff`: `q` covers `p` exactly when `q` extends `p` by one index.
* `TreePath.precedes_iff_lt_and_not_le`: precedence is lexicographic order minus dominance.
* `TreePath.Precedes.trichotomy`: two positions are related by dominance or by precedence.
* `TreePath.leftAligned_iff_exists`: positions are left-aligned exactly when descending through
  first daughters from each reaches a common position.
-/

@[expose] public section

namespace Core.Order

/-- A position in a rose tree is given by its Gorn address, the child indices on the path from
the root. The empty address is the root. -/
@[ext]
structure TreePath where
  /-- The child indices, from the root down. -/
  toList : List ℕ
  deriving DecidableEq, Repr

namespace TreePath

/-- A position dominates another when its address is a prefix of the other's. -/
instance : LE TreePath := ⟨fun p q ↦ p.toList <+: q.toList⟩

theorem le_def {p q : TreePath} : p ≤ q ↔ p.toList <+: q.toList := Iff.rfl

@[simp] theorem mk_le_mk {l m : List ℕ} : (⟨l⟩ : TreePath) ≤ ⟨m⟩ ↔ l <+: m := Iff.rfl

instance : DecidableLE TreePath := fun _ _ ↦ decidable_of_iff _ le_def.symm

instance : PartialOrder TreePath where
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ h₁ h₂ := TreePath.ext (h₁.eq_of_length (h₁.length_le.antisymm h₂.length_le))

instance : DecidableLT TreePath := fun _ _ ↦ decidable_of_iff _ lt_iff_le_not_ge.symm

instance : OrderBot TreePath where
  bot := ⟨[]⟩
  bot_le _ := List.nil_prefix

@[simp] theorem bot_toList : (⊥ : TreePath).toList = [] := rfl

theorem length_strictMono : StrictMono fun p : TreePath ↦ p.toList.length := fun _ _ h ↦
  h.le.length_le.lt_of_ne fun hlen ↦ h.ne (TreePath.ext (h.le.eq_of_length hlen))

instance : WellFoundedLT TreePath := length_strictMono.wellFoundedLT

/-- The paths at or above a path are its prefixes, finitely many. -/
instance : LocallyFiniteOrderBot TreePath :=
  .ofIic TreePath (fun p ↦ (p.toList.inits.map TreePath.mk).toFinset) fun a p ↦ by
    simp only [List.mem_toFinset, List.mem_map, List.mem_inits]
    exact ⟨fun ⟨l, hl, e⟩ ↦ e ▸ hl, fun h ↦ ⟨p.toList, h, rfl⟩⟩

/-! ### Parents -/

/-- The parent of a position drops its last index. The root is its own parent. -/
def parent (p : TreePath) : TreePath := ⟨p.toList.dropLast⟩

@[simp] theorem parent_toList (p : TreePath) : p.parent.toList = p.toList.dropLast := rfl

theorem parent_le (p : TreePath) : p.parent ≤ p := List.dropLast_prefix p.toList

theorem le_parent_of_lt {p q : TreePath} (h : p < q) : p ≤ q.parent := by
  obtain ⟨⟨s, hs⟩, hne⟩ := lt_iff_le_and_ne.mp h
  have hs' : s ≠ [] := by
    rintro rfl
    exact hne (TreePath.ext (by simpa using hs))
  rw [le_def, parent_toList, ← hs, List.dropLast_append_of_ne_nil hs']
  exact List.prefix_append _ _

instance : PredOrder TreePath where
  pred := parent
  pred_le := parent_le
  min_of_le_pred {p} h := by
    have := (le_def.mp h).length_le
    rw [parent_toList, List.length_dropLast] at this
    obtain rfl : p = ⊥ := TreePath.ext (List.eq_nil_of_length_eq_zero (by omega))
    exact isMin_bot
  le_pred_of_lt := le_parent_of_lt

@[simp] theorem pred_eq_parent (p : TreePath) : Order.pred p = p.parent := rfl

/-- A position is covered exactly by its daughters, the extensions by one index. -/
theorem covBy_iff {p q : TreePath} : p ⋖ q ↔ ∃ i, q.toList = p.toList ++ [i] := by
  constructor
  · intro h
    have hq : q.toList ≠ [] := fun hq ↦ ne_bot_of_gt h.lt (TreePath.ext hq)
    refine ⟨q.toList.getLast hq, ?_⟩
    rw [← Order.pred_eq_of_covBy h, pred_eq_parent, parent_toList, List.dropLast_concat_getLast]
  · rintro ⟨i, hi⟩
    have hparent : q.parent = p := TreePath.ext (by simp [hi])
    have hpq : p < q := hparent ▸ (parent_le q).lt_of_ne fun h ↦ by
      simpa [hi] using congrArg (fun r : TreePath ↦ r.toList.length) (hparent.symm.trans h)
    simpa [hparent] using Order.pred_covBy_of_not_isMin (not_isMin_of_lt hpq)

/-! ### Least common ancestors -/

/-- The meet of two positions is their longest common prefix, the deepest position dominating
both. -/
instance : SemilatticeInf TreePath where
  inf p q := ⟨List.commonPrefix p.toList q.toList⟩
  inf_le_left p q := List.commonPrefix_prefix_left p.toList q.toList
  inf_le_right p q := List.commonPrefix_prefix_right p.toList q.toList
  le_inf _ _ _ := List.prefix_commonPrefix

/-! ### Linear precedence -/

/-- `p` precedes `q` when, at some common position, `p` continues into an earlier child than
`q`. -/
def Precedes (p q : TreePath) : Prop :=
  ∃ (r : List ℕ) (i j : ℕ), i < j ∧ r ++ [i] <+: p.toList ∧ r ++ [j] <+: q.toList

namespace Precedes

variable {p q r : TreePath}

/-- A position comes lexicographically before every position it precedes. -/
protected theorem lt (h : Precedes p q) : p.toList < q.toList := by
  obtain ⟨r, i, j, hij, ⟨s, hp⟩, ⟨s', hq⟩⟩ := h
  rw [← hp, ← hq, List.append_assoc, List.append_assoc]
  exact List.append_left_lt (List.cons_lt_cons_iff.mpr (.inl hij))

protected theorem not_le (h : Precedes p q) : ¬ p ≤ q := fun hle ↦ by
  obtain ⟨r, i, j, hij, hi, hj⟩ := h
  have hlen : (r ++ [i]).length = (r ++ [j]).length := by simp
  rcases List.prefix_or_prefix_of_prefix (hi.trans hle) hj with h | h
  · exact hij.ne (by simpa using h.eq_of_length hlen)
  · exact hij.ne (by simpa using (h.eq_of_length hlen.symm).symm)

protected theorem not_ge (h : Precedes p q) : ¬ q ≤ p := by
  rintro ⟨s, hs⟩
  exact List.le_append_left (hs ▸ h.lt)

protected theorem mono {p' q' : TreePath} (h : Precedes p q) (hp : p ≤ p') (hq : q ≤ q') :
    Precedes p' q' :=
  let ⟨r, i, j, hij, hi, hj⟩ := h
  ⟨r, i, j, hij, hi.trans hp, hj.trans hq⟩

theorem cons (i : ℕ) (h : Precedes p q) : Precedes ⟨i :: p.toList⟩ ⟨i :: q.toList⟩ :=
  let ⟨r, a, b, hab, ha, hb⟩ := h
  ⟨i :: r, a, b, hab, List.cons_prefix_cons.mpr ⟨rfl, ha⟩, List.cons_prefix_cons.mpr ⟨rfl, hb⟩⟩

end Precedes

theorem precedes_cons_of_lt {i j : ℕ} (hij : i < j) (p q : TreePath) :
    Precedes ⟨i :: p.toList⟩ ⟨j :: q.toList⟩ :=
  ⟨[], i, j, hij, by simp, by simp⟩

/-- `p` precedes `q` exactly when `p` comes lexicographically before `q` without dominating it. -/
theorem precedes_iff_lt_and_not_le {p q : TreePath} :
    Precedes p q ↔ p.toList < q.toList ∧ ¬ p ≤ q := by
  refine ⟨fun h ↦ ⟨h.lt, h.not_le⟩, fun ⟨hlt, hle⟩ ↦ ?_⟩
  rcases List.lt_iff_exists.mp hlt with ⟨h, -⟩ | ⟨i, h₁, h₂, heq, hi⟩
  · exact absurd (List.prefix_iff_eq_take.mpr h) hle
  · have htake : p.toList.take i = q.toList.take i := List.ext_getElem (by simp; omega)
      fun k hk _ ↦ by simp only [List.length_take] at hk; simpa using heq k (by omega)
    refine ⟨p.toList.take i, _, _, hi, ?_, ?_⟩
    · rw [List.take_concat_get']
      exact List.take_prefix _ _
    · rw [htake, List.take_concat_get']
      exact List.take_prefix _ _

instance (p q : TreePath) : Decidable (Precedes p q) :=
  decidable_of_iff _ precedes_iff_lt_and_not_le.symm

namespace Precedes

variable {p q r : TreePath}

protected theorem irrefl (p : TreePath) : ¬ Precedes p p := fun h ↦ lt_irrefl _ h.lt

protected theorem asymm (h : Precedes p q) : ¬ Precedes q p := fun h' ↦ lt_asymm h.lt h'.lt

protected theorem trans (h₁ : Precedes p q) (h₂ : Precedes q r) : Precedes p r := by
  refine precedes_iff_lt_and_not_le.mpr ⟨h₁.lt.trans h₂.lt, fun hpr ↦ ?_⟩
  obtain ⟨s, k, l, hkl, hk, hl⟩ := h₂
  rcases le_or_gt p.toList.length s.length with hlen | hlen
  · -- `p` dominates the position where `q` and `r` part, hence dominates `q`
    exact h₁.not_le <| (List.prefix_of_prefix_length_le hpr
      ((List.prefix_append _ _).trans hl) hlen).trans ((List.prefix_append _ _).trans hk)
  · -- `p` lies inside `r`'s branch at that position, so `q` precedes `p`
    exact h₁.asymm ⟨s, k, l, hkl, hk, List.prefix_of_prefix_length_le hl hpr (by simpa)⟩

instance : IsStrictOrder TreePath Precedes where
  irrefl := Precedes.irrefl
  trans _ _ _ := Precedes.trans

/-- Any two positions are related by dominance or by precedence. -/
protected theorem trichotomy (p q : TreePath) : p ≤ q ∨ q ≤ p ∨ Precedes p q ∨ Precedes q p := by
  by_cases hpq : p ≤ q
  · exact .inl hpq
  by_cases hqp : q ≤ p
  · exact .inr (.inl hqp)
  rcases lt_trichotomy p.toList q.toList with h | h | h
  · exact .inr (.inr (.inl (precedes_iff_lt_and_not_le.mpr ⟨h, hpq⟩)))
  · exact absurd (TreePath.ext h).le hpq
  · exact .inr (.inr (.inr (precedes_iff_lt_and_not_le.mpr ⟨h, hqp⟩)))

end Precedes

/-! ### Left edges -/

/-- Two positions are left-aligned when their addresses agree once trailing first-daughter steps
are dropped, so that the subtrees at them begin with the same leaf. -/
def LeftAligned (p q : TreePath) : Prop :=
  p.toList.reverse.dropWhile (· == 0) = q.toList.reverse.dropWhile (· == 0)

instance : DecidableRel LeftAligned := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

namespace LeftAligned

variable {p q r : TreePath}

@[refl] protected theorem refl (p : TreePath) : LeftAligned p p := rfl

@[symm] protected theorem symm (h : LeftAligned p q) : LeftAligned q p := Eq.symm h

@[trans] protected theorem trans (h₁ : LeftAligned p q) (h₂ : LeftAligned q r) :
    LeftAligned p r :=
  Eq.trans h₁ h₂

end LeftAligned

private theorem dropWhile_reverse_append_replicate (l : List ℕ) (k : ℕ) :
    (l ++ List.replicate k 0).reverse.dropWhile (· == 0) = l.reverse.dropWhile (· == 0) := by
  rw [List.reverse_append, List.reverse_replicate]
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, List.dropWhile_cons_of_pos rfl, ih]

private theorem exists_eq_reverse_dropWhile_append (l : List ℕ) :
    ∃ k, l = (l.reverse.dropWhile (· == 0)).reverse ++ List.replicate k 0 := by
  refine ⟨(l.reverse.takeWhile (· == 0)).length, ?_⟩
  have h := congrArg List.reverse (List.takeWhile_append_dropWhile (p := (· == 0)) (l := l.reverse))
  rw [List.reverse_append, List.reverse_reverse] at h
  rw [← List.eq_replicate_iff.2 ⟨List.length_reverse, fun x hx ↦ ?_⟩, h]
  exact beq_iff_eq.1 (List.all_eq_true.1 List.all_takeWhile x (List.mem_reverse.1 hx))

/-- Positions are left-aligned exactly when descending through first daughters from each reaches
a common position. -/
theorem leftAligned_iff_exists {p q : TreePath} :
    LeftAligned p q ↔
      ∃ j k, p.toList ++ List.replicate j 0 = q.toList ++ List.replicate k 0 := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_eq_reverse_dropWhile_append p.toList
    obtain ⟨k, hk⟩ := exists_eq_reverse_dropWhile_append q.toList
    refine ⟨k, j, ?_⟩
    rw [hj, hk, h, List.append_assoc, List.append_assoc, List.replicate_append_replicate,
      List.replicate_append_replicate, Nat.add_comm]
  · rintro ⟨j, k, h⟩
    simpa only [LeftAligned, dropWhile_reverse_append_replicate] using
      congrArg (fun l ↦ l.reverse.dropWhile (· == 0)) h

theorem LeftAligned.le_or_ge {p q : TreePath} (h : LeftAligned p q) : p ≤ q ∨ q ≤ p := by
  obtain ⟨j, k, h⟩ := leftAligned_iff_exists.1 h
  have hq : q.toList <+: p.toList ++ List.replicate j 0 := h ▸ List.prefix_append _ _
  exact List.prefix_or_prefix_of_prefix (List.prefix_append _ _) hq

end TreePath

end Core.Order
