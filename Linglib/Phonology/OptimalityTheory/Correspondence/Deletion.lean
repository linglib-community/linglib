module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic

/-!
# Deletion and insertion of one segment

The insertion of a segment at position `i` of a string relates each position to the one it moves
to, along `Fin.succAbove`, and the deletion of the segment at position `i` is the converse. An
insertion therefore violates DEP once and a deletion MAX once, each at `i`, and when no other
segment changes neither violates IDENT.

## Main definitions

* `Correspondence.deletion`: the deletion of the segment at a position, the other segments free
  to change.
* `Correspondence.eraseIdx`, `Correspondence.insertIdx`: the deletion and the insertion of one
  segment, the other segments unchanged.

## Main results

* `Correspondence.maxViolAt_deletion`, `Correspondence.depViolAt_insertIdx`: a deletion violates
  a positional MAX, and an insertion a positional DEP, exactly when the constraint covers its
  position.
* `Correspondence.identViol_eraseIdx`, `Correspondence.identViol_insertIdx`: neither changes
  another segment.

## References

* [mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

variable {α : Type*}

/-! ### Deletion -/

/-- `deletion s t i h` relates `s` to the string `t` one segment shorter by skipping position `i`
of `s`, each position `j` of `t` corresponding to position `i.succAbove j` of `s`. The segments of
`t` need not be those of `s`, so a deletion may come with changes elsewhere. -/
def deletion (s t : List α) (i : Fin s.length) (h : s.length = t.length + 1) :
    Correspondence BinaryRole α :=
  (ofFun t s fun j ↦ ((i.cast h).succAbove j).cast h.symm).swap

/-- `eraseIdx s i` is the deletion of the segment at position `i` of `s` with every other segment
unchanged. -/
def eraseIdx (s : List α) (i : Fin s.length) : Correspondence BinaryRole α :=
  deletion s (s.eraseIdx i) i (by have := i.2; rw [List.length_eraseIdx_of_lt i.2]; omega)

/-- `insertIdx s i a` is the insertion of the segment `a` at position `i` of `s`, the converse of
the deletion of position `i` from the longer string. -/
def insertIdx (s : List α) (i : Fin (s.length + 1)) (a : α) : Correspondence BinaryRole α :=
  (deletion (s.insertIdx i a) s (i.cast (List.length_insertIdx_of_le_length i.is_le a).symm)
    (List.length_insertIdx_of_le_length i.is_le a)).swap

section deletion

variable {s t : List α} {i : Fin s.length} {h : s.length = t.length + 1}

@[simp] theorem deletion_form_lhs : (deletion s t i h).form .lhs = s := rfl

@[simp] theorem deletion_form_rhs : (deletion s t i h).form .rhs = t := rfl

/-- Each position `j` of the shorter string corresponds to position `i.succAbove j` of the longer
alone. -/
theorem mem_deletion_edge {j : Fin t.length} {k : Fin s.length} :
    (j, k) ∈ (deletion s t i h).edge .rhs .lhs ↔ ((i.cast h).succAbove j).cast h.symm = k :=
  mem_ofFun_edge (f := fun j ↦ ((i.cast h).succAbove j).cast h.symm)

theorem deletion_isSymmetric : (deletion s t i h).IsSymmetric :=
  (ofFun_isSymmetric _ _ _).swap

/-- A deletion violates a positional MAX exactly when the constraint protects the deleted
position. -/
theorem maxViolAt_deletion (P : ℕ → Prop) [DecidablePred P] :
    (deletion s t i h).maxViolAt P .lhs .rhs = if P i then 1 else 0 := by
  rw [deletion_isSymmetric.maxViolAt_eq .rhs .lhs, depViolAt_of_graph fun _ _ ↦ mem_deletion_edge]
  have : Finset.univ.image (fun j ↦ ((i.cast h).succAbove j).cast h.symm) = {i}ᶜ := by
    ext k
    rw [Finset.mem_compl, Finset.mem_singleton, ← Fin.cast_inj h, ← ne_eq,
      ← Fin.exists_succAbove_eq_iff]
    simp [Fin.ext_iff]
  split_ifs with hP <;> simp [this, sdiff_compl, hP]

/-- A deletion violates MAX once. -/
theorem maxViol_deletion : (deletion s t i h).maxViol .lhs .rhs = 1 := by
  rw [← maxViolAt_true, maxViolAt_deletion, ite_eq_left trivial]

/-- A deletion does not violate DEP. -/
theorem depViol_deletion : (deletion s t i h).depViol .lhs .rhs = 0 := by
  rw [← deletion_isSymmetric.maxViol_eq]
  exact maxViol_eq_zero_of_graph fun _ _ ↦ mem_deletion_edge

end deletion

/-! ### Without other changes -/

section eraseIdx

variable {s : List α} {i : Fin s.length}

@[simp] theorem eraseIdx_form_lhs : (eraseIdx s i).form .lhs = s := rfl

@[simp] theorem eraseIdx_form_rhs : (eraseIdx s i).form .rhs = s.eraseIdx i := rfl

theorem maxViolAt_eraseIdx (P : ℕ → Prop) [DecidablePred P] :
    (eraseIdx s i).maxViolAt P .lhs .rhs = if P i then 1 else 0 :=
  maxViolAt_deletion P

theorem maxViol_eraseIdx : (eraseIdx s i).maxViol .lhs .rhs = 1 := maxViol_deletion

theorem depViol_eraseIdx : (eraseIdx s i).depViol .lhs .rhs = 0 := depViol_deletion

/-- A deletion of one segment changes no other. -/
theorem identViol_eraseIdx [DecidableEq α] : (eraseIdx s i).identViol .lhs .rhs = 0 := by
  rw [eraseIdx, ← deletion_isSymmetric.identViol_eq,
    identViol_eq_zero_iff_of_graph fun _ _ ↦ mem_deletion_edge]
  intro j
  simp only [deletion_form_rhs, deletion_form_lhs, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_cast]
  split_ifs with hj
  · exact List.getElem_eraseIdx_of_lt j.2 hj
  · exact List.getElem_eraseIdx_of_ge j.2 (not_lt.1 hj)

end eraseIdx

section insertIdx

variable {s : List α} {i : Fin (s.length + 1)} {a : α}

@[simp] theorem insertIdx_form_lhs : (insertIdx s i a).form .lhs = s := rfl

@[simp] theorem insertIdx_form_rhs : (insertIdx s i a).form .rhs = s.insertIdx i a := rfl

/-- An insertion violates a positional DEP exactly when the constraint covers the inserted
position. -/
theorem depViolAt_insertIdx (P : ℕ → Prop) [DecidablePred P] :
    (insertIdx s i a).depViolAt P .lhs .rhs = if P i then 1 else 0 := by
  rw [insertIdx, depViolAt_swap, BinaryRole.swap_lhs, BinaryRole.swap_rhs,
    ← deletion_isSymmetric.maxViolAt_eq, maxViolAt_deletion, Fin.val_cast]

/-- An insertion violates DEP once. -/
theorem depViol_insertIdx : (insertIdx s i a).depViol .lhs .rhs = 1 := by
  rw [← depViolAt_true, depViolAt_insertIdx, ite_eq_left trivial]

/-- An insertion does not violate MAX. -/
theorem maxViol_insertIdx : (insertIdx s i a).maxViol .lhs .rhs = 0 :=
  maxViol_eq_zero_of_graph fun _ _ ↦ mem_deletion_edge

/-- An insertion of one segment changes no other. -/
theorem identViol_insertIdx [DecidableEq α] : (insertIdx s i a).identViol .lhs .rhs = 0 := by
  refine (identViol_eq_zero_iff_of_graph fun _ _ ↦ mem_deletion_edge).2 fun j ↦ ?_
  simp only [deletion_form_rhs, deletion_form_lhs, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_cast]
  split_ifs with hj
  · exact (List.getElem_insertIdx_of_lt hj _).symm
  · exact (List.getElem_insertIdx_of_gt (Nat.lt_succ_of_le (not_lt.1 hj)) _).symm

end insertIdx

end OptimalityTheory.Correspondence
