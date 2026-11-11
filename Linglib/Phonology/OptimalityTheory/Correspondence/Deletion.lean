module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Diagram

/-!
# Deletion and insertion

A deletion relates each position of the shorter string to the position of the longer one it comes
from: its edge from the output is the graph of that map, and its edge from the input the converse.
It [violates a positional MAX](##OptimalityTheory.Correspondence.Diagram.maxViolAt_deletion) at
the protected positions off the range of the map, so deleting the segment at position `i`, along
`Fin.succAbove i`, violates MAX once at `i`, and deleting the positions `D`
[once at each of them](##OptimalityTheory.Correspondence.Diagram.maxViolAt_eraseIdxs). An
insertion is a deletion with its strings exchanged, and
[violates a positional DEP](##OptimalityTheory.Correspondence.Diagram.depViolAt_insertIdx) at the
inserted position. When no other segment changes, neither violates IDENT.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence.Diagram

variable {α : Type*}

/-! ### Deletion along a map of positions -/

/-- `deletion s t f` relates `s` to the string `t` along `f`: each position `j` of `t` corresponds
to position `f j` of `s` alone, and the positions of `s` off the range of `f` are deleted. The
segments of `t` need not be those of `s`, so a deletion may come with changes elsewhere. -/
def deletion (s t : List α) (f : Fin t.length → Fin s.length) : Diagram BinaryRole α :=
  (ofFun t s f).swap

section deletion

variable {s t : List α} {f : Fin t.length → Fin s.length}

@[simp] theorem deletion_form_lhs : (deletion s t f).form .lhs = s := rfl

@[simp] theorem deletion_form_rhs : (deletion s t f).form .rhs = t := rfl

@[simp] theorem deletion_edge_rhs_lhs : (deletion s t f).edge .rhs .lhs = graph f := rfl

@[simp] theorem deletion_edge_lhs_rhs : (deletion s t f).edge .lhs .rhs = (graph f).inv := rfl

theorem deletion_isSymmetric : (deletion s t f).IsSymmetric :=
  (ofFun_isSymmetric _ _ _).swap

/-- A deletion violates a positional MAX at the protected positions off the range of its map. -/
theorem maxViolAt_deletion (P : ℕ → Prop) [DecidablePred P] :
    (deletion s t f).maxViolAt P .lhs .rhs =
      ((Finset.univ.filter fun i : Fin s.length ↦ P i) \ Finset.univ.image f).card :=
  depViolOn_of_graph (rel_graph f) _

theorem depViol_deletion : (deletion s t f).depViol .lhs .rhs = 0 :=
  (depViol_inv _).trans (maxViol_eq_zero_of_graph (rel_graph f))

theorem identViol_deletion_eq_zero_iff [DecidableEq α] :
    (deletion s t f).identViol .lhs .rhs = 0 ↔ ∀ j, t[j] = s[f j] := by
  rw [identViol, identViolFeature, deletion_edge_lhs_rhs, identViol_inv]
  exact identViol_eq_zero_iff_of_graph (rel_graph f) _ _

/-- A deletion along `Fin.succAbove p` violates a positional MAX exactly when the constraint
protects position `p`. -/
theorem maxViolAt_deletion_succAbove (p : Fin (t.length + 1)) (h : t.length + 1 = s.length)
    (P : ℕ → Prop) [DecidablePred P] :
    (deletion s t fun j ↦ (p.succAbove j).cast h).maxViolAt P .lhs .rhs =
      if P p then 1 else 0 := by
  have : Finset.univ.image (fun j ↦ (p.succAbove j).cast h) = {p.cast h}ᶜ := by
    ext k
    rw [Finset.mem_compl, Finset.mem_singleton, ← Fin.cast_inj h.symm, ← ne_eq,
      Fin.cast_cast, Fin.cast_eq_self, ← Fin.exists_succAbove_eq_iff]
    simp [Fin.ext_iff]
  rw [maxViolAt_deletion, this]
  split_ifs with hP <;> simp [sdiff_compl, hP]

end deletion

/-! ### One segment -/

/-- `eraseIdx s i` is the deletion of the segment at position `i` of `s` with every other segment
unchanged. -/
def eraseIdx (s : List α) (i : Fin s.length) : Diagram BinaryRole α :=
  have h : (s.eraseIdx i).length + 1 = s.length := by
    rw [List.length_eraseIdx_of_lt i.2]; have := i.2; omega
  deletion s (s.eraseIdx i) fun j ↦ ((i.cast h.symm).succAbove j).cast h

/-- `insertIdx s i a` is the insertion of the segment `a` at position `i` of `s`, the converse of
the deletion of position `i` from the longer string. -/
def insertIdx (s : List α) (i : Fin (s.length + 1)) (a : α) : Diagram BinaryRole α :=
  (deletion (s.insertIdx i a) s fun j ↦
    (i.succAbove j).cast (List.length_insertIdx_of_le_length i.is_le a).symm).swap

section eraseIdx

variable {s : List α} {i : Fin s.length}

@[simp] theorem eraseIdx_form_lhs : (eraseIdx s i).form .lhs = s := rfl

@[simp] theorem eraseIdx_form_rhs : (eraseIdx s i).form .rhs = s.eraseIdx i := rfl

theorem maxViolAt_eraseIdx (P : ℕ → Prop) [DecidablePred P] :
    (eraseIdx s i).maxViolAt P .lhs .rhs = if P i then 1 else 0 :=
  maxViolAt_deletion_succAbove _ _ P

theorem maxViol_eraseIdx : (eraseIdx s i).maxViol .lhs .rhs = 1 := by
  rw [← maxViolAt_true, maxViolAt_eraseIdx, ite_eq_left trivial]

theorem depViol_eraseIdx : (eraseIdx s i).depViol .lhs .rhs = 0 := depViol_deletion

/-- A deletion of one segment changes no other. -/
theorem identViol_eraseIdx [DecidableEq α] : (eraseIdx s i).identViol .lhs .rhs = 0 := by
  refine identViol_deletion_eq_zero_iff.2 fun j ↦ ?_
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_cast]
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
    ← deletion_isSymmetric.maxViolAt_eq, maxViolAt_deletion_succAbove]

theorem depViol_insertIdx : (insertIdx s i a).depViol .lhs .rhs = 1 := by
  rw [← depViolAt_true, depViolAt_insertIdx, ite_eq_left trivial]

theorem maxViol_insertIdx : (insertIdx s i a).maxViol .lhs .rhs = 0 := by
  rw [insertIdx, maxViol_swap, BinaryRole.swap_lhs, BinaryRole.swap_rhs,
    deletion_isSymmetric.maxViol_eq, depViol_deletion]

/-- An insertion of one segment changes no other. -/
theorem identViol_insertIdx [DecidableEq α] : (insertIdx s i a).identViol .lhs .rhs = 0 := by
  rw [insertIdx, identViol_swap, BinaryRole.swap_lhs, BinaryRole.swap_rhs,
    deletion_isSymmetric.identViol_eq]
  refine identViol_deletion_eq_zero_iff.2 fun j ↦ ?_
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs with hj
  · exact (List.getElem_insertIdx_of_lt hj _).symm
  · exact (List.getElem_insertIdx_of_gt (Nat.lt_succ_of_le (not_lt.1 hj)) _).symm

end insertIdx

/-! ### Deletion of a set of positions -/

/-- `eraseIdxs s D` is the deletion of the segments at the positions `D` of `s` with every other
segment unchanged, each surviving segment corresponding to itself. Positions past the end of `s`
delete nothing. -/
def eraseIdxs (s : List α) (D : Finset ℕ) : Diagram BinaryRole α :=
  let L := s.zipIdx.filter fun p ↦ p.2 ∉ D
  deletion s (L.map Prod.fst) fun j ↦
    have hj : (j : ℕ) < L.length := j.2.trans_eq (List.length_map _)
    ⟨L[j].2, List.snd_lt_of_mem_zipIdx (List.mem_of_mem_filter (L.getElem_mem hj))⟩

section eraseIdxs

variable {s : List α} {D : Finset ℕ}

@[simp] theorem eraseIdxs_form_lhs : (eraseIdxs s D).form .lhs = s := rfl

@[simp] theorem eraseIdxs_form_rhs :
    (eraseIdxs s D).form .rhs = (s.zipIdx.filter fun p ↦ p.2 ∉ D).map Prod.fst := rfl

/-- A deletion of the positions `D` violates a positional MAX once for each protected position
in `D`. -/
theorem maxViolAt_eraseIdxs (hD : ∀ k ∈ D, k < s.length) (P : ℕ → Prop) [DecidablePred P] :
    (eraseIdxs s D).maxViolAt P .lhs .rhs = (D.filter P).card := by
  rw [eraseIdxs, maxViolAt_deletion]
  convert_to ((Finset.univ.filter fun i : Fin s.length ↦ P i) \
    Finset.univ.filter fun i ↦ (i : ℕ) ∉ D).card = _
  · congr 2
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Fin.ext_iff,
      Fin.exists_iff, List.length_map]
    refine (List.exists_mem_iff_getElem (p := fun p : α × ℕ ↦ p.2 = (i : ℕ))).symm.trans ?_
    simp [List.mem_zipIdx_iff_getElem?]
  · rw [← Finset.card_map Fin.valEmbedding]
    congr 1
    ext k
    simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not, Fin.valEmbedding_apply]
    exact ⟨fun ⟨i, ⟨hP, hi⟩, hk⟩ ↦ hk ▸ ⟨hi, hP⟩, fun ⟨hk, hP⟩ ↦ ⟨⟨k, hD k hk⟩, ⟨hP, hk⟩, rfl⟩⟩

theorem depViol_eraseIdxs : (eraseIdxs s D).depViol .lhs .rhs = 0 := depViol_deletion

/-- A deletion of a set of positions changes no other segment. -/
theorem identViol_eraseIdxs [DecidableEq α] : (eraseIdxs s D).identViol .lhs .rhs = 0 := by
  refine identViol_deletion_eq_zero_iff.2 fun j ↦ ?_
  simp only [Fin.getElem_fin, List.getElem_map]
  exact (List.fst_eq_of_mem_zipIdx (List.mem_of_mem_filter (List.getElem_mem _))).trans (by simp)

end eraseIdxs

end OptimalityTheory.Correspondence.Diagram
