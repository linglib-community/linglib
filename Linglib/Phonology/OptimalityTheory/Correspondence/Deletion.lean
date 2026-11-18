module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Coindexation

/-!
# Deletion and insertion

The deletion of a set of positions of a string leaves every other segment coindexed with itself,
so it violates a positional MAX
[once at each deleted position](##OptimalityTheory.Correspondence.Coindexation.maxViolAt_eraseIdxs)
the constraint protects, and
[no DEP](##OptimalityTheory.Correspondence.Coindexation.depViol_eraseIdxs). An inserted segment
bears no index, so an insertion
[violates DEP once](##OptimalityTheory.Correspondence.Coindexation.depViol_insertIdx) and
[no MAX](##OptimalityTheory.Correspondence.Coindexation.maxViol_insertIdx).

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

variable {α : Type*}

/-- The positions of a string indexed by position are the indices of its segments. -/
theorem zipIdx_indexed (s : List α) :
    (indexed s).zipIdx = s.zipIdx.map fun x ↦ (Segment.ofIndex x.1 x.2, x.2) := by
  rw [indexed, List.zipIdx_map]
  suffices h : ∀ k, (s.zipIdx k).zipIdx k = (s.zipIdx k).map fun x ↦ (x, x.2) by
    rw [h 0, List.map_map]
    rfl
  intro k
  induction s generalizing k with
  | nil => rfl
  | cons a s ih => simp [List.zipIdx_cons, ih (k + 1)]

namespace Coindexation

/-- `deletion s t f` relates `s` to the string `t` along `f`: each segment of `t` bears the index
of the position `f j` of `s` it comes from, and the positions of `s` off the range of `f` are
deleted. The segments of `t` need not be those of `s`. -/
def deletion (s t : List α) (f : Fin t.length → Fin s.length) : Coindexation BinaryRole α :=
  ofStrings fun
    | .lhs => indexed s
    | .rhs => List.ofFn fun j ↦ .ofIndex t[j] (f j)

/-! ### Deletion of a set of positions -/

/-- `eraseIdxs s D` is the deletion of the segments at the positions `D` of `s` with every other
segment unchanged, each surviving segment bearing the index of its position in `s`. Positions
past the end of `s` delete nothing. -/
def eraseIdxs (s : List α) (D : Finset ℕ) : Coindexation BinaryRole α :=
  ofStrings fun
    | .lhs => indexed s
    | .rhs => (s.zipIdx.filter fun p ↦ p.2 ∉ D).map fun p ↦ .ofIndex p.1 p.2

section eraseIdxs

variable {s : List α} {D : Finset ℕ}

@[simp] theorem eraseIdxs_string_lhs : (eraseIdxs s D).string .lhs = s := by
  simp [eraseIdxs]

@[simp] theorem eraseIdxs_string_rhs :
    (eraseIdxs s D).string .rhs = (s.zipIdx.filter fun p ↦ p.2 ∉ D).map Prod.fst := by
  simp [eraseIdxs, Function.comp_def]

/-- A segment of `s` has a correspondent after the deletion of `D` exactly when its position is
not in `D`. -/
private theorem forall_not_corresponds_iff {x : α × ℕ} (hx : x ∈ s.zipIdx) :
    (∀ y ∈ (s.zipIdx.filter fun p ↦ p.2 ∉ D).map fun p ↦ Segment.ofIndex p.1 p.2,
      ¬ (Segment.ofIndex x.1 x.2).Corresponds y) ↔ x.2 ∈ D := by
  constructor
  · intro h
    by_contra hD
    exact h _ (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simpa using hD⟩, rfl⟩) (by simp)
  · rintro hD _ hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    rw [Segment.corresponds_ofIndex]
    intro h
    simpa [← h, hD] using (List.mem_filter.1 hp).2

/-- A deletion of the positions `D` violates a positional MAX once for each protected position
in `D`. -/
theorem maxViolAt_eraseIdxs (hD : ∀ k ∈ D, k < s.length) (P : ℕ → Prop) [DecidablePred P] :
    (eraseIdxs s D).maxViolAt P .lhs .rhs = (D.filter P).card := by
  rw [maxViolAt, eraseIdxs, toward_ofStrings, toward_ofStrings, Segment.maxViolAt,
    zipIdx_indexed, List.countP_map]
  rw [List.countP_congr (q := fun x ↦ decide (P x.2 ∧ x.2 ∈ D)) fun x hx ↦ by
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [forall_not_corresponds_iff hx]]
  rw [show (fun x : α × ℕ ↦ decide (P x.2 ∧ x.2 ∈ D)) =
    (fun k ↦ decide (P k ∧ k ∈ D)) ∘ Prod.snd from rfl, ← List.countP_map,
    List.zipIdx_map_snd, ← List.range_eq_range', List.countP_eq_length_filter]
  have : D.filter P = (Finset.range s.length).filter fun k ↦ P k ∧ k ∈ D := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨hk, hP⟩ ↦ ⟨hD k hk, hP, hk⟩, fun ⟨_, hP, hk⟩ ↦ ⟨hk, hP⟩⟩
  rw [this, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card]

/-- A segment of a string indexed by position corresponds with itself. -/
private theorem corresponds_self_of_mem_indexed {l : List α} {x : Segment α}
    (hx : x ∈ indexed l) : x.Corresponds x := by
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  simp

theorem depViol_eraseIdxs : (eraseIdxs s D).depViol .lhs .rhs = 0 := by
  rw [depViol, eraseIdxs, toward_ofStrings, toward_ofStrings, Segment.depViol, Segment.maxViol,
    List.countP_eq_zero]
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
  simpa using ⟨_, List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, rfl⟩, by simp⟩

end eraseIdxs

/-! ### One segment -/

/-- `eraseIdx s i` is the deletion of the segment at position `i` of `s` with every other segment
unchanged. -/
def eraseIdx (s : List α) (i : Fin s.length) : Coindexation BinaryRole α := eraseIdxs s {(i : ℕ)}

/-- `insertIdx s i a` is the insertion of the segment `a`, bearing no index, at position `i` of
`s`. -/
def insertIdx (s : List α) (i : Fin (s.length + 1)) (a : α) : Coindexation BinaryRole α :=
  ofStrings fun
    | .lhs => indexed s
    | .rhs => (indexed s).insertIdx i ⟨a, []⟩

section eraseIdx

variable {s : List α} {i : Fin s.length}

@[simp] theorem eraseIdx_string_lhs : (eraseIdx s i).string .lhs = s := eraseIdxs_string_lhs

private theorem map_fst_filter_zipIdx (l : List α) (k n : ℕ) :
    ((l.zipIdx k).filter fun p ↦ p.2 ∉ ({k + n} : Finset ℕ)).map Prod.fst = l.eraseIdx n := by
  induction l generalizing k n with
  | nil => rfl
  | cons a l ih =>
    cases n with
    | zero =>
      have h : ∀ p ∈ l.zipIdx (k + 1), decide (p.2 ∉ ({k + 0} : Finset ℕ)) = true := fun p hp ↦ by
        have := (List.mem_zipIdx hp).1
        simp only [add_zero, Finset.mem_singleton, decide_eq_true_eq]
        omega
      rw [List.zipIdx_cons, List.filter_cons_of_neg (by simp), List.filter_eq_self.2 h,
        List.zipIdx_map_fst]
      rfl
    | succ n =>
      have := ih (k + 1) n
      simp only [List.zipIdx_cons, List.eraseIdx_cons_succ] at this ⊢
      rw [List.filter_cons_of_pos (by simp), List.map_cons, ← this]
      simp [add_assoc, add_comm 1 n]

@[simp] theorem eraseIdx_string_rhs : (eraseIdx s i).string .rhs = s.eraseIdx i := by
  rw [eraseIdx, eraseIdxs_string_rhs]
  simpa using map_fst_filter_zipIdx s 0 i

theorem maxViolAt_eraseIdx (P : ℕ → Prop) [DecidablePred P] :
    (eraseIdx s i).maxViolAt P .lhs .rhs = if P i then 1 else 0 := by
  rw [eraseIdx, maxViolAt_eraseIdxs (by simp) P, Finset.filter_singleton]
  split_ifs <;> rfl

theorem maxViol_eraseIdx : (eraseIdx s i).maxViol .lhs .rhs = 1 := by
  rw [← maxViolAt_true, maxViolAt_eraseIdx, ite_eq_left trivial]

theorem depViol_eraseIdx : (eraseIdx s i).depViol .lhs .rhs = 0 := depViol_eraseIdxs

end eraseIdx

section insertIdx

variable {s : List α} {i : Fin (s.length + 1)} {a : α}

@[simp] theorem insertIdx_string_lhs : (insertIdx s i a).string .lhs = s := by
  simp [insertIdx]

@[simp] theorem insertIdx_string_rhs : (insertIdx s i a).string .rhs = s.insertIdx i a := by
  simp [insertIdx, List.map_insertIdx]

theorem maxViol_insertIdx : (insertIdx s i a).maxViol .lhs .rhs = 0 := by
  rw [maxViol, insertIdx, toward_ofStrings, toward_ofStrings, Segment.maxViol,
    List.countP_eq_zero]
  intro x hx
  have hi : (i : ℕ) ≤ (indexed s).length := by simpa using i.is_le
  simpa using ⟨x, (List.mem_insertIdx hi).2 (.inr hx), corresponds_self_of_mem_indexed hx⟩

theorem depViol_insertIdx : (insertIdx s i a).depViol .lhs .rhs = 1 := by
  have hi : (i : ℕ) ≤ (indexed s).length := by simpa using i.is_le
  rw [depViol, insertIdx, toward_ofStrings, toward_ofStrings, Segment.depViol, Segment.maxViol,
    (List.perm_insertIdx _ _ hi).countP_eq, List.countP_cons]
  have h : (indexed s).countP (fun x ↦ ∀ y ∈ indexed s, ¬ x.Corresponds y) = 0 :=
    List.countP_eq_zero.2 fun x hx ↦ by
      simpa using ⟨x, hx, corresponds_self_of_mem_indexed hx⟩
  rw [h]
  simp [Segment.Corresponds]

end insertIdx

end Coindexation

end OptimalityTheory.Correspondence
