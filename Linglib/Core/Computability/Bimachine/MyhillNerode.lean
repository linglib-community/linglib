/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Finite.Set
public import Mathlib.Basic.Finite.Prod
public import Linglib.Core.Computability.Bimachine
public import Linglib.Core.Computability.Mealy.MyhillNerode

/-!
# The Myhill–Nerode theorem for bimachines

A length-preserving function whose output can depend on input unboundedly far to its right, as
in bidirectional harmony, has infinitely many residuals. It is computed by a letter-to-letter
bimachine if and only if it has finitely many synchronous residuals and coresiduals
(`isLetterToLetterBimachineComputable_iff_syncResidual`). Over a finite alphabet that is every
length-preserving bimachine-computable function
(`isLetterToLetterBimachineComputable_iff_isBimachineComputable`), while reversal is computed by
no bimachine at all (`not_isBimachineComputable_reverse`).

## References

* [S. Eilenberg, *Automata, Languages and Machines, Volume A* (1974)][eilenberg-1974]
* [C. Reutenauer and M. P. Schützenberger, *Minimization of Rational Word Functions*
  (1991)][reutenauer-schutzenberger-1991]: the canonical bimachine, whose length-preserving
  stratum is the characterization here
* [E. Filiot and P. A. Reynier, *Transducers, Logic and Algebra for Functions of Finite Words*
  (2016)][filiot-reynier-2016]: a survey of the canonical bimachine
-/

@[expose] public section

open Function

variable {α β : Type*}

section Bimachine

variable {L R : Type*} (B : Bimachine L R α β)

theorem Bimachine.syncResidual_run (w : B.LetterToLetter) (x : List α) :
    syncResidual B.run x = (B.emitted (B.lState x) · B.rInit) :=
  funext fun v ↦ by
    rw [syncResidual, w.run_eq, B.emitted_append, List.drop_left' (w.length_emitted ..)]
    rfl

theorem Bimachine.syncCoresidual_run (w : B.LetterToLetter) (y : List α) :
    syncCoresidual B.run y = (B.emitted B.lInit · (B.rState y)) :=
  funext fun u ↦ by
    rw [syncCoresidual, w.run_eq, B.emitted_append, List.take_left' (w.length_emitted ..)]
    rfl

/-! ### Necessity -/

theorem IsLetterToLetterBimachineComputable.finite_range_syncResidual {f : List α → List β}
    (hf : IsLetterToLetterBimachineComputable f) : (Set.range (syncResidual f)).Finite := by
  obtain ⟨L, _, R, _, B, ⟨w⟩, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range fun l v ↦ B.emitted l v B.rInit)
    (Set.range_subset_iff.mpr fun x ↦ ⟨_, (B.syncResidual_run w x).symm⟩)

theorem IsLetterToLetterBimachineComputable.finite_range_syncCoresidual {f : List α → List β}
    (hf : IsLetterToLetterBimachineComputable f) : (Set.range (syncCoresidual f)).Finite := by
  obtain ⟨L, _, R, _, B, ⟨w⟩, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range fun r u ↦ B.emitted B.lInit u r)
    (Set.range_subset_iff.mpr fun y ↦ ⟨B.rState y, (B.syncCoresidual_run w y).symm⟩)

/-! ### Sufficiency -/

/-- A length-preserving `f` with finite left and right summaries, congruent in their
respective scan directions and jointly determining each output cell, is
bimachine-computable. -/
theorem isLetterToLetterBimachineComputable_of_stateSummaries
    {f : List α → List β} {L R : Type*} [Fintype L] [Fintype R]
    (stateL : List α → L) (δL : L → α → L) (stateR : List α → R) (δR : R → α → R)
    (out : L → α → R → β)
    (hδL : ∀ u x, stateL (u ++ [x]) = δL (stateL u) x)
    (hδR : ∀ x w, stateR (x :: w) = δR (stateR w) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (stateL u) x (stateR w)))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsLetterToLetterBimachineComputable f := by
  set B : Bimachine L R α β :=
    { lInit := stateL [], lStep := δL, rInit := stateR [], rStep := δR,
      output := fun l a r ↦ [out l a r] }
  let w : B.LetterToLetter := { cell := out, output_eq := fun _ _ _ ↦ rfl }
  suffices B.run = f from this ▸ B.isLetterToLetterBimachineComputable ⟨w⟩
  have hL : ∀ u, B.lState u = stateL u := foldl_eq_of_append_singleton hδL []
  have hR : ∀ w, B.rState w = stateR w := fun w ↦ by
    induction w with
    | nil => rfl
    | cons x w ih => rw [B.rState_cons, ih, hδR]
  funext xs
  refine List.ext_getElem? fun i ↦ ?_
  rw [w.getElem?_run, getElem?_eq_of_append_cons hlen hout]
  simp only [hL, hR]
  rfl

theorem isLetterToLetterBimachineComputable_of_syncResidual {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length)
    (hfinL : (Set.range (syncResidual f)).Finite)
    (hfinR : (Set.range (syncCoresidual f)).Finite) :
    IsLetterToLetterBimachineComputable f := by
  have := hfinL.fintype
  have := hfinR.fintype
  choose repL hrepL using fun r : Set.range (syncResidual f) ↦ r.prop
  choose repR hrepR using fun s : Set.range (syncCoresidual f) ↦ s.prop
  refine isLetterToLetterBimachineComputable_of_stateSummaries
    (fun u ↦ ⟨syncResidual f u, Set.mem_range_self u⟩)
    (fun r x ↦ ⟨fun v ↦ (r.val (x :: v)).drop 1, by
      obtain ⟨u, hu⟩ := r.prop
      exact ⟨u ++ [x], by rw [syncResidual_append_singleton f, hu]⟩⟩)
    (fun w ↦ ⟨syncCoresidual f w, Set.mem_range_self w⟩)
    (fun s x ↦ ⟨fun u ↦ (s.val (u ++ [x])).take u.length, by
      obtain ⟨w, hw⟩ := s.prop
      exact ⟨x :: w, by rw [syncCoresidual_cons, hw]⟩⟩)
    (fun r x s ↦ (f (repL r ++ x :: repR s))[(repL r).length]'(by
      rw [hlen]
      simp))
    (fun u x ↦ Subtype.ext (syncResidual_append_singleton f u x))
    (fun x w ↦ Subtype.ext (syncCoresidual_cons f x w))
    (fun u x w ↦ ?_) hlen
  set r : Set.range (syncResidual f) := ⟨syncResidual f u, Set.mem_range_self u⟩
  set s : Set.range (syncCoresidual f) := ⟨syncCoresidual f w, Set.mem_range_self w⟩
  have hres : syncResidual f (repL r) = syncResidual f u := hrepL r
  have hcores : syncCoresidual f (repR s) = syncCoresidual f w := hrepR s
  calc (f (u ++ x :: w))[u.length]?
      = (syncResidual f u (x :: w))[0]? := (getElem?_syncResidual_cons f u x w).symm
    _ = (syncResidual f (repL r) (x :: w))[0]? := by rw [hres]
    _ = (f (repL r ++ x :: w))[(repL r).length]? := getElem?_syncResidual_cons f _ x w
    _ = (syncCoresidual f w (repL r ++ [x]))[(repL r).length]? :=
        (getElem?_syncCoresidual_append f _ x w).symm
    _ = (syncCoresidual f (repR s) (repL r ++ [x]))[(repL r).length]? := by rw [hcores]
    _ = (f (repL r ++ x :: repR s))[(repL r).length]? := getElem?_syncCoresidual_append f _ x _
    _ = some ((f (repL r ++ x :: repR s))[(repL r).length]'(by rw [hlen]; simp)) :=
        List.getElem?_eq_getElem _

end Bimachine

/-- A function is computed by a letter-to-letter bimachine iff it is length-preserving with finitely
many synchronous residuals and finitely many coresiduals, which is the Myhill–Nerode theorem for
bimachines. -/
theorem isLetterToLetterBimachineComputable_iff_syncResidual {f : List α → List β} :
    IsLetterToLetterBimachineComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (Set.range (syncResidual f)).Finite
        ∧ (Set.range (syncCoresidual f)).Finite :=
  ⟨fun hf ↦ ⟨hf.length_eq, hf.finite_range_syncResidual, hf.finite_range_syncCoresidual⟩,
   fun h ↦ isLetterToLetterBimachineComputable_of_syncResidual h.1 h.2.1 h.2.2⟩


/-! ### Resynchronization

Cut the input of a bimachine as `x ++ v`. The output is what `x` and the final left block emit,
given the right state over `v`, followed by what `v` and the final right block emit, given the left
state over `x`. When the function preserves length, how far the first part runs ahead of `x` is
fixed by those two states alone, so the synchronous residual of `x` is fixed by its left state and
finitely many short words, and a letter-to-letter machine computes the function. -/

namespace Bimachine

variable {L R : Type*} (B : Bimachine L R α β)

/-- What `B` emits for the prefix `x` of a word whose suffix leaves the right automaton in `r`. -/
private def leftPart (x : List α) (r : R) : List β :=
  B.finalLeft (B.rStateFrom r x) ++ B.emitted B.lInit x r

/-- What `B` emits for the suffix `v` of a word whose prefix leaves the left automaton in `l`. -/
private def rightPart (l : L) (v : List α) : List β :=
  B.emitted l v B.rInit ++ B.finalRight (B.lStateFrom l v)

private theorem run_append_eq (x v : List α) :
    B.run (x ++ v) = leftPart B x (B.rState v) ++ rightPart B (B.lState x) v := by
  simp [run, leftPart, rightPart, rState, lState, rStateFrom_append, lStateFrom_append,
    emitted_append]

private theorem exists_mem_output {b : β} {l : L} {x : List α} {r : R} (h : b ∈ B.emitted l x r) :
    ∃ l a r, b ∈ B.output l a r := by
  induction x generalizing l with
  | nil => simp at h
  | cons a x ih =>
    rw [emitted_cons, List.mem_append] at h
    exact h.elim (fun h ↦ ⟨_, _, _, h⟩) ih

end Bimachine

open Bimachine in
/-- Over a finite alphabet, a length-preserving bimachine-computable function has finitely many
synchronous residuals. -/
theorem IsBimachineComputable.finite_range_syncResidual [Finite α] {f : List α → List β}
    (hf : IsBimachineComputable f) (hlen : ∀ x, (f x).length = x.length) :
    (Set.range (syncResidual f)).Finite := by
  classical
  obtain ⟨L, _, R, _, B, rfl⟩ := hf
  let rep : R → List α := fun r ↦ if h : ∃ v, B.rState v = r then h.choose else []
  have hrep (v : List α) : B.rState (rep (B.rState v)) = B.rState v := by
    have h : ∃ w, B.rState w = B.rState v := ⟨v, rfl⟩
    simp only [rep, h, ↓reduceDIte]
    exact h.choose_spec
  have hsum (x v : List α) : (leftPart B x (B.rState v)).length
      + (rightPart B (B.lState x) v).length = x.length + v.length := by
    simpa [run_append_eq] using hlen (x ++ v)
  let Λ : Set β := (⋃ p : L × α × R, {b | b ∈ B.output p.1 p.2.1 p.2.2})
    ∪ ⋃ r : R, {b | b ∈ B.finalLeft r}
  have hΛ : Λ.Finite :=
    (Set.finite_iUnion fun _ ↦ List.finite_toSet _).union
      (Set.finite_iUnion fun _ ↦ List.finite_toSet _)
  let D := Finset.univ.sup fun r ↦ (rep r).length
  let W : Set (List β) := {w | w.length ≤ D ∧ ∀ b ∈ w, b ∈ Λ}
  have hW : W.Finite := by
    have := hΛ.to_subtype
    refine ((List.finite_length_le Λ D).image (List.map Subtype.val)).subset fun w hw ↦ ?_
    lift w to List Λ using hw.2
    exact ⟨w, by simpa using hw.1, rfl⟩
  let S (x : List α) (r : R) : List β := (leftPart B x (B.rState (rep r))).drop x.length
  let k (l : L) (r : R) : ℕ := (rightPart B l (rep r)).length - (rep r).length
  let Φ (p : L × (R → List β)) (v : List α) : List β :=
    p.2 (B.rState v) ++ (rightPart B p.1 v).drop (k p.1 (B.rState v))
  refine (((Set.toFinite (Set.univ : Set L)).prod (Set.Finite.pi fun _ ↦ hW)).image Φ).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨(B.lState x, S x), ⟨trivial, fun r _ ↦ ⟨?_, fun b hb ↦ ?_⟩⟩, funext fun v ↦ ?_⟩
  · have := hsum x (rep r)
    have hD : (rep r).length ≤ D := Finset.le_sup (f := fun r ↦ (rep r).length) (Finset.mem_univ r)
    simp only [S, List.length_drop]
    omega
  · rcases List.mem_append.mp (List.mem_of_mem_drop hb) with h | h
    · exact .inr (Set.mem_iUnion.mpr ⟨_, h⟩)
    · obtain ⟨l, a, r, h⟩ := B.exists_mem_output h
      exact .inl (Set.mem_iUnion.mpr ⟨(l, a, r), h⟩)
  · have := hsum x (rep (B.rState v))
    rw [hrep] at this
    simp only [Φ, S, k, hrep, Function.syncResidual, run_append_eq, List.drop_append]
    congr 2
    omega

/-- Over a finite alphabet, a length-preserving bimachine-computable function has finitely many
synchronous coresiduals. -/
theorem IsBimachineComputable.finite_range_syncCoresidual [Finite α] {f : List α → List β}
    (hf : IsBimachineComputable f) (hlen : ∀ x, (f x).length = x.length) :
    (Set.range (syncCoresidual f)).Finite := by
  have hlen' (x : List α) : (List.revConj f x).length = x.length := by simp [List.revConj, hlen]
  refine ((hf.revConj.finite_range_syncResidual hlen').image
    fun g u ↦ (g u.reverse).reverse).subset ?_
  rintro _ ⟨y, rfl⟩
  refine ⟨_, ⟨y.reverse, rfl⟩, funext fun u ↦ ?_⟩
  simp only [Function.syncCoresidual, Function.syncResidual, List.revConj, List.reverse_append,
    List.reverse_reverse, List.length_reverse, List.drop_reverse, hlen, List.length_append]
  congr 1
  omega

/-- Over a finite alphabet, a function is computed by a letter-to-letter bimachine exactly when it
is bimachine-computable and preserves length ([eilenberg-1974] Th. XI.7.1). -/
theorem isLetterToLetterBimachineComputable_iff_isBimachineComputable [Finite α]
    {f : List α → List β} :
    IsLetterToLetterBimachineComputable f ↔
      IsBimachineComputable f ∧ ∀ x, (f x).length = x.length :=
  ⟨fun h ↦ ⟨.of_letterToLetter h, h.length_eq⟩, fun ⟨hf, hlen⟩ ↦
    isLetterToLetterBimachineComputable_of_syncResidual hlen (hf.finite_range_syncResidual hlen)
      (hf.finite_range_syncCoresidual hlen)⟩

/-- The finite alphabet is needed: over `ℕ`, the shift `x :: xs ↦ xs ++ [0]` is bimachine-computable
and preserves length, but a letter-to-letter machine would have to remember the second letter. -/
theorem exists_isBimachineComputable_not_isLetterToLetterBimachineComputable :
    ∃ f : List ℕ → List ℕ, IsBimachineComputable f ∧ (∀ x, (f x).length = x.length) ∧
      ¬ IsLetterToLetterBimachineComputable f := by
  let B : Bimachine Bool Unit ℕ ℕ :=
    { lInit := false, lStep := fun _ _ ↦ true, rInit := (), rStep := fun _ _ ↦ (),
      output := fun l a _ ↦ if l then [a] else [], finalRight := fun l ↦ if l then [0] else [] }
  have hl (xs : List ℕ) : B.lStateFrom true xs = true := by
    induction xs with
    | nil => rfl
    | cons _ _ ih => exact ih
  have he (xs : List ℕ) : B.emitted true xs () = xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simpa [B] using ih
  have hrun (a : ℕ) (xs : List ℕ) : B.run (a :: xs) = xs ++ [0] := by
    simp [Bimachine.run, Bimachine.lState, B, hl, he]
  refine ⟨B.run, B.isBimachineComputable, fun x ↦ ?_, fun h ↦ ?_⟩
  · cases x <;> simp [hrun]
    rfl
  refine Set.infinite_range_of_injective (f := fun n : ℕ ↦ syncCoresidual B.run [n])
    (fun m n hmn ↦ ?_) (h.finite_range_syncCoresidual.subset
      (Set.range_subset_iff.mpr fun n ↦ ⟨[n], rfl⟩))
  simpa [Function.syncCoresidual, hrun] using congrFun hmn [0]

/-- Reversal is not computed by any finite bimachine: its synchronous residuals are distinct. -/
theorem not_isBimachineComputable_reverse :
    ¬ IsBimachineComputable (List.reverse : List Bool → List Bool) := fun h ↦ by
  refine Set.infinite_range_of_injective
    (f := fun n : ℕ ↦ syncResidual List.reverse (List.replicate n true)) (fun m n hmn ↦ ?_)
    ((h.finite_range_syncResidual fun _ ↦ List.length_reverse).subset
      (Set.range_subset_iff.mpr fun n ↦ ⟨_, rfl⟩))
  have := congrArg (List.count true) (congrFun hmn (List.replicate (m + n) false))
  simpa [Function.syncResidual, List.drop_append, List.count_replicate] using this
