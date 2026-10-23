/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Basic
public import Linglib.Core.Computability.Bimachine
public import Linglib.Core.Computability.Subsequential
public import Linglib.Core.Data.List.TakeDrop

/-!
# Side dependence for string functions

A string function `f` depends boundedly on a side when one margin `N` serves every output
coordinate `i`: the output at `i` factors (`Function.FactorsThrough`) through the part of the
input not `N`-far from `i` on that side, the suffix from `i - N` or the prefix through `i + N`
(`Edge.window`). Unbounded dependence on both
sides at one target, and the stronger demand for both sides at once, are witnessed by
`flankWord`: a target in a run of filler between two flanks that can be edited separately. The
non-interacting bimachines, whose cell output is an order-independent union of one-sided
change rules over the identity, are the weakly deterministic class; a map that needs both sides
at once escapes them.

## Main definitions

* `LeftDetermined f i`: output coordinate `i` is fixed by the input prefix through `i`
* `BoundedDependence f s`, `UnboundedDependence f s`: whether one margin caps the
  influence of side `s` at every output coordinate
* `TwoSidedUnboundedDependence f`: for every `d`, one base word carries a target
  flipped by far perturbations on either side
* `RequiresBothSides f`: the target is changed, and either far perturbation alone
  reverts it
* `OneSidedChanges f`: every changed cell is determined by one side of its input
  alone
* `flankWord x fill y n`: a target buried in a filler run with editable flanks
* `Bimachine.NonInteraction`, `Bimachine.IsNonInteracting`: the cell output decomposed
  as an order-independent union of one-sided change-rules over the identity
* `IsNonInteractingBimachineComputable f`: `f` is computed by some non-interacting
  finite bimachine

## Main theorems

* `unboundedDependence_iff`: every margin fails at some output coordinate
* `RequiresBothSides.of_flanks`: the three-map witness template — a map is excluded
  by three target-cell observations
* `IsNonInteractingBimachineComputable.oneSidedChanges`: a non-interacting bimachine
  changes each cell from one side
* `IsLeftSubsequential.boundedDependence_right`, `IsRightSubsequential.boundedDependence_left`:
  a length-preserving subsequential function depends boundedly on the input ahead of its scan
* `TwoSidedUnboundedDependence.not_isSubsequential`: two-sided unbounded dependence rules out
  a subsequential function in either direction
* `Mealy.leftDetermined`, `Mealy.boundedDependence_right`: a sequential machine is
  prefix-determined at every coordinate
* `RequiresBothSides.not_isNonInteractingBimachineComputable`: a map whose target needs
  both sides at once is computed by no non-interacting bimachine
* `setOf_isNonInteractingBimachineComputable_ssubset`: the non-interacting class is
  proper inside the bimachine-computable functions

## Implementation notes

The coordinate predicates index the output coordinate and the input window
separately, which is informative for length-preserving functions; for block-emitting
transducers the two drift apart. `BoundedDependence` is the positive primitive;
`unboundedDependence_iff` recovers the margin-indexed witness form, and unpacking the
negated dependence yields word-pair witnesses. The forms are margin-indexed rather than
fixed-index because a fixed target has only finitely many positions to its left. The
predicates place no in-range guard on target coordinates, since for length-preserving maps
an out-of-range coordinate is `none` on both sides of any perturbation.

A window is a list, not a set of positions, so the dependence predicates factor through it
without asking the two inputs to have the same length: a suffix from `i - N` that two words
share fixes their lengths whenever it is nonempty. The perturbation predicates keep the length
condition, since the BMRS locality theorems read `w.length`.

## References

* [meinhardt-mai-bakovic-mccollum-2024]
-/

@[expose] public section

open Function

variable {α β : Type*} {f : List α → List β}

/-! ### The dependence lattice -/

/-- Output coordinate `i` is fixed by the input prefix through `i`. -/
def LeftDetermined (f : List α → List β) (i : ℕ) : Prop :=
  FactorsThrough (fun u ↦ (f u)[i]?) (List.take (i + 1))

/-- An equal-length variant of `base` differing only beyond the `d`-margin of target
`i` on side `s`. -/
def IsFarPerturbation (base u : List α) (i d : ℕ) (s : Edge) : Prop :=
  u.length = base.length ∧ s.window i d base = s.window i d u

/-- `f` depends boundedly on side `s` when a single margin caps, at every output
coordinate, how far input on side `s` can matter. -/
def BoundedDependence (f : List α → List β) (s : Edge) : Prop :=
  ∃ N, ∀ i, FactorsThrough (fun u ↦ (f u)[i]?) (s.window i N)

/-- `f` depends unboundedly on side `s`. -/
def UnboundedDependence (f : List α → List β) (s : Edge) : Prop :=
  ¬ BoundedDependence f s

@[simp] theorem not_unboundedDependence_iff {s : Edge} :
    ¬ UnboundedDependence f s ↔ BoundedDependence f s := not_not

/-- Unbounded dependence, coordinate-wise, says that every margin fails at some output
coordinate. -/
theorem unboundedDependence_iff {s : Edge} :
    UnboundedDependence f s ↔
      ∀ N, ∃ i, ¬ FactorsThrough (fun u ↦ (f u)[i]?) (s.window i N) := by
  simp only [UnboundedDependence, BoundedDependence, not_exists, not_forall]

theorem BoundedDependence.right_of_leftDetermined (h : ∀ i, LeftDetermined f i) :
    BoundedDependence f .right := ⟨0, h⟩

/-- For every `d`, one base word carries a target whose output flips under a far
perturbation on either side. -/
def TwoSidedUnboundedDependence (f : List α → List β) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ (f base)[i]? ≠ (f u)[i]?

theorem TwoSidedUnboundedDependence.unboundedDependence
    (h : TwoSidedUnboundedDependence f) (s : Edge) : UnboundedDependence f s :=
  unboundedDependence_iff.mpr fun N ↦
    have ⟨_, i, _, hw⟩ := h N
    have ⟨_, ⟨_, hag⟩, hne⟩ := hw s
    ⟨i, fun hft ↦ hne (hft hag)⟩

/-- `f` requires both sides when some target changes under `f` yet perturbing either
far side reverts it to the identity. -/
def RequiresBothSides (f : List α → List α) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧ (f base)[i]? ≠ base[i]? ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ u[i]? = base[i]? ∧ (f u)[i]? = u[i]?

/-- Every changed cell is determined by the input on one side of it alone — which
side may vary from cell to cell. -/
def OneSidedChanges (f : List α → List α) : Prop :=
  ∀ (w : List α) (i : ℕ), (f w)[i]? ≠ w[i]? →
    ∃ s : Edge, ∀ ⦃u : List α⦄, w.length = u.length →
      s.window i 0 w = s.window i 0 u → (f w)[i]? = (f u)[i]?

theorem RequiresBothSides.not_oneSidedChanges {f : List α → List α}
    (hf : RequiresBothSides f) : ¬ OneSidedChanges f := fun hs ↦
  have ⟨base, i, _, hchange, hw⟩ := hf 0
  have ⟨s, hdet⟩ := hs base i hchange
  have ⟨_, ⟨hlen, hag⟩, hsym, hrev⟩ := hw s
  hchange ((hdet hlen.symm hag).trans (hrev.trans hsym))

theorem RequiresBothSides.twoSidedUnboundedDependence {f : List α → List α}
    (hf : RequiresBothSides f) : TwoSidedUnboundedDependence f := fun d ↦
  have ⟨base, i, hi, hchange, hw⟩ := hf d
  ⟨base, i, hi, fun s ↦
    have ⟨u, hp, hsym, hrev⟩ := hw s
    ⟨u, hp, fun h ↦ hchange (h.trans (hrev.trans hsym))⟩⟩

section FlankWitness

variable {x fill y a : α} {n k : ℕ} {p : α → Bool}

/-! ### The flank-witness template

The recurring witness family for two-sided unboundedness: a target buried in a filler
run, with independently editable flanks. `RequiresBothSides.of_flanks` packages the
whole assembly — a map is excluded by three target-cell observations: the base image
leaves the filler, and either single-flank perturbation restores it. -/

/-- `flankWord x fill y n` is the word `x`, then `n` copies of `fill`, then `y`. -/
def flankWord (x fill y : α) (n : ℕ) : List α := x :: (List.replicate n fill ++ [y])

@[simp] theorem length_flankWord :
    (flankWord x fill y n).length = n + 2 := by
  simp [flankWord]

theorem getElem?_flankWord :
    (flankWord x fill y n)[k]? = if k = 0 then some x else if k = n + 1 then some y
      else if k < n + 2 then some fill else none := by
  simp only [flankWord, List.getElem?_cons, List.getElem?_append, List.getElem?_replicate,
    List.length_replicate, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

@[simp] theorem getElem?_flankWord_zero :
    (flankWord x fill y n)[0]? = some x := rfl

@[simp] theorem head?_flankWord : (flankWord x fill y n).head? = some x := rfl

@[simp] theorem getElem?_flankWord_last :
    (flankWord x fill y n)[n + 1]? = some y := by
  rw [getElem?_flankWord]; simp

theorem getElem?_flankWord_mid (h₁ : 0 < k) (h₂ : k ≤ n) :
    (flankWord x fill y n)[k]? = some fill := by
  rw [getElem?_flankWord]
  split_ifs <;> first | rfl | omega

theorem getElem?_flankWord_eq_some_iff {j : ℕ} (hfill : fill ≠ a) :
    (flankWord x fill y n)[j]? = some a ↔ j = 0 ∧ x = a ∨ j = n + 1 ∧ y = a := by
  rw [getElem?_flankWord]
  split_ifs <;> simp_all

theorem take_flankWord (hk : k ≤ n) :
    (flankWord x fill y n).take (k + 1) = x :: List.replicate k fill := by
  rw [flankWord, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
    List.take_replicate, Nat.min_eq_left hk]

theorem drop_flankWord (hk : k ≤ n) :
    (flankWord x fill y n).drop (k + 1) = List.replicate (n - k) fill ++ [y] := by
  rw [flankWord, List.drop_succ_cons, List.drop_append_of_le_length (by simp; omega),
    List.drop_replicate]

theorem mem_take_flankWord_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    a ∈ (flankWord x fill y n).take (k + 1) ↔ x = a := by
  rw [take_flankWord hk]
  simp [List.mem_replicate, eq_comm, hfill]

theorem mem_drop_flankWord_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    a ∈ (flankWord x fill y n).drop (k + 1) ↔ y = a := by
  rw [drop_flankWord hk]
  simp [List.mem_replicate, eq_comm, hfill]

theorem any_take_flankWord (hfill : p fill = false) (hk : k ≤ n) :
    ((flankWord x fill y n).take (k + 1)).any p = p x := by
  rw [take_flankWord hk]
  simp [hfill]

theorem any_drop_flankWord (hfill : p fill = false) (hk : k ≤ n) :
    ((flankWord x fill y n).drop (k + 1)).any p = p y := by
  rw [drop_flankWord hk]
  simp [hfill]

theorem IsFarPerturbation.flankWord_left {i d : ℕ} (x' : α) (h : d < i) :
    IsFarPerturbation (flankWord x fill y n) (flankWord x' fill y n) i d .left := by
  obtain ⟨k, hk⟩ : ∃ k, i - d = k + 1 := ⟨i - d - 1, by omega⟩
  exact ⟨by simp, by simp [hk, flankWord]⟩

theorem IsFarPerturbation.flankWord_right {i d : ℕ} (y' : α) (h : i + d ≤ n) :
    IsFarPerturbation (flankWord x fill y n) (flankWord x fill y' n) i d .right :=
  ⟨by simp, by simp only [Edge.window_right, take_flankWord h]⟩

/-- A `d`-indexed family of flank words whose target's image flips under changing
either flank alone has two-sided unbounded dependence. -/
theorem TwoSidedUnboundedDependence.of_flanks {fill xOn yOn xOff yOff : α}
    {n t : ℕ → ℕ} (ht : ∀ d, d < t d) (hn : ∀ d, t d + d ≤ n d)
    (hL : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]?
      ≠ (f (flankWord xOff fill yOn (n d)))[t d]?)
    (hR : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]?
      ≠ (f (flankWord xOn fill yOff (n d)))[t d]?) :
    TwoSidedUnboundedDependence f := by
  intro d
  have h₁ := ht d; have h₂ := hn d
  refine ⟨flankWord xOn fill yOn (n d), t d, by rw [length_flankWord]; omega, fun s ↦ ?_⟩
  match s with
  | .left => exact ⟨_, .flankWord_left xOff (ht d), hL d⟩
  | .right => exact ⟨_, .flankWord_right yOff (hn d), hR d⟩

/-- A `d`-indexed family of flank words whose target sits `d`-far from both flanks,
changed in the base and reverted by flipping either flank alone, requires both sides. -/
theorem RequiresBothSides.of_flanks {f : List α → List α}
    {fill xOn yOn xOff yOff : α} {n t : ℕ → ℕ}
    (ht : ∀ d, d < t d) (hn : ∀ d, t d + d ≤ n d)
    (hchange : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]? ≠ some fill)
    (hrevL : ∀ d, (f (flankWord xOff fill yOn (n d)))[t d]? = some fill)
    (hrevR : ∀ d, (f (flankWord xOn fill yOff (n d)))[t d]? = some fill) :
    RequiresBothSides f := by
  intro d
  have h₁ := ht d; have h₂ := hn d
  have hmid : ∀ x y : α, (flankWord x fill y (n d))[t d]? = some fill := fun _ _ ↦
    getElem?_flankWord_mid (by omega) (by omega)
  refine ⟨flankWord xOn fill yOn (n d), t d, by rw [length_flankWord]; omega,
    fun h ↦ hchange d (h.trans (hmid _ _)), fun s ↦ ?_⟩
  match s with
  | .left => exact ⟨_, .flankWord_left xOff (ht d),
      (hmid _ _).trans (hmid _ _).symm, (hrevL d).trans (hmid _ _).symm⟩
  | .right => exact ⟨_, .flankWord_right yOff (hn d),
      (hmid _ _).trans (hmid _ _).symm, (hrevR d).trans (hmid _ _).symm⟩

end FlankWitness

/-! ### Non-interacting bimachines: the apparatus -/

namespace Bimachine

variable {L R : Type*}

/-! ### Non-interacting decompositions -/

/-- The output at a cell is determined by one side alone when fixing the input symbol and
one context state already fixes it. -/
def OneSidedAt (B : Bimachine L R α β) (l : L) (a : α) (r : R) : Prop :=
  (∀ r', B.output l a r' = B.output l a r) ∨ (∀ l', B.output l' a r = B.output l a r)

section

variable [DecidableEq α]

/-- `unite cL cR a` takes the left proposal if it fires (`≠ a`), else the right one —
the union of two change proposals over the identity default `a`. The tie-break is
asymmetric (when both fire the left wins) but inert under the order-independence
`IsNonInteracting` requires. -/
def unite (cL cR a : α) : α := if cL = a then cR else cL

@[simp] theorem unite_right_self (cL a : α) : unite cL a a = cL := by
  grind [unite]

@[simp] theorem unite_left_self (cR a : α) : unite a cR a = cR := ite_eq_left rfl

theorem unite_of_left_ne {cL a : α} (h : cL ≠ a) (cR : α) : unite cL cR a = cL := ite_eq_right h

theorem unite_comm_iff {cL cR a : α} :
    unite cL cR a = unite cR cL a ↔ (cL ≠ a → cR ≠ a → cL = cR) := by
  grind [unite]

@[simp] theorem unite_eq_self_iff {cL cR a : α} : unite cL cR a = a ↔ cL = a ∧ cR = a := by
  grind [unite]

/-- A non-interacting decomposition of a bimachine is a change-rule per side over the
identity default, whose union is order-independent and produces the cell output. -/
structure NonInteraction (B : Bimachine L R α α) where
  /-- `ruleL l a` is the change the left context proposes for the current symbol. -/
  ruleL : L → α → α
  /-- `ruleR r a` is the change the right context proposes for the current symbol. -/
  ruleR : R → α → α
  /-- The union of the two proposals is order-independent (by `unite_comm_iff`, they agree
  wherever both fire), so neither side can suppress the other's change. -/
  unite_comm : ∀ l a r, unite (ruleL l a) (ruleR r a) a = unite (ruleR r a) (ruleL l a) a
  /-- The cell output is the union of the two proposals. -/
  output_eq : ∀ l a r, B.output l a r = [unite (ruleL l a) (ruleR r a) a]

/-- A bimachine over a single alphabet is non-interacting when it admits a
non-interacting decomposition (`NonInteraction`) of its cell output. -/
def IsNonInteracting (B : Bimachine L R α α) : Prop := Nonempty B.NonInteraction

variable {L' R' : Type*} {B : Bimachine L R α α} (w : B.NonInteraction) {l : L} {a : α}
  {r : R}

/-- A non-interacting decomposition exhibits the bimachine as letter-to-letter. -/
def NonInteraction.letterToLetter : B.LetterToLetter :=
  ⟨fun l a r ↦ unite (w.ruleL l a) (w.ruleR r a) a, w.output_eq⟩

theorem NonInteraction.output_eq_ruleL (hL : w.ruleL l a ≠ a) :
    B.output l a r = [w.ruleL l a] :=
  (w.output_eq l a r).trans (by rw [unite_of_left_ne hL])

theorem NonInteraction.output_eq_ruleR (hR : w.ruleR r a ≠ a) :
    B.output l a r = [w.ruleR r a] :=
  (w.output_eq l a r).trans (by rw [w.unite_comm l a r, unite_of_left_ne hR])

theorem NonInteraction.oneSidedAt_of_change (w : B.NonInteraction)
    (hne : B.output l a r ≠ [a]) : B.OneSidedAt l a r := by
  by_cases hL : w.ruleL l a = a
  · have hR : w.ruleR r a ≠ a := fun hR ↦
      hne ((w.output_eq l a r).trans (by rw [unite_eq_self_iff.mpr ⟨hL, hR⟩]))
    exact .inr fun l' ↦ (w.output_eq_ruleR hR).trans (w.output_eq_ruleR hR).symm
  · exact .inl fun r' ↦ (w.output_eq_ruleL hL).trans (w.output_eq_ruleL hL).symm

theorem IsNonInteracting.oneSidedAt_of_change (h : B.IsNonInteracting)
    (hne : B.output l a r ≠ [a]) : B.OneSidedAt l a r :=
  h.elim fun w ↦ w.oneSidedAt_of_change hne

/-- Transport a decomposition along state equivalences. -/
def NonInteraction.map (eL : L ≃ L') (eR : R ≃ R') :
    (Bimachine.map eL eR B).NonInteraction where
  ruleL l a := w.ruleL (eL.symm l) a
  ruleR r a := w.ruleR (eR.symm r) a
  unite_comm _ a _ := w.unite_comm _ a _
  output_eq _ a _ := w.output_eq _ a _

/-- Non-interaction transports along state reindexing. -/
theorem IsNonInteracting.map (h : B.IsNonInteracting) (eL : L ≃ L') (eR : R ≃ R') :
    (Bimachine.map eL eR B).IsNonInteracting :=
  Nonempty.map (·.map eL eR) h

theorem NonInteraction.getElem?_run_eq_iff {u : List α} {i : ℕ} (hsym : u[i]? = some a) :
    (B.run u)[i]? = u[i]? ↔
      w.ruleL (B.lState (u.take i)) a = a ∧ w.ruleR (B.rState (u.drop (i + 1))) a = a := by
  rw [w.letterToLetter.getElem?_run u i, hsym, Option.map_some, Option.some_inj]
  exact unite_eq_self_iff

end
end Bimachine

/-! ### The non-interacting class -/

section

variable [DecidableEq α]

/-- `f` is computed by a non-interacting finite bimachine. -/
def IsNonInteractingBimachineComputable (f : List α → List α) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α α),
    B.run = f ∧ B.IsNonInteracting

theorem Bimachine.isNonInteractingBimachineComputable {L R : Type*} [Fintype L]
    [Fintype R] (B : Bimachine L R α α) (h : B.IsNonInteracting) :
    IsNonInteractingBimachineComputable B.run :=
  ⟨Shrink L, inferInstance, Shrink R, inferInstance, B.map (equivShrink.{0} L) (equivShrink.{0} R),
    B.run_map _ _, h.map _ _⟩

theorem IsBimachineComputable.of_nonInteracting {f : List α → List α}
    (h : IsNonInteractingBimachineComputable f) : IsBimachineComputable f :=
  have ⟨_, _, _, _, B, hB, _⟩ := h
  hB ▸ B.isBimachineComputable

theorem IsNonInteractingBimachineComputable.length_eq {f : List α → List α}
    (h : IsNonInteractingBimachineComputable f) (x : List α) : (f x).length = x.length :=
  have ⟨_, _, _, _, _, hB, ⟨w⟩⟩ := h
  hB ▸ w.letterToLetter.length_run x
theorem IsNonInteractingBimachineComputable.of_mealyComputable {f : List α → List α}
    (h : IsMealyComputable f) : IsNonInteractingBimachineComputable f :=
  have ⟨_, _, T, hT⟩ := h
  hT ▸ T.toBimachine_run ▸ T.toBimachine.isNonInteractingBimachineComputable
    ⟨⟨T.output, fun _ a ↦ a,
      fun _ a _ ↦ (Bimachine.unite_right_self _ a).trans (Bimachine.unite_left_self _ a).symm,
      fun _ a _ ↦ by simp⟩⟩

end

/-! ### Machines bound dependence

A length-preserving left-subsequential function depends boundedly on the right: the
delay bound of `IsLeftSubsequential.exists_getElem?_append_eq` is the dependence bound.
Sequential machines are the zero-delay case — prefix-determined at every coordinate
(`Mealy.leftDetermined`), which is strictly stronger than bounded right dependence. -/

section Machines

variable {σ : Type*}

/-- A length-preserving left-subsequential function depends boundedly on the right. -/
theorem IsLeftSubsequential.boundedDependence_right
    (hlen : ∀ w, (f w).length = w.length) (hf : IsLeftSubsequential f) :
    BoundedDependence f .right :=
  have ⟨N, hN⟩ := hf.exists_getElem?_take_eq hlen
  ⟨N, fun i u v h ↦ (hN i u).symm.trans ((congrArg (fun w ↦ (f w)[i]?) h).trans (hN i v))⟩

/-- A length-preserving right-subsequential function depends boundedly on the left. -/
theorem IsRightSubsequential.boundedDependence_left
    (hlen : ∀ w, (f w).length = w.length) (hf : IsRightSubsequential f) :
    BoundedDependence f .left := by
  obtain ⟨N, hN⟩ := hf.exists_getElem?_drop_eq hlen
  refine ⟨N, fun i u v h ↦ ?_⟩
  rcases lt_or_ge i N with hiN | hiN
  · simpa [Nat.sub_eq_zero_of_le hiN.le] using congrArg (·[i]?) (congrArg f h)
  · exact (hN i u hiN).symm.trans ((congrArg (fun w ↦ (f w)[N]?) h).trans (hN i v hiN))

/-- A length-preserving function with two-sided unbounded dependence is subsequential in
neither direction. -/
theorem TwoSidedUnboundedDependence.not_isSubsequential (h : TwoSidedUnboundedDependence f)
    (hlen : ∀ w, (f w).length = w.length) : ∀ d, ¬ IsSubsequential d f
  | .left => fun hf ↦ h.unboundedDependence .right (hf.boundedDependence_right hlen)
  | .right => fun hf ↦ h.unboundedDependence .left (hf.boundedDependence_left hlen)

/-- A sequential machine is left-determined at every coordinate. -/
theorem Mealy.leftDetermined (T : Mealy σ α β) (i : ℕ) : LeftDetermined T.run i := fun u v h ↦ by
  simpa [T.run_take] using congrArg (fun w ↦ (T.run w)[i]?) h

/-- A sequential machine's output never depends on input to its right. -/
theorem Mealy.boundedDependence_right (T : Mealy σ α β) : BoundedDependence T.run .right :=
  BoundedDependence.right_of_leftDetermined T.leftDetermined

/-- A Mealy-computable map is left-determined at every coordinate. -/
theorem IsMealyComputable.leftDetermined {f : List α → List β}
    (hf : IsMealyComputable f) (i : ℕ) : LeftDetermined f i := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.leftDetermined i

/-- A Mealy-computable map's output never depends on input to its right. -/
theorem IsMealyComputable.boundedDependence_right {f : List α → List β}
    (hf : IsMealyComputable f) : BoundedDependence f .right :=
  BoundedDependence.right_of_leftDetermined hf.leftDetermined

/-! ### Non-interacting bimachines

A map that requires both sides escapes the non-interacting bimachines, and the
conjunctive flag bimachine shows the non-interacting class is proper. -/

/-- A map that requires both sides is computed by no non-interacting bimachine. At the
witness the base changes but each far perturbation reverts. The right perturbation
shares the left window, silencing `ruleL` at this cell; the left perturbation shares
the right window, silencing `ruleR`; yet the base needs one of them to fire. -/
theorem RequiresBothSides.not_isNonInteractingBimachineComputable [DecidableEq α]
    {f : List α → List α}
    (hf : RequiresBothSides f) : ¬ IsNonInteractingBimachineComputable f := by
  rintro ⟨L, _, R, _, B, rfl, ⟨w⟩⟩
  obtain ⟨base, i, hi, hchange, hw⟩ := hf 0
  choose u hpert hsym hrev using hw
  have hbase : base[i]? = some base[i] := List.getElem?_eq_getElem hi
  apply hchange
  rw [w.getElem?_run_eq_iff hbase, List.take_eq_take_of_le (hpert .right).2 (by omega),
    List.drop_eq_drop_of_le (hpert .left).2 (by omega)]
  exact ⟨((w.getElem?_run_eq_iff ((hsym .right).trans hbase)).mp (hrev .right)).1,
    ((w.getElem?_run_eq_iff ((hsym .left).trans hbase)).mp (hrev .left)).2⟩

/-! ### Strictness: non-interacting ⊊ bimachine-computable

A *conjunctive* change — a symbol raised iff a mark occurs on **both** sides — is
bimachine-computable but requires both sides, so no non-interacting bimachine computes
it. -/

/-- The conjunctive flag bimachine raises a `false` cell exactly when a `true` occurs on
both sides. -/
def conjBM : Bimachine Bool Bool Bool Bool := .ofFlags id id fun l s r ↦ s || (l && r)

theorem conjBM.run_flankWord_mid (x y : Bool) (d : ℕ) :
    (conjBM.run (flankWord x false y (2 * d + 1)))[d + 1]? = some (x && y) := by
  rw [conjBM, Bimachine.getElem?_ofFlags_run, getElem?_flankWord_mid (by omega) (by omega),
    any_take_flankWord rfl (by omega), any_drop_flankWord rfl (by omega)]
  rfl

theorem conjBM.requiresBothSides : RequiresBothSides conjBM.run :=
  .of_flanks (fun d ↦ by omega) (fun d ↦ by omega)
    (fun d ↦ by rw [conjBM.run_flankWord_mid]; decide)
    (conjBM.run_flankWord_mid false true) (conjBM.run_flankWord_mid true false)

/-- Changed cells of a non-interacting bimachine's run are each determined by a
single side, `OneSidedAt` transported to words. -/
theorem IsNonInteractingBimachineComputable.oneSidedChanges [DecidableEq α]
    {f : List α → List α} (hf : IsNonInteractingBimachineComputable f) :
    OneSidedChanges f := by
  obtain ⟨L, _, R, _, B, rfl, ⟨wni⟩⟩ := hf
  have hni : B.IsNonInteracting := ⟨wni⟩
  set w := wni.letterToLetter with hw
  intro xs i hchange
  rcases lt_or_ge i xs.length with hi | hi
  · have ha : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
    have hcell : w.cell (B.lState (xs.take i)) xs[i] (B.rState (xs.drop (i + 1)))
        ≠ xs[i] :=
      fun h ↦ hchange (by rw [w.getElem?_run, ha, Option.map_some, h])
    have hout : B.output (B.lState (xs.take i)) xs[i] (B.rState (xs.drop (i + 1)))
        ≠ [xs[i]] := by rw [w.output_eq]; simpa using hcell
    rcases hni.oneSidedAt_of_change hout with hR | hL
    · refine ⟨.right, fun v hlen hag ↦ ?_⟩
      have hv : v[i]? = some xs[i] :=
        (List.take_eq_take_iff_getElem?.mp hag i (by omega)).symm.trans ha
      show (B.run xs)[i]? = (B.run v)[i]?
      rw [w.getElem?_run, w.getElem?_run, ha, hv, Option.map_some, Option.map_some,
        ← List.take_eq_take_of_le hag (by omega), w.cell_inj.mpr (hR (B.rState (v.drop (i + 1))))]
    · refine ⟨.left, fun v hlen hag ↦ ?_⟩
      have hv : v[i]? = some xs[i] :=
        (List.drop_eq_drop_iff_getElem?.mp hag i (by omega)).symm.trans ha
      show (B.run xs)[i]? = (B.run v)[i]?
      rw [w.getElem?_run, w.getElem?_run, ha, hv, Option.map_some, Option.map_some,
        ← List.drop_eq_drop_of_le hag (by omega), w.cell_inj.mpr (hL (B.lState (v.take i)))]
  · exact absurd (by rw [List.getElem?_eq_none (by simpa [w.length_run] using hi),
      List.getElem?_eq_none hi]) hchange

/-- The non-interacting class is proper inside the bimachine-computable functions —
`conjBM` is computed by a bimachine, but by no non-interacting one. -/
theorem setOf_isNonInteractingBimachineComputable_ssubset :
    {f : List Bool → List Bool | IsNonInteractingBimachineComputable f} ⊂
      {f | IsBimachineComputable f} :=
  ⟨fun _ h ↦ IsBimachineComputable.of_nonInteracting h,
   fun h ↦ conjBM.requiresBothSides.not_isNonInteractingBimachineComputable
     (h conjBM.isBimachineComputable)⟩

end Machines

