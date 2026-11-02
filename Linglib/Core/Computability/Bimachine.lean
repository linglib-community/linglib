/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Mealy
public import Linglib.Core.Computability.Edge
public import Mathlib.Data.Fintype.Shrink

/-!
# Bimachines

A `Bimachine`, in the sense of Schützenberger and Eilenberg, reads its input in both
directions: a left automaton scans `→`, a right automaton scans `←`, and output `i` is
`output (lState (x.take i)) (x i) (rState (x.drop (i+1)))`. By the theorem of Elgot and Mezei,
word-output bimachines compute exactly the rational functions; they are the transducers of
Schützenberger's semi-monomial representations, as Sakarovitch presents them. The
letter-to-letter machines here compute the total length-preserving ones.

## Main definitions

* `Bimachine L R α β`: machine with left states `L`, right states `R`, alphabets `α`, `β`
* `Bimachine.run`: the computed function
* `Bimachine.reverse`: the mirror machine, the two automata trading sides
* `IsBimachineComputable f`: `f` is computed by some finite bimachine

## Main theorems

* `Bimachine.LetterToLetter.getElem?_run`: output `i` is
  `output (lState (x.take i)) (x i) (rState (x.drop (i+1)))`
* `Bimachine.run_reverse`: the mirror machine computes the reverse conjugate
* `IsBimachineComputable.revConj`: the class is closed under reverse conjugation

## Implementation notes

Only the left state is threaded through the run (`Bimachine.runFrom`); the recursion
reads each tail's right state on the spot. The class existentials pin state types at
`Type`, as `Language.IsRegular` does; `Bimachine.isBimachineComputable` reaches the class from
state types in any universes through `Shrink`. The identification of `IsBimachineComputable`
with the total rational functions preserving the empty word is classical and not formalized
here; `ElgotMezei.lean` proves the composition half.

[UPSTREAM] candidate: `Mathlib.Computability.Bimachine`.

## References

* [schutzenberger-1961]
* [eilenberg-1974]
* [elgot-mezei-1965]
* [schutzenberger-1976]
* [sakarovitch-2009]
-/

@[expose] public section

variable {L R α β : Type*}

/-- A bimachine is a left automaton scanning left to right, a right automaton scanning
right to left, and a cell output reading both context states and the current symbol. -/
structure Bimachine (L R α β : Type*) where
  /-- The left automaton starts in this state. -/
  lInit : L
  /-- The left automaton steps on each symbol, scanning left to right. -/
  lStep : L → α → L
  /-- The right automaton starts in this state. -/
  rInit : R
  /-- The right automaton steps on each symbol, scanning right to left. -/
  rStep : R → α → R
  /-- A cell emits a word from the two context states and the current input symbol. -/
  output : L → α → R → List β

instance [Inhabited L] [Inhabited R] : Inhabited (Bimachine L R α β) :=
  ⟨⟨default, fun _ _ ↦ default, default, fun _ _ ↦ default, fun _ _ _ ↦ []⟩⟩

namespace Bimachine

variable (B : Bimachine L R α β)

/-- `B.lStateAfter l pre` is the left state reached from `l` after scanning `pre`. -/
def lStateAfter (l : L) : List α → L := List.foldl B.lStep l

/-- `B.lState pre` is the left state after scanning `pre` left to right from the start. -/
def lState : List α → L := B.lStateAfter B.lInit

/-- `B.rState suf` is the right state after scanning `suf` right to left. -/
def rState (suf : List α) : R := suf.foldr (fun a r ↦ B.rStep r a) B.rInit

/-- `B.runFrom l x` runs `B` on `x` threading the left state from `l`; each tail's
right state is read on the spot. -/
def runFrom : L → List α → List β
  | _, [] => []
  | l, x :: xs => B.output l x (B.rState xs) ++ runFrom (B.lStep l x) xs

/-- `B.run` is the function `B` computes. -/
def run : List α → List β := B.runFrom B.lInit

section
variable (l : L) (x : α) (xs : List α)

@[simp] theorem lStateAfter_nil : B.lStateAfter l [] = l := rfl
@[simp] theorem lStateAfter_cons : B.lStateAfter l (x :: xs) = B.lStateAfter (B.lStep l x) xs :=
  rfl
@[simp] theorem lState_nil : B.lState [] = B.lInit := rfl
@[simp] theorem rState_nil : B.rState [] = B.rInit := rfl
@[simp] theorem rState_cons : B.rState (x :: xs) = B.rStep (B.rState xs) x := rfl

theorem lState_append (ys : List α) : B.lState (xs ++ ys) = B.lStateAfter (B.lState xs) ys :=
  List.foldl_append

theorem rState_append (ys : List α) :
    B.rState (xs ++ ys) = rState {B with rInit := B.rState ys} xs :=
  List.foldr_append

@[simp] theorem runFrom_nil : B.runFrom l [] = [] := rfl
@[simp] theorem runFrom_cons :
    B.runFrom l (x :: xs) = B.output l x (B.rState xs) ++ B.runFrom (B.lStep l x) xs := rfl

end

/-! ### Letter-to-letter bimachines

A cell of a general bimachine emits a word, so the run is a concatenation and output
positions need not track input positions. A **letter-to-letter** bimachine emits exactly
one symbol per cell ([sakarovitch-2009] §IV.6); the function it computes is then
*length-preserving*, and the positional description below holds. -/

/-- A witness that `B` is *letter-to-letter* names, by `cell`, the one symbol every cell
emits. -/
structure LetterToLetter (B : Bimachine L R α β) where
  /-- `cell l a r` is the symbol the cell emits. -/
  cell : L → α → R → β
  /-- Every cell emits exactly that one symbol. -/
  output_eq : ∀ l a r, B.output l a r = [cell l a r]

/-- `B` is letter-to-letter when it admits a `LetterToLetter` witness. -/
def IsLetterToLetter (B : Bimachine L R α β) : Prop := Nonempty B.LetterToLetter

namespace LetterToLetter

variable {B}

@[simp] theorem length_runFrom (w : B.LetterToLetter) (l : L) (xs : List α) :
    (B.runFrom l xs).length = xs.length := by
  induction xs generalizing l <;> simp [w.output_eq, *]

@[simp] theorem length_run (w : B.LetterToLetter) (xs : List α) :
    (B.run xs).length = xs.length :=
  w.length_runFrom B.lInit xs

theorem getElem?_runFrom (w : B.LetterToLetter) (l : L) (xs : List α) (i : ℕ) :
    (B.runFrom l xs)[i]? = xs[i]?.map fun a ↦
      w.cell (B.lStateAfter l (xs.take i)) a (B.rState (xs.drop (i + 1))) := by
  induction xs generalizing l i <;> cases i <;> simp [w.output_eq, *]

/-- Output `i` is `cell (lState (x.take i)) (x i) (rState (x.drop (i+1)))`. -/
theorem getElem?_run (w : B.LetterToLetter) (x : List α) (i : ℕ) :
    (B.run x)[i]? = x[i]?.map fun a ↦
      w.cell (B.lState (x.take i)) a (B.rState (x.drop (i + 1))) :=
  w.getElem?_runFrom B.lInit x i

end LetterToLetter

/-! ### Transport along state equivalences -/

variable {L' R' : Type*}

/-- Transport a bimachine along equivalences on the two state spaces. -/
@[simps]
def map (eL : L ≃ L') (eR : R ≃ R') (B : Bimachine L R α β) : Bimachine L' R' α β where
  lInit := eL B.lInit
  lStep l a := eL (B.lStep (eL.symm l) a)
  rInit := eR B.rInit
  rStep r a := eR (B.rStep (eR.symm r) a)
  output l a r := B.output (eL.symm l) a (eR.symm r)

@[simp] theorem map_refl : map (Equiv.refl L) (Equiv.refl R) B = B := rfl

@[simp] theorem map_map {L'' R'' : Type*} (eL : L ≃ L') (eR : R ≃ R') (eL' : L' ≃ L'')
    (eR' : R' ≃ R'') : map eL' eR' (map eL eR B) = map (eL.trans eL') (eR.trans eR') B := rfl

@[simp] theorem lStateAfter_map (eL : L ≃ L') (eR : R ≃ R') (l' : L') (pre : List α) :
    (map eL eR B).lStateAfter l' pre = eL (B.lStateAfter (eL.symm l') pre) := by
  induction pre generalizing l' <;> simp [*]

@[simp] theorem lState_map (eL : L ≃ L') (eR : R ≃ R') (pre : List α) :
    (map eL eR B).lState pre = eL (B.lState pre) := by
  simp [lState]

@[simp] theorem rState_map (eL : L ≃ L') (eR : R ≃ R') (suf : List α) :
    (map eL eR B).rState suf = eR (B.rState suf) :=
  List.foldr_hom eR fun x y ↦ by simp

@[simp] theorem runFrom_map (eL : L ≃ L') (eR : R ≃ R') (l' : L') (xs : List α) :
    (map eL eR B).runFrom l' xs = B.runFrom (eL.symm l') xs := by
  induction xs generalizing l' <;> simp [*]

@[simp] theorem run_map (eL : L ≃ L') (eR : R ≃ R') :
    (map eL eR B).run = B.run := by
  funext xs; simp [run]

theorem LetterToLetter.cell_inj {B : Bimachine L R α β} (w : B.LetterToLetter)
    {l l' : L} {a a' : α} {r r' : R} :
    w.cell l a r = w.cell l' a' r' ↔ B.output l a r = B.output l' a' r' := by
  rw [w.output_eq, w.output_eq]; simp

/-- Letter-to-letter-ness transports along state reindexing. -/
def LetterToLetter.map {L' R' : Type*} {B : Bimachine L R α β} (w : B.LetterToLetter)
    (eL : L ≃ L') (eR : R ≃ R') : (Bimachine.map eL eR B).LetterToLetter :=
  ⟨fun l a r ↦ w.cell (eL.symm l) a (eR.symm r), fun _ _ _ ↦ w.output_eq _ _ _⟩

/-! ### Reversal

Read backwards, a bimachine is again a bimachine: the two automata trade sides and every
cell emits its word reversed. The mirror computes the reverse conjugate, so the
bimachine-computable functions are closed under `List.revConj`. -/

/-- In the mirror image of `B` the right automaton scans left to right, the left one right to
left, and each cell emits its word reversed. -/
@[simps]
def reverse : Bimachine R L α β where
  lInit := B.rInit
  lStep := B.rStep
  rInit := B.lInit
  rStep := B.lStep
  output r a l := (B.output l a r).reverse

@[simp] theorem reverse_reverse : B.reverse.reverse = B := by
  simp [reverse]

private theorem runFrom_append_singleton (l : L) (xs : List α) (a : α) :
    B.runFrom l (xs ++ [a]) =
      ({ B with rInit := B.rStep B.rInit a } : Bimachine L R α β).runFrom l xs
        ++ B.output (B.lStateAfter l xs) a B.rInit := by
  induction xs generalizing l with
  | nil => simp [runFrom]
  | cons y ys ih =>
    simp only [List.cons_append, runFrom_cons, ih, List.append_assoc, lStateAfter_cons]
    congr 2
    simp [rState, List.foldr_append]

private theorem reverse_runFrom (r : R) (xs : List α) :
    B.reverse.runFrom r xs =
      (({ B with rInit := r } : Bimachine L R α β).runFrom B.lInit xs.reverse).reverse := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih =>
    rw [runFrom_cons, ih, List.reverse_cons, runFrom_append_singleton, List.reverse_append]
    congr 1
    simp [rState, lStateAfter]

/-- The mirror bimachine computes the reverse conjugate. -/
@[simp] theorem run_reverse : B.reverse.run = List.revConj B.run :=
  funext fun xs ↦ B.reverse_runFrom B.rInit xs

/-! ### Flag bimachines

The recurring two-sided-trigger shape: each side's automaton is the one-bit "some symbol
on my side satisfies `p`" flag, so `lState`/`rState` compute `List.any` and the cell sees
exactly the two flags. -/

variable (pL pR : α → Bool) (out : Bool → α → Bool → β)

/-- The bimachine whose side states are "a symbol satisfying `pL`/`pR` occurred on my
side" flags. -/
def ofFlags : Bimachine Bool Bool α β where
  lInit := false
  lStep l a := l || pL a
  rInit := false
  rStep r a := r || pR a
  output l a r := [out l a r]

@[simp] theorem ofFlags_lInit : (ofFlags pL pR out).lInit = false := rfl
@[simp] theorem ofFlags_lStep (l : Bool) (a : α) :
    (ofFlags pL pR out).lStep l a = (l || pL a) := rfl
@[simp] theorem ofFlags_rInit : (ofFlags pL pR out).rInit = false := rfl
@[simp] theorem ofFlags_rStep (r : Bool) (a : α) :
    (ofFlags pL pR out).rStep r a = (r || pR a) := rfl
@[simp] theorem ofFlags_output (l : Bool) (a : α) (r : Bool) :
    (ofFlags pL pR out).output l a r = [out l a r] := rfl

/-- A flag bimachine is letter-to-letter, with `out` as its cell. -/
def ofFlags_letterToLetter : (ofFlags pL pR out).LetterToLetter := ⟨out, fun _ _ _ ↦ rfl⟩

@[simp] theorem ofFlags_lStateAfter (l : Bool) (xs : List α) :
    (ofFlags pL pR out).lStateAfter l xs = (l || xs.any pL) := by
  induction xs generalizing l <;> simp [*, Bool.or_assoc]

@[simp] theorem ofFlags_lState (xs : List α) : (ofFlags pL pR out).lState xs = xs.any pL := by
  simp [lState]

@[simp] theorem ofFlags_rState (xs : List α) : (ofFlags pL pR out).rState xs = xs.any pR := by
  induction xs <;> simp [*, Bool.or_comm]

theorem getElem?_ofFlags_run (x : List α) (i : ℕ) :
    ((ofFlags pL pR out).run x)[i]?
      = x[i]?.map fun a ↦ out ((x.take i).any pL) a ((x.drop (i + 1)).any pR) := by
  simp [(ofFlags_letterToLetter pL pR out).getElem?_run, ofFlags_letterToLetter]

end Bimachine

/-! ### Sequential machines as bimachines -/

section ToBimachine

variable {σ : Type*} (T : Mealy σ α β)

/-- A sequential machine as the bimachine whose left automaton does all the work and
whose right automaton is trivial. -/
@[simps]
def Mealy.toBimachine : Bimachine σ Unit α β where
  lInit := T.start
  lStep := T.step
  rInit := ()
  rStep _ _ := ()
  output l a _ := [T.output l a]

@[simp] theorem Mealy.toBimachine_runFrom (s : σ) (xs : List α) :
    T.toBimachine.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s <;> simp [*]

@[simp] theorem Mealy.toBimachine_run : T.toBimachine.run = T.run :=
  funext fun xs ↦ T.toBimachine_runFrom T.start xs

end ToBimachine

/-! ### The bimachine-computable class -/

/-- Computability by a finite bimachine — classically, the total rational functions
preserving the empty word. -/
def IsBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α β),
    B.run = f

theorem Bimachine.isBimachineComputable {L R : Type*} [Fintype L] [Fintype R]
    (B : Bimachine L R α β) : IsBimachineComputable B.run :=
  ⟨Shrink L, inferInstance, Shrink R, inferInstance, B.map (equivShrink.{0} L) (equivShrink.{0} R),
    B.run_map _ _⟩

/-- The reverse conjugate of a bimachine-computable function is bimachine-computable. -/
protected theorem IsBimachineComputable.revConj {f : List α → List β}
    (h : IsBimachineComputable f) : IsBimachineComputable (List.revConj f) :=
  have ⟨L, _, R, _, B, hB⟩ := h
  ⟨R, ‹_›, L, ‹_›, B.reverse, hB ▸ B.run_reverse⟩

@[simp] theorem isBimachineComputable_revConj_iff {f : List α → List β} :
    IsBimachineComputable (List.revConj f) ↔ IsBimachineComputable f :=
  ⟨fun h ↦ List.revConj_revConj f ▸ h.revConj, .revConj⟩

/-- `f` is computed by a finite **letter-to-letter** bimachine. These are the total
length-preserving rational functions. -/
def IsLengthPreservingBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α β),
    B.IsLetterToLetter ∧ B.run = f

theorem Bimachine.isLengthPreservingBimachineComputable {L R : Type*} [Fintype L]
    [Fintype R] (B : Bimachine L R α β) (h : B.IsLetterToLetter) :
    IsLengthPreservingBimachineComputable B.run :=
  have ⟨w⟩ := h
  ⟨Shrink L, inferInstance, Shrink R, inferInstance, B.map (equivShrink.{0} L) (equivShrink.{0} R),
    ⟨w.map _ _⟩, B.run_map _ _⟩

theorem IsBimachineComputable.of_lengthPreserving {f : List α → List β}
    (h : IsLengthPreservingBimachineComputable f) : IsBimachineComputable f :=
  have ⟨L, _, R, _, B, _, hB⟩ := h
  ⟨L, ‹_›, R, ‹_›, B, hB⟩

theorem IsLengthPreservingBimachineComputable.length_eq {f : List α → List β}
    (h : IsLengthPreservingBimachineComputable f) (x : List α) : (f x).length = x.length :=
  have ⟨_, _, _, _, _, ⟨w⟩, hB⟩ := h
  hB ▸ w.length_run x

theorem IsBimachineComputable.of_mealyComputable {f : List α → List β}
    (h : IsMealyComputable f) : IsBimachineComputable f :=
  have ⟨_, _, T, hT⟩ := h
  hT ▸ T.toBimachine_run ▸ T.toBimachine.isBimachineComputable
