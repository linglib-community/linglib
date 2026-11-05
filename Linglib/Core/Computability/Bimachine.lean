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

A `Bimachine` reads its input in both directions: a left automaton scans `→`, a right automaton
scans `←`, each cell emits a word from the two states around it, and two final functions emit a
block at either end of the output. A single right state gives a subsequential transducer, and the
functions computed by finite bimachines are the total rational functions. [Reversing a
machine](##Bimachine.run_reverse) exchanges the two automata and computes the reverse conjugate,
and [a letter-to-letter machine](##Bimachine.LetterToLetter.getElem?_run) computes a
length-preserving function whose output `i` reads the two states around letter `i`. Composition is
in `ElgotMezei.lean`.

## Implementation notes

The definition is that of Reutenauer and Schützenberger, whose final functions give the empty word
an arbitrary image and make the subsequential transducers the case of one right state. Eilenberg's
machines are those with empty final functions, which compute exactly the total rational functions
preserving the empty word: his *generalized bimachine* is the word-output case, and his *bimachine*
the letter-to-letter one. They are the transducers of Schützenberger's semi-monomial
representations, as Sakarovitch observes.

The class existentials pin state types at `Type`, as `Language.IsRegular` does;
`Bimachine.isBimachineComputable` reaches the class from state types in any universes through
`Shrink`.

[UPSTREAM] candidate: `Mathlib.Computability.Bimachine`.

## TODO

* Every rational function is computed by a finite bimachine, which needs Schützenberger's
  semi-monomial construction and rational relations as objects.

## References

* [schutzenberger-1961]
* [eilenberg-1974]
* [schutzenberger-1976]
* [reutenauer-schutzenberger-1991]
* [sakarovitch-2009]
-/

@[expose] public section

variable {L R α β : Type*}

/-- A bimachine is a left automaton scanning left to right, a right automaton scanning right to
left, a cell output reading both context states and the current symbol, and two final functions
for the ends of the output. -/
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
  /-- The final left function emits the first block, from the right state over the whole word. -/
  finalLeft : R → List β := fun _ ↦ []
  /-- The final right function emits the last block, from the left state over the whole word. -/
  finalRight : L → List β := fun _ ↦ []

instance [Inhabited L] [Inhabited R] : Inhabited (Bimachine L R α β) :=
  ⟨{ lInit := default, lStep := fun _ _ ↦ default, rInit := default, rStep := fun _ _ ↦ default,
     output := fun _ _ _ ↦ [] }⟩

namespace Bimachine

variable (B : Bimachine L R α β)

/-- `B.lStateFrom l xs` is the left state reached from `l` after scanning `xs`. -/
def lStateFrom (l : L) : List α → L := List.foldl B.lStep l

/-- `B.lState xs` is the left state after scanning `xs` left to right from the start. -/
def lState : List α → L := B.lStateFrom B.lInit

/-- `B.rStateFrom r xs` is the right state reached from `r` after scanning `xs` right to left. -/
def rStateFrom (r : R) (xs : List α) : R := xs.foldr (fun a r ↦ B.rStep r a) r

/-- `B.rState xs` is the right state after scanning `xs` right to left from the start. -/
def rState : List α → R := B.rStateFrom B.rInit

/-- `B.emitted l xs r` is the output over `xs` between the left state `l` and the right state `r`,
the extension of the cell output to words ([eilenberg-1974] (7.4) to (7.7),
[reutenauer-schutzenberger-1991] (5)). -/
def emitted : L → List α → R → List β
  | _, [], _ => []
  | l, x :: xs, r => B.output l x (B.rStateFrom r xs) ++ emitted (B.lStep l x) xs r

/-- `B.run` is the function `B` computes: the final left block, the cells, the final right block
([reutenauer-schutzenberger-1991] (6)). -/
def run (xs : List α) : List β :=
  B.finalLeft (B.rState xs) ++ B.emitted B.lInit xs B.rInit ++ B.finalRight (B.lState xs)

section
variable (l : L) (r : R) (x : α) (xs ys : List α)

@[simp] theorem lStateFrom_nil : B.lStateFrom l [] = l := rfl
@[simp] theorem lStateFrom_cons : B.lStateFrom l (x :: xs) = B.lStateFrom (B.lStep l x) xs := rfl
@[simp] theorem lState_nil : B.lState [] = B.lInit := rfl
@[simp] theorem rStateFrom_nil : B.rStateFrom r [] = r := rfl
@[simp] theorem rStateFrom_cons : B.rStateFrom r (x :: xs) = B.rStep (B.rStateFrom r xs) x := rfl
@[simp] theorem rState_nil : B.rState [] = B.rInit := rfl
@[simp] theorem rState_cons : B.rState (x :: xs) = B.rStep (B.rState xs) x := rfl

theorem lStateFrom_append : B.lStateFrom l (xs ++ ys) = B.lStateFrom (B.lStateFrom l xs) ys :=
  List.foldl_append

theorem rStateFrom_append : B.rStateFrom r (xs ++ ys) = B.rStateFrom (B.rStateFrom r ys) xs :=
  List.foldr_append

theorem lState_append : B.lState (xs ++ ys) = B.lStateFrom (B.lState xs) ys :=
  B.lStateFrom_append _ xs ys

@[simp] theorem emitted_nil : B.emitted l [] r = [] := rfl
@[simp] theorem emitted_cons :
    B.emitted l (x :: xs) r = B.output l x (B.rStateFrom r xs) ++ B.emitted (B.lStep l x) xs r :=
  rfl

theorem emitted_append : B.emitted l (xs ++ ys) r =
    B.emitted l xs (B.rStateFrom r ys) ++ B.emitted (B.lStateFrom l xs) ys r := by
  induction xs generalizing l <;> simp [rStateFrom_append, *]

end

/-! ### Letter-to-letter bimachines

A cell of a general bimachine emits a word, so the run is a concatenation and output positions need
not track input positions. A **letter-to-letter** bimachine emits exactly one symbol per cell and
nothing at either end ([sakarovitch-2009] §IV.6); the function it computes is then
*length-preserving*, and the positional description below holds. -/

/-- A witness that `B` is *letter-to-letter* names, by `cell`, the one symbol every cell
emits. -/
structure LetterToLetter (B : Bimachine L R α β) where
  /-- `cell l a r` is the symbol the cell emits. -/
  cell : L → α → R → β
  /-- Every cell emits exactly that one symbol. -/
  output_eq : ∀ l a r, B.output l a r = [cell l a r]
  /-- The final left function emits nothing. -/
  finalLeft_eq : ∀ r, B.finalLeft r = [] := by intro; rfl
  /-- The final right function emits nothing. -/
  finalRight_eq : ∀ l, B.finalRight l = [] := by intro; rfl

/-- `B` is letter-to-letter when it admits a `LetterToLetter` witness. -/
def IsLetterToLetter (B : Bimachine L R α β) : Prop := Nonempty B.LetterToLetter

namespace LetterToLetter

variable {B}

/-- A letter-to-letter machine computes its cells alone. -/
theorem run_eq (w : B.LetterToLetter) (xs : List α) : B.run xs = B.emitted B.lInit xs B.rInit := by
  simp [run, w.finalLeft_eq, w.finalRight_eq]

@[simp] theorem length_emitted (w : B.LetterToLetter) (l : L) (xs : List α) (r : R) :
    (B.emitted l xs r).length = xs.length := by
  induction xs generalizing l <;> simp [w.output_eq, *]

@[simp] theorem length_run (w : B.LetterToLetter) (xs : List α) :
    (B.run xs).length = xs.length := by
  rw [w.run_eq, w.length_emitted]

theorem getElem?_emitted (w : B.LetterToLetter) (l : L) (xs : List α) (r : R) (i : ℕ) :
    (B.emitted l xs r)[i]? = xs[i]?.map fun a ↦
      w.cell (B.lStateFrom l (xs.take i)) a (B.rStateFrom r (xs.drop (i + 1))) := by
  induction xs generalizing l i <;> cases i <;> simp [w.output_eq, *]

/-- Output `i` is `cell (lState (x.take i)) (x i) (rState (x.drop (i+1)))`. -/
theorem getElem?_run (w : B.LetterToLetter) (x : List α) (i : ℕ) :
    (B.run x)[i]? = x[i]?.map fun a ↦
      w.cell (B.lState (x.take i)) a (B.rState (x.drop (i + 1))) := by
  rw [w.run_eq, w.getElem?_emitted]
  rfl

end LetterToLetter

/-! ### Reindexing along state equivalences -/

variable {L' R' : Type*}

/-- Lifts equivalences on the two state spaces to an equivalence on bimachines. -/
@[simps apply_lInit apply_lStep apply_rInit apply_rStep apply_output apply_finalLeft
  apply_finalRight]
def reindex (eL : L ≃ L') (eR : R ≃ R') : Bimachine L R α β ≃ Bimachine L' R' α β where
  toFun B :=
    { lInit := eL B.lInit
      lStep := fun l a ↦ eL (B.lStep (eL.symm l) a)
      rInit := eR B.rInit
      rStep := fun r a ↦ eR (B.rStep (eR.symm r) a)
      output := fun l a r ↦ B.output (eL.symm l) a (eR.symm r)
      finalLeft := fun r ↦ B.finalLeft (eR.symm r)
      finalRight := fun l ↦ B.finalRight (eL.symm l) }
  invFun B :=
    { lInit := eL.symm B.lInit
      lStep := fun l a ↦ eL.symm (B.lStep (eL l) a)
      rInit := eR.symm B.rInit
      rStep := fun r a ↦ eR.symm (B.rStep (eR r) a)
      output := fun l a r ↦ B.output (eL l) a (eR r)
      finalLeft := fun r ↦ B.finalLeft (eR r)
      finalRight := fun l ↦ B.finalRight (eL l) }
  left_inv B := by simp
  right_inv B := by simp

@[simp] theorem reindex_refl : reindex (Equiv.refl L) (Equiv.refl R) B = B := rfl

@[simp] theorem symm_reindex (eL : L ≃ L') (eR : R ≃ R') :
    (reindex (α := α) (β := β) eL eR).symm = reindex eL.symm eR.symm :=
  rfl

@[simp] theorem lStateFrom_reindex (eL : L ≃ L') (eR : R ≃ R') (l' : L') (xs : List α) :
    (reindex eL eR B).lStateFrom l' xs = eL (B.lStateFrom (eL.symm l') xs) := by
  induction xs generalizing l' <;> simp [*]

@[simp] theorem lState_reindex (eL : L ≃ L') (eR : R ≃ R') (xs : List α) :
    (reindex eL eR B).lState xs = eL (B.lState xs) := by
  simp [lState]

@[simp] theorem rStateFrom_reindex (eL : L ≃ L') (eR : R ≃ R') (r' : R') (xs : List α) :
    (reindex eL eR B).rStateFrom r' xs = eR (B.rStateFrom (eR.symm r') xs) := by
  induction xs <;> simp [*]

@[simp] theorem rState_reindex (eL : L ≃ L') (eR : R ≃ R') (xs : List α) :
    (reindex eL eR B).rState xs = eR (B.rState xs) := by
  simp [rState]

@[simp] theorem emitted_reindex (eL : L ≃ L') (eR : R ≃ R') (l' : L') (xs : List α) (r' : R') :
    (reindex eL eR B).emitted l' xs r' = B.emitted (eL.symm l') xs (eR.symm r') := by
  induction xs generalizing l' <;> simp [*]

@[simp] theorem run_reindex (eL : L ≃ L') (eR : R ≃ R') :
    (reindex eL eR B).run = B.run := by
  funext xs; simp [run]

theorem LetterToLetter.cell_inj {B : Bimachine L R α β} (w : B.LetterToLetter)
    {l l' : L} {a a' : α} {r r' : R} :
    w.cell l a r = w.cell l' a' r' ↔ B.output l a r = B.output l' a' r' := by
  rw [w.output_eq, w.output_eq]; simp

/-- Letter-to-letter-ness transports along state reindexing. -/
def LetterToLetter.reindex {L' R' : Type*} {B : Bimachine L R α β} (w : B.LetterToLetter)
    (eL : L ≃ L') (eR : R ≃ R') : (Bimachine.reindex eL eR B).LetterToLetter :=
  ⟨fun l a r ↦ w.cell (eL.symm l) a (eR.symm r), fun _ _ _ ↦ w.output_eq _ _ _,
    fun _ ↦ w.finalLeft_eq _, fun _ ↦ w.finalRight_eq _⟩

/-! ### Reversal

Read backwards, a bimachine is again a bimachine: the two automata trade sides, as do the two final
functions, and everything emitted is reversed. The mirror computes the reverse conjugate, so the
bimachine-computable functions are closed under `List.revConj`. -/

/-- In the mirror image of `B` the right automaton scans left to right, the left one right to left,
and each block is emitted reversed. -/
@[simps]
def reverse : Bimachine R L α β where
  lInit := B.rInit
  lStep := B.rStep
  rInit := B.lInit
  rStep := B.lStep
  output r a l := (B.output l a r).reverse
  finalLeft l := (B.finalRight l).reverse
  finalRight r := (B.finalLeft r).reverse

@[simp] theorem reverse_reverse : B.reverse.reverse = B := by
  simp [reverse]

@[simp] theorem lStateFrom_reverse (r : R) (xs : List α) :
    B.reverse.lStateFrom r xs = B.rStateFrom r xs.reverse := by
  induction xs generalizing r <;> simp [rStateFrom_append, *]

@[simp] theorem rStateFrom_reverse (l : L) (xs : List α) :
    B.reverse.rStateFrom l xs = B.lStateFrom l xs.reverse := by
  induction xs <;> simp [lStateFrom_append, *]

@[simp] theorem emitted_reverse (r : R) (xs : List α) (l : L) :
    B.reverse.emitted r xs l = (B.emitted l xs.reverse r).reverse := by
  induction xs generalizing r <;> simp [emitted_append, *]

/-- The mirror bimachine computes the reverse conjugate. -/
@[simp] theorem run_reverse : B.reverse.run = List.revConj B.run :=
  funext fun xs ↦ by simp [run, rState, lState, List.revConj, List.append_assoc]

/-- The mirror of a letter-to-letter machine is letter-to-letter. -/
def LetterToLetter.reverse {B : Bimachine L R α β} (w : B.LetterToLetter) :
    B.reverse.LetterToLetter :=
  ⟨fun r a l ↦ w.cell l a r, fun _ _ _ ↦ by simp [w.output_eq], fun _ ↦ by simp [w.finalRight_eq],
    fun _ ↦ by simp [w.finalLeft_eq]⟩

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
def ofFlags_letterToLetter : (ofFlags pL pR out).LetterToLetter where
  cell := out
  output_eq _ _ _ := rfl

@[simp] theorem ofFlags_lStateFrom (l : Bool) (xs : List α) :
    (ofFlags pL pR out).lStateFrom l xs = (l || xs.any pL) := by
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

@[simp] theorem Mealy.emitted_toBimachine (s : σ) (xs : List α) (r : Unit) :
    T.toBimachine.emitted s xs r = T.runFrom s xs := by
  induction xs generalizing s <;> simp [*]

@[simp] theorem Mealy.toBimachine_run : T.toBimachine.run = T.run :=
  funext fun xs ↦ by simp [Bimachine.run, run]

/-- A sequential machine is a letter-to-letter bimachine. -/
def Mealy.toBimachine_letterToLetter : T.toBimachine.LetterToLetter where
  cell l a _ := T.output l a
  output_eq _ _ _ := rfl

end ToBimachine

/-! ### The bimachine-computable class -/

/-- Computability by a finite bimachine — classically, the total rational functions. -/
def IsBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α β),
    B.run = f

theorem Bimachine.isBimachineComputable {L R : Type*} [Fintype L] [Fintype R]
    (B : Bimachine L R α β) : IsBimachineComputable B.run :=
  ⟨Shrink L, inferInstance, Shrink R, inferInstance,
    Bimachine.reindex (equivShrink.{0} L) (equivShrink.{0} R) B, B.run_reindex _ _⟩

/-- The reverse conjugate of a bimachine-computable function is bimachine-computable. -/
protected theorem IsBimachineComputable.revConj {f : List α → List β}
    (h : IsBimachineComputable f) : IsBimachineComputable (List.revConj f) :=
  have ⟨L, _, R, _, B, hB⟩ := h
  ⟨R, ‹_›, L, ‹_›, B.reverse, hB ▸ B.run_reverse⟩

@[simp] theorem isBimachineComputable_revConj_iff {f : List α → List β} :
    IsBimachineComputable (List.revConj f) ↔ IsBimachineComputable f :=
  ⟨fun h ↦ List.revConj_revConj f ▸ h.revConj, .revConj⟩

/-- `f` is computed by a finite **letter-to-letter** bimachine. These are the total
length-preserving rational functions ([eilenberg-1974], Theorem XI.7.1). -/
def IsLengthPreservingBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α β),
    B.IsLetterToLetter ∧ B.run = f

theorem Bimachine.isLengthPreservingBimachineComputable {L R : Type*} [Fintype L]
    [Fintype R] (B : Bimachine L R α β) (h : B.IsLetterToLetter) :
    IsLengthPreservingBimachineComputable B.run :=
  have ⟨w⟩ := h
  ⟨Shrink L, inferInstance, Shrink R, inferInstance,
    Bimachine.reindex (equivShrink.{0} L) (equivShrink.{0} R) B, ⟨w.reindex _ _⟩, B.run_reindex _ _⟩

theorem IsBimachineComputable.of_lengthPreserving {f : List α → List β}
    (h : IsLengthPreservingBimachineComputable f) : IsBimachineComputable f :=
  have ⟨L, _, R, _, B, _, hB⟩ := h
  ⟨L, ‹_›, R, ‹_›, B, hB⟩

theorem IsLengthPreservingBimachineComputable.length_eq {f : List α → List β}
    (h : IsLengthPreservingBimachineComputable f) (x : List α) : (f x).length = x.length :=
  have ⟨_, _, _, _, _, ⟨w⟩, hB⟩ := h
  hB ▸ w.length_run x

theorem IsLengthPreservingBimachineComputable.of_mealyComputable {f : List α → List β}
    (h : IsMealyComputable f) : IsLengthPreservingBimachineComputable f :=
  have ⟨_, _, T, hT⟩ := h
  hT ▸ T.toBimachine_run ▸
    T.toBimachine.isLengthPreservingBimachineComputable ⟨T.toBimachine_letterToLetter⟩

/-- The reverse conjugate of a length-preserving bimachine-computable function is one too. -/
protected theorem IsLengthPreservingBimachineComputable.revConj {f : List α → List β}
    (h : IsLengthPreservingBimachineComputable f) :
    IsLengthPreservingBimachineComputable (List.revConj f) :=
  have ⟨L, _, R, _, B, ⟨w⟩, hB⟩ := h
  ⟨R, ‹_›, L, ‹_›, B.reverse, ⟨w.reverse⟩, hB ▸ B.run_reverse⟩

theorem IsBimachineComputable.of_mealyComputable {f : List α → List β}
    (h : IsMealyComputable f) : IsBimachineComputable f :=
  .of_lengthPreserving (.of_mealyComputable h)
