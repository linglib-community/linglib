/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Fintype.Shrink

/-!
# Mealy machines

A Mealy machine is a deterministic transducer which reads its input left to
right and emits exactly one output symbol per input symbol, so the function it computes
is length-preserving by construction. Output coordinate `i` of the run is the output
at the state reached after the length-`i` input prefix (`Mealy.getElem?_run`),
so the run of a prefix is the prefix of the run (`Mealy.run_take`).

Note that this definition allows for machines with infinite states; a `Fintype`
instance must be supplied for the finite-state class `IsMealyComputable`.

## Main definitions

* `Mealy σ α β`: transducer with states `σ`, input alphabet `α`, output alphabet `β`
* `Mealy.evalFrom`, `Mealy.eval`: the state reached after reading a word
* `Mealy.run`, `Mealy.runRight`: the left-to-right and right-to-left passes
* `Mealy.comp`: the cascade connection, computing the composite function
* `Mealy.ofFn`: the single-state machine applying a fixed symbol map letter-wise
* `Mealy.ofFlag`: the one-bit machine tracking whether an earlier symbol satisfies `p`
* `Mealy.map`: transport along an equivalence on states
* `IsMealyComputable f`: `f` is computed by some finite-state `Mealy`

## Main theorems

* `Mealy.getElem?_run`: output coordinate `i` is the output at the state reached
  after the length-`i` input prefix
* `Mealy.run_take`: the run of a prefix is the prefix of the run
* `Mealy.getElem?_runRight`: output coordinate `i` of the right-to-left pass is the output at
  the state reached over the reversed strict suffix
* `Mealy.getElem?_ofFlag_run`, `Mealy.getElem?_ofFlag_runRight`: each coordinate of a
  flag machine sees the flag over its strict prefix (its strict suffix, for the
  right-to-left pass)
* `Mealy.isMealyComputable`: a finite-state machine computes a Mealy-computable function,
  whatever the universe of its state type
* `IsMealyComputable.comp`: closure under composition

## Implementation notes

The functions computed by Mealy machines are the *sequential functions* of Holcombe's
algebraic automata theory. `SubsequentialTransducer` generalizes to word-block outputs and
a state-final output, after Mohri; `Mealy.toSubsequentialTransducer` exhibits a Mealy
machine as the singleton-output, empty-flush case.

`IsMealyComputable` pins the state type at `Type`, as `Language.IsRegular` does;
`Mealy.isMealyComputable` reaches it from any universe through `Shrink`.

[UPSTREAM] candidate: `Mathlib.Computability.Mealy`.

The Myhill–Nerode characterization of the Mealy-computable functions by their
residuals is in `Core/Computability/Residual.lean`.

## TODO

* Mealy machine homomorphisms in Holcombe's sense, with `map` at an equivalence as the
  isomorphism case.
* The right-scan mirror via reverse conjugation.
* Moore machines (state-determined output) and the Mealy–Moore equivalence: same
  states one way, `σ × β` states the other, so the computable classes coincide.
* The graph view: the zipped graph of a Mealy-computable map is a regular language
  over `α × β` (the synchronous rational relations). Residuals of the map correspond
  to left quotients of the graph, so this would derive `isMealyComputable_iff_residual`
  from the language Myhill–Nerode theorem.

## References

* [mealy-1955]
* [holcombe-1982]
* [mohri-1997]
-/

@[expose] public section

variable {σ α β : Type*}

/-- A Mealy machine is a set of states (`σ`), a starting state (`start`), a
transition function (`step`) and an output function (`output`); it is letter-to-letter,
emitting exactly one output symbol per input symbol. -/
@[ext]
structure Mealy (σ α β : Type*) where
  /-- The machine starts in this state. -/
  start : σ
  /-- The transition function gives the state reached on reading a symbol. -/
  step : σ → α → σ
  /-- The output function gives the symbol emitted on reading an input symbol in a state. -/
  output : σ → α → β

instance [Inhabited σ] [Inhabited β] : Inhabited (Mealy σ α β) :=
  ⟨⟨default, fun _ _ ↦ default, fun _ _ ↦ default⟩⟩

namespace Mealy

variable (T : Mealy σ α β)

/-- `T.evalFrom s x` evaluates `T` with input `x` starting from the state `s`. -/
def evalFrom (s : σ) : List α → σ := List.foldl T.step s

/-- `T.eval x` evaluates `T` with input `x` starting from the state `T.start`. -/
def eval : List α → σ := T.evalFrom T.start

/-- `T.runFrom s x` runs `T` on the input `x` starting from the state `s`, emitting one
output symbol per input symbol. -/
def runFrom : σ → List α → List β
  | _, [] => []
  | s, x :: xs => T.output s x :: runFrom (T.step s x) xs

/-- `T.run x` runs `T` on the input `x` starting from the state `T.start`. -/
def run : List α → List β := T.runFrom T.start

/-- `T.runRight x` runs `T` right-to-left on the input `x`. -/
def runRight (xs : List α) : List β := (T.run xs.reverse).reverse

section
variable (s : σ) (x : α) (xs ys : List α)

@[simp] theorem runFrom_nil : T.runFrom s [] = [] := rfl
@[simp] theorem runFrom_cons :
    T.runFrom s (x :: xs) = T.output s x :: T.runFrom (T.step s x) xs := rfl
@[simp] theorem evalFrom_nil : T.evalFrom s [] = s := rfl
@[simp] theorem evalFrom_cons : T.evalFrom s (x :: xs) = T.evalFrom (T.step s x) xs := rfl
@[simp] theorem eval_nil : T.eval [] = T.start := rfl

theorem evalFrom_append : T.evalFrom s (xs ++ ys) = T.evalFrom (T.evalFrom s xs) ys :=
  List.foldl_append

theorem runFrom_append :
    T.runFrom s (xs ++ ys) = T.runFrom s xs ++ T.runFrom (T.evalFrom s xs) ys := by
  induction xs generalizing s <;> simp [*]

@[simp] theorem length_runFrom : (T.runFrom s xs).length = xs.length := by
  induction xs generalizing s <;> simp [*]

@[simp] theorem length_run : (T.run xs).length = xs.length := T.length_runFrom T.start xs

@[simp] theorem length_runRight : (T.runRight xs).length = xs.length := by simp [runRight]

@[simp] theorem runRight_reverse : T.runRight xs.reverse = (T.run xs).reverse := by
  simp [runRight]

@[simp] theorem runRight_nil : T.runRight [] = [] := rfl

@[simp] theorem runRight_cons :
    T.runRight (x :: xs) = T.output (T.eval xs.reverse) x :: T.runRight xs := by
  simp [runRight, run, eval, runFrom_append]

theorem getElem?_runFrom (i : ℕ) :
    (T.runFrom s xs)[i]? = xs[i]?.map (T.output (T.evalFrom s (xs.take i))) := by
  induction xs generalizing s i <;> cases i <;> simp [*]

theorem getElem?_run (i : ℕ) :
    (T.run xs)[i]? = xs[i]?.map (T.output (T.eval (xs.take i))) :=
  T.getElem?_runFrom T.start xs i

theorem runFrom_take (n : ℕ) : T.runFrom s (xs.take n) = (T.runFrom s xs).take n := by
  induction xs generalizing s n <;> cases n <;> simp [*]

theorem run_take (n : ℕ) : T.run (xs.take n) = (T.run xs).take n := T.runFrom_take T.start xs n

theorem getElem?_runRight (i : ℕ) :
    (T.runRight xs)[i]? =
      xs[i]?.map (T.output (T.eval (xs.drop (i + 1)).reverse)) := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp [ih]

end

/-! ### Composition -/

section Comp

variable {γ σ' : Type*} (T₂ : Mealy σ' β γ) (T₁ : Mealy σ α β)

/-- `T₂.comp T₁` feeds the outputs of `T₁` to `T₂` — the cascade connection of
[holcombe-1982] — computing `T₂.run ∘ T₁.run`. -/
@[simps]
def comp : Mealy (σ' × σ) α γ where
  start := (T₂.start, T₁.start)
  step p a := (T₂.step p.1 (T₁.output p.2 a), T₁.step p.2 a)
  output p a := T₂.output p.1 (T₁.output p.2 a)

@[simp] theorem runFrom_comp (p : σ' × σ) (xs : List α) :
    (T₂.comp T₁).runFrom p xs = T₂.runFrom p.1 (T₁.runFrom p.2 xs) := by
  induction xs generalizing p <;> simp [*]

@[simp] theorem run_comp : (T₂.comp T₁).run = T₂.run ∘ T₁.run := by
  funext xs; simp [run]

end Comp

/-! ### Letter-wise machines -/

/-- `ofFn h` is the single-state machine applying `h` to every symbol. -/
def ofFn (h : α → β) : Mealy Unit α β where
  start := ()
  step _ _ := ()
  output _ := h

@[simp] theorem ofFn_output (h : α → β) (u : Unit) : (ofFn h).output u = h := rfl

@[simp] theorem ofFn_run (h : α → β) (xs : List α) : (ofFn h).run xs = xs.map h := by
  show (ofFn h).runFrom () xs = _
  induction xs <;> simp [*]

/-! ### Flag machines -/

section Flag

variable (p : α → Bool) (out : Bool → α → β)

/-- The Mealy machine whose state is the monotone flag "a symbol satisfying `p` has
occurred". -/
def ofFlag : Mealy Bool α β where
  start := false
  step b a := b || p a
  output := out

@[simp] theorem ofFlag_start : (ofFlag p out).start = false := rfl

@[simp] theorem ofFlag_step (b : Bool) (a : α) :
    (ofFlag p out).step b a = (b || p a) := rfl

@[simp] theorem ofFlag_output : (ofFlag p out).output = out := rfl

@[simp] theorem ofFlag_evalFrom (b : Bool) (xs : List α) :
    (ofFlag p out).evalFrom b xs = (b || xs.any p) := by
  induction xs generalizing b <;> simp [*, Bool.or_assoc]

@[simp] theorem ofFlag_eval (xs : List α) : (ofFlag p out).eval xs = xs.any p := by
  simp [eval]

theorem getElem?_ofFlag_run (xs : List α) (i : ℕ) :
    ((ofFlag p out).run xs)[i]? = xs[i]?.map (out ((xs.take i).any p)) := by
  simp [getElem?_run]

theorem getElem?_ofFlag_runRight (xs : List α) (i : ℕ) :
    ((ofFlag p out).runRight xs)[i]? = xs[i]?.map (out ((xs.drop (i + 1)).any p)) := by
  simp [getElem?_runRight]

end Flag

/-! ### Transport along state equivalences -/

variable {τ : Type*}

/-- Transport a Mealy machine along an equivalence on states. -/
@[simps]
def map (g : σ ≃ τ) (T : Mealy σ α β) : Mealy τ α β where
  start := g T.start
  step t x := g (T.step (g.symm t) x)
  output t x := T.output (g.symm t) x

@[simp] theorem map_refl : map (Equiv.refl σ) T = T := rfl

@[simp] theorem map_map {υ : Type*} (g : σ ≃ τ) (h : τ ≃ υ) :
    map h (map g T) = map (g.trans h) T := rfl

@[simp] theorem evalFrom_map (g : σ ≃ τ) (t : τ) (xs : List α) :
    (map g T).evalFrom t xs = g (T.evalFrom (g.symm t) xs) := by
  induction xs generalizing t <;> simp [*]

@[simp] theorem runFrom_map (g : σ ≃ τ) (t : τ) (xs : List α) :
    (map g T).runFrom t xs = T.runFrom (g.symm t) xs := by
  induction xs generalizing t <;> simp [*]

@[simp] theorem run_map (g : σ ≃ τ) : (map g T).run = T.run := by
  funext xs; simp [run]

end Mealy

/-! ### The Mealy-computable class -/

/-- `f` is computed by some finite-state `Mealy` machine. -/
def IsMealyComputable (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : Mealy σ α β), T.run = f

theorem Mealy.isMealyComputable {σ : Type*} [Fintype σ] (T : Mealy σ α β) :
    IsMealyComputable T.run :=
  ⟨Shrink σ, inferInstance, T.map (equivShrink.{0} σ), T.run_map _⟩

theorem IsMealyComputable.comp {γ : Type*} {g : List β → List γ} {f : List α → List β}
    (hg : IsMealyComputable g) (hf : IsMealyComputable f) :
    IsMealyComputable (g ∘ f) := by
  obtain ⟨σ₂, _, T₂, rfl⟩ := hg
  obtain ⟨σ₁, _, T₁, rfl⟩ := hf
  exact ⟨σ₂ × σ₁, inferInstance, T₂.comp T₁, T₂.run_comp T₁⟩

theorem isMealyComputable_map (h : α → β) : IsMealyComputable (List.map h) :=
  funext (Mealy.ofFn_run h) ▸ (Mealy.ofFn h).isMealyComputable

theorem isMealyComputable_id : IsMealyComputable (id : List α → List α) := by
  simpa using isMealyComputable_map (id : α → α)

