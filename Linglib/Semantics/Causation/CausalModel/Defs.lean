module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Update
public import Linglib.Core.Data.Part
public import Linglib.Core.Order.WellFoundedFixedPoint

/-!
# Causal models

This file defines causal models in the sense of Halpern and Pearl. A causal model has a type `U`
of exogenous contexts, a value type `α v` for each endogenous variable `v`, a directed graph on
the variables (mathlib's `Digraph`), and for each variable a structural equation that gives its
value from the context and the values of its parents in the graph. When the graph is well
founded, every context determines exactly one assignment that satisfies the equations,
`CausalModel.solve`. An intervention holding the variables of a finite set at given values
replaces their equations by constants, which gives the submodel `CausalModel.intervene`, Pearl's
`M_x`; its solution is the world the intervention brings about.

The solution is characterized as the unique fixed point of one round of the equations, and it is
reached by iterating that round from any assignment once per rank of a ranking of the graph, which
is how a finite model computes it.

## Main definitions

* `CausalModel U V α`: exogenous contexts `U`, a graph, and structural equations
* `CausalModel.IsAcyclic`: the graph is well founded
* `CausalModel.ContextAtRoots`: only the roots read the context
* `CausalModel.step`: one round of the equations
* `CausalModel.solve`: the solution in a context
* `CausalModel.intervene`: the submodel of an intervention, written `M[c ← x, d ← y]` for single
  variables, scoped in `CausalModel`
* `[c ← x, d ← y]`: the partial assignment settling `c` and `d`, an observation, scoped in
  `CausalModel`

## Main results

* `CausalModel.isFixedPt_solve`, `CausalModel.eq_solve_of_isFixedPt`: the solution is the unique
  fixed point of `step`
* `CausalModel.solve_eq_iterate`, `CausalModel.solve_eq_iterate_card`: iterating `step` past a
  ranking of the graph reaches it, so in a finite model `decide` evaluates the solution
  (`CausalModel.decidableEqSolve`)

## Implementation notes

An equation reads the whole assignment, and `dependsOn_eqn` says that it only reads the parents
(mathlib's `DependsOn`), so equations are written without the parents' subtype. For a finite
inductive type of variables the default proof of `dependsOn_eqn` discharges it. The graph is data,
the edges a paper draws, and bounds what an equation may read rather than recording what it does
read; a submodel keeps the graph, since a constant equation reads nothing. An intervention gives
values only to the variables it holds, `x : ∀ v : X, α v`, as Pearl's realization of `X` and
mathlib's `Function.updateFinset` do. The solution is `WellFounded.fixedPoint` of `step`, whose
construction fills the coordinates an equation ignores arbitrarily, hence `[∀ v, Nonempty (α v)]`.

A concrete model in a study is written to one recipe. The exogenous context is a structure whose
fields name what the paper leaves to the world (`structure Context where match : Bool`, with
`deriving DecidableEq, Fintype, Inhabited, Repr`), never a positional tuple. The edges are a
`Finset (V × V)` (`def edges : Finset (V × V) := {(.match, .fire)}`) with `graph :=
⟨fun w v ↦ (w, v) ∈ edges⟩`, adjacency is decided by `fun w v ↦ inferInstanceAs (Decidable
((w, v) ∈ edges))`, and acyclicity by `Finite.wellFounded_of_irrefl_transGen (by decide)`.
Interventions are written `M[c ← x]`, partial assignments `[c ← x, d ← y]`, and updates of a named
assignment `Function.update s c (Part.some x)`. A theorem quantifying over assignments or
settlements (necessity, sufficient sets) is proved structurally through the equations rather than by
`decide`, which enumerates them.

## References

* [halpern-pearl-2005]
* [pearl-2000]
* [bongers-forre-peters-mooij-2021]
-/

@[expose] public section

/-- A causal model is a directed graph on the variables `V` with a structural equation at each
variable. The equation gives the variable's value in `α v` from an exogenous context in `U` and
the values of the variable's parents, the sources of its incoming edges. -/
structure CausalModel (U V : Type*) (α : V → Type*) where
  /-- The causal graph, with an edge from `w` to `v` when `v`'s equation may read `w`. -/
  graph : Digraph V
  /-- The structural equation of each variable, read in a context. -/
  eqn : ∀ v, U → (∀ w, α w) → α v
  /-- Each equation reads only the variable's parents. For a finite inductive type of variables
  whose equations match on the variable, the default proof rewrites each variable an equation
  reads by the hypothesis, deciding that it is a parent. -/
  dependsOn_eqn : ∀ v u, DependsOn (eqn v u) {w | graph.Adj w v} := by
    intro v u x y h; cases v <;> simp (disch := decide) [h]

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α)

/-- A model is acyclic, or recursive, when its graph is well founded. -/
abbrev IsAcyclic : Prop := WellFounded M.graph.Adj

/-- The context reaches a model only at its roots when the equation of every variable with a
parent gives the same value in every context, as in the dynamics of Schulz and Nadathur, whose
inner variables are truth functions of their parents. -/
class ContextAtRoots : Prop where
  eqn_eq_of_adj {v w : V} : M.graph.Adj w v → ∀ u u' y, M.eqn v u y = M.eqn v u' y

theorem IsAcyclic.of_depth (depth : V → ℕ) (h : ∀ {w v}, M.graph.Adj w v → depth w < depth v) :
    M.IsAcyclic :=
  RelHomClass.wellFounded (⟨depth, h⟩ : M.graph.Adj →r (· < ·)) wellFounded_lt

/-- `[c ← x]` is the partial assignment settling `c` to `x` and leaving every other variable
open, in the notation of Halpern and Pearl; `[c ← x, d ← y]` settles both. It serves as an
observation. -/
scoped syntax (name := partialAssignment) "[" (term " ← " term),+ "]" : term

macro_rules (kind := partialAssignment)
  | `([$c ← $x]) => `(Function.update ⊥ $c (Part.some $x))
  | `([$c ← $x, $[$cs ← $xs],*]) => `(Function.update [$[$cs ← $xs],*] $c (Part.some $x))

/-- `M.step u y` applies the equations once in the context `u`, each variable taking the value its
equation gives to `y`. -/
def step (u : U) (y : ∀ v, α v) : ∀ v, α v :=
  fun v ↦ M.eqn v u y

variable {M}

theorem step_apply (u : U) (y : ∀ v, α v) (v : V) : M.step u y v = M.eqn v u y := rfl

theorem dependsOn_step (u : U) (v : V) : DependsOn (M.step u · v) {w | M.graph.Adj w v} :=
  M.dependsOn_eqn v u

section Solve

variable (M) [∀ v, Nonempty (α v)] [hM : M.IsAcyclic]

/-- The solution of the model in the context `u`, the unique assignment satisfying every
equation. -/
noncomputable def solve (u : U) : ∀ v, α v :=
  hM.fixedPoint (M.step u)

/-- The solution satisfies the equations. -/
theorem isFixedPt_solve (u : U) : Function.IsFixedPt (M.step u) (M.solve u) :=
  hM.isFixedPt_fixedPoint (dependsOn_step u)

variable {M}

/-- An assignment satisfying the equations is the solution. -/
theorem eq_solve_of_isFixedPt {u : U} {x : ∀ v, α v} (hx : Function.IsFixedPt (M.step u) x) :
    x = M.solve u :=
  WellFounded.eq_fixedPoint_of_isFixedPt (dependsOn_step u) hx

theorem isFixedPt_iff_eq_solve {u : U} {x : ∀ v, α v} :
    Function.IsFixedPt (M.step u) x ↔ x = M.solve u :=
  WellFounded.isFixedPt_iff_eq_fixedPoint (dependsOn_step u)

theorem solve_apply (u : U) (v : V) : M.solve u v = M.eqn v u (M.solve u) :=
  WellFounded.fixedPoint_apply (dependsOn_step u) v

/-- Iterating the equations from any assignment past a ranking of the graph reaches the
solution. -/
theorem solve_eq_iterate (r : M.graph.Adj →r ((· < ·) : ℕ → ℕ → Prop)) {n : ℕ}
    (hn : ∀ v, r v < n) (u : U) (x : ∀ v, α v) : M.solve u = (M.step u)^[n] x :=
  WellFounded.fixedPoint_eq_iterate (dependsOn_step u) r hn x

/-- In a finite model, iterating the equations once per variable reaches the solution. -/
theorem solve_eq_iterate_card [Fintype V] (u : U) (x : ∀ v, α v) :
    M.solve u = (M.step u)^[Fintype.card V] x :=
  WellFounded.fixedPoint_eq_iterate_card (dependsOn_step u) x

/-- In a finite model the value of the solution at a variable is decided by iterating the
equations. It takes priority over the value type's own decidable equality, which cannot evaluate
`solve`. -/
instance (priority := high) decidableEqSolve [Fintype V] [∀ v, Inhabited (α v)]
    [∀ v, DecidableEq (α v)] (u : U) (v : V) (x : α v) : Decidable (M.solve u v = x) :=
  decidable_of_iff ((M.step u)^[Fintype.card V] default v = x) <| by
    rw [solve_eq_iterate_card u default]

/-- In a finite model, whether the solutions of two models agree at a variable is decided by
iterating the equations of both. -/
instance (priority := high + 1) decidableEqSolveSolve [Fintype V] [∀ v, Inhabited (α v)]
    [∀ v, DecidableEq (α v)] (N : CausalModel U V α) [N.IsAcyclic] (u u' : U) (v : V) :
    Decidable (M.solve u v = N.solve u' v) :=
  decidable_of_iff ((M.step u)^[Fintype.card V] default v =
      (N.step u')^[Fintype.card V] default v) <| by
    rw [solve_eq_iterate_card u default, solve_eq_iterate_card u' default]

end Solve

section Intervene

variable [DecidableEq V]

variable (M) in
/-- The submodel `M.intervene X x` holds the variables of `X` at their values in `x`: their
equations become constants, and every other equation is kept (Pearl's submodel `M_x`). -/
def intervene (X : Finset V) (x : ∀ v : X, α v) : CausalModel U V α where
  graph := M.graph
  eqn v u y := Function.updateFinset (M.step u y) X x v
  dependsOn_eqn v u _ _ h := by
    simp only [Function.updateFinset]
    split
    · rfl
    · exact M.dependsOn_eqn v u h

instance [hM : M.IsAcyclic] (X : Finset V) (x : ∀ v : X, α v) : (M.intervene X x).IsAcyclic :=
  hM

variable {X : Finset V} {x : ∀ v : X, α v} {v : V}

theorem intervene_eqn_of_mem (h : v ∈ X) (u : U) (y : ∀ v, α v) :
    (M.intervene X x).eqn v u y = x ⟨v, h⟩ := by
  simp [intervene, Function.updateFinset, h]

theorem intervene_eqn_of_notMem (h : v ∉ X) (u : U) (y : ∀ v, α v) :
    (M.intervene X x).eqn v u y = M.eqn v u y := by
  simp [intervene, Function.updateFinset, h, step]

/-- `M[c ← x]` is the submodel holding `c` at `x`, and `M[c ← x, d ← y]` intervenes on `c` and
then on `d`. -/
scoped syntax:max (name := interveneNotation) term noWs "[" (term " ← " term),+ "]" : term

macro_rules (kind := interveneNotation)
  | `($M[$c ← $x]) => `(CausalModel.intervene $M (singleton $c) (uniqueElim $x))
  | `($M[$c ← $x, $[$cs ← $xs],*]) =>
    `((CausalModel.intervene $M (singleton $c) (uniqueElim $x))[$[$cs ← $xs],*])

end Intervene

end CausalModel
