/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Linglib.Logic.Trivalent.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

/-!
# Peters-Kleene deployment

Peters-Kleene deployment applies a classical truth function to three-valued arguments one at a
time, from left to right ([george-2014] §3). A classical argument fills the next argument position.
An undefined argument is repaired to either classical value, and the repair succeeds only if the
two values leave the same function of the remaining arguments; otherwise the whole application is
undefined. Each argument position is thus treated by the Strong Kleene principle with the earlier
arguments fixed and the later ones still open, which is Krahmer's middle Kleene intuition made
explicit.

Deploying the classical negation, conjunction, disjunction and material conditional gives exactly
the connectives of [peters-1979], the Middle Kleene connectives `meetMiddle` and `joinMiddle`. As
stipulated truth tables the Peters connectives do not meet the explanatory challenge of
[schlenker-2008a], since nothing selects them among the trivalent extensions of the classical
connectives. Deriving them by deployment does: the rule is uniform, so a connective's projection
behaviour follows from its classical meaning and the order of its arguments.

## Main definitions

* `Trivalent.reduceFirst`: the reduction `f/x` of a truth function by a classical value
  (Definition 12).
* `Trivalent.pkReduce`: the Peters-Kleene reduction `f///X` by a set of classical values
  (Definition 13).
* `Trivalent.deploy`: the Peters-Kleene deployment `f[x₁, …, xₙ]` (Definition 15).
* `Trivalent.deployWith`: deployment on arguments of any type with repair sets, read off
  Definition 13 literally.
* `Trivalent.deploy₁`, `Trivalent.deploy₂`: deployment of unary and binary truth functions.

## Main results

* `Trivalent.deploy_cons_ofProp`, `Trivalent.deploy_cons_zero`: deployment takes its arguments one
  at a time.
* `Trivalent.deploy_ofProp`: on classical arguments, deployment is application (Remark 8).
* `Trivalent.deploy_eq_zero_of_reduceFirst_ne`: an undefined argument in a position that matters
  makes the deployment undefined (generalising Remarks 9 and 10).
* `Trivalent.deploy_eq_deployWith`: on truth values, deployment with the repair sets `toFinset`
  is `deploy`.
* `Trivalent.toFinset_deploy₁`: unary deployment is the Strong Kleene lift.
* `Trivalent.deploy₂_ofProp_left`, `Trivalent.deploy₂_zero_left`: binary deployment is unary
  deployment after its first argument.
* `Trivalent.deploy₁_not`, `Trivalent.deploy₂_and`, `Trivalent.deploy₂_or`,
  `Trivalent.deploy₂_imp`, `Trivalent.Connectives.middleKleene_eq_deploy`: deployment of the
  classical connectives gives the Peters connectives (Proposition 3, whose cells include
  Remarks 11 and 12).

## Implementation notes

An `n`-ary truth function is a function on `Fin n → Bool`, and a `0`-ary one is identified with
its value. A failed reduction is `none` rather than George's constant function to the failure
value, which deployment then sends to `0`. The repair set of a value (Definition 14) is
`SignType.toFinset`. Choosing `true` or `false` as the member to reduce by is specific to `Bool`
and keeps `deploy` computable. Repair sets of predicates over an infinite domain ([george-2014]
§4) need George's existential formulation of Definition 13, which `deployWith` follows.

## References

* [george-2014]
* [peters-1979]
* [kleene-1952]
* [schlenker-2008a]
-/

@[expose] public section

namespace Trivalent

open SignType

variable {n : ℕ}

/-- The reduction `f/x` of an `n + 1`-ary function into truth values by an argument fills its
first argument position. -/
def reduceFirst {α : Type*} (f : (Fin (n + 1) → α) → Bool) (x : α) : (Fin n → α) → Bool :=
  fun ys ↦ f (Fin.cons x ys)

@[simp] theorem reduceFirst_apply {α : Type*} (f : (Fin (n + 1) → α) → Bool) (x : α)
    (ys : Fin n → α) : reduceFirst f x ys = f (Fin.cons x ys) := rfl

/-- On a unary function, reduction is application (Remark 6). -/
theorem reduceFirst_unary (f : (Fin 1 → Bool) → Bool) (x : Bool) : reduceFirst f x ![] = f ![x] :=
  rfl

/-- The Peters-Kleene reduction `f///X` is the reduction of `f` by any member of `X` when every
member gives the same reduction, and fails otherwise. It reduces by `true` when `X` contains it
and by `false` otherwise, which for a nonempty `X` is a member; Definition 13 requires `X`
nonempty, and on `∅` the reduction is by `false`. -/
def pkReduce (f : (Fin (n + 1) → Bool) → Bool) (X : Finset Bool) :
    Option ((Fin n → Bool) → Bool) :=
  if ∀ x ∈ X, ∀ y ∈ X, reduceFirst f x = reduceFirst f y then
    some (reduceFirst f (decide (true ∈ X)))
  else none

/-- Peters-Kleene reduction by a single value is reduction by that value (Remark 7). -/
@[simp] theorem pkReduce_singleton (f : (Fin (n + 1) → Bool) → Bool) (x : Bool) :
    pkReduce f {x} = some (reduceFirst f x) := by
  cases x <;> simp [pkReduce]

theorem pkReduce_toFinset_zero (f : (Fin (n + 1) → Bool) → Bool) :
    pkReduce f (toFinset 0) =
      if reduceFirst f true = reduceFirst f false then some (reduceFirst f true) else none := by
  by_cases h : reduceFirst f true = reduceFirst f false <;> simp [pkReduce, h, eq_comm]

/-- The Peters-Kleene deployment `f[x₁, …, xₙ]` Peters-Kleene reduces `f` by the repair set of
each argument in turn, following George's convention `f[x₁, …, xₙ] = f[x₁]…[xₙ]`, and is
undefined once a reduction fails. -/
def deploy : {n : ℕ} → ((Fin n → Bool) → Bool) → (Fin n → SignType) → SignType
  | 0, f, _ => ofProp (f ![])
  | _ + 1, f, x =>
    match pkReduce f (toFinset (x 0)) with
    | some g => deploy g (Fin.tail x)
    | none => 0

/-- A classical first argument fills the first argument position. -/
theorem deploy_cons_ofProp (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (x : Fin n → SignType) :
    deploy f (Fin.cons (ofProp b) x) = deploy (reduceFirst f b) x := by
  have h : toFinset (ofProp b) = {b} := by cases b <;> rfl
  rw [deploy, Fin.cons_zero, h, pkReduce_singleton, Fin.tail_cons]

/-- An undefined first argument is skipped if its position does not matter, and makes the
deployment undefined otherwise. -/
theorem deploy_cons_zero (f : (Fin (n + 1) → Bool) → Bool) (x : Fin n → SignType) :
    deploy f (Fin.cons 0 x) =
      if reduceFirst f true = reduceFirst f false then deploy (reduceFirst f true) x else 0 := by
  rw [deploy, Fin.cons_zero, pkReduce_toFinset_zero, Fin.tail_cons]
  split_ifs <;> rfl

/-- On classical arguments, deployment is application (Remark 8). -/
theorem deploy_ofProp (f : (Fin n → Bool) → Bool) (b : Fin n → Bool) :
    deploy f (fun i ↦ ofProp (b i)) = ofProp (f b) := by
  induction n with
  | zero => rw [deploy, Subsingleton.elim b ![]]
  | succ n ih =>
    have h : toFinset (ofProp (b 0)) = {b 0} := by cases b 0 <;> rfl
    rw [deploy, h, pkReduce_singleton]
    exact (ih _ (Fin.tail b)).trans (by rw [reduceFirst, Fin.cons_self_tail])

/-- An undefined argument in a position whose value matters makes the deployment undefined,
generalising Remarks 9 and 10. -/
theorem deploy_eq_zero_of_reduceFirst_ne {f : (Fin (n + 1) → Bool) → Bool}
    (h : reduceFirst f true ≠ reduceFirst f false) {x : Fin (n + 1) → SignType} (hx : x 0 = 0) :
    deploy f x = 0 := by
  simp only [deploy, hx, pkReduce_toFinset_zero, h, ite_false]

/-! ### Deployment over arbitrary repair sets

Deployment needs only a repair set for each argument, so it applies to any function into truth
values once its arguments have repairs ([george-2014] §4.1). `deployWith rep` deploys a function
of arguments in `α` on arguments in `β`, with repair sets given by `rep`, reading Definition 13
literally: the reduction by a nonempty repair set succeeds when one function is the reduction by
every member. On truth values with `toFinset` as the repair set it is `deploy`
(`deploy_eq_deployWith`). All argument positions share one type, which covers the quantifiers
and determiners of [george-2014] but not a function mixing predicates and truth values. -/

section DeployWith

variable {α β : Type*} (rep : β → Set α)

open Classical in
/-- The Peters-Kleene deployment of a function of arguments in `α` on arguments in `β`, with
repair sets given by `rep`. An empty repair set makes the deployment undefined, which Definition 13
leaves open since George's repair sets are never empty. -/
noncomputable def deployWith : {n : ℕ} → ((Fin n → α) → Bool) → (Fin n → β) → SignType
  | 0, f, _ => ofProp (f ![])
  | _ + 1, f, x =>
    if h : ∃ g, (rep (x 0)).Nonempty ∧ ∀ a ∈ rep (x 0), reduceFirst f a = g then
      deployWith h.choose (Fin.tail x)
    else 0

variable {rep}

theorem deployWith_zero (f : (Fin 0 → α) → Bool) (x : Fin 0 → β) :
    deployWith rep f x = ofProp (f ![]) := by
  rw [deployWith]

/-- If every member of a nonempty repair set of the first argument gives the same reduction, the
deployment continues with that reduction. -/
theorem deployWith_succ_of_forall {f : (Fin (n + 1) → α) → Bool} {x : Fin (n + 1) → β}
    {g : (Fin n → α) → Bool} (hne : (rep (x 0)).Nonempty)
    (h : ∀ a ∈ rep (x 0), reduceFirst f a = g) :
    deployWith rep f x = deployWith rep g (Fin.tail x) := by
  have hex : ∃ g, (rep (x 0)).Nonempty ∧ ∀ a ∈ rep (x 0), reduceFirst f a = g := ⟨g, hne, h⟩
  obtain ⟨a, ha⟩ := hne
  rw [deployWith, dite_eq_left_of_eq_true (eq_true hex), ← h a ha,
    (Classical.choose_spec hex).2 a ha]

/-- If two repairs of the first argument give different reductions, the deployment is
undefined. -/
theorem deployWith_succ_of_ne {f : (Fin (n + 1) → α) → Bool} {x : Fin (n + 1) → β} {a b : α}
    (ha : a ∈ rep (x 0)) (hb : b ∈ rep (x 0)) (hab : reduceFirst f a ≠ reduceFirst f b) :
    deployWith rep f x = 0 := by
  rw [deployWith, dite_eq_right_of_eq_false (eq_false ?_)]
  rintro ⟨g, -, h⟩
  exact hab ((h a ha).trans (h b hb).symm)

/-- On truth values, deployment by `toFinset` is `deploy`. -/
theorem deploy_eq_deployWith (f : (Fin n → Bool) → Bool) (x : Fin n → SignType) :
    deploy f x = deployWith (fun s ↦ ↑(toFinset s)) f x := by
  induction n with
  | zero => rw [deploy, deployWith_zero]
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    generalize x 0 = s, Fin.tail x = y
    have hs : ∀ b : Bool, s = ofProp b → deploy f (Fin.cons s y) =
        deployWith (fun s ↦ ↑(toFinset s)) f (Fin.cons s y) := by
      rintro b rfl
      rw [deploy_cons_ofProp, ih, deployWith_succ_of_forall (g := reduceFirst f b)
        (by cases b <;> simp) fun a ha ↦ by cases b <;> simp_all, Fin.tail_cons]
    cases s
    · rw [show SignType.zero = 0 from rfl, deploy_cons_zero]
      split_ifs with h
      · rw [ih, deployWith_succ_of_forall (g := reduceFirst f true) (by simp) fun a ha ↦ by
          cases a <;> simp_all, Fin.tail_cons]
      · rw [deployWith_succ_of_ne (a := true) (b := false) (by simp) (by simp) h]
    · exact hs false rfl
    · exact hs true rfl

end DeployWith

/-! ### Unary and binary deployment -/

/-- The deployment of a unary truth function. -/
def deploy₁ (f : Bool → Bool) (x : SignType) : SignType :=
  deploy (fun v ↦ f (v 0)) ![x]

/-- The deployment of a binary truth function, its first argument first. -/
def deploy₂ (f : Bool → Bool → Bool) (x y : SignType) : SignType :=
  deploy (fun v ↦ f (v 0) (v 1)) ![x, y]

/-- Unary deployment is the Strong Kleene lift: it leaves open the classical values `f` takes on
the repair set of its argument. -/
theorem toFinset_deploy₁ (f : Bool → Bool) (x : SignType) :
    toFinset (deploy₁ f x) = (toFinset x).image f := by
  revert f x; decide

/-- After a classical first argument, binary deployment is unary deployment. -/
theorem deploy₂_ofProp_left (f : Bool → Bool → Bool) (b : Bool) (y : SignType) :
    deploy₂ f (ofProp b) y = deploy₁ (f b) y := by
  rw [deploy₂, deploy₁, Matrix.vecCons, deploy_cons_ofProp]; rfl

/-- After an undefined first argument, binary deployment is unary deployment if the first
position does not matter, and undefined otherwise. -/
theorem deploy₂_zero_left (f : Bool → Bool → Bool) (y : SignType) :
    deploy₂ f 0 y = if f true = f false then deploy₁ (f true) y else 0 := by
  revert f y; decide

/-! ### The Peters connectives -/

/-- Deploying classical negation gives Kleene's negation (Proposition 3). -/
@[simp] theorem deploy₁_not : deploy₁ (!·) = Neg.neg := by
  funext x; revert x; decide

/-- Deploying classical conjunction gives Peters' conjunction (Proposition 3). -/
@[simp] theorem deploy₂_and : deploy₂ (· && ·) = meetMiddle := by
  funext x y; revert x y; decide

/-- Deploying classical disjunction gives Peters' disjunction (Proposition 3). -/
@[simp] theorem deploy₂_or : deploy₂ (· || ·) = joinMiddle := by
  funext x y; revert x y; decide

/-- Deploying the classical material conditional gives Peters' conditional (Proposition 3). -/
@[simp] theorem deploy₂_imp : deploy₂ (fun a b ↦ !a || b) = fun x y ↦ joinMiddle (-x) y := by
  funext x y; revert x y; decide

/-- The Middle Kleene connectives are the Peters-Kleene deployments of the classical ones. -/
theorem Connectives.middleKleene_eq_deploy :
    Connectives.middleKleene =
      ⟨deploy₂ (· && ·), deploy₂ (· || ·), deploy₂ fun a b ↦ !a || b⟩ := by
  rw [deploy₂_and, deploy₂_or, deploy₂_imp]; rfl

end Trivalent
