/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Tactic.SplitIfs

/-!
# Selection rules and their states

A head merges with the constituents it selects. A *selection rule* `S` on a type `α` of items and a
type `R` of residues says when a head with residue `r` selects a sister whose head is `b` and whose
residue is `u`, `S.Selects r b u`, and what it has left to select afterwards, `S.rest r b u`. A
constituent under the rule is its projecting head with the residue of that head. Of two sisters the
one that selects the other projects; where each selects the other the rule says which head outranks
the other, and where neither selects, or neither outranks, the node has no head.

The states of a rule are its constituents together with `0`, the failure of Merge. Their
product is the constituent that projects, after it has selected its sister. It makes them a
commutative magma with zero, so a selection state extends from lexical items to syntactic objects
as a morphism of magmas (`Minimalist.Licensing`), and the head of a product is the head of a factor.

## Main definitions

* `Minimalist.SelectionRule`: a selection rule on items and residues.
* `Minimalist.SelectionRule.Constituent`: a projecting head with its residue.
* `Minimalist.SelectionRule.Constituent.Projects`: one constituent projects over a sister.
* `Minimalist.SelectionRule.State`: a constituent or `0`, a `CommMagma` and `MulZeroClass`.
* `Minimalist.SelectionRule.State.head`, `Minimalist.SelectionRule.State.residual`: the
  projecting head of a state and its residue.
* `Minimalist.SelectionRule.State.side`, `Minimalist.SelectionRule.State.Projects`: which of two
  sisters projects.
* `Minimalist.SelectionRule.State.map`: the state with its head relabelled.

## Main results

* `Minimalist.SelectionRule.Constituent.Projects.asymm`: of two sisters at most one projects.
* `Minimalist.SelectionRule.State.head_mul`: the head of a product is a factor's head.
* `Minimalist.SelectionRule.State.mul_self`: no constituent merges with itself.
* `Minimalist.SelectionRule.State.foldl_mul_of`: along a spine the product is iterated selection.

## Implementation notes

The items are a parameter. A rule reads nothing off an item except through `Selects`, `rest` and
`Outranks`, so the states are defined before any lexicon is.

A rule is a term, and its constituents and states are types indexed by it, as the quotient by a
congruence is indexed by the congruence. Two rules on the same residues then have different
states, each with its own product, and a statement names the rule it is about.

`S.State` is a one-field structure over `Option S.Constituent`, so that the product can be an
instance on it: the `Option` is implementation, and `0` is the public spelling of the failure, the
off-domain value of a partial head function. There is no `One` and no associativity claim, so the
states are a `CommMagma` and `MulZeroClass` only.

## References

* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
* [adger-2003]
-/

@[expose] public section

namespace Minimalist

/-- A selection rule on items `α` and residues `R`: when a head selects a sister, what it has left
to select afterwards, and which of two heads projects when each selects the other. -/
structure SelectionRule (α : Type*) (R : Type*) where
  /-- A head with residue `r` selects a sister whose head is `b` and whose residue is `u`. -/
  Selects : R → α → R → Prop
  /-- Selection is decidable, so that the product computes. -/
  [decidableSelects : ∀ r b u, Decidable (Selects r b u)]
  /-- The residue left to a head with residue `r` once it has selected such a sister. -/
  rest : R → α → R → R
  /-- `Outranks a b` holds when, of two sisters that each select the other, the one headed by `a`
  projects over the one headed by `b`. -/
  Outranks : α → α → Prop := fun _ _ ↦ False
  /-- Outranking is decidable, so that the product computes. -/
  [decidableOutranks : DecidableRel Outranks]
  /-- No two heads outrank each other. -/
  outranks_asymm : ∀ ⦃a b⦄, Outranks a b → ¬ Outranks b a := by exact fun _ _ h ↦ h.elim

namespace SelectionRule

variable {α R : Type*}

instance (S : SelectionRule α R) (r : R) (b : α) (u : R) :
    Decidable (S.Selects r b u) :=
  S.decidableSelects r b u

instance (S : SelectionRule α R) : DecidableRel S.Outranks := S.decidableOutranks

/-- The residue left to a head with residue `r` once it selects a sister whose head is `b` and
whose residue is `u`, and `none` when it does not select it. -/
def select (S : SelectionRule α R) (r : R) (b : α) (u : R) : Option R :=
  if S.Selects r b u then some (S.rest r b u) else none

theorem select_eq_some_iff {S : SelectionRule α R} {r u r' : R} {b : α} :
    S.select r b u = some r' ↔ S.Selects r b u ∧ S.rest r b u = r' := by
  simp [select]

theorem select_eq_none_iff {S : SelectionRule α R} {r u : R} {b : α} :
    S.select r b u = none ↔ ¬ S.Selects r b u := by
  simp [select]

/-- A constituent under the rule `S`: its projecting head with what that head has yet to
select. -/
structure Constituent (S : SelectionRule α R) where
  /-- The projecting head. -/
  head : α
  /-- What the head has yet to select. -/
  residue : R
  deriving DecidableEq

namespace Constituent

variable {S : SelectionRule α R} {x y : S.Constituent}

/-- `x` projects over its sister `y`: it selects `y`, and where `y` selects it too, its head
outranks the head of `y`. -/
def Projects (x y : S.Constituent) : Prop :=
  S.Selects x.residue y.head y.residue ∧
    (S.Selects y.residue x.head x.residue → S.Outranks x.head y.head)

instance (x y : S.Constituent) : Decidable (x.Projects y) := inferInstanceAs (Decidable (_ ∧ _))

/-- Of two sisters at most one projects. -/
theorem Projects.asymm (h : x.Projects y) : ¬ y.Projects x :=
  fun h' ↦ S.outranks_asymm (h.2 h'.1) (h'.2 h.1)

theorem not_projects_self (x : S.Constituent) : ¬ x.Projects x := fun h ↦ h.asymm h

/-- The constituent `x` once it has selected `y`. -/
def select (x y : S.Constituent) : S.Constituent := ⟨x.head, S.rest x.residue y.head y.residue⟩

@[simp] theorem head_select (x y : S.Constituent) : (x.select y).head = x.head := rfl

/-- The constituent with its head relabelled by `f`. -/
def map (f : α → α) (x : S.Constituent) : S.Constituent :=
  ⟨f x.head, x.residue⟩

end Constituent

/-- A state of the rule `S`: a constituent, or `0` where Merge has failed. -/
structure State (S : SelectionRule α R) where
  /-- The constituent, `none` for `0`. -/
  toOption : Option S.Constituent
  deriving DecidableEq

namespace State

variable {S : SelectionRule α R}

/-- The state with projecting head `tok` and residue `r`. -/
def of (tok : α) (r : R) : S.State := ⟨some ⟨tok, r⟩⟩

instance : Zero S.State := ⟨⟨none⟩⟩

/-- Recursor for `SelectionRule.State` using the preferred forms `0` and `of tok r`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recZeroOf {motive : S.State → Sort*} (zero : motive 0)
    (of : ∀ tok r, motive (of tok r)) : ∀ x, motive x
  | ⟨none⟩ => zero
  | ⟨some ⟨tok, r⟩⟩ => of tok r

/-- The projecting head, and `none` for `0`. -/
def head (x : S.State) : Option α := x.toOption.map (·.head)

/-- The residue of the projecting head, and `none` for `0`. -/
def residual (x : S.State) : Option R := x.toOption.map (·.residue)

@[simp] theorem head_of (tok : α) (r : R) : (of tok r : S.State).head = some tok :=
  rfl

@[simp] theorem head_zero : (0 : S.State).head = none := rfl

/-- A state other than `0` has a head. -/
theorem exists_head_of_ne_zero {x : S.State} (h : x ≠ 0) : ∃ t, x.head = some t := by
  rcases x with ⟨_ | c⟩
  · exact absurd rfl h
  · exact ⟨c.head, rfl⟩

@[simp] theorem residual_of (tok : α) (r : R) :
    (of tok r : S.State).residual = some r :=
  rfl

@[simp] theorem residual_zero : (0 : S.State).residual = none := rfl

@[simp] theorem of_ne_zero (tok : α) (r : R) : (of tok r : S.State) ≠ 0 :=
  mt (congrArg toOption) (Option.some_ne_none _)

/-- The state with its head relabelled by `f`. -/
def map (f : α → α) (x : S.State) : S.State :=
  ⟨x.toOption.map (Constituent.map f)⟩

@[simp] theorem map_zero (f : α → α) : (0 : S.State).map f = 0 :=
  rfl

@[simp] theorem map_of (f : α → α) (tok : α)
    (r : R) : (of tok r : S.State).map f = of (f tok) r :=
  rfl

@[simp] theorem head_map (f : α → α) (x : S.State) :
    (x.map f).head = x.head.map f := by
  cases x <;> rfl

/-! ### The product -/

/-- Merge of two constituents: the one that projects, once it has selected the other, and `0`
where neither projects. -/
def merge (x y : S.Constituent) : S.State :=
  if x.Projects y then ⟨some (x.select y)⟩ else if y.Projects x then ⟨some (y.select x)⟩ else 0

theorem merge_comm (x y : S.Constituent) : merge x y = merge y x := by
  unfold merge
  by_cases h : x.Projects y
  · simp [h, h.asymm]
  · by_cases h' : y.Projects x <;> simp [h, h']

theorem merge_of_projects {x y : S.Constituent} (h : x.Projects y) :
    merge x y = ⟨some (x.select y)⟩ :=
  if_pos h

theorem merge_eq_zero {x y : S.Constituent} (h : ¬ x.Projects y) (h' : ¬ y.Projects x) :
    merge x y = 0 := by
  simp [merge, h, h']

/-- The product of two selection states is the sister that projects, once it has selected the
other, and `0` where no sister projects. -/
instance : MulZeroClass S.State where
  mul
    | ⟨some x⟩, ⟨some y⟩ => merge x y
    | _, _ => 0
  zero := 0
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | _⟩ <;> rfl

theorem of_mul_of (a b : α) (r u : R) :
    (of a r * of b u : S.State) = merge ⟨a, r⟩ ⟨b, u⟩ :=
  rfl

instance : CommMagma S.State where
  mul_comm x y := by
    rcases x with ⟨_ | x⟩ <;> rcases y with ⟨_ | y⟩ <;> first | rfl | exact merge_comm x y

/-- No constituent merges with itself, since no constituent projects over itself. -/
@[simp] theorem mul_self (x : S.State) : x * x = 0 := by
  rcases x with ⟨_ | x⟩
  · rfl
  · exact merge_eq_zero x.not_projects_self x.not_projects_self

/-- The head of a merger is the head of one of the two constituents. -/
theorem head_merge (x y : S.Constituent) {t : α} (h : t ∈ (merge x y).head) :
    t = x.head ∨ t = y.head := by
  unfold merge at h
  split_ifs at h
  · exact .inl (Option.some.inj h).symm
  · exact .inr (Option.some.inj h).symm
  · cases h

/-- The head of a product of selection states is one of its factors' heads. -/
theorem head_mul {x y : S.State} {t : α} (h : t ∈ (x * y).head) :
    t ∈ x.head ∨ t ∈ y.head := by
  rcases x with ⟨_ | x⟩ <;> rcases y with ⟨_ | y⟩ <;> try cases h
  rcases head_merge x y h with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

/-- The projecting daughter, `some true` for the left and `some false` for the right. -/
def side : S.State → S.State → Option Bool
  | ⟨some x⟩, ⟨some y⟩ =>
    if x.Projects y then some true else if y.Projects x then some false else none
  | _, _ => none

theorem side_of_of (a b : α) (r u : R) :
    side (of a r : S.State) (of b u) =
      if (⟨a, r⟩ : S.Constituent).Projects ⟨b, u⟩ then some true
      else if (⟨b, u⟩ : S.Constituent).Projects ⟨a, r⟩ then some false else none :=
  rfl

/-- Swapping the sisters swaps the side that projects. -/
theorem side_comm (x y : S.State) : side x y = (side y x).map Bool.not := by
  rcases x with ⟨_ | x⟩ <;> rcases y with ⟨_ | y⟩ <;> try rfl
  show (if x.Projects y then some true else if y.Projects x then some false else none) =
    (if y.Projects x then some true else if x.Projects y then some false else none).map Bool.not
  by_cases h : x.Projects y
  · simp [h, h.asymm]
  · by_cases h' : y.Projects x <;> simp [h, h']

/-- `x` projects over `y`: both are constituents, and the constituent of `x` projects over that of
`y`. -/
def Projects (x y : S.State) : Prop := side x y = some true

instance : DecidableRel (Projects (S := S)) := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

/-- Of two states at most one projects. -/
theorem Projects.asymm {x y : S.State} (h : x.Projects y) : ¬ y.Projects x := fun h' ↦ by
  rw [Projects, side_comm, h] at h'
  cases h'

instance : Std.Asymm (Projects (S := S)) := ⟨fun _ _ ↦ Projects.asymm⟩

/-- The head of a product is the head of the factor that projects. -/
theorem head_mul_eq (x y : S.State) :
    (x * y).head = if x.Projects y then x.head else if y.Projects x then y.head else none := by
  rcases x with ⟨_ | x⟩ <;> rcases y with ⟨_ | y⟩ <;> try rfl
  show (merge x y).head = if side ⟨some x⟩ ⟨some y⟩ = some true then _ else
    if side ⟨some y⟩ ⟨some x⟩ = some true then _ else none
  unfold merge side
  by_cases h : x.Projects y
  · simp [h, head]
  · by_cases h' : y.Projects x
    · simp [h, h', head]
    · simp [h, h', head]
      rfl

/-- A product fails exactly when neither factor projects. -/
theorem mul_eq_zero_iff (x y : S.State) : x * y = 0 ↔ ¬ x.Projects y ∧ ¬ y.Projects x := by
  rcases x with ⟨_ | x⟩ <;> rcases y with ⟨_ | y⟩ <;>
    try exact iff_of_true rfl ⟨by simp [Projects, side], by simp [Projects, side]⟩
  show merge x y = 0 ↔ ¬ side ⟨some x⟩ ⟨some y⟩ = some true ∧ ¬ side ⟨some y⟩ ⟨some x⟩ = some true
  unfold merge side
  by_cases h : x.Projects y
  · simp [h, h.asymm]
    exact fun h0 ↦ by cases h0
  · by_cases h' : y.Projects x
    · simp [h, h']
      exact fun h0 ↦ by cases h0
    · simp [h, h']

/-- A relabelling of heads that selection does not see commutes with the product. -/
theorem map_mul {f : α → α}
    (hsel : ∀ (r : R) b u, S.Selects r (f b) u ↔ S.Selects r b u)
    (hrest : ∀ (r : R) b u, S.rest r (f b) u = S.rest r b u)
    (hout : ∀ a b, S.Outranks (f a) (f b) ↔ S.Outranks a b)
    (x y : S.State) : (x * y).map f = x.map f * y.map f := by
  rcases x with ⟨_ | x⟩ <;> rcases y with ⟨_ | y⟩ <;> try rfl
  have hp : ∀ a b : S.Constituent, (a.map f).Projects (b.map f) ↔ a.Projects b := fun a b ↦ by
    simp [Constituent.Projects, Constituent.map, hsel, hout]
  show (merge x y).map f = merge (x.map f) (y.map f)
  unfold merge
  simp only [hp]
  split_ifs
  · simp [map, Constituent.map, Constituent.select, hrest]
  · simp [map, Constituent.map, Constituent.select, hrest]
  · rfl

/-! ### Spines -/

private theorem foldl_mul_zero {α : Type*} (f : α → S.State) (l : List α) :
    l.foldl (fun x a ↦ x * f a) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, zero_mul, ih]

/-- Along a spine, the product is iterated selection: when no sister selects the head `h`,
merging them in turn leaves `h` projecting with the residue of selecting each, and fails where
`h` does not select one. -/
theorem foldl_mul_of (h : α) (r : R)
    (args : List (α × R))
    (hargs : ∀ a ∈ args, ∀ r', ¬ S.Selects a.2 h r') :
    args.foldl (fun x a ↦ x * of a.1 a.2) (of h r : S.State) =
      (args.foldlM (fun r a ↦ S.select r a.1 a.2) r).elim 0 (of h) := by
  induction args generalizing r with
  | nil => rfl
  | cons a args ih =>
    obtain ⟨b, u⟩ := a
    have hu := hargs (b, u) List.mem_cons_self r
    have key : (of h r : S.State) * of b u = (S.select r b u).elim 0 (of h) := by
      rw [of_mul_of]
      by_cases hs : S.Selects r b u
      · rw [merge_of_projects ⟨hs, fun h' ↦ (hu h').elim⟩, select_eq_some_iff.2 ⟨hs, rfl⟩]; rfl
      · rw [merge_eq_zero (fun hp ↦ hs hp.1) (fun hp ↦ hu hp.1), select_eq_none_iff.2 hs]; rfl
    rw [List.foldl_cons, List.foldlM_cons, key]
    cases hsel : S.select r b u with
    | none => exact foldl_mul_zero _ _
    | some r' => exact ih r' fun a ha ↦ hargs a (List.mem_cons_of_mem _ ha)

end State

end SelectionRule

end Minimalist
