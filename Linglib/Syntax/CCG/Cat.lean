module

public import Linglib.Core.Computability.Edge
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# CCG categories

The categories of combinatory categorial grammar are built from atoms by a rightward and a
leftward slash, each slash carrying one of Baldridge's modalities. Every category is uniquely an
atom, its *target*, followed by a sequence of *arguments*, slash–category pairs; Kuhlmann, Koller
and Satta write it `A|ₘXₘ ⋯ |₁X₁`, and the composition rules of every CCG formalism have the
form `X/Y Yβ ⇒ Xβ` over an argument sequence `β`. Categories are stated over an arbitrary type
`α` of atoms, so a grammar with featured atoms instantiates its own inventory.

## Main definitions

* `CCG.Modality`: the slash modalities, a bounded order with `dot = ⊥`, `star = ⊤`, and
  `diamond` and `cross` incomparable.
* `CCG.Cat`: categories over a type `α` of atoms.
* `CCG.Cat.Arg`, `CCG.Cat.pushArgs`: an argument, and the category `xβ`.
* `CCG.Cat.target`, `CCG.Cat.args`: the target and the arguments of a category.
* `CCG.Cat.equivTargetArgs`: a category is its target together with its arguments.
* `CCG.Cat.count`: the count of an atom.

## Main statements

* `CCG.Cat.atom_pushArgs_eq_iff`: a category is `aβ` exactly when `a` is its target and `β` its
  arguments.

## Notation

* `X / Y`, `X \ Y`: slashes with the unrestricted modality `dot`, written unannotated as in
  Steedman's presentation.
* `X /⋄ Y`, `X \⋄ Y`, `X /× Y`, `X \× Y`, `X /⋆ Y`, `X \⋆ Y`: slashes with the annotated
  modality.

All are scoped to the `CCG` namespace. Because `/` overloads division, categories are written
fully parenthesized (`(S \ NP) / NP`).

## References

* [steedman-2000]
* [steedman-2019]
* [baldridge-2002]
* [kuhlmann-koller-satta-2015]
* [van-benthem-1986]
-/

@[expose] public section

namespace CCG

/-! ### Slash modalities -/

/-- The modality a slash carries, determining which rule classes it licenses. The order is
reverse inclusion of licenses, `s ≤ m` iff `s` licenses every rule class `m` does, so composition
gates on `s ≤ diamond` (harmonic) and `s ≤ cross` (crossing), while application is licensed by
every modality (`s ≤ ⊤`). -/
inductive Modality where
  /-- The unrestricted modality, written as an unannotated slash, combining by any rule. -/
  | dot
  /-- The order-preserving `⋄`, licensing application and harmonic composition. -/
  | diamond
  /-- The permuting `×`, licensing application and crossing composition. -/
  | cross
  /-- The modality `⋆`, licensing application only. -/
  | star
  deriving DecidableEq, Repr, Fintype

namespace Modality

instance : LE Modality where
  le a b := a = dot ∨ a = b ∨ b = star

instance : DecidableLE Modality := fun a b ↦
  inferInstanceAs (Decidable (a = dot ∨ a = b ∨ b = star))

instance : PartialOrder Modality where
  le_refl _ := Or.inr (Or.inl rfl)
  le_trans := by decide
  le_antisymm := by decide

instance : BoundedOrder Modality where
  top := star
  le_top _ := Or.inr (Or.inr rfl)
  bot := dot
  bot_le _ := Or.inl rfl

@[simp] theorem dot_le (m : Modality) : dot ≤ m := Or.inl rfl

end Modality

/-! ### Categories -/

/-- CCG categories over a type `α` of atomic categories, built from atoms by directional
slashes that each carry a `Modality`. -/
inductive Cat (α : Type*) where
  /-- An atomic category. -/
  | atom : α → Cat α
  /-- `X/ₘY` looks right for a `Y` to give an `X`, at modality `m`. -/
  | rslash : Cat α → Modality → Cat α → Cat α
  /-- `X\ₘY` looks left for a `Y` to give an `X`, at modality `m`. -/
  | lslash : Cat α → Modality → Cat α → Cat α
  deriving Repr, DecidableEq

scoped notation:60 X "/" Y => Cat.rslash X Modality.dot Y
scoped notation:60 X "\\" Y => Cat.lslash X Modality.dot Y
scoped notation:60 X "/⋄" Y => Cat.rslash X Modality.diamond Y
scoped notation:60 X "\\⋄" Y => Cat.lslash X Modality.diamond Y
scoped notation:60 X "/×" Y => Cat.rslash X Modality.cross Y
scoped notation:60 X "\\×" Y => Cat.lslash X Modality.cross Y
scoped notation:60 X "/⋆" Y => Cat.rslash X Modality.star Y
scoped notation:60 X "\\⋆" Y => Cat.lslash X Modality.star Y

namespace Cat

variable {α : Type*}

/-! ### Targets and arguments -/

/-- An argument of a category, a slash–category pair. -/
structure Arg (α : Type*) where
  /-- The side the slash looks to, `right` for `/` and `left` for `\`. -/
  side : Edge
  /-- The modality of the slash. -/
  modality : Modality
  /-- The argument category. -/
  cat : Cat α
  deriving Repr, DecidableEq

/-- `x.push a` is `x` with `a` as its new outermost argument. -/
def push (x : Cat α) : Arg α → Cat α
  | ⟨.right, m, y⟩ => .rslash x m y
  | ⟨.left, m, y⟩ => .lslash x m y

@[simp] theorem push_right (x y : Cat α) (m : Modality) :
    x.push ⟨.right, m, y⟩ = .rslash x m y := rfl

@[simp] theorem push_left (x y : Cat α) (m : Modality) :
    x.push ⟨.left, m, y⟩ = .lslash x m y := rfl

/-- `x.pushArgs β` is the category `xβ`, which adds the arguments `β` to `x` innermost first, so
that `x.pushArgs [a₁, a₂]` has `a₂` as its outermost argument. -/
def pushArgs (x : Cat α) (β : List (Arg α)) : Cat α := β.foldl push x

@[simp] theorem pushArgs_nil (x : Cat α) : x.pushArgs [] = x := rfl

@[simp] theorem pushArgs_cons (x : Cat α) (a : Arg α) (β : List (Arg α)) :
    x.pushArgs (a :: β) = (x.push a).pushArgs β := rfl

@[simp] theorem pushArgs_append (x : Cat α) (β γ : List (Arg α)) :
    x.pushArgs (β ++ γ) = (x.pushArgs β).pushArgs γ := List.foldl_append

/-- The target of a category, its leftmost atom after stripping all arguments, which plays the
role of a function's return type. -/
def target : Cat α → α
  | .atom a => a
  | .rslash x _ _ => target x
  | .lslash x _ _ => target x

@[simp] theorem target_atom (a : α) : target (atom a) = a := rfl

@[simp] theorem target_rslash (x y : Cat α) (m : Modality) :
    target (rslash x m y) = target x := rfl

@[simp] theorem target_lslash (x y : Cat α) (m : Modality) :
    target (lslash x m y) = target x := rfl

@[simp] theorem target_push (x : Cat α) (a : Arg α) : (x.push a).target = x.target := by
  obtain ⟨_ | _, _, _⟩ := a <;> rfl

@[simp] theorem target_pushArgs (x : Cat α) (β : List (Arg α)) :
    (x.pushArgs β).target = x.target := by
  induction β generalizing x <;> simp [*]

/-- The arguments of a category, innermost first. -/
def args : Cat α → List (Arg α)
  | .atom _ => []
  | .rslash x m y => x.args ++ [⟨.right, m, y⟩]
  | .lslash x m y => x.args ++ [⟨.left, m, y⟩]

@[simp] theorem args_atom (a : α) : args (atom a) = [] := rfl

@[simp] theorem args_rslash (x y : Cat α) (m : Modality) :
    args (rslash x m y) = x.args ++ [⟨.right, m, y⟩] := rfl

@[simp] theorem args_lslash (x y : Cat α) (m : Modality) :
    args (lslash x m y) = x.args ++ [⟨.left, m, y⟩] := rfl

@[simp] theorem args_push (x : Cat α) (a : Arg α) : (x.push a).args = x.args ++ [a] := by
  obtain ⟨_ | _, _, _⟩ := a <;> rfl

@[simp] theorem args_pushArgs (x : Cat α) (β : List (Arg α)) :
    (x.pushArgs β).args = x.args ++ β := by
  induction β generalizing x <;> simp [*]

@[simp] theorem atom_target_pushArgs_args (c : Cat α) : (atom c.target).pushArgs c.args = c := by
  induction c with
  | atom => rfl
  | rslash x m y ih => simp [ih]
  | lslash x m y ih => simp [ih]

/-- Every category is uniquely its target followed by its arguments. -/
def equivTargetArgs : Cat α ≃ α × List (Arg α) where
  toFun c := (c.target, c.args)
  invFun p := (atom p.1).pushArgs p.2
  left_inv := atom_target_pushArgs_args
  right_inv p := by simp

theorem atom_pushArgs_eq_iff {a : α} {β : List (Arg α)} {c : Cat α} :
    (atom a).pushArgs β = c ↔ a = c.target ∧ β = c.args :=
  (equivTargetArgs.symm_apply_eq (x := (a, β))).trans Prod.ext_iff

/-! ### Type-raising

Type-raising is morpholexical in [steedman-2019], the work of case morphemes rather than a
syntactic rule, so these build the categories that raised lexical entries carry. -/

/-- `forwardTypeRaise x t` is `t / (t \ x)`, the forward-raised (`>T`) category of `x` at
target `t`. -/
def forwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t / (t \ x)

/-- `backwardTypeRaise x t` is `t \ (t / x)`, the backward-raised (`<T`) category of `x` at
target `t`. -/
def backwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t \ (t / x)

variable [DecidableEq α]

/-! ### The count invariant -/

/-- The count of the atom `a` in a category ([van-benthem-1986]) adds `1` for each occurrence in
result position and subtracts `1` for each occurrence in argument position, so that every
combinatory rule preserves it (`CCG.Rule.count_eq`). -/
def count (a : α) : Cat α → ℤ
  | .atom b => if b = a then 1 else 0
  | .rslash x _ y => count a x - count a y
  | .lslash x _ y => count a x - count a y

@[simp] theorem count_atom (a b : α) : count a (atom b) = if b = a then 1 else 0 := rfl

@[simp] theorem count_rslash (a : α) (x y : Cat α) (m : Modality) :
    count a (rslash x m y) = count a x - count a y := rfl

@[simp] theorem count_lslash (a : α) (x y : Cat α) (m : Modality) :
    count a (lslash x m y) = count a x - count a y := rfl

@[simp] theorem count_push (a : α) (x : Cat α) (b : Arg α) :
    (x.push b).count a = x.count a - b.cat.count a := by
  obtain ⟨_ | _, _, _⟩ := b <;> rfl

theorem count_pushArgs (a : α) (x : Cat α) (β : List (Arg α)) :
    (x.pushArgs β).count a = x.count a - (β.map (·.cat.count a)).sum := by
  induction β generalizing x with
  | nil => simp
  | cons b β ih =>
    simp only [pushArgs_cons, ih, count_push, List.map_cons, List.sum_cons]
    omega

end Cat

end CCG
