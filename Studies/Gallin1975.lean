module

public import Linglib.Semantics.Composition.Term

/-!
# Gallin (1975): Intensional and Higher-Order Modal Logic

Montague's intensional logic IL has variables and constants of every type, application,
abstraction and identity, and two operators on indices: `^A`, the intension of `A`, a function
from indices, and `ˇA`, the value at the current index of an intension. A term has a value at an
index under an assignment, a constant denoting at each index what its meaning gives it there.
Gallin translates IL into the two-sorted type theory Ty₂, where indices are the values of
variables of type $s$: a constant becomes a constant of type $⟨s,α⟩$ applied to a distinguished
index variable, `^A` the abstraction of the translate of `A` over that variable, and `ˇA` the
application of the translate of `A` to it. [The translation preserves the
semantics](##eval_toTy2): the value of a term at an index is the value of its translate with the
index variable sent to that index, so [a formula is valid in IL exactly when its translate is valid
in Ty₂](##valid_iff_valid_toTy2).

## Implementation notes

The types of IL are the composition engine's types, the intension type $⟨s,α⟩$ being
`Ty.intens α`, and the terms of Ty₂ are the engine's terms under its total interpretation, with
application the mode of functional application and identity a constant interpreted as equality.
Variables are typed by a typing of their indices, as the engine's are. The index variable is the
variable `0` of the translate, and the variables of the term being translated are shifted up by
one, so the translation is defined on every term and captures no variable.

## References

* [gallin-1975]
-/

@[expose] public section

namespace Gallin1975

open Montague (Ty Sorts Mode)
open scoped Montague

universe u

/-- The terms of IL over the constants `K`, under a typing `Γ` of the variable indices: variables,
constants, application, abstraction, identity, the intension `^A` of a term and the value `ˇA` at
the current index of an intension (p. 11). -/
inductive IL.Term (Γ : ℕ → Ty) (K : Ty → Type u) : Ty → Type u
  | var (n : ℕ) : IL.Term Γ K (Γ n)
  | const {α : Ty} (c : K α) : IL.Term Γ K α
  | app {α β : Ty} (f : IL.Term Γ K (α ⇒ β)) (a : IL.Term Γ K α) : IL.Term Γ K β
  | lam {β : Ty} (n : ℕ) (b : IL.Term Γ K β) : IL.Term Γ K (Γ n ⇒ β)
  | ident {α : Ty} (a b : IL.Term Γ K α) : IL.Term Γ K .t
  | up {α : Ty} (a : IL.Term Γ K α) : IL.Term Γ K (.intens α)
  | down {α : Ty} (a : IL.Term Γ K (.intens α)) : IL.Term Γ K α

variable {K : Ty → Type u} {E W : Type} {S : Sorts} {Γ : ℕ → Ty}

open scoped Assignment

/-- The value of a term at the index `i` under the assignment `g`, given the meaning `m` of the
constants, a function from indices (p. 13): a constant denotes its meaning at `i`, identity is
equality, `^A` denotes the function from each index to the value of `A` there, and `ˇA` the value
of `A` at `i` applied to `i`. -/
noncomputable def IL.Term.value (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α S) :
    (∀ n, Ty.Domain E W (Γ n) S) → W → {α : Ty} → IL.Term Γ K α → Ty.Domain E W α S
  | g, _, _, .var n => g n
  | _, i, _, .const c => m c i
  | g, i, _, .app f a => f.value m g i (a.value m g i)
  | g, i, _, .lam n b => fun x ↦ b.value m (g[n ↦ x]) i
  | g, i, _, .ident a b => a.value m g i = b.value m g i
  | g, _, _, .up a => fun j ↦ a.value m g j
  | g, i, _, .down a => a.value m g i i

-- p. 14: `ˇ^A` always has the value of `A`
theorem value_down_up (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α S)
    (g : ∀ n, Ty.Domain E W (Γ n) S) (i : W) {α : Ty} (A : IL.Term Γ K α) :
    (IL.Term.down (.up A)).value m g i = A.value m g i :=
  rfl

/-- The constant of the model for `^ˇA`: an individual concept. -/
inductive Concept : Ty → Type
  | c : Concept (.intens .e)

-- p. 14: `^ˇA` need not have the value of `A`, here for a concept whose meaning at each index is
-- the concept constant at that index
theorem value_up_down_ne :
    (IL.Term.up (.down (.const Concept.c)) : IL.Term (fun _ ↦ .e) Concept _).value
        (E := Bool) (S := {}) (fun | .c => fun i _ ↦ i) (fun _ ↦ false) true ≠
      (IL.Term.const Concept.c : IL.Term (fun _ ↦ .e) Concept _).value (fun | .c => fun i _ ↦ i)
        (fun _ ↦ false) true := by
  intro h
  simpa [IL.Term.value] using congrFun h false

/-- The constants of Ty₂ the translation introduces: for each constant of IL of type `α`, a
constant of type `⟨s,α⟩` naming its intension, and identity at each type. -/
inductive Constant (K : Ty → Type u) : Ty → Type u
  | intension {α : Ty} (c : K α) : Constant K (.intens α)
  | identity (α : Ty) : Constant K (α ⇒ α ⇒ .t)

/-- The interpretation of the constants of Ty₂: a constant's intension is the meaning `m` gives the
constant of IL, and identity is equality. -/
def Constant.interp (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α S) :
    ∀ {α : Ty}, Constant K α → Ty.Domain E W α S
  | _, .intension c => m c
  | _, .identity _ => fun x y ↦ x = y

/-- The typing of the translate's indices: the index variable `0` has type `s`, and the index
`n + 1` the type `Γ` gives `n`. -/
def typing (Γ : ℕ → Ty) : ℕ → Ty
  | 0 => .s
  | n + 1 => Γ n

/-- The translate of a term of IL into Ty₂ (p. 61): a variable keeps its shape with its index
shifted, a constant is its intension applied to the index variable, application, abstraction and
identity keep their shape, `^A` is the abstraction of the translate of `A` over the index variable,
and `ˇA` its application to that variable. -/
def IL.Term.toTy2 : {α : Ty} → IL.Term Γ K α → Montague.Term (typing Γ) (Constant K) α
  | _, .var n => .var (n + 1)
  | _, .const c => .comp .functionalLeft (.const (.intension c)) (.var 0)
  | _, .app f a => .comp .functionalLeft f.toTy2 a.toTy2
  | _, .lam n b => .lam (n + 1) b.toTy2
  | _, .ident a b =>
    .comp .functionalLeft (.comp .functionalLeft (.const (.identity _)) a.toTy2) b.toTy2
  | _, .up a => .lam 0 a.toTy2
  | _, .down a => .comp .functionalLeft a.toTy2 (.var 0)

-- p. 61, clauses (ii), (iii) and (vi): `A(^B)` goes to `A*(λxₛ B*)`
example (f : K (.intens .t ⇒ .t)) (p : K .t) :
    (IL.Term.app (.const f) (.up (.const p)) : IL.Term Γ K .t).toTy2 =
      .comp .functionalLeft (.comp .functionalLeft (.const (.intension f)) (.var 0))
        (.lam 0 (.comp .functionalLeft (.const (.intension p)) (.var 0))) :=
  rfl

/-- Gallin's Lemma 8.2.1, that the translation preserves the semantics: under any assignment `g`
of the translate's variables, the translate denotes the value of the term at the index `g 0` under
the assignment `g` makes to the shifted variables. -/
theorem eval_toTy2 (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α S)
    (g : ∀ n, Ty.Domain E W (typing Γ n) S) {α : Ty} (A : IL.Term Γ K α) :
    A.toTy2.eval (Constant.interp m) g = A.value m (fun n ↦ g (n + 1)) (g 0) := by
  induction A generalizing g with
  | var n => rfl
  | const c => rfl
  | app f a ihf iha => simp only [IL.Term.toTy2, Montague.Term.eval_comp, Mode.eval, ihf, iha]; rfl
  | lam n b ih =>
    funext x
    refine (ih (g[n + 1 ↦ x])).trans ?_
    rw [Function.update_comp_eq_of_injective' g Nat.succ_injective n x,
      Function.update_of_ne (Nat.succ_ne_zero n).symm]
    rfl
  | ident a b iha ihb =>
    simp only [IL.Term.toTy2, Montague.Term.eval_comp, Montague.Term.eval_const, Mode.eval, iha,
      ihb]
    rfl
  | up a ih =>
    funext j
    refine (ih (g[0 ↦ j])).trans ?_
    rw [Function.update_comp_eq_of_forall_ne' g _ Nat.succ_ne_zero, Function.update_self]
    rfl
  | down a ih => simp only [IL.Term.toTy2, Montague.Term.eval_comp, Mode.eval, ih]; rfl

/-- Gallin's Theorem 8.2 (i): a formula is valid in IL, true in every model at every index under
every assignment, exactly when its translate is valid in Ty₂. -/
theorem valid_iff_valid_toTy2 (A : IL.Term Γ K .t) :
    (∀ (E W : Type) [Nonempty E] [Nonempty W] (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α S)
      (g : ∀ n, Ty.Domain E W (Γ n) S) (i : W), A.value m g i) ↔
    ∀ (E W : Type) [Nonempty E] [Nonempty W] (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α S)
      (g : ∀ n, Ty.Domain E W (typing Γ n) S), A.toTy2.eval (Constant.interp m) g := by
  refine ⟨fun h E W _ _ m g ↦ ?_, fun h E W _ _ m g i ↦ ?_⟩
  · rw [eval_toTy2]
    exact h E W m _ _
  · have := h E W m fun | 0 => i | n + 1 => g n
    rwa [eval_toTy2] at this

end Gallin1975
