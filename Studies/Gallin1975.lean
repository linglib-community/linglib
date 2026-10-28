module

public import Linglib.Semantics.Composition.Term

/-!
# Gallin (1975): Intensional and Higher-Order Modal Logic

Montague's intensional logic evaluates an expression at an index, and its operator `^` hands an
operator the intension of its argument. Gallin translates it into the two-sorted type theory Ty₂,
where indices are the values of variables of type $s$: a constant becomes a constant of type
$⟨s,α⟩$ applied to a distinguished index variable, and `^A` becomes the abstraction of the
translate of `A` over that variable. [The translation preserves the semantics](##eval_toTy2): the
value of an expression at an index is the value of its translate with the index variable sent to
that index.

## Implementation notes

The source language is the composition engine's terms under their intensional evaluation, whose
intensional functional application is application to the `^` of the argument; `ˇ` and identity,
which the engine lacks, are not translated. The index variable is the variable `0` of the
translate, and the variables of the term being translated are shifted up by one, so the translation
is defined on every term, whatever the typing of its indices, and captures no variable.

## References

* [gallin-1975]
-/

@[expose] public section

namespace Gallin1975

open Montague

universe u

/-- The constants the translation introduces: a constant of type `ty` becomes a constant of type
`s ⇒ ty`, naming its intension. -/
inductive IntensionConst (K : Ty → Type u) : Ty → Type u
  | mk {ty : Ty} (c : K ty) : IntensionConst K (.s ⇒ ty)

variable {K : Ty → Type u} {E W : Type} {S : Sorts}

/-- The interpretation of the introduced constants, each the intension `I` gives the constant it
comes from. -/
def IntensionConst.interp (I : ∀ {ty : Ty}, K ty → W → Ty.Domain E W ty S) :
    ∀ {ty : Ty}, IntensionConst K ty → Ty.Domain E W ty S
  | _, .mk c => I c

/-- The typing of the translate's indices: the index variable `0` has type `s`, and the index
`n + 1` the type `Γ` gives `n`. -/
def typing (Γ : ℕ → Ty) : ℕ → Ty
  | 0 => .s
  | n + 1 => Γ n

variable {Γ : ℕ → Ty}

/-- The translate of a composition: intensional functional application becomes functional
application to the argument abstracted over the index variable, and every other mode is kept. -/
def translateMode {K' : Ty → Type u} {σ₁ σ₂ τ : Ty} :
    Mode σ₁ σ₂ τ → Term (typing Γ) K' σ₁ → Term (typing Γ) K' σ₂ → Term (typing Γ) K' τ
  | .intensionalLeft, l, r => .comp .functionalLeft l (.lam 0 r)
  | .intensionalRight, l, r => .comp .functionalRight (.lam 0 l) r
  | m, l, r => .comp m l r

/-- The translate of a term into Ty₂: a constant is applied to the index variable, a variable and
an abstraction keep their shape with their indices shifted, and intensional application abstracts
its argument over the index variable. -/
def toTy2 : {ty : Ty} → Term Γ K ty → Term (typing Γ) (IntensionConst K) ty
  | _, .const c => .comp .functionalLeft (.const (.mk c)) (.var 0)
  | _, .var n => .var (n + 1)
  | _, .lam n b => .lam (n + 1) (toTy2 b)
  | _, .comp m l r => translateMode m (toTy2 l) (toTy2 r)

-- p. 61, clauses (ii), (iii) and (vi): `A(^B)` goes to `A*(λxₛ B*)`
example (f : K (.intens .t ⇒ .t)) (p : K .t) :
    toTy2 (Γ := Γ) (.comp .intensionalLeft (.const f) (.const p)) =
      .comp .functionalLeft (.comp .functionalLeft (.const (.mk f)) (.var 0))
        (.lam 0 (.comp .functionalLeft (.const (.mk p)) (.var 0))) :=
  rfl

open scoped Assignment

/-- Gallin's Lemma 8.2.1, that the translation preserves the semantics: under any assignment `g`
of the translate's variables, the translate denotes the value of the term at the index `g 0`
under the assignment `g` makes to the shifted variables. -/
theorem eval_toTy2 (I : ∀ {ty : Ty}, K ty → W → Ty.Domain E W ty S)
    (g : ∀ n, Ty.Domain E W (typing Γ n) S) {ty : Ty} (t : Term Γ K ty) :
    (toTy2 t).eval (IntensionConst.interp I) g = t.intension I (fun n ↦ g (n + 1)) (g 0) := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih =>
    funext x
    refine (ih (g[n + 1 ↦ x])).trans ?_
    rw [Function.update_comp_eq_of_injective' g Nat.succ_injective n x,
      Function.update_of_ne (Nat.succ_ne_zero n).symm]
    rfl
  | comp m l r ihl ihr =>
    cases m <;> simp only [toTy2, translateMode, Term.eval_comp, Term.eval_lam,
      Term.intension_comp, Mode.eval, Mode.intension, ihl, ihr, Function.update_self,
      Function.update_comp_eq_of_forall_ne' g _ Nat.succ_ne_zero] <;> rfl

end Gallin1975
