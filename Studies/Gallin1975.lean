module

public import Linglib.Semantics.Composition.Interpreter.Effect
public import Linglib.Logic.Assignment
public import Mathlib.Data.Finset.Basic

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

λ-conversion holds in Ty₂ wherever the argument is free for the variable, and in IL only where in
addition the variable is free in no scope of `^` or the argument is modally closed. Since `^`
translates to an abstraction over the index variable, and [a term is modally closed exactly when its
translate does not read that variable](##modallyClosed_iff),
[IL's law is Ty₂'s, pulled back along the translation](##value_app_lam).

## Implementation notes

The types of IL and of Ty₂ are the types over two basic types, individuals and indices, the
intension type $⟨s,α⟩$ being `intens α`; a term of IL may here have any type of Ty₂, where the
book's have `s` only as the argument of an intension. The models are the standard ones.
Variables are typed by a typing of their indices. The index variable is the variable `0` of the
translate, and the variables of the term being translated are shifted up by one, so the
translation is defined on every term and captures no variable.

## References

* [gallin-1975]
-/

@[expose] public section

namespace Gallin1975

open Interpreter

universe u

/-- The basic types: individuals and indices. -/
inductive Atom
  | e | s
  deriving DecidableEq

/-- The domains of the basic types. -/
abbrev Dom (E W : Type) : Atom → Type
  | .e => E
  | .s => W

/-- The types of Ty₂ (p. 58): individuals, truth values, indices and functions. -/
abbrev Ty := Interpreter.Ty Atom

/-- The type of individuals. -/
abbrev e : Ty := .base .e

/-- The type of indices. -/
abbrev s : Ty := .base .s

/-- The type $⟨s,α⟩$ of the intensions of `α`. -/
abbrev intens (α : Ty) : Ty := s ⇒ α

/-- The domain of a type in the standard frame over individuals `E` and indices `W` (p. 59). -/
abbrev Ty.Domain (E W : Type) (α : Ty) : Type := Interpreter.Ty.Dom (Dom E W) α

/-! ### Ty₂ -/

/-- The terms of Ty₂ over the constants `K`, under a typing `Γ` of the variable indices:
constants and variables, application, abstraction and identity (p. 59). -/
inductive Ty2.Term (Γ : ℕ → Ty) (K : Ty → Type u) : Ty → Type u
  | const {α : Ty} (c : K α) : Ty2.Term Γ K α
  | var (n : ℕ) : Ty2.Term Γ K (Γ n)
  | lam {β : Ty} (n : ℕ) (b : Ty2.Term Γ K β) : Ty2.Term Γ K (Γ n ⇒ β)
  | app {α β : Ty} (f : Ty2.Term Γ K (α ⇒ β)) (a : Ty2.Term Γ K α) : Ty2.Term Γ K β
  | ident {α : Ty} (a b : Ty2.Term Γ K α) : Ty2.Term Γ K .t

namespace Ty2.Term

variable {Γ : ℕ → Ty} {K : Ty → Type u} {E W : Type}

/-- The value of a term in a standard model, under an interpretation of the constants and an
assignment (pp. 59-60). -/
noncomputable def eval (I : ∀ {α : Ty}, K α → Ty.Domain E W α) :
    {α : Ty} → Ty2.Term Γ K α → (∀ n, Ty.Domain E W (Γ n)) → Ty.Domain E W α
  | _, .const c, _ => I c
  | _, .var n, g => g n
  | _, .lam n b, g => fun x ↦ b.eval I (Function.update g n x)
  | _, .app f a, g => f.eval I g (a.eval I g)
  | _, .ident a b, g => a.eval I g = b.eval I g

/-- The variables free in a term. -/
def freeVars : {α : Ty} → Ty2.Term Γ K α → Finset ℕ
  | _, .const _ => ∅
  | _, .var n => {n}
  | _, .lam n b => b.freeVars.erase n
  | _, .app f a => f.freeVars ∪ a.freeVars
  | _, .ident a b => a.freeVars ∪ b.freeVars

/-- The term with each free variable `n` replaced by `σ n`. -/
def subst : {α : Ty} → Ty2.Term Γ K α → (∀ n, Ty2.Term Γ K (Γ n)) → Ty2.Term Γ K α
  | _, .const c, _ => .const c
  | _, .var n, σ => σ n
  | _, .lam n b, σ => .lam n (b.subst (Function.update σ n (.var n)))
  | _, .app f a, σ => .app (f.subst σ) (a.subst σ)
  | _, .ident a b, σ => .ident (a.subst σ) (b.subst σ)

/-- The replacements `σ` are free for a term when no binder in it captures a free variable of the
replacement for a variable free below it. -/
def FreeFor : {α : Ty} → Ty2.Term Γ K α → (∀ n, Ty2.Term Γ K (Γ n)) → Prop
  | _, .const _, _ | _, .var _, _ => True
  | _, .lam n b, σ => (∀ m ∈ b.freeVars, m ≠ n → n ∉ (σ m).freeVars) ∧
      b.FreeFor (Function.update σ n (.var n))
  | _, .app f a, σ => f.FreeFor σ ∧ a.FreeFor σ
  | _, .ident a b, σ => a.FreeFor σ ∧ b.FreeFor σ

theorem freeFor_var {α : Ty} (t : Ty2.Term Γ K α) : t.FreeFor fun n ↦ .var n := by
  induction t with
  | const c => trivial
  | var n => trivial
  | lam n b ih =>
    refine ⟨fun m _ hmn h ↦ hmn (Finset.mem_singleton.1 h).symm, ?_⟩
    rwa [Function.update_eq_self_iff.2 rfl]
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | ident a b iha ihb => exact ⟨iha, ihb⟩

variable (I : ∀ {α : Ty}, K α → Ty.Domain E W α)

-- a term's value depends on the assignment only at its free variables
theorem eval_congr_of_agree {α : Ty} (t : Ty2.Term Γ K α) {g g' : ∀ n, Ty.Domain E W (Γ n)}
    (hg : ∀ n ∈ t.freeVars, g n = g' n) : t.eval I g = t.eval I g' := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => exact hg n (Finset.mem_singleton_self n)
  | lam n b ih =>
    refine funext fun x ↦ ih fun m hm ↦ ?_
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [Function.update_of_ne hmn, hg m (Finset.mem_erase.2 ⟨hmn, hm⟩)]
  | app f a ihf iha =>
    simp only [freeVars, Finset.mem_union] at hg
    simp only [eval, ihf fun n hn ↦ hg n (.inl hn), iha fun n hn ↦ hg n (.inr hn)]
  | ident a b iha ihb =>
    simp only [freeVars, Finset.mem_union] at hg
    simp only [eval, iha fun n hn ↦ hg n (.inl hn), ihb fun n hn ↦ hg n (.inr hn)]

-- the substitution lemma: where no binder captures, a substituted term has the value of the
-- original at the values of the replacements
theorem eval_subst {α : Ty} {t : Ty2.Term Γ K α} {σ : ∀ n, Ty2.Term Γ K (Γ n)}
    (ht : t.FreeFor σ) (g : ∀ n, Ty.Domain E W (Γ n)) :
    (t.subst σ).eval I g = t.eval I fun n ↦ (σ n).eval I g := by
  suffices h : ∀ {v : ∀ n, Ty.Domain E W (Γ n)}, (∀ n ∈ t.freeVars, (σ n).eval I g = v n) →
      (t.subst σ).eval I g = t.eval I v from h fun _ _ ↦ rfl
  induction t generalizing σ g with
  | const c => exact fun _ ↦ rfl
  | var n => exact fun hv ↦ hv n (Finset.mem_singleton_self n)
  | lam n b ih =>
    refine fun hv ↦ funext fun x ↦ ih ht.2 _ fun m hm ↦ ?_
    obtain rfl | hmn := eq_or_ne m n
    · simp [eval]
    · rw [Function.update_of_ne hmn, Function.update_of_ne hmn,
        eval_congr_of_agree I (σ m) (g' := g) fun k hk ↦ Function.update_of_ne
          (fun hkn : k = n ↦ ht.1 m hm hmn (hkn ▸ hk)) x g]
      exact hv m (Finset.mem_erase.2 ⟨hmn, hm⟩)
  | app f a ihf iha =>
    intro _ hv
    simp only [subst, eval, ihf ht.1 g fun n hn ↦ hv n (Finset.mem_union_left _ hn),
      iha ht.2 g fun n hn ↦ hv n (Finset.mem_union_right _ hn)]
  | ident a b iha ihb =>
    intro _ hv
    simp only [subst, eval, iha ht.1 g fun n hn ↦ hv n (Finset.mem_union_left _ hn),
      ihb ht.2 g fun n hn ↦ hv n (Finset.mem_union_right _ hn)]

-- λ-conversion, AS4 of Ty₂ (p. 60): a function abstracted over `n` applied to `a` has the value
-- of its body with `a` for `n`, where `a` is free for `n` in the body
theorem eval_beta {n : ℕ} {β : Ty} {b : Ty2.Term Γ K β} {a : Ty2.Term Γ K (Γ n)}
    (hb : b.FreeFor (Function.update (fun k ↦ .var k) n a)) (g : ∀ n, Ty.Domain E W (Γ n)) :
    (Ty2.Term.app (.lam n b) a).eval I g =
      (b.subst (Function.update (fun k ↦ .var k) n a)).eval I g := by
  rw [eval_subst I hb]
  refine congrArg (b.eval I) (funext fun k ↦ ?_)
  obtain rfl | hk := eq_or_ne k n
  · rw [Function.update_self, Function.update_self]
  · simp [Function.update_of_ne hk, eval]

end Ty2.Term

/-! ### IL and its translation -/

/-- The terms of IL over the constants `K`, under a typing `Γ` of the variable indices: variables,
constants, application, abstraction, identity, the intension `^A` of a term and the value `ˇA` at
the current index of an intension (p. 11). -/
inductive IL.Term (Γ : ℕ → Ty) (K : Ty → Type u) : Ty → Type u
  | var (n : ℕ) : IL.Term Γ K (Γ n)
  | const {α : Ty} (c : K α) : IL.Term Γ K α
  | app {α β : Ty} (f : IL.Term Γ K (α ⇒ β)) (a : IL.Term Γ K α) : IL.Term Γ K β
  | lam {β : Ty} (n : ℕ) (b : IL.Term Γ K β) : IL.Term Γ K (Γ n ⇒ β)
  | ident {α : Ty} (a b : IL.Term Γ K α) : IL.Term Γ K .t
  | up {α : Ty} (a : IL.Term Γ K α) : IL.Term Γ K (intens α)
  | down {α : Ty} (a : IL.Term Γ K (intens α)) : IL.Term Γ K α

variable {K : Ty → Type u} {E W : Type} {Γ : ℕ → Ty}

/-- The value of a term at the index `i` under the assignment `g`, given the meaning `m` of the
constants, a function from indices (p. 13): a constant denotes its meaning at `i`, identity is
equality, `^A` denotes the function from each index to the value of `A` there, and `ˇA` the value
of `A` at `i` applied to `i`. -/
noncomputable def IL.Term.value (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α) :
    (∀ n, Ty.Domain E W (Γ n)) → W → {α : Ty} → IL.Term Γ K α → Ty.Domain E W α
  | g, _, _, .var n => g n
  | _, i, _, .const c => m c i
  | g, i, _, .app f a => f.value m g i (a.value m g i)
  | g, i, _, .lam n b => fun x ↦ b.value m (Function.update g n x) i
  | g, i, _, .ident a b => a.value m g i = b.value m g i
  | g, _, _, .up a => fun j ↦ a.value m g j
  | g, i, _, .down a => a.value m g i i

-- p. 14: `ˇ^A` always has the value of `A`
theorem value_down_up (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α)
    (g : ∀ n, Ty.Domain E W (Γ n)) (i : W) {α : Ty} (A : IL.Term Γ K α) :
    (IL.Term.down (.up A)).value m g i = A.value m g i :=
  rfl

/-- The constant of the model for `^ˇA`: an individual concept. -/
inductive Concept : Ty → Type
  | c : Concept (intens e)

-- p. 14: `^ˇA` need not have the value of `A`, here for a concept whose meaning at each index is
-- the concept constant at that index
theorem value_up_down_ne :
    (IL.Term.up (.down (.const Concept.c)) : IL.Term (fun _ ↦ e) Concept _).value
        (E := Bool) (fun | .c => fun i _ ↦ i) (fun _ ↦ false) true ≠
      (IL.Term.const Concept.c : IL.Term (fun _ ↦ e) Concept _).value (fun | .c => fun i _ ↦ i)
        (fun _ ↦ false) true := by
  intro h
  simpa [IL.Term.value] using congrFun h false

/-- The constants of Ty₂ the translation introduces: for each constant of IL of type `α`, a
constant of type `⟨s,α⟩` naming its intension (p. 61). -/
inductive Constant (K : Ty → Type u) : Ty → Type u
  | intension {α : Ty} (c : K α) : Constant K (intens α)

/-- The interpretation of the constants of Ty₂: a constant's intension is the meaning `m` gives the
constant of IL. -/
def Constant.interp (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α) :
    ∀ {α : Ty}, Constant K α → Ty.Domain E W α
  | _, .intension c => m c

/-- The typing of the translate's indices: the index variable `0` has type `s`, and the index
`n + 1` the type `Γ` gives `n`. -/
def typing (Γ : ℕ → Ty) : ℕ → Ty
  | 0 => s
  | n + 1 => Γ n

/-- The translate of a term of IL into Ty₂ (p. 61): a variable keeps its shape with its index
shifted, a constant is its intension applied to the index variable, application, abstraction and
identity keep their shape, `^A` is the abstraction of the translate of `A` over the index variable,
and `ˇA` its application to that variable. -/
def IL.Term.toTy2 : {α : Ty} → IL.Term Γ K α → Ty2.Term (typing Γ) (Constant K) α
  | _, .var n => .var (n + 1)
  | _, .const c => .app (.const (.intension c)) (.var 0)
  | _, .app f a => .app f.toTy2 a.toTy2
  | _, .lam n b => .lam (n + 1) b.toTy2
  | _, .ident a b => .ident a.toTy2 b.toTy2
  | _, .up a => .lam 0 a.toTy2
  | _, .down a => .app a.toTy2 (.var 0)

-- p. 61, clauses (ii), (iii) and (vi): `A(^B)` goes to `A*(λxₛ B*)`
example (f : K (intens .t ⇒ .t)) (p : K .t) :
    (IL.Term.app (.const f) (.up (.const p)) : IL.Term Γ K .t).toTy2 =
      .app (.app (.const (.intension f)) (.var 0))
        (.lam 0 (.app (.const (.intension p)) (.var 0))) :=
  rfl

/-- Gallin's Lemma 8.2.1, that the translation preserves the semantics: under any assignment `g`
of the translate's variables, the translate denotes the value of the term at the index `g 0` under
the assignment `g` makes to the shifted variables. -/
theorem eval_toTy2 (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α)
    (g : ∀ n, Ty.Domain E W (typing Γ n)) {α : Ty} (A : IL.Term Γ K α) :
    A.toTy2.eval (Constant.interp m) g = A.value m (fun n ↦ g (n + 1)) (g 0) := by
  induction A generalizing g with
  | var n => rfl
  | const c => rfl
  | app f a ihf iha => simp only [IL.Term.toTy2, Ty2.Term.eval, ihf, iha]; rfl
  | lam n b ih =>
    funext x
    refine (ih (Function.update g (n + 1) x)).trans ?_
    rw [Function.update_comp_eq_of_injective' g Nat.succ_injective n x,
      Function.update_of_ne (Nat.succ_ne_zero n).symm]
    rfl
  | ident a b iha ihb =>
    simp only [IL.Term.toTy2, Ty2.Term.eval, iha, ihb]
    rfl
  | up a ih =>
    funext j
    refine (ih (Function.update g 0 j)).trans ?_
    rw [Function.update_comp_eq_of_forall_ne' g _ Nat.succ_ne_zero, Function.update_self]
    rfl
  | down a ih => simp only [IL.Term.toTy2, Ty2.Term.eval, ih]; rfl

/-- Gallin's Theorem 8.2 (i): a formula is valid in IL, true in every model at every index under
every assignment, exactly when its translate is valid in Ty₂. -/
theorem valid_iff_valid_toTy2 (A : IL.Term Γ K .t) :
    (∀ (E W : Type) [Nonempty E] [Nonempty W] (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α)
      (g : ∀ n, Ty.Domain E W (Γ n)) (i : W), A.value m g i) ↔
    ∀ (E W : Type) [Nonempty E] [Nonempty W] (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α)
      (g : ∀ n, Ty.Domain E W (typing Γ n)), A.toTy2.eval (Constant.interp m) g := by
  refine ⟨fun h E W _ _ m g ↦ ?_, fun h E W _ _ m g i ↦ ?_⟩
  · rw [eval_toTy2]
    exact h E W m _ _
  · have := h E W m fun | 0 => i | n + 1 => g n
    rwa [eval_toTy2] at this

/-! ### λ-conversion -/

section Conversion

open Function

/-- The variables free in a term. -/
def IL.Term.freeVars : {α : Ty} → IL.Term Γ K α → Finset ℕ
  | _, .var n => {n}
  | _, .const _ => ∅
  | _, .app f a => f.freeVars ∪ a.freeVars
  | _, .lam n b => b.freeVars.erase n
  | _, .ident a b => a.freeVars ∪ b.freeVars
  | _, .up a => a.freeVars
  | _, .down a => a.freeVars

/-- p. 14: the modally closed terms, the smallest class holding the variables and every `^A`, and
closed under application, identity and abstraction. -/
def IL.Term.ModallyClosed : {α : Ty} → IL.Term Γ K α → Prop
  | _, .var _ | _, .up _ => True
  | _, .const _ | _, .down _ => False
  | _, .app f a => f.ModallyClosed ∧ a.ModallyClosed
  | _, .lam _ b => b.ModallyClosed
  | _, .ident a b => a.ModallyClosed ∧ b.ModallyClosed

/-- The term with each free variable `n` replaced by `σ n`. -/
def IL.Term.subst : {α : Ty} → IL.Term Γ K α → (∀ n, IL.Term Γ K (Γ n)) → IL.Term Γ K α
  | _, .var n, σ => σ n
  | _, .const c, _ => .const c
  | _, .app f a, σ => .app (f.subst σ) (a.subst σ)
  | _, .lam n b, σ => .lam n (b.subst (update σ n (.var n)))
  | _, .ident a b, σ => .ident (a.subst σ) (b.subst σ)
  | _, .up a, σ => .up (a.subst σ)
  | _, .down a, σ => .down (a.subst σ)

/-- p. 19, condition (i) of AS4: no free occurrence of `x` lies within a part `λy C` where `y` is
free in `B`. -/
def IL.Term.FreeFor : {α : Ty} → IL.Term Γ K α → (x : ℕ) → IL.Term Γ K (Γ x) → Prop
  | _, .var _, _, _ | _, .const _, _, _ => True
  | _, .app f a, x, B => f.FreeFor x B ∧ a.FreeFor x B
  | _, .lam y b, x, B => y = x ∨ ((x ∈ b.freeVars → y ∉ B.freeVars) ∧ b.FreeFor x B)
  | _, .ident a b, x, B => a.FreeFor x B ∧ b.FreeFor x B
  | _, .up a, x, B => a.FreeFor x B
  | _, .down a, x, B => a.FreeFor x B

/-- p. 19, the negation of condition (ii) of AS4: a free occurrence of `x` lies within the scope of
`^`. -/
def IL.Term.FreeInUp (x : ℕ) : {α : Ty} → IL.Term Γ K α → Prop
  | _, .var _ | _, .const _ => False
  | _, .app f a => f.FreeInUp x ∨ a.FreeInUp x
  | _, .lam y b => y ≠ x ∧ b.FreeInUp x
  | _, .ident a b => a.FreeInUp x ∨ b.FreeInUp x
  | _, .up a => x ∈ a.freeVars
  | _, .down a => a.FreeInUp x

theorem IL.Term.FreeInUp.mem_freeVars {x : ℕ} {α : Ty} {A : IL.Term Γ K α} (h : A.FreeInUp x) :
    x ∈ A.freeVars := by
  induction A <;> simp_all [IL.Term.FreeInUp, IL.Term.freeVars] <;> tauto

theorem succ_mem_freeVars_toTy2 {k : ℕ} {α : Ty} (A : IL.Term Γ K α) :
    k + 1 ∈ A.toTy2.freeVars ↔ k ∈ A.freeVars := by
  induction A <;> simp_all [IL.Term.toTy2, IL.Term.freeVars, Ty2.Term.freeVars]

/-- A term is modally closed exactly when its translate does not read the index variable. -/
theorem modallyClosed_iff {α : Ty} (A : IL.Term Γ K α) :
    A.ModallyClosed ↔ 0 ∉ A.toTy2.freeVars := by
  induction A <;> simp_all [IL.Term.ModallyClosed, IL.Term.toTy2, Ty2.Term.freeVars]

-- p. 14: the value of a modally closed term is independent of the index
theorem value_eq_of_modallyClosed (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α)
    (g : ∀ n, Ty.Domain E W (Γ n)) (i j : W) {α : Ty} {A : IL.Term Γ K α}
    (h : A.ModallyClosed) : A.value m g i = A.value m g j := by
  have e := fun v : W ↦ eval_toTy2 m (fun | 0 => v | n + 1 => g n) A
  refine (e i).symm.trans (.trans ?_ (e j))
  refine Ty2.Term.eval_congr_of_agree _ _ fun n hn ↦ ?_
  cases n with
  | zero => exact absurd hn ((modallyClosed_iff A).1 h)
  | succ n => rfl

/-- The replacements of the translate that correspond to replacements in a term of IL: the index
variable stays. -/
def lift (σ : ∀ n, IL.Term Γ K (Γ n)) : ∀ n, Ty2.Term (typing Γ) (Constant K) (typing Γ n)
  | 0 => .var 0
  | n + 1 => (σ n).toTy2

theorem toTy2_subst {α : Ty} (A : IL.Term Γ K α) (σ : ∀ n, IL.Term Γ K (Γ n)) :
    (A.subst σ).toTy2 = A.toTy2.subst (lift σ) := by
  induction A generalizing σ with
  | var n => rfl
  | const c => rfl
  | app f a ihf iha => simp only [IL.Term.subst, IL.Term.toTy2, Ty2.Term.subst, ihf, iha]
  | lam n b ih =>
    simp only [IL.Term.subst, IL.Term.toTy2, Ty2.Term.subst, ih]
    congr 2
    funext k
    cases k with
    | zero => simp [lift]
    | succ k =>
      obtain rfl | hk := eq_or_ne k n
      · simp [lift, IL.Term.toTy2]
      · have hk' : k + 1 ≠ n + 1 := by omega
        simp [lift, update_of_ne hk, update_of_ne hk']
  | ident a b iha ihb => simp only [IL.Term.subst, IL.Term.toTy2, Ty2.Term.subst, iha, ihb]
  | up a ih =>
    simp only [IL.Term.subst, IL.Term.toTy2, Ty2.Term.subst, ih]
    congr 2
    funext k
    cases k <;> simp [lift]
  | down a ih => simp only [IL.Term.subst, IL.Term.toTy2, Ty2.Term.subst, ih]; rfl

/-- The replacement of the translate's variable `x + 1` by the translate of `B`. -/
abbrev replacement (x : ℕ) (B : IL.Term Γ K (Γ x)) :
    ∀ n, Ty2.Term (typing Γ) (Constant K) (typing Γ n) :=
  update (fun k ↦ .var k) (x + 1) B.toTy2

theorem lift_update_var (x : ℕ) (B : IL.Term Γ K (Γ x)) :
    lift (update (fun k ↦ .var k) x B) = replacement x B := by
  funext k
  cases k with
  | zero => simp [lift]
  | succ k =>
    obtain rfl | hk := eq_or_ne k x
    · simp [lift]
    · have hk' : k + 1 ≠ x + 1 := by omega
      simp [lift, update_of_ne hk, update_of_ne hk', IL.Term.toTy2]

theorem replacement_self (x : ℕ) (B : IL.Term Γ K (Γ x)) :
    replacement x B (x + 1) = B.toTy2 :=
  update_self ..

theorem replacement_of_ne {x m : ℕ} (hm : m ≠ x + 1) (B : IL.Term Γ K (Γ x)) :
    replacement x B m = .var m :=
  update_of_ne hm ..

theorem update_replacement {x y : ℕ} (hy : y ≠ x + 1) (B : IL.Term Γ K (Γ x)) :
    update (replacement x B) y (.var y) = replacement x B := by
  funext k
  obtain rfl | hk := eq_or_ne k y
  · simp [update_of_ne hy]
  · simp [update_of_ne hk]

/-- Conditions (i), and (ii) or (ii'), of AS4 say that `B` is free for `x` in the translate. -/
theorem freeFor_toTy2 {x : ℕ} {B : IL.Term Γ K (Γ x)} {α : Ty} {A : IL.Term Γ K α}
    (h₁ : A.FreeFor x B) (h₂ : ¬ A.FreeInUp x ∨ B.ModallyClosed) :
    A.toTy2.FreeFor (replacement x B) := by
  induction A with
  | var n => trivial
  | const c => exact ⟨trivial, trivial⟩
  | app f a ihf iha =>
    simp only [IL.Term.FreeFor] at h₁
    exact ⟨ihf h₁.1 (h₂.imp (fun h h' ↦ h (Or.inl h')) id),
      iha h₁.2 (h₂.imp (fun h h' ↦ h (Or.inr h')) id)⟩
  | lam y b ih =>
    simp only [IL.Term.FreeFor] at h₁
    simp only [IL.Term.toTy2, Ty2.Term.FreeFor]
    obtain rfl | hyx := eq_or_ne y x
    · refine ⟨fun m _ hm h ↦ ?_, ?_⟩
      · rw [replacement_of_ne hm] at h
        exact hm (Finset.mem_singleton.1 h).symm
      · rw [replacement, update_idem, update_eq_self_iff.2 rfl]
        exact Ty2.Term.freeFor_var _
    · have hne : y + 1 ≠ x + 1 := by omega
      obtain ⟨hcap, hb⟩ := h₁.resolve_left hyx
      refine ⟨fun m hm hmy h ↦ ?_, ?_⟩
      · obtain rfl | hmx := eq_or_ne m (x + 1)
        · rw [replacement_self] at h
          exact hcap ((succ_mem_freeVars_toTy2 b).1 hm) ((succ_mem_freeVars_toTy2 B).1 h)
        · rw [replacement_of_ne hmx] at h
          exact hmy (Finset.mem_singleton.1 h).symm
      · rw [update_replacement hne]
        exact ih hb (h₂.imp (fun h h' ↦ h ⟨hyx, h'⟩) id)
  | ident a b iha ihb =>
    simp only [IL.Term.FreeFor] at h₁
    exact ⟨iha h₁.1 (h₂.imp (fun h h' ↦ h (Or.inl h')) id),
      ihb h₁.2 (h₂.imp (fun h h' ↦ h (Or.inr h')) id)⟩
  | up a ih =>
    simp only [IL.Term.FreeFor] at h₁
    simp only [IL.Term.toTy2, Ty2.Term.FreeFor]
    refine ⟨fun m hm hm0 h ↦ ?_, ?_⟩
    · obtain rfl | hmx := eq_or_ne m (x + 1)
      · rw [replacement_self] at h
        obtain h' | h' := h₂
        · exact h' ((succ_mem_freeVars_toTy2 a).1 hm)
        · exact (modallyClosed_iff B).1 h' h
      · rw [replacement_of_ne hmx] at h
        exact hm0 (Finset.mem_singleton.1 h).symm
    · rw [update_replacement (by omega)]
      exact ih h₁ (h₂.imp (fun h h' ↦ h h'.mem_freeVars) id)
  | down a ih =>
    simp only [IL.Term.FreeFor] at h₁
    exact ⟨ih h₁ h₂, trivial⟩

/-- p. 19, AS4 of IL: λ-conversion, where `B` is free for `x` in `A` and either no free occurrence
of `x` lies within the scope of `^` or `B` is modally closed. It is AS4 of Ty₂ (p. 60), pulled back
along the translation. -/
theorem value_app_lam (m : ∀ {α : Ty}, K α → W → Ty.Domain E W α)
    (g : ∀ n, Ty.Domain E W (Γ n)) (i : W) {x : ℕ} {β : Ty} {A : IL.Term Γ K β}
    {B : IL.Term Γ K (Γ x)} (h₁ : A.FreeFor x B) (h₂ : ¬ A.FreeInUp x ∨ B.ModallyClosed) :
    (IL.Term.app (.lam x A) B).value m g i =
      (A.subst (update (fun k ↦ .var k) x B)).value m g i := by
  let g' : ∀ n, Ty.Domain E W (typing Γ n) := fun | 0 => i | n + 1 => g n
  have e := Ty2.Term.eval_beta (Constant.interp m) (freeFor_toTy2 h₁ h₂) g'
  have e₂ := eval_toTy2 m g' (A.subst (update (fun k ↦ .var k) x B))
  rw [toTy2_subst, lift_update_var] at e₂
  exact (eval_toTy2 m g' (.app (.lam x A) B)).symm.trans (e.trans e₂)

-- p. 16: unrestricted, the law fails: `(λx. ^x)(ˇc)` differs from `^ˇc` where `ˇc` is not rigid
theorem value_app_lam_ne :
    IL.Term.value (E := Bool) (fun | Concept.c => fun i _ ↦ i) (fun _ ↦ false) true
        (.app (.lam 0 (.up (.var 0))) (.down (.const Concept.c)) :
          IL.Term (fun _ ↦ e) Concept _) ≠
      IL.Term.value (E := Bool) (fun | Concept.c => fun i _ ↦ i) (fun _ ↦ false) true
        ((.up (.var 0) : IL.Term (fun _ ↦ e) Concept _).subst
          (update (fun k ↦ .var k) 0 (.down (.const Concept.c)))) := by
  intro h
  simpa [IL.Term.value, IL.Term.subst] using congrFun h false

end Conversion

end Gallin1975
