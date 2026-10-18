module

public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Composition.Assignment

/-!
# Terms of the composition modes

A logical form is a term: the constants its words translate to, the variables of type `e` its
traces bind, the abstraction over such a variable, and the composition of two terms by a mode
(`Montague.Term`). Every interpretation of the trees is an evaluation of their terms: the
denotation under an assignment of the variables (`Montague.Term.eval`), whose variable and
abstraction cases are Heim and Kratzer's Traces and Pronouns Rule and Predicate Abstraction; the
denotation under an applicative effect, where abstraction needs the effect's distributor
(`Montague.Term.evalM`); and the partial denotation of `Composition/Partial.lean`. Trees translate
to terms in `Composition/Tree.lean`.

## Main definitions

* `Montague.Term`: the terms over a signature of constants.
* `Montague.Term.eval`, `Montague.Term.evalM`: the denotation of a term, pure and under an
  applicative effect.
* `Montague.PredAbs`: the distributor an effect needs for abstraction.

## Main results

* `Montague.Term.eval_var`, `Montague.Term.eval_lam`: a variable denotes by `interpPronoun` and an
  abstraction by `lambdaAbsG`.
* `Montague.Term.evalM_id`: at the identity effect, evaluation is the pure denotation.
* `Montague.Term.evalM_congr_of_agree`: a term's denotation depends on the assignment only at its
  free variables.

## Implementation notes

Variables are named by the trace indices, so a binder with index `n` translates to the
abstraction over the variable `n`, and translation needs no fresh names.

## References

* [heim-kratzer-1998]
* [montague-1973]
-/

@[expose] public section

universe u

namespace Montague

/-- The terms over a signature `K` of constants are, by type, the constants, the variables of
type `e`, the abstractions over a variable, and the compositions of two terms by a mode. -/
inductive Term (K : Ty → Type u) : Ty → Type u where
  | const {ty : Ty} (c : K ty) : Term K ty
  | var (n : ℕ) : Term K .e
  | lam {τ : Ty} (n : ℕ) (body : Term K τ) : Term K (.e ⇒ τ)
  | comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term K σ₁) (r : Term K σ₂) : Term K τ

/-- An effect supports Predicate Abstraction when it has an entity-distributor, which commutes
`M` over entity-indexed families. `Id` and the Reader-like effects have one; scope effects such
as `Cont R` do not, since abstraction would have to run one continuation at every entity at
once, and record that by `dist? = none`. -/
class PredAbs (M : Type → Type) (E W : Type) (D : Type := ℝ) where
  /-- The entity-distributor, if the effect has one. -/
  dist? : Option (∀ ty : Ty, (E → M (Ty.Domain E W ty D)) → M (E → Ty.Domain E W ty D))

instance (E W D : Type) : PredAbs Id E W D := ⟨some fun _ f ↦ f⟩

@[simp] theorem PredAbs.dist?_id (E W D : Type) :
    PredAbs.dist? (M := Id) (E := E) (W := W) (D := D) = some fun _ f ↦ f := rfl

namespace Term

variable {K K' : Ty → Type*}

/-- Rename the constants of a term. -/
def map (f : ∀ {ty : Ty}, K ty → K' ty) : {ty : Ty} → Term K ty → Term K' ty
  | _, const c => const (f c)
  | _, var n => var n
  | _, lam n b => lam n (b.map f)
  | _, comp m l r => comp m (l.map f) (r.map f)

/-- The free variables of a term. -/
def freeVars : {ty : Ty} → Term K ty → Finset ℕ
  | _, const _ => ∅
  | _, var n => {n}
  | _, lam n b => b.freeVars.erase n
  | _, comp _ l r => l.freeVars ∪ r.freeVars

/-- Two terms over two signatures have the same shape, with constants related by `R`. -/
inductive Rel (R : ∀ ty : Ty, K ty → K' ty → Prop) : {ty : Ty} → Term K ty → Term K' ty → Prop
  | const {ty : Ty} {c : K ty} {c' : K' ty} : R ty c c' → Rel R (const c) (const c')
  | var (n : ℕ) : Rel R (var n) (var n)
  | lam {τ : Ty} (n : ℕ) {b : Term K τ} {b' : Term K' τ} : Rel R b b' → Rel R (lam n b) (lam n b')
  | comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) {l : Term K σ₁} {l' : Term K' σ₁} {r : Term K σ₂}
      {r' : Term K' σ₂} : Rel R l l' → Rel R r r' → Rel R (comp m l r) (comp m l' r')

variable {E W D : Type}

open scoped Assignment

/-- The denotation of a term under an interpretation of the constants and an assignment of the
variables. -/
def eval (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D) (g : Assignment E) :
    {ty : Ty} → Term K ty → Ty.Domain E W ty D
  | _, const c => I c
  | _, var n => g n
  | _, lam n b => fun x ↦ eval I (g[n ↦ x]) b
  | _, comp m l r => m.eval (eval I g l) (eval I g r)

/-- A variable denotes the value of its index under the assignment, by the Traces and Pronouns
Rule. -/
theorem eval_var (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D) (g : Assignment E) (n : ℕ) :
    (var n : Term K .e).eval I g = interpPronoun n g :=
  rfl

/-- An abstraction denotes the abstraction of its body over its variable, by Predicate
Abstraction. -/
theorem eval_lam (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D) (g : Assignment E) (n : ℕ)
    {τ : Ty} (b : Term K τ) : (lam n b).eval I g = lambdaAbsG n (fun g' ↦ b.eval I g') g :=
  rfl

/-- `evalM I g t` is the denotation of `t` under an applicative effect, given an interpretation
`I` of the constants as computations and an assignment `g`. A composition runs its left daughter
first, and an abstraction distributes the effect over the entities, so `evalM` is `none` when
the effect has no distributor. -/
def evalM {M : Type → Type} [Applicative M] [PredAbs M E W D]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty D)) (g : Assignment E) :
    {ty : Ty} → Term K ty → Option (M (Ty.Domain E W ty D))
  | _, const c => some (I c)
  | _, var n => some (pure (g n))
  | _, lam n b => (PredAbs.dist? (M := M) (E := E) (W := W) (D := D)).bind fun dist ↦
      (evalM I g b).map fun probe ↦ dist _ fun x ↦ (evalM I (g[n ↦ x]) b).getD probe
  | _, comp m l r => (evalM I g l).bind fun a ↦ (evalM I g r).map fun b ↦ m.evalM a b

/-- At the identity effect, evaluation is the pure denotation. -/
@[simp] theorem evalM_id (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D) (g : Assignment E)
    {ty : Ty} (t : Term K ty) : t.evalM (M := Id) I g = some (t.eval I g) := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => simp [evalM, ih, eval]
  | comp m l r ihl ihr => simp only [evalM, ihl, ihr, Option.bind_some, Option.map_some]; rfl

/-- The denotation of a renamed term interprets the renamed constants. -/
theorem eval_map (I : ∀ {ty : Ty}, K' ty → Ty.Domain E W ty D) (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).eval I g = t.eval (fun c ↦ I (f c)) g := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => funext x; exact ih _
  | comp m l r ihl ihr => simp only [map, eval, ihl, ihr]

/-- Evaluating a renamed term interprets the renamed constants. -/
theorem evalM_map {M : Type → Type} [Applicative M] [PredAbs M E W D]
    (I : ∀ {ty : Ty}, K' ty → M (Ty.Domain E W ty D)) (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).evalM I g = t.evalM (fun c ↦ I (f c)) g := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => simp only [map, evalM, ih]
  | comp m l r ihl ihr => simp only [map, evalM, ihl, ihr]

/-- Whether a term has a denotation under an effect, and at which type, does not depend on the
assignment. -/
theorem isSome_evalM {M : Type → Type} [Applicative M] [PredAbs M E W D]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty D)) (g g' : Assignment E) {ty : Ty}
    (t : Term K ty) : (t.evalM I g).isSome = (t.evalM I g').isSome := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => rfl
  | lam n b ih =>
    simp only [evalM]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) <;> simp [ih g g']
  | comp m l r ihl ihr =>
    have hl := ihl g g'
    have hr := ihr g g'
    simp only [evalM]
    cases h₁ : l.evalM I g <;> cases h₂ : l.evalM I g' <;> cases h₃ : r.evalM I g <;>
      cases h₄ : r.evalM I g' <;> simp_all

/-- A term's denotation depends on the assignment only at its free variables. -/
theorem evalM_congr_of_agree {M : Type → Type} [Applicative M] [PredAbs M E W D]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty D)) {ty : Ty} (t : Term K ty)
    {g g' : Assignment E} (h : ∀ n ∈ t.freeVars, g n = g' n) : t.evalM I g = t.evalM I g' := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => simp [evalM, h n (Finset.mem_singleton_self n)]
  | lam n b ih =>
    have hb : ∀ x, b.evalM I (g[n ↦ x]) = b.evalM I (g'[n ↦ x]) := fun x ↦ ih fun m hm ↦ by
      by_cases hmn : m = n
      · subst hmn; simp
      · simp [Function.update_of_ne hmn, h m (Finset.mem_erase.2 ⟨hmn, hm⟩)]
    simp only [evalM]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) with
    | none => rfl
    | some dist =>
      have hsome := isSome_evalM I g g' b
      simp only [Option.bind_some]
      rcases hg : b.evalM I g with _ | p <;> rcases hg' : b.evalM I g' with _ | p' <;>
        simp only [hg, hg', Option.isSome_none, Option.isSome_some, reduceCtorEq] at hsome
      · rfl
      · simp only [Option.map_some, Option.some.injEq]
        congr 1
        funext x
        rw [hb x]
        have hx : (b.evalM I (g'[n ↦ x])).isSome := by
          rw [isSome_evalM I _ g' b, hg']; rfl
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hx
        simp [hv]
  | comp m l r ihl ihr =>
    simp only [freeVars, Finset.mem_union] at h
    simp only [evalM, ihl fun n hn ↦ h n (.inl hn), ihr fun n hn ↦ h n (.inr hn)]

end Term

end Montague
