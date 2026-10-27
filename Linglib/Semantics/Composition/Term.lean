module

public import Linglib.Core.Control.Distributive
public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Composition.Assignment

/-!
# Logical forms as terms

A logical form is a term, built from the constants its words translate to, variables for the
individuals its traces denote, abstraction, and composition by a mode. Its denotation under an
assignment follows [the Traces and Pronouns Rule](##eval_var) and
[Predicate Abstraction](##eval_lam), and its intension, under words interpreted as intensions, is
its denotation at every world; the denotation is
[the case of words that do not vary with the world](##intension_const_interp). Under an effect,
such as a set of readings, a term denotes a computation.

## Main definitions

* `Montague.Term`: the terms over a signature of constants.
* `Montague.Term.eval`, `Montague.Term.evalM`: the denotation of a term, pure and under an
  applicative effect.
* `Montague.Term.intension`: the intension of a term, its denotation at each world.

## Implementation notes

Variables are named by the trace indices, so a binder with index `n` translates to the
abstraction over the variable `n`, and translation needs no fresh names. Trees translate to terms
in `Composition/Tree.lean`, and the partial denotation of a term is in `Composition/Partial.lean`.

Under an effect, the body of an abstraction is a computation at each entity, and the abstract is
the computation of a function that `Distributive` gives. Scope effects such as continuations do
not distribute over functions, so the engine does not interpret them. For a set of readings the
distribution chooses a reading at each entity: Kratzer and Shimoyama's abstraction, which Shan and
Charlow show overgenerates functional readings, since a constant family of readings distributes to
more than the constant functions (`SetM.not_preservesConst`).

## References

* [heim-kratzer-1998]
* [montague-1973]
* [von-fintel-heim-2011]
* [kratzer-shimoyama-2002]
* [shan-2004]
* [charlow-2020]
-/

@[expose] public section

universe u

namespace Montague

/-- The terms over a signature `K` of constants are, by type, the constants, the variables of
type `e`, the abstractions over a variable, and the compositions of two terms by a mode. -/
inductive Term (K : Ty → Type u) : Ty → Type u where
  /-- A constant of the signature. -/
  | const {ty : Ty} (c : K ty) : Term K ty
  /-- The variable of type `e` with index `n`. -/
  | var (n : ℕ) : Term K .e
  /-- The abstraction of a body over the variable `n`. -/
  | lam {τ : Ty} (n : ℕ) (body : Term K τ) : Term K (.e ⇒ τ)
  /-- The composition of two terms by a mode. -/
  | comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term K σ₁) (r : Term K σ₂) : Term K τ

namespace Term

variable {K K' : Ty → Type*}

/-- The term with its constants renamed by `f`. -/
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

variable {E W : Type} {S : Sorts}

open scoped Assignment

/-- The denotation of a term under an interpretation of the constants and an assignment of the
variables. -/
def eval (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E) :
    {ty : Ty} → Term K ty → Ty.Domain E W ty S
  | _, const c => I c
  | _, var n => g n
  | _, lam n b => fun x ↦ eval I (g[n ↦ x]) b
  | _, comp m l r => m.eval (eval I g l) (eval I g r)

/-- A variable denotes the value of its index under the assignment, by the Traces and Pronouns
Rule. -/
theorem eval_var (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E) (n : ℕ) :
    (var n : Term K .e).eval I g = g n :=
  rfl

/-- An abstraction denotes the abstraction of its body over its variable, by Predicate
Abstraction. -/
theorem eval_lam (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E) (n : ℕ)
    {τ : Ty} (b : Term K τ) : (lam n b).eval I g = lambdaAbsG n (fun g' ↦ b.eval I g') g :=
  rfl

/-- The intension of a term under an interpretation `I` of the constants as intensions and an
assignment of the variables: at each world, a constant denotes its intension's value there and a
composition composes the daughters' intensions by its mode (`Mode.intension`). -/
def intension (I : ∀ {ty : Ty}, K ty → W → Ty.Domain E W ty S) (g : Assignment E) :
    {ty : Ty} → Term K ty → W → Ty.Domain E W ty S
  | _, const c => I c
  | _, var n => fun _ ↦ g n
  | _, lam n b => fun w x ↦ intension I (g[n ↦ x]) b w
  | _, comp m l r => m.intension (intension I g l) (intension I g r)

/-- Under constants that do not vary with the world, a term's intension is constant at its
denotation, so the evaluation `eval` is the case of a lexicon of rigid intensions. -/
@[simp] theorem intension_const_interp (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S)
    (g : Assignment E) {ty : Ty} (t : Term K ty) (w : W) :
    t.intension (fun c _ ↦ I c) g w = t.eval I g := by
  induction t generalizing g w with
  | const c => rfl
  | var n => rfl
  | lam n b ih => funext x; exact ih _ w
  | comp m l r ihl ihr =>
    simp only [intension, eval]
    rw [show l.intension (fun c _ ↦ I c) g = fun _ ↦ l.eval I g from funext (ihl g),
      show r.intension (fun c _ ↦ I c) g = fun _ ↦ r.eval I g from funext (ihr g),
      Mode.intension_const]

/-- The denotation of a term under an applicative effect, given an interpretation `I` of the
constants as computations and an assignment `g`. A composition runs its left daughter first, and
an abstraction distributes the effect over the entities. -/
def evalM {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : Assignment E) :
    {ty : Ty} → Term K ty → Option (M (Ty.Domain E W ty S))
  | _, const c => some (I c)
  | _, var n => some (pure (g n))
  | _, lam n b =>
      (evalM I g b).map fun probe ↦ distribute fun x ↦ (evalM I (g[n ↦ x]) b).getD probe
  | _, comp m l r => (evalM I g l).bind fun a ↦ (evalM I g r).map fun b ↦ m.evalM a b

/-- At the identity effect, evaluation is the pure denotation. -/
@[simp] theorem evalM_id (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E)
    {ty : Ty} (t : Term K ty) : t.evalM (M := Id) I g = some (t.eval I g) := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => simp [evalM, ih, eval]
  | comp m l r ihl ihr => simp only [evalM, ihl, ihr, Option.bind_some, Option.map_some]; rfl

theorem eval_map (I : ∀ {ty : Ty}, K' ty → Ty.Domain E W ty S) (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).eval I g = t.eval (fun c ↦ I (f c)) g := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => funext x; exact ih _
  | comp m l r ihl ihr => simp only [map, eval, ihl, ihr]

theorem intension_map (I : ∀ {ty : Ty}, K' ty → W → Ty.Domain E W ty S)
    (f : ∀ {ty : Ty}, K ty → K' ty) (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).intension I g = t.intension (fun c ↦ I (f c)) g := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => funext w x; exact congrFun (ih _) w
  | comp m l r ihl ihr => simp only [map, intension, ihl, ihr]

theorem evalM_map {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K' ty → M (Ty.Domain E W ty S)) (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).evalM I g = t.evalM (fun c ↦ I (f c)) g := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => simp only [map, evalM, ih]
  | comp m l r ihl ihr => simp only [map, evalM, ihl, ihr]

theorem isSome_evalM {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g g' : Assignment E) {ty : Ty}
    (t : Term K ty) : (t.evalM I g).isSome = (t.evalM I g').isSome := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => rfl
  | lam n b ih => simp [evalM, ih g g']
  | comp m l r ihl ihr =>
    have hl := ihl g g'
    have hr := ihr g g'
    simp only [evalM]
    cases h₁ : l.evalM I g <;> cases h₂ : l.evalM I g' <;> cases h₃ : r.evalM I g <;>
      cases h₄ : r.evalM I g' <;> simp_all

/-- A term's denotation depends on the assignment only at its free variables. -/
theorem evalM_congr_of_agree {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) {ty : Ty} (t : Term K ty)
    {g g' : Assignment E} (h : ∀ n ∈ t.freeVars, g n = g' n) : t.evalM I g = t.evalM I g' := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => simp [evalM, h n (Finset.mem_singleton_self n)]
  | lam n b ih =>
    have hb : ∀ x, b.evalM I (g[n ↦ x]) = b.evalM I (g'[n ↦ x]) := fun x ↦ ih fun m hm ↦ by
      by_cases hmn : m = n
      · subst hmn; simp
      · simp [Function.update_of_ne hmn, h m (Finset.mem_erase.2 ⟨hmn, hm⟩)]
    have hsome := isSome_evalM I g g' b
    simp only [evalM]
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

/-- A term whose constants are values of another's sets of values evaluates, under the set effect,
to a set containing the first term's denotation. -/
theorem Rel.mem_run_evalM {ty : Ty} {u : Term (fun ty ↦ Id (Ty.Domain E W ty S)) ty}
    {u' : Term (fun ty ↦ SetM (Ty.Domain E W ty S)) ty}
    (h : Rel (fun _ c c' ↦ c ∈ SetM.run c') u u') (g : Assignment E) :
    ∃ X, u'.evalM (fun c ↦ c) g = some X ∧ u.eval (fun c ↦ c) g ∈ X.run := by
  induction h generalizing g with
  | const hc => exact ⟨_, rfl, hc⟩
  | var n => exact ⟨_, rfl, rfl⟩
  | @lam τ n b b' _ ih =>
    obtain ⟨X₀, hX₀, -⟩ := ih g
    refine ⟨distribute fun x ↦ (b'.evalM (fun c ↦ c) (g[n ↦ x])).getD X₀,
      by simp only [evalM, hX₀, Option.map_some], SetM.mem_run_distribute.2 fun x ↦ ?_⟩
    obtain ⟨X, hX, hmem⟩ := ih (g[n ↦ x])
    simpa [hX, eval] using hmem
  | @comp σ₁ σ₂ τ m l l' r r' _ _ ihl ihr =>
    obtain ⟨Xl, hXl, hl⟩ := ihl g
    obtain ⟨Xr, hXr, hr⟩ := ihr g
    refine ⟨m.evalM Xl Xr, by simp only [evalM, hXl, hXr, Option.bind_some, Option.map_some], ?_⟩
    exact ⟨m.eval (l.eval (fun c ↦ c) g), ⟨_, hl, rfl⟩, _, hr, rfl⟩

end Term

end Montague
