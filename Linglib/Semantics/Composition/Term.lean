module

public import Linglib.Core.Control.Distributive
public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Composition.Assignment

/-!
# Logical forms as terms

A logical form is a term, built from the constants its words translate to, variables,
abstraction and composition by a mode. A variable is an index paired with a type, as in von Fintel
and Heim's official notation, the pairing fixed by a typing of the indices: Heim and Kratzer's
indices are all of type $e$, and von Fintel and Heim's world pronouns are indices of type $s$.
A term has a value in any
*interpretation*, which fixes a domain at each type and how constants, variables, abstraction and
the modes are interpreted, and the values of related terms in two interpretations are related
[whenever the relation holds of the constants and variables and survives abstraction and every
mode](##Rel.realize). Composition under an effect is an interpretation, and Heim and Kratzer's
total semantics is its case under the identity effect. An intension is a computation that reads a
world, as Shan treats intensionality, and its type says so (`Ty.comp`), so a semantics relative to
a world is the total semantics of a lexicon whose worldly words have such types.

A term's value commutes with [substitution](##Term.realize_subst) where no binder captures and each
replacement denotes a value, as every term does under the total semantics, where this is
[λ-conversion](##Term.eval_beta); under the set effect
[λ-conversion fails with no capture](##Term.exists_evalM_comp_lam_ne_subst).

## Main definitions

* `Montague.Term`: the terms over a signature of constants under a typing of the indices.
* `Montague.Term.subst`, `Montague.Term.FreeFor`: substitution and when it captures nothing.
* `Montague.individualIndices`: Heim and Kratzer's typing, every index of type `e`.
* `Montague.Interpretation`: an interpretation of the terms.
* `Montague.Term.realize`: the value of a term in an interpretation under an assignment.
* `Montague.Interpretation.total`, `Montague.Interpretation.effectful`: the total and effectful
  interpretations.
* `Montague.Term.eval`, `Montague.Term.evalM`: the values in them.

## Implementation notes

The structure follows mathlib's `FirstOrder.Language.Term.realize`, defined once over any
`L.Structure`: each semantics is an interpretation rather than its own evaluator, and `Rel.realize`
relates two of them by induction on terms; the fundamental lemma of logical relations is its case
in `Composition/LogicalRelation.lean`. Variables are named by the
trace indices, so a binder with index `n` translates to the abstraction over the variable `n`, and
translation needs no fresh names. The typing `Γ : ℕ → Ty` is a parameter of the terms, so an
assignment is a dependent function giving each index a value of its type; under
`individualIndices` it is an ordinary assignment of individuals, and an assignment needs values
only at the types the typing uses. Trees translate to terms in `Composition/Tree.lean`, and the
partial denotation of a term is in `Composition/Partial.lean`.

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
* [gallin-1975]
* [moggi-1991]
* [kratzer-shimoyama-2002]
* [shan-2001]
* [shan-2004]
* [charlow-2020]
-/


@[expose] public section

universe u

namespace Montague

/-- Heim and Kratzer's typing of the variable indices: every index is a variable over
individuals. -/
abbrev individualIndices : ℕ → Ty := fun _ ↦ .e

/-- The terms over a signature `K` of constants, under a typing `Γ` of the variable indices, are,
by type, the constants, the variables, each of the type its index has, the abstractions over
them, and the compositions of two terms by a mode. -/
inductive Term (Γ : ℕ → Ty) (K : Ty → Type u) : Ty → Type u where
  /-- A constant of the signature. -/
  | const {ty : Ty} (c : K ty) : Term Γ K ty
  /-- The variable with index `n`, of the type `Γ n`. -/
  | var (n : ℕ) : Term Γ K (Γ n)
  /-- The abstraction of a body over the variable `n`. -/
  | lam {τ : Ty} (n : ℕ) (body : Term Γ K τ) : Term Γ K (Γ n ⇒ τ)
  /-- The composition of two terms by a mode. -/
  | comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term Γ K σ₁) (r : Term Γ K σ₂) : Term Γ K τ

namespace Term

variable {Γ : ℕ → Ty} {K K' : Ty → Type*}

/-- The term with its constants renamed by `f`. -/
def map (f : ∀ {ty : Ty}, K ty → K' ty) : {ty : Ty} → Term Γ K ty → Term Γ K' ty
  | _, const c => const (f c)
  | _, var n => var n
  | _, lam n b => lam n (b.map f)
  | _, comp m l r => comp m (l.map f) (r.map f)

/-- The free variables of a term. -/
def freeVars : {ty : Ty} → Term Γ K ty → Finset ℕ
  | _, const _ => ∅
  | _, var n => {n}
  | _, lam n b => b.freeVars.erase n
  | _, comp _ l r => l.freeVars ∪ r.freeVars

/-- The term with each free variable `n` replaced by `σ n`. A binder keeps its variable, so a
replacement with that variable free in it is captured; `FreeFor` says when none is. -/
def subst : {ty : Ty} → Term Γ K ty → (∀ n, Term Γ K (Γ n)) → Term Γ K ty
  | _, const c, _ => const c
  | _, var n, σ => σ n
  | _, lam n b, σ => lam n (b.subst (Function.update σ n (var n)))
  | _, comp m l r, σ => comp m (l.subst σ) (r.subst σ)

/-- The replacements `σ` are *free for* a term when no binder in it captures a free variable of
the replacement for a variable free below it. -/
def FreeFor : {ty : Ty} → Term Γ K ty → (∀ n, Term Γ K (Γ n)) → Prop
  | _, const _, _ | _, var _, _ => True
  | _, lam n b, σ => (∀ m ∈ b.freeVars, m ≠ n → n ∉ (σ m).freeVars) ∧
      b.FreeFor (Function.update σ n (var n))
  | _, comp _ l r, σ => l.FreeFor σ ∧ r.FreeFor σ

/-- The variables themselves are free for any term. -/
theorem freeFor_var {ty : Ty} (t : Term Γ K ty) : t.FreeFor fun n ↦ var n := by
  induction t with
  | const c => trivial
  | var n => trivial
  | lam n b ih =>
    refine ⟨fun m _ hmn h ↦ hmn (Finset.mem_singleton.1 h).symm, ?_⟩
    rwa [Function.update_eq_self_iff.2 rfl]
  | comp m l r ihl ihr => exact ⟨ihl, ihr⟩

/-- Two terms over two signatures have the same shape, with constants related by `R`. -/
inductive Rel (R : ∀ ty : Ty, K ty → K' ty → Prop) :
    {ty : Ty} → Term Γ K ty → Term Γ K' ty → Prop
  | const {ty : Ty} {c : K ty} {c' : K' ty} : R ty c c' → Rel R (const c) (const c')
  | var (n : ℕ) : Rel R (var n) (var n)
  | lam {τ : Ty} (n : ℕ) {b : Term Γ K τ} {b' : Term Γ K' τ} :
      Rel R b b' → Rel R (lam n b) (lam n b')
  | comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) {l : Term Γ K σ₁} {l' : Term Γ K' σ₁}
      {r : Term Γ K σ₂} {r' : Term Γ K' σ₂} :
      Rel R l l' → Rel R r r' → Rel R (comp m l r) (comp m l' r')

end Term

/-! ### Interpretations -/

universe u' v w v' w'

/-- An interpretation of the terms over a signature `K`: a domain at each type, what a variable of
each type denotes, and how constants, variables, abstractions and compositions are interpreted. -/
structure Interpretation (K : Ty → Type u) where
  /-- The domain of each type. -/
  D : Ty → Type v
  /-- What a variable of each type denotes. -/
  Val : Ty → Type w
  /-- The value of each constant. -/
  const : ∀ {ty : Ty}, K ty → D ty
  /-- The value of a variable, from what it denotes. -/
  var : ∀ {σ : Ty}, Val σ → D σ
  /-- The value of an abstraction, from its body as a function of what the bound variable
  denotes. -/
  lam : ∀ {σ τ : Ty}, (Val σ → D τ) → D (σ ⇒ τ)
  /-- The value of a composition, from its daughters' values. -/
  mode : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → D σ₁ → D σ₂ → D τ

namespace Interpretation

variable {K : Ty → Type u} {K' : Ty → Type u'}

/-- The interpretation of the terms over `K` that interprets a constant as `A` interprets its image
under `f`. -/
def comap (A : Interpretation.{u', v, w} K') (f : ∀ {ty : Ty}, K ty → K' ty) :
    Interpretation.{u, v, w} K where
  D := A.D
  Val := A.Val
  const c := A.const (f c)
  var := A.var
  lam := A.lam
  mode := A.mode

end Interpretation

namespace Term

variable {Γ : ℕ → Ty} {K : Ty → Type u} {K' : Ty → Type u'}

/-- The value of a term in an interpretation under an assignment of values to the variables, each
of its index's type. -/
def realize (A : Interpretation.{u, v, w} K) (g : ∀ n, A.Val (Γ n)) :
    {ty : Ty} → Term Γ K ty → A.D ty
  | _, const c => A.const c
  | _, var n => A.var (g n)
  | _, lam n b => A.lam fun x ↦ realize A (Function.update g n x) b
  | _, comp m l r => A.mode m (realize A g l) (realize A g r)

section Realize

variable (A : Interpretation.{u, v, w} K) (g : ∀ n, A.Val (Γ n))

@[simp] theorem realize_const {ty : Ty} (c : K ty) :
    (const c : Term Γ K ty).realize A g = A.const c :=
  rfl

@[simp] theorem realize_var (n : ℕ) : (var n : Term Γ K (Γ n)).realize A g = A.var (g n) := rfl

@[simp] theorem realize_lam {τ : Ty} (n : ℕ) (b : Term Γ K τ) :
    (lam n b).realize A g = A.lam fun x ↦ b.realize A (Function.update g n x) := rfl

@[simp] theorem realize_comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term Γ K σ₁)
    (r : Term Γ K σ₂) : (comp m l r).realize A g = A.mode m (l.realize A g) (r.realize A g) := rfl

end Realize

/-- A term's value depends on the assignment only at its free variables. -/
theorem realize_congr_of_agree (A : Interpretation.{u, v, w} K) {ty : Ty} (t : Term Γ K ty)
    {g g' : ∀ n, A.Val (Γ n)} (hg : ∀ n ∈ t.freeVars, g n = g' n) :
    t.realize A g = t.realize A g' := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => exact congrArg A.var (hg n (Finset.mem_singleton_self n))
  | lam n b ih =>
    refine congrArg A.lam (funext fun x ↦ ih fun m hm ↦ ?_)
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [Function.update_of_ne hmn, hg m (Finset.mem_erase.2 ⟨hmn, hm⟩)]
  | comp m l r ihl ihr =>
    simp only [freeVars, Finset.mem_union] at hg
    exact congrArg₂ (A.mode m) (ihl fun n hn ↦ hg n (.inl hn)) (ihr fun n hn ↦ hg n (.inr hn))

/-- The substitution lemma: where each replacement denotes a value that the variable it replaces
denotes under `v`, and no binder captures it, a substituted term has the value of the original
under `v`. Replacements need not be values in general: a computation can have effects that a
variable lacks. -/
theorem realize_subst (A : Interpretation.{u, v, w} K) {ty : Ty} {t : Term Γ K ty}
    {σ : ∀ n, Term Γ K (Γ n)} (ht : t.FreeFor σ) {g v : ∀ n, A.Val (Γ n)}
    (hv : ∀ n ∈ t.freeVars, (σ n).realize A g = A.var (v n)) :
    (t.subst σ).realize A g = t.realize A v := by
  induction t generalizing σ g v with
  | const c => rfl
  | var n => exact hv n (Finset.mem_singleton_self n)
  | lam n b ih =>
    refine congrArg A.lam (funext fun x ↦ ih ht.2 fun m hm ↦ ?_)
    obtain rfl | hmn := eq_or_ne m n
    · simp
    · rw [Function.update_of_ne hmn, Function.update_of_ne hmn,
        realize_congr_of_agree A (σ m) (g' := g) fun k hk ↦ Function.update_of_ne
          (fun hkn : k = n ↦ ht.1 m hm hmn (hkn ▸ hk)) x g]
      exact hv m (Finset.mem_erase.2 ⟨hmn, hm⟩)
  | comp m l r ihl ihr =>
    simp only [freeVars, Finset.mem_union] at hv
    exact congrArg₂ (A.mode m) (ihl ht.1 fun n hn ↦ hv n (.inl hn))
      (ihr ht.2 fun n hn ↦ hv n (.inr hn))

theorem realize_map (A : Interpretation.{u', v, w} K') (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : ∀ n, A.Val (Γ n)) {ty : Ty} (t : Term Γ K ty) :
    (t.map f).realize A g = t.realize (A.comap f) g := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => exact congrArg A.lam (funext fun x ↦ ih _)
  | comp m l r ihl ihr => exact congrArg₂ (A.mode m) (ihl g) (ihr g)

/-- A relation between the values of two interpretations that holds of the constants the terms
relate and of the variables the assignments relate, and that abstraction and every mode preserve,
holds of the values of two related terms. -/
theorem Rel.realize {Rc : ∀ ty : Ty, K ty → K' ty → Prop} {A : Interpretation.{u, v, w} K}
    {B : Interpretation.{u', v', w'} K'} (R : ∀ ty : Ty, A.D ty → B.D ty → Prop)
    (RV : ∀ σ : Ty, A.Val σ → B.Val σ → Prop)
    (hc : ∀ {ty : Ty} (c : K ty) (c' : K' ty), Rc ty c c' → R ty (A.const c) (B.const c'))
    (hv : ∀ {σ : Ty} x y, RV σ x y → R σ (A.var x) (B.var y))
    (hl : ∀ {σ τ : Ty} (f : A.Val σ → A.D τ) (f' : B.Val σ → B.D τ),
      (∀ x y, RV σ x y → R τ (f x) (f' y)) → R (σ ⇒ τ) (A.lam f) (B.lam f'))
    (hm : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) a a' b b', R σ₁ a a' → R σ₂ b b' →
      R τ (A.mode m a b) (B.mode m a' b'))
    {ty : Ty} {t : Term Γ K ty} {t' : Term Γ K' ty} (ht : Rel Rc t t')
    {g : ∀ n, A.Val (Γ n)} {g' : ∀ n, B.Val (Γ n)} (hg : ∀ n, RV (Γ n) (g n) (g' n)) :
    R ty (t.realize A g) (t'.realize B g') := by
  induction ht generalizing g g' with
  | const hc' => exact hc _ _ hc'
  | var n => exact hv _ _ (hg n)
  | lam n _ ih =>
    refine hl _ _ fun x y hxy ↦ ih fun m ↦ ?_
    by_cases hmn : m = n
    · subst hmn; simpa using hxy
    · simpa [Function.update_of_ne hmn] using hg m
  | comp m _ _ ihl ihr => exact hm m _ _ _ _ (ihl hg) (ihr hg)

/-- Every term is related to itself when equal constants are. -/
theorem Rel.refl_eq {ty : Ty} (t : Term Γ K ty) : Rel (fun _ c c' ↦ c = c') t t := by
  induction t with
  | const c => exact .const rfl
  | var n => exact .var n
  | lam n b ih => exact .lam n ih
  | comp m l r ihl ihr => exact .comp m ihl ihr

/-- `Rel.realize` for one term in two interpretations. -/
theorem rel_realize {A : Interpretation.{u, v, w} K} {B : Interpretation.{u, v', w'} K}
    (R : ∀ ty : Ty, A.D ty → B.D ty → Prop) (RV : ∀ σ : Ty, A.Val σ → B.Val σ → Prop)
    (hc : ∀ {ty : Ty} (c : K ty), R ty (A.const c) (B.const c))
    (hv : ∀ {σ : Ty} x y, RV σ x y → R σ (A.var x) (B.var y))
    (hl : ∀ {σ τ : Ty} (f : A.Val σ → A.D τ) (f' : B.Val σ → B.D τ),
      (∀ x y, RV σ x y → R τ (f x) (f' y)) → R (σ ⇒ τ) (A.lam f) (B.lam f'))
    (hm : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) a a' b b', R σ₁ a a' → R σ₂ b b' →
      R τ (A.mode m a b) (B.mode m a' b'))
    {ty : Ty} (t : Term Γ K ty) {g : ∀ n, A.Val (Γ n)} {g' : ∀ n, B.Val (Γ n)}
    (hg : ∀ n, RV (Γ n) (g n) (g' n)) : R ty (t.realize A g) (t.realize B g') :=
  Rel.realize (Rc := fun _ c c' ↦ c = c') R RV (fun c _ h ↦ by subst h; exact hc c) hv hl hm
    (Rel.refl_eq t) hg

end Term

/-! ### The total and effectful interpretations -/

variable {E W : Type} {S : Sorts}

namespace Interpretation

variable {K : Ty → Type u}

/-- The effectful interpretation under an applicative effect that distributes over functions: a
term's value is a computation, an abstraction distributes the effect over the values of its
variable, and a composition runs its left daughter first. -/
def effectful {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) : Interpretation K where
  D ty := M (Ty.Domain E W ty S)
  Val ty := Ty.Domain E W ty S
  const := I
  var x := Pure.pure x
  lam f := distribute f
  mode m := m.evalM

/-- The total interpretation is the effectful interpretation under the identity effect: a constant
denotes what `I` gives it, a variable its value, an abstraction the function from the values of
its variable to its body's, and a composition what its mode makes of its daughters
([heim-kratzer-1998]). -/
abbrev total (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) : Interpretation K :=
  effectful (M := Id) I

/-- The call-by-value interpretation at a monad `M` ([moggi-1991]): a term's value is a computation
in `Ty.DomainM M`, a variable denotes a value, an abstraction the function from the values of its
variable to its body's computations, and a composition `Mode.evalKleisli`. Unlike `effectful`, it
needs no distributor, since a function returns computations. -/
def kleisli (M : Type → Type) [Monad M] [FlattenAlternatives M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.DomainM M E W ty S)) : Interpretation K where
  D ty := M (Ty.DomainM M E W ty S)
  Val ty := Ty.DomainM M E W ty S
  const := I
  var x := pure x
  lam f := pure f
  mode m := m.evalKleisli

end Interpretation

namespace Term

variable {Γ : ℕ → Ty} {K : Ty → Type u} {K' : Ty → Type u'}

open scoped Assignment

/-- The denotation of a term under an interpretation of the constants and an assignment of values
to the variables. -/
def eval (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : ∀ n, Ty.Domain E W (Γ n) S)
    {ty : Ty} (t : Term Γ K ty) : Ty.Domain E W ty S :=
  t.realize (.total I) g

section Eval

variable (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : ∀ n, Ty.Domain E W (Γ n) S)

@[simp] theorem eval_const {ty : Ty} (c : K ty) : (const c : Term Γ K ty).eval I g = I c :=
  rfl

/-- A variable denotes the value of its index under the assignment, by the Traces and Pronouns
Rule. -/
@[simp] theorem eval_var (n : ℕ) : (var n : Term Γ K (Γ n)).eval I g = g n :=
  rfl

/-- An abstraction denotes the function from the values of its variable to its body's value under
the assignment modified there, by Predicate Abstraction. -/
@[simp] theorem eval_lam (n : ℕ) {τ : Ty} (b : Term Γ K τ) :
    (lam n b).eval I g = fun x ↦ b.eval I (g[n ↦ x]) :=
  rfl

@[simp] theorem eval_comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term Γ K σ₁) (r : Term Γ K σ₂) :
    (comp m l r).eval I g = m.eval (l.eval I g) (r.eval I g) :=
  rfl

end Eval

theorem eval_map (I : ∀ {ty : Ty}, K' ty → Ty.Domain E W ty S) (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : ∀ n, Ty.Domain E W (Γ n) S) {ty : Ty} (t : Term Γ K ty) :
    (t.map f).eval I g = t.eval (fun c ↦ I (f c)) g :=
  realize_map (.total I) f g t

/-- Under the total interpretation every term denotes a value, so substitution needs only that no
binder captures. -/
theorem eval_subst {ty : Ty} {t : Term Γ K ty} {σ : ∀ n, Term Γ K (Γ n)} (ht : t.FreeFor σ)
    (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : ∀ n, Ty.Domain E W (Γ n) S) :
    (t.subst σ).eval I g = t.eval I fun n ↦ (σ n).eval I g :=
  realize_subst (.total I) ht fun _ _ ↦ rfl

/-- λ-conversion, [gallin-1975]'s axiom AS4 of Ty₂ (p. 60): under the total interpretation, a
function abstracted over `n` applied to `a` has the value of its body with `a` for `n`, where `a` is
free for `n` in the body. -/
theorem eval_beta {n : ℕ} {τ : Ty} {b : Term Γ K τ} {a : Term Γ K (Γ n)}
    (hb : b.FreeFor (Function.update (fun k ↦ var k) n a))
    (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : ∀ n, Ty.Domain E W (Γ n) S) :
    (comp .functionalLeft (lam n b) a).eval I g =
      (b.subst (Function.update (fun k ↦ var k) n a)).eval I g := by
  rw [eval_subst hb]
  refine congrArg (b.eval I) (funext fun k ↦ ?_)
  obtain rfl | hk := eq_or_ne k n
  · simp [eval]
  · simp [Function.update_of_ne hk]

/-- The denotation of a term under an applicative effect, given an interpretation `I` of the
constants as computations and an assignment of values to the variables. -/
def evalM {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : ∀ n, Ty.Domain E W (Γ n) S)
    {ty : Ty} (t : Term Γ K ty) : M (Ty.Domain E W ty S) :=
  t.realize (.effectful I) g

section Effect

variable {M : Type → Type} [Applicative M] [Distributive M]
  (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : ∀ n, Ty.Domain E W (Γ n) S)

@[simp] theorem evalM_const {ty : Ty} (c : K ty) : (const c : Term Γ K ty).evalM I g = I c :=
  rfl

@[simp] theorem evalM_var (n : ℕ) : (var n : Term Γ K (Γ n)).evalM I g = pure (g n) :=
  rfl

@[simp] theorem evalM_lam (n : ℕ) {τ : Ty} (b : Term Γ K τ) :
    (lam n b).evalM I g = distribute fun x ↦ b.evalM I (g[n ↦ x]) :=
  rfl

@[simp] theorem evalM_comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term Γ K σ₁)
    (r : Term Γ K σ₂) : (comp m l r).evalM I g = m.evalM (l.evalM I g) (r.evalM I g) :=
  rfl

end Effect

theorem evalM_map {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K' ty → M (Ty.Domain E W ty S)) (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : ∀ n, Ty.Domain E W (Γ n) S) {ty : Ty} (t : Term Γ K ty) :
    (t.map f).evalM I g = t.evalM (fun c ↦ I (f c)) g :=
  realize_map (.effectful I) f g t

/-- At the identity effect, evaluation is the pure denotation. -/
@[simp] theorem evalM_id (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S)
    (g : ∀ n, Ty.Domain E W (Γ n) S) {ty : Ty} (t : Term Γ K ty) :
    t.evalM (M := Id) I g = t.eval I g :=
  rfl

/-- A term whose constants are values of another's sets of values evaluates, under the set effect,
to a set containing the first term's denotation. -/
theorem Rel.mem_run_evalM {ty : Ty} {u : Term Γ (fun ty ↦ Id (Ty.Domain E W ty S)) ty}
    {u' : Term Γ (fun ty ↦ SetM (Ty.Domain E W ty S)) ty}
    (hu : Rel (fun _ c c' ↦ c ∈ SetM.run c') u u') (g : ∀ n, Ty.Domain E W (Γ n) S) :
    u.eval (fun c ↦ c) g ∈ (u'.evalM (fun c ↦ c) g).run :=
  hu.realize (A := .total fun c ↦ c) (B := .effectful (M := SetM) fun c ↦ c)
    (fun ty x (X : SetM (Ty.Domain E W ty S)) ↦ x ∈ SetM.run X) (fun _ ↦ (· = ·))
    (fun _ _ hc ↦ hc) (fun _ _ h ↦ by subst h; exact rfl)
    (fun _ _ h ↦ SetM.mem_run_distribute.2 fun x ↦ h x x rfl)
    (fun m a _ b _ ha hb ↦ ⟨m.eval a, ⟨a, ha, rfl⟩, b, hb, rfl⟩) fun _ ↦ rfl

/-- Under the set effect λ-conversion fails with no capture, since substituting copies a choice:
`(λx. x = x)(a)` has only the value true, while `a = a` has both truth values when `a` has two
alternatives. So `realize_subst` asks that a replacement denote a value. -/
theorem exists_evalM_comp_lam_ne_subst :
    ∃ (a : Term individualIndices (fun ty ↦ SetM (Ty.Domain Bool Unit ty)) .e)
      (b : Term individualIndices (fun ty ↦ SetM (Ty.Domain Bool Unit ty)) .t),
      b.FreeFor (Function.update (fun k ↦ var k) 0 a) ∧
        (comp .functionalLeft (lam 0 b) a).evalM (fun c ↦ c) (fun _ ↦ true) ≠
          (b.subst (Function.update (fun k ↦ var k) 0 a)).evalM (fun c ↦ c) (fun _ ↦ true) := by
  refine ⟨const (Set.univ : Set Bool), comp .functionalLeft (comp .functionalLeft
    (const (pure fun x y : Bool ↦ x = y)) (var 0)) (var 0), by simp [FreeFor], ?_⟩
  intro h
  have hr := congrArg (False ∈ SetM.run ·) h
  simp only [subst, Function.update_self, evalM, realize, Interpretation.effectful, Mode.evalM,
    map_pure, seq_pure, Mode.eval, eq_iff_iff] at hr
  obtain ⟨_, ⟨F, hF, rfl⟩, x, -, hx⟩ :=
    hr.2 ⟨_, ⟨_, ⟨_, rfl, true, trivial, rfl⟩, rfl⟩, false, trivial, by simp⟩
  have hFx : F x = True := SetM.mem_run_distribute.1 hF x
  simp [hFx] at hx

end Term

end Montague
