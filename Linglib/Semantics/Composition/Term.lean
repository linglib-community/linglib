module

public import Linglib.Core.Control.Distributive
public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Composition.Assignment

/-!
# Logical forms as terms

A logical form is a term, built from the constants its words translate to, variables for the
individuals its traces denote, abstraction, and composition by a mode. A term has a value in any
*interpretation*, which fixes a domain at each type and how constants, variables, abstraction and
the modes are interpreted, and the values of related terms in two interpretations are related
[whenever the relation holds of the constants and variables and survives abstraction and every
mode](##Rel.realize). Heim and Kratzer's total semantics, von Fintel and Heim's semantics relative
to a world, and composition under an effect are interpretations, and the total denotation is
[the case of the intension where no word varies with the world](##intension_const_interp).

## Main definitions

* `Montague.Term`: the terms over a signature of constants.
* `Montague.Interpretation`: an interpretation of the terms.
* `Montague.Term.realize`: the value of a term in an interpretation under an assignment.
* `Montague.Interpretation.total`, `Montague.Interpretation.intensional`,
  `Montague.Interpretation.effectful`: the total, intensional and effectful interpretations.
* `Montague.Term.eval`, `Montague.Term.intension`, `Montague.Term.evalM`: the values in them.

## Implementation notes

The structure follows mathlib's `FirstOrder.Language.Term.realize`, defined once over any
`L.Structure`: each semantics is an interpretation rather than its own evaluator, and the lemma
relating two of them is the fundamental lemma of logical relations. Variables are named by the
trace indices, so a binder with index `n` translates to the
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

end Term

/-! ### Interpretations -/

universe u' v w v' w'

/-- An interpretation of the terms over a signature `K`: a domain at each type, what a variable
denotes, and how constants, variables, abstractions and compositions are interpreted. -/
structure Interpretation (K : Ty → Type u) where
  /-- The domain of each type. -/
  D : Ty → Type v
  /-- What a variable denotes. -/
  Var : Type w
  /-- The value of each constant. -/
  const : ∀ {ty : Ty}, K ty → D ty
  /-- The value of a variable, from what it denotes. -/
  var : Var → D .e
  /-- The value of an abstraction, from its body as a function of what the bound variable
  denotes. -/
  lam : ∀ {τ : Ty}, (Var → D τ) → D (.e ⇒ τ)
  /-- The value of a composition, from its daughters' values. -/
  mode : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → D σ₁ → D σ₂ → D τ

namespace Interpretation

variable {K : Ty → Type u} {K' : Ty → Type u'}

/-- The interpretation of the terms over `K` that interprets a constant as `A` interprets its image
under `f`. -/
def comap (A : Interpretation.{u', v, w} K') (f : ∀ {ty : Ty}, K ty → K' ty) :
    Interpretation.{u, v, w} K where
  D := A.D
  Var := A.Var
  const c := A.const (f c)
  var := A.var
  lam := A.lam
  mode := A.mode

end Interpretation

namespace Term

variable {K : Ty → Type u} {K' : Ty → Type u'}

/-- The value of a term in an interpretation under an assignment of its variables. -/
def realize (A : Interpretation.{u, v, w} K) (g : ℕ → A.Var) : {ty : Ty} → Term K ty → A.D ty
  | _, const c => A.const c
  | _, var n => A.var (g n)
  | _, lam n b => A.lam fun x ↦ realize A (Function.update g n x) b
  | _, comp m l r => A.mode m (realize A g l) (realize A g r)

section Realize

variable (A : Interpretation.{u, v, w} K) (g : ℕ → A.Var)

@[simp] theorem realize_const {ty : Ty} (c : K ty) : (const c).realize A g = A.const c := rfl

@[simp] theorem realize_var (n : ℕ) : (var n : Term K .e).realize A g = A.var (g n) := rfl

@[simp] theorem realize_lam {τ : Ty} (n : ℕ) (b : Term K τ) :
    (lam n b).realize A g = A.lam fun x ↦ b.realize A (Function.update g n x) := rfl

@[simp] theorem realize_comp {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term K σ₁) (r : Term K σ₂) :
    (comp m l r).realize A g = A.mode m (l.realize A g) (r.realize A g) := rfl

/-- A term's value depends on the assignment only at its free variables. -/
theorem realize_congr_of_agree {ty : Ty} (t : Term K ty) {g g' : ℕ → A.Var}
    (h : ∀ n ∈ t.freeVars, g n = g' n) : t.realize A g = t.realize A g' := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => exact congrArg A.var (h n (Finset.mem_singleton_self n))
  | lam n b ih =>
    refine congrArg A.lam (funext fun x ↦ ih fun m hm ↦ ?_)
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [Function.update_of_ne hmn, h m (Finset.mem_erase.2 ⟨hmn, hm⟩)]
  | comp m l r ihl ihr =>
    simp only [freeVars, Finset.mem_union] at h
    exact congrArg₂ (A.mode m) (ihl fun n hn ↦ h n (.inl hn)) (ihr fun n hn ↦ h n (.inr hn))

end Realize

theorem realize_map (A : Interpretation.{u', v, w} K') (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : ℕ → A.Var) {ty : Ty} (t : Term K ty) :
    (t.map f).realize A g = t.realize (A.comap f) g := by
  induction t generalizing g with
  | const c => rfl
  | var n => rfl
  | lam n b ih => exact congrArg A.lam (funext fun x ↦ ih _)
  | comp m l r ihl ihr => exact congrArg₂ (A.mode m) (ihl g) (ihr g)

/-- The fundamental lemma of logical relations: a relation between the values of two
interpretations that holds of the constants the terms relate and of the variables the assignments
relate, and that abstraction and every mode preserve, holds of the values of two related terms. -/
theorem Rel.realize {Rc : ∀ ty : Ty, K ty → K' ty → Prop} {A : Interpretation.{u, v, w} K}
    {B : Interpretation.{u', v', w'} K'} (R : ∀ ty : Ty, A.D ty → B.D ty → Prop)
    (RV : A.Var → B.Var → Prop)
    (hc : ∀ {ty : Ty} (c : K ty) (c' : K' ty), Rc ty c c' → R ty (A.const c) (B.const c'))
    (hv : ∀ x y, RV x y → R .e (A.var x) (B.var y))
    (hl : ∀ {τ : Ty} (f : A.Var → A.D τ) (f' : B.Var → B.D τ),
      (∀ x y, RV x y → R τ (f x) (f' y)) → R (.e ⇒ τ) (A.lam f) (B.lam f'))
    (hm : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) a a' b b', R σ₁ a a' → R σ₂ b b' →
      R τ (A.mode m a b) (B.mode m a' b'))
    {ty : Ty} {t : Term K ty} {t' : Term K' ty} (ht : Rel Rc t t') {g : ℕ → A.Var}
    {g' : ℕ → B.Var} (hg : ∀ n, RV (g n) (g' n)) : R ty (t.realize A g) (t'.realize B g') := by
  induction ht generalizing g g' with
  | const h => exact hc _ _ h
  | var n => exact hv _ _ (hg n)
  | lam n _ ih =>
    refine hl _ _ fun x y hxy ↦ ih fun m ↦ ?_
    by_cases hmn : m = n
    · subst hmn; simpa using hxy
    · simpa [Function.update_of_ne hmn] using hg m
  | comp m _ _ ihl ihr => exact hm m _ _ _ _ (ihl hg) (ihr hg)

/-- Every term is related to itself when equal constants are. -/
theorem Rel.refl_eq {ty : Ty} (t : Term K ty) : Rel (fun _ c c' ↦ c = c') t t := by
  induction t with
  | const c => exact .const rfl
  | var n => exact .var n
  | lam n b ih => exact .lam n ih
  | comp m l r ihl ihr => exact .comp m ihl ihr

/-- The fundamental lemma for one term in two interpretations. -/
theorem realize_rel {A : Interpretation.{u, v, w} K} {B : Interpretation.{u, v', w'} K}
    (R : ∀ ty : Ty, A.D ty → B.D ty → Prop) (RV : A.Var → B.Var → Prop)
    (hc : ∀ {ty : Ty} (c : K ty), R ty (A.const c) (B.const c))
    (hv : ∀ x y, RV x y → R .e (A.var x) (B.var y))
    (hl : ∀ {τ : Ty} (f : A.Var → A.D τ) (f' : B.Var → B.D τ),
      (∀ x y, RV x y → R τ (f x) (f' y)) → R (.e ⇒ τ) (A.lam f) (B.lam f'))
    (hm : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) a a' b b', R σ₁ a a' → R σ₂ b b' →
      R τ (A.mode m a b) (B.mode m a' b'))
    {ty : Ty} (t : Term K ty) {g : ℕ → A.Var} {g' : ℕ → B.Var} (hg : ∀ n, RV (g n) (g' n)) :
    R ty (t.realize A g) (t.realize B g') :=
  Rel.realize (Rc := fun _ c c' ↦ c = c') R RV (fun c _ h ↦ by subst h; exact hc c) hv hl hm
    (Rel.refl_eq t) hg

end Term

/-! ### The total, intensional and effectful interpretations -/

variable {E W : Type} {S : Sorts}

namespace Interpretation

variable {K : Ty → Type u}

/-- The total interpretation: a constant denotes what `I` gives it, a variable its value, an
abstraction the function from the values of its variable to its body's, and a composition what its
mode makes of its daughters ([heim-kratzer-1998]). -/
def total (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) : Interpretation K where
  D ty := Ty.Domain E W ty S
  Var := E
  const := I
  var := id
  lam f := f
  mode m := m.eval

/-- The intensional interpretation: a term's value is its intension, its denotation at every
world, a constant's that `I` gives it, and a composition composes its daughters' intensions by its
mode, intensional application giving the function its argument's whole intension
([von-fintel-heim-2011]). -/
def intensional (I : ∀ {ty : Ty}, K ty → W → Ty.Domain E W ty S) : Interpretation K where
  D ty := W → Ty.Domain E W ty S
  Var := E
  const := I
  var x := fun _ ↦ x
  lam f := fun w x ↦ f x w
  mode m := m.intension

/-- The effectful interpretation under an applicative effect that distributes over functions: a
term's value is a computation, an abstraction distributes the effect over the values of its
variable, and a composition runs its left daughter first. -/
def effectful {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) : Interpretation K where
  D ty := M (Ty.Domain E W ty S)
  Var := E
  const := I
  var x := Pure.pure x
  lam f := distribute f
  mode m := m.evalM

end Interpretation

namespace Term

variable {K : Ty → Type u} {K' : Ty → Type u'}

open scoped Assignment

/-- The denotation of a term under an interpretation of the constants and an assignment of the
variables. -/
def eval (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E) {ty : Ty}
    (t : Term K ty) : Ty.Domain E W ty S :=
  t.realize (.total I) g

@[simp] theorem eval_const (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E)
    {ty : Ty} (c : K ty) : (const c).eval I g = I c :=
  rfl

/-- A variable denotes the value of its index under the assignment, by the Traces and Pronouns
Rule. -/
@[simp] theorem eval_var (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E) (n : ℕ) :
    (var n : Term K .e).eval I g = g n :=
  rfl

/-- An abstraction denotes the abstraction of its body over its variable, by Predicate
Abstraction. -/
theorem eval_lam (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E) (n : ℕ)
    {τ : Ty} (b : Term K τ) : (lam n b).eval I g = lambdaAbsG n (fun g' ↦ b.eval I g') g :=
  rfl

@[simp] theorem eval_comp (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E)
    {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term K σ₁) (r : Term K σ₂) :
    (comp m l r).eval I g = m.eval (l.eval I g) (r.eval I g) :=
  rfl

theorem eval_map (I : ∀ {ty : Ty}, K' ty → Ty.Domain E W ty S) (f : ∀ {ty : Ty}, K ty → K' ty)
    (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).eval I g = t.eval (fun c ↦ I (f c)) g :=
  realize_map (.total I) f g t

/-- The intension of a term under an interpretation `I` of the constants as intensions and an
assignment of the variables, its denotation at every world. -/
def intension (I : ∀ {ty : Ty}, K ty → W → Ty.Domain E W ty S) (g : Assignment E) {ty : Ty}
    (t : Term K ty) : W → Ty.Domain E W ty S :=
  t.realize (.intensional I) g

@[simp] theorem intension_comp (I : ∀ {ty : Ty}, K ty → W → Ty.Domain E W ty S)
    (g : Assignment E) {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term K σ₁) (r : Term K σ₂) :
    (comp m l r).intension I g = m.intension (l.intension I g) (r.intension I g) :=
  rfl

theorem intension_map (I : ∀ {ty : Ty}, K' ty → W → Ty.Domain E W ty S)
    (f : ∀ {ty : Ty}, K ty → K' ty) (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).intension I g = t.intension (fun c ↦ I (f c)) g :=
  realize_map (.intensional I) f g t

/-- Under constants that do not vary with the world, a term's intension is constant at its
denotation, so the evaluation `eval` is the case of a lexicon of rigid intensions. -/
@[simp] theorem intension_const_interp (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S)
    (g : Assignment E) {ty : Ty} (t : Term K ty) (w : W) :
    t.intension (fun c _ ↦ I c) g w = t.eval I g :=
  congrFun (realize_rel (A := .intensional fun c _ ↦ I c) (B := .total I)
    (fun _ f x ↦ f = fun _ ↦ x) (· = ·) (fun _ ↦ rfl) (fun _ _ h ↦ by subst h; rfl)
    (fun _ _ h ↦ funext fun _ ↦ funext fun x ↦ congrFun (h x x rfl) _)
    (fun m _ a' _ b' ha hb ↦ by subst ha hb; funext w; exact Mode.intension_const m a' b' w)
    t fun _ ↦ rfl) w

/-- The denotation of a term under an applicative effect, given an interpretation `I` of the
constants as computations and an assignment `g`. -/
def evalM {M : Type → Type} [Applicative M] [Distributive M]
    (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : Assignment E) {ty : Ty}
    (t : Term K ty) : M (Ty.Domain E W ty S) :=
  t.realize (.effectful I) g

section Effect

variable {M : Type → Type} [Applicative M] [Distributive M]

@[simp] theorem evalM_const (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : Assignment E)
    {ty : Ty} (c : K ty) : (const c).evalM I g = I c :=
  rfl

@[simp] theorem evalM_var (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : Assignment E)
    (n : ℕ) : (var n : Term K .e).evalM I g = pure (g n) :=
  rfl

@[simp] theorem evalM_lam (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : Assignment E)
    (n : ℕ) {τ : Ty} (b : Term K τ) :
    (lam n b).evalM I g = distribute fun x ↦ b.evalM I (g[n ↦ x]) :=
  rfl

@[simp] theorem evalM_comp (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) (g : Assignment E)
    {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term K σ₁) (r : Term K σ₂) :
    (comp m l r).evalM I g = m.evalM (l.evalM I g) (r.evalM I g) :=
  rfl

theorem evalM_map (I : ∀ {ty : Ty}, K' ty → M (Ty.Domain E W ty S))
    (f : ∀ {ty : Ty}, K ty → K' ty) (g : Assignment E) {ty : Ty} (t : Term K ty) :
    (t.map f).evalM I g = t.evalM (fun c ↦ I (f c)) g :=
  realize_map (.effectful I) f g t

/-- A term's denotation depends on the assignment only at its free variables. -/
theorem evalM_congr_of_agree (I : ∀ {ty : Ty}, K ty → M (Ty.Domain E W ty S)) {ty : Ty}
    (t : Term K ty) {g g' : Assignment E} (h : ∀ n ∈ t.freeVars, g n = g' n) :
    t.evalM I g = t.evalM I g' :=
  realize_congr_of_agree _ t h

end Effect

/-- At the identity effect, evaluation is the pure denotation. -/
@[simp] theorem evalM_id (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S) (g : Assignment E)
    {ty : Ty} (t : Term K ty) : t.evalM (M := Id) I g = t.eval I g :=
  realize_rel (A := .effectful (M := Id) I) (B := .total I) (fun _ ↦ (· = ·)) (· = ·)
    (fun _ ↦ rfl) (fun _ _ h ↦ by subst h; rfl) (fun _ _ h ↦ funext fun x ↦ h x x rfl)
    (fun _ _ _ _ _ ha hb ↦ by subst ha hb; rfl) t fun _ ↦ rfl

/-- A term whose constants are values of another's sets of values evaluates, under the set effect,
to a set containing the first term's denotation. -/
theorem Rel.mem_run_evalM {ty : Ty} {u : Term (fun ty ↦ Id (Ty.Domain E W ty S)) ty}
    {u' : Term (fun ty ↦ SetM (Ty.Domain E W ty S)) ty}
    (h : Rel (fun _ c c' ↦ c ∈ SetM.run c') u u') (g : Assignment E) :
    u.eval (fun c ↦ c) g ∈ (u'.evalM (fun c ↦ c) g).run :=
  h.realize (A := .total fun c ↦ c) (B := .effectful (M := SetM) fun c ↦ c)
    (fun ty x (X : SetM (Ty.Domain E W ty S)) ↦ x ∈ SetM.run X) (· = ·) (fun _ _ hc ↦ hc)
    (fun _ _ h ↦ by subst h; exact rfl)
    (fun _ _ h ↦ SetM.mem_run_distribute.2 fun x ↦ h x x rfl)
    (fun m a _ b _ ha hb ↦ ⟨m.eval a, ⟨a, ha, rfl⟩, b, hb, rfl⟩) fun _ ↦ rfl

end Term

end Montague
