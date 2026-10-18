module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Composition.Assignment

/-!
# Terms of the composition modes

A tree that the composition modes interpret has a logical form: the term recording the constants
its words translate to, the variables its traces bind, and the mode by which each binary node
composes its daughters (`HeimKratzer.Term`, `HeimKratzer.Tree.translate`). Translation is the one
type-driven step: a terminal translates to its word's constant, a binary node to the composition
of its daughters' terms by the mode their types select, a trace to the variable of its index,
and a binder to the abstraction over that variable.

Every interpretation of the trees is an evaluation of their terms: the denotation, under an
assignment of the variables (`HeimKratzer.Term.eval`); the denotation under an applicative
effect, where abstraction needs the effect's distributor (`HeimKratzer.Term.evalM`); and the
partial denotation of `Composition/Partial.lean`. Each is defined by recursion on terms, once for
all trees.

## Main definitions

* `HeimKratzer.Term`: the terms over a signature of constants.
* `HeimKratzer.Term.eval`, `HeimKratzer.Term.evalM`: the denotation of a term, pure and under an
  applicative effect.
* `HeimKratzer.PredAbs`: the distributor an effect needs for abstraction.
* `HeimKratzer.Tree.translate`: the term a tree translates to.

## Main results

* `HeimKratzer.Term.evalM_id`: at the identity effect, evaluation is the pure denotation.
* `HeimKratzer.Term.evalM_congr_of_agree`: a term's denotation depends on the assignment only at
  its free variables.
* `HeimKratzer.Tree.translate_map_const`: translation commutes with renaming the constants.
* `HeimKratzer.Tree.freeVars_subset`: the free variables of a tree's term are its free traces.

## Implementation notes

Variables are named by the trace indices, so a binder with index `n` translates to the
abstraction over the variable `n`, and translation needs no fresh names.

## References

* [heim-kratzer-1998]
* [montague-1973]
-/

@[expose] public section

universe u

namespace HeimKratzer

open Montague

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

/-! ### Translation -/

namespace Tree

open PhraseStructure

variable {C : Type} {K : Ty → Type*} {L : Type*}

/-- `translate lex t` is the term the tree `t` translates to by the composition principles of
[heim-kratzer-1998]. A terminal translates to its word's constant, a non-branching node to its
daughter's term, a binary node to the composition of its daughters' terms by the mode their types
select, a trace to the variable of its index, and a binder to the abstraction over that variable. -/
def translate (lex : L → Option (Σ ty, K ty)) : Tree C L → Option (Σ ty, Term K ty)
  | .terminal _ w => (lex w).map fun c ↦ ⟨c.1, .const c.2⟩
  | .node _ (t :: []) => translate lex t
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← translate lex t1
    let d2 ← translate lex t2
    Mode.combine? (fun m l r ↦ .comp m l r) d1 d2
  | .node _ _ => none
  | .adjoin _ (t :: []) => translate lex t
  | .adjoin _ (t1 :: t2 :: []) => do
    let d1 ← translate lex t1
    let d2 ← translate lex t2
    Mode.combine? (fun m l r ↦ .comp m l r) d1 d2
  | .adjoin _ _ => none
  | .trace n _ => some ⟨.e, .var n⟩
  | .bind n _ body => (translate lex body).map fun d ↦ ⟨.e ⇒ d.1, .lam n d.2⟩
  | _ => none

variable (lex : L → Option (Σ ty, K ty))

@[simp] theorem translate_terminal (c : C) (w : L) :
    translate lex (.terminal c w : Tree C L) = (lex w).map fun c ↦ ⟨c.1, .const c.2⟩ := rfl

@[simp] theorem translate_node_unary (c : C) (t : Tree C L) :
    translate lex (.node c (t :: [])) = translate lex t := rfl

@[simp] theorem translate_node_binary (c : C) (t₁ t₂ : Tree C L) :
    translate lex (.node c (t₁ :: t₂ :: [])) = ((translate lex t₁).bind fun d₁ ↦
      (translate lex t₂).bind fun d₂ ↦ Mode.combine? (fun m l r ↦ .comp m l r) d₁ d₂) := rfl

@[simp] theorem translate_adjoin_unary (c : C) (t : Tree C L) :
    translate lex (.adjoin c (t :: [])) = translate lex t := rfl

@[simp] theorem translate_adjoin_binary (c : C) (t₁ t₂ : Tree C L) :
    translate lex (.adjoin c (t₁ :: t₂ :: [])) = ((translate lex t₁).bind fun d₁ ↦
      (translate lex t₂).bind fun d₂ ↦ Mode.combine? (fun m l r ↦ .comp m l r) d₁ d₂) := rfl

@[simp] theorem translate_trace (n : ℕ) (c : C) :
    translate lex (.trace n c : Tree C L) = some ⟨.e, .var n⟩ := rfl

@[simp] theorem translate_bind (n : ℕ) (c : C) (body : Tree C L) :
    translate lex (.bind n c body) =
      (translate lex body).map fun d ↦ ⟨.e ⇒ d.1, .lam n d.2⟩ := rfl

/-- A node whose daughters its label does not license translates to nothing. -/
theorem translate_junk {l : Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ Tree.Label.Licenses l (cs.map RoseTree.value)) :
    translate lex (RoseTree.node l cs) = none := by
  cases l with
  | terminal c w => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | node c => exact absurd trivial h
  | segment c => exact absurd trivial h
  | trace n c => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | bind n c =>
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩
    · rfl
    · exact absurd rfl h
    · rfl


/-- Translation commutes with renaming the constants. -/
theorem translate_map_const {K' : Ty → Type*} (f : ∀ {ty : Ty}, K ty → K' ty) (t : Tree C L) :
    translate (fun w ↦ (lex w).map fun c ↦ ⟨c.1, f c.2⟩) t =
      (translate lex t).map fun d ↦ ⟨d.1, d.2.map f⟩ := by
  induction t using Tree.rec' with
  | terminal c w => simp only [translate_terminal]; cases lex w <;> rfl
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp)
    | [t₁, t₂] =>
      simp only [translate_node_binary, ih t₁ (by simp), ih t₂ (by simp)]
      cases translate lex t₁ <;> cases translate lex t₂ <;> try rfl
      exact (Mode.combine?_map (fun _ _ _ ↦ rfl) _ _).symm
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp)
    | [t₁, t₂] =>
      simp only [translate_adjoin_binary, ih t₁ (by simp), ih t₂ (by simp)]
      cases translate lex t₁ <;> cases translate lex t₂ <;> try rfl
      exact (Mode.combine?_map (fun _ _ _ ↦ rfl) _ _).symm
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih => simp only [translate_bind, ih, Option.map_map]; rfl
  | junk l cs hj _ => rw [translate_junk _ hj, translate_junk _ hj]; rfl


private theorem bind_combine?_map_fst {K' : Ty → Type*}
    {op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → Term K σ₁ → Term K σ₂ → Term K τ}
    {op' : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → Term K' σ₁ → Term K' σ₂ → Term K' τ}
    {o₁ o₂ : Option (Σ ty, Term K ty)} {o₁' o₂' : Option (Σ ty, Term K' ty)}
    (h₁ : o₁.map (·.1) = o₁'.map (·.1)) (h₂ : o₂.map (·.1) = o₂'.map (·.1)) :
    (o₁.bind fun a ↦ o₂.bind fun b ↦ Mode.combine? op a b).map (·.1) =
      (o₁'.bind fun a ↦ o₂'.bind fun b ↦ Mode.combine? op' a b).map (·.1) := by
  rcases o₁ with _ | ⟨σ₁, u₁⟩ <;> rcases o₁' with _ | ⟨σ₁', u₁'⟩ <;> simp at h₁ ⊢
  subst h₁
  rcases o₂ with _ | ⟨σ₂, u₂⟩ <;> rcases o₂' with _ | ⟨σ₂', u₂'⟩ <;> simp at h₂ ⊢
  subst h₂
  simp

/-- The types of a tree's term depend only on the types of its words' constants. -/
theorem translate_map_fst {K' : Ty → Type*} {lex' : L → Option (Σ ty, K' ty)}
    (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    (translate lex t).map (·.1) = (translate lex' t).map (·.1) := by
  induction t using Tree.rec' with
  | terminal c w => simpa [Option.map_map, Function.comp_def] using h w
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp)
    | [t₁, t₂] =>
      simp only [translate_node_binary]
      exact bind_combine?_map_fst (ih t₁ (by simp)) (ih t₂ (by simp))
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp)
    | [t₁, t₂] =>
      simp only [translate_adjoin_binary]
      exact bind_combine?_map_fst (ih t₁ (by simp)) (ih t₂ (by simp))
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    simp only [translate_bind, Option.map_map]
    revert ih
    cases translate lex body <;> cases translate lex' body <;> simp_all
  | junk l cs hj _ => rw [translate_junk _ hj, translate_junk _ hj]; rfl

/-- Lexicons whose constants are related translate a tree to terms of the same shape with
related constants. -/
theorem translate_rel {K' : Ty → Type*} {R : ∀ ty : Ty, K ty → K' ty → Prop}
    {lex' : L → Option (Σ ty, K' ty)}
    (hlex : ∀ w d', lex' w = some d' → ∃ c, lex w = some ⟨d'.1, c⟩ ∧ R d'.1 c d'.2)
    (t : Tree C L) :
    ∀ {d'}, translate lex' t = some d' →
      ∃ u, translate lex t = some ⟨d'.1, u⟩ ∧ Term.Rel R u d'.2 := by
  induction t using Tree.rec' with
  | terminal c w =>
    intro d' h
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨c', hc', hR⟩ := hlex w d hd
    exact ⟨.const c', by simp [hc'], .const hR⟩
  | node c cs ih =>
    match cs with
    | [] => intro d' h; simp [translate] at h
    | [t] => intro d' h; exact ih t (by simp) h
    | [t₁, t₂] =>
      intro d' h
      simp only [translate_node_binary, Option.bind_eq_some_iff] at h
      obtain ⟨⟨σ₁, u₁'⟩, h₁, ⟨σ₂, u₂'⟩, h₂, h⟩ := h
      obtain ⟨u₁, hu₁, hr₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨u₂, hu₂, hr₂⟩ := ih t₂ (by simp) h₂
      simp only [Mode.combine?, Option.map_eq_some_iff] at h
      obtain ⟨⟨τ, m⟩, hm, rfl⟩ := h
      exact ⟨.comp m u₁ u₂, by simp [translate_node_binary, hu₁, hu₂, Mode.combine?, hm],
        .comp m hr₁ hr₂⟩
    | _ :: _ :: _ :: _ => intro d' h; simp [translate] at h
  | adjoin c cs ih =>
    match cs with
    | [] => intro d' h; simp [translate] at h
    | [t] => intro d' h; exact ih t (by simp) h
    | [t₁, t₂] =>
      intro d' h
      simp only [translate_adjoin_binary, Option.bind_eq_some_iff] at h
      obtain ⟨⟨σ₁, u₁'⟩, h₁, ⟨σ₂, u₂'⟩, h₂, h⟩ := h
      obtain ⟨u₁, hu₁, hr₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨u₂, hu₂, hr₂⟩ := ih t₂ (by simp) h₂
      simp only [Mode.combine?, Option.map_eq_some_iff] at h
      obtain ⟨⟨τ, m⟩, hm, rfl⟩ := h
      exact ⟨.comp m u₁ u₂, by simp [translate_adjoin_binary, hu₁, hu₂, Mode.combine?, hm],
        .comp m hr₁ hr₂⟩
    | _ :: _ :: _ :: _ => intro d' h; simp [translate] at h
  | trace n c =>
    intro d' h
    obtain rfl := Option.some.inj h.symm
    exact ⟨.var n, rfl, .var n⟩
  | bind n c body ih =>
    intro d' h
    obtain ⟨⟨τ, b'⟩, hb, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨b, hb', hr⟩ := ih hb
    exact ⟨.lam n b, by simp [hb'], .lam n hr⟩
  | junk l cs hj _ => intro d' h; rw [translate_junk _ hj] at h; exact absurd h (by simp)

end Tree

end HeimKratzer
