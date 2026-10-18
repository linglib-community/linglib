module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Composition.Term

/-!
# Type-driven interpretation

This file interprets phrase-structure trees by Heim and Kratzer's type-driven composition, with
the intensional application of von Fintel and Heim and the event identification of Kratzer,
parameterized over an effect functor `M` in the style of Bumford and Charlow. A tree translates
to a term of the composition modes (`PhraseStructure.Tree.translate`): a terminal to its word's
constant, a binary node to the composition of its daughters' terms by the mode their types
select, a trace to the variable of its index, and a binder to the abstraction over it. Its
denotation is the evaluation of that term (`PhraseStructure.Tree.interp`), so a tree is
interpreted by translation followed by the interpretation of the terms, as in Montague's theory
of translation. Translation is the one type-driven step, and Predicate Abstraction is a capability
of the effect (`PredAbs`) rather than a given.

## Main definitions

* `Montague.Lexicon`: a string-keyed lexicon of effectful denotations.
* `PhraseStructure.Tree.translate`: the term a tree translates to.
* `PhraseStructure.Tree.interp`: the denotation of a tree under an assignment, the evaluation of
  its term; a binary node composes by the mode `Montague.Ty.mode?` selects.
* `PhraseStructure.Tree.ty?`: the type a tree composes to, from the types of its leaves alone.
* `PhraseStructure.Tree.readings`: the readings of a tree under a lexicon of sets of readings.
* `PhraseStructure.Tree.HoldsAt`: the truth of a tree under a lexicon and an assignment.

## Main results

* `PhraseStructure.Tree.interp_eq_eval_translate`: the pure engine is the denotation of the
  tree's term.
* `PhraseStructure.Tree.interp_map_fst`: the type of a tree's denotation is the type `ty?`
  computes.
* `PhraseStructure.Tree.interp_congr_of_agree` and its corollaries: Heim and Kratzer's theorems
  on variable binding, that a tree's denotation depends on the assignment only at its free traces.
* `PhraseStructure.Tree.readings_eq_of_choice`, `PhraseStructure.Tree.mem_readings_node_binary`:
  the engine on an unambiguous lexicon is a case of `readings`, and a binary node's readings
  compose pointwise.
* `PhraseStructure.Tree.translate_map_const`, `PhraseStructure.Tree.translate_rel`: translation
  commutes with renaming the constants and carries related lexicons to related terms.

## Implementation notes

The tree operations live in the namespace of `PhraseStructure.Tree`, as mathlib's `Term.realize`
lives in that of `Term`, so that `t.interp lex g` works. Binary nodes sequence effects in linear
order, the left daughter's first whichever daughter is the function, so at `M = Cont R` surface
scope is the default reading and inverse scope needs a reordered evaluation
(`Composition/Cont.lean`). Predicate Abstraction needs a distributor
`(E → M (Ty.Domain ty)) → M (E → Ty.Domain ty)`, which scope effects lack, so under them `.bind`
nodes fail and binding comes from the order of effects instead. The abstraction's fallback value
`valueAt` is never reached, since types do not depend on the assignment. The category parameter
of a tree is ignored, composition being type-driven.

## References

* [montague-1970], §5
* [heim-kratzer-1998]
* [von-fintel-heim-2011]
* [kratzer-1996]
* [bumford-charlow-2026]
-/

@[expose] public section

namespace Montague

open scoped Assignment

/-- A lexicon looks up a string's `M`-effectful denotation, if it has one. -/
abbrev Lexicon (E W : Type) (M : Type → Type := Id) (S : Sorts := {}) :=
  String → Option (Denotation E W M S)

/-! The pure engine computes in `Id`, whose applicative operations are application. The lemmas
are `simp` lemmas in this namespace only, since they identify `Id α` with `α`. -/

@[scoped simp] theorem seq_eq_apply {α β : Type} (f : Id (α → β)) (x : Id α) : f <*> x = f x :=
  rfl

@[scoped simp] theorem map_eq_apply {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl

@[scoped simp] theorem pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- The value of an interpreted daughter at the type `τ`, with the default `v` where the
daughter is uninterpretable or of another type. Types do not depend on the assignment
(`interp_map_fst_congr`), so under Predicate Abstraction the default is never reached
(`valueAt_of_map_fst`). -/
def valueAt {E W : Type} {S : Sorts} {M : Type → Type} (τ : Ty) (v : M (Ty.Domain E W τ S)) :
    Option (Denotation E W M S) → M (Ty.Domain E W τ S)
  | some ⟨ty, val⟩ => if h : ty = τ then h ▸ val else v
  | none => v

@[simp] theorem valueAt_some {E W : Type} {S : Sorts} {M : Type → Type} {τ : Ty}
    (v x : M (Ty.Domain E W τ S)) :
    valueAt τ v (some ⟨τ, x⟩ : Option (Denotation E W M S)) = x := by
  simp [valueAt]

theorem valueAt_of_map_fst {E W : Type} {S : Sorts} {M : Type → Type} {τ : Ty}
    {v v' : M (Ty.Domain E W τ S)} {d : Option (Denotation E W M S)}
    (h : d.map (·.1) = some τ) : valueAt τ v d = valueAt τ v' d := by
  obtain _ | ⟨ty, val⟩ := d
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h; simp [valueAt]

/-- The denotation of a term whose constants are denotations, at its type. -/
abbrev evalAt {E W : Type} {M : Type → Type} [Applicative M] {S : Sorts} [PredAbs M E W S]
    (g : Assignment E) (d : Σ ty, Term (fun ty ↦ M (Ty.Domain E W ty S)) ty) :
    Option (Denotation E W M S) :=
  (d.2.evalM (fun c ↦ c) g).map fun v ↦ ⟨d.1, v⟩

end Montague

namespace PhraseStructure.Tree

open Montague
open scoped Assignment

/-! ### Translation -/

section Translate

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

end Translate

/-! ### Tree interpretation -/

section TreeInterp

variable {C : Type}

/-- In the denotation of a tree under an assignment, by the composition principles of
[heim-kratzer-1998], a terminal denotes what its leaf interpretation gives it, a non-branching
node what its daughter does, a binary node what the mode its daughters' types select composes, a
trace the value of its index, and a binder the abstraction over its index, when the effect has a
distributor. It is the denotation of the tree's term, each word's denotation its constant. -/
def interp {E W : Type} {M : Type → Type} [Applicative M] {S : Sorts} [PredAbs M E W S]
    {L : Type*} (lex : L → Option (Denotation E W M S)) (g : Assignment E) (t : Tree C L) :
    Option (Denotation E W M S) :=
  (translate (K := fun ty ↦ M (Ty.Domain E W ty S)) lex t).bind (evalAt g)

end TreeInterp

/-! ### Reduction lemmas

One `@[simp]` lemma per constructor, so that a derivation reduces by `simp` toward its
composed denotation. -/

section Reduction

variable {C : Type} {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M] [PredAbs M E W S]
  {L : Type*}

private theorem bind_evalAt_combine (g : Assignment E)
    (t₁ t₂ : Option (Σ ty, Term (fun ty ↦ M (Ty.Domain E W ty S)) ty)) :
    (t₁.bind fun d₁ ↦ t₂.bind fun d₂ ↦ Mode.combine? (fun m l r ↦ .comp m l r) d₁ d₂).bind
        (evalAt g) =
      (t₁.bind (evalAt g)).bind fun d₁ ↦ (t₂.bind (evalAt g)).bind fun d₂ ↦
        Mode.combine? Mode.evalM d₁ d₂ := by
  rcases t₁ with _ | ⟨τ₁, u₁⟩
  · rfl
  rcases t₂ with _ | ⟨τ₂, u₂⟩
  · simp only [Option.bind_some, Option.bind_none]
    cases evalAt g ⟨τ₁, u₁⟩ <;> rfl
  simp only [Option.bind_some, evalAt, Mode.combine?]
  rcases hm : τ₁.mode? τ₂ with _ | ⟨τ, m⟩ <;>
    rcases ha : u₁.evalM (fun c ↦ c) g with _ | a <;>
    rcases hb : u₂.evalM (fun c ↦ c) g with _ | b <;>
    simp [Term.evalM, hm, ha, hb]

variable (lex : L → Option (Denotation E W M S)) (g : Assignment E)

@[simp] theorem interp_terminal (c : C) (w : L) :
    interp lex g (.terminal c w : Tree C L) = lex w := by
  simp only [interp, translate_terminal]
  cases lex w <;> rfl

@[simp] theorem interp_node_unary (c : C) (t : Tree C L) :
    interp lex g (.node c (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_adjoin_unary (c : C) (t : Tree C L) :
    interp lex g (.adjoin c (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_node_binary (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.node c (t₁ :: t₂ :: [])) = ((interp lex g t₁).bind fun d₁ ↦
      (interp lex g t₂).bind fun d₂ ↦ Mode.combine? Mode.evalM d₁ d₂) :=
  bind_evalAt_combine g _ _

@[simp] theorem interp_adjoin_binary (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.adjoin c (t₁ :: t₂ :: [])) = ((interp lex g t₁).bind fun d₁ ↦
      (interp lex g t₂).bind fun d₂ ↦ Mode.combine? Mode.evalM d₁ d₂) :=
  bind_evalAt_combine g _ _

@[simp] theorem interp_trace (n : ℕ) (c : C) :
    interp lex g (.trace n c : Tree C L) = some ⟨.e, pure (g n)⟩ := rfl

@[simp] theorem interp_bind (n : ℕ) (c : C) (body : Tree C L) :
    interp lex g (.bind n c body) =
      (PredAbs.dist? (M := M) (E := E) (W := W) (S := S)).bind fun dist ↦
        (interp lex g body).bind fun d ↦
          some ⟨.fn .e d.1, dist d.1 fun x ↦ valueAt d.1 d.2 (interp lex (g[n ↦ x]) body)⟩ := by
  simp only [interp, translate_bind, evalAt]
  rcases translate (K := fun ty ↦ M (Ty.Domain E W ty S)) lex body with _ | ⟨τ, b⟩
  · cases PredAbs.dist? (M := M) (E := E) (W := W) (S := S) <;> rfl
  · simp only [Option.map_some, Option.bind_some, Term.evalM]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (S := S) with
    | none => rfl
    | some dist =>
      rcases b.evalM (fun c ↦ c) g with _ | p
      · rfl
      · simp only [Option.bind_some, Option.map_some]
        congr 3
        funext x
        rcases b.evalM (fun c ↦ c) (g[n ↦ x]) with _ | v <;> simp [valueAt]

/-- A node whose daughters its label does not license denotes nothing. -/
theorem interp_junk {l : Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ Tree.Label.Licenses l (cs.map RoseTree.value)) :
    interp lex g (RoseTree.node l cs) = none := by
  simp only [interp, translate_junk _ h, Option.bind_none]

end Reduction

/-! ### The type of a tree

The type a tree composes to is a function of the types of its leaves: `ty?` computes it by the
recursion of `interp`, with `Ty.combine?` at the binary nodes, and `interp_map_fst` is the
agreement. Interpretability is therefore decided by the types of the leaves alone. -/

section TreeTyping

variable {C : Type} {L : Type*}

/-- The type a tree composes to, from the types `lexTy` gives its leaves, with `abs` saying
whether the effect supports Predicate Abstraction. -/
def ty? (lexTy : L → Option Ty) (abs : Bool) : Tree C L → Option Ty
  | .terminal _ w => lexTy w
  | .node _ (t :: []) => ty? lexTy abs t
  | .node _ (t1 :: t2 :: []) => do
    let σ ← ty? lexTy abs t1
    let τ ← ty? lexTy abs t2
    σ.combine? τ
  | .node _ _ => none
  | .adjoin _ (t :: []) => ty? lexTy abs t
  | .adjoin _ (t1 :: t2 :: []) => do
    let σ ← ty? lexTy abs t1
    let τ ← ty? lexTy abs t2
    σ.combine? τ
  | .adjoin _ _ => none
  | .trace _ _ => some .e
  | .bind _ _ body => if abs then (ty? lexTy abs body).map (.fn .e) else none
  | _ => none

variable (lexTy : L → Option Ty) (abs : Bool)

@[simp] theorem ty?_terminal (c : C) (w : L) :
    ty? lexTy abs (.terminal c w : Tree C L) = lexTy w := rfl

@[simp] theorem ty?_node_unary (c : C) (t : Tree C L) :
    ty? lexTy abs (.node c (t :: [])) = ty? lexTy abs t := rfl

@[simp] theorem ty?_node_binary (c : C) (t₁ t₂ : Tree C L) :
    ty? lexTy abs (.node c (t₁ :: t₂ :: [])) =
      (ty? lexTy abs t₁).bind fun σ ↦ (ty? lexTy abs t₂).bind fun τ ↦ σ.combine? τ := rfl

@[simp] theorem ty?_adjoin_unary (c : C) (t : Tree C L) :
    ty? lexTy abs (.adjoin c (t :: [])) = ty? lexTy abs t := rfl

@[simp] theorem ty?_adjoin_binary (c : C) (t₁ t₂ : Tree C L) :
    ty? lexTy abs (.adjoin c (t₁ :: t₂ :: [])) =
      (ty? lexTy abs t₁).bind fun σ ↦ (ty? lexTy abs t₂).bind fun τ ↦ σ.combine? τ := rfl

@[simp] theorem ty?_trace (n : ℕ) (c : C) : ty? lexTy abs (.trace n c : Tree C L) = some .e := rfl

@[simp] theorem ty?_bind (n : ℕ) (c : C) (body : Tree C L) :
    ty? lexTy abs (.bind n c body) =
      if abs then (ty? lexTy abs body).map (.fn .e) else none := rfl

/-- A node whose daughters its label does not license has no type. -/
theorem ty?_junk {l : Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ Tree.Label.Licenses l (cs.map RoseTree.value)) :
    ty? lexTy abs (RoseTree.node l cs) = none := by
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

variable {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M] [PredAbs M E W S]

variable {lexTy} {lex : L → Option (Denotation E W M S)}

/-- The type of a tree's denotation is the type `ty?` computes from the types of its leaves. -/
theorem interp_map_fst (h : ∀ w, (lex w).map (·.1) = lexTy w) (g : Assignment E)
    (t : Tree C L) :
    (interp lex g t).map (·.1) =
      ty? lexTy (PredAbs.dist? (M := M) (E := E) (W := W) (S := S)).isSome t := by
  induction t using Tree.rec' generalizing g with
  | terminal c w => rw [interp_terminal]; exact h w
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      rw [interp_node_binary, ty?_node_binary, ← ih t₁ (by simp) g, ← ih t₂ (by simp) g]
      cases interp lex g t₁ <;> cases interp lex g t₂ <;> simp [Ty.combine?]
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      rw [interp_adjoin_binary, ty?_adjoin_binary, ← ih t₁ (by simp) g, ← ih t₂ (by simp) g]
      cases interp lex g t₁ <;> cases interp lex g t₂ <;> simp [Ty.combine?]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    rw [interp_bind, ty?_bind, ← ih g]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (S := S) <;>
      cases interp lex g body <;> rfl
  | junk l cs hj _ => rw [interp_junk lex g hj, ty?_junk _ _ hj]; rfl

/-- A tree is interpretable exactly when the types of its leaves give it a type. -/
theorem isSome_interp (h : ∀ w, (lex w).map (·.1) = lexTy w) (g : Assignment E)
    (t : Tree C L) :
    (interp lex g t).isSome =
      (ty? lexTy (PredAbs.dist? (M := M) (E := E) (W := W) (S := S)).isSome t).isSome := by
  rw [← interp_map_fst h g t, Option.isSome_map]

end TreeTyping

/-! ### Assignment dependence and free variables

[heim-kratzer-1998]'s theorems on variable binding (§5.4.2): the denotation of a tree depends
on the assignment only at the traces free in it. Interpretability and the type composed do not
depend on the assignment at all (`interp_map_fst_congr`), so with total assignments their
theorem (9), that a tree with no free occurrence of the index `i` denotes alike under an
assignment and its modification at `i`, is `interp_update_of_not_mem_freeIndices`, and their
(10), that a closed tree denotes alike under every assignment, is `interp_congr_of_closed`. -/

section FreeVariables

variable {C : Type} {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M] [PredAbs M E W S]
  {L : Type*} (lex : L → Option (Denotation E W M S))

/-- Whether a tree is interpretable, and at which type, does not depend on the assignment. -/
theorem interp_map_fst_congr (g g' : Assignment E) (t : Tree C L) :
    (interp lex g t).map (·.1) = (interp lex g' t).map (·.1) := by
  rw [interp_map_fst (fun _ ↦ rfl), interp_map_fst (fun _ ↦ rfl)]

/-- Assignments agreeing on the traces free in a tree give it the same denotation, the
coincidence theorem ([heim-kratzer-1998] §5.4.2). -/
theorem interp_congr_of_agree {g g' : Assignment E} {t : Tree C L}
    (h : ∀ i ∈ t.freeIndices, g i = g' i) : interp lex g t = interp lex g' t := by
  induction t using Tree.rec' generalizing g g' with
  | terminal c w => simp only [interp_terminal]
  | node c cs ih =>
    have hm : ∀ t ∈ cs, ∀ i ∈ t.freeIndices, g i = g' i := fun t ht i hi =>
      h i (Tree.mem_freeIndices_node.2 ⟨t, ht, hi⟩)
    match cs with
    | [] => rfl
    | [t] => simp only [interp_node_unary]; exact ih t (by simp) (hm t (by simp))
    | [t₁, t₂] =>
      simp only [interp_node_binary]
      rw [ih t₁ (by simp) (hm t₁ (by simp)), ih t₂ (by simp) (hm t₂ (by simp))]
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    have hm : ∀ t ∈ cs, ∀ i ∈ t.freeIndices, g i = g' i := fun t ht i hi =>
      h i (Tree.mem_freeIndices_adjoin.2 ⟨t, ht, hi⟩)
    match cs with
    | [] => rfl
    | [t] => simp only [interp_adjoin_unary]; exact ih t (by simp) (hm t (by simp))
    | [t₁, t₂] =>
      simp only [interp_adjoin_binary]
      rw [ih t₁ (by simp) (hm t₁ (by simp)), ih t₂ (by simp) (hm t₂ (by simp))]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => simp only [interp_trace]; rw [h n (by simp)]
  | bind n c body ih =>
    simp only [interp_bind]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (S := S) with
    | none => rfl
    | some dist =>
      have hb : ∀ x, interp lex (g[n ↦ x]) body = interp lex (g'[n ↦ x]) body :=
        fun x ↦ ih fun i hi ↦ by
          by_cases hin : i = n
          · subst hin; simp
          · rw [Function.update_of_ne hin, Function.update_of_ne hin]
            exact h i (by rw [Tree.freeIndices_bind]; exact Finset.mem_erase.mpr ⟨hin, hi⟩)
      have ht := interp_map_fst_congr lex g g' body
      revert ht
      cases hg : interp lex g body <;> cases hg' : interp lex g' body <;> intro ht
      · rfl
      · simp at ht
      · simp at ht
      · rename_i d d'
        obtain ⟨τ, v⟩ := d; obtain ⟨τ', v'⟩ := d'
        simp only [Option.map_some, Option.some.injEq] at ht
        subst ht
        simp only [Option.bind_some, Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
        congr 1
        funext x
        rw [hb x]
        exact valueAt_of_map_fst (by rw [interp_map_fst_congr lex _ g' body, hg']; rfl)
  | junk l cs hj _ => rw [interp_junk lex g hj, interp_junk lex g' hj]

/-- By [heim-kratzer-1998]'s (9), a tree with no free trace at index `i` denotes alike under an
assignment and its modification at `i`. -/
theorem interp_update_of_not_mem_freeIndices {t : Tree C L} {i : ℕ}
    (h : i ∉ t.freeIndices) (g : Assignment E) (x : E) :
    interp lex (g[i ↦ x]) t = interp lex g t :=
  interp_congr_of_agree lex fun j hj ↦
    Function.update_of_ne (fun hji ↦ h (by subst hji; exact hj)) x g

/-- By [heim-kratzer-1998]'s (10), a closed tree denotes alike under every assignment. -/
theorem interp_congr_of_closed {t : Tree C L} (h : t.Closed) (g g' : Assignment E) :
    interp lex g t = interp lex g' t :=
  interp_congr_of_agree lex fun i hi ↦ absurd (h ▸ hi) (Finset.notMem_empty i)

end FreeVariables

/-! ### Readings of an ambiguous lexicon

A word may have several available readings. A resolution of a tree chooses one reading for
each occurrence of a word, and the readings of the tree are the values the engine computes
over its resolutions. The engine on a lexicon with one reading per word is the special case
(`readings_eq_of_choice`), and a binary node's readings are the pointwise compositions of its
daughters' (`mem_readings_node_binary`). -/

section Readings

variable {C : Type} {L : Type*} {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M]
  [PredAbs M E W S]

/-- Interpretation commutes with relabelling the leaves. -/
theorem interp_map {L' : Type*} (lex : L' → Option (Denotation E W M S)) (f : L → L')
    (g : Assignment E) (t : Tree C L) : interp lex g (t.map f) = interp (lex ∘ f) g t := by
  induction t using Tree.rec' generalizing g with
  | terminal c w => rfl
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      simp only [Tree.map_node, List.map, interp_node_binary, ih t₁ (by simp), ih t₂ (by simp)]
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      simp only [Tree.map_adjoin, List.map, interp_adjoin_binary, ih t₁ (by simp), ih t₂ (by simp)]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih => simp only [Tree.map_bind, interp_bind, ih]
  | junk l cs hj _ =>
    have hmap : (cs.map (Tree.map f)).map RoseTree.value =
        (cs.map RoseTree.value).map (Tree.Label.mapWord f) := by
      simp only [List.map_map]
      exact List.map_congr_left fun t _ ↦ Tree.value_map f t
    rw [Tree.map_rose, interp_junk _ _ (by rw [hmap, Tree.Label.licenses_mapWord]; exact hj),
      interp_junk _ _ hj]

variable (lex : L → Set (Denotation E W M S)) (g : Assignment E)

/-- The readings of a tree under a leaf interpretation giving each word a set of readings, the
values the engine computes over the resolutions of the tree, each occurrence of a word resolved
to one of its readings. -/
def readings (t : Tree C L) : Set (Denotation E W M S) :=
  {d | ∃ r : Tree C {p : L × Denotation E W M S // p.2 ∈ lex p.1},
    r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d}

variable {lex g}

/-- A value the engine computes under a choice of readings is the value of a resolved tree. -/
theorem exists_resolution_of_interp {choice : L → Option (Denotation E W M S)} {t : Tree C L}
    {d : Denotation E W M S} (h : interp choice g t = some d) :
    ∃ r : Tree C {p : L × Denotation E W M S // choice p.1 = some p.2},
      r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d := by
  induction t using Tree.rec' generalizing g d with
  | terminal c w =>
    rw [interp_terminal] at h
    exact ⟨.terminal c ⟨(w, d), h⟩, rfl, by rw [interp_terminal]⟩
  | node c cs ih =>
    match cs with
    | [] => exact absurd h (by simp [interp, translate])
    | [t] =>
      obtain ⟨r, hr, hd⟩ := ih t (by simp) h
      exact ⟨.node c (r :: []), by simp [hr], hd⟩
    | [t₁, t₂] =>
      rw [interp_node_binary] at h
      obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, hd₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨r₂, hr₂, hd₂⟩ := ih t₂ (by simp) h₂
      exact ⟨.node c (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
        by rw [interp_node_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩
    | _ :: _ :: _ :: _ => exact absurd h (by simp [interp, translate])
  | adjoin c cs ih =>
    match cs with
    | [] => exact absurd h (by simp [interp, translate])
    | [t] =>
      obtain ⟨r, hr, hd⟩ := ih t (by simp) h
      exact ⟨.adjoin c (r :: []), by simp [hr], hd⟩
    | [t₁, t₂] =>
      rw [interp_adjoin_binary] at h
      obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, hd₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨r₂, hr₂, hd₂⟩ := ih t₂ (by simp) h₂
      exact ⟨.adjoin c (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
        by rw [interp_adjoin_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩
    | _ :: _ :: _ :: _ => exact absurd h (by simp [interp, translate])
  | trace n c => exact ⟨.trace n c, rfl, h⟩
  | bind n c body ih =>
    rw [interp_bind] at h
    obtain ⟨dist, hdist, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨τ, probe⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hd⟩ := ih hb
    have hres : ∀ g', interp choice g' body = interp (fun p ↦ some p.1.2) g' r := fun g' ↦ by
      rw [← hr, interp_map]
      exact congrFun (congrFun (congrArg _ (funext fun p ↦ p.2)) g') r
    refine ⟨.bind n c r, by simp [hr], ?_⟩
    rw [interp_bind, hdist, Option.bind_some, hd, Option.bind_some]
    simpa only [hres] using h
  | junk l cs hj _ => exact absurd h (by rw [interp_junk _ _ hj]; simp)

/-- A value the engine computes under a choice among the readings is a reading. -/
theorem interp_mem_readings {choice : L → Option (Denotation E W M S)}
    (hc : ∀ w d, choice w = some d → d ∈ lex w) {t : Tree C L} {d : Denotation E W M S}
    (h : interp choice g t = some d) : d ∈ readings lex g t := by
  obtain ⟨r, hr, hd⟩ := exists_resolution_of_interp h
  refine ⟨r.map fun p ↦ ⟨p.1, hc _ _ p.2⟩, ?_, ?_⟩
  · rw [Tree.map_map]; exact hr
  · rw [interp_map]; exact hd

/-- On a lexicon with one reading per word, the readings are the engine's values. -/
theorem readings_eq_of_choice (choice : L → Option (Denotation E W M S)) (t : Tree C L) :
    readings (fun w ↦ {d | choice w = some d}) g t = {d | interp choice g t = some d} := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ interp_mem_readings (fun _ _ h ↦ h) h⟩
  show interp choice g t = some d
  rw [← hr, interp_map]
  exact (congrFun (congrFun (congrArg _ (funext fun p ↦ p.2)) g) r).trans hd

@[simp] theorem readings_terminal (c : C) (w : L) : readings lex g (.terminal c w) = lex w := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ ⟨.terminal c ⟨(w, d), h⟩, rfl, rfl⟩⟩
  rcases r with ⟨l, cs⟩
  simp only [Tree.map_rose, RoseTree.node.injEq, List.map_eq_nil_iff] at hr
  obtain ⟨hl, rfl⟩ := hr
  cases l with
  | terminal c' p =>
    simp only [Tree.Label.mapWord, Tree.Label.terminal.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    cases Option.some.inj hd
    exact p.2
  | _ => simp [Tree.Label.mapWord] at hl

@[simp] theorem readings_trace (n : ℕ) (c : C) :
    readings lex g (.trace n c) = {⟨.e, pure (g n)⟩} := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ ⟨.trace n c, rfl, h ▸ rfl⟩⟩
  rcases r with ⟨l, cs⟩
  simp only [Tree.map_rose, RoseTree.node.injEq, List.map_eq_nil_iff] at hr
  obtain ⟨hl, rfl⟩ := hr
  cases l with
  | trace n' c' =>
    simp only [Tree.Label.mapWord, Tree.Label.trace.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact (Option.some.inj hd).symm
  | _ => simp [Tree.Label.mapWord] at hl

/-- A binary node's readings are the pointwise compositions of its daughters'. -/
theorem mem_readings_node_binary {c : C} {t₁ t₂ : Tree C L} {d : Denotation E W M S} :
    d ∈ readings lex g (.node c (t₁ :: t₂ :: [])) ↔
      ∃ d₁ ∈ readings lex g t₁, ∃ d₂ ∈ readings lex g t₂,
        Mode.combine? Mode.evalM d₁ d₂ = some d := by
  constructor
  · rintro ⟨r, hr, hd⟩
    rcases r with ⟨l, cs⟩
    simp only [Tree.map_rose, RoseTree.node.injEq] at hr
    obtain ⟨hl, hcs⟩ := hr
    cases l with
    | node c' =>
      simp only [Tree.Label.mapWord, Tree.Label.node.injEq] at hl
      subst hl
      obtain ⟨r₁, cs₁, rfl, rfl, hcs₁⟩ := List.map_eq_cons_iff.mp hcs
      obtain ⟨r₂, cs₂, rfl, rfl, hcs₂⟩ := List.map_eq_cons_iff.mp hcs₁
      obtain rfl := List.map_eq_nil_iff.mp hcs₂
      rw [interp_node_binary] at hd
      obtain ⟨d₁, h₁, hd⟩ := Option.bind_eq_some_iff.mp hd
      obtain ⟨d₂, h₂, hd⟩ := Option.bind_eq_some_iff.mp hd
      exact ⟨d₁, ⟨r₁, rfl, h₁⟩, d₂, ⟨r₂, rfl, h₂⟩, hd⟩
    | _ => simp [Tree.Label.mapWord] at hl
  · rintro ⟨d₁, ⟨r₁, hr₁, hd₁⟩, d₂, ⟨r₂, hr₂, hd₂⟩, h⟩
    exact ⟨.node c (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
      by rw [interp_node_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩

end Readings


/-! ### Interpretation is evaluation of the translation -/

section Translation

variable {C : Type} {K : Ty → Type*} {L : Type*} {E W : Type} {S : Sorts}

/-- Interpreting a tree whose words denote what an interpretation `I` of their constants gives
is evaluating the tree's term under `I`. -/
theorem interp_eq_eval_translate (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S)
    (lex : L → Option (Σ ty, K ty)) (g : Assignment E) (t : Tree C L) :
    interp (M := Id) (fun w ↦ (lex w).map fun c ↦ ⟨c.1, I c.2⟩) g t =
      (translate lex t).map fun d ↦ ⟨d.1, d.2.eval I g⟩ := by
  simp only [interp, translate_map_const, evalAt]
  cases translate lex t with
  | none => rfl
  | some d => simp [Term.eval_map]

end Translation


/-! ### Truth -/

section Truth

variable {C : Type} {L : Type*} {E W : Type}

/-- A tree holds under a lexicon and an assignment when it composes to a true truth value. -/
def HoldsAt (lex : L → Option (Denotation E W)) (g : Assignment E) (t : Tree C L) : Prop :=
  ∃ p, interp lex g t = some ⟨.t, p⟩ ∧ p

end Truth

end PhraseStructure.Tree
