module

public import Linglib.Semantics.Composition.Term
public import Linglib.Semantics.Composition.Lexicon

/-!
# Type-driven interpretation

This file is the composition engine of Heim and Kratzer's type-driven interpretation, with the
intensional application of von Fintel and Heim and the event identification of Kratzer
(`eventIdentification`), parameterized over an effect functor `M` in the style of Bumford and
Charlow. A node denotes an `M`-computation in the domain of its semantic type,
a `Denotation`, and each composition principle lifts through the `Applicative` structure of
`M`, so the pure Heim and Kratzer engine is the instance `M = Id`. A terminal node denotes
what its leaf interpretation gives it, a string in a `Lexicon` or a fragment carrier through
its readings; a non-branching node denotes what its daughter does; a binary node composes by
functional application in either order, then intensional functional application, then
predicate modification, then event identification, whichever the daughters' types admit first;
a trace denotes its index's value under the assignment; and a binder abstracts over its index
by Predicate Abstraction, which is a capability of the effect (`PredAbs`) rather than a given.

A tree is interpreted by evaluating its translation (`Composition/Term.lean`): the composition
modes are the typed operations of `Composition/Mode.lean`, selected by the daughters' types
alone, and `interp` is the evaluation of the term a tree translates to. Each equation of the
engine is then a fact about that evaluation, and the pure engine is the denotation of the term
(`interp_eq_eval_translate`).

## Main declarations

* `interp` interprets a tree under an assignment, over any leaf type, as the evaluation of its
  translation; a binary node composes by `Montague.Ty.mode?` (`interp_node_binary`).
* `tyBinary` is the type a binary node composes to, a function of the daughters' types alone.
* `ty?` is the type a tree composes to, a function of the types of its leaves alone, and the
  type of its denotation (`interp_map_fst`).
* `interp_congr_of_agree` and its corollaries are Heim and Kratzer's theorems on variable
  binding: interpretability and the composed type never depend on the assignment
  (`interp_map_fst_congr`), and a tree's denotation depends on it only at the traces free in
  the tree.
* `readings` composes a lexicon of sets of readings, the values the engine computes over the
  tree's resolutions; the engine on an unambiguous lexicon is the special case
  (`readings_eq_of_choice`) and a binary node's readings compose pointwise
  (`mem_readings_node_binary`).
* `interp_eq_eval_translate`: the pure engine is the denotation of the tree's term.

## Implementation notes

Binary nodes sequence effects in linear order, the left daughter's first whichever daughter is
the function, so at `M = Cont R` surface scope is the default reading and inverse scope needs
a reordered evaluation (`Composition/Cont.lean`). Predicate Abstraction needs a distributor
`(E → M (Ty.Domain ty)) → M (E → Ty.Domain ty)`, which scope effects lack, so under them `.bind`
nodes fail and binding comes from the order of effects instead; making the distributor optional
turns that rivalry into a fact instance resolution checks. The abstraction's fallback value
`valueAt` is never reached, since types do not depend on the assignment. The category parameter
of a tree is ignored, composition being type-driven.

## References

* [heim-kratzer-1998]
* [von-fintel-heim-2011]
* [kratzer-1996]
* [bumford-charlow-2026]
-/

@[expose] public section

namespace HeimKratzer.Tree

open Montague
open scoped Assignment

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
def valueAt {E W D : Type} {M : Type → Type} (τ : Ty) (v : M (Ty.Domain E W τ D)) :
    Option (Denotation E W M D) → M (Ty.Domain E W τ D)
  | some ⟨ty, val⟩ => if h : ty = τ then h ▸ val else v
  | none => v

@[simp] theorem valueAt_some {E W D : Type} {M : Type → Type} {τ : Ty}
    (v x : M (Ty.Domain E W τ D)) :
    valueAt τ v (some ⟨τ, x⟩ : Option (Denotation E W M D)) = x := by
  simp [valueAt]

theorem valueAt_of_map_fst {E W D : Type} {M : Type → Type} {τ : Ty}
    {v v' : M (Ty.Domain E W τ D)} {d : Option (Denotation E W M D)}
    (h : d.map (·.1) = some τ) : valueAt τ v d = valueAt τ v' d := by
  obtain _ | ⟨ty, val⟩ := d
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h; simp [valueAt]

/-! ### Tree interpretation -/

open PhraseStructure

section TreeInterp

variable {C : Type}

/-- The denotation of a term whose constants are denotations, at its type. -/
abbrev evalAt {E W : Type} {M : Type → Type} [Applicative M] {D : Type} [PredAbs M E W D]
    (g : Assignment E) (d : Σ ty, Term (fun ty ↦ M (Ty.Domain E W ty D)) ty) :
    Option (Denotation E W M D) :=
  (d.2.evalM (fun c ↦ c) g).map fun v ↦ ⟨d.1, v⟩

/-- In the denotation of a tree under an assignment, by the composition principles of
[heim-kratzer-1998], a terminal denotes what its leaf interpretation gives it, a non-branching
node what its daughter does, a binary node what the mode its daughters' types select composes, a
trace the value of its index, and a binder the abstraction over its index, when the effect has a
distributor. It is the denotation of the tree's term, each word's denotation its constant. -/
def interp {E W : Type} {M : Type → Type} [Applicative M] {D : Type} [PredAbs M E W D]
    {L : Type*} (lex : L → Option (Denotation E W M D)) (g : Assignment E) (t : Tree C L) :
    Option (Denotation E W M D) :=
  (translate (K := fun ty ↦ M (Ty.Domain E W ty D)) lex t).bind (evalAt g)

end TreeInterp

/-! ### Reduction lemmas

One `@[simp]` lemma per constructor, so that a derivation reduces by `simp` toward its
composed denotation. -/

section Reduction

variable {C : Type} {E W D : Type} {M : Type → Type} [Applicative M] [PredAbs M E W D]
  {L : Type*}

private theorem bind_evalAt_combine (g : Assignment E)
    (t₁ t₂ : Option (Σ ty, Term (fun ty ↦ M (Ty.Domain E W ty D)) ty)) :
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

variable (lex : L → Option (Denotation E W M D)) (g : Assignment E)

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
      (PredAbs.dist? (M := M) (E := E) (W := W) (D := D)).bind fun dist ↦
        (interp lex g body).bind fun d ↦
          some ⟨.fn .e d.1, dist d.1 fun x ↦ valueAt d.1 d.2 (interp lex (g[n ↦ x]) body)⟩ := by
  simp only [interp, translate_bind, evalAt]
  rcases translate (K := fun ty ↦ M (Ty.Domain E W ty D)) lex body with _ | ⟨τ, b⟩
  · cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) <;> rfl
  · simp only [Option.map_some, Option.bind_some, Term.evalM]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) with
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
recursion of `interp`, with `tyBinary` at the binary nodes, and `interp_map_fst` is the
agreement. Interpretability is therefore decided by the types of the leaves alone. -/

/-- The type two daughters compose to, the mother's type under the mode their types select. -/
def tyBinary (σ τ : Ty) : Option Ty := (σ.mode? τ).map (·.1)

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
    tyBinary σ τ
  | .node _ _ => none
  | .adjoin _ (t :: []) => ty? lexTy abs t
  | .adjoin _ (t1 :: t2 :: []) => do
    let σ ← ty? lexTy abs t1
    let τ ← ty? lexTy abs t2
    tyBinary σ τ
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
      (ty? lexTy abs t₁).bind fun σ ↦ (ty? lexTy abs t₂).bind fun τ ↦ tyBinary σ τ := rfl

@[simp] theorem ty?_adjoin_unary (c : C) (t : Tree C L) :
    ty? lexTy abs (.adjoin c (t :: [])) = ty? lexTy abs t := rfl

@[simp] theorem ty?_adjoin_binary (c : C) (t₁ t₂ : Tree C L) :
    ty? lexTy abs (.adjoin c (t₁ :: t₂ :: [])) =
      (ty? lexTy abs t₁).bind fun σ ↦ (ty? lexTy abs t₂).bind fun τ ↦ tyBinary σ τ := rfl

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

variable {E W D : Type} {M : Type → Type} [Applicative M] [PredAbs M E W D]

variable {lexTy} {lex : L → Option (Denotation E W M D)}

/-- The type of a tree's denotation is the type `ty?` computes from the types of its leaves. -/
theorem interp_map_fst (h : ∀ w, (lex w).map (·.1) = lexTy w) (g : Assignment E)
    (t : Tree C L) :
    (interp lex g t).map (·.1) =
      ty? lexTy (PredAbs.dist? (M := M) (E := E) (W := W) (D := D)).isSome t := by
  induction t using Tree.rec' generalizing g with
  | terminal c w => rw [interp_terminal]; exact h w
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      rw [interp_node_binary, ty?_node_binary, ← ih t₁ (by simp) g, ← ih t₂ (by simp) g]
      cases interp lex g t₁ <;> cases interp lex g t₂ <;> simp [tyBinary]
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      rw [interp_adjoin_binary, ty?_adjoin_binary, ← ih t₁ (by simp) g, ← ih t₂ (by simp) g]
      cases interp lex g t₁ <;> cases interp lex g t₂ <;> simp [tyBinary]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    rw [interp_bind, ty?_bind, ← ih g]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) <;>
      cases interp lex g body <;> rfl
  | junk l cs hj _ => rw [interp_junk lex g hj, ty?_junk _ _ hj]; rfl

/-- A tree is interpretable exactly when the types of its leaves give it a type. -/
theorem isSome_interp (h : ∀ w, (lex w).map (·.1) = lexTy w) (g : Assignment E)
    (t : Tree C L) :
    (interp lex g t).isSome =
      (ty? lexTy (PredAbs.dist? (M := M) (E := E) (W := W) (D := D)).isSome t).isSome := by
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

variable {C : Type} {E W D : Type} {M : Type → Type} [Applicative M] [PredAbs M E W D]
  {L : Type*} (lex : L → Option (Denotation E W M D))

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
    cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) with
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

variable {C : Type} {L : Type*} {E W D : Type} {M : Type → Type} [Applicative M]
  [PredAbs M E W D]

/-- Interpretation commutes with relabelling the leaves. -/
theorem interp_map {L' : Type*} (lex : L' → Option (Denotation E W M D)) (f : L → L')
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

variable (lex : L → Set (Denotation E W M D)) (g : Assignment E)

/-- The readings of a tree under a leaf interpretation giving each word a set of readings, the
values the engine computes over the resolutions of the tree, each occurrence of a word resolved
to one of its readings. -/
def readings (t : Tree C L) : Set (Denotation E W M D) :=
  {d | ∃ r : Tree C {p : L × Denotation E W M D // p.2 ∈ lex p.1},
    r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d}

variable {lex g}

/-- A value the engine computes under a choice of readings is the value of a resolved tree. -/
theorem exists_resolution_of_interp {choice : L → Option (Denotation E W M D)} {t : Tree C L}
    {d : Denotation E W M D} (h : interp choice g t = some d) :
    ∃ r : Tree C {p : L × Denotation E W M D // choice p.1 = some p.2},
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
theorem interp_mem_readings {choice : L → Option (Denotation E W M D)}
    (hc : ∀ w d, choice w = some d → d ∈ lex w) {t : Tree C L} {d : Denotation E W M D}
    (h : interp choice g t = some d) : d ∈ readings lex g t := by
  obtain ⟨r, hr, hd⟩ := exists_resolution_of_interp h
  refine ⟨r.map fun p ↦ ⟨p.1, hc _ _ p.2⟩, ?_, ?_⟩
  · rw [Tree.map_map]; exact hr
  · rw [interp_map]; exact hd

/-- On a lexicon with one reading per word, the readings are the engine's values. -/
theorem readings_eq_of_choice (choice : L → Option (Denotation E W M D)) (t : Tree C L) :
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
theorem mem_readings_node_binary {c : C} {t₁ t₂ : Tree C L} {d : Denotation E W M D} :
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

variable {C : Type} {K : Ty → Type*} {L : Type*} {E W D : Type}

/-- Interpreting a tree whose words denote what an interpretation `I` of their constants gives
is evaluating the tree's term under `I`. -/
theorem interp_eq_eval_translate (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D)
    (lex : L → Option (Σ ty, K ty)) (g : Assignment E) (t : Tree C L) :
    interp (M := Id) (fun w ↦ (lex w).map fun c ↦ ⟨c.1, I c.2⟩) g t =
      (translate lex t).map fun d ↦ ⟨d.1, d.2.eval I g⟩ := by
  simp only [interp, translate_map_const, evalAt]
  cases translate lex t with
  | none => rfl
  | some d => simp [Term.eval_map]

end Translation

end HeimKratzer.Tree
