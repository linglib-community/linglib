module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Composition.Term

/-!
# Type-driven interpretation of trees

Type-driven interpretation gives each node of a tree the meaning that the mode its daughters'
types select makes of its daughters' meanings, with traces and binders interpreted by an
assignment as in Heim and Kratzer. As in Montague's theory of translation,
[a tree's denotation is the evaluation of the term it translates to](##interp_eq_eval_translate),
and [it depends on the assignment only at the tree's free traces](##interp_congr_of_agree).
Denotations may be computations under an effect, after Bumford and Charlow, and a tree whose
words are computations, reading a world or ranging over alternatives, has as many derivations as
the modes lifting composition over those effects allow. Under a typing of the indices, a trace or
binder of index $n$ is a variable of the type its index has, so a world pronoun and the λ binding
it are a trace and a binder whose index has type $s$.

## Main definitions

* `Montague.Lexicon`: a lexicon of effectful denotations, keyed by strings.
* `PhraseStructure.Tree.translate`: the term a tree translates to.
* `PhraseStructure.Tree.translations`: every term a tree translates to, one per derivation.
* `PhraseStructure.Tree.interp`: the denotation of a tree under an assignment of individuals.
* `PhraseStructure.Tree.interpWith`: the denotation under a typing of the indices.
* `PhraseStructure.Tree.ty?`: the type a tree composes to, from the types of its words alone.
* `PhraseStructure.Tree.readings`: the readings of a tree under a lexicon of sets of readings.
* `PhraseStructure.Tree.HoldsAt`: the truth of a tree under a lexicon and an assignment.
* `PhraseStructure.Tree.HoldsAtWith`: the truth of a tree under a typing of its indices.

## Implementation notes

The tree operations live in the namespace `PhraseStructure.Tree`, so that `t.interp lex g` works.
`interp` is `interpWith` at `individualIndices` (`interp_eq_interpWith`), as mathlib's
`Formula.Realize` is `BoundedFormula.Realize` with no bound variables, since the typing cannot be
inferred from an assignment of individuals.
Translation is the only type-driven step and the only recursion on trees the semantics needs: the
type of a tree is the type of its term, and the dependence of a denotation on the assignment and on
the words is the term's (`freeVars_translate`, `translate_map`). Translation respects renaming and
relating constants (`translate_map_const`, `translate_rel`). Binary nodes sequence effects left to
right, whichever daughter is the function, so at `M = Cont R` the engine derives surface scope only:
inverse scope needs an evaluation order chosen per node, which the engine does not provide
(`Studies/Barker2002.lean` marks each rule with a permutation of its daughters). Predicate
Abstraction needs the effect to distribute over functions,
`(E → M (Ty.Domain ty)) → M (E → Ty.Domain ty)`. The abstraction's fallback value `valueAt` is
never reached, since types do not depend on the assignment. The category of a node and the kind
of a phrase are ignored, composition being type-driven.

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
abbrev evalAt {E W : Type} {M : Type → Type} [Applicative M] {S : Sorts} [Distributive M]
    {Γ : ℕ → Ty} (g : ∀ n, Ty.Domain E W (Γ n) S)
    (d : Σ ty, Term Γ (fun ty ↦ M (Ty.Domain E W ty S)) ty) : Denotation E W M S :=
  ⟨d.1, d.2.evalM (fun c ↦ c) g⟩

end Montague

namespace PhraseStructure.Tree

open Montague
open scoped Assignment

/-! ### Translation -/

section Translate

variable {C : Type} {Γ : ℕ → Ty} {K : Ty → Type*} {L : Type*}

/-- The term a tree translates to, by the composition principles of [heim-kratzer-1998]. A
terminal goes to its word's constant, a non-branching node to its daughter's term, a binary node to
its daughters' terms composed by the mode their types select, a trace to the variable of its index,
and a binder to the abstraction over that variable. -/
def translate (Γ : ℕ → Ty) (lex : L → Option (Σ ty, K ty)) : Tree C L → Option (Σ ty, Term Γ K ty)
  | .terminal _ w => (lex w).map fun c ↦ ⟨c.1, .const c.2⟩
  | .phrase _ _ (t :: []) => translate Γ lex t
  | .phrase _ _ (t1 :: t2 :: []) => do
    let d1 ← translate Γ lex t1
    let d2 ← translate Γ lex t2
    Mode.combine? (fun m l r ↦ .comp m l r) d1 d2
  | .phrase _ _ _ => none
  | .trace n _ => some ⟨Γ n, .var n⟩
  | .bind n _ body => (translate Γ lex body).map fun d ↦ ⟨Γ n ⇒ d.1, .lam n d.2⟩
  | _ => none

/-- Every term a tree translates to, one for each way of composing it ([bumford-charlow-2026]'s
interpreter): a binary node composes its daughters' terms by every mode their types admit,
`Ty.modes`, where `translate` takes the basic mode they select. -/
def translations (Γ : ℕ → Ty) (lex : L → Option (Σ ty, K ty)) :
    Tree C L → List (Σ ty, Term Γ K ty)
  | .terminal _ w => ((lex w).map fun c ↦ ⟨c.1, .const c.2⟩).toList
  | .phrase _ _ (t :: []) => translations Γ lex t
  | .phrase _ _ (t1 :: t2 :: []) =>
    (translations Γ lex t1).flatMap fun d1 ↦ (translations Γ lex t2).flatMap fun d2 ↦
      (d1.1.modes d2.1).map fun p ↦ ⟨p.1, .comp p.2 d1.2 d2.2⟩
  | .phrase _ _ _ => []
  | .trace n _ => [⟨Γ n, .var n⟩]
  | .bind n _ body => (translations Γ lex body).map fun d ↦ ⟨Γ n ⇒ d.1, .lam n d.2⟩
  | _ => []

variable (lex : L → Option (Σ ty, K ty))

@[simp] theorem translate_terminal (c : C) (w : L) :
    translate Γ lex (.terminal c w : Tree C L) = (lex w).map fun c ↦ ⟨c.1, .const c.2⟩ := rfl

@[simp] theorem translate_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    translate Γ lex (.phrase c k (t :: [])) = translate Γ lex t := rfl

@[simp] theorem translate_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    translate Γ lex (.phrase c k (t₁ :: t₂ :: [])) = ((translate Γ lex t₁).bind fun d₁ ↦
      (translate Γ lex t₂).bind fun d₂ ↦ Mode.combine? (fun m l r ↦ .comp m l r) d₁ d₂) := rfl

@[simp] theorem translate_trace (n : ℕ) (c : C) :
    translate Γ lex (.trace n c : Tree C L) = some ⟨Γ n, .var n⟩ := rfl

@[simp] theorem translate_bind (n : ℕ) (c : C) (body : Tree C L) :
    translate Γ lex (.bind n c body) =
      (translate Γ lex body).map fun d ↦ ⟨Γ n ⇒ d.1, .lam n d.2⟩ := rfl

theorem translate_junk {l : Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ Tree.Label.Licenses l (cs.map RoseTree.value)) :
    translate Γ lex (RoseTree.node l cs) = none := by
  cases l with
  | terminal c w => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | phrase c k => exact absurd trivial h
  | trace n c => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | bind n c =>
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩
    · rfl
    · exact absurd rfl h
    · rfl


theorem translate_map_const {K' : Ty → Type*} (f : ∀ {ty : Ty}, K ty → K' ty) (t : Tree C L) :
    translate Γ (fun w ↦ (lex w).map fun c ↦ ⟨c.1, f c.2⟩) t =
      (translate Γ lex t).map fun d ↦ ⟨d.1, d.2.map f⟩ := by
  induction t using Tree.rec' with
  | terminal c w => simp only [translate_terminal]; cases lex w <;> rfl
  | phrase c k cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp)
    | [t₁, t₂] =>
      simp only [translate_phrase_binary, ih t₁ (by simp), ih t₂ (by simp)]
      cases translate Γ lex t₁ <;> cases translate Γ lex t₂ <;> try rfl
      exact (Mode.combine?_map (fun _ _ _ ↦ rfl) _ _).symm
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih => simp only [translate_bind, ih, Option.map_map]; rfl
  | junk l cs hj _ => rw [translate_junk _ hj, translate_junk _ hj]; rfl


private theorem bind_combine?_map_fst {K' : Ty → Type*}
    {op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → Term Γ K σ₁ → Term Γ K σ₂ → Term Γ K τ}
    {op' : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → Term Γ K' σ₁ → Term Γ K' σ₂ → Term Γ K' τ}
    {o₁ o₂ : Option (Σ ty, Term Γ K ty)} {o₁' o₂' : Option (Σ ty, Term Γ K' ty)}
    (h₁ : o₁.map (·.1) = o₁'.map (·.1)) (h₂ : o₂.map (·.1) = o₂'.map (·.1)) :
    (o₁.bind fun a ↦ o₂.bind fun b ↦ Mode.combine? op a b).map (·.1) =
      (o₁'.bind fun a ↦ o₂'.bind fun b ↦ Mode.combine? op' a b).map (·.1) := by
  rcases o₁ with _ | ⟨σ₁, u₁⟩ <;> rcases o₁' with _ | ⟨σ₁', u₁'⟩ <;> simp at h₁ ⊢
  subst h₁
  rcases o₂ with _ | ⟨σ₂, u₂⟩ <;> rcases o₂' with _ | ⟨σ₂', u₂'⟩ <;> simp at h₂ ⊢
  subst h₂
  simp

theorem translate_map_fst {K' : Ty → Type*} {lex' : L → Option (Σ ty, K' ty)}
    (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    (translate Γ lex t).map (·.1) = (translate Γ lex' t).map (·.1) := by
  induction t using Tree.rec' with
  | terminal c w => simpa [Option.map_map, Function.comp_def] using h w
  | phrase c k cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp)
    | [t₁, t₂] =>
      simp only [translate_phrase_binary]
      exact bind_combine?_map_fst (ih t₁ (by simp)) (ih t₂ (by simp))
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    simp only [translate_bind, Option.map_map]
    revert ih
    cases translate Γ lex body <;> cases translate Γ lex' body <;> simp_all
  | junk l cs hj _ => rw [translate_junk _ hj, translate_junk _ hj]; rfl

/-- Lexicons whose constants are related translate a tree to terms of the same shape with
related constants. -/
theorem translate_rel {K' : Ty → Type*} {R : ∀ ty : Ty, K ty → K' ty → Prop}
    {lex' : L → Option (Σ ty, K' ty)}
    (hlex : ∀ w d', lex' w = some d' → ∃ c, lex w = some ⟨d'.1, c⟩ ∧ R d'.1 c d'.2)
    (t : Tree C L) :
    ∀ {d'}, translate Γ lex' t = some d' →
      ∃ u, translate Γ lex t = some ⟨d'.1, u⟩ ∧ Term.Rel R u d'.2 := by
  induction t using Tree.rec' with
  | terminal c w =>
    intro d' h
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨c', hc', hR⟩ := hlex w d hd
    exact ⟨.const c', by simp [hc'], .const hR⟩
  | phrase c k cs ih =>
    match cs with
    | [] => intro d' h; simp [translate] at h
    | [t] => intro d' h; exact ih t (by simp) h
    | [t₁, t₂] =>
      intro d' h
      simp only [translate_phrase_binary, Option.bind_eq_some_iff] at h
      obtain ⟨⟨σ₁, u₁'⟩, h₁, ⟨σ₂, u₂'⟩, h₂, h⟩ := h
      obtain ⟨u₁, hu₁, hr₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨u₂, hu₂, hr₂⟩ := ih t₂ (by simp) h₂
      simp only [Mode.combine?, Option.map_eq_some_iff] at h
      obtain ⟨⟨τ, m⟩, hm, rfl⟩ := h
      exact ⟨.comp m u₁ u₂, by simp [translate_phrase_binary, hu₁, hu₂, Mode.combine?, hm],
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

/-- The free variables of a tree's term are among the tree's free indices. -/
theorem freeVars_translate {t : Tree C L} {d : Σ ty, Term Γ K ty}
    (h : translate Γ lex t = some d) : d.2.freeVars ⊆ t.freeIndices := by
  induction t using Tree.rec' generalizing d with
  | terminal c w =>
    obtain ⟨c', -, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Term.freeVars]
  | phrase c k cs ih =>
    match cs, h with
    | [t], h => exact fun i hi ↦ Tree.mem_freeIndices_phrase.2 ⟨t, by simp, ih t (by simp) h hi⟩
    | [t₁, t₂], h =>
      obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
      intro i hi
      rcases Finset.mem_union.1 hi with hi | hi
      · exact Tree.mem_freeIndices_phrase.2 ⟨t₁, by simp, ih t₁ (by simp) h₁ hi⟩
      · exact Tree.mem_freeIndices_phrase.2 ⟨t₂, by simp, ih t₂ (by simp) h₂ hi⟩
  | trace n c =>
    obtain rfl := (Option.some.inj h).symm
    simp [Term.freeVars]
  | bind n c body ih =>
    obtain ⟨d', h', rfl⟩ := Option.map_eq_some_iff.1 h
    rw [Tree.freeIndices_bind]
    exact Finset.erase_subset_erase n (ih h')
  | junk l cs hj _ => rw [translate_junk _ hj] at h; cases h

/-- Translating a tree with relabelled words is translating the tree under the relabelled
lexicon. -/
theorem translate_map {L' : Type*} (lex : L' → Option (Σ ty, K ty)) (f : L → L')
    (t : Tree C L) : translate Γ lex (t.map f) = translate Γ (lex ∘ f) t := by
  induction t using Tree.rec' with
  | terminal c w => rfl
  | phrase c k cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp)
    | [t₁, t₂] =>
      simp only [Tree.map_phrase, List.map, translate_phrase_binary, ih t₁ (by simp),
        ih t₂ (by simp)]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih => simp only [Tree.map_bind, translate_bind, ih]
  | junk l cs hj _ =>
    have hmap : (cs.map (Tree.map f)).map RoseTree.value =
        (cs.map RoseTree.value).map (Tree.Label.mapWord f) := by
      simp only [List.map_map]
      exact List.map_congr_left fun t _ ↦ Tree.value_map f t
    rw [Tree.map_rose, translate_junk _ (by rw [hmap, Tree.Label.licenses_mapWord]; exact hj),
      translate_junk _ hj]

end Translate

/-! ### Tree interpretation -/

section TreeInterp

variable {C : Type}

/-- The denotation of a tree under an assignment, by the composition principles of
[heim-kratzer-1998]. A terminal denotes its leaf interpretation, a non-branching node its
daughter's denotation, a binary node its daughters' denotations composed by the mode their types
select, a trace the value of its index, and a binder the abstraction over its index when the
effect has a distributor. It is the denotation of the tree's term with each word's denotation as
its constant. -/
def interp {E W : Type} {M : Type → Type} [Applicative M] {S : Sorts} [Distributive M]
    {L : Type*} (lex : L → Option (Denotation E W M S)) (g : Assignment E) (t : Tree C L) :
    Option (Denotation E W M S) :=
  (translate individualIndices (K := fun ty ↦ M (Ty.Domain E W ty S)) lex t).map (evalAt g)

/-- The denotation of a tree under a typing `Γ` of its indices and an assignment of values of
those types: a trace or binder of index `n` is a variable of type `Γ n`. -/
def interpWith {E W : Type} {M : Type → Type} [Applicative M] {S : Sorts} [Distributive M]
    {L : Type*} (Γ : ℕ → Ty) (lex : L → Option (Denotation E W M S))
    (g : ∀ n, Ty.Domain E W (Γ n) S) (t : Tree C L) : Option (Denotation E W M S) :=
  (translate Γ (K := fun ty ↦ M (Ty.Domain E W ty S)) lex t).map (evalAt g)

theorem interp_eq_interpWith {E W : Type} {M : Type → Type} [Applicative M] {S : Sorts}
    [Distributive M] {L : Type*} (lex : L → Option (Denotation E W M S)) (g : Assignment E)
    (t : Tree C L) : interp lex g t = interpWith individualIndices lex g t := rfl

end TreeInterp

/-! ### Reduction lemmas

One `@[simp]` lemma per constructor, so that a derivation reduces by `simp` toward its
composed denotation. -/

section Reduction

variable {C : Type} {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M] [Distributive M]
  {L : Type*}

private theorem map_evalAt_combine (g : Assignment E)
    (t₁ t₂ : Option (Σ ty, Term individualIndices (fun ty ↦ M (Ty.Domain E W ty S)) ty)) :
    (t₁.bind fun d₁ ↦ t₂.bind fun d₂ ↦ Mode.combine? (fun m l r ↦ .comp m l r) d₁ d₂).map
        (evalAt g) =
      (t₁.map (evalAt g)).bind fun d₁ ↦ (t₂.map (evalAt g)).bind fun d₂ ↦
        Mode.combine? Mode.evalM d₁ d₂ := by
  rcases t₁ with _ | ⟨τ₁, u₁⟩
  · rfl
  rcases t₂ with _ | ⟨τ₂, u₂⟩
  · rfl
  simp only [Option.bind_some, Option.map_some, Mode.combine?]
  rcases τ₁.mode? τ₂ with _ | ⟨τ, m⟩ <;> rfl

variable (lex : L → Option (Denotation E W M S)) (g : Assignment E)

@[simp] theorem interp_terminal (c : C) (w : L) :
    interp lex g (.terminal c w : Tree C L) = lex w := by
  simp only [interp, translate_terminal]
  cases lex w <;> rfl

@[simp] theorem interp_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    interp lex g (.phrase c k (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    interp lex g (.phrase c k (t₁ :: t₂ :: [])) = ((interp lex g t₁).bind fun d₁ ↦
      (interp lex g t₂).bind fun d₂ ↦ Mode.combine? Mode.evalM d₁ d₂) :=
  map_evalAt_combine g _ _

@[simp] theorem interp_trace (n : ℕ) (c : C) :
    interp lex g (.trace n c : Tree C L) = some ⟨.e, pure (g n)⟩ := rfl

@[simp] theorem interp_bind (n : ℕ) (c : C) (body : Tree C L) :
    interp lex g (.bind n c body) =
      (interp lex g body).bind fun d ↦
        some ⟨.fn .e d.1, distribute fun x ↦ valueAt d.1 d.2 (interp lex (g[n ↦ x]) body)⟩ := by
  simp only [interp, translate_bind]
  rcases translate individualIndices (K := fun ty ↦ M (Ty.Domain E W ty S)) lex body with _ | ⟨τ, b⟩
  · rfl
  · simp [evalAt, valueAt]

variable (Γ : ℕ → Ty) (g' : ∀ n, Ty.Domain E W (Γ n) S)

@[simp] theorem interpWith_trace (n : ℕ) (c : C) :
    interpWith Γ lex g' (.trace n c : Tree C L) = some ⟨Γ n, pure (g' n)⟩ := rfl

@[simp] theorem interpWith_terminal (c : C) (w : L) :
    interpWith Γ lex g' (.terminal c w : Tree C L) = lex w := by
  simp only [interpWith, translate_terminal, Option.map_map]
  cases lex w <;> rfl

@[simp] theorem interpWith_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    interpWith Γ lex g' (.phrase c k (t₁ :: t₂ :: [])) = (interpWith Γ lex g' t₁).bind fun d₁ ↦
      (interpWith Γ lex g' t₂).bind fun d₂ ↦ Mode.combine? Mode.evalM d₁ d₂ := by
  simp only [interpWith, translate_phrase_binary]
  rcases translate Γ (K := fun ty ↦ M (Ty.Domain E W ty S)) lex t₁ with _ | ⟨τ₁, u₁⟩
  · rfl
  rcases translate Γ (K := fun ty ↦ M (Ty.Domain E W ty S)) lex t₂ with _ | ⟨τ₂, u₂⟩
  · rfl
  simp only [Option.bind_some, Option.map_some, Mode.combine?, Option.map_map]
  rfl

@[simp] theorem interpWith_bind (n : ℕ) (c : C) (body : Tree C L) :
    interpWith Γ lex g' (.bind n c body) =
      (interpWith Γ lex g' body).bind fun d ↦
        some ⟨Γ n ⇒ d.1,
          distribute fun x ↦ valueAt d.1 d.2 (interpWith Γ lex (g'[n ↦ x]) body)⟩ := by
  simp only [interpWith, translate_bind]
  rcases translate Γ (K := fun ty ↦ M (Ty.Domain E W ty S)) lex body with _ | ⟨τ, b⟩
  · rfl
  · simp [evalAt, valueAt]

theorem interp_junk {l : Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ Tree.Label.Licenses l (cs.map RoseTree.value)) :
    interp lex g (RoseTree.node l cs) = none := by
  simp only [interp, translate_junk _ h, Option.map_none]

end Reduction

/-! ### The type of a tree

The type a tree composes to is a function of the types of its leaves: `ty?` is the type of the
term the tree translates to under a lexicon of bare types, and `interp_map_fst` is the agreement.
Interpretability is therefore decided by the types of the leaves alone. -/

section TreeTyping

variable {C : Type} {Γ : ℕ → Ty} {L : Type*}

/-- The type a tree composes to under a typing `Γ` of its indices, from the types `lexTy` gives its
leaves: the type of the term it translates to. -/
def ty? (Γ : ℕ → Ty) (lexTy : L → Option Ty) (t : Tree C L) : Option Ty :=
  (translate Γ (K := fun _ ↦ Unit) (fun w ↦ (lexTy w).map fun ty ↦ ⟨ty, ()⟩) t).map (·.1)

variable {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M] [Distributive M]
  {lexTy : L → Option Ty} {lex : L → Option (Denotation E W M S)}

/-- The type of a tree's denotation is the type `ty?` computes from the types of its leaves. -/
theorem interp_map_fst (h : ∀ w, (lex w).map (·.1) = lexTy w) (g : Assignment E)
    (t : Tree C L) :
    (interp lex g t).map (·.1) =
      ty? individualIndices lexTy t := by
  rw [interp, Option.map_map]
  exact translate_map_fst lex (fun w ↦ by simp [← h w, Option.map_map, Function.comp_def]) t

theorem isSome_interp (h : ∀ w, (lex w).map (·.1) = lexTy w) (g : Assignment E)
    (t : Tree C L) :
    (interp lex g t).isSome =
      (ty? individualIndices lexTy t).isSome := by
  rw [← interp_map_fst h g t, Option.isSome_map]

end TreeTyping

/-! ### Assignment dependence and free variables

[heim-kratzer-1998]'s theorems on variable binding (§5.4.2): the denotation of a tree depends
on the assignment only at the traces free in it. Interpretability and the type do not depend on
the assignment at all (`interp_map_fst_congr`). With total assignments, their theorem (9) is
`interp_update_of_not_mem_freeIndices`: a tree with no free occurrence of `i` has the same
denotation under an assignment and its modification at `i`. Their (10) is `interp_congr_of_closed`:
a closed tree has the same denotation under every assignment. -/

section FreeVariables

variable {C : Type} {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M] [Distributive M]
  {L : Type*} (lex : L → Option (Denotation E W M S))

theorem interp_map_fst_congr (g g' : Assignment E) (t : Tree C L) :
    (interp lex g t).map (·.1) = (interp lex g' t).map (·.1) := by
  rw [interp_map_fst (fun _ ↦ rfl), interp_map_fst (fun _ ↦ rfl)]

/-- Assignments agreeing on the traces free in a tree give it the same denotation, the
coincidence theorem ([heim-kratzer-1998] §5.4.2). -/
theorem interp_congr_of_agree {g g' : Assignment E} {t : Tree C L}
    (h : ∀ i ∈ t.freeIndices, g i = g' i) : interp lex g t = interp lex g' t := by
  rcases ht : translate individualIndices (K := fun ty ↦ M (Ty.Domain E W ty S)) lex t with
    _ | ⟨τ, u⟩
  · simp [interp, ht]
  · simp only [interp, ht, Option.map_some]
    exact congrArg (fun v ↦ some (⟨τ, v⟩ : Denotation E W M S))
      (Term.evalM_congr_of_agree (fun c ↦ c) u fun n hn ↦ h n (freeVars_translate lex ht hn))

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
(`readings_eq_of_choice`), and a binary phrase's readings are the pointwise compositions of its
daughters' (`mem_readings_phrase_binary`). -/

section Readings

variable {C : Type} {L : Type*} {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M]
  [Distributive M]

theorem interp_map {L' : Type*} (lex : L' → Option (Denotation E W M S)) (f : L → L')
    (g : Assignment E) (t : Tree C L) : interp lex g (t.map f) = interp (lex ∘ f) g t := by
  simp only [interp, translate_map]

variable (lex : L → Set (Denotation E W M S)) (g : Assignment E)

/-- The readings of a tree when each word has a set of readings are the denotations of the trees
obtained by resolving each occurrence of a word to one of its readings. -/
def readings (t : Tree C L) : Set (Denotation E W M S) :=
  {d | ∃ r : Tree C {p : L × Denotation E W M S // p.2 ∈ lex p.1},
    r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d}

variable {lex g}

theorem exists_resolution_of_interp {choice : L → Option (Denotation E W M S)} {t : Tree C L}
    {d : Denotation E W M S} (h : interp choice g t = some d) :
    ∃ r : Tree C {p : L × Denotation E W M S // choice p.1 = some p.2},
      r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d := by
  induction t using Tree.rec' generalizing g d with
  | terminal c w =>
    rw [interp_terminal] at h
    exact ⟨.terminal c ⟨(w, d), h⟩, rfl, by rw [interp_terminal]⟩
  | phrase c k cs ih =>
    match cs with
    | [] => exact absurd h (by simp [interp, translate])
    | [t] =>
      obtain ⟨r, hr, hd⟩ := ih t (by simp) h
      exact ⟨.phrase c k (r :: []), by simp [hr], hd⟩
    | [t₁, t₂] =>
      rw [interp_phrase_binary] at h
      obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, hd₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨r₂, hr₂, hd₂⟩ := ih t₂ (by simp) h₂
      exact ⟨.phrase c k (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
        by rw [interp_phrase_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩
    | _ :: _ :: _ :: _ => exact absurd h (by simp [interp, translate])
  | trace n c => exact ⟨.trace n c, rfl, h⟩
  | bind n c body ih =>
    rw [interp_bind] at h
    obtain ⟨⟨τ, probe⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hd⟩ := ih hb
    have hres : ∀ g', interp choice g' body = interp (fun p ↦ some p.1.2) g' r := fun g' ↦ by
      rw [← hr, interp_map]
      exact congrFun (congrFun (congrArg _ (funext fun p ↦ p.2)) g') r
    refine ⟨.bind n c r, by simp [hr], ?_⟩
    rw [interp_bind, hd, Option.bind_some]
    simpa only [hres] using h
  | junk l cs hj _ => exact absurd h (by rw [interp_junk _ _ hj]; simp)

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
  obtain ⟨p, rfl, rfl⟩ := Tree.map_eq_terminal_iff.1 hr
  cases Option.some.inj hd
  exact p.2

@[simp] theorem readings_trace (n : ℕ) (c : C) :
    readings lex g (.trace n c) = {⟨.e, pure (g n)⟩} := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ ⟨.trace n c, rfl, h ▸ rfl⟩⟩
  obtain rfl := Tree.map_eq_trace_iff.1 hr
  exact (Option.some.inj hd).symm

/-- A binary phrase's readings are the pointwise compositions of its daughters'. -/
theorem mem_readings_phrase_binary {c : C} {k : PhraseKind} {t₁ t₂ : Tree C L}
    {d : Denotation E W M S} :
    d ∈ readings lex g (.phrase c k (t₁ :: t₂ :: [])) ↔
      ∃ d₁ ∈ readings lex g t₁, ∃ d₂ ∈ readings lex g t₂,
        Mode.combine? Mode.evalM d₁ d₂ = some d := by
  constructor
  · rintro ⟨r, hr, hd⟩
    obtain ⟨cs, rfl, hcs⟩ := Tree.map_eq_phrase_iff.1 hr
    obtain ⟨r₁, cs₁, rfl, rfl, hcs₁⟩ := List.map_eq_cons_iff.mp hcs
    obtain ⟨r₂, cs₂, rfl, rfl, hcs₂⟩ := List.map_eq_cons_iff.mp hcs₁
    obtain rfl := List.map_eq_nil_iff.mp hcs₂
    rw [interp_phrase_binary] at hd
    obtain ⟨d₁, h₁, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨d₂, h₂, hd⟩ := Option.bind_eq_some_iff.mp hd
    exact ⟨d₁, ⟨r₁, rfl, h₁⟩, d₂, ⟨r₂, rfl, h₂⟩, hd⟩
  · rintro ⟨d₁, ⟨r₁, hr₁, hd₁⟩, d₂, ⟨r₂, hr₂, hd₂⟩, h⟩
    exact ⟨.phrase c k (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
      by rw [interp_phrase_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩

/-- A binder's readings interpret it over a resolution of its body, which reads each occurrence
the same way at every value of the bound variable. -/
theorem mem_readings_bind {n : ℕ} {c : C} {t : Tree C L} {d : Denotation E W M S} :
    d ∈ readings lex g (.bind n c t) ↔ ∃ r : Tree C {p : L × Denotation E W M S // p.2 ∈ lex p.1},
      r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g (.bind n c r) = some d := by
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun ⟨r, hr, hd⟩ ↦ ⟨.bind n c r, by rw [Tree.map_bind, hr], hd⟩⟩
  obtain ⟨b, rfl, hb⟩ := Tree.map_eq_bind_iff.1 hr
  exact ⟨b, hb, hd⟩

end Readings

/-! ### Readings and the set effect

Resolving each occurrence of a word before interpretation, as `readings` does, chooses one reading
for every entity an abstraction ranges over. Under the set effect an abstraction chooses a reading
at each entity (`SetM.mem_run_distribute`), so the readings of a tree are among the values the
engine computes for it under the set effect. -/

section SetEffect

variable {C : Type} {L : Type*} {E W : Type} {S : Sorts}

/-- The readings of a word under a set-valued lexicon: its denotations at each of its values. -/
def wordReadings (lex : L → Option (Denotation E W SetM S)) (w : L) : Set (Denotation E W Id S) :=
  {d | ∃ X, lex w = some ⟨d.1, X⟩ ∧ d.2 ∈ X.run}

/-- The readings of a tree under the readings of a set-valued lexicon's words are among the values
the engine computes for it under the set effect. -/
theorem mem_interp_setM_of_mem_readings (lex : L → Option (Denotation E W SetM S))
    (g : Assignment E) {t : Tree C L} {d : Denotation E W Id S}
    (hd : d ∈ readings (wordReadings lex) g t) :
    ∃ X, interp lex g t = some ⟨d.1, X⟩ ∧ d.2 ∈ X.run := by
  obtain ⟨r, rfl, hr⟩ := hd
  rw [interp_map]
  simp only [interp] at hr ⊢
  obtain ⟨⟨τ, u⟩, hu, hev⟩ := Option.map_eq_some_iff.1 hr
  have hrel : ∀ (p : {p : L × Denotation E W Id S //
      p.2 ∈ wordReadings lex p.1}) d',
      (lex ∘ fun x ↦ x.1.1) p = some d' →
        ∃ c, some p.1.2 = some ⟨d'.1, c⟩ ∧ c ∈ SetM.run d'.2 := by
    rintro ⟨⟨w, ⟨τ', c⟩⟩, X, hX, hc⟩ d' hd'
    simp only [Function.comp_apply, hX, Option.some.injEq] at hd'
    subst hd'
    exact ⟨c, rfl, hc⟩
  have htypes : (translate individualIndices (lex ∘ fun x ↦ x.1.1) r).map (·.1) = some τ := by
    rw [← translate_map_fst (lex := fun p ↦ some p.1.2) (fun p ↦ ?_) r, hu]
    · rfl
    · obtain ⟨⟨w, ⟨τ', c⟩⟩, X, hX, -⟩ := p
      simp [hX]
  obtain ⟨⟨τ', u'⟩, hu', hτ⟩ := Option.map_eq_some_iff.1 htypes
  subst hτ
  obtain ⟨u₀, hu₀, hR⟩ :=
    translate_rel (R := fun _ c c' ↦ c ∈ SetM.run c') (fun p ↦ some p.1.2) hrel r hu'
  rw [hu, Option.some.injEq, Sigma.mk.injEq] at hu₀
  obtain ⟨-, hu₀⟩ := hu₀
  obtain rfl := eq_of_heq hu₀
  have hmem := hR.mem_run_evalM g
  simp only [evalAt, Term.evalM_id] at hev
  subst hev
  exact ⟨_, by rw [hu', Option.map_some], hmem⟩

end SetEffect


/-! ### Interpretation is evaluation of the translation -/

section Translation

variable {C : Type} {K : Ty → Type*} {L : Type*} {E W : Type} {S : Sorts}

/-- Interpreting a tree whose words denote what an interpretation `I` of their constants gives
is evaluating the tree's term under `I`. -/
theorem interp_eq_eval_translate (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S)
    (lex : L → Option (Σ ty, K ty)) (g : Assignment E) (t : Tree C L) :
    interp (M := Id) (fun w ↦ (lex w).map fun c ↦ ⟨c.1, I c.2⟩) g t =
      (translate individualIndices lex t).map fun d ↦ ⟨d.1, d.2.eval I g⟩ := by
  simp only [interp, translate_map_const]
  cases translate individualIndices lex t with
  | none => rfl
  | some d => simp [evalAt, Term.eval_map]

end Translation

/-! ### Truth -/

section Truth

variable {C : Type} {L : Type*} {E W : Type}

/-- A tree holds under a lexicon and an assignment when it composes to a true truth value. -/
def HoldsAt (lex : L → Option (Denotation E W)) (g : Assignment E) (t : Tree C L) : Prop :=
  ∃ p, interp lex g t = some ⟨.t, p⟩ ∧ p

/-- A tree holds under a typing `Γ` of its indices, a lexicon and an assignment of values of those
types when it composes to a true truth value. -/
def HoldsAtWith (Γ : ℕ → Ty) (lex : L → Option (Denotation E W)) (g : ∀ n, Ty.Domain E W (Γ n))
    (t : Tree C L) : Prop :=
  ∃ p, interpWith Γ lex g t = some ⟨.t, p⟩ ∧ p

theorem holdsAtWith_iff {Γ : ℕ → Ty} {lex : L → Option (Denotation E W)}
    {g : ∀ n, Ty.Domain E W (Γ n)} {t : Tree C L} {p : Prop}
    (h : interpWith Γ lex g t = some ⟨.t, p⟩) : HoldsAtWith Γ lex g t ↔ p := by
  simp [HoldsAtWith, h]

end Truth

end PhraseStructure.Tree
