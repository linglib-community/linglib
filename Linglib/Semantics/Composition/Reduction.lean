module

public import Linglib.Semantics.Composition.Model
public import Linglib.Core.ModelTheory.Binders
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.Tactic.FinCases

/-!
# The first-order fragment of type-driven composition

`compileFO` compiles the first-order fragment of Heim and Kratzer's trees, after Quantifier
Raising, into mathlib `FirstOrder.Language.Formula`s. Whenever it succeeds, the denotation
`Tree.interp` composes is equivalent to the realization of the compiled formula over the model,
the same triangle `Semantics/Dynamic/DRS/Reduction.lean` proves for DRT. First-order consequence
between compiled formulas then transfers to entailment between trees in every composition model.

## Main definitions

* `FOWords`, `Model.lexiconFO`: the logical vocabulary over a naming-map lexicon.
* `FOWords.FreshFor`, `LexNaming.Disjoint`: the well-formedness conditions the compiler needs.
* `compileFO`: the partial compiler.
* `HoldsAt`: truth of a tree at a world under an assignment.

## Main results

* `interp_compileFO`, `holdsAt_iff_realize`: the engine's denotation of a compiled tree is the
  realization of its formula.
* `holdsAt_of_models`: first-order consequence yields entailment in every composition model.
* `models_imp_iff_entails`, `holdsAt_compactness`: tree entailment is first-order consequence
  over the empty theory, and families of trees satisfy compactness.

## Implementation notes

Trace indices are the formulas' free variables (`ℕ`), so a binder index is the variable name and
the assignment update `g[n ↦ x]` is `Function.update`. Quantifiers bind exactly one trace, so
closure uses the computable singleton binders `Formula.all₁` and `Formula.ex₁` (mathlib's
`iAlls` and `iExs` are noncomputable). *Most* and the other proportional determiners are not
first-order definable, as Barwise and Cooper showed, so they lie outside the compiled fragment
and `compileFO` is partial.

## References

* [heim-kratzer-1998]
* [barwise-cooper-1981]
-/

@[expose] public section

universe u v

namespace HeimKratzer

open FirstOrder Language
open FirstOrder.Language.Formula (all₁ ex₁)
open Montague
open HeimKratzer.Tree
open PhraseStructure (Tree)

variable {L : Language.{u, v}}

/-! ### The logical vocabulary -/

/-- Word forms for the compiled logical vocabulary, parameterizable per
fragment/language. -/
structure FOWords where
  every : String := "every"
  some_ : String := "some"
  no : String := "no"
  not_ : String := "not"
  and_ : String := "and"
  or_ : String := "or"

/-- The logical vocabulary's lexicon gives the quantifier words their denotations from
`Quantification` and the connectives their truth functions, with arguments flipped so that
`[t₁ [and t₂]]` composes to `⟦t₁⟧ ∧ ⟦t₂⟧`. -/
def FOWords.lexicon (fw : FOWords) (E W : Type) : Lexicon E W := fun s ↦
  if s = fw.every then some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Quantifier.GQ.every⟩
  else if s = fw.some_ then some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Quantifier.GQ.some⟩
  else if s = fw.no then some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Quantifier.GQ.no⟩
  else if s = fw.not_ then some ⟨.t ⇒ .t, Not⟩
  else if s = fw.and_ then some ⟨.t ⇒ .t ⇒ .t, fun q p ↦ p ∧ q⟩
  else if s = fw.or_ then some ⟨.t ⇒ .t ⇒ .t, fun q p ↦ p ∨ q⟩
  else none

/-- A naming-map lexicon extended with the logical vocabulary. Content words
take priority; `FOWords.FreshFor` rules out collisions. -/
def Model.lexiconFO (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W) :
    Lexicon m.E m.W := fun s ↦
  m.lexiconAt nm w s <|> fw.lexicon m.E m.W s

/-- The logical word forms are fresh for the naming maps. -/
def FOWords.FreshFor (fw : FOWords) (nm : LexNaming L) : Prop :=
  ∀ s ∈ [fw.every, fw.some_, fw.no, fw.not_, fw.and_, fw.or_],
    nm.names s = none ∧ nm.preds₁ s = none ∧ nm.preds₂ s = none

/-- Each word form names at most one kind of symbol, so the compiler's
classification of a word agrees with the lexicon's lookup order. -/
structure LexNaming.Disjoint (nm : LexNaming L) : Prop where
  names_of_preds₁ : ∀ s R, nm.preds₁ s = some R → nm.names s = none
  names_of_preds₂ : ∀ s R, nm.preds₂ s = some R → nm.names s = none
  preds₁_of_preds₂ : ∀ s R, nm.preds₂ s = some R → nm.preds₁ s = none

/-! ### The compiler

Recognized (QR'd Heim-Kratzer) shapes: name/trace–verb predication with
optional object, sentence negation `[not t]`, sentence coordination
`[t₁ [and t₂]]`, and quantified clauses `[[Q N] [bind k body]]`. Everything
else — in particular *most* — is outside the fragment and compiles to
`none`. -/

/-- `compileTerm` compiles an entity subtree, a proper name or a trace, to a term. -/
def compileTerm (nm : LexNaming L) : Tree Unit String → Option (L.Term ℕ)
  | .terminal _ s => (nm.names s).map Constants.term
  | .trace k _ => some (Language.Term.var k)
  | _ => none

/-- `compilePred` compiles a predicate subtree applied to a subject term, either an
intransitive verb or a transitive verb with a name or trace as object. -/
def compilePred (nm : LexNaming L) (τ : L.Term ℕ) :
    Tree Unit String → Option (L.Formula ℕ)
  | .terminal _ v => (nm.preds₁ v).map fun R ↦ R.formula₁ τ
  | .node _ [.terminal _ v, obj] =>
      (nm.preds₂ v).bind fun R ↦
        (compileTerm nm obj).map fun τₒ ↦ R.formula₂ τ τₒ
  | _ => none

/-- `compileFO` compiles the first-order fragment of a tree to a formula with trace indices as
free variables, returning `none` outside the fragment. -/
def compileFO (fw : FOWords) (nm : LexNaming L) :
    Tree Unit String → Option (L.Formula ℕ)
  | .node _ [.terminal _ s, r] =>
      if s = fw.not_ then (compileFO fw nm r).map BoundedFormula.not
      else (nm.names s).bind fun c ↦ compilePred nm (Constants.term c) r
  | .node _ [.trace k _, r] => compilePred nm (Language.Term.var k) r
  | .node _ [.node _ [.terminal _ q, .terminal _ nw], .bind k _ body] =>
      (nm.preds₁ nw).bind fun R ↦
        (compileFO fw nm body).bind fun ψ ↦
          if q = fw.every then some (all₁ k ((R.formula₁ (Language.Term.var k)).imp ψ))
          else if q = fw.some_ then some (ex₁ k (R.formula₁ (Language.Term.var k) ⊓ ψ))
          else if q = fw.no then
            some (all₁ k ((R.formula₁ (Language.Term.var k)).imp ψ.not))
          else none
  | .node _ [l, .node _ [.terminal _ s, t₂] ] =>
      if s = fw.and_ then
        (compileFO fw nm l).bind fun φ₁ ↦
          (compileFO fw nm t₂).map fun φ₂ ↦ φ₁ ⊓ φ₂
      else if s = fw.or_ then
        (compileFO fw nm l).bind fun φ₁ ↦
          (compileFO fw nm t₂).map fun φ₂ ↦ φ₁ ⊔ φ₂
      else none
  | _ => none

/-! ### Lookup lemmas -/

/-- The six logical word forms are pairwise distinct. -/
def FOWords.Nodup (fw : FOWords) : Prop :=
  ([fw.every, fw.some_, fw.no, fw.not_, fw.and_, fw.or_] : List String).Nodup

section Lookups

variable (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W)

theorem Model.lexiconFO_names {s : String} {c : L.Constants}
    (h : nm.names s = some c) :
    m.lexiconFO fw nm w s = some ⟨.e, m.const c w⟩ := by
  simp [Model.lexiconFO, Model.lexiconAt, h]

theorem Model.lexiconFO_preds₁ {s : String} {R : L.Relations 1}
    (h : nm.preds₁ s = some R) (h₀ : nm.names s = none) :
    m.lexiconFO fw nm w s = some ⟨.e ⇒ .t, m.pred₁ext R w⟩ := by
  simp [Model.lexiconFO, Model.lexiconAt, h, h₀]

theorem Model.lexiconFO_preds₂ {s : String} {R : L.Relations 2}
    (h : nm.preds₂ s = some R) (h₀ : nm.names s = none)
    (h₁ : nm.preds₁ s = none) :
    m.lexiconFO fw nm w s = some ⟨.e ⇒ .e ⇒ .t, m.pred₂ext R w⟩ := by
  simp [Model.lexiconFO, Model.lexiconAt, h, h₀, h₁]

/-- At a word fresh for the naming maps, lookup falls through to the logical
vocabulary. -/
theorem Model.lexiconFO_fresh {s : String}
    (h₀ : nm.names s = none) (h₁ : nm.preds₁ s = none)
    (h₂ : nm.preds₂ s = none) :
    m.lexiconFO fw nm w s = fw.lexicon m.E m.W s := by
  simp [Model.lexiconFO, Model.lexiconAt, h₀, h₁, h₂]

end Lookups

namespace FOWords

variable {fw : FOWords}

private theorem nodup_ne (hnd : fw.Nodup) :
    (fw.some_ ≠ fw.every) ∧
    (fw.no ≠ fw.every ∧ fw.no ≠ fw.some_) ∧
    (fw.not_ ≠ fw.every ∧ fw.not_ ≠ fw.some_ ∧ fw.not_ ≠ fw.no) ∧
    (fw.and_ ≠ fw.every ∧ fw.and_ ≠ fw.some_ ∧ fw.and_ ≠ fw.no ∧
      fw.and_ ≠ fw.not_) ∧
    (fw.or_ ≠ fw.every ∧ fw.or_ ≠ fw.some_ ∧ fw.or_ ≠ fw.no ∧
      fw.or_ ≠ fw.not_ ∧ fw.or_ ≠ fw.and_) := by
  simp only [FOWords.Nodup, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15, -⟩ := hnd
  exact ⟨Ne.symm h1, ⟨Ne.symm h2, Ne.symm h6⟩, ⟨Ne.symm h3, Ne.symm h7, Ne.symm h10⟩,
    ⟨Ne.symm h4, Ne.symm h8, Ne.symm h11, Ne.symm h13⟩,
    ⟨Ne.symm h5, Ne.symm h9, Ne.symm h12, Ne.symm h14, Ne.symm h15⟩⟩

variable (E W : Type)

theorem lexicon_every :
    fw.lexicon E W fw.every
      = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Quantifier.GQ.every⟩ := by
  simp [FOWords.lexicon]

theorem lexicon_some (hnd : fw.Nodup) :
    fw.lexicon E W fw.some_
      = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Quantifier.GQ.some⟩ := by
  obtain ⟨h1, _, _, _, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1]

theorem lexicon_no (hnd : fw.Nodup) :
    fw.lexicon E W fw.no
      = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Quantifier.GQ.no⟩ := by
  obtain ⟨_, ⟨h1, h2⟩, _, _, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2]

theorem lexicon_not (hnd : fw.Nodup) :
    fw.lexicon E W fw.not_ = some ⟨.t ⇒ .t, Not⟩ := by
  obtain ⟨_, _, ⟨h1, h2, h3⟩, _, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2, h3]

theorem lexicon_and (hnd : fw.Nodup) :
    fw.lexicon E W fw.and_
      = some ⟨.t ⇒ .t ⇒ .t, fun q p ↦ p ∧ q⟩ := by
  obtain ⟨_, _, _, ⟨h1, h2, h3, h4⟩, _⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2, h3, h4]

theorem lexicon_or (hnd : fw.Nodup) :
    fw.lexicon E W fw.or_
      = some ⟨.t ⇒ .t ⇒ .t, fun q p ↦ p ∨ q⟩ := by
  obtain ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩⟩ := nodup_ne hnd
  simp [FOWords.lexicon, h1, h2, h3, h4, h5]

/-- Extract the naming-map-freshness triple for a logical word. -/
theorem FreshFor.at {nm : LexNaming L} (h : fw.FreshFor nm) {s : String}
    (hs : s ∈ [fw.every, fw.some_, fw.no, fw.not_, fw.and_, fw.or_]) :
    nm.names s = none ∧ nm.preds₁ s = none ∧ nm.preds₂ s = none :=
  h s hs

end FOWords

/-! ### Atoms at a model's world -/

section RealizeAt

variable (m : Model L) (w : m.W) (g : Assignment m.E)

/-- The realization of a unary atom `R(τ)` is the extension of `R` at the term's value. -/
theorem Model.realizeAt_rel₁ (R : L.Relations 1) (τ : L.Term ℕ) :
    (R.formula₁ τ).RealizeAt m.interp w g ↔ m.pred₁ext R w (τ.realizeAt m.interp w g) := by
  rw [Formula.realizeAt_rel₁, Matrix.cons_fin_one]
  rfl

/-- The realization of a binary atom `R(τ₁, τ₂)`, subject first, is the object-first extension
of `R` at the terms' values. -/
theorem Model.realizeAt_rel₂ (R : L.Relations 2) (τ₁ τ₂ : L.Term ℕ) :
    (R.formula₂ τ₁ τ₂).RealizeAt m.interp w g ↔
      m.pred₂ext R w (τ₂.realizeAt m.interp w g) (τ₁.realizeAt m.interp w g) := by
  rw [Formula.realizeAt_rel₂]
  exact iff_of_eq (congrArg _ (funext fun i ↦ by fin_cases i <;> rfl))

end RealizeAt

/-! ### Engine reduction helpers (at `M = Id`) -/

section EngineHelpers

variable {E W : Type}

/-- Forward FA at `Id`, with the applicative collapsed. -/
private theorem combine?_fn_left_id {σ τ : Ty} (f : Ty.Domain E W (σ ⇒ τ)) (x : Ty.Domain E W σ) :
    Mode.combine? Mode.evalM (⟨σ ⇒ τ, f⟩ : Denotation E W) ⟨σ, x⟩ = some ⟨τ, f x⟩ := by
  rw [Mode.combine?_fn_left]; rfl

/-- Backward functional application at `Id` applies a unary predicate to an entity subject. -/
private theorem combine?_e_et_id (x : Ty.Domain E W .e) (P : Ty.Domain E W (.e ⇒ .t)) :
    Mode.combine? Mode.evalM (⟨.e, x⟩ : Denotation E W) ⟨.e ⇒ .t, P⟩ = some ⟨.t, P x⟩ := by
  rw [Mode.combine?_fn_right]; rfl

/-- Backward functional application at `Id` applies a sentential operator to a sentence. -/
private theorem combine?_t_tt_id (p : Ty.Domain E W .t) (F : Ty.Domain E W (.t ⇒ .t)) :
    Mode.combine? Mode.evalM (⟨.t, p⟩ : Denotation E W) ⟨.t ⇒ .t, F⟩ = some ⟨.t, F p⟩ := by
  rw [Mode.combine?_fn_right]; rfl

private theorem predAbs_id_dist :
    PredAbs.dist? (M := Id) (E := E) (W := W) (D := ℝ) = some (fun _ f ↦ f) := rfl

/-- An `Iff` between truth values lifts through `some ⟨.t, ·⟩`. -/
private theorem some_t_congr {p q : Ty.Domain E W .t} (h : p ↔ q) :
    (some ⟨.t, p⟩ : Option (Denotation E W)) = some ⟨.t, q⟩ :=
  congrArg (fun r ↦ (some ⟨.t, r⟩ : Option (Denotation E W))) (propext h)

/-- Given the body's interpretation at the outer assignment, a `.bind` node at `Id` denotes an
entity predicate that agrees pointwise with the body at the updated assignments. -/
private theorem interp_bind_exists (lex : Lexicon E W) (g : Assignment E)
    (k : ℕ) (c : Unit) (body : Tree Unit String) {p : Ty.Domain E W .t}
    (hbody : Tree.interp lex g body = some ⟨.t, p⟩) :
    ∃ F : Ty.Domain E W (.e ⇒ .t),
      Tree.interp lex g (.bind k c body) = some ⟨.fn .e .t, F⟩ ∧
      ∀ (x : E) (px : Ty.Domain E W .t),
        Tree.interp lex (Function.update g k x) body = some ⟨.t, px⟩ →
        F x = px := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · rw [Tree.interp_bind, predAbs_id_dist, hbody]
    rfl
  · intro x px hx
    simp only [hx]
    rfl

end EngineHelpers

/-! ### Agreement -/

section Agreement

variable (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W)

/-- The engine's value of a compiled entity subtree is the realization of its term. -/
theorem interp_compileTerm (g : Assignment m.E) :
    ∀ {t : Tree Unit String} {τ : L.Term ℕ}, compileTerm nm t = some τ →
      Tree.interp (m.lexiconFO fw nm w) g t
        = some ⟨.e, τ.realizeAt m.interp w g⟩
  | .terminal _ s, τ, h => by
      simp only [compileTerm, Option.map_eq_some_iff] at h
      obtain ⟨c, hc, rfl⟩ := h
      rw [interp_terminal, m.lexiconFO_names fw nm w hc, Term.realizeAt_constants]
      rfl
  | .trace k _, τ, h => by
      simp only [compileTerm, Option.some.injEq] at h
      subst h
      rfl

/-- A subject term and a compiled predicate subtree compose to the realization of the compiled
atom. -/
theorem interp_compilePred (hdj : nm.Disjoint) (g : Assignment m.E)
    {subj : Tree Unit String} {τ : L.Term ℕ}
    (hsubj : compileTerm nm subj = some τ) :
    ∀ {r : Tree Unit String} {φ : L.Formula ℕ}, compilePred nm τ r = some φ →
      ∀ c : Unit,
        Tree.interp (m.lexiconFO fw nm w) g (.node c [subj, r])
          = some ⟨.t, φ.RealizeAt m.interp w g⟩
  | .terminal _ v, φ, h, c => by
      simp only [compilePred, Option.map_eq_some_iff] at h
      obtain ⟨R, hR, rfl⟩ := h
      rw [interp_node_binary, interp_compileTerm m fw nm w g hsubj, Option.bind_some,
        interp_terminal,
        m.lexiconFO_preds₁ fw nm w hR (hdj.names_of_preds₁ v R hR),
        Option.bind_some, combine?_e_et_id]
      exact some_t_congr (m.realizeAt_rel₁ w g R τ).symm
  | .node _ [.terminal _ v, obj], φ, h, c => by
      simp only [compilePred, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨R, hR, τₒ, hobj, rfl⟩ := h
      rw [interp_node_binary, interp_compileTerm m fw nm w g hsubj, Option.bind_some,
        interp_node_binary, interp_terminal,
        m.lexiconFO_preds₂ fw nm w hR (hdj.names_of_preds₂ v R hR)
          (hdj.preds₁_of_preds₂ v R hR),
        Option.bind_some,
        interp_compileTerm m fw nm w g hobj, Option.bind_some,
        combine?_fn_left_id, Option.bind_some, combine?_e_et_id]
      exact some_t_congr (m.realizeAt_rel₂ w g R τ τₒ).symm

/-- Composition of a quantified clause `[[Q N] [bind k body]]` from the
lexicon lookups of the quantifier and restrictor words and the `.bind`
node's interpretation. -/
private theorem interp_quantClause {g : Assignment m.E} {q nw : String}
    {Q : Ty.Domain m.E m.W ((.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t)}
    {N F : Ty.Domain m.E m.W (.e ⇒ .t)} {k : ℕ} {body : Tree Unit String}
    {a a₁ a₂ a₃ a₄ : Unit}
    (hQ : m.lexiconFO fw nm w q = some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, Q⟩)
    (hN : m.lexiconFO fw nm w nw = some ⟨.e ⇒ .t, N⟩)
    (hbind : Tree.interp (m.lexiconFO fw nm w) g (.bind k a₄ body)
      = some ⟨.fn .e .t, F⟩) :
    Tree.interp (m.lexiconFO fw nm w) g
        (.node a [.node a₁ [.terminal a₂ q, .terminal a₃ nw], .bind k a₄ body])
      = some ⟨.t, Q N F⟩ := by
  rw [interp_node_binary, interp_node_binary, interp_terminal, hQ, Option.bind_some,
    interp_terminal, hN,
    Option.bind_some, combine?_fn_left_id, Option.bind_some, hbind,
    Option.bind_some, combine?_fn_left_id]

/-- Whenever the compiler succeeds, the engine's denotation of the tree is the realization of
the compiled formula over the model at `w`. -/
theorem interp_compileFO (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) (t : Tree Unit String) :
    ∀ {φ : L.Formula ℕ} (g : Assignment m.E), compileFO fw nm t = some φ →
      Tree.interp (m.lexiconFO fw nm w) g t
        = some ⟨.t, φ.RealizeAt m.interp w g⟩ := by
  induction t using compileFO.induct fw with
  | case1 a a₁ r ih =>
    -- negation [not r]
    intro φ g h
    simp only [compileFO, ↓reduceIte, Option.map_eq_some_iff] at h
    obtain ⟨ψ, hψ, rfl⟩ := h
    have hfr₁ := hfr.at (s := fw.not_) (by simp)
    rw [interp_node_binary, interp_terminal,
      m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2,
      FOWords.lexicon_not m.E m.W hnd, Option.bind_some,
      ih g hψ, Option.bind_some, combine?_fn_left_id]
    congr 1
  | case2 a a₁ s r hs =>
    -- name-subject predication
    intro φ g h
    simp only [compileFO, ite_eq_right hs, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, hpred⟩ := h
    exact interp_compilePred m fw nm w hdj g
      (by simp [compileTerm, hc]) hpred a
  | case3 a k a₁ r =>
    -- trace-subject predication
    intro φ g h
    simp only [compileFO] at h
    exact interp_compilePred m fw nm w hdj g (by simp [compileTerm]) h a
  | case4 a a₁ a₂ q a₃ nw k a₄ body ih =>
    -- quantified clause [[Q N] [bind k body]]
    intro φ g h
    simp only [compileFO, Option.bind_eq_some_iff] at h
    obtain ⟨R, hR, ψ, hψ, hq⟩ := h
    obtain ⟨F, hbind, hF⟩ :=
      interp_bind_exists (m.lexiconFO fw nm w) g k a₄ body (ih g hψ)
    have hquant : ∀ x : m.E,
        F x = ψ.RealizeAt m.interp w (Function.update g k x) := fun x ↦
      hF x _ (ih (Function.update g k x) hψ)
    have hrestr : ∀ x : m.E,
        (Relations.formula₁ R (Language.Term.var k)).RealizeAt m.interp w (Function.update g k x)
          ↔ m.pred₁ext R w x := by
      intro x
      rw [m.realizeAt_rel₁, Term.realizeAt_var, Function.update_self]
    have hN := m.lexiconFO_preds₁ fw nm w hR (hdj.names_of_preds₁ _ _ hR)
    by_cases hq1 : q = fw.every
    · rw [ite_eq_left hq1] at hq
      cases hq
      subst hq1
      have hfr₁ := hfr.at (s := fw.every) (by simp)
      rw [interp_quantClause m fw nm w
        ((m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2).trans
          (FOWords.lexicon_every m.E m.W)) hN hbind]
      refine some_t_congr ?_
      rw [Formula.realizeAt_all₁]
      simp only [Quantifier.GQ.every, Formula.realizeAt_imp]
      exact forall_congr' fun x ↦
        imp_congr (hrestr x).symm (by rw [hquant x])
    · rw [ite_eq_right hq1] at hq
      by_cases hq2 : q = fw.some_
      · rw [ite_eq_left hq2] at hq
        cases hq
        subst hq2
        have hfr₁ := hfr.at (s := fw.some_) (by simp)
        rw [interp_quantClause m fw nm w
          ((m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2).trans
            (FOWords.lexicon_some m.E m.W hnd)) hN hbind]
        refine some_t_congr ?_
        rw [Formula.realizeAt_ex₁]
        simp only [Quantifier.GQ.some, Formula.realizeAt_inf]
        exact exists_congr fun x ↦
          and_congr (hrestr x).symm (by rw [hquant x])
      · rw [ite_eq_right hq2] at hq
        by_cases hq3 : q = fw.no
        · rw [ite_eq_left hq3] at hq
          cases hq
          subst hq3
          have hfr₁ := hfr.at (s := fw.no) (by simp)
          rw [interp_quantClause m fw nm w
            ((m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2).trans
              (FOWords.lexicon_no m.E m.W hnd)) hN hbind]
          refine some_t_congr ?_
          rw [Formula.realizeAt_all₁]
          simp only [Quantifier.GQ.no, Formula.realizeAt_imp,
            Formula.realizeAt_not]
          exact forall_congr' fun x ↦
            imp_congr (hrestr x).symm (by rw [hquant x])
        · rw [ite_eq_right hq3] at hq
          simp at hq
  | case5 a l a₁ a₂ t₂ hl₁ hl₂ ihl iht =>
    -- coordination [l [and t₂]]
    intro φ g h
    simp only [compileFO, ↓reduceIte, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    have hfr₁ := hfr.at (s := fw.and_) (by simp)
    rw [interp_node_binary, ihl g h₁, Option.bind_some, interp_node_binary,
      interp_terminal,
      m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2,
      FOWords.lexicon_and m.E m.W hnd, Option.bind_some,
      iht g h₂, Option.bind_some, combine?_fn_left_id, Option.bind_some,
      combine?_t_tt_id]
    refine some_t_congr ?_
    rw [Formula.realizeAt_inf]
  | case6 a l a₁ a₂ t₂ hl₁ hl₂ hne ihl iht =>
    -- coordination [l [or t₂]]
    intro φ g h
    simp only [compileFO, ite_eq_right hne, ↓reduceIte, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    have hfr₁ := hfr.at (s := fw.or_) (by simp)
    rw [interp_node_binary, ihl g h₁, Option.bind_some, interp_node_binary,
      interp_terminal,
      m.lexiconFO_fresh fw nm w hfr₁.1 hfr₁.2.1 hfr₁.2.2,
      FOWords.lexicon_or m.E m.W hnd, Option.bind_some,
      iht g h₂, Option.bind_some, combine?_fn_left_id, Option.bind_some,
      combine?_t_tt_id]
    refine some_t_congr ?_
    rw [Formula.realizeAt_sup]
  | case7 a l a₁ a₂ s t₂ hl₁ hl₂ hs₁ hs₂ =>
    intro φ g h
    simp only [compileFO, ite_eq_right hs₁, ite_eq_right hs₂] at h
    simp at h
  | case8 t hex₁ hex₂ hex₃ hex₄ =>
    intro φ g h
    rw [compileFO.eq_def] at h
    split at h
    all_goals
      first
        | simp at h
        | exact (hex₁ _ _ _ _ rfl).elim
        | exact (hex₂ _ _ _ _ rfl).elim
        | exact (hex₃ _ _ _ _ _ _ _ _ _ rfl).elim
        | exact (hex₄ _ _ _ _ _ _ rfl).elim

end Agreement

/-! ### Truth and consequence transfer -/

section Consequence

variable (m : Model L) (fw : FOWords) (nm : LexNaming L) (w : m.W)

/-- A tree holds at a model's world under an assignment when it composes to a true truth
value. -/
def HoldsAt (lex : Lexicon m.E m.W) (g : Assignment m.E)
    (t : Tree Unit String) : Prop :=
  ∃ p, Tree.interp lex g t = some ⟨.t, p⟩ ∧ p

theorem holdsAt_iff_realize (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {t : Tree Unit String} {φ : L.Formula ℕ}
    (h : compileFO fw nm t = some φ) (g : Assignment m.E) :
    HoldsAt m (m.lexiconFO fw nm w) g t ↔ φ.RealizeAt m.interp w g := by
  constructor
  · rintro ⟨p, hp, htrue⟩
    have := (interp_compileFO m fw nm w hnd hfr hdj t g h).symm.trans hp
    simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at this
    rw [this]
    exact htrue
  · intro hr
    exact ⟨_, interp_compileFO m fw nm w hnd hfr hdj t g h, hr⟩

/-- First-order consequence between compiled formulas yields entailment between the trees in
every composition model, at every world and under every assignment. -/
theorem holdsAt_of_models (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {t₁ t₂ : Tree Unit String} {φ₁ φ₂ : L.Formula ℕ}
    (h₁ : compileFO fw nm t₁ = some φ₁) (h₂ : compileFO fw nm t₂ = some φ₂)
    (hmod : ∀ (M : Type) (S : L.Structure M) (v : ℕ → M),
      @Formula.Realize L M S ℕ φ₁ v → @Formula.Realize L M S ℕ φ₂ v)
    (g : Assignment m.E) :
    HoldsAt m (m.lexiconFO fw nm w) g t₁ →
      HoldsAt m (m.lexiconFO fw nm w) g t₂ := by
  rw [holdsAt_iff_realize m fw nm w hnd hfr hdj h₁ g,
    holdsAt_iff_realize m fw nm w hnd hfr hdj h₂ g]
  exact hmod m.E (m.interp w) g

end Consequence

end HeimKratzer

namespace HeimKratzer

/-- The default logical vocabulary is pairwise distinct. -/
theorem FOWords.nodup_default : ({} : FOWords).Nodup := by
  unfold FOWords.Nodup
  decide

end HeimKratzer

/-! ### Bridge to mathlib `Theory` consequence

For universe-0 languages, composition models and mathlib's bundled models
coincide: tree entailment over nonempty-domain composition models *is*
first-order consequence over the empty theory, and compactness transfers
to families of trees. (`ModelType` requires nonempty carriers, hence the
nonempty-domain restriction — standard in the GQ literature.) -/

namespace HeimKratzer

open FirstOrder Language
open PhraseStructure (Tree)

section TheoryBridge

variable {L₀ : Language.{0, 0}} (fw : FOWords) (nm : LexNaming L₀)

/-- A first-order structure as a one-world composition model. -/
def Model.ofStructure (M : Type) (S : L₀.Structure M) : Model L₀ :=
  ⟨M, Unit, fun _ ↦ S⟩

private theorem modelEmpty (M : Type) [L₀.Structure M] : M ⊨ (∅ : L₀.Theory) :=
  ⟨fun _φ hφ ↦ absurd hφ (by simp)⟩

/-- Over composition models with nonempty domains, entailment between compiled trees coincides
with mathlib's `⊨ᵇ` over the empty theory. -/
theorem models_imp_iff_entails (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {t₁ t₂ : Tree Unit String} {φ₁ φ₂ : L₀.Formula ℕ}
    (h₁ : compileFO fw nm t₁ = some φ₁) (h₂ : compileFO fw nm t₂ = some φ₂) :
    (∅ : L₀.Theory) ⊨ᵇ φ₁.imp φ₂ ↔
      ∀ (m : Model L₀), Nonempty m.E → ∀ (w : m.W) (g : Assignment m.E),
        HoldsAt m (m.lexiconFO fw nm w) g t₁ →
          HoldsAt m (m.lexiconFO fw nm w) g t₂ := by
  constructor
  · intro hmod m hne w g
    rw [holdsAt_iff_realize m fw nm w hnd hfr hdj h₁ g,
      holdsAt_iff_realize m fw nm w hnd hfr hdj h₂ g]
    let := m.interp w
    have : m.E ⊨ (∅ : L₀.Theory) := inferInstance
    have : Nonempty m.E := hne
    have h := hmod ⟨m.E⟩ g default
    exact BoundedFormula.realize_imp.mp h
  · intro hent M v xs
    have hxs : xs = default := funext fun i ↦ i.elim0
    subst hxs
    rw [BoundedFormula.realize_imp]
    have := hent (Model.ofStructure M M.struc) M.nonempty' () v
    rw [holdsAt_iff_realize (Model.ofStructure M M.struc) fw nm ()
        hnd hfr hdj h₁ v,
      holdsAt_iff_realize (Model.ofStructure M M.struc) fw nm ()
        hnd hfr hdj h₂ v] at this
    exact this

/-! ### Closed trees as sentences, and compactness -/

/-- A family of closed fragment trees is jointly satisfiable in a composition model with a
nonempty domain iff every finite subfamily is. The nontrivial direction is mathlib's compactness
theorem `Theory.isSatisfiable_iff_isFinitelySatisfiable`. -/
theorem holdsAt_compactness (hnd : fw.Nodup) (hfr : fw.FreshFor nm)
    (hdj : nm.Disjoint) {ι : Type} (trees : ι → Tree Unit String)
    (φs : ι → L₀.Formula ℕ)
    (hc : ∀ i, compileFO fw nm (trees i) = some (φs i))
    (hcl : ∀ i, (φs i).freeVarFinset = ∅) :
    (∃ (m : Model L₀) (_ : Nonempty m.E) (w : m.W) (g : Assignment m.E),
        ∀ i, HoldsAt m (m.lexiconFO fw nm w) g (trees i)) ↔
      ∀ s : Finset ι,
        ∃ (m : Model L₀) (_ : Nonempty m.E) (w : m.W) (g : Assignment m.E),
          ∀ i ∈ s, HoldsAt m (m.lexiconFO fw nm w) g (trees i) := by
  constructor
  · rintro ⟨m, hne, w, g, hall⟩ s
    exact ⟨m, hne, w, g, fun i _ ↦ hall i⟩
  · intro hfin
    have hsat : Theory.IsSatisfiable
        (L := L₀) (Set.range fun i ↦ (φs i).toSentence (hcl i)) := by
      rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
      intro T₀ hT₀
      classical
      choose f hf using fun (x : T₀) ↦ hT₀ x.2
      obtain ⟨m, hne, w, g, hs⟩ := hfin (Finset.univ.image f)
      let := m.interp w
      have : Nonempty m.E := hne
      have : m.E ⊨ (T₀ : L₀.Theory) := by
        refine ⟨fun ψ hψ ↦ ?_⟩
        obtain ⟨x, rfl⟩ : ∃ x : T₀, (φs (f x)).toSentence (hcl (f x)) = ψ :=
          ⟨⟨ψ, hψ⟩, hf ⟨ψ, hψ⟩⟩
        rw [Formula.realize_toSentence (v := g)]
        have hold := hs (f x) (Finset.mem_image_of_mem f (Finset.mem_univ x))
        rw [holdsAt_iff_realize m fw nm w hnd hfr hdj (hc (f x)) g] at hold
        exact hold
      exact Theory.Model.isSatisfiable m.E
    obtain ⟨N⟩ := hsat
    let := N.struc
    have := N.nonempty'
    refine ⟨Model.ofStructure N N.struc, N.nonempty', (),
      fun _ ↦ Classical.arbitrary N, fun i ↦ ?_⟩
    rw [holdsAt_iff_realize (Model.ofStructure N N.struc) fw nm ()
      hnd hfr hdj (hc i) _]
    have : (N : Type) ⊨ (φs i).toSentence (hcl i) :=
      N.is_model.realize_of_mem _ (Set.mem_range_self i)
    exact (Formula.realize_toSentence (M := (N : Type)) (φs i) (hcl i)
      (fun _ ↦ Classical.arbitrary N)).mp this

end TheoryBridge

end HeimKratzer
