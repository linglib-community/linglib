module

public import Linglib.Semantics.Composition.Model
public import Linglib.Semantics.Composition.Tree
public import Linglib.Core.ModelTheory.Binders
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.Tactic.FinCases

/-!
# The first-order fragment of type-driven composition

A logical form built only from names, predicates, the determiners *every*, *some* and *no*, and
the truth-functional connectives reads back to a first-order formula with the same truth
conditions, [soundly](##realizes_readback). So
[a tree holds exactly where its readback is true](##holdsAt_iff_realizeAt),
[entailment between trees is first-order consequence](##models_imp_iff_entails), and
[families of trees satisfy compactness](##holdsAt_compactness).

## Main definitions

* `FirstOrderConstant`, `FirstOrderConstant.interp`: the first-order constants and their
  denotations in a composition model at a world; `Model.lexicon` interprets the words of a
  fragment through them.
* `Ty.SyntacticDomain`: the syntactic model, by type and number of bound variables.
* `Term.readback`, `Term.toFormula`: the readback of a logical form.
* `Ty.Realizes`: the logical relation between the syntactic and the standard model.

## Implementation notes

The syntactic model is built from mathlib's terms and bounded formulas, and indexed by the
number of bound variables in scope, and gives truth values
and functions at every larger number, so a determiner binds the next de Bruijn variable of
`BoundedFormula` without computing a fresh name. Formulas are never carried to more bound
variables, since `BoundedFormula.castLE` keeps the index an inner quantifier binds. *Most* is not
first-order definable, as Barwise and Cooper showed, so it is not a first-order constant.

## References

* [heim-kratzer-1998]
* [barwise-cooper-1981]
* [montague-1973]
-/

@[expose] public section

universe u v w

namespace Montague

open FirstOrder Language

/-! ### First-order constants -/

section Constants

variable {L : Language.{u, v}}

variable (L) in
/-- The first-order constants over a signature `L` are its constant symbols at type `e`, its
unary and binary relation symbols at `e ⇒ t` and `e ⇒ e ⇒ t`, the determiners *every*, *some*
and *no*, negation, and conjunction and disjunction. -/
inductive FirstOrderConstant : Ty → Type (max u v) where
  | name (c : L.Constants) : FirstOrderConstant (.e)
  | rel₁ (R : L.Relations 1) : FirstOrderConstant (.e ⇒ .t)
  | rel₂ (R : L.Relations 2) : FirstOrderConstant (.e ⇒ .e ⇒ .t)
  | every : FirstOrderConstant Ty.det
  | some : FirstOrderConstant Ty.det
  | no : FirstOrderConstant Ty.det
  | neg : FirstOrderConstant (.t ⇒ .t)
  | conj : FirstOrderConstant (.t ⇒ .t ⇒ .t)
  | disj : FirstOrderConstant (.t ⇒ .t ⇒ .t)

/-- At a world of a composition model a symbol denotes what the structure there gives it, the
determiners denote those of `Quantification`, and conjunction and disjunction take the second
conjunct first, as a right-branching coordination `[t₁ [and t₂]]` composes. -/
def FirstOrderConstant.interp (m : Model L) (w : m.W) :
    {ty : Ty} → FirstOrderConstant L ty → Ty.Domain m.E m.W ty
  | _, .name c => m.const c w
  | _, .rel₁ R => m.pred₁ R w
  | _, .rel₂ R => m.pred₂ R w
  | _, .every => Quantifier.GQ.every
  | _, .some => Quantifier.GQ.some
  | _, .no => Quantifier.GQ.no
  | _, .neg => Not
  | _, .conj => fun q p ↦ p ∧ q
  | _, .disj => fun q p ↦ p ∨ q

/-- The lexicon a composition model induces at a world from a translation of words into
first-order constants. -/
def Model.lexicon {X : Type*} (m : Model L) (words : X → Option (Σ ty, FirstOrderConstant L ty))
    (w : m.W) : X → Option (Denotation m.E m.W) :=
  fun x ↦ (words x).map fun c ↦ ⟨c.1, c.2.interp m w⟩

end Constants

/-! ### The syntactic model

The syntactic model takes the function and relation symbols of the signature in one universe,
so that terms and bounded formulas share it. -/

/-- In the syntactic model of the types over the free variables `α`, with `n` bound variables in
scope, an entity is a term, and a truth value and a function are given at every larger number of
bound variables, as a bounded formula and as a function on the values there. The other sorts,
worlds among them, are trivial, so an intension is a function that ignores its world. -/
abbrev Ty.SyntacticDomain (L : Language.{u, u}) (α : Type w) : Ty → ℕ → Type (max u w)
  | .e, i => L.Term (α ⊕ Fin i)
  | .t, i => ∀ k, i ≤ k → L.BoundedFormula α k
  | .fn σ τ, i => ∀ k, i ≤ k → Ty.SyntacticDomain L α σ k → Ty.SyntacticDomain L α τ k
  | _, _ => PUnit

/-- A predicate of the syntactic model applied to the next bound variable, with `j + 1` bound
variables in scope, as a determiner applies its restrictor and scope to the variable it binds. -/
def Ty.SyntacticDomain.applyNext {L : Language.{u, u}} {α : Type w} {k j : ℕ}
    (P : Ty.SyntacticDomain L α (.e ⇒ .t) k) (h : k ≤ j) : L.BoundedFormula α (j + 1) :=
  P (j + 1) (h.trans j.le_succ) (Language.Term.var (.inr (Fin.last j))) (j + 1) le_rfl

/-- The logical relation between the syntactic model and the standard one over a structure,
under a valuation `v` of the free variables and `xs` of the `n` bound ones. A term realizes the
entity it denotes, a formula realizes a truth value with `xs` extended to any larger number of
bound variables, a function realizes a function that sends realized arguments to realized values
with `xs` so extended. -/
def Ty.Realizes {L : Language.{u, u}} {α : Type w} {M W : Type} {Q : Sorts} (S : L.Structure M)
    (v : α → M) :
    (ty : Ty) → (n : ℕ) → (Fin n → M) → Ty.SyntacticDomain L α ty n → Ty.Domain M W ty Q → Prop
  | .e, _, xs, x, a => letI := S; x.realize (Sum.elim v xs) = a
  | .t, i, xs, φ, p => ∀ k (hk : i ≤ k) (ys : Fin k → M), ys ∘ Fin.castLE hk = xs →
      (letI := S; (φ k hk).Realize v ys ↔ p)
  | .fn σ τ, i, xs, f, f' => ∀ k (hk : i ≤ k) (ys : Fin k → M), ys ∘ Fin.castLE hk = xs →
      ∀ x a, Ty.Realizes S v σ k ys x a → Ty.Realizes S v τ k ys (f k hk x) (f' a)
  | _, _, _, _, _ => True

section SyntacticModel

variable {L : Language.{u, u}}

section Readback

variable {α : Type w}

/-- In the syntactic model a mode applies at the current number of bound variables, and predicate
modification and event identification conjoin pointwise. -/
def Mode.readback {n : ℕ} : ∀ {σ₁ σ₂ τ : Ty},
    Mode σ₁ σ₂ τ → Ty.SyntacticDomain L α σ₁ n → Ty.SyntacticDomain L α σ₂ n →
      Ty.SyntacticDomain L α τ n
  | _, _, _, .functionalLeft, f, a => f n le_rfl a
  | _, _, _, .functionalRight, a, f => f n le_rfl a
  | _, _, _, .predicateModification, p, q => fun k hk x j hj ↦ p k hk x j hj ⊓ q k hk x j hj
  | _, _, _, .eventIdentificationLeft, f, p => fun k hk x j hj e i hi ↦
      f k hk x j hj e i hi ⊓ p j (hk.trans hj) e i hi
  | _, _, _, .eventIdentificationRight, p, f => fun k hk x j hj e i hi ↦
      f k hk x j hj e i hi ⊓ p j (hk.trans hj) e i hi
  | _, _, _, .mapRight _, _, _ => PUnit.unit
  | _, _, _, .mapLeft _, _, _ => PUnit.unit
  | _, _, _, .ap _, _, _ => PUnit.unit
  | _, _, _, .join _, _, _ => PUnit.unit
  | _, _, _, .unitRight m, a, b => m.readback (fun k hk _ ↦ a k hk PUnit.unit) b
  | _, _, _, .unitLeft m, a, b => m.readback a fun k hk _ ↦ b k hk PUnit.unit

/-- In the syntactic model a symbol is an atom, a determiner binds the next bound variable where
its scope is complete, and negation and the connectives are the formula connectives. -/
def FirstOrderConstant.readback : {ty : Ty} → (n : ℕ) → FirstOrderConstant L ty →
    Ty.SyntacticDomain L α ty n
  | _, _, .name c => c.term
  | _, _, .rel₁ R => fun _ _ x _ hj ↦ R.boundedFormula₁ (x.relabel (Sum.map id (Fin.castLE hj)))
  | _, _, .rel₂ R => fun _ _ y _ hk x _ hj ↦
      R.boundedFormula₂ (x.relabel (Sum.map id (Fin.castLE hj)))
        (y.relabel (Sum.map id (Fin.castLE (hk.trans hj))))
  | _, _, .every => fun _ _ P _ hk Q _ hj ↦ ((P.applyNext (hk.trans hj)).imp (Q.applyNext hj)).all
  | _, _, .some => fun _ _ P _ hk Q _ hj ↦ (P.applyNext (hk.trans hj) ⊓ Q.applyNext hj).ex
  | _, _, .no => fun _ _ P _ hk Q _ hj ↦
      ((P.applyNext (hk.trans hj)).imp (Q.applyNext hj).not).all
  | _, _, .neg => fun _ _ φ j hj ↦ (φ j hj).not
  | _, _, .conj => fun _ _ q _ hk p j hj ↦ p j hj ⊓ q j (hk.trans hj)
  | _, _, .disj => fun _ _ q _ hk p j hj ↦ p j hj ⊔ q j (hk.trans hj)

/-- The readback of a term in the syntactic model, given readbacks of its constants, with `n`
bound variables in scope and a valuation `ρ` of its variables in terms. An abstraction reads back
to a function at every larger number of bound variables, under `ρ` carried there and updated at
its variable. -/
def Term.readback {K : Ty → Type*} (R : ∀ {ty : Ty} (n : ℕ), K ty → Ty.SyntacticDomain L α ty n)
    (n : ℕ) (ρ : ℕ → L.Term (α ⊕ Fin n)) :
    {ty : Ty} → Term individualIndices K ty → Ty.SyntacticDomain L α ty n
  | _, .const c => R n c
  | _, .var i => ρ i
  | _, .lam i b => fun k hk x ↦
      readback R k (Function.update (fun j ↦ (ρ j).relabel (Sum.map id (Fin.castLE hk))) i x) b
  | _, .comp μ l r => μ.readback (readback R n ρ l) (readback R n ρ r)

end Readback

/-- The first-order formula a logical form over the first-order constants reads back to, whose
free variables are the logical form's variables. -/
def Term.toFormula (u : Term individualIndices (FirstOrderConstant L) .t) : L.Formula ℕ :=
  u.readback FirstOrderConstant.readback 0 (fun i ↦ Language.Term.var (.inl i)) 0 le_rfl

/-! ### Soundness of the readback -/

section Soundness

variable {α : Type w} {M W : Type} {Q : Sorts}

variable (S : L.Structure M) (v : α → M)

private theorem comp_castLE_trans {k₁ k₂ k₃ : ℕ} {h₁ : k₁ ≤ k₂} {h₂ : k₂ ≤ k₃} {xs : Fin k₁ → M}
    {ys : Fin k₂ → M} {zs : Fin k₃ → M} (hys : ys ∘ Fin.castLE h₁ = xs)
    (hzs : zs ∘ Fin.castLE h₂ = ys) : zs ∘ Fin.castLE (h₁.trans h₂) = xs := by
  subst hys hzs
  rfl

private theorem snoc_comp_castLE {k j : ℕ} {h : k ≤ j} {h' : k ≤ j + 1} (zs : Fin j → M)
    (a : M) : (Fin.snoc zs a : Fin (j + 1) → M) ∘ Fin.castLE h' = zs ∘ Fin.castLE h :=
  funext fun i ↦ Fin.snoc_castSucc (α := fun _ ↦ M) (p := zs) (x := a) (i := Fin.castLE h i)

private theorem realize_relabel_castLE {n k : ℕ} (hk : n ≤ k) (x : L.Term (α ⊕ Fin n))
    (ys : Fin k → M) :
    letI := S
    (x.relabel (Sum.map id (Fin.castLE hk))).realize (Sum.elim v ys) =
      x.realize (Sum.elim v (ys ∘ Fin.castLE hk)) := by
  rw [Term.realize_relabel, Sum.elim_comp_map, Function.comp_id]

private theorem realize_applyNext {k j : ℕ} {ys : Fin k → M}
    {P : Ty.SyntacticDomain L α (.e ⇒ .t) k}
    {P' : Ty.Domain M W (.e ⇒ .t) Q} (hP : Ty.Realizes S v (.e ⇒ .t) k ys P P') (h : k ≤ j)
    {zs : Fin j → M} (hzs : zs ∘ Fin.castLE h = ys) (a : M) :
    letI := S
    (P.applyNext h).Realize v (Fin.snoc zs a) ↔ P' a :=
  hP _ _ _ ((snoc_comp_castLE zs a).trans hzs) _ a (by simp [Ty.Realizes]) _ le_rfl _ rfl

/-- A composition mode preserves the logical relation. -/
theorem Mode.realizes_readback {σ₁ σ₂ τ : Ty} (μ : Mode σ₁ σ₂ τ) {n : ℕ} {xs : Fin n → M}
    {a : Ty.SyntacticDomain L α σ₁ n} {b : Ty.SyntacticDomain L α σ₂ n}
    {a' : Ty.Domain M W σ₁ Q} {b' : Ty.Domain M W σ₂ Q}
    (ha : Ty.Realizes S v σ₁ n xs a a') (hb : Ty.Realizes S v σ₂ n xs b b') :
    Ty.Realizes S v τ n xs (μ.readback a b) (μ.eval a' b') := by
  let := S
  induction μ with
  | mapRight _ _ | mapLeft _ _ | ap _ _ | join _ _ => trivial
  | unitRight _ ih =>
    exact ih (fun k hk ys hys _ x _ ↦ ha k hk ys hys PUnit.unit (Eff.pure _ x) trivial) hb
  | unitLeft _ ih =>
    exact ih ha fun k hk ys hys _ x _ ↦ hb k hk ys hys PUnit.unit (Eff.pure _ x) trivial
  | functionalLeft => exact ha n le_rfl xs rfl b b' hb
  | functionalRight => exact hb n le_rfl xs rfl a a' ha
  | predicateModification =>
    intro k hk ys hys x c hx j hj zs hzs
    simp only [Mode.readback, Mode.eval, BoundedFormula.realize_inf,
      Modifier.intersective_apply]
    exact and_congr (ha k hk ys hys x c hx j hj zs hzs) (hb k hk ys hys x c hx j hj zs hzs)
  | eventIdentificationLeft =>
    intro k hk ys hys x c hx j hj zs hzs e d he i hi us hus
    simp only [Mode.readback, Mode.eval, BoundedFormula.realize_inf,
      ArgumentStructure.eventIdentification]
    exact and_congr (ha k hk ys hys x c hx j hj zs hzs e d he i hi us hus)
      (hb j (hk.trans hj) zs (comp_castLE_trans hys hzs) e d he i hi us hus)
  | eventIdentificationRight =>
    intro k hk ys hys x c hx j hj zs hzs e d he i hi us hus
    simp only [Mode.readback, Mode.eval, BoundedFormula.realize_inf,
      ArgumentStructure.eventIdentification]
    exact and_congr (hb k hk ys hys x c hx j hj zs hzs e d he i hi us hus)
      (ha j (hk.trans hj) zs (comp_castLE_trans hys hzs) e d he i hi us hus)

/-- When the readbacks of the constants realize their denotations, the readback of a term under
a valuation of its variables realizes the term's denotation under the assignment that valuation
realizes. This is the fundamental lemma of the logical relation. -/
theorem Term.realizes_readback {K : Ty → Type*}
    {R : ∀ {ty : Ty} (n : ℕ), K ty → Ty.SyntacticDomain L α ty n}
    {I : ∀ {ty : Ty}, K ty → Ty.Domain M W ty Q}
    (hR : ∀ {ty : Ty} (c : K ty) (n : ℕ) (xs : Fin n → M), Ty.Realizes S v ty n xs (R n c) (I c))
    {ty : Ty} (u : Term individualIndices K ty) {n : ℕ} {ρ : ℕ → L.Term (α ⊕ Fin n)}
    {xs : Fin n → M}
    {g : Assignment M} (hρ : ∀ i, Ty.Realizes (W := W) (Q := Q) S v .e n xs (ρ i) (g i)) :
    Ty.Realizes S v ty n xs (u.readback R n ρ) (u.eval I g) := by
  let := S
  induction u generalizing n ρ xs g with
  | const c => exact hR c n xs
  | var i => exact hρ i
  | lam i b ih =>
    intro k hk ys hys x a hx
    refine ih fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hji
    · simpa using hx
    · simp only [Function.update_of_ne hji]
      exact (realize_relabel_castLE S v hk (ρ j) ys).trans (hys ▸ hρ j)
  | comp μ l r ihl ihr => exact μ.realizes_readback S v (ihl hρ) (ihr hρ)

/-- The readbacks of the first-order constants realize their denotations in a composition
model at a world. -/
theorem FirstOrderConstant.realizes_readback (m : Model L) (w : m.W) (v : α → m.E) {ty : Ty}
    (c : FirstOrderConstant L ty) (n : ℕ) (xs : Fin n → m.E) :
    Ty.Realizes (m.interp w) v ty n xs (FirstOrderConstant.readback n c) (c.interp m w) := by
  let := m.interp w
  cases c with
  | name c => exact Term.realize_constants
  | rel₁ R =>
    intro k hk ys hys x a hx j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp, Model.pred₁,
      BoundedFormula.realize_rel₁, realize_relabel_castLE (m.interp w) v, hzs]
    rw [show x.realize (Sum.elim v ys) = a from hx, Matrix.cons_fin_one]
  | rel₂ R =>
    intro k₁ hk₁ ys₁ hys₁ y b hy k₂ hk₂ ys₂ hys₂ x a hx j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp, Model.pred₂,
      BoundedFormula.realize_rel₂, realize_relabel_castLE (m.interp w) v,
      comp_castLE_trans hys₂ hzs, hzs]
    rw [show x.realize (Sum.elim v ys₂) = a from hx, show y.realize (Sum.elim v ys₁) = b from hy]
    exact iff_of_eq (congrArg _ (funext fun i ↦ by fin_cases i <;> rfl))
  | every =>
    intro k₁ hk₁ ys₁ hys₁ P P' hP k₂ hk₂ ys₂ hys₂ Q Q' hQ j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp, Quantifier.GQ.every,
      BoundedFormula.realize_all, BoundedFormula.realize_imp]
    exact forall_congr' fun a ↦ imp_congr
      (realize_applyNext _ v hP _ (comp_castLE_trans hys₂ hzs) a)
      (realize_applyNext _ v hQ hj hzs a)
  | some =>
    intro k₁ hk₁ ys₁ hys₁ P P' hP k₂ hk₂ ys₂ hys₂ Q Q' hQ j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp, Quantifier.GQ.some,
      BoundedFormula.realize_ex, BoundedFormula.realize_inf]
    exact exists_congr fun a ↦ and_congr
      (realize_applyNext _ v hP _ (comp_castLE_trans hys₂ hzs) a)
      (realize_applyNext _ v hQ hj hzs a)
  | no =>
    intro k₁ hk₁ ys₁ hys₁ P P' hP k₂ hk₂ ys₂ hys₂ Q Q' hQ j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp, Quantifier.GQ.no,
      BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_not]
    exact forall_congr' fun a ↦ imp_congr
      (realize_applyNext _ v hP _ (comp_castLE_trans hys₂ hzs) a)
      (not_congr (realize_applyNext _ v hQ hj hzs a))
  | neg =>
    intro k hk ys hys φ p hφ j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp,
      BoundedFormula.realize_not]
    exact not_congr (hφ j hj zs hzs)
  | conj =>
    intro k₁ hk₁ ys₁ hys₁ q q' hq k₂ hk₂ ys₂ hys₂ p p' hp j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp,
      BoundedFormula.realize_inf]
    exact and_congr (hp j hj zs hzs) (hq j (hk₂.trans hj) zs (comp_castLE_trans hys₂ hzs))
  | disj =>
    intro k₁ hk₁ ys₁ hys₁ q q' hq k₂ hk₂ ys₂ hys₂ p p' hp j hj zs hzs
    simp only [FirstOrderConstant.readback, FirstOrderConstant.interp,
      BoundedFormula.realize_sup]
    exact or_congr (hp j hj zs hzs) (hq j (hk₂.trans hj) zs (comp_castLE_trans hys₂ hzs))

/-- A first-order logical form denotes, at a world of a composition model and under an
assignment, the realization of its readback there. -/
theorem Term.realizeAt_toFormula (m : Model L) (w : m.W)
    (u : Term individualIndices (FirstOrderConstant L) .t)
    (g : Assignment m.E) :
    u.toFormula.RealizeAt m.interp w g ↔ u.eval (FirstOrderConstant.interp m w) g :=
  Term.realizes_readback (m.interp w) g (FirstOrderConstant.realizes_readback m w g) u
    (n := 0) (ρ := fun i ↦ Language.Term.var (.inl i)) (xs := default) (g := g) (fun _ ↦ rfl) 0
    le_rfl default (Subsingleton.elim _ _)

end Soundness

end SyntacticModel

/-- A first-order structure as a one-world composition model. -/
def Model.ofStructure {L : Language.{0, 0}} (M : Type) (S : L.Structure M) : Model L :=
  ⟨M, Unit, fun _ ↦ S⟩

end Montague

namespace PhraseStructure.Tree

open FirstOrder Language
open Montague

/-! ### Trees -/

section Readback

variable {L : Language.{u, u}} {C : Type} {X : Type*}

variable {words : X → Option (Σ ty, FirstOrderConstant L ty)}

theorem holdsAt_iff_eval (m : Model L) (w : m.W) {t : Tree C X}
    {u : Term individualIndices (FirstOrderConstant L) .t}
    (h : Tree.translate individualIndices words t = some ⟨.t, u⟩)
    (g : Assignment m.E) :
    HoldsAt (m.lexicon words w) g t ↔ u.eval (FirstOrderConstant.interp m w) g := by
  unfold HoldsAt Model.lexicon
  rw [Tree.interp_eq_eval_translate (FirstOrderConstant.interp m w), h]
  simp

/-- A tree that translates to a logical form of type `t` holds where the readback of the
logical form is realized. -/
theorem holdsAt_iff_realizeAt (m : Model L) (w : m.W) {t : Tree C X}
    {u : Term individualIndices (FirstOrderConstant L) .t}
    (h : Tree.translate individualIndices words t = some ⟨.t, u⟩)
    (g : Assignment m.E) :
    HoldsAt (m.lexicon words w) g t ↔ u.toFormula.RealizeAt m.interp w g :=
  (holdsAt_iff_eval m w h g).trans (Term.realizeAt_toFormula m w u g).symm

/-- First-order consequence between the readbacks of two trees yields entailment between the
trees in every composition model, at every world and under every assignment. -/
theorem holdsAt_of_models {t₁ t₂ : Tree C X}
    {u₁ u₂ : Term individualIndices (FirstOrderConstant L) .t}
    (h₁ : Tree.translate individualIndices words t₁ = some ⟨.t, u₁⟩)
    (h₂ : Tree.translate individualIndices words t₂ = some ⟨.t, u₂⟩)
    (hmod : ∀ (M : Type) (S : L.Structure M) (v : ℕ → M),
      @Formula.Realize L M S ℕ u₁.toFormula v → @Formula.Realize L M S ℕ u₂.toFormula v)
    (m : Model L) (w : m.W) (g : Assignment m.E) :
    HoldsAt (m.lexicon words w) g t₁ → HoldsAt (m.lexicon words w) g t₂ := by
  rw [holdsAt_iff_realizeAt m w h₁, holdsAt_iff_realizeAt m w h₂]
  exact hmod m.E (m.interp w) g

end Readback

/-! ### Consequence and compactness

For universe-0 languages, composition models and mathlib's bundled models coincide: entailment
between trees over composition models with nonempty domains is first-order consequence over the
empty theory, and compactness transfers to families of trees. Mathlib's `ModelType` has nonempty
carriers, hence the restriction to nonempty domains, which is standard in the study of
generalized quantifiers. -/

section Compactness

variable {L₀ : Language.{0, 0}} {C : Type} {X : Type*}
  {words : X → Option (Σ ty, FirstOrderConstant L₀ ty)}

private theorem modelEmpty (M : Type) [L₀.Structure M] : M ⊨ (∅ : L₀.Theory) :=
  ⟨fun _φ hφ ↦ absurd hφ (by simp)⟩

/-- Over composition models with nonempty domains, entailment between two trees is mathlib's
`⊨ᵇ` between their readbacks over the empty theory. -/
theorem models_imp_iff_entails {t₁ t₂ : Tree C X}
    {u₁ u₂ : Term individualIndices (FirstOrderConstant L₀) .t}
    (h₁ : Tree.translate individualIndices words t₁ = some ⟨.t, u₁⟩)
    (h₂ : Tree.translate individualIndices words t₂ = some ⟨.t, u₂⟩) :
    (∅ : L₀.Theory) ⊨ᵇ u₁.toFormula.imp u₂.toFormula ↔
      ∀ (m : Model L₀), Nonempty m.E → ∀ (w : m.W) (g : Assignment m.E),
        HoldsAt (m.lexicon words w) g t₁ → HoldsAt (m.lexicon words w) g t₂ := by
  constructor
  · intro hmod m hne w g
    rw [holdsAt_iff_realizeAt m w h₁, holdsAt_iff_realizeAt m w h₂]
    let := m.interp w
    have : m.E ⊨ (∅ : L₀.Theory) := inferInstance
    have : Nonempty m.E := hne
    exact BoundedFormula.realize_imp.mp (hmod ⟨m.E⟩ g default)
  · intro hent M v xs
    obtain rfl : xs = default := funext fun i ↦ i.elim0
    rw [BoundedFormula.realize_imp]
    have := hent (Model.ofStructure M M.struc) M.nonempty' () v
    rwa [holdsAt_iff_realizeAt (Model.ofStructure M M.struc) () h₁,
      holdsAt_iff_realizeAt (Model.ofStructure M M.struc) () h₂] at this

/-- A family of trees whose readbacks are closed is jointly true in a composition model with a
nonempty domain iff every finite subfamily is. The nontrivial direction is mathlib's compactness
theorem `Theory.isSatisfiable_iff_isFinitelySatisfiable`. -/
theorem holdsAt_compactness {ι : Type} {trees : ι → Tree C X}
    {us : ι → Term individualIndices (FirstOrderConstant L₀) .t}
    (hc : ∀ i, Tree.translate individualIndices words (trees i) = some ⟨.t, us i⟩)
    (hcl : ∀ i, (us i).toFormula.freeVarFinset = ∅) :
    (∃ (m : Model L₀) (_ : Nonempty m.E) (w : m.W) (g : Assignment m.E),
        ∀ i, HoldsAt (m.lexicon words w) g (trees i)) ↔
      ∀ s : Finset ι,
        ∃ (m : Model L₀) (_ : Nonempty m.E) (w : m.W) (g : Assignment m.E),
          ∀ i ∈ s, HoldsAt (m.lexicon words w) g (trees i) := by
  constructor
  · rintro ⟨m, hne, w, g, hall⟩ s
    exact ⟨m, hne, w, g, fun i _ ↦ hall i⟩
  · intro hfin
    have hsat : Theory.IsSatisfiable
        (L := L₀) (Set.range fun i ↦ (us i).toFormula.toSentence (hcl i)) := by
      rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
      intro T₀ hT₀
      classical
      choose f hf using fun (x : T₀) ↦ hT₀ x.2
      obtain ⟨m, hne, w, g, hs⟩ := hfin (Finset.univ.image f)
      let := m.interp w
      have : Nonempty m.E := hne
      have : m.E ⊨ (T₀ : L₀.Theory) := by
        refine ⟨fun ψ hψ ↦ ?_⟩
        obtain ⟨x, rfl⟩ : ∃ x : T₀, (us (f x)).toFormula.toSentence (hcl (f x)) = ψ :=
          ⟨⟨ψ, hψ⟩, hf ⟨ψ, hψ⟩⟩
        rw [Formula.realize_toSentence (v := g)]
        have hold := hs (f x) (Finset.mem_image_of_mem f (Finset.mem_univ x))
        rwa [holdsAt_iff_realizeAt m w (hc (f x)) g] at hold
      exact Theory.Model.isSatisfiable m.E
    obtain ⟨N⟩ := hsat
    let := N.struc
    have := N.nonempty'
    refine ⟨Model.ofStructure N N.struc, N.nonempty', (), fun _ ↦ Classical.arbitrary N,
      fun i ↦ ?_⟩
    rw [holdsAt_iff_realizeAt (Model.ofStructure N N.struc) () (hc i)]
    have : (N : Type) ⊨ (us i).toFormula.toSentence (hcl i) :=
      N.is_model.realize_of_mem _ (Set.mem_range_self i)
    exact (Formula.realize_toSentence (M := (N : Type)) (us i).toFormula (hcl i)
      (fun _ ↦ Classical.arbitrary N)).mp this

end Compactness


end PhraseStructure.Tree
