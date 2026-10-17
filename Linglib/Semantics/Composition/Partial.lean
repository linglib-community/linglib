module

public import Mathlib.Data.PFun
public import Linglib.Semantics.Composition.Tree

/-!
# Partial interpretation

This file is Heim and Kratzer's composition engine on partial denotations. A function
denotes a partial function, mathlib's `PFun`, whose domain is the definedness condition the
book attaches to a lexical entry, and a node denotes a `Part` value of its type, defined when
its daughters are and the function among them is defined at its argument. Functional
Application in either order and Predicate Modification are the modes; a trace denotes the value
of its index and a binder abstracts over its index, the abstract being a partial function that
is undefined wherever the body is. Predicate Abstraction therefore needs no distributor, and the
undefined value is the abstract's own fallback, not a probe.

The book's distinction between uninterpretability and presupposition failure (§4.4.4) is the
difference between the engine returning no denotation and returning an undefined one:
`Uninterpretable` is decided by the types of the leaves alone (`uninterpretable_congr`), and
`PresupFailure` asks after the denotations. The definite article is the book's Fregean entry
(`the`), defined on the predicates true of exactly one individual.

## Main declarations

* `Ty.PDomain` and `PDenotation` are the partial domains and denotations.
* `Partial.interp` is the engine, with the modes `Partial.applyForward?`, `Partial.applyBackward?`
  and `Partial.predicateModification?`, and `Partial.interpBinary` trying them in order.
* `Partial.Uninterpretable` and `Partial.PresupFailure` are the two ways of lacking a value, and
  `Partial.interp_map_fst_congr` shows the first depends on the leaves' types alone.
* `Partial.the` is the definite article, with `Partial.the_dom` its definedness condition.
* `Ty.Lifts` and `Denotation.Lifts` relate a total denotation to a partial one lifting it, and
  `Partial.interp_lifts` shows that on a lexicon lifting a total one the partial engine's
  defined values lift the pure engine's, so such a lexicon has no presupposition failure
  (`Partial.not_presupFailure_of_lifts`). `Ty.Domain.toPartial` is the lift at a first-order
  type.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

namespace Montague

/-- Partial denotation domains, as `Ty.Domain` but with functions the partial functions `→.`,
whose domain is a lexical entry's definedness condition. -/
abbrev Ty.PDomain (E W : Type) (ty : Ty) (D : Type := ℝ) : Type :=
  match ty with
  | .e => E
  | .t => Prop
  | .d => D
  | .n => ℕ
  | .v => Empty
  | .s => Empty
  | .fn a b => Ty.PDomain E W a D →. Ty.PDomain E W b D
  | .intens a => W →. Ty.PDomain E W a D

/-- A partial denotation is a semantic type with a possibly undefined value in its partial
domain. -/
abbrev PDenotation (E W : Type) (D : Type := ℝ) : Type :=
  (ty : Ty) × Part (Ty.PDomain E W ty D)

end Montague

namespace HeimKratzer

open Montague

namespace Partial

open PhraseStructure Tree
open scoped Assignment

variable {E W D : Type}

/-! ### Composition modes -/

/-- Forward functional application, the function being the left daughter. The node is defined
when both daughters are and the function is defined at the argument. -/
def applyForward? (df da : PDenotation E W D) : Option (PDenotation E W D) :=
  match hf : df.1 with
  | .fn σ τ =>
    if ha : σ = da.1 then
      let f : Part (Ty.PDomain E W (σ ⇒ τ) D) := hf ▸ df.2
      let a : Part (Ty.PDomain E W σ D) := ha ▸ da.2
      some ⟨τ, f.bind fun fv ↦ a.bind fv⟩
    else none
  | _ => none

/-- Backward functional application, the function being the right daughter. -/
def applyBackward? (da df : PDenotation E W D) : Option (PDenotation E W D) :=
  match hf : df.1 with
  | .fn σ τ =>
    if ha : σ = da.1 then
      let f : Part (Ty.PDomain E W (σ ⇒ τ) D) := hf ▸ df.2
      let a : Part (Ty.PDomain E W σ D) := ha ▸ da.2
      some ⟨τ, f.bind fun fv ↦ a.bind fv⟩
    else none
  | _ => none

/-- Predicate modification conjoins two partial predicates, the conjunction being defined where
both are. -/
def predicateModification? (d₁ d₂ : PDenotation E W D) : Option (PDenotation E W D) :=
  match h₁ : d₁.1, h₂ : d₂.1 with
  | .fn .e .t, .fn .e .t =>
    let p : Part (Ty.PDomain E W (.e ⇒ .t) D) := h₁ ▸ d₁.2
    let q : Part (Ty.PDomain E W (.e ⇒ .t) D) := h₂ ▸ d₂.2
    some ⟨.fn .e .t, p.bind fun P ↦ q.bind fun Q ↦
      Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b⟩
  | _, _ => none

/-- The modes a binary node tries, in order. -/
def interpBinary (d₁ d₂ : PDenotation E W D) : Option (PDenotation E W D) :=
  applyForward? d₁ d₂ <|> applyBackward? d₁ d₂ <|> predicateModification? d₁ d₂

/-- The type a binary node composes to, a function of the daughters' types alone. -/
def tyBinary (σ τ : Ty) : Option Ty := σ.apply? τ <|> τ.apply? σ <|> σ.predicateModification? τ

theorem applyForward?_map_fst (d₁ d₂ : PDenotation E W D) :
    (applyForward? d₁ d₂).map (·.1) = Ty.apply? d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold applyForward? Ty.apply?
  dsimp only
  split <;> (try split_ifs) <;> simp_all

theorem applyBackward?_map_fst (d₁ d₂ : PDenotation E W D) :
    (applyBackward? d₁ d₂).map (·.1) = Ty.apply? d₂.1 d₁.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold applyBackward? Ty.apply?
  dsimp only
  split <;> (try split_ifs) <;> simp_all

theorem predicateModification?_map_fst (d₁ d₂ : PDenotation E W D) :
    (predicateModification? d₁ d₂).map (·.1) = Ty.predicateModification? d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold predicateModification? Ty.predicateModification?
  dsimp only
  split <;> simp_all

theorem interpBinary_map_fst (d₁ d₂ : PDenotation E W D) :
    (interpBinary d₁ d₂).map (·.1) = tyBinary d₁.1 d₂.1 := by
  simp only [interpBinary, tyBinary, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.map_or,
    applyForward?_map_fst, applyBackward?_map_fst, predicateModification?_map_fst]

/-! ### Evaluation on defined daughters

These are rewriting lemmas rather than `simp` lemmas, since the reducible `Ty.PDomain` keys a
concrete domain and a variable one differently for `simp`'s index. -/

/-- Forward application of a defined function to a defined argument evaluates the function. -/
theorem applyForward?_some_some {σ τ : Ty} (f : Ty.PDomain E W (σ ⇒ τ) D)
    (a : Ty.PDomain E W σ D) :
    applyForward? (⟨σ ⇒ τ, Part.some f⟩ : PDenotation E W D) ⟨σ, Part.some a⟩ =
      some ⟨τ, f a⟩ := by
  simp [applyForward?]

/-- Backward application of a defined function to a defined argument evaluates the function. -/
theorem applyBackward?_some_some {σ τ : Ty} (a : Ty.PDomain E W σ D)
    (f : Ty.PDomain E W (σ ⇒ τ) D) :
    applyBackward? (⟨σ, Part.some a⟩ : PDenotation E W D) ⟨σ ⇒ τ, Part.some f⟩ =
      some ⟨τ, f a⟩ := by
  simp [applyBackward?]

/-- Predicate modification of two defined predicates conjoins them pointwise. -/
theorem predicateModification?_some_some (P Q : Ty.PDomain E W (.e ⇒ .t) D) :
    predicateModification? (⟨.e ⇒ .t, Part.some P⟩ : PDenotation E W D) ⟨.e ⇒ .t, Part.some Q⟩ =
      some ⟨.e ⇒ .t, Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b⟩ := by
  simp [predicateModification?]

/-- A binary node whose left daughter is a defined function over the right daughter's type
applies it forward. -/
theorem interpBinary_forward {σ τ : Ty} (f : Ty.PDomain E W (σ ⇒ τ) D) (a : Ty.PDomain E W σ D) :
    interpBinary (⟨σ ⇒ τ, Part.some f⟩ : PDenotation E W D) ⟨σ, Part.some a⟩ = some ⟨τ, f a⟩ := by
  rw [interpBinary, applyForward?_some_some]; rfl

/-- A binary node whose right daughter is a defined function over the left daughter's type
applies it backward, forward application failing since no type is its own argument type. -/
theorem interpBinary_backward {σ τ : Ty} (a : Ty.PDomain E W σ D) (f : Ty.PDomain E W (σ ⇒ τ) D) :
    interpBinary (⟨σ, Part.some a⟩ : PDenotation E W D) ⟨σ ⇒ τ, Part.some f⟩ = some ⟨τ, f a⟩ := by
  have h : applyForward? (⟨σ, Part.some a⟩ : PDenotation E W D) ⟨σ ⇒ τ, Part.some f⟩ = none :=
    Option.map_eq_none_iff.mp (by rw [applyForward?_map_fst]; exact Ty.apply?_fn_self σ τ)
  rw [interpBinary, h, applyBackward?_some_some]; rfl

/-- Two defined predicates compose by predicate modification, application failing on them. -/
theorem interpBinary_predicateModification (P Q : Ty.PDomain E W (.e ⇒ .t) D) :
    interpBinary (⟨.e ⇒ .t, Part.some P⟩ : PDenotation E W D) ⟨.e ⇒ .t, Part.some Q⟩ =
      some ⟨.e ⇒ .t, Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b⟩ := by
  have h₁ : applyForward? (⟨.e ⇒ .t, Part.some P⟩ : PDenotation E W D) ⟨.e ⇒ .t, Part.some Q⟩ =
      none := Option.map_eq_none_iff.mp (by rw [applyForward?_map_fst]; rfl)
  have h₂ : applyBackward? (⟨.e ⇒ .t, Part.some P⟩ : PDenotation E W D) ⟨.e ⇒ .t, Part.some Q⟩ =
      none := Option.map_eq_none_iff.mp (by rw [applyBackward?_map_fst]; rfl)
  rw [interpBinary, h₁, h₂, predicateModification?_some_some]; rfl

/-! ### Tree interpretation -/

/-- The value of an interpreted daughter at the type `τ`, which is undefined where the daughter
is uninterpretable or of another type. -/
def valueAt (τ : Ty) : Option (PDenotation E W D) → Part (Ty.PDomain E W τ D)
  | some ⟨ty, v⟩ => if h : ty = τ then h ▸ v else Part.none
  | none => Part.none

variable {C : Type} {L : Type*}

/-- In the partial denotation of a tree under an assignment, a terminal denotes what its leaf
interpretation gives it, a non-branching node what its daughter does, a binary node, a projection or
an adjunction, what `interpBinary` composes, a trace the value of its index, and a binder the
partial function abstracting over its index in the body. -/
def interp (lex : L → Option (PDenotation E W D)) (g : Assignment E) :
    Tree C L → Option (PDenotation E W D)
  | .terminal _ w => lex w
  | .node _ (t :: []) => interp lex g t
  | .node _ (t₁ :: t₂ :: []) => do
    let d₁ ← interp lex g t₁
    let d₂ ← interp lex g t₂
    interpBinary d₁ d₂
  | .node _ _ => none
  | .adjoin _ (t :: []) => interp lex g t
  | .adjoin _ (t₁ :: t₂ :: []) => do
    let d₁ ← interp lex g t₁
    let d₂ ← interp lex g t₂
    interpBinary d₁ d₂
  | .adjoin _ _ => none
  | .trace n _ => some ⟨.e, Part.some (g n)⟩
  | .bind n _ body =>
    (interp lex g body).map fun d ↦
      ⟨.fn .e d.1, Part.some fun x ↦ valueAt d.1 (interp lex (g[n ↦ x]) body)⟩
  | _ => none

variable (lex lex' : L → Option (PDenotation E W D)) (g g' : Assignment E)

@[simp] theorem interp_terminal (c : C) (w : L) :
    interp lex g (.terminal c w : Tree C L) = lex w := rfl

@[simp] theorem interp_node_unary (c : C) (t : Tree C L) :
    interp lex g (.node c (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_node_binary (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.node c (t₁ :: t₂ :: [])) =
      (interp lex g t₁).bind fun d₁ ↦ (interp lex g t₂).bind fun d₂ ↦ interpBinary d₁ d₂ := rfl

@[simp] theorem interp_adjoin_unary (c : C) (t : Tree C L) :
    interp lex g (.adjoin c (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_adjoin_binary (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.adjoin c (t₁ :: t₂ :: [])) =
      (interp lex g t₁).bind fun d₁ ↦ (interp lex g t₂).bind fun d₂ ↦ interpBinary d₁ d₂ := rfl

@[simp] theorem interp_trace (n : ℕ) (c : C) :
    interp lex g (.trace n c : Tree C L) = some ⟨.e, Part.some (g n)⟩ := rfl

@[simp] theorem interp_bind (n : ℕ) (c : C) (body : Tree C L) :
    interp lex g (.bind n c body) = (interp lex g body).map fun d ↦
      ⟨.fn .e d.1, Part.some fun x ↦ valueAt d.1 (interp lex (g[n ↦ x]) body)⟩ := rfl

/-- A node whose daughters its label does not license denotes nothing. -/
theorem interp_junk {l : PhraseStructure.Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ PhraseStructure.Tree.Label.Licenses l (cs.map RoseTree.value)) :
    interp lex g (RoseTree.node l cs) = none := by
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

/-! ### Uninterpretability and presupposition failure -/

/-- A tree is uninterpretable when the engine assigns it no denotation. -/
def Uninterpretable (t : Tree C L) : Prop := interp lex g t = none

/-- A tree is a presupposition failure when its denotation is undefined. -/
def PresupFailure (t : Tree C L) : Prop := ∃ d, interp lex g t = some d ∧ ¬ d.2.Dom

/-- Whether a tree is interpretable, and at which type, depends only on the types of its
leaves, [heim-kratzer-1998]'s characterization of uninterpretability. -/
theorem interp_map_fst_congr (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    (interp lex g t).map (·.1) = (interp lex' g' t).map (·.1) := by
  induction t using Tree.rec' generalizing g g' with
  | terminal c w => exact h w
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => simp only [interp_node_unary]; exact ih t (by simp) g g'
    | [t₁, t₂] =>
      simp only [interp_node_binary]
      have h₁ := ih t₁ (by simp) g g'
      have h₂ := ih t₂ (by simp) g g'
      revert h₁ h₂
      cases interp lex g t₁ <;> cases interp lex' g' t₁ <;>
        cases interp lex g t₂ <;> cases interp lex' g' t₂ <;>
        intro h₁ h₂ <;> simp_all [interpBinary_map_fst]
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    match cs with
    | [] => rfl
    | [t] => simp only [interp_adjoin_unary]; exact ih t (by simp) g g'
    | [t₁, t₂] =>
      simp only [interp_adjoin_binary]
      have h₁ := ih t₁ (by simp) g g'
      have h₂ := ih t₂ (by simp) g g'
      revert h₁ h₂
      cases interp lex g t₁ <;> cases interp lex' g' t₁ <;>
        cases interp lex g t₂ <;> cases interp lex' g' t₂ <;>
        intro h₁ h₂ <;> simp_all [interpBinary_map_fst]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    simp only [interp_bind]
    have h := ih g g'
    revert h
    cases interp lex g body <;> cases interp lex' g' body <;> intro h <;> simp_all
  | junk l cs hj _ => rw [interp_junk lex g hj, interp_junk lex' g' hj]

/-- Uninterpretability is decided by the leaves' types alone. -/
theorem uninterpretable_congr (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    Uninterpretable lex g t ↔ Uninterpretable lex' g' t := by
  have := interp_map_fst_congr lex lex' g g' h t
  constructor
  · intro hn; rw [hn] at this; exact Option.map_eq_none_iff.mp this.symm
  · intro hn; rw [hn] at this; exact Option.map_eq_none_iff.mp this

/-! ### The definite article -/

/-- A partial predicate holds of an individual when it is defined there and true. -/
def Holds (P : E →. Prop) (x : E) : Prop := ∃ h : (P x).Dom, (P x).get h

/-- [heim-kratzer-1998]'s Fregean entry for the definite article, which maps a predicate true of
exactly one individual to that individual and is undefined elsewhere. -/
noncomputable def the : Ty.PDomain E W ((.e ⇒ .t) ⇒ .e) D :=
  fun P ↦ ⟨∃! x, Holds P x, fun h ↦ Classical.choose h⟩

/-- The definite article is defined exactly on the predicates true of one individual. -/
theorem the_dom (P : E →. Prop) : (the (W := W) (D := D) P).Dom ↔ ∃! x, Holds P x := Iff.rfl

/-- A total predicate holds where it is true. -/
@[simp] theorem holds_lift (P : E → Prop) (x : E) : Holds (PFun.lift P) x ↔ P x := by
  simp [Holds, PFun.lift]

/-- On a total predicate true of exactly one individual, the definite article picks it. -/
theorem the_lift_eq_some {P : E → Prop} {a : E} (h : ∀ x, P x ↔ x = a) :
    the (W := W) (D := D) (PFun.lift P) = Part.some a := by
  have hu : ∃! x, Holds (PFun.lift P) x := ⟨a, (holds_lift P a).mpr ((h a).mpr rfl),
    fun y hy ↦ (h y).mp ((holds_lift P y).mp hy)⟩
  exact Part.eq_some_iff.mpr ⟨hu, (h _).mp ((holds_lift P _).mp (Classical.choose_spec hu).1)⟩

end Partial

/-! ### Total lexica

A partial denotation lifts a total one when it agrees with it at a base type and, at a function
type, is defined on every lift of an argument with a value lifting the total function's value.
On a lexicon whose entries lift a total lexicon, every defined value of the partial engine lifts
the pure engine's value at the same node, so a total lexicon has no presupposition failures. The
converse fails, since the pure engine also has intensional application and event
identification. -/

end HeimKratzer

namespace Montague

variable {E W D : Type}

/-- The lifting relation between a total denotation and a partial one of the same type. -/
def Ty.Lifts : (ty : Ty) → Ty.Domain E W ty D → Ty.PDomain E W ty D → Prop
  | .e, x, y => x = y
  | .t, x, y => x = y
  | .d, x, y => x = y
  | .n, x, y => x = y
  | .v, x, y => x = y
  | .s, x, y => x = y
  | .fn a b, f, f' => ∀ x y, Ty.Lifts a x y → ∃ z, f' y = Part.some z ∧ Ty.Lifts b (f x) z
  | .intens a, f, f' => ∀ w, ∃ z, f' w = Part.some z ∧ Ty.Lifts a (f w) z

@[simp] theorem Ty.lifts_e {x y : E} : Ty.Lifts (E := E) (W := W) (D := D) .e x y ↔ x = y :=
  Iff.rfl

@[simp] theorem Ty.lifts_t {x y : Prop} : Ty.Lifts (E := E) (W := W) (D := D) .t x y ↔ x = y :=
  Iff.rfl

theorem Ty.lifts_fn {a b : Ty} {f : Ty.Domain E W (a ⇒ b) D} {f' : Ty.PDomain E W (a ⇒ b) D} :
    Ty.Lifts (a ⇒ b) f f' ↔
      ∀ x y, Ty.Lifts a x y → ∃ z, f' y = Part.some z ∧ Ty.Lifts b (f x) z :=
  Iff.rfl

/-- A total function of individuals lifts to the everywhere-defined partial function whose
values lift its values. -/
theorem Ty.lifts_lift {b : Ty} {f : E → Ty.Domain E W b D} {f' : E → Ty.PDomain E W b D}
    (h : ∀ x, Ty.Lifts b (f x) (f' x)) : Ty.Lifts (.e ⇒ b) f (PFun.lift f') :=
  fun x _ hxy ↦ ⟨f' x, hxy ▸ rfl, h x⟩

/-- A partial denotation lifts a total one when it has the same type and a defined value that
lifts the total value. -/
inductive Denotation.Lifts : Denotation E W Id D → PDenotation E W D → Prop
  | mk {ty : Ty} {x : Ty.Domain E W ty D} {y : Ty.PDomain E W ty D} (h : Ty.Lifts ty x y) :
      Denotation.Lifts ⟨ty, x⟩ ⟨ty, Part.some y⟩

theorem Denotation.Lifts.fst {d : Denotation E W Id D} {d' : PDenotation E W D}
    (h : d.Lifts d') : d.1 = d'.1 := by cases h; rfl

/-- The types whose functions take only individuals as arguments are those the extensional
lexicon of [heim-kratzer-1998] has, namely individuals, truth values, degrees, cardinalities,
eventualities, functions from individuals, and intensions. -/
inductive Ty.FirstOrder : Ty → Prop
  | e : FirstOrder .e
  | t : FirstOrder .t
  | d : FirstOrder .d
  | n : FirstOrder .n
  | v : FirstOrder .v
  | s : FirstOrder .s
  | fn {b : Ty} : FirstOrder b → FirstOrder (.e ⇒ b)
  | intens {a : Ty} : FirstOrder a → FirstOrder (.intens a)

/-- The partial denotation a total one lifts to, defined everywhere on individual arguments
and nowhere on a function argument. -/
def Ty.Domain.toPartial : (ty : Ty) → Ty.Domain E W ty D → Ty.PDomain E W ty D
  | .e, x => x
  | .t, x => x
  | .d, x => x
  | .n, x => x
  | .v, x => x
  | .s, x => x
  | .fn .e b, f => PFun.lift fun x ↦ toPartial b (f x)
  | .fn _ _, _ => fun _ ↦ Part.none
  | .intens a, f => PFun.lift fun w ↦ toPartial a (f w)

/-- At a first-order type, the lift of a total denotation lifts it. -/
theorem Ty.lifts_toPartial {ty : Ty} (h : ty.FirstOrder) (x : Ty.Domain E W ty D) :
    Ty.Lifts ty x (Ty.Domain.toPartial ty x) := by
  induction h with
  | fn _ ih => exact Ty.lifts_lift fun x ↦ ih _
  | intens _ ih => exact fun w ↦ ⟨_, rfl, ih _⟩
  | _ => rfl

/-- The partial denotation a total one lifts to. -/
def Denotation.toPartial (d : Denotation E W Id D) : PDenotation E W D :=
  ⟨d.1, Part.some (Ty.Domain.toPartial d.1 d.2)⟩

/-- A first-order total denotation is lifted by its partial counterpart. -/
theorem Denotation.lifts_toPartial {d : Denotation E W Id D} (h : d.1.FirstOrder) :
    d.Lifts d.toPartial := by
  obtain ⟨ty, x⟩ := d
  exact .mk (Ty.lifts_toPartial h x)

end Montague

namespace HeimKratzer

open Montague

section Total

open PhraseStructure Tree
open scoped Assignment

variable {E W D : Type}

namespace Partial

variable {d₁ d₂ : Denotation E W Id D} {d₁' d₂' d' : PDenotation E W D}

theorem applyForward?_lifts (h₁ : d₁.Lifts d₁') (h₂ : d₂.Lifts d₂')
    (h : applyForward? d₁' d₂' = some d') :
    ∃ d : Denotation E W Id D,
      (Tree.Modes.ofApplicative E W Id D).applyForward? d₁ d₂ = some d ∧ d.Lifts d' := by
  cases h₁ with | @mk ty₁ x₁ y₁ hl₁ => ?_
  cases h₂ with | @mk ty₂ x₂ y₂ hl₂ => ?_
  cases ty₁
  case fn σ τ =>
    by_cases hσ : σ = ty₂
    · subst hσ
      rw [applyForward?_some_some, Option.some.injEq] at h
      subst h
      obtain ⟨z, hz, hl⟩ := hl₁ x₂ y₂ hl₂
      exact ⟨⟨τ, x₁ x₂⟩, by rw [Tree.Modes.applyForward?_fn]; rfl, hz ▸ .mk hl⟩
    · have hty := applyForward?_map_fst (⟨σ ⇒ τ, Part.some y₁⟩ : PDenotation E W D)
        ⟨ty₂, Part.some y₂⟩
      rw [h] at hty
      simp [Ty.apply?, hσ] at hty
  all_goals simp [applyForward?] at h

theorem applyBackward?_lifts (h₁ : d₁.Lifts d₁') (h₂ : d₂.Lifts d₂')
    (h : applyBackward? d₁' d₂' = some d') :
    ∃ d : Denotation E W Id D,
      (Tree.Modes.ofApplicative E W Id D).applyBackward? d₁ d₂ = some d ∧ d.Lifts d' := by
  cases h₁ with | @mk ty₁ x₁ y₁ hl₁ => ?_
  cases h₂ with | @mk ty₂ x₂ y₂ hl₂ => ?_
  cases ty₂
  case fn σ τ =>
    by_cases hσ : σ = ty₁
    · subst hσ
      rw [applyBackward?_some_some, Option.some.injEq] at h
      subst h
      obtain ⟨z, hz, hl⟩ := hl₂ x₁ y₁ hl₁
      exact ⟨⟨τ, x₂ x₁⟩, by rw [Tree.Modes.applyBackward?_fn]; rfl, hz ▸ .mk hl⟩
    · have hty := applyBackward?_map_fst (⟨ty₁, Part.some y₁⟩ : PDenotation E W D)
        ⟨σ ⇒ τ, Part.some y₂⟩
      rw [h] at hty
      simp [Ty.apply?, hσ] at hty
  all_goals simp [applyBackward?] at h

theorem predicateModification?_lifts (h₁ : d₁.Lifts d₁') (h₂ : d₂.Lifts d₂')
    (h : predicateModification? d₁' d₂' = some d') :
    ∃ d : Denotation E W Id D,
      (Tree.Modes.ofApplicative E W Id D).interpBinary d₁ d₂ = some d ∧ d.Lifts d' := by
  cases h₁ with | @mk ty₁ x₁ y₁ hl₁ => ?_
  cases h₂ with | @mk ty₂ x₂ y₂ hl₂ => ?_
  have hty :=
    predicateModification?_map_fst (⟨ty₁, Part.some y₁⟩ : PDenotation E W D) ⟨ty₂, Part.some y₂⟩
  rw [h] at hty
  dsimp only at hty
  unfold Ty.predicateModification? at hty
  split at hty
  · rw [predicateModification?_some_some, Option.some.injEq] at h
    subst h
    refine ⟨_, (Tree.Modes.ofApplicative E W Id D).interpBinary_predicateModification x₁ x₂,
      .mk (Ty.lifts_fn.mpr fun x _ hxy ↦ ?_)⟩
    obtain rfl : x = _ := hxy
    obtain ⟨a, ha, hla⟩ := hl₁ x x rfl
    obtain ⟨b, hb, hlb⟩ := hl₂ x x rfl
    rw [Ty.lifts_t] at hla hlb
    subst hla hlb
    exact ⟨x₁ x ∧ x₂ x, by simp [ha, hb], rfl⟩
  · simp at hty

theorem interpBinary_lifts (h₁ : d₁.Lifts d₁') (h₂ : d₂.Lifts d₂')
    (h : interpBinary d₁' d₂' = some d') :
    ∃ d : Denotation E W Id D,
      (Tree.Modes.ofApplicative E W Id D).interpBinary d₁ d₂ = some d ∧ d.Lifts d' := by
  simp only [interpBinary, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_some_iff] at h
  rcases h with h | ⟨hf, h | ⟨hb, h⟩⟩
  · obtain ⟨d, hd, hl⟩ := applyForward?_lifts h₁ h₂ h
    exact ⟨d, by simp only [Tree.Modes.interpBinary, Tree.Modes.functionalApplication?,
      Option.orElse_eq_orElse, Option.orElse_eq_or, hd, Option.some_or], hl⟩
  · obtain ⟨d, hd, hl⟩ := applyBackward?_lifts h₁ h₂ h
    have hf' : (Tree.Modes.ofApplicative E W Id D).applyForward? d₁ d₂ = none :=
      Option.map_eq_none_iff.mp <| by
        rw [Tree.Modes.applyForward?_map_fst, h₁.fst, h₂.fst, ← applyForward?_map_fst, hf]; rfl
    exact ⟨d, by simp only [Tree.Modes.interpBinary, Tree.Modes.functionalApplication?,
      Option.orElse_eq_orElse, Option.orElse_eq_or, hf', hd, Option.none_or, Option.some_or], hl⟩
  · exact predicateModification?_lifts h₁ h₂ h

variable {C : Type} {L : Type*} {lex : L → Option (Denotation E W Id D)}
  {lex' : L → Option (PDenotation E W D)}

/-- On a lexicon lifting a total one, every defined value of the partial engine lifts the pure
engine's value at that node. -/
theorem interp_lifts (hlex : ∀ w d', lex' w = some d' → ∃ d, lex w = some d ∧ d.Lifts d')
    (g : Assignment E) (t : Tree C L) (h : interp lex' g t = some d') :
    ∃ d, Tree.interp lex g t = some d ∧ d.Lifts d' := by
  induction t using Tree.rec' generalizing g d' with
  | terminal c w => exact hlex w d' h
  | node c cs ih =>
    match cs with
    | [] => exact absurd h (by simp [interp])
    | [t] => exact ih t (by simp) g h
    | [t₁, t₂] =>
      rw [interp_node_binary] at h
      obtain ⟨d₁', h₁', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₂', h₂', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₁, hd₁, hl₁⟩ := ih t₁ (by simp) g h₁'
      obtain ⟨d₂, hd₂, hl₂⟩ := ih t₂ (by simp) g h₂'
      obtain ⟨d, hd, hl⟩ := interpBinary_lifts hl₁ hl₂ h
      exact ⟨d, by rw [Tree.interp_node_binary, hd₁, hd₂, Option.bind_some, Option.bind_some,
        hd], hl⟩
    | _ :: _ :: _ :: _ => exact absurd h (by simp [interp])
  | adjoin c cs ih =>
    match cs with
    | [] => exact absurd h (by simp [interp])
    | [t] => exact ih t (by simp) g h
    | [t₁, t₂] =>
      rw [interp_adjoin_binary] at h
      obtain ⟨d₁', h₁', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₂', h₂', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₁, hd₁, hl₁⟩ := ih t₁ (by simp) g h₁'
      obtain ⟨d₂, hd₂, hl₂⟩ := ih t₂ (by simp) g h₂'
      obtain ⟨d, hd, hl⟩ := interpBinary_lifts hl₁ hl₂ h
      exact ⟨d, by rw [Tree.interp_adjoin_binary, hd₁, hd₂, Option.bind_some, Option.bind_some,
        hd], hl⟩
    | _ :: _ :: _ :: _ => exact absurd h (by simp [interp])
  | trace n c =>
    rw [interp_trace, Option.some.injEq] at h
    subst h
    exact ⟨⟨.e, g n⟩, rfl, .mk rfl⟩
  | bind n c body ih =>
    rw [interp_bind, Option.map_eq_some_iff] at h
    obtain ⟨⟨τ, v⟩, hb, rfl⟩ := h
    obtain ⟨d, hd, hl⟩ := ih g hb
    cases hl with | @mk _ x₀ y₀ _ => ?_
    refine ⟨⟨.e ⇒ τ, fun x ↦ Tree.valueAt τ x₀ (Tree.interp lex (g[n ↦ x]) body)⟩, ?_, .mk ?_⟩
    · rw [Tree.interp_bind, hd]; rfl
    · intro x _ hxy
      obtain rfl : x = _ := hxy
      have hty := interp_map_fst_congr lex' lex' g (g[n ↦ x]) (fun _ ↦ rfl) body
      rw [hb] at hty
      obtain ⟨v', hv'⟩ : ∃ v', interp lex' (g[n ↦ x]) body = some ⟨τ, v'⟩ := by
        rcases hg : interp lex' (g[n ↦ x]) body with _ | ⟨τ', v'⟩
        · simp [hg] at hty
        · simp only [hg, Option.map_some, Option.some.injEq] at hty; subst hty; exact ⟨v', rfl⟩
      obtain ⟨d', hd', hl'⟩ := ih (g[n ↦ x]) hv'
      cases hl' with | @mk _ x' y' hl' => ?_
      refine ⟨y', by simp [valueAt, hv'], ?_⟩
      simpa [Tree.valueAt, hd'] using hl'
  | junk l cs hj _ => exact absurd h (by rw [interp_junk _ _ hj]; simp)

/-- A lexicon lifting a total one has no presupposition failures. -/
theorem not_presupFailure_of_lifts
    (hlex : ∀ w d', lex' w = some d' → ∃ d, lex w = some d ∧ d.Lifts d') (g : Assignment E)
    (t : Tree C L) : ¬ PresupFailure lex' g t := by
  rintro ⟨d', hd', hdom⟩
  obtain ⟨d, -, hl⟩ := interp_lifts hlex g t hd'
  cases hl
  exact hdom trivial

/-- The entrywise lift of a first-order lexicon lifts it. -/
theorem lifts_map_toPartial (h : ∀ w d, lex w = some d → d.1.FirstOrder) (w : L)
    (d' : PDenotation E W D) (h' : (lex w).map Denotation.toPartial = some d') :
    ∃ d, lex w = some d ∧ d.Lifts d' := by
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h'
  exact ⟨d, hd, Denotation.lifts_toPartial (h w d hd)⟩

/-- The entrywise lift of a first-order lexicon has no presupposition failures. -/
theorem not_presupFailure_map_toPartial (h : ∀ w d, lex w = some d → d.1.FirstOrder)
    (g : Assignment E) (t : Tree C L) :
    ¬ PresupFailure (fun w ↦ (lex w).map Denotation.toPartial) g t :=
  not_presupFailure_of_lifts (lifts_map_toPartial h) g t

end Partial

end Total

end HeimKratzer
