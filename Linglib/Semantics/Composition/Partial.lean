module

public import Mathlib.Data.PFun
public import Linglib.Semantics.Composition.Tree

/-!
# Partial interpretation

This file is Heim and Kratzer's composition engine on partial denotations. A function
denotes a partial function, mathlib's `PFun`, whose domain is the definedness condition the
book attaches to a lexical entry, and a node denotes a `Part` value of its type, defined when
its daughters are and the function among them is defined at its argument. The engine evaluates
the term a tree translates to (`Tree.translate`), so it composes by the same modes as the total
engine (`Mode.evalPartial`); a trace denotes the value of its index and a binder abstracts over
its index, the abstract being a partial function that is undefined wherever the body is.
Predicate Abstraction therefore needs no distributor.

The book's distinction between uninterpretability and presupposition failure (§4.4.4) is the
difference between the engine returning no denotation and returning an undefined one:
`Uninterpretable` is decided by the types of the leaves alone (`uninterpretable_congr`), and
`PresupFailure` asks after the denotations. The definite article is the book's Fregean entry
(`the`), defined on the predicates true of exactly one individual.

## Main declarations

* `Ty.PDomain` and `PDenotation` are the partial domains and denotations.
* `Mode.evalPartial` and `Term.evalPartial` are the partial denotations of a mode and of a term,
  and `Partial.interp` the engine, evaluating a tree's term.
* `Partial.Uninterpretable` and `Partial.PresupFailure` are the two ways of lacking a value, and
  `Partial.interp_map_fst_congr` shows the first depends on the leaves' types alone.
* `Partial.the` is the definite article, with `Partial.the_dom` its definedness condition.
* `Ty.Lifts` and `Denotation.Lifts` relate a total denotation to a partial one lifting it, and
  `Partial.interp_lifts` shows that on a lexicon lifting a total one the partial engine's
  values lift the pure engine's, every mode preserving the lift (`Mode.lifts_evalPartial`), so
  such a lexicon has no presupposition failure (`Partial.not_presupFailure_of_lifts`).
  `Ty.Domain.toPartial` is the lift at a first-order type.

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

/-! ### Partial denotations of the modes and terms -/

section Evaluation

variable {E W D : Type} {σ₁ σ₂ τ : Ty}

/-- The partial denotation of a mode, defined where both daughters are and the function or role
head among them is defined at its argument. -/
def Mode.evalPartial : Mode σ₁ σ₂ τ → Part (Ty.PDomain E W σ₁ D) → Part (Ty.PDomain E W σ₂ D) →
    Part (Ty.PDomain E W τ D)
  | .functionalLeft, f, a => f.bind fun fv ↦ a.bind fv
  | .functionalRight, a, f => f.bind fun fv ↦ a.bind fv
  | .intensionalLeft, f, a => f.bind fun fv ↦ a.bind fun av ↦ fv fun _ ↦ Part.some av
  | .intensionalRight, a, f => f.bind fun fv ↦ a.bind fun av ↦ fv fun _ ↦ Part.some av
  | .predicateModification, p, q => p.bind fun P ↦ q.bind fun Q ↦
      Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b
  | .eventIdentificationLeft, f, p => f.bind fun F ↦ p.bind fun P ↦
      Part.some fun x ↦ (F x).map fun Fx e ↦ (Fx e).bind fun a ↦ (P e).map fun b ↦ a ∧ b
  | .eventIdentificationRight, p, f => f.bind fun F ↦ p.bind fun P ↦
      Part.some fun x ↦ (F x).map fun Fx e ↦ (Fx e).bind fun a ↦ (P e).map fun b ↦ a ∧ b

open scoped Assignment

/-- The partial denotation of a term under a partial interpretation of the constants and an
assignment; an abstraction is the partial function undefined wherever its body is. -/
def Term.evalPartial {K : Ty → Type} (I : ∀ {ty : Ty}, K ty → Part (Ty.PDomain E W ty D))
    (g : Assignment E) : {ty : Ty} → Term K ty → Part (Ty.PDomain E W ty D)
  | _, .const c => I c
  | _, .var n => Part.some (g n)
  | _, .lam n b => Part.some fun x ↦ evalPartial I (g[n ↦ x]) b
  | _, .comp m l r => m.evalPartial (evalPartial I g l) (evalPartial I g r)

end Evaluation

namespace Partial

open PhraseStructure Tree
open scoped Assignment

variable {E W D : Type}

/-! ### Composition of defined daughters

These are rewriting lemmas rather than `simp` lemmas, since the reducible `Ty.PDomain` keys a
concrete domain and a variable one differently for `simp`'s index. -/

/-- A binary node whose left daughter is a defined function over the right daughter's type
applies it forward. -/
theorem combine?_forward {σ τ : Ty} (f : Ty.PDomain E W (σ ⇒ τ) D) (a : Ty.PDomain E W σ D) :
    Mode.combine? Mode.evalPartial (⟨σ ⇒ τ, Part.some f⟩ : PDenotation E W D) ⟨σ, Part.some a⟩ =
      some ⟨τ, f a⟩ := by
  rw [Mode.combine?_fn_left]; simp [Mode.evalPartial]

/-- A binary node whose right daughter is a defined function over the left daughter's type
applies it backward. -/
theorem combine?_backward {σ τ : Ty} (a : Ty.PDomain E W σ D) (f : Ty.PDomain E W (σ ⇒ τ) D) :
    Mode.combine? Mode.evalPartial (⟨σ, Part.some a⟩ : PDenotation E W D) ⟨σ ⇒ τ, Part.some f⟩ =
      some ⟨τ, f a⟩ := by
  rw [Mode.combine?_fn_right]; simp [Mode.evalPartial]

/-- Two defined predicates compose by predicate modification, conjoined pointwise. -/
theorem combine?_predicateModification (P Q : Ty.PDomain E W (.e ⇒ .t) D) :
    Mode.combine? Mode.evalPartial (⟨.e ⇒ .t, Part.some P⟩ : PDenotation E W D)
        ⟨.e ⇒ .t, Part.some Q⟩ =
      some ⟨.e ⇒ .t, Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b⟩ := by
  rw [Mode.combine?_predicateModification]; simp [Mode.evalPartial]

/-! ### Tree interpretation -/

/-- The value of an interpreted daughter at the type `τ`, which is undefined where the daughter
is uninterpretable or of another type. -/
def valueAt (τ : Ty) : Option (PDenotation E W D) → Part (Ty.PDomain E W τ D)
  | some ⟨ty, v⟩ => if h : ty = τ then h ▸ v else Part.none
  | none => Part.none

variable {C : Type} {L : Type*}

/-- The partial denotation of a tree under an assignment: its term's partial denotation, each
word's partial denotation its constant. A terminal denotes what its leaf interpretation gives it,
a binary node what the mode its daughters' types select composes, a trace the value of its
index, and a binder the partial function abstracting over its index in the body. -/
def interp (lex : L → Option (PDenotation E W D)) (g : Assignment E) (t : Tree C L) :
    Option (PDenotation E W D) :=
  (translate (K := fun ty ↦ Part (Ty.PDomain E W ty D)) lex t).map fun d ↦
    ⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩

variable (lex lex' : L → Option (PDenotation E W D)) (g g' : Assignment E)

@[simp] theorem interp_terminal (c : C) (w : L) :
    interp lex g (.terminal c w : Tree C L) = lex w := by
  simp only [interp, translate_terminal, Option.map_map]
  cases lex w <;> rfl

@[simp] theorem interp_node_unary (c : C) (t : Tree C L) :
    interp lex g (.node c (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_adjoin_unary (c : C) (t : Tree C L) :
    interp lex g (.adjoin c (t :: [])) = interp lex g t := rfl

omit lex in
private theorem map_bind_combine
    (t₁ t₂ : Option (Σ ty, Term (fun ty ↦ Part (Ty.PDomain E W ty D)) ty)) :
    (t₁.bind fun d₁ ↦ t₂.bind fun d₂ ↦ Mode.combine? (fun m l r ↦ .comp m l r) d₁ d₂).map
        (fun d ↦ (⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩ : PDenotation E W D)) =
      (t₁.map fun d ↦ ⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩).bind fun d₁ ↦
        (t₂.map fun d ↦ ⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩).bind fun d₂ ↦
          Mode.combine? Mode.evalPartial d₁ d₂ := by
  rcases t₁ with _ | ⟨τ₁, u₁⟩ <;> rcases t₂ with _ | ⟨τ₂, u₂⟩ <;> try rfl
  simp only [Option.bind_some, Option.map_some, Mode.combine?, Option.map_map]
  rfl

@[simp] theorem interp_node_binary (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.node c (t₁ :: t₂ :: [])) = (interp lex g t₁).bind fun d₁ ↦
      (interp lex g t₂).bind fun d₂ ↦ Mode.combine? Mode.evalPartial d₁ d₂ :=
  map_bind_combine g _ _

@[simp] theorem interp_adjoin_binary (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.adjoin c (t₁ :: t₂ :: [])) = (interp lex g t₁).bind fun d₁ ↦
      (interp lex g t₂).bind fun d₂ ↦ Mode.combine? Mode.evalPartial d₁ d₂ :=
  map_bind_combine g _ _

@[simp] theorem interp_trace (n : ℕ) (c : C) :
    interp lex g (.trace n c : Tree C L) = some ⟨.e, Part.some (g n)⟩ := rfl

@[simp] theorem interp_bind (n : ℕ) (c : C) (body : Tree C L) :
    interp lex g (.bind n c body) = (interp lex g body).map fun d ↦
      ⟨.fn .e d.1, Part.some fun x ↦ valueAt d.1 (interp lex (g[n ↦ x]) body)⟩ := by
  simp only [interp, translate_bind, Option.map_map]
  rcases translate (K := fun ty ↦ Part (Ty.PDomain E W ty D)) lex body with _ | ⟨τ, b⟩
  · rfl
  · simp [Term.evalPartial, valueAt]

/-- A node whose daughters its label does not license denotes nothing. -/
theorem interp_junk {l : PhraseStructure.Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ PhraseStructure.Tree.Label.Licenses l (cs.map RoseTree.value)) :
    interp lex g (RoseTree.node l cs) = none := by
  simp only [interp, translate_junk _ h, Option.map_none]

/-! ### Uninterpretability and presupposition failure -/

/-- A tree is uninterpretable when the engine assigns it no denotation. -/
def Uninterpretable (t : Tree C L) : Prop := interp lex g t = none

/-- A tree is a presupposition failure when its denotation is undefined. -/
def PresupFailure (t : Tree C L) : Prop := ∃ d, interp lex g t = some d ∧ ¬ d.2.Dom

/-- Whether a tree is interpretable, and at which type, depends only on the types of its
leaves, [heim-kratzer-1998]'s characterization of uninterpretability. -/
theorem interp_map_fst_congr (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    (interp lex g t).map (·.1) = (interp lex' g' t).map (·.1) := by
  simp only [interp, Option.map_map, Function.comp_def]
  exact translate_map_fst lex h t

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
On a lexicon whose entries lift a total lexicon, every value of the partial engine is defined and
lifts the pure engine's value at the same node, since both evaluate the same term and every mode
preserves the lift; so a total lexicon has no presupposition failures. -/

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

/-- Every mode preserves the lift: on defined daughters lifting total ones, a mode's partial
value is defined and lifts its total value. -/
theorem Mode.lifts_evalPartial {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) {a : Ty.Domain E W σ₁ D}
    {b : Ty.Domain E W σ₂ D} {a' : Ty.PDomain E W σ₁ D} {b' : Ty.PDomain E W σ₂ D}
    (ha : Ty.Lifts σ₁ a a') (hb : Ty.Lifts σ₂ b b') :
    ∃ z, m.evalPartial (Part.some a') (Part.some b') = Part.some z ∧ Ty.Lifts τ (m.eval a b) z := by
  cases m with
  | functionalLeft => simpa [evalPartial, eval] using ha b b' hb
  | functionalRight => simpa [evalPartial, eval] using hb a a' ha
  | intensionalLeft =>
    simpa [evalPartial, eval] using ha (fun _ ↦ b) (fun _ ↦ Part.some b') fun _ ↦ ⟨b', rfl, hb⟩
  | intensionalRight =>
    simpa [evalPartial, eval] using hb (fun _ ↦ a) (fun _ ↦ Part.some a') fun _ ↦ ⟨a', rfl, ha⟩
  | predicateModification =>
    refine ⟨_, by simp [evalPartial]; rfl, Ty.lifts_fn.mpr fun x _ hxy ↦ ?_⟩
    obtain rfl : x = _ := hxy
    obtain ⟨p, hp, hlp⟩ := ha x x rfl
    obtain ⟨q, hq, hlq⟩ := hb x x rfl
    rw [Ty.lifts_t] at hlp hlq
    subst hlp hlq
    exact ⟨a x ∧ b x, by simp [hp, hq], rfl⟩
  | eventIdentificationLeft =>
    refine ⟨_, by simp [evalPartial]; rfl, Ty.lifts_fn.mpr fun x _ hxy ↦ ?_⟩
    obtain rfl : x = _ := hxy
    obtain ⟨F, hF, hlF⟩ := ha x x rfl
    refine ⟨_, by simp [hF]; rfl, Ty.lifts_fn.mpr fun e _ hey ↦ ?_⟩
    obtain rfl : e = _ := hey
    obtain ⟨p, hp, hlp⟩ := hlF e e rfl
    obtain ⟨q, hq, hlq⟩ := hb e e rfl
    rw [Ty.lifts_t] at hlp hlq
    subst hlp hlq
    exact ⟨a x e ∧ b e, by simp [hp, hq], rfl⟩
  | eventIdentificationRight =>
    refine ⟨_, by simp [evalPartial]; rfl, Ty.lifts_fn.mpr fun x _ hxy ↦ ?_⟩
    obtain rfl : x = _ := hxy
    obtain ⟨F, hF, hlF⟩ := hb x x rfl
    refine ⟨_, by simp [hF]; rfl, Ty.lifts_fn.mpr fun e _ hey ↦ ?_⟩
    obtain rfl : e = _ := hey
    obtain ⟨p, hp, hlp⟩ := hlF e e rfl
    obtain ⟨q, hq, hlq⟩ := ha e e rfl
    rw [Ty.lifts_t] at hlp hlq
    subst hlp hlq
    exact ⟨b x e ∧ a e, by simp [hp, hq], rfl⟩

/-- A partial constant lifts a total one when it is defined with a value lifting it. -/
def LiftsConst (ty : Ty) (c : Id (Ty.Domain E W ty D)) (c' : Part (Ty.PDomain E W ty D)) : Prop :=
  ∃ y, c' = Part.some y ∧ Ty.Lifts ty c y

/-- Terms of the same shape whose partial constants lift the total ones have a defined partial
denotation lifting the total one, under every assignment. -/
theorem Term.Rel.lifts {ty : Ty} {u : Term (fun ty ↦ Id (Ty.Domain E W ty D)) ty}
    {u' : Term (fun ty ↦ Part (Ty.PDomain E W ty D)) ty} (h : Term.Rel LiftsConst u u')
    (g : Assignment E) :
    ∃ z, u'.evalPartial (fun c ↦ c) g = Part.some z ∧ Ty.Lifts ty (u.eval (fun c ↦ c) g) z := by
  induction h generalizing g with
  | const hc => exact hc
  | var n => exact ⟨g n, rfl, rfl⟩
  | lam n _ ih =>
    exact ⟨_, rfl, Ty.lifts_fn.mpr fun x _ hxy ↦ by obtain rfl : x = _ := hxy; exact ih _⟩
  | comp m _ _ ihl ihr =>
    obtain ⟨zl, hzl, hll⟩ := ihl g
    obtain ⟨zr, hzr, hlr⟩ := ihr g
    simp only [Term.evalPartial, hzl, hzr, Term.eval]
    exact m.lifts_evalPartial hll hlr

namespace Partial

variable {C : Type} {L : Type*} {lex : L → Option (Denotation E W Id D)}
  {lex' : L → Option (PDenotation E W D)}

/-- On a lexicon lifting a total one, every value of the partial engine is defined and lifts the
pure engine's value at that node. -/
theorem interp_lifts (hlex : ∀ w d', lex' w = some d' → ∃ d, lex w = some d ∧ d.Lifts d')
    (g : Assignment E) (t : Tree C L) {d' : PDenotation E W D} (h : interp lex' g t = some d') :
    ∃ d, Tree.interp lex g t = some d ∧ d.Lifts d' := by
  have hrel : ∀ w d', lex' w = some d' → ∃ c, lex w = some ⟨d'.1, c⟩ ∧ LiftsConst d'.1 c d'.2 := by
    intro w d' hd'
    obtain ⟨d, hd, hl⟩ := hlex w d' hd'
    cases hl with | @mk ty x y hxy => exact ⟨x, hd, y, rfl, hxy⟩
  obtain ⟨⟨τ, u'⟩, ht', rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨u, hu, hr⟩ := translate_rel lex hrel t ht'
  obtain ⟨z, hz, hl⟩ := hr.lifts g
  refine ⟨⟨τ, u.eval (fun c ↦ c) g⟩, ?_, ?_⟩
  · simp [Tree.interp, hu, Tree.evalAt]; rfl
  · simp only [hz]
    exact .mk hl

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
