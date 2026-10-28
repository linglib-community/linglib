module

public import Mathlib.Data.PFun
public import Linglib.Logic.Trivalent.Part
public import Linglib.Semantics.Composition.Tree

/-!
# Partial interpretation

A word with a definedness condition, such as the definite article, denotes a partial function in
Heim and Kratzer. A node has a value only where its daughters do and the function among them is
defined at its argument, and a sentence that composes but has no value suffers presupposition
failure, as distinct from uninterpretability, where the types do not compose.
[Every mode is strict](##dom_right_of_dom_evalPartial), and on a lexicon lifting a total one
[the partial engine's values lift the total engine's](##interpPartial_lifts), so such a lexicon
[has no presupposition failure](##not_presupFailure_of_lifts).

## Main definitions

* `Montague.Ty.PDomain`, `Montague.PDenotation`: the partial domains and denotations.
* `Montague.Mode.evalPartial`: the partial denotation of a mode.
* `Montague.Interpretation.partial`, `Montague.Term.evalPartial`: the partial interpretation of
  terms, and a term's partial denotation in it.
* `PhraseStructure.Tree.interpPartial`: the partial engine, evaluating a tree's term.
* `PhraseStructure.Tree.Uninterpretable`, `PhraseStructure.Tree.PresupFailure`: the two ways of
  lacking a value.
* `Montague.Ty.Lifts`, `Montague.Denotation.Lifts`: the relation of a total denotation to a
  partial one lifting it, with `Montague.Ty.Domain.toPartial` the lift at a first-order type.

## Implementation notes

A partial function is mathlib's `PFun`, and a node denotes a `Part` value of its type. The engine
evaluates the term a tree translates to (`PhraseStructure.Tree.translate`), so Predicate
Abstraction needs no distributor; uninterpretability is the engine returning no denotation, and
presupposition failure its returning an undefined one. `Ty.PDomain` interprets a function type by
the partial functions `a → Part b`, with partiality inside the arrow: the call-by-value monadic
interpretation of the types at `Part`, of which `Ty.Domain` is the case at `Id`. The effectful
engine of `Composition/Tree.lean` at `M = Part` is a different engine, with partiality outside the
arrow, `Part (a → b)`. There a Fregean definite, defined on some predicates and undefined on
others, has no value, and Predicate Abstraction would be defined only where the body is defined
at every entity.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

namespace Montague

/-- Partial denotation domains, as `Ty.Domain` but with functions the partial functions `→.`,
whose domain is a lexical entry's definedness condition. -/
abbrev Ty.PDomain (E W : Type) (ty : Ty) (S : Sorts := {}) : Type :=
  match ty with
  | .e => E
  | .t => Prop
  | .d => S.degree
  | .n => ℕ
  | .v => S.eventuality
  | .s => W
  | .fn a b => Ty.PDomain E W a S →. Ty.PDomain E W b S
  | .comp (.reader ι) b => Ty.PDomain E W ι S →. Ty.PDomain E W b S

/-- A partial denotation is a semantic type with a possibly undefined value in its partial
domain. -/
abbrev PDenotation (E W : Type) (S : Sorts := {}) : Type :=
  (ty : Ty) × Part (Ty.PDomain E W ty S)

/-! ### Partial denotations of the modes and terms -/

section Evaluation

variable {E W : Type} {S : Sorts} {σ₁ σ₂ τ : Ty}

/-- The partial denotation of a mode, defined where both daughters are and the function or role
head among them is defined at its argument. -/
def Mode.evalPartial : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → Part (Ty.PDomain E W σ₁ S) →
    Part (Ty.PDomain E W σ₂ S) → Part (Ty.PDomain E W τ S)
  | _, _, _, .functionalLeft, f, a => f.bind fun fv ↦ a.bind fv
  | _, _, _, .functionalRight, a, f => f.bind fun fv ↦ a.bind fv
  | _, _, _, .predicateModification, p, q => p.bind fun P ↦ q.bind fun Q ↦
      Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b
  | _, _, _, .eventIdentificationLeft, f, p => f.bind fun F ↦ p.bind fun P ↦
      Part.some fun x ↦ (F x).map fun Fx e ↦ (Fx e).bind fun a ↦ (P e).map fun b ↦ a ∧ b
  | _, _, _, .eventIdentificationRight, p, f => f.bind fun F ↦ p.bind fun P ↦
      Part.some fun x ↦ (F x).map fun Fx e ↦ (Fx e).bind fun a ↦ (P e).map fun b ↦ a ∧ b
  | _, _, _, .mapRight (f := .reader _) m, a, b =>
      a.bind fun av ↦ b.map fun bv i ↦ m.evalPartial (Part.some av) (bv i)
  | _, _, _, .mapLeft (f := .reader _) m, a, b =>
      a.bind fun av ↦ b.map fun bv i ↦ m.evalPartial (av i) (Part.some bv)
  | _, _, _, .unitRight (f := .reader _) m, a, b =>
      m.evalPartial (a.map fun av x ↦ av fun _ ↦ Part.some x) b
  | _, _, _, .unitLeft (f := .reader _) m, a, b =>
      m.evalPartial a (b.map fun bv y ↦ bv fun _ ↦ Part.some y)

/-- Every mode is strict in its left daughter. -/
theorem Mode.dom_left_of_dom_evalPartial (m : Mode σ₁ σ₂ τ) {a : Part (Ty.PDomain E W σ₁ S)}
    {b : Part (Ty.PDomain E W σ₂ S)} (h : (m.evalPartial a b).Dom) : a.Dom := by
  induction m with
  | @unitRight f _ _ _ _ _ ih => cases f; exact ih h
  | @unitLeft f _ _ _ _ _ ih => cases f; exact ih h
  | @mapRight f => cases f; exact h.1
  | @mapLeft f => cases f; exact h.1
  | functionalLeft | functionalRight | predicateModification | eventIdentificationLeft
  | eventIdentificationRight =>
    obtain ⟨h₁, h₂⟩ := h; first | exact h₁ | exact Part.Dom.of_bind h₂

/-- Every mode is strict in its right daughter. -/
theorem Mode.dom_right_of_dom_evalPartial (m : Mode σ₁ σ₂ τ) {a : Part (Ty.PDomain E W σ₁ S)}
    {b : Part (Ty.PDomain E W σ₂ S)} (h : (m.evalPartial a b).Dom) : b.Dom := by
  induction m with
  | @unitRight f _ _ _ _ _ ih => cases f; exact ih h
  | @unitLeft f _ _ _ _ _ ih => cases f; exact ih h
  | @mapRight f => cases f; exact h.2
  | @mapLeft f => cases f; exact h.2
  | functionalLeft | functionalRight | predicateModification | eventIdentificationLeft
  | eventIdentificationRight =>
    obtain ⟨h₁, h₂⟩ := h; first | exact h₁ | exact Part.Dom.of_bind h₂

open scoped Assignment

/-- The partial interpretation: a term's value is a possibly undefined partial denotation, an
abstraction is the partial function undefined wherever its body is, and a composition is defined
where its daughters are and the function among them is defined at its argument. -/
def Interpretation.partial {K : Ty → Type*} (I : ∀ {ty : Ty}, K ty → Part (Ty.PDomain E W ty S)) :
    Interpretation K where
  D ty := Part (Ty.PDomain E W ty S)
  Val ty := Ty.PDomain E W ty S
  const := I
  var x := Part.some x
  lam f := Part.some f
  mode m := m.evalPartial

/-- The partial denotation of a term under a partial interpretation of the constants and an
assignment. -/
def Term.evalPartial {Γ : ℕ → Ty} {K : Ty → Type*}
    (I : ∀ {ty : Ty}, K ty → Part (Ty.PDomain E W ty S)) (g : ∀ n, Ty.PDomain E W (Γ n) S)
    {ty : Ty} (t : Term Γ K ty) : Part (Ty.PDomain E W ty S) :=
  t.realize (.partial I) g

@[simp] theorem Term.evalPartial_lam {Γ : ℕ → Ty} {K : Ty → Type*}
    (I : ∀ {ty : Ty}, K ty → Part (Ty.PDomain E W ty S)) (g : ∀ n, Ty.PDomain E W (Γ n) S)
    (n : ℕ) {τ : Ty} (b : Term Γ K τ) :
    (Term.lam n b).evalPartial I g = Part.some fun x ↦ b.evalPartial I (g[n ↦ x]) :=
  rfl

@[simp] theorem Term.evalPartial_comp {Γ : ℕ → Ty} {K : Ty → Type*}
    (I : ∀ {ty : Ty}, K ty → Part (Ty.PDomain E W ty S)) (g : ∀ n, Ty.PDomain E W (Γ n) S)
    {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) (l : Term Γ K σ₁) (r : Term Γ K σ₂) :
    (Term.comp m l r).evalPartial I g = m.evalPartial (l.evalPartial I g) (r.evalPartial I g) :=
  rfl

end Evaluation

section Composition

variable {E W : Type} {S : Sorts}

/-! ### Composition of defined daughters

These are rewriting lemmas rather than `simp` lemmas, since the reducible `Ty.PDomain` keys a
concrete domain and a variable one differently for `simp`'s index. For the same reason, a `Part`
redex at a concrete type, such as `(Part.some f).bind k` after `Mode.evalPartial` unfolds, is
rewritten by `erw`, not `rw`. -/

theorem Mode.combine?_evalPartial_fn_left {σ τ : Ty} (f : Ty.PDomain E W (σ ⇒ τ) S)
    (a : Ty.PDomain E W σ S) :
    Mode.combine? Mode.evalPartial (⟨σ ⇒ τ, Part.some f⟩ : PDenotation E W S) ⟨σ, Part.some a⟩ =
      some ⟨τ, f a⟩ := by
  rw [Mode.combine?_fn_left]; simp [Mode.evalPartial]

theorem Mode.combine?_evalPartial_fn_right {σ τ : Ty} (a : Ty.PDomain E W σ S)
    (f : Ty.PDomain E W (σ ⇒ τ) S) :
    Mode.combine? Mode.evalPartial (⟨σ, Part.some a⟩ : PDenotation E W S) ⟨σ ⇒ τ, Part.some f⟩ =
      some ⟨τ, f a⟩ := by
  rw [Mode.combine?_fn_right]; simp [Mode.evalPartial]

theorem Mode.combine?_evalPartial_predicateModification (P Q : Ty.PDomain E W (.e ⇒ .t) S) :
    Mode.combine? Mode.evalPartial (⟨.e ⇒ .t, Part.some P⟩ : PDenotation E W S)
        ⟨.e ⇒ .t, Part.some Q⟩ =
      some ⟨.e ⇒ .t, Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b⟩ := by
  rw [Mode.combine?_predicateModification]; simp [Mode.evalPartial]

/-- The value of an interpreted daughter at the type `τ`, which is undefined where the daughter
is uninterpretable or of another type. -/
def valueAtPartial (τ : Ty) : Option (PDenotation E W S) → Part (Ty.PDomain E W τ S)
  | some ⟨ty, v⟩ => if h : ty = τ then h ▸ v else Part.none
  | none => Part.none

end Composition

/-! ### Total lexica

A partial denotation lifts a total one when it agrees with it at a base type and, at a function
type, is defined on every lift of an argument with a value lifting the total function's value.
On a lexicon whose entries lift a total lexicon, every value of the partial engine is defined and
lifts the pure engine's value at the same node, since both evaluate the same term and every mode
preserves the lift; so a total lexicon has no presupposition failures. -/

section Total

variable {E W : Type} {S : Sorts}

open scoped Assignment

/-- The lifting relation between a total denotation and a partial one of the same type. -/
def Ty.Lifts : (ty : Ty) → Ty.Domain E W ty S → Ty.PDomain E W ty S → Prop
  | .e, x, y => x = y
  | .t, x, y => x = y
  | .d, x, y => x = y
  | .n, x, y => x = y
  | .v, x, y => x = y
  | .s, x, y => x = y
  | .fn a b, f, f' => ∀ x y, Ty.Lifts a x y → ∃ z, f' y = Part.some z ∧ Ty.Lifts b (f x) z
  | .comp (.reader ι) b, f, f' =>
    ∀ x y, Ty.Lifts ι x y → ∃ z, f' y = Part.some z ∧ Ty.Lifts b (f x) z

@[simp] theorem Ty.lifts_e {x y : E} : Ty.Lifts (E := E) (W := W) (S := S) .e x y ↔ x = y :=
  Iff.rfl

@[simp] theorem Ty.lifts_t {x y : Prop} : Ty.Lifts (E := E) (W := W) (S := S) .t x y ↔ x = y :=
  Iff.rfl

theorem Ty.lifts_fn {a b : Ty} {f : Ty.Domain E W (a ⇒ b) S} {f' : Ty.PDomain E W (a ⇒ b) S} :
    Ty.Lifts (a ⇒ b) f f' ↔
      ∀ x y, Ty.Lifts a x y → ∃ z, f' y = Part.some z ∧ Ty.Lifts b (f x) z :=
  Iff.rfl

theorem Ty.lifts_lift {b : Ty} {f : E → Ty.Domain E W b S} {f' : E → Ty.PDomain E W b S}
    (h : ∀ x, Ty.Lifts b (f x) (f' x)) : Ty.Lifts (.e ⇒ b) f (PFun.lift f') :=
  fun x _ hxy ↦ ⟨f' x, hxy ▸ rfl, h x⟩

/-- A partial denotation lifts a total one when it has the same type and a defined value that
lifts the total value. -/
inductive Denotation.Lifts : Denotation E W Id S → PDenotation E W S → Prop
  | mk {ty : Ty} {x : Ty.Domain E W ty S} {y : Ty.PDomain E W ty S} (h : Ty.Lifts ty x y) :
      Denotation.Lifts ⟨ty, x⟩ ⟨ty, Part.some y⟩

theorem Denotation.Lifts.fst {d : Denotation E W Id S} {d' : PDenotation E W S}
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
  | fn {b : Ty} : FirstOrder b → FirstOrder (.e ⇒ b)
  | intens {a : Ty} : FirstOrder a → FirstOrder (.intens a)

/-- The partial denotation a total one lifts to, defined everywhere on individual arguments
and nowhere on a function argument. -/
def Ty.Domain.toPartial : (ty : Ty) → Ty.Domain E W ty S → Ty.PDomain E W ty S
  | .e, x => x
  | .t, x => x
  | .d, x => x
  | .n, x => x
  | .v, x => x
  | .s, x => x
  | .fn .e b, f => PFun.lift fun x ↦ toPartial b (f x)
  | .intens a, f => PFun.lift fun w ↦ toPartial a (f w)
  | .fn _ _, _ => fun _ ↦ Part.none
  | .comp (.reader _) _, _ => fun _ ↦ Part.none

theorem Ty.lifts_toPartial {ty : Ty} (h : ty.FirstOrder) (x : Ty.Domain E W ty S) :
    Ty.Lifts ty x (Ty.Domain.toPartial ty x) := by
  induction h with
  | fn _ ih => exact Ty.lifts_lift fun x ↦ ih _
  | intens _ ih => exact fun _ _ hw ↦ ⟨_, hw ▸ rfl, ih _⟩
  | _ => rfl

/-- The partial denotation a total one lifts to. -/
def Denotation.toPartial (d : Denotation E W Id S) : PDenotation E W S :=
  ⟨d.1, Part.some (Ty.Domain.toPartial d.1 d.2)⟩

theorem Denotation.lifts_toPartial {d : Denotation E W Id S} (h : d.1.FirstOrder) :
    d.Lifts d.toPartial := by
  obtain ⟨ty, x⟩ := d
  exact .mk (Ty.lifts_toPartial h x)

/-- Every mode preserves the lift, since on defined daughters that lift total ones a mode's
partial value is defined and lifts its total value. -/
theorem Mode.lifts_evalPartial {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) {a : Ty.Domain E W σ₁ S}
    {b : Ty.Domain E W σ₂ S} {a' : Ty.PDomain E W σ₁ S} {b' : Ty.PDomain E W σ₂ S}
    (ha : Ty.Lifts σ₁ a a') (hb : Ty.Lifts σ₂ b b') :
    ∃ z, m.evalPartial (Part.some a') (Part.some b') = Part.some z ∧ Ty.Lifts τ (m.eval a b) z := by
  induction m with
  | @mapRight f _ _ _ m ih =>
    cases f
    refine ⟨fun i ↦ m.evalPartial (Part.some a') (b' i), by simp [evalPartial], fun x y hxy ↦ ?_⟩
    obtain ⟨w, hw, hlw⟩ := hb x y hxy
    obtain ⟨z, hz, hlz⟩ := ih ha hlw
    exact ⟨z, by simp only [hw, hz], hlz⟩
  | @mapLeft f _ _ _ m ih =>
    cases f
    refine ⟨fun i ↦ m.evalPartial (a' i) (Part.some b'), by simp [evalPartial], fun x y hxy ↦ ?_⟩
    obtain ⟨w, hw, hlw⟩ := ha x y hxy
    obtain ⟨z, hz, hlz⟩ := ih hlw hb
    exact ⟨z, by simp only [hw, hz], hlz⟩
  | @unitRight f _ _ _ _ m ih =>
    cases f
    simpa [evalPartial, eval, Eff.pure] using
      ih (a := fun x ↦ a fun _ ↦ x) (a' := fun x ↦ a' fun _ ↦ Part.some x)
        (fun x y hxy ↦ ha (fun _ ↦ x) (fun _ ↦ Part.some y) fun _ _ _ ↦ ⟨y, rfl, hxy⟩) hb
  | @unitLeft f _ _ _ _ m ih =>
    cases f
    simpa [evalPartial, eval, Eff.pure] using
      ih (b := fun y ↦ b fun _ ↦ y) (b' := fun y ↦ b' fun _ ↦ Part.some y) ha
        (fun x y hxy ↦ hb (fun _ ↦ x) (fun _ ↦ Part.some y) fun _ _ _ ↦ ⟨y, rfl, hxy⟩)
  | functionalLeft => simpa [evalPartial, eval] using ha b b' hb
  | functionalRight => simpa [evalPartial, eval] using hb a a' ha
  | predicateModification =>
    refine ⟨_, by simp [evalPartial]; rfl, Ty.lifts_fn.mpr fun x y hxy ↦ ?_⟩
    obtain ⟨p, hp, hlp⟩ := ha x y hxy
    obtain ⟨q, hq, hlq⟩ := hb x y hxy
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
def LiftsConst (ty : Ty) (c : Id (Ty.Domain E W ty S)) (c' : Part (Ty.PDomain E W ty S)) : Prop :=
  ∃ y, c' = Part.some y ∧ Ty.Lifts ty c y

theorem Term.Rel.lifts {Γ : ℕ → Ty} {ty : Ty} {u : Term Γ (fun ty ↦ Id (Ty.Domain E W ty S)) ty}
    {u' : Term Γ (fun ty ↦ Part (Ty.PDomain E W ty S)) ty} (h : Term.Rel LiftsConst u u')
    {g : ∀ n, Ty.Domain E W (Γ n) S} {g' : ∀ n, Ty.PDomain E W (Γ n) S}
    (hg : ∀ n, Ty.Lifts (Γ n) (g n) (g' n)) :
    ∃ z, u'.evalPartial (fun c ↦ c) g' = Part.some z ∧ Ty.Lifts ty (u.eval (fun c ↦ c) g) z :=
  h.realize (A := .total fun c ↦ c) (B := .partial fun c ↦ c)
    (fun ty x (y : Part (Ty.PDomain E W ty S)) ↦ LiftsConst ty x y) Ty.Lifts (fun _ _ hc ↦ hc)
    (fun _ y h ↦ ⟨y, rfl, h⟩) (fun _ f' h ↦ ⟨f', rfl, fun x y hxy ↦ h x y hxy⟩)
    (fun m _ _ _ _ ⟨_, hzl, hll⟩ ⟨_, hzr, hlr⟩ ↦ by
      subst hzl hzr; exact m.lifts_evalPartial hll hlr)
    hg

variable {L : Type*} {lex : L → Option (Denotation E W Id S)}

theorem lifts_map_toPartial (h : ∀ w d, lex w = some d → d.1.FirstOrder) (w : L)
    (d' : PDenotation E W S) (h' : (lex w).map Denotation.toPartial = some d') :
    ∃ d, lex w = some d ∧ d.Lifts d' := by
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h'
  exact ⟨d, hd, Denotation.lifts_toPartial (h w d hd)⟩

end Total

end Montague

namespace PhraseStructure.Tree

open Montague
open scoped Assignment

variable {E W : Type} {S : Sorts}

/-! ### Partial interpretation -/

section Partial

variable {C : Type} {L : Type*}

/-- The partial denotation of a tree under an assignment is its term's partial denotation, with each
word's partial denotation its constant. A terminal denotes what its leaf interpretation gives it, a
binary node what the mode its daughters' types select composes, a trace the value of its index, and
a binder the partial function abstracting over its index in the body. -/
def interpPartial (lex : L → Option (PDenotation E W S)) (g : Assignment E) (t : Tree C L) :
    Option (PDenotation E W S) :=
  (translate individualIndices (K := fun ty ↦ Part (Ty.PDomain E W ty S)) lex t).map fun d ↦
    ⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩

private theorem map_bind_combine (g : Assignment E)
    (t₁ t₂ : Option (Σ ty, Term individualIndices (fun ty ↦ Part (Ty.PDomain E W ty S)) ty)) :
    (t₁.bind fun d₁ ↦ t₂.bind fun d₂ ↦ Mode.combine? (fun m l r ↦ .comp m l r) d₁ d₂).map
        (fun d ↦ (⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩ : PDenotation E W S)) =
      (t₁.map fun d ↦ ⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩).bind fun d₁ ↦
        (t₂.map fun d ↦ ⟨d.1, d.2.evalPartial (fun c ↦ c) g⟩).bind fun d₂ ↦
          Mode.combine? Mode.evalPartial d₁ d₂ := by
  rcases t₁ with _ | ⟨τ₁, u₁⟩ <;> rcases t₂ with _ | ⟨τ₂, u₂⟩ <;> try rfl
  simp only [Option.bind_some, Option.map_some, Mode.combine?, Option.map_map]
  rfl

variable (lex lex' : L → Option (PDenotation E W S)) (g g' : Assignment E)

@[simp] theorem interpPartial_terminal (c : C) (w : L) :
    interpPartial lex g (.terminal c w : Tree C L) = lex w := by
  simp only [interpPartial, translate_terminal, Option.map_map]
  cases lex w <;> rfl

@[simp] theorem interpPartial_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    interpPartial lex g (.phrase c k (t :: [])) = interpPartial lex g t := rfl

@[simp] theorem interpPartial_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    interpPartial lex g (.phrase c k (t₁ :: t₂ :: [])) = (interpPartial lex g t₁).bind fun d₁ ↦
      (interpPartial lex g t₂).bind fun d₂ ↦ Mode.combine? Mode.evalPartial d₁ d₂ :=
  map_bind_combine g _ _

@[simp] theorem interpPartial_trace (n : ℕ) (c : C) :
    interpPartial lex g (.trace n c : Tree C L) = some ⟨.e, Part.some (g n)⟩ := rfl

@[simp] theorem interpPartial_bind (n : ℕ) (c : C) (body : Tree C L) :
    interpPartial lex g (.bind n c body) = (interpPartial lex g body).map fun d ↦
      ⟨.fn .e d.1, Part.some fun x ↦ valueAtPartial d.1 (interpPartial lex (g[n ↦ x]) body)⟩ := by
  simp only [interpPartial, translate_bind, Option.map_map]
  rcases translate individualIndices (K := fun ty ↦ Part (Ty.PDomain E W ty S)) lex body with
    _ | ⟨τ, b⟩
  · rfl
  · simp [valueAtPartial]

theorem interpPartial_junk {l : PhraseStructure.Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ PhraseStructure.Tree.Label.Licenses l (cs.map RoseTree.value)) :
    interpPartial lex g (RoseTree.node l cs) = none := by
  simp only [interpPartial, translate_junk _ h, Option.map_none]

/-! ### Uninterpretability and presupposition failure -/

/-- A tree is uninterpretable when the engine assigns it no denotation. -/
def Uninterpretable (t : Tree C L) : Prop := interpPartial lex g t = none

/-- A tree is a presupposition failure when its denotation is undefined. -/
def PresupFailure (t : Tree C L) : Prop := ∃ d, interpPartial lex g t = some d ∧ ¬ d.2.Dom

/-- A sentence fails exactly where its three-valued readout is undefined, so the engine's
denotations and Strong Kleene propositions agree on presupposition failure. -/
theorem presupFailure_iff_ofPart_eq_zero {t : Tree C L} {v : Part Prop}
    (h : interpPartial lex g t = some ⟨.t, v⟩) :
    PresupFailure lex g t ↔ SignType.ofPart v = 0 := by
  rw [PresupFailure, SignType.ofPart_eq_zero_iff, h]
  simp

theorem interpPartial_map_fst_congr (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1))
    (t : Tree C L) :
    (interpPartial lex g t).map (·.1) = (interpPartial lex' g' t).map (·.1) := by
  simp only [interpPartial, Option.map_map, Function.comp_def]
  exact translate_map_fst lex h t

/-- Uninterpretability is decided by the leaves' types alone. -/
theorem uninterpretable_congr (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    Uninterpretable lex g t ↔ Uninterpretable lex' g' t := by
  have := interpPartial_map_fst_congr lex lex' g g' h t
  constructor
  · intro hn; rw [hn] at this; exact Option.map_eq_none_iff.mp this.symm
  · intro hn; rw [hn] at this; exact Option.map_eq_none_iff.mp this

end Partial

section Total

variable {C : Type} {L : Type*} {lex : L → Option (Denotation E W Id S)}
  {lex' : L → Option (PDenotation E W S)}

/-- On a lexicon lifting a total one, every value of the partial engine is defined and lifts the
pure engine's value at that node. -/
theorem interpPartial_lifts (hlex : ∀ w d', lex' w = some d' → ∃ d, lex w = some d ∧ d.Lifts d')
    (g : Assignment E) (t : Tree C L) {d' : PDenotation E W S}
    (h : interpPartial lex' g t = some d') :
    ∃ d, Tree.interp lex g t = some d ∧ d.Lifts d' := by
  have hrel : ∀ w d', lex' w = some d' → ∃ c, lex w = some ⟨d'.1, c⟩ ∧ LiftsConst d'.1 c d'.2 := by
    intro w d' hd'
    obtain ⟨d, hd, hl⟩ := hlex w d' hd'
    cases hl with | @mk ty x y hxy => exact ⟨x, hd, y, rfl, hxy⟩
  obtain ⟨⟨τ, u'⟩, ht', rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨u, hu, hr⟩ := translate_rel lex hrel t ht'
  obtain ⟨z, hz, hl⟩ := hr.lifts (g := g) (g' := g) fun _ ↦ rfl
  refine ⟨⟨τ, u.eval (fun c ↦ c) g⟩, ?_, ?_⟩
  · simp [Tree.interp, hu, evalAt]; rfl
  · simp only [hz]
    exact .mk hl

/-- A lexicon lifting a total one has no presupposition failures. -/
theorem not_presupFailure_of_lifts
    (hlex : ∀ w d', lex' w = some d' → ∃ d, lex w = some d ∧ d.Lifts d') (g : Assignment E)
    (t : Tree C L) : ¬ PresupFailure lex' g t := by
  rintro ⟨d', hd', hdom⟩
  obtain ⟨d, -, hl⟩ := interpPartial_lifts hlex g t hd'
  cases hl
  exact hdom trivial

theorem not_presupFailure_map_toPartial (h : ∀ w d, lex w = some d → d.1.FirstOrder)
    (g : Assignment E) (t : Tree C L) :
    ¬ PresupFailure (fun w ↦ (lex w).map Denotation.toPartial) g t :=
  not_presupFailure_of_lifts (lifts_map_toPartial h) g t

end Total

end PhraseStructure.Tree
