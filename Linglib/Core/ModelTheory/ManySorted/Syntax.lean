module

public import Linglib.Core.ModelTheory.ManySorted.LanguageMap
public import Mathlib.Logic.Equiv.Defs

/-!
# Terms of a many-sorted language

The terms of a many-sorted language over sorted variables are built from variables and function
symbols, with pairing to assemble the arguments of a symbol. A term has a shape, and a term of one
sort is a term of the shape of that sort.

## Main definitions

* `ManySorted.Language.Term`: the terms over sorted variables, by shape.
* `ManySorted.Language.Term.bind`: substitution of terms for variables.
* `ManySorted.Signature.Place`: the argument places of a sort in a shape.
* `ManySorted.Language.Term.proj`: the component of a term at an argument place.
* `ManySorted.Language.Term.places`: the term whose components are the argument places.
* `ManySorted.Language.LHom.onTerm`: the term of a second language that a term is, along a map.
* `ManySorted.Language.Term.constantsVarsEquiv`: terms with constants are terms with extra
  variables.
-/

@[expose] public section

universe u v w w'

namespace ManySorted

variable {S : Type u} {L : Language.{u, v} S} {α : S → Type w} {β : S → Type w'}

/-- The terms of a language over variables `α`, by the shape of what they denote. -/
inductive Language.Term (L : Language.{u, v} S) (α : S → Type w) :
    Signature S → Type (max u v w)
  /-- A variable. -/
  | var {s : S} (x : α s) : Term L α (.of s)
  /-- A function symbol applied to a term of the shape of its arguments. -/
  | func {σ : Signature S} {t : S} (f : L.Functions σ t) (r : Term L α σ) : Term L α (.of t)
  /-- A pair of terms. -/
  | prod {σ τ : Signature S} (a : Term L α σ) (b : Term L α τ) : Term L α (.prod σ τ)
  /-- The empty tuple. -/
  | nil : Term L α .nil

/-- The argument places of sort `s` in a shape. -/
inductive Signature.Place : Signature S → S → Type u
  /-- The place of a single argument. -/
  | here {s : S} : Place (.of s) s
  /-- A place in the left component. -/
  | left {σ τ : Signature S} {s : S} (p : Place σ s) : Place (.prod σ τ) s
  /-- A place in the right component. -/
  | right {σ τ : Signature S} {s : S} (p : Place τ s) : Place (.prod σ τ) s

namespace Language.Term

/-- Substitution of terms for the variables. -/
def bind : {σ : Signature S} → L.Term α σ → (∀ {s : S}, α s → L.Term β (.of s)) → L.Term β σ
  | _, var x, θ => θ x
  | _, func f r, θ => func f (r.bind θ)
  | _, prod a b, θ => prod (a.bind θ) (b.bind θ)
  | _, nil, _ => nil

/-- The component of a term at an argument place of its shape. -/
def proj : {σ : Signature S} → {s : S} → σ.Place s → L.Term α σ → L.Term α (.of s)
  | _, _, .here, t => t
  | _, _, .left p, prod a _ => proj p a
  | _, _, .right p, prod _ b => proj p b

/-- The term of a shape whose components are its argument places. -/
def places : (σ : Signature S) → L.Term σ.Place σ
  | .nil => nil
  | .of _ => var .here
  | .prod σ τ => prod ((places σ).bind fun p ↦ var (.left p))
      ((places τ).bind fun p ↦ var (.right p))

end Language.Term

namespace Language

variable {L' L'' : Language.{u, v} S}

namespace LHom

/-- Maps a term's symbols along a language map. -/
def onTerm (φ : L →ᴸ L') : {σ : Signature S} → L.Term α σ → L'.Term α σ
  | _, .var x => .var x
  | _, .func f r => .func (φ.onFunction f) (φ.onTerm r)
  | _, .prod a b => .prod (φ.onTerm a) (φ.onTerm b)
  | _, .nil => .nil

@[simp] theorem id_onTerm {σ : Signature S} (t : L.Term α σ) : (LHom.id L).onTerm t = t := by
  induction t with
  | var x => rfl
  | func f r ih => simp only [onTerm, ih, id_onFunction, id_eq]
  | prod a b iha ihb => simp only [onTerm, iha, ihb]
  | nil => rfl

@[simp] theorem comp_onTerm (ψ : L' →ᴸ L'') (φ : L →ᴸ L') {σ : Signature S} (t : L.Term α σ) :
    (ψ ∘ᴸ φ).onTerm t = ψ.onTerm (φ.onTerm t) := by
  induction t with
  | var x => rfl
  | func f r ih => simp only [onTerm, ih, comp_onFunction]
  | prod a b iha ihb => simp only [onTerm, iha, ihb]
  | nil => rfl

end LHom

namespace Term

variable {γ : S → Type v}

/-- Sends a term with constants to a term with extra variables. -/
def constantsToVars :
    {σ : Signature S} → (L.withConstants γ).Term α σ → L.Term (fun s ↦ γ s ⊕ α s) σ
  | _, var a => var (.inr a)
  | _, func (.inl f) r => func f r.constantsToVars
  | _, func (σ := σ) (.inr c) _ =>
    match σ, c with
    | .nil, c => var (.inl c)
  | _, prod a b => prod a.constantsToVars b.constantsToVars
  | _, nil => nil

/-- Sends a term with extra variables to a term with constants. -/
def varsToConstants :
    {σ : Signature S} → L.Term (fun s ↦ γ s ⊕ α s) σ → (L.withConstants γ).Term α σ
  | _, var (.inr a) => var a
  | _, var (.inl c) => func (L.con c) nil
  | _, func f r => func (.inl f) r.varsToConstants
  | _, prod a b => prod a.varsToConstants b.varsToConstants
  | _, nil => nil

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquiv {σ : Signature S} :
    (L.withConstants γ).Term α σ ≃ L.Term (fun s ↦ γ s ⊕ α s) σ where
  toFun := constantsToVars
  invFun := varsToConstants
  left_inv t := by
    induction t with
    | var a => rfl
    | @func σ _ f r ih =>
      cases f with
      | inl f => simp only [constantsToVars, varsToConstants, ih]
      | inr c =>
        cases σ with
        | nil => cases r; rfl
        | of _ => exact nomatch c
        | prod _ _ => exact nomatch c
    | prod a b iha ihb => simp only [constantsToVars, varsToConstants, iha, ihb]
    | nil => rfl
  right_inv t := by
    induction t with
    | var x => cases x <;> rfl
    | func f r ih => simp only [varsToConstants, constantsToVars, ih]
    | prod a b iha ihb => simp only [varsToConstants, constantsToVars, iha, ihb]
    | nil => rfl

end Term

end Language

end ManySorted
