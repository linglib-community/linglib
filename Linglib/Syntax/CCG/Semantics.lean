/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Semantics.Composition.Effect
public import Linglib.Semantics.Composition.Basic

/-!
# The semantics of CCG derivations

Each category has a semantic type. An atom has the type the grammar gives it, and `X/Y` and
`X\Y` both have the type of functions from the type of `Y` to the type of `X`: the direction and
the modality of a slash matter to word order and not to meaning. A lexical entry pairs a word
with a logical form of the type of its category. The meaning of a derivation is computed from
the meanings of its leaves: application applies a function to its argument, and composition
composes two functions beneath the arguments the rule passes on. Composition of functions is
associative, so [derivations that differ only in their bracketing have the same
meaning](##CCG.Derivation.interp_fcomp_assoc), the *spurious ambiguity* of CCG. The identity
behind it, at every degree, is `composeUnder_comp`.

## Implementation notes

A logical form is a function of what the constants of a signature denote, so an entry is the same
in every model. The combinatory rules are the binary rules of a many-sorted grammar over the
categories, and the meaning of a derivation is its value as a derivation of that grammar.

## TODO

* That the combinatory rules are derivable, composition and type raising being theorems of the
  Lambek calculus, belongs to the syntax of the calculus and is not stated here: the grammar
  takes the rules of a rule system as given.

## References

* [steedman-2000]
* [steedman-2019]
* [montague-1973]
* [karttunen-1989]
* [pareschi-steedman-1987]
-/

@[expose] public section

namespace CCG

open Interpreter ManySorted ManySorted.Language

variable {T α : Type*} {B : Type}

/-! ### Type correspondence -/

/-- `c.toTy τ` is the semantic type of the category `c` when each atom `a` has type `τ a`. -/
def Cat.toTy (τ : α → Ty B) : Cat α → Ty B
  | .atom a => τ a
  | .slash _ x _ y => y.toTy τ ⇒ x.toTy τ

@[simp] theorem Cat.toTy_forwardTypeRaise (τ : α → Ty B) (x t : Cat α) :
    (x.forwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

@[simp] theorem Cat.toTy_backwardTypeRaise (τ : α → Ty B) (x t : Cat α) :
    (x.backwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

/-! ### Derivation interpretation -/

variable (T) in
/-- A lexical entry of category `c` pairs a word with a logical form of the type of `c`, as
[steedman-2000] writes an entry `word := category : logical form`. The logical form is a function
of what the constants `K` denote, at whatever domains, so it is the same in every model. -/
structure LexEntry (τ : α → Ty B) (K : Ty B → Type*) (c : Cat α) where
  /-- The word. -/
  word : T
  /-- The logical form of the word at its category. -/
  lf : ∀ {D : B → Type}, (∀ {ty : Ty B}, K ty → ty.Dom D) → (c.toTy τ).Dom D

/-- The word and category of an entry, the pair a syntactic lexicon lists. -/
def LexEntry.toPair {τ : α → Ty B} {K : Ty B → Type*} (e : Σ c, LexEntry T τ K c) : T × Cat α :=
  (e.2.word, e.1)

/-- `composeUnder τ β f g` composes `f` with `g` beneath the arguments `β`, Curry's combinator
`Bⁿ` for `n` the length of `β`: it takes the arguments of `g`, outermost first, and applies `f`
to the result. -/
def composeUnder (τ : α → Ty B) {D : B → Type} : (β : List (Cat.Arg α)) → {x y : Cat α} →
    (y.toTy τ ⇒ x.toTy τ).Dom D → ((y.pushArgs β).toTy τ).Dom D →
      ((x.pushArgs β).toTy τ).Dom D
  | [], _, _, f, g => f g
  | ⟨s, m, z⟩ :: β, x, y, f, g =>
      composeUnder τ β (x := .slash s x m z) (y := .slash s y m z) (f ∘ ·) g

/-- Composing beneath arguments is associative: composing `f` after `g` and then with `h` beneath
`γ` is composing `f` with the composition of `g` and `h` beneath `γ`. -/
theorem composeUnder_comp (τ : α → Ty B) {D : B → Type} :
    ∀ (γ : List (Cat.Arg α)) {x y z : Cat α} (f : (y.toTy τ ⇒ x.toTy τ).Dom D)
      (g : (z.toTy τ ⇒ y.toTy τ).Dom D) (h : ((z.pushArgs γ).toTy τ).Dom D),
      composeUnder τ γ (x := x) (y := z) (f ∘ g) h =
        composeUnder τ γ f (composeUnder τ γ (x := y) (y := z) g h)
  | [], _, _, _, _, _, _ => rfl
  | ⟨s, m, w⟩ :: γ, x, y, z, f, g, h =>
      composeUnder_comp τ γ (x := .slash s x m w) (y := .slash s y m w) (z := .slash s z m w)
        (f ∘ ·) (g ∘ ·) h

/-- `r.sem τ` is the meaning of the rule `r` as an operation on its daughters' meanings, the
primary composed with the secondary beneath the arguments the rule passes on. -/
def Rule.sem (τ : α → Ty B) {D : B → Type} {R : RuleSystem α} : {l r c : Cat α} → Rule R l r c →
    (l.toTy τ).Dom D → (r.toTy τ).Dom D → (c.toTy τ).Dom D
  | _, _, _, .forward β _, f, g => composeUnder τ β f g
  | _, _, _, .backward β _, g, f => composeUnder τ β f g

/-- The combinatory rules of a rule system as the binary rules of a grammar over categories, so
that a derivation is a derivation of that grammar. -/
@[reducible] def grammar (R : RuleSystem α) : ManySorted.Language (Cat α) :=
  .mk₂ (fun _ _ ↦ PEmpty) (Rule R)

/-- A category's values are the meanings of its type, and a rule combines the meanings of its
daughters by `Rule.sem`. -/
instance (R : RuleSystem α) (τ : α → Ty B) (D : B → Type) :
    (grammar R).Structure fun c ↦ (c.toTy τ).Dom D :=
  .mk₂ nofun fun r ↦ r.sem τ

/-- A derivation as a derivation of the grammar of its rule system, over its leaves. -/
def Derivation.toDeriv {W : Cat α → Type*} {R : RuleSystem α} : {c : Cat α} →
    Derivation W R c → Deriv (grammar R) W c
  | _, .lex _ w => .leaf w
  | _, .node r d₁ d₂ => .binary r d₁.toDeriv d₂.toDeriv

section Interp

variable {W : Cat α → Type*} {R : RuleSystem α} {τ : α → Ty B} {K : Ty B → Type*} {D : B → Type}

/-- `d.realize τ ρ` is the meaning of the derivation `d` when `ρ` gives the meanings of its
leaves: the value of `d` as a derivation of the grammar of its rules. -/
def Derivation.realize (τ : α → Ty B) (ρ : ∀ c, W c → (c.toTy τ).Dom D) {c : Cat α}
    (d : Derivation W R c) : (c.toTy τ).Dom D :=
  d.toDeriv.realize (inferInstance : (grammar R).Structure fun c ↦ (c.toTy τ).Dom D)
    fun {c} w ↦ ρ c w

@[simp] theorem Derivation.realize_lex (ρ : ∀ c, W c → (c.toTy τ).Dom D) (c : Cat α) (w : W c) :
    (Derivation.lex c w : Derivation W R c).realize τ ρ = ρ c w := rfl

@[simp] theorem Derivation.realize_node (ρ : ∀ c, W c → (c.toTy τ).Dom D) {l r c : Cat α}
    (ru : Rule R l r c) (d₁ : Derivation W R l) (d₂ : Derivation W R r) :
    (Derivation.node ru d₁ d₂).realize τ ρ = ru.sem τ (d₁.realize τ ρ) (d₂.realize τ ρ) := rfl

variable (I : ∀ {ty : Ty B}, K ty → ty.Dom D)

/-- `d.interp I` is the meaning of the derivation `d` over lexical entries when the constants
denote by `I`, a leaf denoting the value of its logical form. -/
def Derivation.interp {c : Cat α} (d : Derivation (LexEntry T τ K) R c) : (c.toTy τ).Dom D :=
  d.realize τ fun _ e ↦ e.lf I

@[simp] theorem Derivation.interp_lex (c : Cat α) (e : LexEntry T τ K c) :
    (Derivation.lex c e : Derivation (LexEntry T τ K) R c).interp I = e.lf I := rfl

@[simp] theorem Derivation.interp_node {l r c : Cat α} (ru : Rule R l r c)
    (d₁ : Derivation (LexEntry T τ K) R l) (d₂ : Derivation (LexEntry T τ K) R r) :
    (Derivation.node ru d₁ d₂).interp I = ru.sem τ (d₁.interp I) (d₂.interp I) := rfl

/-- The derivation over the words of the entries. -/
def Derivation.words {c : Cat α} (d : Derivation (LexEntry T τ K) R c) :
    Derivation (fun _ ↦ T) R c :=
  d.map fun _ e ↦ e.word

end Interp

/-! ### Spurious ambiguity

Composition is associative, so left- and right-branching derivations of the same
composition-application chain receive the same interpretation, whatever the lexicon. This is
the local source of CCG's spurious ambiguity ([steedman-2000]). A chart parser may keep one
derivation per equivalence class, since reassociating `fcomp`/`fapp` (or `bcomp`/`bapp`)
nodes cannot change what a constituent means, and the matching-entry tests of
[karttunen-1989] and [pareschi-steedman-1987] exploit exactly this invariance. -/

section SpuriousAmbiguity

variable {R : RuleSystem α} {τ : α → Ty B} {K : Ty B → Type*} {D : B → Type}
  (I : ∀ {ty : Ty B}, K ty → ty.Dom D)

local notation "𝒟" => Derivation (LexEntry T τ K) R

/-- Reassociating a forward-composition chain preserves its interpretation, since composition
is associative. -/
theorem Derivation.interp_fcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (d₁ : 𝒟 (.slash .right x m y)) (d₂ : 𝒟 (.slash .right y n z))
    (d₃ : 𝒟 (.slash .right z p w)) (h₁ : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩])
    (h₂ : R x ⟨.right, n, z⟩ [⟨.right, p, w⟩]) (h₃ : R y ⟨.right, n, z⟩ [⟨.right, p, w⟩])
    (h₄ : R x ⟨.right, m, y⟩ [⟨.right, p, w⟩]) :
    (Derivation.fcomp (.fcomp d₁ d₂ h₁) d₃ h₂).interp I
      = (Derivation.fcomp d₁ (.fcomp d₂ d₃ h₃) h₄).interp I :=
  rfl

/-- Composing and then applying has the interpretation of applying twice, since
`(f ∘ g) x = f (g x)`. -/
theorem Derivation.interp_fapp_fcomp {x y z : Cat α} {m n : Modality}
    (d₁ : 𝒟 (.slash .right x m y)) (d₂ : 𝒟 (.slash .right y n z))
    (d₃ : 𝒟 z) (h₁ : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩])
    (h₂ : R x ⟨.right, n, z⟩ []) (h₃ : R y ⟨.right, n, z⟩ []) (h₄ : R x ⟨.right, m, y⟩ []) :
    (Derivation.fapp (.fcomp d₁ d₂ h₁) d₃ h₂).interp I
      = (Derivation.fapp d₁ (.fapp d₂ d₃ h₃) h₄).interp I :=
  rfl

theorem Derivation.interp_bcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (d₁ : 𝒟 (.slash .left y p z)) (d₂ : 𝒟 (.slash .left x n y))
    (d₃ : 𝒟 (.slash .left w m x)) (h₁ : R x ⟨.left, n, y⟩ [⟨.left, p, z⟩])
    (h₂ : R w ⟨.left, m, x⟩ [⟨.left, p, z⟩]) (h₃ : R w ⟨.left, m, x⟩ [⟨.left, n, y⟩])
    (h₄ : R w ⟨.left, n, y⟩ [⟨.left, p, z⟩]) :
    (Derivation.bcomp (.bcomp d₁ d₂ h₁) d₃ h₂).interp I
      = (Derivation.bcomp d₁ (.bcomp d₂ d₃ h₃) h₄).interp I :=
  rfl

theorem Derivation.interp_bapp_bcomp {x y w : Cat α} {m n : Modality}
    (d₁ : 𝒟 y) (d₂ : 𝒟 (.slash .left x n y))
    (d₃ : 𝒟 (.slash .left w m x)) (h₁ : R x ⟨.left, n, y⟩ [])
    (h₂ : R w ⟨.left, m, x⟩ []) (h₃ : R w ⟨.left, m, x⟩ [⟨.left, n, y⟩])
    (h₄ : R w ⟨.left, n, y⟩ []) :
    (Derivation.bapp (.bapp d₁ d₂ h₁) d₃ h₂).interp I
      = (Derivation.bapp d₁ (.bcomp d₂ d₃ h₃) h₄).interp I :=
  rfl

end SpuriousAmbiguity

end CCG
