module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Semantics.Composition.Effect
public import Linglib.Semantics.Composition.Basic

/-!
# The CCG syntax-semantics interface

A typing of the atoms extends to every category, sending `X/Y` and `X\Y` to the function type
from the type of `Y` to that of `X` and ignoring slash modalities, which control combinatory
potential rather than meaning. Since a `Derivation` is indexed by its category, its
interpretation needs no run-time category checks: a rule instance `X/Y Yβ ⇒ Xβ` composes its
daughters' meanings beneath the arguments `β`, Curry's combinator `Bⁿ` for `n` the length of `β`,
so application is function application and first-order composition is Steedman's `B`.
A lexical entry of a category pairs a word with a logical form of the category's type, a function
of what the constants of a signature denote, so an entry is the same in every model. Type-raising
and coordination are lexical, so their logical forms (the Montague lift, generalized conjunction)
are entries' logical forms. The combinatory rules are the binary rules of a grammar over
categories, and the meaning of a derivation whose leaves are lexical entries is its value as a
derivation of that grammar.

## Main definitions

* `CCG.Cat.toTy`: the semantic type of a category under a typing of its atoms.
* `CCG.LexEntry`: a lexical entry of a category, a word with a logical form.
* `CCG.composeUnder`: composition beneath an argument sequence, Curry's `Bⁿ`.
* `CCG.grammar`: the combinatory rules of a rule system as a grammar over categories.
* `CCG.Derivation.interp`: the meaning of a derivation over lexical entries in an interpretation
  of the constants, and `CCG.Derivation.words`, the derivation over its words.

## Main statements

* `CCG.Derivation.interp_fcomp_assoc`, `CCG.Derivation.interp_fapp_fcomp` and their backward
  mirrors: in every rule system, reassociating a composition-application chain does not change
  its interpretation, the source of CCG's spurious ambiguity.

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

variable {R : RuleSystem α} {τ : α → Ty B} {K : Ty B → Type*} {D : B → Type}
  (I : ∀ {ty : Ty B}, K ty → ty.Dom D)

/-- `d.interp I` is the meaning of the derivation `d` over lexical entries when the constants
denote by `I`: the value of `d` as a derivation of the grammar of its rules, a leaf denoting the
value of its logical form. -/
def Derivation.interp {c : Cat α} (d : Derivation (LexEntry T τ K) R c) : (c.toTy τ).Dom D :=
  d.toDeriv.realize (inferInstance : (grammar R).Structure fun c ↦ (c.toTy τ).Dom D)
    fun e ↦ e.lf I

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
