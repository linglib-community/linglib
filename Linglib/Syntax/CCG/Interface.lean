module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Semantics.Composition.Ty

/-!
# The CCG syntax-semantics interface

A typing of the atoms extends to every category, sending `X/Y` and `X\Y` to the function type
from the type of `Y` to that of `X` and ignoring slash modalities, which control combinatory
potential rather than meaning. Since a `Derivation` is indexed by its category, its
interpretation needs no run-time category checks: a rule instance `X/Y Yβ ⇒ Xβ` composes its
daughters' meanings beneath the arguments `β`, Curry's combinator `Bⁿ` for `n` the length of `β`,
so application is function application and first-order composition is Steedman's `B`.
Type-raising and coordination are lexical, so their meanings (the Montague lift, generalized
conjunction) come from the lexicon. A lexicon returns meanings at the queried category, so the
interface is sound by typing rather than by a theorem.

## Main definitions

* `CCG.Cat.toTy`: the semantic type of a category under a typing of its atoms.
* `CCG.SemLexicon`: a semantic lexicon, giving a word an optional meaning at each category.
* `CCG.composeUnder`: composition beneath an argument sequence, Curry's `Bⁿ`.
* `CCG.Derivation.interp`: the meaning of a derivation, `none` only when a word is missing from
  the lexicon.

## Main statements

* `CCG.Derivation.interp_fcomp_assoc`, `CCG.Derivation.interp_fapp_fcomp` and their backward
  mirrors: in every rule system, reassociating a composition-application chain does not change
  its interpretation, the source of CCG's spurious ambiguity.

## References

* [steedman-2000]
* [steedman-2019]
* [karttunen-1989]
* [pareschi-steedman-1987]
-/

@[expose] public section

namespace CCG

open Montague

variable {T α : Type*}

/-! ### Type correspondence -/

/-- `c.toTy τ` is the semantic type of the category `c` when each atom `a` has type `τ a`. -/
def Cat.toTy (τ : α → Ty) : Cat α → Ty
  | .atom a => τ a
  | .rslash x _ y => y.toTy τ ⇒ x.toTy τ
  | .lslash x _ y => y.toTy τ ⇒ x.toTy τ

@[simp] theorem Cat.toTy_forwardTypeRaise (τ : α → Ty) (x t : Cat α) :
    (x.forwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

@[simp] theorem Cat.toTy_backwardTypeRaise (τ : α → Ty) (x t : Cat α) :
    (x.backwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

/-! ### Derivation interpretation -/

variable (T) in
/-- A semantic lexicon gives a word an optional meaning at each category, of that category's
type under the atom typing `τ`. Type-raised and coordinating entries carry the meanings of
type-raising and coordination. -/
def SemLexicon (τ : α → Ty) (E W : Type) :=
  T → (c : Cat α) → Option (Ty.Domain E W (c.toTy τ))

/-- `composeUnder τ β f g` composes `f` with `g` beneath the arguments `β`, Curry's combinator
`Bⁿ` for `n` the length of `β`: it takes the arguments of `g`, outermost first, and applies `f`
to the result. -/
def composeUnder (τ : α → Ty) {E W : Type} : (β : List (Cat.Arg α)) → {x y : Cat α} →
    Ty.Domain E W (y.toTy τ ⇒ x.toTy τ) → Ty.Domain E W ((y.pushArgs β).toTy τ) →
      Ty.Domain E W ((x.pushArgs β).toTy τ)
  | [], _, _, f, g => f g
  | ⟨.right, m, z⟩ :: β, x, y, f, g =>
      composeUnder τ β (x := .rslash x m z) (y := .rslash y m z) (f ∘ ·) g
  | ⟨.left, m, z⟩ :: β, x, y, f, g =>
      composeUnder τ β (x := .lslash x m z) (y := .lslash y m z) (f ∘ ·) g

/-- `r.sem τ` is the meaning of the rule `r` as an operation on its daughters' meanings, the
primary composed with the secondary beneath the arguments the rule passes on. -/
def Rule.sem (τ : α → Ty) {E W : Type} {R : RuleSystem α} : {l r c : Cat α} → Rule R l r c →
    Ty.Domain E W (l.toTy τ) → Ty.Domain E W (r.toTy τ) → Ty.Domain E W (c.toTy τ)
  | _, _, _, .forward β _, f, g => composeUnder τ β f g
  | _, _, _, .backward β _, g, f => composeUnder τ β f g

/-- `d.interp lex` is the meaning of the derivation `d`. A leaf takes its meaning from `lex`
and a rule node combines its daughters' meanings by `Rule.sem`, so the result is `none` only
when a word is missing from the lexicon. -/
def Derivation.interp {R : RuleSystem α} {τ : α → Ty} {E W : Type} (lex : SemLexicon T τ E W) :
    {c : Cat α} → Derivation T R c → Option (Ty.Domain E W (c.toTy τ))
  | _, .lex f c => lex f c
  | _, .node ru d₁ d₂ => do some (ru.sem τ (← d₁.interp lex) (← d₂.interp lex))

/-! ### Spurious ambiguity

Composition is associative, so left- and right-branching derivations of the same
composition-application chain receive the same interpretation, whatever the lexicon. This is
the local source of CCG's spurious ambiguity ([steedman-2000]). A chart parser may keep one
derivation per equivalence class, since reassociating `fcomp`/`fapp` (or `bcomp`/`bapp`)
nodes cannot change what a constituent means, and the matching-entry tests of
[karttunen-1989] and [pareschi-steedman-1987] exploit exactly this invariance. -/

section SpuriousAmbiguity

variable {R : RuleSystem α} {τ : α → Ty} {E W : Type} (lex : SemLexicon T τ E W)

/-- Reassociating a forward-composition chain preserves its interpretation, since composition
is associative. -/
theorem Derivation.interp_fcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (d₁ : Derivation T R (.rslash x m y)) (d₂ : Derivation T R (.rslash y n z))
    (d₃ : Derivation T R (.rslash z p w)) (h₁ : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩])
    (h₂ : R x ⟨.right, n, z⟩ [⟨.right, p, w⟩]) (h₃ : R y ⟨.right, n, z⟩ [⟨.right, p, w⟩])
    (h₄ : R x ⟨.right, m, y⟩ [⟨.right, p, w⟩]) :
    (Derivation.fcomp (.fcomp d₁ d₂ h₁) d₃ h₂).interp lex
      = (Derivation.fcomp d₁ (.fcomp d₂ d₃ h₃) h₄).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

/-- Composing and then applying has the interpretation of applying twice, since
`(f ∘ g) x = f (g x)`. -/
theorem Derivation.interp_fapp_fcomp {x y z : Cat α} {m n : Modality}
    (d₁ : Derivation T R (.rslash x m y)) (d₂ : Derivation T R (.rslash y n z))
    (d₃ : Derivation T R z) (h₁ : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩])
    (h₂ : R x ⟨.right, n, z⟩ []) (h₃ : R y ⟨.right, n, z⟩ []) (h₄ : R x ⟨.right, m, y⟩ []) :
    (Derivation.fapp (.fcomp d₁ d₂ h₁) d₃ h₂).interp lex
      = (Derivation.fapp d₁ (.fapp d₂ d₃ h₃) h₄).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

theorem Derivation.interp_bcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (d₁ : Derivation T R (.lslash y p z)) (d₂ : Derivation T R (.lslash x n y))
    (d₃ : Derivation T R (.lslash w m x)) (h₁ : R x ⟨.left, n, y⟩ [⟨.left, p, z⟩])
    (h₂ : R w ⟨.left, m, x⟩ [⟨.left, p, z⟩]) (h₃ : R w ⟨.left, m, x⟩ [⟨.left, n, y⟩])
    (h₄ : R w ⟨.left, n, y⟩ [⟨.left, p, z⟩]) :
    (Derivation.bcomp (.bcomp d₁ d₂ h₁) d₃ h₂).interp lex
      = (Derivation.bcomp d₁ (.bcomp d₂ d₃ h₃) h₄).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

theorem Derivation.interp_bapp_bcomp {x y w : Cat α} {m n : Modality}
    (d₁ : Derivation T R y) (d₂ : Derivation T R (.lslash x n y))
    (d₃ : Derivation T R (.lslash w m x)) (h₁ : R x ⟨.left, n, y⟩ [])
    (h₂ : R w ⟨.left, m, x⟩ []) (h₃ : R w ⟨.left, m, x⟩ [⟨.left, n, y⟩])
    (h₄ : R w ⟨.left, n, y⟩ []) :
    (Derivation.bapp (.bapp d₁ d₂ h₁) d₃ h₂).interp lex
      = (Derivation.bapp d₁ (.bcomp d₂ d₃ h₃) h₄).interp lex := by
  simp only [Derivation.interp]
  rcases d₁.interp lex with _ | m₁ <;> rcases d₂.interp lex with _ | m₂ <;>
    rcases d₃.interp lex with _ | m₃ <;> rfl

end SpuriousAmbiguity

end CCG
