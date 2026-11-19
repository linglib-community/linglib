module

public import Linglib.Syntax.CCG.Semantics

/-!
# Eisner (1996): Efficient Normal-Form Parsing for Combinatory Categorial Grammar

Composition makes a combinatory categorial grammar give one string many derivations with one
meaning, its *spurious ambiguity*. [eisner-1996] picks one derivation from each such class by a
condition on the shape of the tree alone. A derivation is in *normal form* when the output of
forward composition is never the left input of a forward rule, and the output of backward
composition never the right input of a backward rule. Two derivations are *equivalent* when
they have the same meaning whatever the words mean. In the grammar with every instance of the
rule schema, each derivation is equivalent to [one in normal
form](##Eisner1996.exists_isNormal_equivalent), and [two equivalent derivations in normal form
are the same](##Eisner1996.eq_of_isNormal_of_equivalent), so a parser that builds only normal
forms finds each reading exactly once.

## Implementation notes

The paper takes the meanings of the leaves of a tree to be independent. Here a meaning is given
to each leaf by its category and its word, so the uniqueness theorem is stated for derivations
whose leaves are distinct.

## TODO

* `exists_isNormal_equivalent`: by induction on the derivation, as the paper sketches. Where
  the normal form of the left daughter of a forward rule is a forward composition of `β₁` and
  `β₂`, rotate to `β₁` combined with the normal form of `β₂` and the right daughter. The
  rotated rules have the degree of the two original rules together, less one, and the meaning
  is unchanged by `composeUnder_append`. What remains is to build the rotated tree, whose
  categories agree with the original only up to `Cat.pushArgs_append`, with its mirror image for
  backward rules, and to show that the recursion ends.
* `eq_of_isNormal_of_equivalent`: the paper sketches a proof that two distinct normal-form trees
  differ in which leaf takes immediate scope over which, and gives the full proof in the longer
  version of the paper, which has not been read.

## References

* [eisner-1996]
-/

@[expose] public section

namespace Eisner1996

open CCG Interpreter

variable {α : Type*} {W : Cat α → Type*} {R : RuleSystem α} {c : Cat α}

/-! ### Normal form -/

/-- The rule is a forward composition, of degree at least one. -/
def IsForwardComp {l r c : Cat α} : Rule R l r c → Prop
  | .forward β _ => β ≠ []
  | .backward _ _ => False

/-- The rule is a backward composition, of degree at least one. -/
def IsBackwardComp {l r c : Cat α} : Rule R l r c → Prop
  | .forward _ _ => False
  | .backward β _ => β ≠ []

/-- The rule is forward, an application or a composition. -/
def IsForward {l r c : Cat α} : Rule R l r c → Prop
  | .forward _ _ => True
  | .backward _ _ => False

instance {l r c : Cat α} : ∀ ru : Rule R l r c, Decidable (IsForwardComp ru)
  | .forward β _ => inferInstanceAs (Decidable (β ≠ []))
  | .backward _ _ => isFalse id

instance {l r c : Cat α} : ∀ ru : Rule R l r c, Decidable (IsBackwardComp ru)
  | .forward _ _ => isFalse id
  | .backward β _ => inferInstanceAs (Decidable (β ≠ []))

instance {l r c : Cat α} : ∀ ru : Rule R l r c, Decidable (IsForward ru)
  | .forward _ _ => isTrue trivial
  | .backward _ _ => isFalse id

/-- The derivation is the output of a rule satisfying `p`. -/
def RootIs (p : ∀ {l r c : Cat α}, Rule R l r c → Prop) {c : Cat α} : Derivation W R c → Prop
  | .lex _ _ => False
  | .node ru _ _ => p ru

instance (p : ∀ {l r c : Cat α}, Rule R l r c → Prop)
    [hp : ∀ {l r c : Cat α} (ru : Rule R l r c), Decidable (p ru)] {c : Cat α} :
    ∀ d : Derivation W R c, Decidable (RootIs p d)
  | .lex _ _ => isFalse id
  | .node ru _ _ => hp ru

/-- A derivation is in normal form when no output of forward composition is the left input of
a forward rule and no output of backward composition is the right input of a backward rule (7). -/
def IsNormal {c : Cat α} : Derivation W R c → Prop
  | .lex _ _ => True
  | .node ru d₁ d₂ => IsNormal d₁ ∧ IsNormal d₂ ∧
      (IsForward ru → ¬ RootIs IsForwardComp d₁) ∧ (¬ IsForward ru → ¬ RootIs IsBackwardComp d₂)

instance IsNormal.decidable {c : Cat α} : ∀ d : Derivation W R c, Decidable (IsNormal d)
  | .lex _ _ => isTrue trivial
  | .node _ d₁ d₂ =>
      @instDecidableAnd _ _ (decidable d₁) (@instDecidableAnd _ _ (decidable d₂) inferInstance)

/-! ### Equivalence -/

/-- The leaves of a derivation with their categories, from left to right. -/
def leaves {c : Cat α} : Derivation W R c → List (Σ c, W c)
  | .lex c w => [⟨c, w⟩]
  | .node _ d₁ d₂ => leaves d₁ ++ leaves d₂

/-- Two derivations are equivalent when they have the same meaning whatever their leaves mean,
at every typing of the atoms and over every domain (§4.1). -/
def Equivalent {c : Cat α} (d d' : Derivation W R c) : Prop :=
  ∀ {B : Type} (τ : α → Ty B) (D : B → Type) (ρ : ∀ c, W c → (c.toTy τ).Dom D),
    d.realize τ ρ = d'.realize τ ρ

/-! ### *John likes Mary* -/

/-- The atoms of (8). -/
inductive Atom
  | S | NP
  deriving DecidableEq

/-- The rule system of pure CCG, with every instance of the schema (§4). -/
def pure : RuleSystem α := fun _ _ _ ↦ True

instance (x : Cat α) (a : Cat.Arg α) (β : List (Cat.Arg α)) : Decidable (pure x a β) :=
  inferInstanceAs (Decidable True)

/-- The sentence category. -/
abbrev S : Cat Atom := .atom .S

/-- The noun-phrase category. -/
abbrev NP : Cat Atom := .atom .NP

/-- (8a): the subject applies to the verb phrase. -/
def likesApplied : Derivation (fun _ ↦ String) (pure (α := Atom)) S :=
  .fapp (.lex (S / (S \ NP)) "John") (.fapp (.lex ((S \ NP) / NP) "likes") (.lex NP "Mary"))

/-- (8b): the subject composes with the verb, and the result applies to the object. -/
def likesComposed : Derivation (fun _ ↦ String) (pure (α := Atom)) S :=
  .fapp (.fcomp (.lex (S / (S \ NP)) "John") (.lex ((S \ NP) / NP) "likes")) (.lex NP "Mary")

/-- Of the two derivations of *John likes Mary* in (8), which have the same leaves and the same
meaning, the one that applies is in normal form and the one that composes is not. -/
theorem likes_normal :
    IsNormal likesApplied ∧ ¬ IsNormal likesComposed ∧
      leaves likesApplied = leaves likesComposed ∧ Equivalent likesApplied likesComposed :=
  ⟨by decide, by decide, rfl, fun _ _ _ ↦ rfl⟩

/-! ### The rotation

The meaning of a forward composition that is the left input of a forward rule is the meaning of
the tree rotated to the right, in which the right input of the composition combines first with
the right input of the rule. The two trees have the same category only up to
`Cat.pushArgs_append`, and `castDom` carries a meaning along such an equation. -/

/-- A meaning of one category as a meaning of an equal category. -/
def castDom {B : Type} {D : B → Type} (τ : α → Ty B) {c c' : Cat α} (h : c = c')
    (v : (c.toTy τ).Dom D) : (c'.toTy τ).Dom D :=
  h ▸ v

/-- Composing `f` with `g` beneath `β` and a last rightward argument `z`, and the result with
`h` beneath `γ`, is composing `f` beneath `β` and `γ` with the composition of `g` and `h`
beneath `γ`. -/
theorem composeUnder_append {B : Type} {D : B → Type} (τ : α → Ty B) (m : Modality) (z : Cat α)
    (γ : List (Cat.Arg α)) :
    ∀ (β : List (Cat.Arg α)) (x y : Cat α) (f : (y.toTy τ ⇒ x.toTy τ).Dom D)
      (g : ((y.pushArgs (β ++ [⟨.right, m, z⟩])).toTy τ).Dom D)
      (h : ((z.pushArgs γ).toTy τ).Dom D),
      composeUnder τ γ (x := x.pushArgs β) (y := z)
          (castDom τ (Cat.pushArgs_append x β [⟨.right, m, z⟩]) (composeUnder τ _ f g)) h =
        castDom τ (Cat.pushArgs_append x β γ)
          (composeUnder τ (β ++ γ) f (castDom τ (Cat.pushArgs_append y β γ).symm
            (composeUnder τ γ (x := y.pushArgs β) (y := z)
              (castDom τ (Cat.pushArgs_append y β [⟨.right, m, z⟩]) g) h)))
  | [], _, _, f, g, h => composeUnder_comp τ γ f g h
  | b :: β, x, y, f, g, h => composeUnder_append τ m z γ β (x.push b) (y.push b) (f ∘ ·) g h

/-! ### Existence and uniqueness -/

/-- Theorem 1: in pure CCG every derivation is equivalent to one in normal form over the same
leaves. -/
theorem exists_isNormal_equivalent (d : Derivation W (pure (α := α)) c) :
    ∃ d' : Derivation W (pure (α := α)) c,
      IsNormal d' ∧ leaves d' = leaves d ∧ Equivalent d d' := by
  sorry

/-- Theorem 2: two equivalent derivations in normal form over the same distinct leaves are the
same derivation. -/
theorem eq_of_isNormal_of_equivalent {d d' : Derivation W (pure (α := α)) c} (h : IsNormal d)
    (h' : IsNormal d') (hl : leaves d = leaves d') (hn : (leaves d).Nodup)
    (he : Equivalent d d') : d = d' := by
  sorry

end Eisner1996
