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
form](##Eisner1996.exists_isNormal_equivalent), so a parser that builds only normal forms loses
no reading. The paper also states that two equivalent derivations in normal form are the same,
so that such a parser finds each reading exactly once.

## TODO

* Uniqueness, the paper's second theorem, is not stated: two equivalent derivations in normal
  form over the same leaves are the same derivation. The paper takes the meanings of the leaves
  of a tree to be independent, and here a meaning is given to each leaf by its category and its
  word, so the statement needs the leaves to be distinct. The author's unpublished proof gives
  each leaf a constant of its own and each tree a λ-term in which only constants take
  arguments. Two distinct terms of this kind differ in some model. Two distinct trees over the
  same leaves differ either in the rule that joins two common subtrees or in the side to which
  a common subtree combines, and when both are in normal form some constant then has a
  different parent or child in the two terms. A model whose atoms denote such terms would stand
  in for the syntax of terms, and the comparison of parents and children is the long part.

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

/-- Composing `f` with `g` beneath `β` and a last argument `z`, and the result with `h` beneath
`γ`, is composing `f` beneath `β` and `γ` with the composition of `g` and `h` beneath `γ`. -/
theorem composeUnder_append {B : Type} {D : B → Type} (τ : α → Ty B) (s : Edge) (m : Modality)
    (z : Cat α) (γ : List (Cat.Arg α)) :
    ∀ (β : List (Cat.Arg α)) (x y : Cat α) (f : (y.toTy τ ⇒ x.toTy τ).Dom D)
      (g : ((y.pushArgs (β ++ [⟨s, m, z⟩])).toTy τ).Dom D)
      (h : ((z.pushArgs γ).toTy τ).Dom D),
      composeUnder τ γ (x := x.pushArgs β) (y := z)
          (castDom τ (Cat.pushArgs_append x β [⟨s, m, z⟩]) (composeUnder τ _ f g)) h =
        castDom τ (Cat.pushArgs_append x β γ)
          (composeUnder τ (β ++ γ) f (castDom τ (Cat.pushArgs_append y β γ).symm
            (composeUnder τ γ (x := y.pushArgs β) (y := z)
              (castDom τ (Cat.pushArgs_append y β [⟨s, m, z⟩]) g) h)))
  | [], _, _, f, g, h => composeUnder_comp τ γ f g h
  | b :: β, x, y, f, g, h => composeUnder_append τ s m z γ β (x.push b) (y.push b) (f ∘ ·) g h

/-! ### Existence -/

-- a derivation of one category is one of an equal category, with the same shape, leaves, meaning
private theorem exists_cast {c c' : Cat α} (h : c = c') (d : Derivation W R c) :
    ∃ d' : Derivation W R c', (IsNormal d' ↔ IsNormal d) ∧ leaves d' = leaves d ∧
      ∀ {B : Type} (τ : α → Ty B) (D : B → Type) (ρ : ∀ c, W c → (c.toTy τ).Dom D),
        d'.realize τ ρ = castDom τ h (d.realize τ ρ) := by
  subst h
  exact ⟨d, Iff.rfl, rfl, fun _ _ _ ↦ rfl⟩

/-- A forward rule over two derivations in normal form has a normal form. Where the left input
is a forward composition, its right daughter combines first with the right input, the rotation
of (13), and the same holds again of that combination. -/
private theorem exists_forward {c₁ : Cat α} (d₁ : Derivation W (pure (α := α)) c₁) :
    IsNormal d₁ → ∀ {x y : Cat α} {m : Modality} (hc : c₁ = .slash .right x m y)
      (γ : List (Cat.Arg α)) (d₂ : Derivation W (pure (α := α)) (y.pushArgs γ)), IsNormal d₂ →
      ∃ d' : Derivation W (pure (α := α)) (x.pushArgs γ), IsNormal d' ∧
        leaves d' = leaves d₁ ++ leaves d₂ ∧
        ∀ {B : Type} (τ : α → Ty B) (D : B → Type) (ρ : ∀ c, W c → (c.toTy τ).Dom D),
          d'.realize τ ρ =
            composeUnder τ γ (castDom τ hc (d₁.realize τ ρ)) (d₂.realize τ ρ) := by
  induction d₁ with
  | lex c w =>
    rintro - x y m rfl γ d₂ h₂
    exact ⟨.node (.forward γ trivial) (.lex _ w) d₂,
      ⟨trivial, h₂, fun _ ↦ id, fun h ↦ (h trivial).elim⟩, rfl, fun _ _ _ ↦ rfl⟩
  | node ru a b _ ihb =>
    intro h₁ x y m hc γ d₂ h₂
    by_cases hf : IsForwardComp ru
    · cases ru with
      | backward => exact hf.elim
      | forward β' _ =>
        obtain rfl | ⟨β, ⟨s, m', z⟩, rfl⟩ := β'.eq_nil_or_concat'
        · exact (hf rfl).elim
        have e := hc
        simp only [Cat.pushArgs_append, Cat.pushArgs_cons, Cat.pushArgs_nil, Cat.push_mk,
          Cat.slash.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        obtain ⟨e', he', hl', hs'⟩ := ihb h₁.2.1 (Cat.pushArgs_append _ β [_]) γ d₂ h₂
        obtain ⟨e'', hn'', hl'', hs''⟩ := exists_cast (Cat.pushArgs_append _ β γ).symm e'
        obtain ⟨d', hn, hl, hs⟩ := exists_cast (Cat.pushArgs_append _ β γ)
          (.node (.forward (β ++ γ) trivial) a e'')
        refine ⟨d', hn.2 ⟨h₁.1, hn''.2 he', fun _ ↦ h₁.2.2.1 trivial, fun h ↦ (h trivial).elim⟩,
          ?_, fun τ D ρ ↦ ?_⟩
        · rw [hl, leaves, hl'', hl', leaves, List.append_assoc]
        · rw [hs, Derivation.realize_node, hs'', hs']
          exact (composeUnder_append τ .right _ _ γ β _ _ _ _ _).symm
    · subst hc
      exact ⟨.node (.forward γ trivial) (.node ru a b) d₂,
        ⟨h₁, h₂, fun _ ↦ hf, fun h ↦ (h trivial).elim⟩, rfl, fun _ _ _ ↦ rfl⟩

/-- A backward rule over two derivations in normal form has a normal form, the mirror image of
`exists_forward`. -/
private theorem exists_backward {c₂ : Cat α} (d₂ : Derivation W (pure (α := α)) c₂) :
    IsNormal d₂ → ∀ {x y : Cat α} {m : Modality} (hc : c₂ = .slash .left x m y)
      (γ : List (Cat.Arg α)) (d₁ : Derivation W (pure (α := α)) (y.pushArgs γ)), IsNormal d₁ →
      ∃ d' : Derivation W (pure (α := α)) (x.pushArgs γ), IsNormal d' ∧
        leaves d' = leaves d₁ ++ leaves d₂ ∧
        ∀ {B : Type} (τ : α → Ty B) (D : B → Type) (ρ : ∀ c, W c → (c.toTy τ).Dom D),
          d'.realize τ ρ =
            composeUnder τ γ (castDom τ hc (d₂.realize τ ρ)) (d₁.realize τ ρ) := by
  induction d₂ with
  | lex c w =>
    rintro - x y m rfl γ d₁ h₁
    exact ⟨.node (.backward γ trivial) d₁ (.lex _ w),
      ⟨h₁, trivial, fun h ↦ h.elim, fun _ ↦ id⟩, rfl, fun _ _ _ ↦ rfl⟩
  | node ru b a ihb _ =>
    intro h₂ x y m hc γ d₁ h₁
    by_cases hf : IsBackwardComp ru
    · cases ru with
      | forward => exact hf.elim
      | backward β' _ =>
        obtain rfl | ⟨β, ⟨s, m', z⟩, rfl⟩ := β'.eq_nil_or_concat'
        · exact (hf rfl).elim
        have e := hc
        simp only [Cat.pushArgs_append, Cat.pushArgs_cons, Cat.pushArgs_nil, Cat.push_mk,
          Cat.slash.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        obtain ⟨e', he', hl', hs'⟩ := ihb h₂.1 (Cat.pushArgs_append _ β [_]) γ d₁ h₁
        obtain ⟨e'', hn'', hl'', hs''⟩ := exists_cast (Cat.pushArgs_append _ β γ).symm e'
        obtain ⟨d', hn, hl, hs⟩ := exists_cast (Cat.pushArgs_append _ β γ)
          (.node (.backward (β ++ γ) trivial) e'' a)
        refine ⟨d', hn.2 ⟨hn''.2 he', h₂.2.1, fun h ↦ h.elim, fun _ ↦ h₂.2.2.2 id⟩,
          ?_, fun τ D ρ ↦ ?_⟩
        · rw [hl, leaves, hl'', hl', leaves, List.append_assoc]
        · rw [hs, Derivation.realize_node, hs'', hs']
          exact (composeUnder_append τ .left _ _ γ β _ _ _ _ _).symm
    · subst hc
      exact ⟨.node (.backward γ trivial) d₁ (.node ru b a),
        ⟨h₁, h₂, fun h ↦ h.elim, fun _ ↦ hf⟩, rfl, fun _ _ _ ↦ rfl⟩

/-- Theorem 1: in pure CCG every derivation is equivalent to one in normal form over the same
leaves. -/
theorem exists_isNormal_equivalent (d : Derivation W (pure (α := α)) c) :
    ∃ d' : Derivation W (pure (α := α)) c,
      IsNormal d' ∧ leaves d' = leaves d ∧ Equivalent d d' := by
  induction d with
  | lex c w => exact ⟨.lex c w, trivial, rfl, fun _ _ _ ↦ rfl⟩
  | node ru d₁ d₂ ih₁ ih₂ =>
    obtain ⟨e₁, hn₁, hl₁, he₁⟩ := ih₁
    obtain ⟨e₂, hn₂, hl₂, he₂⟩ := ih₂
    cases ru with
    | forward γ _ =>
      obtain ⟨d', hn, hl, hs⟩ := exists_forward e₁ hn₁ rfl γ e₂ hn₂
      exact ⟨d', hn, by rw [hl, hl₁, hl₂]; rfl, fun τ D ρ ↦ by
        rw [hs, Derivation.realize_node, he₁ τ D ρ, he₂ τ D ρ]; rfl⟩
    | backward γ _ =>
      obtain ⟨d', hn, hl, hs⟩ := exists_backward e₂ hn₂ rfl γ e₁ hn₁
      exact ⟨d', hn, by rw [hl, hl₁, hl₂]; rfl, fun τ D ρ ↦ by
        rw [hs, Derivation.realize_node, he₁ τ D ρ, he₂ τ D ρ]; rfl⟩

end Eisner1996
