module

public import Mathlib.Logic.Function.Basic

/-!
# Type-driven grammars and their simulations

A type-driven grammar says how the meanings of constituents combine, knowing only their types: it
has binary rules, the modes of combination, and unary rules, the type shifts. A derivation is a
tree of rules over typed leaves, and an interpretation gives each rule an operation on the domains
of its types, so that a derivation has a value. One grammar simulates another when each rule of the
second is a derived operation of the first, and then [whatever the second derives, the first
derives with the same value](##Composition.Grammar.Simulates.exists_deriv): the comparison of what
two compositional systems can express.

## Main definitions

* `Composition.Grammar`: the unary and binary rules over a type of semantic types.
* `Composition.Grammar.Deriv`: the derivations over typed leaves, the free algebra of the rules.
* `Composition.Grammar.Interpretation`: an operation for each rule, over a family of domains.
* `Composition.Grammar.Hom`: a translation of types and of rules into derived operations.
* `Composition.Grammar.Simulates`: over one family of domains, every rule of one grammar is a
  derived operation of another.

## Implementation notes

A grammar is a many-sorted signature with operations of arity one and two, a derivation a term
over it, and an interpretation an algebra, as `FirstOrder.Language`, its terms and its structures
are for one sort. The domains are a parameter of an interpretation, as the carrier is of a
structure, so that two grammars are compared over the same domains without transport. A derived
operation is a derivation whose leaves are holes, `One` or `Two`; it may use a hole more than once
or not at all.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

namespace Composition

universe u v w

/-- A type-driven grammar over semantic types `T`: its type shifts and its modes of combination,
each typed by what it takes and what it yields. -/
structure Grammar (T : Type u) where
  /-- The unary rules from one type to another. -/
  Unary : T → T → Type v
  /-- The binary rules combining a left and a right daughter into a mother. -/
  Binary : T → T → T → Type v

namespace Grammar

variable {T : Type u} {T' : Type u} {G : Grammar.{u, v} T} {G' : Grammar.{u, v} T'}
  {G'' : Grammar.{u, v} T} {W W' : T → Type w} {D : T → Type w} {D' : T' → Type w}

/-- A derivation of a type from leaves of the types `W` supplies. -/
inductive Deriv (G : Grammar.{u, v} T) (W : T → Type w) : T → Type (max u v w)
  /-- A leaf. -/
  | leaf {a : T} (x : W a) : Deriv G W a
  /-- A unary rule applied to a derivation. -/
  | unary {a b : T} (s : G.Unary a b) (d : Deriv G W a) : Deriv G W b
  /-- A binary rule applied to two derivations. -/
  | binary {a b c : T} (m : G.Binary a b c) (d₁ : Deriv G W a) (d₂ : Deriv G W b) : Deriv G W c

namespace Deriv

/-- Substitution of derivations for the leaves. -/
def bind {a : T} : Deriv G W a → (∀ {b : T}, W b → Deriv G W' b) → Deriv G W' a
  | leaf x, σ => σ x
  | unary s d, σ => unary s (d.bind σ)
  | binary m d₁ d₂, σ => binary m (d₁.bind σ) (d₂.bind σ)

@[simp] theorem bind_leaf {a : T} (d : Deriv G W a) : (d.bind fun x ↦ leaf x) = d := by
  induction d with
  | leaf x => rfl
  | unary s d ih => simp [bind, ih]
  | binary m d₁ d₂ ih₁ ih₂ => simp [bind, ih₁, ih₂]

end Deriv

/-- An interpretation of a grammar over the domains `D`: an operation for each rule. -/
structure Interpretation (G : Grammar.{u, v} T) (D : T → Type w) where
  /-- The operation of a unary rule. -/
  unary {a b : T} : G.Unary a b → D a → D b
  /-- The operation of a binary rule. -/
  binary {a b c : T} : G.Binary a b c → D a → D b → D c

namespace Deriv

/-- The value of a derivation, given the values of its leaves. -/
def eval (I : Interpretation G D) (ρ : ∀ {a : T}, W a → D a) {a : T} : Deriv G W a → D a
  | leaf x => ρ x
  | unary s d => I.unary s (d.eval I ρ)
  | binary m d₁ d₂ => I.binary m (d₁.eval I ρ) (d₂.eval I ρ)

theorem eval_bind (I : Interpretation G D) (ρ : ∀ {a : T}, W' a → D a) {a : T}
    (d : Deriv G W a) (σ : ∀ {b : T}, W b → Deriv G W' b) :
    (d.bind σ).eval I ρ = d.eval I fun x ↦ (σ x).eval I ρ := by
  induction d with
  | leaf x => rfl
  | unary s d ih => simp [bind, eval, ih]
  | binary m d₁ d₂ ih₁ ih₂ => simp [bind, eval, ih₁, ih₂]

end Deriv

/-- One hole, of type `a`. -/
inductive One (a : T) : T → Type w
  /-- The hole. -/
  | here : One a a

/-- Two holes, of types `a` and `b`. -/
inductive Two (a b : T) : T → Type w
  /-- The left hole. -/
  | left : Two a b a
  /-- The right hole. -/
  | right : Two a b b

/-- The values of one hole. -/
def One.val {a : T} (x : D a) : ∀ {b : T}, One.{u, w} a b → D b
  | _, .here => x

/-- The values of two holes. -/
def Two.val {a b : T} (x : D a) (y : D b) : ∀ {c : T}, Two.{u, w} a b c → D c
  | _, .left => x
  | _, .right => y

/-- A translation of one grammar into another: a map of types, and for each rule a derived
operation of the other grammar at the images of its types. -/
structure Hom (G : Grammar.{u, v} T) (G' : Grammar.{u, v} T') where
  /-- The translation of types. -/
  ty : T → T'
  /-- The derived operation a unary rule translates to. -/
  unary {a b : T} : G.Unary a b → Deriv G' (One.{u, w} (ty a)) (ty b)
  /-- The derived operation a binary rule translates to. -/
  binary {a b c : T} : G.Binary a b c → Deriv G' (Two.{u, w} (ty a) (ty b)) (ty c)

namespace Hom

/-- A translation carries derivations to derivations, given the translations of the leaves. -/
def onDeriv (F : Hom.{u, v, w} G G') {W' : T' → Type w}
    (ι : ∀ {a : T}, W a → Deriv G' W' (F.ty a)) {a : T} : Deriv G W a → Deriv G' W' (F.ty a)
  | .leaf x => ι x
  | .unary s d => (F.unary s).bind fun | .here => F.onDeriv ι d
  | .binary m d₁ d₂ => (F.binary m).bind fun
    | .left => F.onDeriv ι d₁
    | .right => F.onDeriv ι d₂

end Hom

/-- The interpretation a translation induces on the translated grammar. -/
def Interpretation.comap (F : Hom.{u, v, w} G G') (I : Interpretation G' D') :
    Interpretation G (D' ∘ F.ty) where
  unary s x := (F.unary s).eval I (One.val (D := D') x)
  binary m x y := (F.binary m).eval I (Two.val (D := D') x y)

/-- A translation preserves values. -/
theorem Hom.eval_onDeriv (F : Hom.{u, v, w} G G') (I : Interpretation G' D') {W' : T' → Type w}
    (ι : ∀ {a : T}, W a → Deriv G' W' (F.ty a)) (ρ : ∀ {a : T'}, W' a → D' a) {a : T}
    (d : Deriv G W a) :
    (F.onDeriv ι d).eval I ρ = d.eval (I.comap F) fun x ↦ (ι x).eval I ρ := by
  induction d with
  | leaf x => rfl
  | unary s d ih =>
    simp only [onDeriv, Deriv.eval_bind, Deriv.eval, Interpretation.comap]
    congr 1; funext b h; cases h; exact ih
  | binary m d₁ d₂ ih₁ ih₂ =>
    simp only [onDeriv, Deriv.eval_bind, Deriv.eval, Interpretation.comap]
    congr 1; funext b h; cases h
    · exact ih₁
    · exact ih₂

/-- Over one family of domains, `I'` simulates `I` when every rule of `I`'s grammar is a derived
operation of `I'`'s with the same meaning. -/
structure Simulates (I' : Interpretation G'' D) (I : Interpretation G D) : Prop where
  /-- Each unary rule is a derived operation. -/
  unary {a b : T} (s : G.Unary a b) :
    ∃ d : Deriv G'' (One.{u, w} a) b, ∀ x, d.eval I' (One.val x) = I.unary s x
  /-- Each binary rule is a derived operation. -/
  binary {a b c : T} (m : G.Binary a b c) :
    ∃ d : Deriv G'' (Two.{u, w} a b) c, ∀ x y, d.eval I' (Two.val x y) = I.binary m x y

namespace Simulates

variable {I : Interpretation G D} {I' : Interpretation G'' D}

/-- An interpretation simulates itself. -/
protected theorem refl (I : Interpretation G D) : Simulates I I where
  unary s := ⟨.unary s (.leaf .here), fun _ ↦ rfl⟩
  binary m := ⟨.binary m (.leaf .left) (.leaf .right), fun _ _ ↦ rfl⟩

/-- Whatever the simulated grammar derives, the simulating grammar derives with the same value,
whatever the values of the leaves. -/
theorem exists_deriv (h : Simulates I' I) {a : T} (d : Deriv G W a) :
    ∃ d' : Deriv G'' W a, ∀ ρ : ∀ {a : T}, W a → D a, d'.eval I' ρ = d.eval I ρ := by
  induction d with
  | leaf x => exact ⟨.leaf x, fun _ ↦ rfl⟩
  | unary s d ih =>
    obtain ⟨d', hd'⟩ := ih
    obtain ⟨u, hu⟩ := h.unary s
    refine ⟨u.bind fun | .here => d', fun ρ ↦ ?_⟩
    rw [Deriv.eval_bind, Deriv.eval, ← hd' ρ, ← hu]
    congr 1; funext b k; cases k; rfl
  | binary m d₁ d₂ ih₁ ih₂ =>
    obtain ⟨d₁', h₁⟩ := ih₁
    obtain ⟨d₂', h₂⟩ := ih₂
    obtain ⟨u, hu⟩ := h.binary m
    refine ⟨u.bind fun | .left => d₁' | .right => d₂', fun ρ ↦ ?_⟩
    rw [Deriv.eval_bind, Deriv.eval, ← h₁ ρ, ← h₂ ρ, ← hu]
    congr 1; funext b k; cases k <;> rfl

/-- Simulation is transitive. -/
protected theorem trans {G₃ : Grammar.{u, v} T} {I'' : Interpretation G₃ D}
    (h' : Simulates I'' I') (h : Simulates I' I) : Simulates I'' I where
  unary s := by
    obtain ⟨d, hd⟩ := h.unary s
    obtain ⟨d', hd'⟩ := h'.exists_deriv d
    exact ⟨d', fun x ↦ (hd' _).trans (hd x)⟩
  binary m := by
    obtain ⟨d, hd⟩ := h.binary m
    obtain ⟨d', hd'⟩ := h'.exists_deriv d
    exact ⟨d', fun x y ↦ (hd' _).trans (hd x y)⟩

end Simulates

end Grammar

end Composition
