module

public import Linglib.Syntax.CCG.Rule

/-!
# CCG derivations

A derivation is a binary tree. Each leaf is a lexical item with its category, and each node
combines its two daughters by a rule. `Derivation W R c` is the type of derivations of the
category `c` by the rules of `R`, in which a leaf of category `c` is drawn from `W c`. When the
leaves are words, the *yield* of a derivation is the string it spells out, and `LexIn` says that
its leaves are entries of a lexicon. A derivation is *harmonic* when all its rules are.

Type-raising and coordination are lexical: a raised category enters as a leaf, and a
conjunction is a word of category `(X \⋆ X) /⋆ X`, whose `⋆` slashes allow only application.

## References

* [steedman-2019]
* [baldridge-2002]
-/

@[expose] public section

namespace CCG

variable {T α : Type*} {R : RuleSystem α}

/-- A CCG derivation of category `c` is a lexical leaf or a binary `Rule` node over two
derivations, which states the binarity of the Combinatory Projection Principle once. The leaves
of category `c` are drawn from `W c`. A value of `Derivation W R c` is a well-formed derivation,
so "derives `c`" is typechecking. -/
inductive Derivation (W : Cat α → Type*) (R : RuleSystem α) : Cat α → Type _ where
  /-- A lexical leaf of category `c`. -/
  | lex (c : Cat α) (w : W c) : Derivation W R c
  /-- A binary rule application. -/
  | node {l r c : Cat α} :
      Rule R l r c → Derivation W R l → Derivation W R r → Derivation W R c

namespace Derivation

variable {W W' : Cat α → Type*} {x y z : Cat α} {m n : Modality}

/-! The named rules of degree at most 1. Each discharges its gate by `decide` when the
categories are closed. -/

/-- Forward application `>`, `X/Y Y ⇒ X`. -/
abbrev fapp (d₁ : Derivation W R (.slash .right x m y)) (d₂ : Derivation W R y)
    (h : R x ⟨.right, m, y⟩ [] := by decide) : Derivation W R x :=
  .node (r := y) (c := x) (.forward [] h) d₁ d₂

/-- Backward application `<`, `Y X\Y ⇒ X`. -/
abbrev bapp (d₁ : Derivation W R y) (d₂ : Derivation W R (.slash .left x m y))
    (h : R x ⟨.left, m, y⟩ [] := by decide) : Derivation W R x :=
  .node (l := y) (c := x) (.backward [] h) d₁ d₂

/-- Forward harmonic composition `>B`, `X/Y Y/Z ⇒ X/Z`. -/
abbrev fcomp (d₁ : Derivation W R (.slash .right x m y)) (d₂ : Derivation W R (.slash .right y n z))
    (h : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩] := by decide) : Derivation W R (.slash .right x n z) :=
  .node (r := .slash .right y n z) (c := .slash .right x n z) (.forward [⟨.right, n, z⟩] h) d₁ d₂

/-- Backward harmonic composition `<B`, `Y\Z X\Y ⇒ X\Z`. -/
abbrev bcomp (d₁ : Derivation W R (.slash .left y n z)) (d₂ : Derivation W R (.slash .left x m y))
    (h : R x ⟨.left, m, y⟩ [⟨.left, n, z⟩] := by decide) : Derivation W R (.slash .left x n z) :=
  .node (l := .slash .left y n z) (c := .slash .left x n z) (.backward [⟨.left, n, z⟩] h) d₁ d₂

/-- Forward crossing composition `>B×`, `X/Y Y\Z ⇒ X\Z`. -/
abbrev fcompx (d₁ : Derivation W R (.slash .right x m y)) (d₂ : Derivation W R (.slash .left y n z))
    (h : R x ⟨.right, m, y⟩ [⟨.left, n, z⟩] := by decide) : Derivation W R (.slash .left x n z) :=
  .node (r := .slash .left y n z) (c := .slash .left x n z) (.forward [⟨.left, n, z⟩] h) d₁ d₂

/-- Backward crossing composition `<B×`, `Y/Z X\Y ⇒ X/Z`. -/
abbrev bcompx (d₁ : Derivation W R (.slash .right y n z)) (d₂ : Derivation W R (.slash .left x m y))
    (h : R x ⟨.left, m, y⟩ [⟨.right, n, z⟩] := by decide) : Derivation W R (.slash .right x n z) :=
  .node (l := .slash .right y n z) (c := .slash .right x n z) (.backward [⟨.right, n, z⟩] h) d₁ d₂

/-- The derivation with its leaves relabelled by `f`. -/
def map (f : ∀ c, W c → W' c) {c : Cat α} : Derivation W R c → Derivation W' R c
  | .lex c w => .lex c (f c w)
  | .node ru d₁ d₂ => .node ru (d₁.map f) (d₂.map f)

@[simp] theorem map_lex (f : ∀ c, W c → W' c) (c : Cat α) (w : W c) :
    (lex (R := R) c w).map f = .lex c (f c w) := rfl

@[simp] theorem map_node (f : ∀ c, W c → W' c) {l r c : Cat α} (ru : Rule R l r c)
    (d₁ : Derivation W R l) (d₂ : Derivation W R r) :
    (node ru d₁ d₂).map f = .node ru (d₁.map f) (d₂.map f) := rfl

/-- The number of combinatory rule applications in a derivation. -/
def opCount {c : Cat α} : Derivation W R c → Nat
  | .lex _ _ => 0
  | .node _ d₁ d₂ => 1 + d₁.opCount + d₂.opCount

/-- The derivation contains a composition node (of any degree or direction). -/
def HasComp {c : Cat α} : Derivation W R c → Prop
  | .lex _ _ => False
  | .node ru d₁ d₂ => ru.IsComp ∨ d₁.HasComp ∨ d₂.HasComp

instance HasComp.decidable {c : Cat α} : ∀ d : Derivation W R c, Decidable d.HasComp
  | .lex _ _ => isFalse fun h => h
  | .node _ d₁ d₂ =>
      @instDecidableOr _ _ inferInstance
        (@instDecidableOr _ _ (decidable d₁) (decidable d₂))

/-! ### Derivations over tokens -/

/-- The token string a derivation spells out, its leaves from left to right. Rule nodes
concatenate their daughters, so the yield is independent of the derivation's combinatory
structure. -/
def yield {c : Cat α} : Derivation (fun _ ↦ T) R c → List T
  | .lex _ t => [t]
  | .node _ d₁ d₂ => d₁.yield ++ d₂.yield

theorem yield_ne_nil {c : Cat α} (d : Derivation (fun _ ↦ T) R c) : d.yield ≠ [] := by
  induction d with
  | lex => simp [yield]
  | node _ d₁ d₂ ih₁ _ => simp [yield, ih₁]

theorem eq_lex_of_yield_eq_singleton {c : Cat α} {d : Derivation (fun _ ↦ T) R c} {t : T}
    (h : d.yield = [t]) : d = .lex c t := by
  cases d with
  | lex => simp_all [yield]
  | node _ d₁ d₂ =>
    simp only [yield, List.append_eq_singleton_iff] at h
    exact h.elim (fun h ↦ absurd h.1 d₁.yield_ne_nil) fun h ↦ absurd h.2 d₂.yield_ne_nil

/-- Every lexical leaf of the derivation is an entry of the lexicon `L`. -/
def LexIn (L : List (T × Cat α)) {c : Cat α} : Derivation (fun _ ↦ T) R c → Prop
  | .lex c t => (t, c) ∈ L
  | .node _ d₁ d₂ => d₁.LexIn L ∧ d₂.LexIn L

instance LexIn.decidable [DecidableEq T] [DecidableEq α] (L : List (T × Cat α)) {c : Cat α} :
    ∀ d : Derivation (fun _ ↦ T) R c, Decidable (d.LexIn L)
  | .lex c t => inferInstanceAs (Decidable ((t, c) ∈ L))
  | .node _ d₁ d₂ =>
      @instDecidableAnd _ _ (decidable L d₁) (decidable L d₂)

/-! ### Leaf categories and harmonic derivations -/

/-- The categories of the leaves, from left to right. -/
def cats {W : Cat α → Type*} {c : Cat α} : Derivation W R c → List (Cat α)
  | .lex c _ => [c]
  | .node _ d₁ d₂ => d₁.cats ++ d₂.cats

@[simp] theorem cats_map {W W' : Cat α → Type*} (f : ∀ c, W c → W' c) {c : Cat α}
    (d : Derivation W R c) : (d.map f).cats = d.cats := by
  induction d with
  | lex => rfl
  | node _ _ _ ih₁ ih₂ => simp [map, cats, ih₁, ih₂]

/-- Every rule of the derivation is harmonic. -/
def IsHarmonic {W : Cat α → Type*} {c : Cat α} : Derivation W R c → Prop
  | .lex _ _ => True
  | .node ru d₁ d₂ => ru.IsHarmonic ∧ d₁.IsHarmonic ∧ d₂.IsHarmonic

instance IsHarmonic.decidable {W : Cat α → Type*} {c : Cat α} :
    ∀ d : Derivation W R c, Decidable d.IsHarmonic
  | .lex _ _ => isTrue trivial
  | .node _ d₁ d₂ =>
      @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ (decidable d₁) (decidable d₂))

end Derivation

end CCG
