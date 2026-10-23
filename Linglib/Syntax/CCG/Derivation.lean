module

public import Linglib.Syntax.CCG.Cat

/-!
# CCG derivations

Steedman's Combinatory Projection Principle makes every syntactic combinatory rule binary,
linearly ordered and type-dependent, applying to string-adjacent categories. Every such rule is
an instance of one schema, forward composition `X/Y Yβ ⇒ Xβ` or its mirror `Yβ X\Y ⇒ Xβ`, whose
degree is the length of the argument sequence `β`, with application at degree 0. A CCG formalism
is a `RuleSystem`, which says which instances of the schema fire. The multimodal system of
Baldridge and Steedman (`RuleSystem.multimodal`) is the modern inventory: degree at most 2, a
secondary whose arguments all look one way, and a primary slash whose modality licenses
harmonic composition (`⋄`) when they look its way and crossing composition (`×`) when they look
the other way.

A `Derivation T R c` is a tree of lexical leaves, tokens of an alphabet `T`, and binary nodes
labelled by rules of `R`, indexed by its category, so a value of `Derivation T R c` is a
derivation of `c`. Type-raising and coordination are lexical, as in Steedman's morpholexical
treatment: raised categories enter as leaves, and a conjunction is an entry of category
`(X \⋆ X) /⋆ X` whose `star` slashes confine it to application. The substitution rules and the
morphemic slash are not modeled.

## Main definitions

* `CCG.RuleSystem`: which instances of the composition schema fire, with
  `RuleSystem.multimodal` the modern inventory.
* `CCG.Rule`: the instances of the schema a rule system permits.
* `CCG.Derivation`: derivations, with `yield` the token string, `opCount` the number of rule
  applications, `HasComp` whether composition occurs, and `LexIn` whether every leaf is drawn
  from a lexicon.

## Main statements

* `CCG.Derivation.count_eq_sum`: van Benthem's count invariant.

## References

* [steedman-2019]
* [baldridge-2002]
* [kuhlmann-koller-satta-2015]
* [van-benthem-1986]
-/

@[expose] public section

namespace CCG

variable {T α : Type*}

/-! ### Rule systems -/

/-- A rule system says which instances of the composition schema fire. `R x a β` permits the
primary `x a`, the category `x` with outermost argument `a`, to combine with a secondary
`a.cat β` into `x β`, by a forward rule when `a` looks right and a backward rule when it looks
left, and by application when `β` is empty. -/
abbrev RuleSystem (α : Type*) := Cat α → Cat.Arg α → List (Cat.Arg α) → Prop

/-- The multimodal rule system of [baldridge-2002] and [steedman-2019] admits composition of
degree at most 2 into a secondary whose arguments all look one way. The primary slash's
modality must license harmonic composition (`⋄`) when they look its way and crossing composition
(`×`) when they look the other way, and application fires at every modality. -/
def RuleSystem.multimodal : RuleSystem α := fun _ a β ↦
  β.length ≤ 2 ∧ β.Pairwise (·.side = ·.side) ∧
    ∀ b ∈ β, a.modality ≤ if b.side = a.side then .diamond else .cross

instance (x : Cat α) (a : Cat.Arg α) (β : List (Cat.Arg α)) :
    Decidable (RuleSystem.multimodal x a β) :=
  inferInstanceAs (Decidable (β.length ≤ 2 ∧ β.Pairwise (·.side = ·.side) ∧
    ∀ b ∈ β, a.modality ≤ if b.side = a.side then .diamond else .cross))

@[simp] theorem RuleSystem.multimodal_singleton {x : Cat α} {a b : Cat.Arg α} :
    multimodal x a [b] ↔ a.modality ≤ if b.side = a.side then .diamond else .cross := by
  simp [multimodal]

/-! ### Rules and derivations -/

/-- A `Rule R l r c` is an instance of the composition schema that the rule system `R` permits,
combining a left constituent of category `l` with a right constituent of category `r` to give
`c`. Its degree is the length of its argument sequence `β`. -/
inductive Rule (R : RuleSystem α) : Cat α → Cat α → Cat α → Type _ where
  /-- Forward composition `X/Y Yβ ⇒ Xβ` (`>Bⁿ`), forward application `>` when `β = []`. -/
  | forward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) (h : R x ⟨.right, m, y⟩ β) :
      Rule R (.rslash x m y) (y.pushArgs β) (x.pushArgs β)
  /-- Backward composition `Yβ X\Y ⇒ Xβ` (`<Bⁿ`), backward application `<` when `β = []`. -/
  | backward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) (h : R x ⟨.left, m, y⟩ β) :
      Rule R (y.pushArgs β) (.lslash x m y) (x.pushArgs β)

variable {R : RuleSystem α}

/-- The rule is a composition (of any degree or direction) rather than an application. -/
def Rule.IsComp {l r c : Cat α} : Rule R l r c → Prop
  | .forward β _ | .backward β _ => β ≠ []

instance {l r c : Cat α} : ∀ ru : Rule R l r c, Decidable ru.IsComp
  | .forward β _ | .backward β _ => inferInstanceAs (Decidable (β ≠ []))

/-- A CCG derivation of category `c` is a lexical leaf or a binary `Rule` node over two
derivations, which states the binarity of the Combinatory Projection Principle once. A value of
`Derivation T R c` is a well-formed derivation, so "derives `c`" is typechecking. -/
inductive Derivation (T : Type*) (R : RuleSystem α) : Cat α → Type _ where
  /-- A lexical leaf, a token at category `c`. -/
  | lex (t : T) (c : Cat α) : Derivation T R c
  /-- A binary rule application. -/
  | node {l r c : Cat α} :
      Rule R l r c → Derivation T R l → Derivation T R r → Derivation T R c

namespace Derivation

variable {x y z : Cat α} {m n : Modality}

/-! The named rules of degree at most 1. Each discharges its gate by `decide` when the
categories are closed. -/

/-- Forward application `>`, `X/Y Y ⇒ X`. -/
abbrev fapp (d₁ : Derivation T R (.rslash x m y)) (d₂ : Derivation T R y)
    (h : R x ⟨.right, m, y⟩ [] := by decide) : Derivation T R x :=
  .node (r := y) (c := x) (.forward [] h) d₁ d₂

/-- Backward application `<`, `Y X\Y ⇒ X`. -/
abbrev bapp (d₁ : Derivation T R y) (d₂ : Derivation T R (.lslash x m y))
    (h : R x ⟨.left, m, y⟩ [] := by decide) : Derivation T R x :=
  .node (l := y) (c := x) (.backward [] h) d₁ d₂

/-- Forward harmonic composition `>B`, `X/Y Y/Z ⇒ X/Z`. -/
abbrev fcomp (d₁ : Derivation T R (.rslash x m y)) (d₂ : Derivation T R (.rslash y n z))
    (h : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩] := by decide) : Derivation T R (.rslash x n z) :=
  .node (r := .rslash y n z) (c := .rslash x n z) (.forward [⟨.right, n, z⟩] h) d₁ d₂

/-- Backward harmonic composition `<B`, `Y\Z X\Y ⇒ X\Z`. -/
abbrev bcomp (d₁ : Derivation T R (.lslash y n z)) (d₂ : Derivation T R (.lslash x m y))
    (h : R x ⟨.left, m, y⟩ [⟨.left, n, z⟩] := by decide) : Derivation T R (.lslash x n z) :=
  .node (l := .lslash y n z) (c := .lslash x n z) (.backward [⟨.left, n, z⟩] h) d₁ d₂

/-- Forward crossing composition `>B×`, `X/Y Y\Z ⇒ X\Z`. -/
abbrev fcompx (d₁ : Derivation T R (.rslash x m y)) (d₂ : Derivation T R (.lslash y n z))
    (h : R x ⟨.right, m, y⟩ [⟨.left, n, z⟩] := by decide) : Derivation T R (.lslash x n z) :=
  .node (r := .lslash y n z) (c := .lslash x n z) (.forward [⟨.left, n, z⟩] h) d₁ d₂

/-- Backward crossing composition `<B×`, `Y/Z X\Y ⇒ X/Z`. -/
abbrev bcompx (d₁ : Derivation T R (.rslash y n z)) (d₂ : Derivation T R (.lslash x m y))
    (h : R x ⟨.left, m, y⟩ [⟨.right, n, z⟩] := by decide) : Derivation T R (.rslash x n z) :=
  .node (l := .rslash y n z) (c := .rslash x n z) (.backward [⟨.right, n, z⟩] h) d₁ d₂

/-- The token string a derivation spells out, its leaves from left to right. Rule nodes
concatenate their daughters, so the yield is independent of the derivation's combinatory
structure. -/
def yield {c : Cat α} : Derivation T R c → List T
  | .lex f _ => [f]
  | .node _ d₁ d₂ => d₁.yield ++ d₂.yield

theorem yield_ne_nil {c : Cat α} (d : Derivation T R c) : d.yield ≠ [] := by
  induction d with
  | lex => simp [yield]
  | node _ d₁ d₂ ih₁ _ => simp [yield, ih₁]

theorem eq_lex_of_yield_eq_singleton {c : Cat α} {d : Derivation T R c} {t : T}
    (h : d.yield = [t]) : d = .lex t c := by
  cases d with
  | lex => simp_all [yield]
  | node _ d₁ d₂ =>
    simp only [yield, List.append_eq_singleton_iff] at h
    exact h.elim (fun h ↦ absurd h.1 d₁.yield_ne_nil) fun h ↦ absurd h.2 d₂.yield_ne_nil

/-- The number of combinatory rule applications in a derivation. -/
def opCount {c : Cat α} : Derivation T R c → Nat
  | .lex _ _ => 0
  | .node _ d₁ d₂ => 1 + d₁.opCount + d₂.opCount

/-- Every lexical leaf of the derivation is an entry of the lexicon `L`. -/
def LexIn (L : List (T × Cat α)) {c : Cat α} : Derivation T R c → Prop
  | .lex f c => (f, c) ∈ L
  | .node _ d₁ d₂ => d₁.LexIn L ∧ d₂.LexIn L

instance LexIn.decidable [DecidableEq T] [DecidableEq α] (L : List (T × Cat α)) {c : Cat α} :
    ∀ d : Derivation T R c, Decidable (d.LexIn L)
  | .lex f c => inferInstanceAs (Decidable ((f, c) ∈ L))
  | .node _ d₁ d₂ =>
      @instDecidableAnd _ _ (decidable L d₁) (decidable L d₂)

/-! ### The count invariant -/

theorem _root_.CCG.Rule.count_eq [DecidableEq α] (a : α) {l r c : Cat α}
    (ru : Rule R l r c) : c.count a = l.count a + r.count a := by
  cases ru <;> simp only [Cat.count_pushArgs, Cat.count_rslash, Cat.count_lslash] <;> omega

/-- The count invariant of [van-benthem-1986]. A derivation's category has the count of its
leaves, so a string whose lexical counts do not sum to the count of a category has no derivation
of that category from the lexicon, whatever the rule system. -/
theorem count_eq_sum [DecidableEq α] (a : α) {L : List (T × Cat α)} {f : T → ℤ}
    (hL : ∀ p ∈ L, p.2.count a = f p.1) {c : Cat α} :
    ∀ d : Derivation T R c, d.LexIn L → c.count a = (d.yield.map f).sum
  | .lex w c, h => by simpa [yield] using hL (w, c) h
  | .node ru d₁ d₂, h => by
    rw [ru.count_eq a, count_eq_sum a hL d₁ (show d₁.LexIn L ∧ d₂.LexIn L from h).1,
      count_eq_sum a hL d₂ (show d₁.LexIn L ∧ d₂.LexIn L from h).2, yield, List.map_append,
      List.sum_append]

/-- The derivation contains a composition node (of any degree or direction). -/
def HasComp {c : Cat α} : Derivation T R c → Prop
  | .lex _ _ => False
  | .node ru d₁ d₂ => ru.IsComp ∨ d₁.HasComp ∨ d₂.HasComp

instance HasComp.decidable {c : Cat α} : ∀ d : Derivation T R c, Decidable d.HasComp
  | .lex _ _ => isFalse fun h => h
  | .node _ d₁ d₂ =>
      @instDecidableOr _ _ inferInstance
        (@instDecidableOr _ _ (decidable d₁) (decidable d₂))

end Derivation

end CCG
