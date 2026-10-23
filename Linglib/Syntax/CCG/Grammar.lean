module

public import Linglib.Syntax.CCG.Derivation
public import Mathlib.Computability.Language

/-!
# CCG grammars and their languages

A CCG grammar is a finite lexicon, a start atom and a `RuleSystem`, so the formalisms of the
literature are choices of rule system. In the classical formalism of Weir and Joshi and of
Vijay-Shanker and Weir (`Grammar.targetRestricted`) a grammar owns a degree bound and a target
restriction, under which a rule fires only when the target of its primary input is the start
atom. In the multimodal formalism of Baldridge and Steedman (`Grammar.multimodal`) the rule
system is universal, and a grammar is nothing but its lexicon and start atom. A derivation step
is an instance `X/Y Yβ ⇒ Xβ` of the composition schema or its mirror, so it records its argument
sequence `β`, and the harmonic/crossed distinction follows from the slash directions. The
target-restricted rule system is modality-blind, so target-restricted grammars use the
unrestricted modality.

Kuhlmann, Koller and Satta show that with target restrictions the classical formalism is weakly
equivalent to tree-adjoining grammar and without them strictly weaker, and that the multimodal
formalism is likewise less expressive than TAG. Schiffer and Maletti upgrade the equivalence to
strong equivalence for grammars without empty lexical entries and with rules of degree at most 2.
Strings are lists over the token alphabet `T`, so empty lexical entries are inexpressible.

## Main definitions

* `CCG.Grammar`: a lexicon, a start atom, and a rule system.
* `CCG.Grammar.targetRestricted`, `CCG.Grammar.multimodal`: the two formalisms of the
  literature.
* `CCG.Grammar.Derives`: the derivability relation, with `Grammar.language` the language of
  token strings derived at the start atom.

## Main statements

* `CCG.Grammar.derives_iff`: a grammar derives `w` at `c` iff some `CCG.Derivation` in its rule
  system over its lexicon has yield `w`.

## Implementation notes

Derivability is an inductive `Prop`, mathlib's form for grammar formalisms
(`ContextFreeGrammar.Derives`), beside the intrinsically typed `CCG.Derivation` of the
interpreted theory: capacity arguments quantify over all derivations, and induction on `Derives`
is exactly that quantification. As with mathlib's `ContextFreeGrammar T`, a grammar is
parameterized by its token alphabet, and its language is a `Language T`.

## References

* [weir-joshi-1988]
* [vijay-shanker-weir-1994]
* [baldridge-2002]
* [steedman-2019]
* [kuhlmann-koller-satta-2015]
* [schiffer-maletti-2021]
-/

@[expose] public section

namespace CCG

variable {T α : Type*}

/-! ### Grammars and their languages -/

/-- The rule system of the classical formalism ([vijay-shanker-weir-1994],
[kuhlmann-koller-satta-2015]) admits composition up to a degree bound into a primary whose
target is the start atom. -/
def RuleSystem.targetRestricted (start : α) (degree : ℕ) : RuleSystem α :=
  fun x _ β ↦ β.length ≤ degree ∧ x.target = start

/-- A CCG grammar has a finite lexicon, a distinguished start atom, and a rule system. -/
structure Grammar (T α : Type*) where
  /-- Lexical entries, pairing a token with a category. -/
  lexicon : List (T × Cat α)
  /-- The distinguished atom, at which the language collects derivations. -/
  start : α
  /-- The instances of the composition schema the grammar permits. -/
  rules : RuleSystem α

/-- A target-restricted (VW-CCG) grammar restricts its rules to primary inputs with the start
atom as target. The normal form of [schiffer-maletti-2021] has `degree = 2`. -/
def Grammar.targetRestricted (lexicon : List (T × Cat α)) (start : α)
    (degree : Nat) : Grammar T α where
  lexicon := lexicon
  start := start
  rules := .targetRestricted start degree

/-- A multimodal grammar, in the radically lexicalized formalism of [steedman-2019], is a
lexicon and a start atom under the universal modality-controlled rule system. It is strictly less
expressive than the target-restricted grammars ([kuhlmann-koller-satta-2015]). -/
def Grammar.multimodal (lexicon : List (T × Cat α)) (start : α) : Grammar T α where
  lexicon := lexicon
  start := start
  rules := .multimodal

@[simp] theorem Grammar.multimodal_rules (lexicon : List (T × Cat α)) (start : α) :
    (Grammar.multimodal lexicon start).rules = .multimodal := rfl

/-- `G.Derives c w` says the grammar derives the token string `w` at category `c`, by a lexical
entry or by an instance of the composition schema over two adjacent derivations that the
grammar's rule system permits. -/
inductive Grammar.Derives (G : Grammar T α) : Cat α → List T → Prop where
  /-- A lexical entry derives its token. -/
  | lex {t : T} {c : Cat α} : (t, c) ∈ G.lexicon → G.Derives c [t]
  /-- Forward composition `X/Y Yβ ⇒ Xβ`, application when `β = []`. -/
  | forward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) {u v : List T} :
      G.Derives (.rslash x m y) u → G.Derives (y.pushArgs β) v →
      G.rules x ⟨.right, m, y⟩ β → G.Derives (x.pushArgs β) (u ++ v)
  /-- Backward composition `Yβ X\Y ⇒ Xβ`, application when `β = []`. -/
  | backward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) {u v : List T} :
      G.Derives (y.pushArgs β) u → G.Derives (.lslash x m y) v →
      G.rules x ⟨.left, m, y⟩ β → G.Derives (x.pushArgs β) (u ++ v)

/-- The string language of a grammar is the set of token strings derived at the start atom. -/
def Grammar.language (G : Grammar T α) : Language T :=
  { w | G.Derives (.atom G.start) w }

theorem Grammar.Derives.ne_nil {G : Grammar T α} {c : Cat α} {w : List T}
    (h : G.Derives c w) : w ≠ [] := by
  induction h with
  | lex => exact List.cons_ne_nil _ _
  | forward _ _ _ _ ih => exact List.append_ne_nil_of_left_ne_nil ih _
  | backward _ _ _ _ ih => exact List.append_ne_nil_of_left_ne_nil ih _

/-! ### Derivability and the tree calculus

A grammar's derivability coincides with the existence of an intrinsically typed `Derivation`
tree in its rule system over its lexicon: the trees are the proof-relevant calculus (what
`Derivation.interp` consumes), the relation is its string-language shadow. -/

/-- Every `Derivation` tree in a grammar's rule system over its lexicon witnesses derivability. -/
theorem Derivation.derives {G : Grammar T α} {c : Cat α} (d : Derivation T G.rules c)
    (h : d.LexIn G.lexicon) : G.Derives c d.yield := by
  induction d with
  | lex => exact .lex h
  | node ru d₁ d₂ ih₁ ih₂ =>
    cases ru with
    | forward β hr => exact .forward β (ih₁ h.1) (ih₂ h.2) hr
    | backward β hr => exact .backward β (ih₁ h.1) (ih₂ h.2) hr

theorem Grammar.derives_iff {G : Grammar T α} {c : Cat α} {w : List T} :
    G.Derives c w ↔ ∃ d : Derivation T G.rules c, d.LexIn G.lexicon ∧ d.yield = w := by
  refine ⟨fun h ↦ ?_, fun ⟨d, hl, hy⟩ ↦ hy ▸ d.derives hl⟩
  induction h with
  | @lex t c h => exact ⟨.lex t c, h, rfl⟩
  | forward β _ _ hr ih₁ ih₂ =>
    obtain ⟨d₁, h₁, rfl⟩ := ih₁
    obtain ⟨d₂, h₂, rfl⟩ := ih₂
    exact ⟨.node (.forward β hr) d₁ d₂, ⟨h₁, h₂⟩, rfl⟩
  | backward β _ _ hr ih₁ ih₂ =>
    obtain ⟨d₁, h₁, rfl⟩ := ih₁
    obtain ⟨d₂, h₂, rfl⟩ := ih₂
    exact ⟨.node (.backward β hr) d₁ d₂, ⟨h₁, h₂⟩, rfl⟩

end CCG
