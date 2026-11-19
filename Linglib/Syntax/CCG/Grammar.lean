module

public import Linglib.Syntax.CCG.Derivation
public import Mathlib.Computability.Language

/-!
# CCG grammars and their languages

A CCG grammar is a finite lexicon, which gives each word its categories, together with a start
atom and a rule system. The grammar derives a string at a category when the string can be built
from lexical entries by its rules, and its language is the set of strings it derives at the
start atom. [A grammar derives a string exactly when some derivation tree over its lexicon
spells it out](##CCG.Grammar.derives_iff).

How much a grammar can generate depends on its rule system. Kuhlmann, Koller and Satta show
that VW-CCG generates the languages of tree-adjoining grammar, and that grammars without target
restrictions, and the multimodal formalism with the rules of OpenCCG, generate strictly fewer.
Schiffer and Maletti show that for grammars with rules of degree at most 2 the equivalence with
tree-adjoining grammar also holds of the trees. Strings are lists of tokens, so a lexical entry
for the empty string cannot be stated.

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

/-- A CCG grammar has a finite lexicon, a distinguished start atom, and a rule system. -/
structure Grammar (T α : Type*) where
  /-- Lexical entries, pairing a token with a category. -/
  lexicon : List (T × Cat α)
  /-- The distinguished atom, at which the language collects derivations. -/
  start : α
  /-- The instances of the composition schema the grammar permits. -/
  rules : RuleSystem α

/-- A grammar under the uniform target restriction, whose rules fire only on primary inputs with
the start atom as target. The normal form of [schiffer-maletti-2021] has `degree = 2`. -/
def Grammar.targetRestricted (lexicon : List (T × Cat α)) (start : α)
    (degree : Nat) : Grammar T α where
  lexicon := lexicon
  start := start
  rules := .targetRestricted start degree

/-- A multimodal grammar, in the radically lexicalized formalism of [steedman-2019], is a
lexicon, a start atom and a degree bound under the modality-controlled rule system.
[kuhlmann-koller-satta-2015] show that their O-CCG, whose composition rules
`RuleSystem.multimodal` follows, generates a proper subclass of the languages of tree-adjoining
grammar. -/
def Grammar.multimodal (lexicon : List (T × Cat α)) (start : α) (degree : ℕ) : Grammar T α where
  lexicon := lexicon
  start := start
  rules := .multimodal degree

@[simp] theorem Grammar.multimodal_rules (lexicon : List (T × Cat α)) (start : α) (degree : ℕ) :
    (Grammar.multimodal lexicon start degree).rules = .multimodal degree := rfl

/-- `G.Derives c w` says the grammar derives the token string `w` at category `c`, by a lexical
entry or by an instance of the composition schema over two adjacent derivations that the
grammar's rule system permits. -/
inductive Grammar.Derives (G : Grammar T α) : Cat α → List T → Prop where
  /-- A lexical entry derives its token. -/
  | lex {t : T} {c : Cat α} : (t, c) ∈ G.lexicon → G.Derives c [t]
  /-- Forward composition `X/Y Yβ ⇒ Xβ`, application when `β = []`. -/
  | forward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) {u v : List T} :
      G.Derives (.slash .right x m y) u → G.Derives (y.pushArgs β) v →
      G.rules x ⟨.right, m, y⟩ β → G.Derives (x.pushArgs β) (u ++ v)
  /-- Backward composition `Yβ X\Y ⇒ Xβ`, application when `β = []`. -/
  | backward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) {u v : List T} :
      G.Derives (y.pushArgs β) u → G.Derives (.slash .left x m y) v →
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
theorem Derivation.derives {G : Grammar T α} {c : Cat α} (d : Derivation (fun _ ↦ T) G.rules c)
    (h : d.LexIn G.lexicon) : G.Derives c d.yield := by
  induction d with
  | lex => exact .lex h
  | node ru d₁ d₂ ih₁ ih₂ =>
    cases ru with
    | forward β hr => exact .forward β (ih₁ h.1) (ih₂ h.2) hr
    | backward β hr => exact .backward β (ih₁ h.1) (ih₂ h.2) hr

/-- Derivability is the tree calculus: a grammar derives `w` at `c` iff some derivation in its
rule system over its lexicon has yield `w`. -/
theorem Grammar.derives_iff {G : Grammar T α} {c : Cat α} {w : List T} :
    G.Derives c w ↔ ∃ d : Derivation (fun _ ↦ T) G.rules c, d.LexIn G.lexicon ∧ d.yield = w := by
  refine ⟨fun h ↦ ?_, fun ⟨d, hl, hy⟩ ↦ hy ▸ d.derives hl⟩
  induction h with
  | @lex t c h => exact ⟨.lex c t, h, rfl⟩
  | forward β _ _ hr ih₁ ih₂ =>
    obtain ⟨d₁, h₁, rfl⟩ := ih₁
    obtain ⟨d₂, h₂, rfl⟩ := ih₂
    exact ⟨.node (.forward β hr) d₁ d₂, ⟨h₁, h₂⟩, rfl⟩
  | backward β _ _ hr ih₁ ih₂ =>
    obtain ⟨d₁, h₁, rfl⟩ := ih₁
    obtain ⟨d₂, h₂, rfl⟩ := ih₂
    exact ⟨.node (.backward β hr) d₁ d₂, ⟨h₁, h₂⟩, rfl⟩

end CCG
