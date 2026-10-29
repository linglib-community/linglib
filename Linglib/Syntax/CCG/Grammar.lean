module

public import Linglib.Syntax.CCG.Derivation
public import Mathlib.Computability.Language

/-!
# CCG grammars and their languages

A CCG grammar is a finite lexicon, a start atom and a `RuleSystem`. Each formalism of the
literature is a choice of rule system, though a rule system may be any relation on the instances
of the composition schema. In the classical formalism of Weir and Joshi and of Vijay-Shanker and
Weir, VW-CCG, a grammar lists finitely many restricted rules (`RuleSystem.ofRestrictedRules`),
each a forward or backward rule of one degree whose instances may be restricted in the target of
the primary input and in the secondary input. Restricting every rule up to a degree bound to
primary inputs whose target is the start atom (`Grammar.targetRestricted`) is one such grammar
(`RuleSystem.targetRestricted_eq_ofRestrictedRules`), the restriction of Kuhlmann, Koller and
Satta's grammar for `aⁿbⁿcⁿ`. In the multimodal formalism of Baldridge and Steedman
(`Grammar.multimodal`) the rule system is fixed up to a degree bound, and a grammar is nothing
but its lexicon, start atom and bound. A derivation step is an instance `X/Y Yβ ⇒ Xβ` of the
composition schema or its mirror, so it records its argument sequence `β`, and the
harmonic/crossed distinction follows from the slash directions. The VW-CCG rule systems are
modality-blind, so their grammars use the unrestricted modality.

Kuhlmann, Koller and Satta show that VW-CCG is weakly equivalent to tree-adjoining grammar, also
when restricted to prefix-closed grammars, that prefix-closed grammars without target restrictions
are strictly less expressive, and that their O-CCG, the multimodal formalism with the rules of
OpenCCG, is strictly less expressive than TAG as well. Their constructions of TAG languages
restrict secondary inputs, so the uniform target restriction is not the class of the
equivalence. Schiffer and Maletti upgrade the equivalence to strong equivalence for grammars
without empty lexical entries and with rules of degree at most 2. Strings are lists over the
token alphabet `T`, so empty lexical entries are inexpressible.

## Main definitions

* `CCG.Grammar`: a lexicon, a start atom, and a rule system.
* `CCG.RestrictedRule`, `CCG.RuleSystem.ofRestrictedRules`: the restricted rules of VW-CCG and
  the rule system they define.
* `CCG.Grammar.targetRestricted`, `CCG.Grammar.multimodal`: the uniform target restriction and
  the multimodal formalism.
* `CCG.Grammar.Derives`: the derivability relation, with `Grammar.language` the language of
  token strings derived at the start atom.

## Main statements

* `CCG.RuleSystem.targetRestricted_eq_ofRestrictedRules`: the uniform target restriction is a
  VW-CCG rule system.
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

/-- A restricted rule of VW-CCG ([vijay-shanker-weir-1994], [kuhlmann-koller-satta-2015]):
forward or backward composition of one degree, application at degree `0`, whose instances may be
restricted in the target of the primary input and in the secondary input, in part or in its
entirety. -/
structure RestrictedRule (α : Type*) where
  /-- The side the primary slash looks to, `right` for a forward and `left` for a backward
  rule. -/
  side : Edge
  /-- The degree, the number of arguments the rule composes. -/
  degree : ℕ
  /-- The targets the primary input may have. -/
  primaryTarget : Set α
  /-- The secondary inputs the rule admits. -/
  secondary : Set (Cat α)

/-- The rule system of a VW-CCG whose restricted rules are `rs`: an instance of the composition
schema fires when it is a valid instance of one of them. -/
def RuleSystem.ofRestrictedRules (rs : List (RestrictedRule α)) : RuleSystem α := fun x a β ↦
  ∃ r ∈ rs, r.side = a.side ∧ r.degree = β.length ∧ x.target ∈ r.primaryTarget ∧
    a.cat.pushArgs β ∈ r.secondary

/-- The uniform target restriction admits composition up to a degree bound into a primary
input whose target is the start atom, the restriction of every rule of
[kuhlmann-koller-satta-2015]'s grammar for `aⁿbⁿcⁿ`. -/
def RuleSystem.targetRestricted (start : α) (degree : ℕ) : RuleSystem α :=
  fun x _ β ↦ β.length ≤ degree ∧ x.target = start

/-- The uniform target restriction is the VW-CCG rule system of forward and backward composition
of each degree up to the bound, restricted to primary inputs whose target is the start atom and
unrestricted in the secondary input. -/
theorem RuleSystem.targetRestricted_eq_ofRestrictedRules (start : α) (degree : ℕ) :
    targetRestricted start degree = ofRestrictedRules ((List.range (degree + 1)).flatMap
      fun n ↦ [⟨.right, n, {start}, Set.univ⟩, ⟨.left, n, {start}, Set.univ⟩]) := by
  funext x a β
  refine propext ⟨fun ⟨hβ, hx⟩ ↦ ?_, ?_⟩
  · refine ⟨⟨a.side, β.length, {start}, Set.univ⟩, List.mem_flatMap.2 ⟨β.length,
      List.mem_range.2 (by omega), ?_⟩, rfl, rfl, hx, trivial⟩
    cases a.side <;> simp
  · rintro ⟨r, hr, -, hd, hx, -⟩
    obtain ⟨n, hn, hr⟩ := List.mem_flatMap.1 hr
    rw [List.mem_range] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by have : n = β.length := hd; omega, hx⟩

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

/-- Derivability is the tree calculus: a grammar derives `w` at `c` iff some derivation in its
rule system over its lexicon has yield `w`. -/
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
