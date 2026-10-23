module

public import Linglib.Data.Examples.Snyder2026
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Setoid.Basic

/-!
# Snyder (2026): Numbers as Kinds

This file formalizes [snyder-2026]'s Polymorphic Contextualism: the lexical meaning of *two* is
an atomic predicate applying to different countable entities in different contexts, numeral
tokens, subkinds of the kind TWO, or TWO itself, and every other meaning of the word derives
from it by type-shifting. The rival polymorphic analyses take the lexical meaning to be a
numeral, an entity from which the cardinality predicate derives by CARD (Substantivalism), or
the cardinality predicate itself, from which the numeral derives by NOM and Rothstein's
schematic equation (Adjectivalism). The three analyses are derivation maps from a lexical
type through the type-shifters CARD, PM, A, NOM, IOTA and IDENT to the semantic functions of
(1) and (76) (`PolymorphicAnalysis.path`), each of which composes to the function's type
(`analyses_well_typed`); Contextualism derives every function while the two rivals derive
none of the token, kind and taxonomic uses (`contextualism_covers_all`,
`substantivalism_gap`, `adjectivalism_gap`, `contextualism_strictly_extends`). Numbers are
kinds formed as in [mendia-2020] by a salient equivalence relation on their tokens, here the
number system a token belongs to (`kfTWO`), so distinct subkinds of TWO are disjoint
(`subkinds_distinct`); a close appositive is the Sharvy definite over the conjunction of its
two nouns (`closeAppositive`), and definites over disjoint restrictions of the extension of
*two* refer to distinct subkinds, which dissolves Benacerraf's Identification Problem for (20)
(`closeAppositive_ne_of_disjoint`, `identification_problem_resolved`). Section 6 extends the
analysis to colour words, RED having subkinds such as crimson and maroon (`kfRed`,
`red_subkinds_distinct`). The examples are rows of `Data/Examples/Snyder2026`, each of which
carries its semantic function, and every function is attested (`functions_attested`).

## Implementation notes

* Types are the fragment e, ⟨e,t⟩ and ⟨⟨e,t⟩,t⟩; PM is monadic, its second predicate supplied
  by the syntax. Rothstein's schematic equation is a meta-level identification and not a
  type-shifter, so the adjectivalist numeral is the nominalized cardinality predicate with the
  equation read off it.
* In the contextualist diagram the token, kind and taxonomic uses (76h), (76j) and (76f) are
  the lexical predicate itself, applied to tokens or kinds, and the numeral, kind-referring
  and token-referring uses (76e), (76i) and (76g) are IOTA over it; the taxonomic use is
  predicate-typed, the others entity-typed.
* Sharvy's definite is a partial operation over a finite domain, undefined when no or more
  than one entity satisfies the restriction; the Identification Problem is worked on a domain
  with one token per number system.
* Tokens of *two* are classified by their number system (`kfTWO`), which on these tokens agrees
  with section 4.3's partition by the number a token represents; the subkinds of TWO are the
  classes, as kind individuals in the quotient.

## References

* [snyder-2026]
* [mendia-2020]
* [sharvy-1980]
* [partee-1987]
* [benacerraf-1965]
-/

@[expose] public section

namespace Snyder2026

/-! ### The three polymorphic analyses and the semantic functions -/

/-- Semantic types: entities, predicates and generalized quantifiers. -/
inductive SemTy
  | e | et | ett
  deriving DecidableEq

/-- The three polymorphic analyses: the lexical meaning of *two* is a numeral (5), a
cardinality predicate (9), or an atomic predicate over relativized atoms (73). -/
inductive PolymorphicAnalysis
  | substantivalism | adjectivalism | contextualism
  deriving DecidableEq

/-- The lexical type of *two* under each analysis. -/
def PolymorphicAnalysis.lexicalType : PolymorphicAnalysis → SemTy
  | .substantivalism => .e
  | .adjectivalism => .et
  | .contextualism => .et

/-- The semantic functions of *two*: the six of (1) and the token, kind and taxonomic uses of
(76g) to (76j). -/
inductive SemanticFunction
  | predicative | attributive | quantificational | specificational | numeral | closeAppositive
  | tokenRef | tokenPredicate | kindRef | taxonomic
  deriving DecidableEq

/-- The type at which each function is used. -/
def SemanticFunction.targetType : SemanticFunction → SemTy
  | .predicative | .attributive | .tokenPredicate | .taxonomic => .et
  | .quantificational => .ett
  | .specificational | .numeral | .closeAppositive | .tokenRef | .kindRef => .e

/-- The label of a function in the example rows. -/
def SemanticFunction.label : SemanticFunction → String
  | .predicative => "predicative"
  | .attributive => "attributive"
  | .quantificational => "quantificational"
  | .specificational => "specificational"
  | .numeral => "numeral"
  | .closeAppositive => "closeAppositive"
  | .tokenRef => "tokenRef"
  | .tokenPredicate => "tokenPredicate"
  | .kindRef => "kindRef"
  | .taxonomic => "taxonomic"

/-- The type-shifters of the diagrams: CARD (6a), Predicate Modification (7a), A (8a), NOM
(10a), IOTA (74a) and IDENT (17a). -/
inductive Operator
  | card | pm | a | nom | iota | ident
  deriving DecidableEq

/-- The input type of a type-shifter. -/
def Operator.input : Operator → SemTy
  | .card | .ident => .e
  | .pm | .a | .nom | .iota => .et

/-- The output type of a type-shifter. -/
def Operator.output : Operator → SemTy
  | .card | .pm | .ident => .et
  | .a => .ett
  | .nom | .iota => .e

/-- The type a chain of type-shifters reaches from a type, if each composes with the last. -/
def wellTyped : SemTy → List Operator → Option SemTy
  | t, [] => some t
  | t, op :: ops => if t = op.input then wellTyped op.output ops else none

/-- The derivation map of each analysis, the diagrams of sections 2 and 5: the chain of
type-shifters from the lexical meaning to a function, or none where the analysis does not
derive it. Substantivalism derives the cardinal uses by CARD and the close appositive by IDENT
and IOTA; Adjectivalism nominalizes the cardinality predicate for the numeral and passes
through it for the close appositive; Contextualism reaches the numeral, kind and token
references by IOTA, the taxonomic and token predications by the lexical predicate itself, the
cardinal uses through the numeral, and the close appositive by PM with *number* and IOTA (87). -/
def PolymorphicAnalysis.path : PolymorphicAnalysis → SemanticFunction → Option (List Operator)
  | .substantivalism, .numeral => some []
  | .substantivalism, .predicative => some [.card]
  | .substantivalism, .attributive => some [.card, .pm]
  | .substantivalism, .quantificational => some [.card, .a]
  | .substantivalism, .specificational => some [.card, .nom]
  | .substantivalism, .closeAppositive => some [.ident, .iota]
  | .substantivalism, _ => none
  | .adjectivalism, .predicative => some []
  | .adjectivalism, .attributive => some [.pm]
  | .adjectivalism, .quantificational => some [.a]
  | .adjectivalism, .specificational => some [.nom]
  | .adjectivalism, .numeral => some [.nom]
  | .adjectivalism, .closeAppositive => some [.nom, .ident, .iota]
  | .adjectivalism, _ => none
  | .contextualism, .taxonomic => some []
  | .contextualism, .tokenPredicate => some []
  | .contextualism, .numeral => some [.iota]
  | .contextualism, .kindRef => some [.iota]
  | .contextualism, .tokenRef => some [.iota]
  | .contextualism, .predicative => some [.iota, .card]
  | .contextualism, .attributive => some [.iota, .card, .pm]
  | .contextualism, .quantificational => some [.iota, .card, .a]
  | .contextualism, .specificational => some [.iota, .card, .nom]
  | .contextualism, .closeAppositive => some [.pm, .iota]

/-- An analysis covers a function when it derives it. -/
def PolymorphicAnalysis.Covers (a : PolymorphicAnalysis) (sf : SemanticFunction) : Prop :=
  (a.path sf).isSome

instance (a : PolymorphicAnalysis) (sf : SemanticFunction) : Decidable (a.Covers sf) :=
  inferInstanceAs (Decidable (_ = true))

theorem analyses_well_typed (a : PolymorphicAnalysis) (sf : SemanticFunction) :
    ∀ ops ∈ a.path sf, wellTyped a.lexicalType ops = some sf.targetType := by
  cases a <;> cases sf <;> decide

theorem contextualism_covers_all (sf : SemanticFunction) :
    PolymorphicAnalysis.contextualism.Covers sf := by
  cases sf <;> decide

theorem substantivalism_gap :
    ∀ sf ∈ [SemanticFunction.tokenRef, .tokenPredicate, .kindRef, .taxonomic],
      ¬ PolymorphicAnalysis.substantivalism.Covers sf := by
  decide

theorem adjectivalism_gap :
    ∀ sf ∈ [SemanticFunction.tokenRef, .tokenPredicate, .kindRef, .taxonomic],
      ¬ PolymorphicAnalysis.adjectivalism.Covers sf := by
  decide

theorem contextualism_strictly_extends (a : PolymorphicAnalysis) :
    (∀ sf, a.Covers sf → PolymorphicAnalysis.contextualism.Covers sf) ∧
      (a ≠ .contextualism → ∃ sf, PolymorphicAnalysis.contextualism.Covers sf ∧ ¬ a.Covers sf) :=
  ⟨λ sf _ => contextualism_covers_all sf, λ h => ⟨.taxonomic, contextualism_covers_all _,
    by cases a <;> first | exact absurd rfl h | decide⟩⟩

/-! ### Numbers as kinds, sections 4 and 5

A kind is formed by partitioning a domain by a salient equivalence relation; TWO is
partitioned into the subkinds two-of-the-naturals, two-of-the-integers, two-of-the-rationals
and two-of-the-reals by the number system a numeral token belongs to (section 4.3). -/

/-- The number systems of the paper's board. -/
inductive MathSystem
  | nat | int | rat | real
  deriving DecidableEq, Fintype

/-- A numeral token: the number system it belongs to and an index distinguishing tokens of the
same system. -/
structure TwoToken where
  system : MathSystem
  idx : ℕ
  deriving DecidableEq

/-- The kind formation for TWO: tokens are equivalent when they belong to the same number
system, and each class is a subkind of TWO. -/
abbrev kfTWO : Setoid TwoToken := Setoid.ker TwoToken.system

theorem subkinds_distinct {t₁ t₂ : TwoToken} (h : t₁.system ≠ t₂.system) :
    (⟦t₁⟧ : Quotient kfTWO) ≠ ⟦t₂⟧ :=
  fun e ↦ h (Quotient.exact e)

section Sharvy

variable {α : Type*}

/-- Sharvy's definite (16a) over a finite domain: the unique satisfier of the restriction, if
there is exactly one. -/
def sharvyIota (domain : List α) (P : α → Bool) : Option α :=
  match domain.filter P with
  | [j] => some j
  | _ => none

/-- A close appositive (16b): the definite over the conjunction of its two nouns. -/
def closeAppositive (domain : List α) (n₁ n₂ : α → Bool) : Option α :=
  sharvyIota domain λ x => n₁ x && n₂ x

theorem sharvyIota_eq_some_iff {domain : List α} {P : α → Bool} {j : α} :
    sharvyIota domain P = some j ↔ domain.filter P = [j] := by
  unfold sharvyIota
  refine ⟨λ h => ?_, λ h => by rw [h]⟩
  cases hf : domain.filter P with
  | nil => rw [hf] at h; cases h
  | cons hd tl =>
    cases tl with
    | nil => rw [hf] at h; injection h with hj; rw [hj]
    | cons _ _ => rw [hf] at h; cases h

theorem closeAppositive_ne_of_disjoint {domain : List α} {m₁ m₂ n : α → Bool} {j₁ j₂ : α}
    (hDisj : ∀ x, ¬ (m₁ x = true ∧ m₂ x = true)) (h₁ : closeAppositive domain m₁ n = some j₁)
    (h₂ : closeAppositive domain m₂ n = some j₂) : j₁ ≠ j₂ := by
  intro hEq
  have h1mem : j₁ ∈ domain.filter (λ x => m₁ x && n x) := by
    rw [sharvyIota_eq_some_iff.mp h₁]; simp
  have h2mem : j₂ ∈ domain.filter (λ x => m₂ x && n x) := by
    rw [sharvyIota_eq_some_iff.mp h₂]; simp
  have h1 := (List.mem_filter.mp h1mem).2
  have h2 := (List.mem_filter.mp h2mem).2
  rw [Bool.and_eq_true] at h1 h2
  exact hDisj j₁ ⟨h1.1, hEq ▸ h2.1⟩

end Sharvy

/-- Membership in the subkind of TWO of a number system. -/
def inSubkind (s : MathSystem) (t : TwoToken) : Bool := decide (t.system = s)

/-- The board of section 1: one token of two per number system. -/
def board : List TwoToken := [⟨.nat, 0⟩, ⟨.int, 0⟩, ⟨.rat, 0⟩, ⟨.real, 0⟩]

theorem closeAppositive_board (s : MathSystem) :
    closeAppositive board (inSubkind s) (λ _ => true) = some ⟨s, 0⟩ := by
  cases s <;> rfl

/-- Close appositives with the modifiers of two number systems refer to distinct subkinds, so (20a)
and (20b) are jointly coherent (section 5.2). -/
theorem identification_problem_resolved {s₁ s₂ : MathSystem} (h : s₁ ≠ s₂) :
    ∃ j₁ j₂, closeAppositive board (inSubkind s₁) (λ _ => true) = some j₁ ∧
      closeAppositive board (inSubkind s₂) (λ _ => true) = some j₂ ∧ j₁ ≠ j₂ :=
  ⟨_, _, closeAppositive_board s₁, closeAppositive_board s₂,
    closeAppositive_ne_of_disjoint (λ t ⟨h₁, h₂⟩ => h (by
      simp only [inSubkind, decide_eq_true_eq] at h₁ h₂; exact h₁.symm.trans h₂))
      (closeAppositive_board s₁) (closeAppositive_board s₂)⟩

/-! ### Colour words, section 6

The kind RED has the shades of the paint swatches as subkinds, and the colour word is an
atomic predicate over them and their tokens (97). -/

/-- The shades of red on the swatches. -/
inductive Shade
  | crimson | maroon | scarlet
  deriving DecidableEq

/-- A colour token, a swatch of a shade. -/
structure RedToken where
  shade : Shade
  idx : ℕ
  deriving DecidableEq

/-- The kind formation for RED: tokens are equivalent when they are of the same shade. -/
abbrev kfRed : Setoid RedToken := Setoid.ker RedToken.shade

/-- Tokens of distinct shades instantiate distinct subkinds of RED, the taxonomy under (94). -/
theorem red_subkinds_distinct {t₁ t₂ : RedToken} (h : t₁.shade ≠ t₂.shade) :
    (⟦t₁⟧ : Quotient kfRed) ≠ ⟦t₂⟧ :=
  fun e ↦ h (Quotient.exact e)

/-! ### The examples -/

theorem functions_attested (sf : SemanticFunction) :
    ∃ ex ∈ Examples.all, ex.feature? "function" = some sf.label := by
  cases sf <;> decide

end Snyder2026
