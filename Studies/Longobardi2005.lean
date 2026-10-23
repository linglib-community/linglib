module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Longobardi (2005): Toward a Unified Grammar of Reference

This file formalizes [longobardi-2005], which unifies the syntax of proper names and the
semantics of bare nouns under one mapping theory. Access to N-to-D raising, the derivational
route to object reference, is not bipolar but scalar: pronouns are always in D, proper names
raise whenever D holds no lexical determiner, the names of days and *casa* and the kinship terms
raise only under deixis or a genitive modifier, and ordinary common nouns never raise (25).
Three tests rank the four classes of table (28): object reference in D, use as a predicative
restriction outside D, and kind reference under the definite article, which no proper name has,
*la Maria* being as rigid as *Maria* while *il cane* names a kind (26). Individuals are denoted
in D and arguments denote individuals (52), (53), as constants, with one fixed referential value,
or as variables ranging over a set (54), so an argument is a constant exactly when D holds a
lexically referential expression, a raised noun, a pronoun, a demonstrative or an expletive
article chained to the noun, and is otherwise a variable (55), (56), bound by the operator in D
or unselectively when D is empty (59). A variable must range over a set and objects are not sets,
so only a kind-naming noun restricts one: common nouns need not raise (57a), and by Last Resort
(63) may not, while proper names, object-naming, must raise or take an expletive article, which
answers (57b) and (57c). The article of a name is then obligatorily an expletive, whence the
absence of a kind reading in (26b).

## Implementation notes

The scale of properness is the linear order of the four classes of (28), and each test is a
map into the three-valued scale of access, never, under marked conditions, or always, so that
the paper's "conditioned" cells are values rather than lost. N-to-D raising is the choice of
referential content for an empty D, and Last Resort licenses it exactly when the nominal would
otherwise fail to denote. The *solo* diagnostic of raising, the mass and plural morphology of
kind naming (62), and the type-shifting of names under restrictive modification are not
formalized.

## References

* [longobardi-2005]
* [longobardi-1994]
* [longobardi-2001]
-/

@[expose] public section

namespace Longobardi2005

/-! ### The properness hierarchy -/

/-- The four classes of nominal head of table (28), from the most prototypically proper-like:
pronouns; proper names, the names of persons and places; the special common nouns, the names of
days and *casa* and the kinship terms, which raise to D only under deixis or a genitive
modifier; and ordinary common nouns. -/
inductive HeadClass
  | pronoun
  | properName
  | specialCommon
  | commonNoun
  deriving DecidableEq, Repr

namespace HeadClass

/-- Position on the scale of properness. -/
def rank : HeadClass → ℕ
  | .pronoun => 0
  | .properName => 1
  | .specialCommon => 2
  | .commonNoun => 3

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

/-- The scale of properness, the two prototypes at its ends. -/
instance : LinearOrder HeadClass := .lift' rank rank_injective

end HeadClass

/-- How a class passes one of the three tests of (28), which is not at all, only under marked
conditions, or freely. -/
inductive Access
  | never
  | conditioned
  | always
  deriving DecidableEq, Repr

namespace Access

/-- Position on the scale of access. -/
def rank : Access → ℕ
  | .never => 0
  | .conditioned => 1
  | .always => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder Access := .lift' rank rank_injective

end Access

/-- Object reference in D, the first column of (28), which the special common nouns achieve only
with the identifying context of deixis or a genitive restriction and common nouns never do. -/
def HeadClass.objectReference : HeadClass → Access
  | .pronoun | .properName => .always
  | .specialCommon => .conditioned
  | .commonNoun => .never

/-- Use as a predicative restriction outside D, the second column of (28), which pronouns never
have and proper names only under the marked conditions of restrictive modification. -/
def HeadClass.predicative : HeadClass → Access
  | .pronoun => .never
  | .properName => .conditioned
  | .specialCommon | .commonNoun => .always

/-- Kind reference under the definite article, the third column of (28) and the test of (26)
and (27): no pronoun or proper name has it. -/
def HeadClass.kindReference : HeadClass → Access
  | .pronoun | .properName => .never
  | .specialCommon | .commonNoun => .always

theorem objectReference_antitone : Antitone HeadClass.objectReference := fun a b h ↦ by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

theorem predicative_monotone : Monotone HeadClass.predicative := fun a b h ↦ by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

theorem kindReference_monotone : Monotone HeadClass.kindReference := fun a b h ↦ by
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

theorem kindReference_ne_never_iff (c : HeadClass) :
    c.kindReference ≠ .never ↔ .specialCommon ≤ c := by
  cases c <;> decide

theorem objectReference_and_kindReference_iff (c : HeadClass) :
    c.objectReference ≠ .never ∧ c.kindReference ≠ .never ↔ c = .specialCommon := by
  cases c <;> decide

/-! ### The topological mapping theory -/

/-- What a noun names, an object, learned by applying the name to one term of experience, or a
kind, a potentially open set of objects recognizable as such. Proper names are object-naming,
common nouns kind-naming. -/
inductive Naming
  | object
  | kind
  deriving DecidableEq, Repr

/-- The content of D, which is empty, a lexically referential expression, a noun raised to D, a
pronoun, a demonstrative or an expletive article chained to the noun (56a), or an overt
operator, a lexical determiner or quantifier (58). -/
inductive DContent
  | empty
  | referential
  | operator
  deriving DecidableEq, Repr

/-- A nominal, by what its head names and what its D contains. -/
structure Nominal where
  head : Naming
  d : DContent
  deriving DecidableEq, Repr

namespace Nominal

variable (n : Nominal)

/-- A constant has one fixed referential value (54a), which requires referential content in D,
by raising or by an expletive article chained to the noun (56a). -/
def IsConstant : Prop := n.d = .referential

/-- A variable is bound by the operator in D or unselectively when D is empty and ranges over a
set (54b), the objects of the kind the noun names (59); objects are not sets, so only a
kind-naming noun restricts one. -/
def IsVariable : Prop := n.d ≠ .referential ∧ n.head = .kind

/-- Individuals are denoted in D and arguments denote individuals (52), (53), as constants or as
variables. -/
def Denotes : Prop := n.IsConstant ∨ n.IsVariable

instance : Decidable n.IsConstant := inferInstanceAs (Decidable (_ = _))

instance : Decidable n.IsVariable := inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable n.Denotes := inferInstanceAs (Decidable (_ ∨ _))

variable {n}

/-- (55): an argument with an empty D is a variable. -/
theorem isVariable_of_empty (h : n.Denotes) (hd : n.d = .empty) : n.IsVariable :=
  h.resolve_left fun hc ↦ DContent.noConfusion (hd.symm.trans hc)

/-- (56b): an argument that is not a constant is a variable. -/
theorem isVariable_of_not_isConstant (h : n.Denotes) (hc : ¬ n.IsConstant) : n.IsVariable :=
  h.resolve_left hc

theorem isVariable_of_operator (h : n.Denotes) (hd : n.d = .operator) : n.IsVariable :=
  h.resolve_left fun hc ↦ DContent.noConfusion (hd.symm.trans hc)

/-- (57a): a kind-naming noun denotes with any content of D, so a common noun need not raise. -/
theorem denotes_of_kind (h : n.head = .kind) : n.Denotes := by
  by_cases hd : n.d = .referential
  · exact .inl hd
  · exact .inr ⟨hd, h⟩

/-- An object-naming noun denotes only as a constant (57c). -/
theorem denotes_iff_of_object (h : n.head = .object) : n.Denotes ↔ n.IsConstant :=
  ⟨fun hn ↦ hn.resolve_right fun hv ↦ Naming.noConfusion (h.symm.trans hv.2), .inl⟩

end Nominal

/-! ### Last Resort -/

/-- N-to-D raising fills an empty D with referential content, and by Last Resort (63) it is
licensed exactly when the nominal would otherwise fail to denote. -/
def MayRaise (h : Naming) : Prop := ¬ (⟨h, .empty⟩ : Nominal).Denotes

instance (h : Naming) : Decidable (MayRaise h) := inferInstanceAs (Decidable (¬ _))

/-- The answer to (57b) and (57c): a common noun may not raise, since it denotes without, and a
proper name may raise, since it must. -/
theorem mayRaise_iff (h : Naming) : MayRaise h ↔ h = .object := by
  cases h <;> decide

/-! ### Expletive articles -/

/-- An article in D is an operator, binding a variable over the kind the noun names, or an
expletive, chained to the noun and contributing no operator. -/
inductive Article
  | operator
  | expletive
  deriving DecidableEq, Repr

/-- The content an article gives D. -/
def Article.dContent : Article → DContent
  | .operator => .operator
  | .expletive => .referential

/-- With an object-naming head, as in *la Maria*, the nominal denotes iff the article is expletive
(26b). -/
theorem denotes_iff_expletive (a : Article) :
    (⟨.object, a.dContent⟩ : Nominal).Denotes ↔ a = .expletive := by
  cases a <;> decide

/-- With a kind-naming head either article yields a denoting argument ((59), (26a)). -/
theorem denotes_of_kind_article (a : Article) : (⟨.kind, a.dContent⟩ : Nominal).Denotes :=
  Nominal.denotes_of_kind rfl

end Longobardi2005
