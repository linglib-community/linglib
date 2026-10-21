module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Definiteness

This file gives the frame-free vocabulary of definiteness. A nominal is definite or indefinite,
as Heim distinguishes them, and on the continuum of definiteness, or specificity, that Comrie,
Aissen and Haspelmath share, a definite ranks above a specific indefinite above a non-specific
one; Farkas and Brasoveanu separate the kinds of specificity, scopal, epistemic and partitive.
A definite article has one of two strengths, uniqueness and familiarity, after Schwarz, and the
article typologies are built on them. The strength a use of a definite calls for, after Hawkins
and Schwarz, and the strength of a bridging relation are recorded as data here; which cell a
language's determiner inventory falls in is derived in `Syntax/Category/Determiner/Basic.lean`,
and the descriptions themselves denote in `Semantics/Reference/Description.lean`.

## Main definitions

* `Reference.Definiteness`: definite or indefinite, as a two-element bounded linear order.
* `Reference.DefinitenessDegree`: the continuum of definiteness, with its cut
  `DefinitenessDegree.definiteness`.
* `Reference.Description.Strength`, `Reference.Description.Kind`: the strength of a definite
  article and the kind of a description, with `Strength.toKind` and `Kind.strength`.
* `Reference.Description.Use`, `Reference.Description.Bridging`: the uses of a definite
  description and the bridging relations, each with the strength it calls for.
* `Reference.ArticleType`, `Reference.MarkingStrategy`: the three-cell article typology of
  Patel-Grosz and Grosz and the four-cell one of Jenks with Moroney's unmarked cell, and the
  coarsening `MarkingStrategy.articleType`.

## References

* [aissen-2003]
* [comrie-1989]
* [farkas-brasoveanu-2020]
* [haspelmath-2021]
* [schwarz-2009]
* [schwarz-2013]
* [hawkins-1978]
* [heim-1982]
* [jenks-2018]
* [moroney-2021]
* [patel-grosz-grosz-2017]
-/

@[expose] public section

namespace Reference

/-- A nominal is definite or indefinite. A definite retrieves a unique or familiar referent, an
indefinite introduces a new one ([heim-1982]). -/
inductive Definiteness where
  | indefinite
  | definite
  deriving DecidableEq, Repr, Fintype

namespace Definiteness

/-- The rank on the definiteness scale, higher for definite. -/
def rank : Definiteness → ℕ
  | .indefinite => 0
  | .definite   => 1

/-- The order `indefinite < definite` is the definiteness scale of differential argument marking
in its binary form ([aissen-2003]). -/
instance : LinearOrder Definiteness := LinearOrder.lift' rank (by decide)

/-- `⊥ = indefinite`, `⊤ = definite`. -/
instance : BoundedOrder Definiteness where
  top := .definite
  le_top := by decide
  bot := .indefinite
  bot_le := by decide

instance : IsSimpleOrder Definiteness where
  exists_pair_ne := ⟨.indefinite, .definite, by decide⟩
  eq_bot_or_eq_top := by decide

end Definiteness

/-- The degree of definiteness of a nominal ranks a definite above a specific indefinite above a
non-specific indefinite. A specific indefinite is one of whichever kind of specificity a
language's marking tracks. -/
inductive DefinitenessDegree where
  | nonSpecific
  | specific
  | definite
  deriving DecidableEq, Repr, Fintype

namespace DefinitenessDegree

/-- The rank on the continuum, 0 for a non-specific indefinite up to 2 for a definite. -/
def rank : DefinitenessDegree → ℕ
  | .nonSpecific => 0
  | .specific => 1
  | .definite => 2

instance : LinearOrder DefinitenessDegree := LinearOrder.lift' rank (by decide)

/-- A degree is definite at the top of the continuum and indefinite below it. -/
def definiteness (d : DefinitenessDegree) : Definiteness :=
  if .definite ≤ d then .definite else .indefinite

theorem definiteness_monotone : Monotone definiteness := by
  intro a b; revert a b; decide

end DefinitenessDegree

namespace Description

/-- The strength of a definite article ([schwarz-2009]): the weak article presupposes
uniqueness, the strong article familiarity. -/
inductive Strength where
  | uniqueness
  | familiarity
  deriving DecidableEq, Repr

/-- The kind of a nominal description is a constructor of `Description` with its payload erased,
or the indefinite, which denotes no partial individual but which an inventory may realize. -/
inductive Kind where
  | bare
  | indefinite
  | unique
  | anaphoric
  | demonstrative
  | possessive
  deriving DecidableEq, Repr

/-- The weak article realizes the unique description and the strong article the anaphoric
one. -/
def Strength.toKind : Strength → Kind
  | .uniqueness  => .unique
  | .familiarity => .anaphoric

/-- The strength a kind of description presupposes, where it is definite. -/
def Kind.strength : Kind → Option Strength
  | .bare | .indefinite         => none
  | .unique | .possessive       => some .uniqueness
  | .anaphoric | .demonstrative => some .familiarity

@[simp] theorem Strength.strength_toKind (p : Strength) : p.toKind.strength = some p := by
  cases p <;> rfl

/-- A bridging relation is part–whole, as from a fridge to its crisper, or relational, as from a
play to its author ([schwarz-2013]). -/
inductive Bridging where
  | partWhole
  | relational
  deriving DecidableEq, Repr

/-- Part–whole bridging calls for the weak article and relational bridging for the strong one
([schwarz-2009]). -/
def Bridging.strength : Bridging → Strength
  | .partWhole  => .uniqueness
  | .relational => .familiarity

/-- A use of a definite description is one of [hawkins-1978]'s, with bridging split by its relation,
or the donkey use of [schwarz-2009]. -/
inductive Use where
  | anaphoric
  | immediateSituation
  | largerSituation
  | bridging (b : Bridging)
  | donkey
  deriving DecidableEq, Repr

/-- The anaphoric and donkey uses call for the strong article, the situational uses for the weak
one, and a bridging use for the strength of its relation ([schwarz-2009], [schwarz-2013]). -/
def Use.strength : Use → Strength
  | .anaphoric | .donkey => .familiarity
  | .immediateSituation | .largerSituation => .uniqueness
  | .bridging b => b.strength

end Description

/-- An article system has no article, a weak article only, or weak and strong articles
([patel-grosz-grosz-2017]). -/
inductive ArticleType where
  | articleless
  | weakOnly
  | weakAndStrong
  deriving DecidableEq, Repr

/-- The definiteness-marking strategies of [jenks-2018], with [moroney-2021]'s unmarked cell:
one form marks both strengths, two forms mark them apart, only the anaphoric strength is
obligatorily marked, or neither is. A language's cell is derived from its determiner inventory
by `Determiner.Inventory.markingStrategy`. -/
inductive MarkingStrategy where
  | generallyMarked
  | bipartite
  | markedAnaphoric
  | unmarked
  deriving DecidableEq, Repr

/-- The article system of a marking strategy, which collapses the generally-marked and
marked-anaphoric cells to a single weak article. -/
def MarkingStrategy.articleType : MarkingStrategy → ArticleType
  | .generallyMarked | .markedAnaphoric => .weakOnly
  | .bipartite => .weakAndStrong
  | .unmarked  => .articleless

end Reference
