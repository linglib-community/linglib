module

public import Linglib.Syntax.Spine.ExtendedProjection
public import Linglib.Syntax.Spine.Label
public import Mathlib.Tactic.DeriveFintype

/-!
# Grimshaw (2000): Locality and Extended Projection

[grimshaw-2000] takes a category label to be a pair of a categorial specification and a functional
value. The verb, inflection and the complementizer are verbal, with values 0, 1 and 2, and the
noun, the determiner and the preposition are nominal, with the same values. A phrase is an extended
projection of a head below it when the two share their categorial specification and the phrase has
the higher functional value. The clause, a complementizer over inflection over a verb, is then one
extended projection, and so is a preposition over a determiner over a noun. A head forms an
extended projection with its complement exactly when the two share their categorial specification
and the head has the higher value, so a lexical head never forms one with its complement. A
complementizer over inflection over a complementizer is no extended projection, and a
complementizer over a complementizer is one only if the functional value may stay the same. The
functional value of a head is its height in the clause or in the noun phrase.

## Implementation notes

* The paper defines projections on trees. Here a head and the heads of the complements below it
  form a spine, and an extended projection is `Spine.IsExtendedProjection` for the categorial
  specification and a ranking by functional value.
* The paper leaves open whether the functional value must increase from each head to the next or
  may stay the same. The results are stated for the strict ranking, for which no head above the
  lowest is lexical, as the paper's definition requires. With the ranking that lets the value stay
  the same, the two conditions of `Spine.IsExtendedProjection` also hold of a verb over a verb.

## TODO

The conditions on which heads take which complements and the generalized theta criterion concern
how one extended projection is embedded in another, and are not formalized.

## References

* [grimshaw-2000]
-/

@[expose] public section

namespace Grimshaw2000

/-- The categorial specifications of (1) and (2). -/
inductive Category
  | verbal
  | nominal
  deriving DecidableEq, Repr

/-- The heads of (1) and (2). -/
inductive Head
  | V
  | I
  | C
  | N
  | D
  | P
  deriving DecidableEq, Fintype, Repr

namespace Head

/-- (1), (2): the categorial specification of a head. -/
def category : Head → Category
  | V | I | C => .verbal
  | N | D | P => .nominal

/-- (1), (2): the functional value of a head. -/
def F : Head → ℕ
  | V | N => 0
  | I | D => 1
  | C | P => 2

end Head

open Head

/-- (5): the spine of a clause, the verb under inflection under the complementizer. -/
def clause : Spine Head := ⟨[V, I, C]⟩

/-- The spine of a noun phrase under a determiner and a preposition. -/
def nominal : Spine Head := ⟨[N, D, P]⟩

/-- The clause, and the noun phrase under a determiner and a preposition, are extended
projections. -/
theorem isExtendedProjection_clause_nominal :
    clause.IsExtendedProjection category (F · < F ·) ∧
      nominal.IsExtendedProjection category (F · < F ·) := by
  decide

/-- A head forms an extended projection with its complement exactly when the two share their
categorial specification and the head has the higher functional value. -/
theorem isExtendedProjection_pair_iff (x y : Head) :
    (⟨[x, y]⟩ : Spine Head).IsExtendedProjection category (F · < F ·) ↔
      x.category = y.category ∧ x.F < y.F :=
  Spine.isExtendedProjection_pair_iff

/-- A lexical head does not form an extended projection with its complement. -/
theorem not_isExtendedProjection_of_F_eq_zero {x y : Head} (hy : y.F = 0) :
    ¬ (⟨[x, y]⟩ : Spine Head).IsExtendedProjection category (F · < F ·) := fun h ↦ by
  have := ((isExtendedProjection_pair_iff x y).1 h).2
  omega

-- (6): the head and complement combinations that form extended projections
theorem isExtendedProjection_of_mem :
    ∀ x y, (x, y) ∈ [(I, C), (D, P), (V, I), (N, D), (V, C), (N, P)] →
      (⟨[x, y]⟩ : Spine Head).IsExtendedProjection category (F · < F ·) := by
  decide

/-- A complementizer over inflection over a complementizer over a verb is an extended projection
on neither ranking, and a complementizer over a complementizer is one only if the functional value
may stay the same. -/
theorem not_isExtendedProjection_recursion :
    ¬ (⟨[V, C, I, C]⟩ : Spine Head).IsExtendedProjection category (F · < F ·) ∧
      ¬ (⟨[V, C, I, C]⟩ : Spine Head).IsExtendedProjection category (F · ≤ F ·) ∧
      (⟨[C, C]⟩ : Spine Head).IsExtendedProjection category (F · ≤ F ·) ∧
      ¬ (⟨[C, C]⟩ : Spine Head).IsExtendedProjection category (F · < F ·) := by
  decide

-- with the ranking that lets the value stay the same, the two conditions hold of a verb over a
-- verb, which the clause (3d) that no node in between is lexical excludes
theorem isExtendedProjection_le_V_V :
    (⟨[V, V]⟩ : Spine Head).IsExtendedProjection category (F · ≤ F ·) := by
  decide

/-- The functional value of a head is its height in the clause or in the noun phrase. -/
theorem height_eq_F :
    (∀ x ∈ clause, clause.height x = x.F) ∧ ∀ x ∈ nominal, nominal.height x = x.F := by
  decide

end Grimshaw2000
