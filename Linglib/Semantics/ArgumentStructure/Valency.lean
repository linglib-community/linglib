module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Valency

The two core-argument positions of a verbal clause — the internal
argument (complement of the lexical core) and the external argument
(specifier of Voice, after Kratzer) — and **valency**: the set of
positions an argument-introducing locus (root, functional head,
derivational operator) contributes. Valencies form the Boolean lattice
`Finset ArgPosition`; introducers compose by `∪`, and valency-changing
operations, after Creissels, are maps on the lattice.

Coon's division of labor is stated as predicates over valencies
(`IsRootValency`, `IsVoiceValency`), not baked into a type: roots
introduce at most the internal argument, v ~ Voice at most the
external.

`role` reads the comparative role (`ArgumentRole`) of a position off the clause's valency: a lone
position, internal or external alike, is S, and the two positions of a transitive clause are A
and P. The roles are relational, so `label`, the set of roles a valency's arguments bear, is not
monotone: adding a co-argument turns S into A or P, which is why alignment typology needs S as a
concept of its own.

## Main declarations

* `ArgPosition`, `Valency`
* `Valency.IsRootValency`, `IsVoiceValency`, `IsTransitive`
* `Valency.role`, `Valency.label`: the comparative role of a position, and the roles of a valency

## References

* [coon-2019]
* [creissels-2024]
* [kratzer-1996]
-/

@[expose] public section

namespace ArgumentStructure


/-- A core-argument position of the verbal clause: the internal argument
    (complement of the lexical core) or the external argument (specifier
    of Voice, [kratzer-1996]). -/
inductive ArgPosition where
  | internal
  | external
  deriving DecidableEq, Fintype, Repr

/-- The set of core-argument positions an argument-introducing locus
    contributes; inherits the Boolean lattice of finite sets, and
    introducers compose by `∪`. -/
abbrev Valency := Finset ArgPosition

/-- `Finset` carries no `Repr`; over the two-element position universe the
    four valencies render literally. -/
instance : Repr Valency :=
  ⟨fun v _ ↦
    if v = {.internal, .external} then "{internal, external}"
    else if v = ({.internal} : Valency) then "{internal}"
    else if v = ({.external} : Valency) then "{external}"
    else "∅"⟩

namespace Valency

/-- [coon-2019]'s division of labor, root half: roots introduce at most
    the internal argument. A thesis about the lexicon, stated as a
    predicate rather than a type restriction. -/
def IsRootValency (v : Valency) : Prop := v ≤ ({.internal} : Valency)

instance (v : Valency) : Decidable v.IsRootValency :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- [coon-2019]'s division of labor, functional half: v ~ Voice heads
    introduce at most the external argument. -/
def IsVoiceValency (v : Valency) : Prop := v ≤ ({.external} : Valency)

instance (v : Valency) : Decidable v.IsVoiceValency :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A transitive clause realizes both core positions. -/
def IsTransitive (v : Valency) : Prop := v = {.internal, .external}

instance (v : Valency) : Decidable v.IsTransitive :=
  inferInstanceAs (Decidable (_ = _))

/-- Root and Voice valencies are disjoint, so under the division of
    labor the two loci partition a transitive clause's core positions. -/
theorem isRootValency_inter_isVoiceValency :
    ∀ v v' : Valency, v.IsRootValency → v'.IsVoiceValency →
      v ∩ v' = ∅ := by decide

/-- A root valency and a Voice valency compose to a transitive clause
    iff each introduces its position. -/
theorem isTransitive_union_iff :
    ∀ v v' : Valency, v.IsRootValency → v'.IsVoiceValency →
      ((v ∪ v').IsTransitive ↔
        v = {.internal} ∧ v' = {.external}) := by decide

/-! ### Comparative roles -/

/-- The comparative role of position `p` in a clause realizing `v`. A lone position, internal or
external alike, is the S of an intransitive clause; in a transitive clause the external position
is A and the internal one P. A position outside `v` has no role. The clause, not the predicate,
takes the classification. -/
def role (v : Valency) (p : ArgPosition) : Option ArgumentRole :=
  if p ∉ v then none
  else if v.IsTransitive then
    match p with
    | .internal => some .P
    | .external => some .A
  else some .S

/-- The roles a valency's arguments bear. -/
def label (v : Valency) : Finset ArgumentRole := {r | ∃ p, v.role p = some r}

/-- S surfaces exactly for the two singleton valencies — the
    unaccusative (internal) and unergative (external) S, which
    split-intransitive systems mark differently. -/
theorem s_mem_label_iff :
    ∀ v : Valency, .S ∈ label v ↔
      v = {.internal} ∨ v = {.external} := by decide

/-- Labels are relational, not positional, since adding a co-argument relabels S to A or P, so
`label` is not monotone in the lattice. -/
theorem label_not_monotone : ¬ Monotone label := by decide

end Valency

end ArgumentStructure
