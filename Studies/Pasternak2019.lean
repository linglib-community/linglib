module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Mereology

/-!
# Pasternak (2019): A Lot of Hatred and a Ton of Desire

Pasternak analyzes intensity as a monotonic measure function on mental states. *Ann hates Bill more
than Matt hates Jeff* is a verbal comparative of the same shape as Wellwood's *more snow* and *ran
more*: the comparative maximizes the intensity measure over the verb's eventualities with the given
experiencers and themes, and presupposes, as Schwarzschild's monotonicity requires of every such
construction, that the measure is monotonic on the salient part-whole relation among the verb's
states. The comparative entails the matrix positive but not the than-clause positive, which a zero
degree in the than-clause set secures, and under the presupposition it compares the maximal states.
Mental-state predicates are homogeneous, a state of Ann hating Bill having only such states as
parts.

## Main definitions

* `intensityComparative`: the intensity comparative.
* `Monotonic`: the monotonicity presupposition.
* `intensityComparativeZero`: the comparative with a zero degree in the than-clause set.

## Main results

* `intensityComparative_of_greatest`: under the presupposition the comparative compares the maximal
  states.
* `intensityComparativeZero_of_none`: the than-clause positive is not entailed.
* `div_iff`: mental-state homogeneity.

## Implementation notes

The reduction of a comparative to its greatest witnesses under a monotone measure is
`Degree.maxComparative_gt_iff_of_isGreatest`; the zero-degree amendment to the than-clause set is
the paper's own (`thanDegreesZero`); the part-whole order on eventualities is a partial order on the
event domain. The two-dimensional state ontology that grounds the salient part-whole relation, the
Mandarin data, and the desire predicates are not formalized.

## TODO

* Mandarin *duō* / *hěn duō (de)*, which needs Fragment entries.
* The two-dimensional state ontology with its vertical axis and the fineness ordering.
* The desire predicates *want*, *wish*, and *regret* over point-states.

## References

* [pasternak-2019]
* [schwarzschild-2006]
* [wellwood-2015]
-/

@[expose] public section

namespace Pasternak2019

open Degree
open ArgumentStructure (ThematicFrame)

/-- A mental-state verb has a predicate on eventualities and an intensity measure, with thematic
roles assigned by a `ThematicFrame` at use sites. -/
structure MentalStateVerb (E D : Type*) where
  /-- The verb's predicate on eventualities. -/
  predicate : E → Prop
  /-- The intensity measure. -/
  μint : E → D

variable {Entity E D : Type*} [Preorder D] (v : MentalStateVerb E D)
  (frame : ThematicFrame Entity E)

/-- `themed α x e` holds when `e` is an eventuality of the verb with experiencer `α` and theme
`x`. -/
def themed (α x : Entity) (e : E) : Prop :=
  frame.experiencer α e ∧ v.predicate e ∧ frame.theme x e

/-- *α V x at degree d* holds of a themed eventuality of the verb with intensity at least `d`. -/
def MentalStateVerb.holdsAtDegree (α x : Entity) (d : D) (e : E) : Prop :=
  themed v frame α x e ∧ d ≤ v.μint e

/-- The intensity comparative *α V x more than β V y* is `Degree.MaxComparative .gt` with the two
sides differing in experiencer and theme, measured by the intensity measure (56a). -/
def intensityComparative (α β x y : Entity) : Prop :=
  MaxComparative .gt (themed v frame α x) (themed v frame β y) v.μint

/-- `statesOf x` is the set of states of the verb with theme `x`, whatever their experiencer, the
domain of the monotonicity presupposition. -/
def statesOf (x : Entity) : Set E := {e | v.predicate e ∧ frame.theme x e}

/-- The monotonicity presupposition (56b), the paper's (4) on the salient part-whole relation,
says that a proper part of a state of the verb with theme `x` is strictly less intense. -/
def Monotonic [PartialOrder E] (x : Entity) : Prop := StrictMonoOn v.μint (statesOf v frame x)

variable {v frame} {α β x y : Entity}

theorem intensityComparative.exists_matrix (h : intensityComparative v frame α β x y) :
    ∃ e, themed v frame α x e :=
  let ⟨_, _, e, he, _⟩ := h; ⟨e, he⟩

theorem intensityComparative_unique {ea eb : E} (ha : themed v frame α x ea)
    (ha' : ∀ e, themed v frame α x e → e = ea) (hb : themed v frame β y eb)
    (hb' : ∀ e, themed v frame β y e → e = eb) :
    intensityComparative v frame α β x y ↔ v.μint eb < v.μint ea :=
  maxComparative_iff_of_unique ha ha' hb hb'

/-- Under the presupposition on both sides the comparative compares the maximal states, so with
`ea` Ann's state of hating Bill and `eb` Matt's of hating Jeff the sentence holds iff `ea` is
the more intense. -/
theorem intensityComparative_of_greatest [PartialOrder E] {ea eb : E}
    (hx : Monotonic v frame x) (hy : Monotonic v frame y)
    (ha : IsGreatest {e | themed v frame α x e} ea)
    (hb : IsGreatest {e | themed v frame β y e} eb) :
    intensityComparative v frame α β x y ↔ v.μint eb < v.μint ea :=
  maxComparative_gt_iff_of_isGreatest ha (hx.monotoneOn.mono fun _ he ↦ ⟨he.2.1, he.2.2⟩) hb
    (hy.monotoneOn.mono fun _ he ↦ ⟨he.2.1, he.2.2⟩)

section Zero

variable [Zero D] (v frame)

/-- `thanDegreesZero` adds the scale's zero degree to the than-clause degree set, whose maximum
then exists even
without a than-clause witness (62). -/
def thanDegreesZero (Pthan : E → Prop) : Set D :=
  insert 0 (lowerClosure (v.μint '' {e | Pthan e}))

/-- `intensityComparativeZero` is the intensity comparative with the zero degree added to the
than-clause set (62). -/
def intensityComparativeZero (α β x y : Entity) : Prop :=
  ∃ δ, IsGreatest (thanDegreesZero v (themed v frame β y)) δ ∧
    ∃ e, themed v frame α x e ∧ δ < v.μint e

variable {v frame}

/-- The than-clause positive is not entailed (63), as the comparative holds when no `β`-eventuality
has positive intensity. -/
theorem intensityComparativeZero_of_none {e : E} (he : themed v frame α x e)
    (hpos : 0 < v.μint e) (hβ : ∀ e', themed v frame β y e' → v.μint e' ≤ 0) :
    intensityComparativeZero v frame α β x y :=
  ⟨0, ⟨Set.mem_insert _ _, fun _ hd ↦ (Set.mem_insert_iff.1 hd).elim le_of_eq
    fun ⟨_, ⟨e', he', he'd⟩, hle⟩ ↦ hle.trans (he'd ▸ hβ e' he')⟩, e, he, hpos⟩

end Zero

/-- Mental state homogeneity (55) says that a predicate closed under parts holds of `e` iff it
holds of every part of `e`. -/
theorem div_iff {α : Type*} [Preorder α] {P : α → Prop} (h : Mereology.DIV P) (e : α) :
    P e ↔ ∀ e' ≤ e, P e' :=
  ⟨fun he _ hle ↦ h hle he, fun hall ↦ hall e le_rfl⟩

end Pasternak2019
