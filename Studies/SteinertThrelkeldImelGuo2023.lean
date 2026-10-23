module

public import Linglib.Core.Combinatorics.SimpleGraph.Prod
public import Linglib.Semantics.Modality.Universals
public import Linglib.Fragments.Washo.Modals
public import Linglib.Data.Examples.Bochnak2015a
public import Studies.MocnikAbramovitz2019
public import Linglib.Fragments.Javanese.Paciran.Modals
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Steinert-Threlkeld, Imel and Guo (2023): A semantic universal for modality

This file formalizes the Independence of Force and Flavor universal of
[steinert-threlkeld-imel-guo-2023], the substrate's `Modality.ForceFlavorIndependent`,
against the Single Axis of Variability universal of [nauze-2008] it replaces. The Washo verb
*-eʔ*, which [bochnak-2015a] finds specified for neither force nor flavor, varies on both axes
yet is a product, the hypothetical *mighst* is neither, and the singleton meanings of Paciran
Javanese ([vander-klok-2013a]) satisfy the universal trivially. The paper's equivalence of
independence with convexity for the grid betweenness of [chemla-buccola-dautriche-2019] is the
substrate's `forceFlavorIndependent_iff_pair_product_subset`.

Section 4.1 notes gaps in the uses of *-eʔ* that Bochnak elicits: bouletic necessity and weak
necessity but no bouletic possibility, and weak necessity with no other flavor
(`washoAttested_gaps`), so the attested uses are not a product. The paper still takes the
universal to hold of *-eʔ*, since nothing rules the missing pairs out and the analyses of
[bochnak-2015a] and [bochnak-2015b] leave force and flavor free (`washo_attested`).

The paper offers path-connectedness as a weaker fallback universal, defined by replacing the
"and" of independence with an "or" and glossed in a footnote as any two points being joined by a
path. The two readings come apart. Read as a path through the rook's graph on the force-flavor
grid, whose edges change one coordinate, the property follows from the "or" formulation
(`PathConnected.connected`), but the second modal of Table 1, given as satisfying
path-connectedness without independence, is connected in the grid and fails the "or"
formulation: its weak teleological and strong epistemic points share no corner
(`table1b_connected_not_pathConnected`).

The Koryak attitude verb *ivək* is the paper's other counterexample to Nauze's universal, with
the doxastic and assertive flavors of [mocnik-abramovitz-2019] on the flavor axis. Section 4.1
reads them as reporting all four combinations of the two forces and the two flavors, which is
what their lexical entry predicts (`ivek_forceFlavorIndependent`). Their footnote 10, however,
could not confirm an existential 'say', and without it the attested uses are not a product;
they satisfy only path-connectedness (`ivek_attested`).

## Implementation notes

The paper's space has two forces, weak and strong, and the flavors epistemic, deontic and
teleological; the library folds teleological into circumstantial. The doxastic and assertive
flavors of *ivək* lie outside that space, and the universal is stated for any types of forces
and flavors. So do the metaphysical and generic uses of *-eʔ*, which `washoAttested` leaves
out; the weak necessity of [bochnak-2015a] is the library's `ModalForce.weakNecessity`.

## References

* [steinert-threlkeld-imel-guo-2023]
* [nauze-2008]
* [chemla-buccola-dautriche-2019]
* [bochnak-2015a]
* [bochnak-2015b]
* [mocnik-abramovitz-2019]
* [vander-klok-2013a]
-/

@[expose] public section

namespace SteinertThrelkeldImelGuo2023

open Modality SimpleGraph

theorem washo_modalEq :
    ¬ SingleAxis Washo.modalEq.meaning ∧
      ForceFlavorIndependent Washo.modalEq.meaning := by
  decide

/-- `forceTable` maps the force label of a row of [bochnak-2015a] to its force. -/
def forceTable : List (String × ModalForce) :=
  [("possibility", .possibility), ("weak necessity", .weakNecessity), ("necessity", .necessity)]

/-- `flavorTable` maps the flavor label of a row of [bochnak-2015a] to its flavor, when the
flavor lies in the space. -/
def flavorTable : List (String × ModalFlavor) :=
  [("epistemic", .epistemic), ("deontic", .deontic), ("bouletic", .bouletic),
    ("circumstantial", .circumstantial)]

/-- `washoAttested` collects the pairs of the uses of *-eʔ* that [bochnak-2015a] elicits, in §3
and, with the prejacent negated, in §5. -/
def washoAttested : Finset ForceFlavor :=
  (Bochnak2015a.Examples.all.filterMap fun e ↦ (e.parse? "force" forceTable).bind
    fun fo ↦ (e.parse? "flavor" flavorTable).map (fo, ·)).toFinset

/-- The Washo uses of [bochnak-2015a] include both forces with epistemic and deontic flavor but no
bouletic possibility (Section 4.1). -/
theorem washoAttested_gaps :
    ({.necessity, .possibility} : Finset ModalForce) ×ˢ ({.epistemic, .deontic} : Finset _) ⊆
        washoAttested ∧
      (.possibility, .bouletic) ∉ washoAttested ∧
      {p ∈ washoAttested | p.force = .weakNecessity} = {(.weakNecessity, .bouletic)} := by
  decide

theorem washo_attested :
    ¬ SingleAxis washoAttested ∧ ¬ ForceFlavorIndependent washoAttested ∧
      washoAttested ⊂ Washo.modalEq.meaning := by
  decide

theorem ivek_forceFlavorIndependent :
    ForceFlavorIndependent MocnikAbramovitz2019.meaning ∧
      ¬ SingleAxis MocnikAbramovitz2019.meaning :=
  ⟨MocnikAbramovitz2019.meaning_eq ▸ forceFlavorIndependent_product _ _,
    MocnikAbramovitz2019.not_singleAxis_meaning⟩

/-- The pairs [mocnik-abramovitz-2019] attest for *ivək*, without the existential 'say' their
footnote 10 could not confirm, fail the universal and satisfy path-connectedness. -/
theorem ivek_attested :
    ¬ ForceFlavorIndependent MocnikAbramovitz2019.attested ∧
      PathConnected MocnikAbramovitz2019.attested := by
  decide

theorem javanese_singletons :
    ForceFlavorIndependent Javanese.Paciran.mesthi.meaning ∧
      ForceFlavorIndependent Javanese.Paciran.oleh.meaning ∧
      ForceFlavorIndependent Javanese.Paciran.iso.meaning :=
  ⟨.singleton _, .singleton _, .singleton _⟩

/-- The hypothetical *mighst* expresses epistemic possibility and deontic necessity only, which
the universal rules out; it is the third modal of Table 1. -/
def mighst : Finset ForceFlavor := {(.possibility, .epistemic), (.necessity, .deontic)}

theorem not_forceFlavorIndependent_mighst : ¬ ForceFlavorIndependent mighst := by decide

/-! ### Table 1 and the two readings of path-connectedness -/

/-- The first modal of Table 1 expresses both forces with the epistemic and teleological
flavors. -/
def table1a : Finset ForceFlavor :=
  {(.possibility, .epistemic), (.possibility, .circumstantial),
   (.necessity, .epistemic), (.necessity, .circumstantial)}

/-- The second modal of Table 1 expresses weak deontic and teleological and strong epistemic and
deontic. -/
def table1b : Finset ForceFlavor :=
  {(.possibility, .deontic), (.possibility, .circumstantial),
   (.necessity, .epistemic), (.necessity, .deontic)}

theorem table1a_forceFlavorIndependent :
    ForceFlavorIndependent table1a ∧ ¬ SingleAxis table1a := by
  decide

/-- `rookGraph` is the rook's graph on the force-flavor grid, in which pairs differing in exactly
one coordinate are adjacent. -/
abbrev rookGraph : SimpleGraph ForceFlavor := (⊤ : SimpleGraph ModalForce) □ ⊤

theorem reachable_of_fst_eq_or_snd_eq {m : Finset ForceFlavor} {p q : ForceFlavor} (hp : p ∈ m)
    (hq : q ∈ m) (h : p.1 = q.1 ∨ p.2 = q.2) :
    (rookGraph.induce ↑m).Reachable ⟨p, hp⟩ ⟨q, hq⟩ := by
  by_cases hpq : p = q
  · subst hpq; rfl
  refine Adj.reachable ?_
  rw [induce_adj, boxProd_adj, top_adj, top_adj]
  rcases h with h | h
  · exact Or.inr ⟨fun h₂ ↦ hpq (Prod.ext h h₂), h⟩
  · exact Or.inl ⟨fun h₁ ↦ hpq (Prod.ext h₁ h), h⟩

/-- A path-connected meaning induces a connected subgraph of the rook's graph, so the *or*
formulation implies the footnote's. -/
theorem PathConnected.connected {m : Finset ForceFlavor} (h : PathConnected m) (hm : m.Nonempty) :
    (rookGraph.induce ↑m).Connected := by
  have := (Finset.coe_nonempty.2 hm).to_subtype
  refine ⟨fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ ?_⟩
  rcases h p hp q hq with hc | hc
  · exact (reachable_of_fst_eq_or_snd_eq hp hc (Or.inl rfl)).trans
      (reachable_of_fst_eq_or_snd_eq hc hq (Or.inr rfl))
  · exact (reachable_of_fst_eq_or_snd_eq hp hc (Or.inr rfl)).trans
      (reachable_of_fst_eq_or_snd_eq hc hq (Or.inl rfl))

/-- The second modal of Table 1 fails independence and the "or" formulation of
path-connectedness, yet is connected in the rook's graph. -/
theorem table1b_connected_not_pathConnected :
    ¬ ForceFlavorIndependent table1b ∧ ¬ PathConnected table1b ∧
      (rookGraph.induce ↑table1b).Connected := by
  decide +kernel

theorem mighst_not_connected :
    ¬ PathConnected mighst ∧ ¬ (rookGraph.induce ↑mighst).Connected := by
  decide +kernel

end SteinertThrelkeldImelGuo2023
