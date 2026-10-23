module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Linglib.Semantics.Mereology

/-!
# Mereotopology

Mereotopology adds to parthood a relation of connection, which is reflexive, symmetric, and
monotone along parthood, so that parthood and overlap entail it. Casati and Varzi's ground
mereotopology, in the form Grimm gives it, uses connection to single out the self-connected
individuals, which come in one piece, and the clusters, sums of entities transitively connected
through others of their kind, such as a pile of sand or a swarm of locusts. Grimm lets aggregate
nouns denote clusters, under external connection for *sand* and proximate connection for *ants*.
Transitive connection is reachability in the graph of connection between the entities of a
predicate, so a cluster is the sum of finitely many of them inside one connected component, and
the clusters of a component are cumulative.

## Main definitions

* `IsConnection C`: the axioms of a connection relation.
* `SelfConnected C x`: self-connection.
* `connectionGraph C P`: connection between `P`-entities as a graph, whose reachability is
  transitive connection.
* `IsClusterIn C P c`, `IsCluster C P`, `IsMaxCluster C P`: clusters inside a connected
  component, clusters, and maximal clusters.

## Main results

* `IsConnection.of_le`, `IsConnection.of_overlap`: parthood and overlap entail connection.
* `isCluster_iff`: a cluster is the sum of a nonempty finite set of `P`-entities any two of which
  are transitively connected, Grimm's definition.
* `cum_isClusterIn`: the clusters of a connected component are cumulative.
* `disjointPred_isMaxCluster`: maximal clusters do not overlap.

## Implementation notes

Connection is reflexive on non-null individuals only, as `Overlap` relates non-null parts: were
a null individual connected to itself, monotonicity would connect everything. On a carrier
without a null individual, such as a classical mereology, the axioms are Casati and Varzi's.
Monotonicity is stated in the second argument, which by symmetry is the axiom that whatever is
connected to a part is connected to the whole. Self-connection keeps Grimm's overlap formulation.
Strong self-connection, its maximal form, and the strong and external connection relations
defined from it need an interior operator and are not formalized. The chain that connects two
members of a cluster may run through `P`-entities outside the cluster, since Grimm's definition
quantifies over the set the chain runs through.

## References

* [casati-varzi-1999], [grimm-2012]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

/-! ### Connection and self-connection -/

section Connection

variable [PartialOrder α]

/-- A connection relation ([grimm-2012] T1–T3) is reflexive on non-null individuals, symmetric,
and monotone along parthood. -/
structure IsConnection (C : α → α → Prop) : Prop where
  refl ⦃x : α⦄ : ¬ IsBot x → C x x
  symm ⦃x y : α⦄ : C x y → C y x
  mono (z : α) : Monotone (C z)

variable {C : α → α → Prop} {x y : α}

theorem IsConnection.of_le (hC : IsConnection C) (hx : ¬ IsBot x) (h : x ≤ y) : C x y :=
  hC.mono x h (hC.refl hx)

/-- Overlap entails connection ([grimm-2012] (8)). -/
theorem IsConnection.of_overlap (hC : IsConnection C) (h : Overlap x y) : C x y :=
  let ⟨_, hz, hzx, hzy⟩ := h
  hC.symm (hC.mono y hzx (hC.symm (hC.of_le hz hzy)))

variable (C) in
/-- An individual is self-connected ([grimm-2012] D24) if any two individuals that between them
overlap exactly what it overlaps are connected. -/
def SelfConnected (x : α) : Prop :=
  ∀ y z, (∀ w, Overlap w x ↔ Overlap w y ∨ Overlap w z) → C y z

end Connection

/-! ### Clusters -/

/-- In the connection graph of `P`, two distinct `P`-entities are adjacent when they are
connected. Its reachability is transitive connection ([grimm-2012] D32), a chain of `P`-entities
each connected to the next. -/
def connectionGraph (C : α → α → Prop) (P : α → Prop) : SimpleGraph α :=
  SimpleGraph.fromRel fun a b ↦ P a ∧ P b ∧ C a b

theorem connectionGraph_reachable {C : α → α → Prop} {P : α → Prop} {a b : α} (ha : P a)
    (hb : P b) (h : C a b) : (connectionGraph C P).Reachable a b := by
  by_cases hab : a = b
  · exact hab ▸ .refl a
  · exact SimpleGraph.Adj.reachable ⟨hab, .inl ⟨ha, hb, h⟩⟩

section Cluster

variable [PartialOrder α] (C : α → α → Prop) (P : α → Prop)

/-- A cluster of `P`-entities inside the connected component `c` is the sum of a nonempty finite
set of `P`-entities of `c`. -/
def IsClusterIn (c : (connectionGraph C P).ConnectedComponent) (x : α) : Prop :=
  ∃ Z : Finset α, Z.Nonempty ∧
    (∀ z ∈ Z, P z ∧ (connectionGraph C P).connectedComponentMk z = c) ∧ IsLUB (Z : Set α) x

/-- A cluster of `P`-entities ([grimm-2012] D33) is a cluster inside some connected component. -/
def IsCluster (x : α) : Prop := ∃ c, IsClusterIn C P c x

/-- A maximal cluster contains every cluster that overlaps it. -/
def IsMaxCluster (x : α) : Prop :=
  IsCluster C P x ∧ ∀ y, IsCluster C P y → Overlap y x → y ≤ x

variable {C P}

theorem isCluster_iff {x : α} :
    IsCluster C P x ↔ ∃ Z : Finset α, Z.Nonempty ∧ (∀ z ∈ Z, P z) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, (connectionGraph C P).Reachable z z') ∧ IsLUB (Z : Set α) x := by
  constructor
  · rintro ⟨c, Z, hne, hZ, hx⟩
    exact ⟨Z, hne, fun z hz ↦ (hZ z hz).1, fun z hz z' hz' ↦
      SimpleGraph.ConnectedComponent.exact ((hZ z hz).2.trans (hZ z' hz').2.symm), hx⟩
  · rintro ⟨Z, ⟨z₀, hz₀⟩, hP, hR, hx⟩
    exact ⟨_, Z, ⟨z₀, hz₀⟩,
      fun z hz ↦ ⟨hP z hz, SimpleGraph.ConnectedComponent.sound (hR z hz z₀ hz₀)⟩, hx⟩

theorem disjointPred_isMaxCluster : DisjointPred Overlap {x | IsMaxCluster C P x} := by
  rintro ⟨x, hx, y, hy, hne, hov⟩
  exact hne (le_antisymm (hy.2 x hx.1 hov) (hx.2 y hy.1 hov.symm))

end Cluster

theorem cum_isClusterIn [SemilatticeSup α] (C : α → α → Prop) (P : α → Prop)
    (c : (connectionGraph C P).ConnectedComponent) : CUM (IsClusterIn C P c) := by
  classical
  rintro x ⟨Z₁, h₁, hZ₁, hx⟩ y ⟨Z₂, -, hZ₂, hy⟩
  refine ⟨Z₁ ∪ Z₂, h₁.mono Finset.subset_union_left, fun z hz ↦ ?_, ?_⟩
  · rcases Finset.mem_union.1 hz with hz | hz
    exacts [hZ₁ z hz, hZ₂ z hz]
  · rw [Finset.coe_union]
    exact hx.union hy

end Mereology
