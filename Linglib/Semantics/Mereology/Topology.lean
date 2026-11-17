module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Linglib.Semantics.Mereology.Classical
public import Linglib.Semantics.Mereology.Individuation

/-!
# Mereotopology

Mereotopology adds to parthood a relation of connection, reflexive, symmetric and monotone along
parthood, of which [overlap is the least](##Mereology.IsConnection.of_overlap). Connection
singles out the self-connected individuals, which come in one piece:
[any two individuals that sum to one are connected](##Mereology.isSelfConnected_iff). Grimm's
clusters, a pile of sand or a swarm of ants, are sums of entities of a kind transitively
connected through others of the kind, which is to lie in one component of the kind's connection
graph. [The clusters of a component are cumulative](##Mereology.cum_isClusterIn), and a sum of
self-connected individuals transitively connected among themselves
[is self-connected](##Mereology.IsSelfConnected.of_isLUB).

## Implementation notes

Connection is reflexive on non-null individuals only, as `Overlap` relates non-null parts: were
a null individual connected to itself, monotonicity would connect everything. For the same
reason the two individuals that self-connection quantifies over are non-null; a null one would
make every self-connected individual connected to it and so to everything. On a carrier without
a null individual, such as a classical mereology, both are the definitions of the sources.
Monotonicity is stated in the second argument, which by symmetry is the axiom that whatever is
connected to a part is connected to the whole. Self-connection keeps Grimm's overlap
formulation, which over a generalized Boolean algebra is the formulation by sums. The
relation a cluster is taken under need not be a connection relation, as external connection
is not reflexive. The chain that connects two members of a cluster may run through
`P`-entities outside the cluster, since Grimm's definition quantifies over the set the chain
runs through, so a cluster of self-connected entities need not be self-connected.

## TODO

Internal parts, the interior as their sum, strong self-connection, its maximal form relative
to a property, and the strong and external connection relations are not formalized.

## References

* [casati-varzi-1999], [grimm-2012], [grimm-docekal-2021]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

/-! ### Connection -/

section Connection

variable [PartialOrder α]

/-- A connection relation ([grimm-2012] T1–T3) is reflexive on non-null individuals, symmetric,
and monotone along parthood. -/
structure IsConnection (C : α → α → Prop) : Prop where
  refl ⦃x : α⦄ : ¬ IsBot x → C x x
  symm ⦃x y : α⦄ : C x y → C y x
  mono (z : α) : Monotone (C z)

variable {C : α → α → Prop} {x y x' y' : α}

/-- Connection is monotone in both arguments. -/
theorem IsConnection.mono₂ (hC : IsConnection C) (hx : x ≤ x') (hy : y ≤ y') (h : C x y) :
    C x' y' :=
  hC.mono x' hy (hC.symm (hC.mono y hx (hC.symm h)))

/-- Parthood entails connection. -/
theorem IsConnection.of_le (hC : IsConnection C) (hx : ¬ IsBot x) (h : x ≤ y) : C x y :=
  hC.mono x h (hC.refl hx)

/-- Overlap entails connection ([grimm-2012] (8)). -/
theorem IsConnection.of_overlap (hC : IsConnection C) (h : Overlap x y) : C x y :=
  let ⟨_, hz, hzx, hzy⟩ := h
  hC.mono₂ hzx hzy (hC.refl hz)

/-- Overlap is a connection relation, by `IsConnection.of_overlap` the least one. -/
theorem isConnection_overlap : IsConnection (Overlap : α → α → Prop) where
  refl _ h := .refl h
  symm _ _ h := h.symm
  mono _ _ _ h ho := ho.mono le_rfl h

end Connection

/-! ### Transitive connection -/

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

/-! ### Self-connection -/

section SelfConnected

variable [PartialOrder α] {C : α → α → Prop} {x : α}

variable (C) in
/-- An individual is self-connected ([grimm-2012] D24) if any two non-null individuals that
between them overlap exactly what it overlaps are connected. -/
def IsSelfConnected (x : α) : Prop :=
  ∀ y z, ¬ IsBot y → ¬ IsBot z → (∀ w, Overlap w x ↔ Overlap w y ∨ Overlap w z) → C y z

/-- An atom is self-connected, as two individuals that cover it both contain it. -/
theorem Atom.isSelfConnected (hC : IsConnection C) (hx : Atom x) : IsSelfConnected C x := by
  intro y z hy hz h
  have key {u : α} : Overlap u x → x ≤ u := fun ⟨p, hp, hpu, hpx⟩ ↦ hx.eq hpx hp ▸ hpu
  exact hC.of_overlap ⟨x, hx.not_isBot, key ((h y).2 (.inl (.refl hy))),
    key ((h z).2 (.inr (.refl hz)))⟩

section Sum

variable [StronglySupplemented α] [HasProducts α]

/-- The sum of self-connected individuals any two of which are transitively connected through
others among them is self-connected, as a pile of touching grains comes in one piece. -/
theorem IsSelfConnected.of_isLUB (hC : IsConnection C) {Z : Set α}
    (hZ : ∀ z ∈ Z, IsSelfConnected C z)
    (hR : ∀ a ∈ Z, ∀ b ∈ Z, (connectionGraph C (· ∈ Z)).Reachable a b) (hx : IsLUB Z x) :
    IsSelfConnected C x := by
  intro u v hu hv H
  by_contra hCuv
  have hdich : ∀ z ∈ Z, z ≤ u ∨ z ≤ v := fun z hz ↦ by
    by_contra! h
    have cover (p : α) (hp : p ≤ z) (hp0 : ¬ IsBot p) : Overlap p u ∨ Overlap p v :=
      (H p).1 (.of_le hp0 (hp.trans (hx.1 hz)))
    have hzu : Overlap z u := by
      by_contra hn
      exact h.2 (le_of_forall_overlap fun p hp hp0 ↦
        (cover p hp hp0).resolve_left fun ho ↦ hn (ho.mono hp le_rfl))
    have hzv : Overlap z v := by
      by_contra hn
      exact h.1 (le_of_forall_overlap fun p hp hp0 ↦
        (cover p hp hp0).resolve_right fun ho ↦ hn (ho.mono hp le_rfl))
    obtain ⟨a, ha0, ha⟩ := hzu.exists_isGLB
    obtain ⟨b, hb0, hb⟩ := hzv.exists_isGLB
    have haz : a ≤ z := ha.1 (.inl rfl)
    have hbz : b ≤ z := hb.1 (.inl rfl)
    refine hCuv (hC.mono₂ (ha.1 (.inr rfl)) (hb.1 (.inr rfl)) (hZ z hz a b ha0 hb0 fun w ↦
      ⟨fun ⟨p, hp0, hpw, hpz⟩ ↦ ?_, fun h ↦ h.elim (·.mono le_rfl haz) (·.mono le_rfl hbz)⟩))
    rcases cover p hpz hp0 with ⟨q, hq0, hqp, hqu⟩ | ⟨q, hq0, hqp, hqv⟩
    · exact .inl ⟨q, hq0, hqp.trans hpw,
        ha.2 (by rintro _ (rfl | rfl); exacts [hqp.trans hpz, hqu])⟩
    · exact .inr ⟨q, hq0, hqp.trans hpw,
        hb.2 (by rintro _ (rfl | rfl); exacts [hqp.trans hpz, hqv])⟩
  have hov (h : x ≤ u ∨ x ≤ v) : Overlap u v := by
    rcases h with h | h
    · obtain ⟨p, hp0, hpv, hpx⟩ := (H v).2 (.inr (.refl hv))
      exact ⟨p, hp0, hpx.trans h, hpv⟩
    · obtain ⟨p, hp0, hpu, hpx⟩ := (H u).2 (.inl (.refl hu))
      exact ⟨p, hp0, hpu, hpx.trans h⟩
  obtain ⟨a, haZ, hav⟩ : ∃ a ∈ Z, ¬ a ≤ v := by
    by_contra! h
    exact hCuv (hC.of_overlap (hov (.inr (hx.2 h))))
  obtain ⟨b, hbZ, hbu⟩ : ∃ b ∈ Z, ¬ b ≤ u := by
    by_contra! h
    exact hCuv (hC.of_overlap (hov (.inl (hx.2 h))))
  refine hbu ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (hR a haZ b hbZ) |>.rec
    ((hdich a haZ).resolve_right hav) fun {c d} _ hcd ih ↦ ?_)
  obtain ⟨hdZ, hC'⟩ : d ∈ Z ∧ C c d := by
    rcases hcd.2 with ⟨-, hd, h⟩ | ⟨hd, -, h⟩
    exacts [⟨hd, h⟩, ⟨hd, hC.symm h⟩]
  exact (hdich d hdZ).resolve_right fun hdv ↦ hCuv (hC.mono₂ ih hdv hC')
end Sum

end SelfConnected

/-- The sum of two connected self-connected individuals is self-connected. -/
theorem IsSelfConnected.sup [SemilatticeSup α] [StronglySupplemented α] [HasProducts α]
    {C : α → α → Prop} {x y : α} (hC : IsConnection C) (hx : IsSelfConnected C x)
    (hy : IsSelfConnected C y) (hxy : C x y) : IsSelfConnected C (x ⊔ y) := by
  have h : (connectionGraph C (· ∈ ({x, y} : Set α))).Reachable x y :=
    connectionGraph_reachable (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) hxy
  refine .of_isLUB hC (Z := {x, y}) ?_ ?_ isLUB_pair
  · rintro z (rfl | rfl) <;> assumption
  · rintro a (rfl | rfl) b (rfl | rfl)
    exacts [.refl _, h, h.symm, .refl _]

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] {C : α → α → Prop} {x y z : α}

private theorem eq_of_forall_disjoint_iff (h : ∀ w, Disjoint w x ↔ Disjoint w y) : x = y :=
  le_antisymm
    (sdiff_eq_bot_iff.1 (((h _).2 disjoint_sdiff_self_left).eq_bot_of_le sdiff_le))
    (sdiff_eq_bot_iff.1 (((h _).1 disjoint_sdiff_self_left).eq_bot_of_le sdiff_le))

/-- Two individuals between them overlap exactly what `x` overlaps iff they sum to `x`. -/
theorem forall_overlap_iff_or : (∀ w, Overlap w x ↔ Overlap w y ∨ Overlap w z) ↔ y ⊔ z = x := by
  simp only [overlap_iff_not_disjoint, ← not_and_or, not_iff_not, ← disjoint_sup_right]
  exact ⟨fun h ↦ (eq_of_forall_disjoint_iff h).symm, fun h _ ↦ h ▸ Iff.rfl⟩

/-- An individual is self-connected iff any two non-null individuals that sum to it are
connected. -/
theorem isSelfConnected_iff :
    IsSelfConnected C x ↔ ∀ y z, y ≠ ⊥ → z ≠ ⊥ → y ⊔ z = x → C y z := by
  simp only [IsSelfConnected, isBot_iff_eq_bot, forall_overlap_iff_or]

end GeneralizedBooleanAlgebra

/-! ### Clusters -/

section Cluster

variable [PartialOrder α] (C : α → α → Prop) (P : α → Prop)

/-- A cluster of `P`-entities inside the connected component `c` is the sum of a nonempty set of
`P`-entities of `c`. -/
def IsClusterIn (c : (connectionGraph C P).ConnectedComponent) (x : α) : Prop :=
  ∃ Z : Set α, Z.Nonempty ∧
    (∀ z ∈ Z, P z ∧ (connectionGraph C P).connectedComponentMk z = c) ∧ IsLUB Z x

/-- A cluster of `P`-entities ([grimm-2012] D33) is a cluster inside some connected component. -/
def IsCluster (x : α) : Prop := ∃ c, IsClusterIn C P c x

/-- A maximal cluster ([grimm-docekal-2021]) contains every cluster that overlaps it. -/
def IsMaxCluster (x : α) : Prop :=
  IsCluster C P x ∧ ∀ y, IsCluster C P y → Overlap y x → y ≤ x

variable {C P}

/-- A cluster is the sum of a nonempty set of `P`-entities any two of which are transitively
connected. -/
theorem isCluster_iff {x : α} :
    IsCluster C P x ↔ ∃ Z : Set α, Z.Nonempty ∧ (∀ z ∈ Z, P z) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, (connectionGraph C P).Reachable z z') ∧ IsLUB Z x := by
  constructor
  · rintro ⟨c, Z, hne, hZ, hx⟩
    exact ⟨Z, hne, fun z hz ↦ (hZ z hz).1, fun z hz z' hz' ↦
      SimpleGraph.ConnectedComponent.exact ((hZ z hz).2.trans (hZ z' hz').2.symm), hx⟩
  · rintro ⟨Z, ⟨z₀, hz₀⟩, hP, hR, hx⟩
    exact ⟨_, Z, ⟨z₀, hz₀⟩,
      fun z hz ↦ ⟨hP z hz, SimpleGraph.ConnectedComponent.sound (hR z hz z₀ hz₀)⟩, hx⟩

/-- Maximal clusters do not overlap, since each would contain the other. -/
theorem disjointPred_isMaxCluster : DisjointPred Overlap {x | IsMaxCluster C P x} := by
  rintro ⟨x, hx, y, hy, hne, hov⟩
  exact hne (le_antisymm (hy.2 x hx.1 hov) (hx.2 y hy.1 hov.symm))

end Cluster

/-- The clusters of a connected component are cumulative. -/
theorem cum_isClusterIn [SemilatticeSup α] (C : α → α → Prop) (P : α → Prop)
    (c : (connectionGraph C P).ConnectedComponent) : CUM (IsClusterIn C P c) := by
  rintro x ⟨Z₁, h₁, hZ₁, hx⟩ y ⟨Z₂, -, hZ₂, hy⟩
  exact ⟨Z₁ ∪ Z₂, h₁.mono Set.subset_union_left, fun z hz ↦ hz.elim (hZ₁ z) (hZ₂ z),
    hx.union hy⟩

end Mereology
