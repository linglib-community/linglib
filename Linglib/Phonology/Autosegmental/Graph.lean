/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Sort
public import Mathlib.SetTheory.Cardinal.Finite
public import Linglib.Phonology.Autosegmental.OCP

/-!
# Autosegmental representations as labeled mixed graphs

Jardine writes an autosegmental representation as a labeled mixed graph `⟨V, E, A, ℓ⟩`: nodes,
undirected association edges, directed arcs ordering each string, and a labeling, and the
well-formedness axioms of his dissertation (§4.2) carve the representations out of these graphs.
`AR.toGraph` reads a representation as such a graph, with the precedence order of each tier as
its arcs. The reading satisfies Axioms 1–3, it is injective up to isomorphism, and every finite
graph satisfying Axioms 1–3 is isomorphic to one; on it, Axioms 5 and 6 are the No-Crossing
Constraint and the OCP of the representation.

## Main definitions

* `Graph S`, `Graph.Iso`: labeled mixed graphs and their isomorphisms.
* `IsTierOrdered`, `NoInternalAssoc`, `IsSaturated`, `NoCrossing`, `IsOCPClean`: the
  well-formedness axioms.
* `AR.toGraph`: the graph a representation denotes; `AR.ofGraph`: the representation of a finite
  graph satisfying Axioms 1–3.

## Main results

* `AR.nonempty_iso_toGraph_iff`: representations with isomorphic graphs are equal.
* `AR.ofGraphIso`: a finite graph satisfying Axioms 1–3 is the graph of its representation.
* `AR.noCrossing_toGraph_iff`, `AR.isOCPClean_toGraph_iff`: Axioms 5 and 6 on the graph are the
  NCC and the OCP of the representation.

## Implementation notes

The axiom numbering follows the dissertation; Jardine and Heinz number the NCC and the OCP as 4
and 5 and have no saturation axiom. Saturation, Goldsmith's original well-formedness condition,
is stated but never imposed. The arcs of `AR.toGraph` are the precedence order of each tier,
transitively closed, so the OCP reads adjacency as the covering relation of the arcs. Jardine's
2019 graphs carry the successor relation instead (Fig. 4), and their subgraphs (Definition 3)
are read in that signature, which `AR.FactorEmbeds` implements in position coordinates; such
subgraph-based notions are sensitive to the signature, as Jardine's analysis of the logical
complexity of these representations shows. Axiom 5 is Coleman and Local's definition of
crossing lines (p. 304) as the dissertation adopts it, with strict precedence; Jardine and Heinz
state their Axiom 4 with the reflexive order, which read literally forbids a node from linking to
two others. Coleman and Local also argue (pp. 297–298) that the NCC amounts to graph planarity
and so restricts nothing in multiplanar representations, the weaker reading that the 2019 paper
sets aside (fn. 11).

## TODO

* The successor reading of a representation, with `AR.FactorEmbeds` as the connected subgraph
  embedding of the 2019 paper's Definition 3 in it.

## References

* [jardine-2019]
* [jardine-2016b]
* [jardine-heinz-2015]
* [jardine-2017-complexity]
* [goldsmith-1976]
* [coleman-local-1991]
-/

@[expose] public section

namespace Autosegmental

variable {S ι : Type*}

/-- A labeled mixed graph: nodes, undirected association edges, directed order arcs, and a
labeling ([jardine-2019]'s `GR(Γ)`). -/
structure Graph (S : Type*) where
  /-- The nodes. -/
  V : Type*
  /-- The undirected association edges (`E`). -/
  edges : SimpleGraph V
  /-- The directed order arcs (`A`). -/
  arcs : Digraph V
  /-- The labeling (`ℓ`). -/
  label : V → S

namespace Graph

variable {X Y Z : Graph S}

/-- The tier of a node under a tier assignment on the labels. -/
def tier (t : S → ι) (X : Graph S) : X.V → ι := t ∘ X.label

/-- An isomorphism of labeled mixed graphs: a bijection of nodes preserving and reflecting the
edges and the arcs, and preserving the labels. -/
structure Iso (X Y : Graph S) extends X.V ≃ Y.V where
  /-- Association edges correspond. -/
  edges_iff : ∀ v w, Y.edges.Adj (toEquiv v) (toEquiv w) ↔ X.edges.Adj v w
  /-- Order arcs correspond. -/
  arcs_iff : ∀ v w, Y.arcs.Adj (toEquiv v) (toEquiv w) ↔ X.arcs.Adj v w
  /-- Labels are preserved. -/
  label_comp : ∀ v, Y.label (toEquiv v) = X.label v

/-- The identity isomorphism. -/
def Iso.refl (X : Graph S) : Iso X X :=
  ⟨Equiv.refl X.V, fun _ _ ↦ Iff.rfl, fun _ _ ↦ Iff.rfl, fun _ ↦ rfl⟩

/-- The inverse isomorphism. -/
def Iso.symm (e : Iso X Y) : Iso Y X where
  toEquiv := e.toEquiv.symm
  edges_iff v w := by simpa using (e.edges_iff (e.toEquiv.symm v) (e.toEquiv.symm w)).symm
  arcs_iff v w := by simpa using (e.arcs_iff (e.toEquiv.symm v) (e.toEquiv.symm w)).symm
  label_comp v := by simpa using (e.label_comp (e.toEquiv.symm v)).symm

/-- The composition of isomorphisms. -/
def Iso.trans (e : Iso X Y) (f : Iso Y Z) : Iso X Z where
  toEquiv := e.toEquiv.trans f.toEquiv
  edges_iff v w := (f.edges_iff _ _).trans (e.edges_iff v w)
  arcs_iff v w := (f.arcs_iff _ _).trans (e.arcs_iff v w)
  label_comp v := (f.label_comp _).trans (e.label_comp v)

end Graph

/-! ### The well-formedness axioms -/

section Axioms

variable {V : Type*} (E : SimpleGraph V) (A : Digraph V)

/-- The arcs `A` are tier-internal and strictly totally order each fiber of `c` (Axioms 1–2). -/
structure IsTierOrdered (c : V → ι) : Prop extends IsStrictOrder V A.Adj where
  /-- Arcs never leave a tier. -/
  tier_eq : ∀ ⦃v w⦄, A.Adj v w → c v = c w
  /-- Distinct same-tier nodes are arc-comparable. -/
  total : ∀ ⦃v w⦄, v ≠ w → c v = c w → A.Adj v w ∨ A.Adj w v

/-- No association edge links arc-related nodes (Axiom 3). -/
def NoInternalAssoc : Prop := ∀ ⦃v w⦄, E.Adj v w → ¬ A.Adj v w

/-- Every node meets an association edge (Axiom 4, full specification). -/
def IsSaturated : Prop := ∀ v, ∃ w, E.Adj v w

/-- No two association edges straddle in opposite precedence order (Axiom 5, the
No-Crossing Constraint). -/
def NoCrossing : Prop :=
  ∀ ⦃v v' w w'⦄, E.Adj v v' → E.Adj w w' → A.Adj v w → ¬ A.Adj w' v'

/-- Precedence-adjacent nodes on melody tier `m` bear distinct labels (Axiom 6, the OCP). -/
def IsOCPClean (ℓ : V → S) (t : S → ι) (m : ι) : Prop :=
  ∀ ⦃v w⦄, A.Adj v w → (∀ u, ¬ (A.Adj v u ∧ A.Adj u w)) → t (ℓ v) = m → ℓ v ≠ ℓ w

end Axioms

namespace AR

variable {τ : ι → Type*}

/-! ### The graph of a representation -/

section ToGraph

variable (X : AR τ)

/-- The labeled mixed graph a representation denotes: its positions, its association lines, the
precedence order of each tier, and the labels tagged with their tiers. -/
def toGraph : Graph ((i : ι) × τ i) where
  V := X.Pos
  edges := X.assoc
  arcs := ⟨fun v w ↦ v.1 = w.1 ∧ (v.2 : ℕ) < w.2⟩
  label v := ⟨v.1, X.label v⟩

theorem toGraph_arcs_adj {v w : X.Pos} : X.toGraph.arcs.Adj v w ↔ v.1 = w.1 ∧ (v.2 : ℕ) < w.2 :=
  Iff.rfl

theorem isTierOrdered_toGraph : IsTierOrdered X.toGraph.arcs (X.toGraph.tier Sigma.fst) where
  irrefl _ h := lt_irrefl _ h.2
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  tier_eq _ _ h := h.1
  total := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hne (rfl : i = j)
    rcases lt_trichotomy (p : ℕ) q with h | h | h
    · exact .inl ⟨rfl, h⟩
    · exact absurd (by rw [Fin.ext h]) hne
    · exact .inr ⟨rfl, h⟩

/-- The graph of a representation satisfies Axiom 3. -/
theorem noInternalAssoc_toGraph : NoInternalAssoc X.toGraph.edges X.toGraph.arcs :=
  fun _ _ hadj harc ↦ fst_ne_of_adj hadj harc.1

/-- Axiom 5 on the graph of a representation is its No-Crossing Constraint. -/
theorem noCrossing_toGraph_iff :
    Autosegmental.NoCrossing X.toGraph.edges X.toGraph.arcs ↔ X.NoCrossing := by
  constructor
  · intro h i j a ha b hb hlt
    by_contra! hgt
    exact @h ⟨i, a.1⟩ ⟨j, a.2⟩ ⟨i, b.1⟩ ⟨j, b.2⟩ ha hb ⟨rfl, hlt⟩ ⟨rfl, hgt⟩
  · rintro h ⟨i, p⟩ ⟨j, q⟩ ⟨i', p'⟩ ⟨j', q'⟩ hvv' hww' ⟨hi, hpp'⟩ ⟨hj, hqq'⟩
    dsimp only at hi hj hpp' hqq'
    subst hi hj
    exact (isNonCrossing_lines_iff.1 (h _ _) (link_iff_adj (v := ⟨_, p⟩) (w := ⟨_, q⟩) |>.2 hvv')
      (link_iff_adj (v := ⟨_, p'⟩) (w := ⟨_, q'⟩) |>.2 hww') hpp').not_gt hqq'

theorem toGraph_covBy_iff {i : ι} {p q : Fin (X.word i).length} :
    (X.toGraph.arcs.Adj ⟨i, p⟩ ⟨i, q⟩ ∧
        ∀ u, ¬ (X.toGraph.arcs.Adj ⟨i, p⟩ u ∧ X.toGraph.arcs.Adj u ⟨i, q⟩)) ↔
      (q : ℕ) = p + 1 := by
  constructor
  · rintro ⟨⟨-, hpq⟩, hcov⟩
    dsimp only at hpq
    have hq := q.2
    by_contra hne
    exact hcov ⟨i, ⟨p + 1, by omega⟩⟩ ⟨⟨rfl, Nat.lt_succ_self _⟩, ⟨rfl, show (p : ℕ) + 1 < q by
      omega⟩⟩
  · intro hsucc
    refine ⟨⟨rfl, show (p : ℕ) < q by omega⟩, ?_⟩
    rintro ⟨j, u⟩ ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
    dsimp only at h₁ h₂
    omega

/-- Axiom 6 on the graph of a representation is the OCP of its melody tier. -/
theorem isOCPClean_toGraph_iff (m : ι) :
    IsOCPClean X.toGraph.arcs X.toGraph.label Sigma.fst m ↔ X.IsCleanAt m := by
  constructor
  · intro h
    refine List.isChain_iff_getElem.mpr fun p hp heq ↦ ?_
    have hcov := (X.toGraph_covBy_iff (i := m) (p := ⟨p, by omega⟩) (q := ⟨p + 1, hp⟩)).mpr rfl
    exact h hcov.1 hcov.2 rfl (by simp only [toGraph, label, Fin.getElem_fin, heq])
  · intro h v w hvw hcov hm heq
    obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    obtain ⟨hij, hlt⟩ := hvw
    have hm' : i = m := hm
    dsimp only at hij hlt
    subst hij hm'
    have hsucc : (q : ℕ) = p + 1 := (X.toGraph_covBy_iff).mp ⟨⟨rfl, hlt⟩, hcov⟩
    have hq : (p : ℕ) + 1 < (X.word i).length := hsucc ▸ q.2
    refine List.isChain_iff_getElem.mp h p hq ?_
    have := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    simp only [label, Fin.getElem_fin] at this
    simpa [hsucc] using this

end ToGraph

/-! ### Isomorphic graphs come from equal representations -/

section Injective

variable {X Y : AR τ}

private theorem natCard_arcs_pred (v : X.Pos) :
    Nat.card {u : X.Pos // X.toGraph.arcs.Adj u v} = v.2 := by
  obtain ⟨i, p⟩ := v
  refine (Nat.card_congr ?_).trans (Nat.card_fin p)
  exact {
    toFun := fun u ↦ ⟨u.1.2, u.2.2⟩
    invFun := fun q ↦ ⟨⟨i, ⟨q, q.2.trans p.2⟩⟩, rfl, q.2⟩
    left_inv := by
      rintro ⟨⟨j, q⟩, hj, h⟩
      dsimp only at hj
      subst hj
      rfl
    right_inv := fun _ ↦ rfl }

private theorem _root_.Autosegmental.Graph.Iso.fst_snd_toGraph
    (e : Graph.Iso X.toGraph Y.toGraph) (v : X.Pos) :
    (e.toEquiv v).1 = v.1 ∧ ((e.toEquiv v).2 : ℕ) = v.2 := by
  refine ⟨congrArg Sigma.fst (e.label_comp v), ?_⟩
  rw [← natCard_arcs_pred, ← natCard_arcs_pred]
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun u ↦ (e.arcs_iff u v).symm)).symm

private theorem _root_.Autosegmental.Graph.Iso.toEquiv_toGraph
    (e : Graph.Iso X.toGraph Y.toGraph) {i : ι} (p : Fin (X.word i).length) :
    ∃ h : (p : ℕ) < (Y.word i).length, e.toEquiv ⟨i, p⟩ = ⟨i, ⟨p, h⟩⟩ := by
  obtain ⟨h₁, h₂⟩ := e.fst_snd_toGraph ⟨i, p⟩
  rcases hv : e.toEquiv ⟨i, p⟩ with ⟨j, q⟩
  rw [hv] at h₁ h₂
  dsimp only at h₁ h₂
  subst h₁
  exact ⟨h₂ ▸ q.2, congrArg (Sigma.mk j) (Fin.ext h₂)⟩

private theorem _root_.Autosegmental.Graph.Iso.link_toGraph
    (e : Graph.Iso X.toGraph Y.toGraph) {i j : ι} {p q : ℕ} (h : X.Link i j p q) :
    Y.Link i j p q := by
  obtain ⟨hp, hq, hadj⟩ := h
  have hadj' := (e.edges_iff _ _).mpr hadj
  obtain ⟨hp', hv⟩ := e.toEquiv_toGraph ⟨p, hp⟩
  obtain ⟨hq', hw⟩ := e.toEquiv_toGraph ⟨q, hq⟩
  rw [hv, hw] at hadj'
  exact ⟨hp', hq', hadj'⟩

/-- Representations whose graphs are isomorphic are equal: the graph reading is injective up to
isomorphism. -/
theorem nonempty_iso_toGraph_iff : Nonempty (Graph.Iso X.toGraph Y.toGraph) ↔ X = Y := by
  refine ⟨fun ⟨e⟩ ↦ ?_, by rintro rfl; exact ⟨Graph.Iso.refl _⟩⟩
  have hlen (i : ι) : (X.word i).length = (Y.word i).length := by
    have key (X Y : AR τ) (e : Graph.Iso X.toGraph Y.toGraph) :
        (X.word i).length ≤ (Y.word i).length := by
      rcases Nat.eq_zero_or_pos (X.word i).length with h | h
      · omega
      obtain ⟨hlt, -⟩ := e.toEquiv_toGraph ⟨_, Nat.sub_lt h Nat.one_pos⟩
      simp only at hlt
      omega
    exact (key X Y e).antisymm (key Y X e.symm)
  refine ext (funext fun i ↦ List.ext_getElem (hlen i) fun p hp hp' ↦ ?_)
    fun i j p q ↦ ⟨e.link_toGraph, e.symm.link_toGraph⟩
  have hl := e.label_comp ⟨i, ⟨p, hp⟩⟩
  obtain ⟨hq, he⟩ := e.toEquiv_toGraph ⟨p, hp⟩
  rw [he] at hl
  have := eq_of_heq (Sigma.mk.inj_iff.mp hl).2
  simpa [label] using this.symm

end Injective

/-! ### Every finite graph satisfying Axioms 1–3 is the graph of a representation -/

section OfGraph

variable (G : Graph ((i : ι) × τ i))

/-- The nodes of `G` on tier `i`. -/
abbrev _root_.Autosegmental.Graph.Fiber (i : ι) : Type _ := {v : G.V // (G.label v).1 = i}

variable {G}

/-- The `τ i` label of a node on tier `i`. -/
def _root_.Autosegmental.Graph.Fiber.label {i : ι} (v : G.Fiber i) : τ i :=
  v.2 ▸ (G.label v.1).2

theorem _root_.Autosegmental.Graph.Fiber.label_eq {i : ι} (v : G.Fiber i) :
    G.label v.1 = ⟨i, v.label⟩ := by
  obtain ⟨u, hu⟩ := v
  simp only [Graph.Fiber.label]
  conv_lhs => rw [← Sigma.eta (G.label u)]
  exact Sigma.ext hu (by subst hu; rfl)

variable (h : IsTierOrdered G.arcs (G.tier Sigma.fst))

include h in
theorem isStrictTotalOrder_fiber (i : ι) :
    IsStrictTotalOrder (G.Fiber i) fun a b ↦ G.arcs.Adj a.1 b.1 where
  trichotomous a b hab hba := Subtype.ext <| of_not_not fun hne ↦
    (h.total hne (a.2.trans b.2.symm)).elim hab hba
  irrefl a := h.irrefl a.1
  trans _ _ _ hab hbc := h.trans _ _ _ hab hbc

variable [Finite G.V]

/-- The enumeration of a tier in arc order. -/
noncomputable def fiberEnum (i : ι) : Fin (Nat.card (G.Fiber i)) ≃ G.Fiber i :=
  letI := isStrictTotalOrder_fiber h i
  letI := Classical.decRel fun a b : G.Fiber i ↦ G.arcs.Adj a.1 b.1
  letI := linearOrderOfSTO fun a b : G.Fiber i ↦ G.arcs.Adj a.1 b.1
  letI := Fintype.ofFinite (G.Fiber i)
  (monoEquivOfFin (G.Fiber i) Nat.card_eq_fintype_card.symm).toEquiv

theorem arcs_fiberEnum_iff {i : ι} {p q : Fin (Nat.card (G.Fiber i))} :
    G.arcs.Adj (fiberEnum h i p).1 (fiberEnum h i q).1 ↔ p < q :=
  letI := isStrictTotalOrder_fiber h i
  letI := Classical.decRel fun a b : G.Fiber i ↦ G.arcs.Adj a.1 b.1
  letI := linearOrderOfSTO fun a b : G.Fiber i ↦ G.arcs.Adj a.1 b.1
  letI := Fintype.ofFinite (G.Fiber i)
  (monoEquivOfFin (G.Fiber i) Nat.card_eq_fintype_card.symm).lt_iff_lt

/-- The word of tier `i`: the labels of the tier's nodes in arc order. -/
noncomputable def ofGraphWord (i : ι) : List (τ i) := List.ofFn fun p ↦ (fiberEnum h i p).label

/-- The nodes of `G`, enumerated tier by tier in arc order. -/
noncomputable def ofGraphEquiv : ((i : ι) × Fin (ofGraphWord h i).length) ≃ G.V :=
  (Equiv.sigmaCongrRight fun i ↦ (finCongr List.length_ofFn).trans (fiberEnum h i)).trans
    (Equiv.sigmaFiberEquiv fun v ↦ (G.label v).1)

theorem ofGraphEquiv_apply (v : (i : ι) × Fin (ofGraphWord h i).length) :
    ofGraphEquiv h v = (fiberEnum h v.1 (finCongr List.length_ofFn v.2)).1 := rfl

theorem fst_label_ofGraphEquiv (v : (i : ι) × Fin (ofGraphWord h i).length) :
    (G.label (ofGraphEquiv h v)).1 = v.1 :=
  (fiberEnum h v.1 _).2

variable (G) in
/-- The representation of a finite graph satisfying Axioms 1–3: the labels of each tier in arc
order, and the association edges between the corresponding positions. -/
noncomputable def ofGraph (h₃ : NoInternalAssoc G.edges G.arcs) : AR τ where
  word := ofGraphWord h
  assoc := G.edges.comap (ofGraphEquiv h)
  assoc_le v w hvw hvw₁ := by
    have hvw' : G.edges.Adj (ofGraphEquiv h v) (ofGraphEquiv h w) := hvw
    have htier : G.tier Sigma.fst (ofGraphEquiv h v) = G.tier Sigma.fst (ofGraphEquiv h w) := by
      simp only [Graph.tier, Function.comp_apply, fst_label_ofGraphEquiv]
      exact hvw₁
    exact (h.total hvw'.ne htier).elim (h₃ hvw') (h₃ hvw'.symm)
  decidableAdj := Classical.decRel _

/-- A finite graph satisfying Axioms 1–3 is the graph of its representation. -/
noncomputable def ofGraphIso (h₃ : NoInternalAssoc G.edges G.arcs) :
    Graph.Iso (ofGraph G h h₃).toGraph G where
  toEquiv := ofGraphEquiv h
  edges_iff _ _ := Iff.rfl
  arcs_iff := by
    rintro ⟨i, p⟩ ⟨j, q⟩
    change G.arcs.Adj (fiberEnum h i (finCongr List.length_ofFn p)).1
      (fiberEnum h j (finCongr List.length_ofFn q)).1 ↔ i = j ∧ (p : ℕ) < q
    rcases eq_or_ne i j with rfl | hij
    · rw [arcs_fiberEnum_iff]
      exact ⟨fun h ↦ ⟨rfl, h⟩, fun h ↦ h.2⟩
    · refine iff_of_false (fun ha ↦ hij ?_) (fun h' ↦ hij h'.1)
      exact (fiberEnum h i _).2.symm.trans ((h.tier_eq ha).trans (fiberEnum h j _).2)
  label_comp := by
    rintro ⟨i, p⟩
    change G.label (fiberEnum h i (finCongr List.length_ofFn p)).1 = ⟨i, (ofGraphWord h i)[p]⟩
    rw [Graph.Fiber.label_eq]
    simp only [ofGraphWord, Fin.getElem_fin, List.getElem_ofFn]
    rfl

end OfGraph

end AR

end Autosegmental
