module

public import Linglib.Syntax.Minimalist.Workspace.Algebra.Merge.Internal
public import Linglib.Syntax.Minimalist.Workspace.TraceMeasures

/-!
# No Complexity Loss

No Complexity Loss is a condition on a transformation `F → F'` of workspaces (Definition 1.6.2 of
Marcolli, Chomsky and Berwick): the map sending each component of `F` to the component of `F'`
holding its root never decreases degree, so Merge builds hierarchical structure of nondecreasing
complexity. `NoComplexityLoss.Map deg φ` checks a component map, as a multiset `φ` of pairs, for
a degree `deg`, and `NoComplexityLoss deg F F'` asks for one from `F` to `F'`.

A term of Merge chooses a cut for each component, so its own map, `componentMap`, sends a
component taken whole to the Merge and a cut component to its trunk. Along it, no complexity is
lost exactly when every component is taken whole or left uncut, as External Merge does. Every
Sideward term, and every term of the unit stage on its own, cuts a component and loses complexity
(Proposition 1.6.10). These hold for any positive degree whose cuts have a fixed extraction
cost.

## Implementation notes

The book grades by leaf count. A degree that each cut conserves avoids the nullary-node
corrections leaf count incurs when a node loses all its children under a multi-edge cut. At the
pruning cuts this is the vertex count, the canonical Connes–Kreimer grading. At the trace cuts a
trace leaf takes the place of each extracted tree, so extracting a single lexical item keeps the
vertex count. They conserve instead the size `σ`, which leaves trace leaves out (the book's
(1.6.10)), and graded by `σ` every Sideward term loses complexity there too.

## Main definitions

* `Minimalist.NoComplexityLoss`, `Minimalist.NoComplexityLoss.Map`
* `Minimalist.componentMap`: the component map of a choice of cuts.

## Main results

* `Minimalist.NoComplexityLoss.of_componentMap`: the component map of a term of Merge goes to the
  workspace the term builds.
* `Minimalist.NoComplexityLoss.map_componentMap_merge_iff`: a term of Merge loses no complexity
  exactly when it takes components whole or leaves them uncut.
* `Minimalist.NoComplexityLoss.not_map_componentMap_merge`, `not_map_componentMap_unit`: every
  Sideward term and every term of the unit stage loses complexity.
* `Minimalist.NoComplexityLoss.not_map_accessibleSize_componentMap_merge`: at the trace cuts,
  graded by `σ`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

/-! ### No Complexity Loss along the component map of a term of Merge

[marcolli-chomsky-berwick-2025] Definition 1.6.2 states No Complexity Loss for the induced map,
which sends each component of the workspace to the component holding its root afterwards. A term
of Merge or of its unit stage is a choice of a cut for each component (`mergeOpG_apply_of'_eq_sum`,
`mergeOpUnitG_apply_of'_eq_sum`), so its induced map pairs a component taken whole with the object
built from the crown, and a cut component with its trunk. As a multiset of pairs it keeps apart
equal components that go to different places.

The results hold for any positive degree with a fixed extraction cost
(`CutChoice.HasExtractionCost`), such as the degrees each cut conserves: the vertex count at the
pruning cuts (`hasExtractionCost_numNodes_cutSummandsN`) and the size `σ` at the trace cuts
(`hasExtractionCost_accessibleSize_cutSummandsCN`, the book's (1.6.10)). -/

section ComponentMap

variable {α : Type*} {deg : UnorderedTree α → ℕ}

/-- No Complexity Loss holds along a component map when no component is paired with one of lower
    degree. -/
def NoComplexityLoss.Map (deg : UnorderedTree α → ℕ)
    (φ : Multiset (UnorderedTree α × UnorderedTree α)) : Prop :=
  ∀ x ∈ φ, deg x.1 ≤ deg x.2

/-- A workspace transformation `F → F'` satisfies No Complexity Loss when some component map,
    pairing each component of `F` with a component of `F'`, loses no degree
    ([marcolli-chomsky-berwick-2025] Definition 1.6.2 asks this of the induced map). -/
def NoComplexityLoss (deg : UnorderedTree α → ℕ) (F F' : Forest (UnorderedTree α)) : Prop :=
  ∃ φ : Multiset (UnorderedTree α × UnorderedTree α),
    φ.map Prod.fst = F ∧ (∀ x ∈ φ, x.2 ∈ F') ∧ NoComplexityLoss.Map deg φ

variable {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
  {F : Forest (UnorderedTree α)} {s : CutChoice α} {k : ℕ}

/-- A tree taken whole into the crown `{S, S'}` of a term of Merge is one of the merged objects,
    and so weighs no more than any object outweighing both. -/
private theorem deg_le_of_snd_eq_zero (hs : s ∈ forestCutChoicesG cuts F)
    {S S' X : UnorderedTree α} (hK : s.crown = {S, S'}) (hS : deg S ≤ deg X)
    (hS' : deg S' ≤ deg X) : ∀ x ∈ s, x.2.2 = 0 → deg x.1 ≤ deg X := by
  intro x hx h0
  have hmem : x.1 ∈ ({S, S'} : Forest (UnorderedTree α)) := hK ▸ CutChoice.fst_mem_crown hs hx h0
  rcases Multiset.mem_cons.mp hmem with h | h
  · exact h ▸ hS
  · exact Multiset.mem_singleton.mp h ▸ hS'

variable [DecidableEq (UnorderedTree α)]

/-- The component map of a choice of cuts sends a tree taken whole to the object `X` built from the
    crown, and a cut tree to its trunk. -/
def componentMap (X : UnorderedTree α) (s : CutChoice α) :
    Multiset (UnorderedTree α × UnorderedTree α) :=
  s.bind fun x ↦ (if x.2.2 = 0 then {X} else x.2.2).map (Prod.mk x.1)

/-- The component map of a term of Merge pairs each component of the workspace with a component of
    the workspace the term builds. -/
theorem NoComplexityLoss.of_componentMap (hs : s ∈ forestCutChoicesG cuts F)
    {X : UnorderedTree α} (h : NoComplexityLoss.Map deg (componentMap X s)) :
    NoComplexityLoss deg F ({X} + s.trunk) := by
  refine ⟨componentMap X s, ?_, fun y hy ↦ ?_, h⟩
  · rw [componentMap, Multiset.map_bind, ← map_fst_of_mem_forestCutChoicesG hs,
      ← Multiset.bind_singleton]
    refine Multiset.bind_congr fun x hx ↦ ?_
    rcases mem_treeCutsG.mp (mem_treeCutsG_of_mem_forestCutChoicesG hs hx) with h2 | ⟨p, -, h2⟩
    · simp [h2]
    · simp [← h2]
  · obtain ⟨x, hx, hy⟩ := Multiset.mem_bind.mp hy
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
    by_cases h0 : x.2.2 = 0
    · rw [ite_eq_left h0, Multiset.mem_singleton] at ht
      exact Multiset.mem_add.mpr (.inl (Multiset.mem_singleton.mpr ht))
    · rw [ite_eq_right h0] at ht
      exact Multiset.mem_add.mpr (.inr (CutChoice.mem_trunk.mpr ⟨x, hx, ht⟩))

/-- Along the component map of a choice of cuts with an extraction cost in a positive degree, no
    complexity is lost exactly when every tree is taken whole or left uncut, provided the object
    `X` outweighs the trees taken whole. -/
theorem NoComplexityLoss.map_componentMap_iff (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost deg k) (hpos : ∀ T, 0 < deg T) {X : UnorderedTree α}
    (hX : ∀ x ∈ s, x.2.2 = 0 → deg x.1 ≤ deg X) :
    NoComplexityLoss.Map deg (componentMap X s) ↔ ∀ x ∈ s, x.2.1 = 0 ∨ x.2.2 = 0 := by
  simp only [NoComplexityLoss.Map, componentMap, Multiset.mem_bind, Multiset.mem_map]
  constructor
  · intro h x hx
    rcases mem_treeCutsG.mp (mem_treeCutsG_of_mem_forestCutChoicesG hs hx) with h2 | ⟨p, hp, h2⟩
    · exact .inr (by rw [h2])
    · refine .inl ?_
      have hle := h (x.1, p.2) ⟨x, hx, p.2, by simp [← h2], rfl⟩
      have hc := hc x hx (by rw [← h2]; exact Multiset.singleton_ne_zero _)
      rw [← h2] at hc ⊢
      show p.1 = 0
      refine Multiset.eq_zero_of_forall_notMem fun u hu ↦ ?_
      have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem deg hu)
      have := hpos u
      simp only [Multiset.map_singleton, Multiset.sum_singleton] at hle hc
      omega
  · rintro h y ⟨x, hx, t, ht, rfl⟩
    by_cases h0 : x.2.2 = 0
    · rw [ite_eq_left h0, Multiset.mem_singleton] at ht
      exact ht ▸ hX x hx h0
    · rw [ite_eq_right h0] at ht
      rcases mem_treeCutsG.mp (mem_treeCutsG_of_mem_forestCutChoicesG hs hx) with h2 | ⟨p, hp, h2⟩
      · exact absurd (by rw [h2]) h0
      · have hc := hc x hx h0
        rw [← h2, Multiset.mem_singleton] at ht
        have h1 : p.1 = 0 := by
          have := (h x hx).resolve_right h0
          rwa [← h2] at this
        rw [← h2, h1] at hc
        simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.card_zero, Nat.mul_zero,
          Nat.add_zero, Nat.zero_add, Multiset.map_singleton, Multiset.sum_singleton] at hc
        exact (ht ▸ hc).le

/-- A tree of the crown that is not a component of the workspace was cut out of a component, and
    that component goes to a trunk of lower degree. -/
theorem NoComplexityLoss.not_map_componentMap (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost deg k) (hpos : ∀ T, 0 < deg T) {X : UnorderedTree α}
    (hX : ∀ x ∈ s, x.2.2 = 0 → deg x.1 ≤ deg X)
    {T : UnorderedTree α} (hT : T ∈ s.crown) (hTF : T ∉ F) :
    ¬ NoComplexityLoss.Map deg (componentMap X s) := by
  rw [NoComplexityLoss.map_componentMap_iff hs hc hpos hX]
  intro h
  obtain ⟨x, hx, hTx⟩ := CutChoice.mem_crown.mp hT
  rcases h x hx with h0 | h0
  · exact Multiset.notMem_zero _ (h0 ▸ hTx)
  · rw [snd_eq_of_mem_forestCutChoicesG hs hx h0, Multiset.mem_singleton] at hTx
    exact hTF (hTx ▸ fst_mem_of_mem_forestCutChoicesG hs hx)

/-- A term of Merge loses no complexity along its component map exactly when it takes trees whole
    or leaves them uncut ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). -/
theorem NoComplexityLoss.map_componentMap_merge_iff (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost deg k) (hpos : ∀ T, 0 < deg T) {S S' X : UnorderedTree α}
    (hK : s.crown = {S, S'})
    (hS : deg S ≤ deg X) (hS' : deg S' ≤ deg X) :
    NoComplexityLoss.Map deg (componentMap X s) ↔ ∀ x ∈ s, x.2.1 = 0 ∨ x.2.2 = 0 :=
  NoComplexityLoss.map_componentMap_iff hs hc hpos (deg_le_of_snd_eq_zero hs hK hS hS')

/-- Every term of Sideward Merge loses complexity along its component map
    ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). If `S` or `S'` is not a component of the
    workspace, the component it is cut out of goes to a trunk of lower degree. -/
theorem NoComplexityLoss.not_map_componentMap_merge (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost deg k) (hpos : ∀ T, 0 < deg T) {S S' X : UnorderedTree α}
    (hK : s.crown = {S, S'})
    (hS : deg S ≤ deg X) (hS' : deg S' ≤ deg X) (h : S ∉ F ∨ S' ∉ F) :
    ¬ NoComplexityLoss.Map deg (componentMap X s) := by
  have hX := deg_le_of_snd_eq_zero hs hK hS hS'
  rcases h with h | h
  · exact NoComplexityLoss.not_map_componentMap hs hc hpos hX
      (hK ▸ Multiset.mem_cons_self _ _) h
  · exact NoComplexityLoss.not_map_componentMap hs hc hpos hX
      (hK ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)) h

/-- Every term of the unit stage `M_{β,1}` with `β` not a component of the workspace loses
    complexity along its component map ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). -/
theorem NoComplexityLoss.not_map_componentMap_unit (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost deg k) (hpos : ∀ T, 0 < deg T) {β : UnorderedTree α}
    (hK : s.crown = {β}) (hβ : β ∉ F) : ¬ NoComplexityLoss.Map deg (componentMap β s) :=
  NoComplexityLoss.not_map_componentMap hs hc hpos
    (fun x hx h0 ↦ by
      have : x.1 ∈ ({β} : Forest (UnorderedTree α)) := hK ▸ CutChoice.fst_mem_crown hs hx h0
      rw [Multiset.mem_singleton.mp this])
    (hK ▸ Multiset.mem_singleton_self _) hβ

end ComponentMap

/-! ### At the trace cuts

Graded by vertices, a term of Merge at the trace cuts may lose nothing, since a trace leaf takes
the place of each extracted tree. Graded by the size `σ`, which the trace cuts conserve, every
Sideward term loses complexity. -/

section TraceCuts

variable {α β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))] {τ : UnorderedTree (α ⊕ β) → β}
  {F : Forest (UnorderedTree (α ⊕ β))} {s : CutChoice (α ⊕ β)}

/-- At the trace cuts, graded by the size `σ`, every term of Sideward Merge loses complexity along
    its component map ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). -/
theorem NoComplexityLoss.not_map_accessibleSize_componentMap_merge (a : α)
    (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → ∃ a, x.1.value = Sum.inl a)
    {S S' : UnorderedTree (α ⊕ β)} (hK : s.crown = {S, S'})
    (h : S ∉ F ∨ S' ∉ F) :
    ¬ NoComplexityLoss.Map (fun T ↦ Forest.accessibleSize {T})
      (componentMap (UnorderedTree.node (Sum.inl a) {S, S'}) s) := by
  have hmerge := accessibleCount_merge_of_crown_eq a hs hF hK
  refine NoComplexityLoss.not_map_componentMap_merge hs
    (hasExtractionCost_accessibleSize_cutSummandsCN hs hF) (fun T ↦ by simp) hK ?_ ?_ h <;>
    simp only [Forest.accessibleSize_singleton, hmerge] <;> omega

end TraceCuts

end Minimalist
