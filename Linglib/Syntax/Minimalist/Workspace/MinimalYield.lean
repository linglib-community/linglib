module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Syntax.Minimalist.Workspace.Algebra.Coproduct.Deletion
public import Linglib.Syntax.Minimalist.Workspace.TraceMeasures
public import Mathlib.Order.OrderDual

/-!
# Minimal Yield

Minimal Yield (Definition 1.6.1 of Marcolli, Chomsky and Berwick) is a condition on a
transformation `F → F'` of workspaces. The number `b₀` of components does not grow (no
divergence), the number `α` of accessible terms does not fall (no information loss), and the size
`σ = b₀ + α` grows by exactly one (minimality of yield). `MinimalYieldWeak` is the first two
bounds and `MinimalYield` all three. Both take the count of accessible terms of a component as a
parameter, since Proposition 1.6.4 evaluates the one condition under two countings: the deletion
coproduct counts every non-root vertex (`UnorderedTree.numEdges`), the trace coproduct every
non-root vertex but its trace leaves (`UnorderedTree.accessibleCount`).

A term of Merge chooses a cut for each component of the workspace. Each component it takes whole
lowers `b₀` by one, and each tree it extracts costs a fixed number `k` of accessible terms
(`CutChoice.HasExtractionCost`): one under the trace coproduct, and two under the deletion
coproduct on full binary trees (Lemma 1.6.3). When extractions cost one, a term satisfies Minimal
Yield exactly when it takes an object whole, so External Merge and the Sideward case 2(b) pass and
the cases 3(a) and 3(b) fail (Proposition 1.6.8). When they cost two, only External Merge passes,
and 2(b) satisfies only the weak form. Internal Merge gains one accessible term under the trace
coproduct and none under the deletion coproduct, where it satisfies only the weak form
(Proposition 1.6.4).

## Main definitions

* `Minimalist.MinimalYieldWeak`, `Minimalist.MinimalYield`
* `Minimalist.MinimalYield.signature`: the Pareto signature `(b₀ᵒᵈ, α)`, whose order is the weak
  form (`minimalYieldWeak_iff_signature_le`).

## Main results

* `Minimalist.MinimalYield.merge_term_iff_of_extraction_one`,
  `MinimalYield.merge_term_iff_of_extraction_two`: a term of Merge satisfies Minimal Yield exactly
  when it takes one, or both, of its objects whole. External Merge takes both
  (`MinimalYield.em_pair`).
* `Minimalist.MinimalYield.merge_term_accessibleCount_iff`, `MinimalYield.merge_term_numEdges_iff`:
  under trace and under deletion counting.
* `Minimalist.MinimalYield.im_accessibleCount_of_cut`, `MinimalYieldWeak.im_numEdges_of_cut`,
  `MinimalYield.not_im_numEdges_of_cut`: Internal Merge.
* `Minimalist.MinimalYieldWeak.not_of_forall_notMem`: a term whose crown holds no component of the
  workspace violates it under any counting.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree ConnesKreimer

variable {α β κ : Type*}

/-! ### The Minimal Yield principle -/

/-- The weak Minimal Yield principle, for the count `acc` of the accessible terms of a component,
    allows no increase in the number `b₀` of components and no decrease in the number `α` of
    accessible terms. -/
structure MinimalYieldWeak (acc : κ → ℕ) (F F' : Multiset κ) : Prop where
  noDivergence : Multiset.card F' ≤ Multiset.card F
  noInfoLoss : (F.map acc).sum ≤ (F'.map acc).sum

/-- The Minimal Yield principle is the weak form together with the size `σ = b₀ + α` going up by
    exactly one. -/
structure MinimalYield (acc : κ → ℕ) (F F' : Multiset κ) : Prop
    extends MinimalYieldWeak acc F F' where
  minimalYield : Multiset.card F' + (F'.map acc).sum = Multiset.card F + (F.map acc).sum + 1

/-- Spectators preserve Minimal Yield. -/
theorem MinimalYield.add_right {acc : κ → ℕ} {F F' : Multiset κ} (h : MinimalYield acc F F')
    (W : Multiset κ) : MinimalYield acc (F + W) (F' + W) where
  noDivergence := by simpa using h.noDivergence
  noInfoLoss := by simpa using h.noInfoLoss
  minimalYield := by
    simp only [Multiset.card_add, Multiset.map_add, Multiset.sum_add]
    have := h.minimalYield
    omega

/-! ### `MinimalYieldWeak` as a Pareto pullback preorder -/

/-- The Pareto signature `(b₀ᵒᵈ, α)`, `b₀` dualised so fewer components ranks higher. -/
def MinimalYield.signature (acc : κ → ℕ) (F : Multiset κ) : ℕᵒᵈ × ℕ :=
  (OrderDual.toDual (Multiset.card F), (F.map acc).sum)

theorem minimalYieldWeak_iff_signature_le {acc : κ → ℕ} {F F' : Multiset κ} :
    MinimalYieldWeak acc F F' ↔ MinimalYield.signature acc F ≤ MinimalYield.signature acc F' :=
  ⟨fun ⟨h_b, h_a⟩ ↦ ⟨h_b, h_a⟩, fun ⟨h_b, h_a⟩ ↦ ⟨h_b, h_a⟩⟩

/-! ### Terms of Merge and of its unit stage

A term of Merge or of its unit stage on `F` chooses a cut for each component of `F`
(`mergeOpG_apply_of'_eq_sum`, `mergeOpUnitG_apply_of'_eq_sum`). Its workspace holds the object `X`
built from the crown beside the trunk. -/

section Terms

variable [DecidableEq (UnorderedTree α)]
  {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
  {F : Forest (UnorderedTree α)} {s : CutChoice α} {acc : UnorderedTree α → ℕ} {k : ℕ}

/-- A term has one component for the object built from the crown and one for each component that
    was cut, so each component taken whole lowers `b₀` by one. -/
theorem card_singleton_add_trunk_add_numWhole (hs : s ∈ forestCutChoicesG cuts F)
    (X : UnorderedTree α) :
    Multiset.card ({X} + s.trunk) + s.numWhole = Multiset.card F + 1 := by
  rw [Multiset.card_add, Multiset.card_singleton, add_assoc,
    CutChoice.card_trunk_add_numWhole hs, add_comm]

/-- A term that takes no component whole raises `b₀`, so a term satisfying the weak form of
    Minimal Yield takes some component whole. -/
theorem MinimalYieldWeak.numWhole_ne_zero (hs : s ∈ forestCutChoicesG cuts F)
    {X : UnorderedTree α} (h : MinimalYieldWeak acc F ({X} + s.trunk)) : s.numWhole ≠ 0 := by
  have := card_singleton_add_trunk_add_numWhole hs X
  have := h.noDivergence
  omega

/-- A term of Merge has the accessible terms of the workspace, `2` more for the Merge of its two
    objects, and `k` fewer for each object it extracts rather than takes whole. -/
theorem sum_map_merge_term_add (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost acc k) {S S' X : UnorderedTree α} (hK : s.crown = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    (({X} + s.trunk).map acc).sum + 2 * k = (F.map acc).sum + k * s.numWhole + 2 := by
  have h := hc.sum_map_add_mul_numWhole hs
  rw [hK] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, Multiset.card_cons, Multiset.card_singleton] at h
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
  omega

/-- When each extraction costs one accessible term, as under `Δ^c`, a Merge term satisfies Minimal
Yield iff some merged object is an unextracted workspace component (Lemma 1.6.3 (1.6.8)). -/
theorem MinimalYield.merge_term_iff_of_extraction_one (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost acc 1) {S S' X : UnorderedTree α} (hK : s.crown = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    MinimalYield acc F ({X} + s.trunk) ↔ s.numWhole ≠ 0 := by
  have hα := sum_map_merge_term_add hs hc hK hX
  have hb := card_singleton_add_trunk_add_numWhole hs X
  refine ⟨fun h ↦ h.numWhole_ne_zero hs, fun h ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> omega

/-- When each extraction costs two accessible terms, as under `Δ^d`, a Merge term satisfies Minimal
Yield iff both merged objects are unextracted workspace components (Lemma 1.6.3 (1.6.7)). -/
theorem MinimalYield.merge_term_iff_of_extraction_two (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost acc 2) {S S' X : UnorderedTree α} (hK : s.crown = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    MinimalYield acc F ({X} + s.trunk) ↔ s.numWhole = 2 := by
  have hα := sum_map_merge_term_add hs hc hK hX
  have hb := card_singleton_add_trunk_add_numWhole hs X
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have := h.minimalYield; omega
  all_goals omega

/-- With each extraction costing two accessible terms, a term of Merge satisfies the weak form of
    Minimal Yield exactly when it takes at least one of its objects whole. -/
theorem MinimalYieldWeak.merge_term_iff_of_extraction_two (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost acc 2) {S S' X : UnorderedTree α} (hK : s.crown = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    MinimalYieldWeak acc F ({X} + s.trunk) ↔ s.numWhole ≠ 0 := by
  have hα := sum_map_merge_term_add hs hc hK hX
  have hb := card_singleton_add_trunk_add_numWhole hs X
  refine ⟨fun h ↦ h.numWhole_ne_zero hs, fun h ↦ ⟨?_, ?_⟩⟩ <;> omega

/-- A term of the unit stage has the accessible terms of the workspace, less `k` for the object
    it extracts unless it takes it whole. -/
theorem sum_map_unit_term_add (hs : s ∈ forestCutChoicesG cuts F)
    (hc : s.HasExtractionCost acc k) {B : UnorderedTree α} (hK : s.crown = {B}) :
    (({B} + s.trunk).map acc).sum + k = (F.map acc).sum + k * s.numWhole := by
  have h := hc.sum_map_add_mul_numWhole hs
  rw [hK] at h
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton,
    mul_one] at h
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
  omega

/-- A term whose crown contains no workspace component violates Minimal Yield under any counting
([marcolli-chomsky-berwick-2025] Proposition 1.6.8, Remark 1.6.7). -/
theorem MinimalYieldWeak.not_of_forall_notMem (acc : UnorderedTree α → ℕ)
    (hs : s ∈ forestCutChoicesG cuts F) (hK : ∀ T ∈ s.crown, T ∉ F) (X : UnorderedTree α) :
    ¬ MinimalYieldWeak acc F ({X} + s.trunk) := fun h ↦
  h.numWhole_ne_zero hs <| CutChoice.numWhole_eq_zero.mpr fun x hx hx0 ↦
    hK x.1 (CutChoice.fst_mem_crown hs hx hx0) (fst_mem_of_mem_forestCutChoicesG hs hx)

/-- Strong-form corollary of `MinimalYieldWeak.not_of_forall_notMem`. -/
theorem MinimalYield.not_of_forall_notMem (acc : UnorderedTree α → ℕ)
    (hs : s ∈ forestCutChoicesG cuts F) (hK : ∀ T ∈ s.crown, T ∉ F) (X : UnorderedTree α) :
    ¬ MinimalYield acc F ({X} + s.trunk) :=
  fun h ↦ MinimalYieldWeak.not_of_forall_notMem acc hs hK X h.toMinimalYieldWeak

end Terms

/-! ### External Merge

External Merge is the term of Merge that takes both of its objects whole. It extracts nothing, so
it satisfies Minimal Yield whatever extractions cost. -/

/-- External Merge of a pair satisfies Minimal Yield under deletion counting, with Δb₀ = −1,
    Δα = +2 and Δσ = +1. -/
theorem MinimalYield.em_pair (lbl : α) (S S' : UnorderedTree (α ⊕ β)) :
    MinimalYield UnorderedTree.numEdges ({S, S'} : Forest (UnorderedTree (α ⊕ β)))
      {UnorderedTree.node (Sum.inl lbl) {S, S'}} := by
  classical
  simpa using (merge_term_iff_of_extraction_two
    (map_whole_mem_forestCutChoicesG (cuts := cutSummandsN) _)
    (CutChoice.hasExtractionCost_map_whole _ _ _) (CutChoice.crown_map_whole _)
    (UnorderedTree.numEdges_node_pair _ S S')).2 (by simp)

/-- External Merge of two objects that are not traces satisfies Minimal Yield under trace
    counting. -/
theorem MinimalYield.em_pair_accessibleCount (lbl : α) {S S' : UnorderedTree (α ⊕ β)}
    (hS : S.numTraces < S.numNodes) (hS' : S'.numTraces < S'.numNodes) :
    MinimalYield UnorderedTree.accessibleCount ({S, S'} : Forest (UnorderedTree (α ⊕ β)))
      {UnorderedTree.node (Sum.inl lbl) {S, S'}} := by
  classical
  simpa using (merge_term_iff_of_extraction_two
    (map_whole_mem_forestCutChoicesG (cuts := cutSummandsN) _)
    (CutChoice.hasExtractionCost_map_whole _ _ _) (CutChoice.crown_map_whole _)
    (UnorderedTree.accessibleCount_merge lbl S S' hS hS')).2 (by simp)

/-! ### Internal Merge

Internal Merge extracts a term `v` of `T` and merges it with what remains. -/

section Internal

variable (lbl : α) {T : UnorderedTree (α ⊕ β)}
  {p : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)} {v : UnorderedTree (α ⊕ β)}

/-- Internal Merge through a deletion cut of a full binary tree keeps its accessible terms
    ([marcolli-chomsky-berwick-2025] Proposition 1.6.4, for `Δ^d`). -/
theorem numEdges_im_of_cut (hT : T.IsFullBinary) (hp : p ∈ cutSummandsDN T) (hv : p.1 = {v}) :
    (UnorderedTree.node (Sum.inl lbl) {v, p.2}).numEdges = T.numEdges := by
  rw [UnorderedTree.numEdges_node_pair, cutSummandsDN_numEdges hT hp hv]

/-- Internal Merge through a deletion cut of a full binary tree satisfies the weak form of Minimal
    Yield under deletion counting. -/
theorem MinimalYieldWeak.im_numEdges_of_cut (hT : T.IsFullBinary) (hp : p ∈ cutSummandsDN T)
    (hv : p.1 = {v}) :
    MinimalYieldWeak UnorderedTree.numEdges {T} {UnorderedTree.node (Sum.inl lbl) {v, p.2}} :=
  ⟨by simp, by simp only [Multiset.map_singleton, Multiset.sum_singleton,
    numEdges_im_of_cut lbl hT hp hv, le_refl]⟩

/-- Internal Merge through a deletion cut of a full binary tree violates Minimal Yield under
    deletion counting, since its size `σ` does not grow. -/
theorem MinimalYield.not_im_numEdges_of_cut (hT : T.IsFullBinary) (hp : p ∈ cutSummandsDN T)
    (hv : p.1 = {v}) :
    ¬ MinimalYield UnorderedTree.numEdges {T} {UnorderedTree.node (Sum.inl lbl) {v, p.2}} :=
  fun h ↦ by
    have := h.minimalYield
    simp only [Multiset.card_singleton, Multiset.map_singleton, Multiset.sum_singleton,
      numEdges_im_of_cut lbl hT hp hv] at this
    omega

end Internal

/-- Internal Merge through a trace cut of a tree whose root is not a trace gains one accessible
    term ([marcolli-chomsky-berwick-2025] Proposition 1.6.4, for `Δ^c`). -/
theorem accessibleCount_im_of_cut (lbl a₀ : α) (τ : UnorderedTree (α ⊕ β) → β)
    (F₀ : Forest (UnorderedTree (α ⊕ β)))
    (p : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β))
    (hp : p ∈ cutSummandsCN τ (UnorderedTree.node (Sum.inl a₀) F₀))
    (v : UnorderedTree (α ⊕ β)) (hv : p.1 = {v}) :
    (UnorderedTree.node (Sum.inl lbl) {v, p.2}).accessibleCount =
      (UnorderedTree.node (Sum.inl a₀) F₀).accessibleCount + 1 := by
  rw [UnorderedTree.accessibleCount_merge lbl v p.2
    (UnorderedTree.numTraces_lt_numNodes_of_isLeft <|
      cutSummandsCN_value_isLeft_of_mem_crown τ _ p hp v (hv ▸ Multiset.mem_singleton_self v))
    (UnorderedTree.numTraces_lt_numNodes_of_isLeft <| by
      rw [cutSummandsCN_trunk_value τ _ p hp]; simp)]
  have := cutSummandsCN_accessibleCount τ (by simp) hp
  simp only [hv, Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton] at this
  omega

/-- Internal Merge through a trace cut satisfies Minimal Yield under trace counting, with Δb₀ = 0,
    Δα = +1 and Δσ = +1. -/
theorem MinimalYield.im_accessibleCount_of_cut (lbl a₀ : α) (τ : UnorderedTree (α ⊕ β) → β)
    (F₀ : Forest (UnorderedTree (α ⊕ β)))
    (p : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β))
    (hp : p ∈ cutSummandsCN τ (UnorderedTree.node (Sum.inl a₀) F₀))
    (v : UnorderedTree (α ⊕ β)) (hv : p.1 = {v}) :
    MinimalYield UnorderedTree.accessibleCount
      ({UnorderedTree.node (Sum.inl a₀) F₀} : Forest (UnorderedTree (α ⊕ β)))
      {UnorderedTree.node (Sum.inl lbl) {v, p.2}} := by
  have := accessibleCount_im_of_cut lbl a₀ τ F₀ p hp v hv
  refine ⟨⟨by simp, ?_⟩, ?_⟩ <;>
  · simp only [Multiset.card_singleton, Multiset.map_singleton, Multiset.sum_singleton, this]
    omega

/-! ### Terms of Merge under deletion counting

On a full binary workspace, a term of Merge that takes an object whole extracts at most one tree
from each component, which costs two accessible terms (1.6.7). A term that takes neither object
whole diverges, whatever its extractions cost. -/

section Deletion

variable [DecidableEq (UnorderedTree α)] {F : Forest (UnorderedTree α)} {s : CutChoice α}
  {S S' X : UnorderedTree α}

private theorem hasExtractionCost_numEdges_merge_term (hF : ∀ T ∈ F, T.IsFullBinary)
    (hs : s ∈ forestCutChoicesG cutSummandsDN F) (hK : s.crown = {S, S'}) (h : s.numWhole ≠ 0) :
    s.HasExtractionCost UnorderedTree.numEdges 2 :=
  hasExtractionCost_numEdges_cutSummandsDN hF hs fun x hx hx0 ↦ by
    have := CutChoice.card_add_numWhole_le_card_crown hs hx hx0
    rw [hK] at this
    simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton] at this
    omega

/-- Under deletion counting, on a full binary workspace, a term of Merge satisfies Minimal Yield
    exactly when it takes both of its objects whole ([marcolli-chomsky-berwick-2025]
    Propositions 1.6.4 and 1.6.8, for `Δ^d`). -/
theorem MinimalYield.merge_term_numEdges_iff (hF : ∀ T ∈ F, T.IsFullBinary)
    (hs : s ∈ forestCutChoicesG cutSummandsDN F) (hK : s.crown = {S, S'})
    (hX : X.numEdges = S.numEdges + S'.numEdges + 2) :
    MinimalYield UnorderedTree.numEdges F ({X} + s.trunk) ↔ s.numWhole = 2 :=
  ⟨fun h ↦ (merge_term_iff_of_extraction_two hs
      (hasExtractionCost_numEdges_merge_term hF hs hK (h.numWhole_ne_zero hs)) hK hX).1 h,
    fun h ↦ (merge_term_iff_of_extraction_two hs
      (hasExtractionCost_numEdges_merge_term hF hs hK (by omega)) hK hX).2 h⟩

/-- Under deletion counting, on a full binary workspace, a term of Merge satisfies the weak form of
    Minimal Yield exactly when it takes an object whole. -/
theorem MinimalYieldWeak.merge_term_numEdges_iff (hF : ∀ T ∈ F, T.IsFullBinary)
    (hs : s ∈ forestCutChoicesG cutSummandsDN F) (hK : s.crown = {S, S'})
    (hX : X.numEdges = S.numEdges + S'.numEdges + 2) :
    MinimalYieldWeak UnorderedTree.numEdges F ({X} + s.trunk) ↔ s.numWhole ≠ 0 :=
  ⟨fun h ↦ h.numWhole_ne_zero hs, fun h ↦ (MinimalYieldWeak.merge_term_iff_of_extraction_two hs
    (hasExtractionCost_numEdges_merge_term hF hs hK h) hK hX).2 h⟩

end Deletion

/-! ### Terms of Merge under trace counting -/

section Trace

variable [DecidableEq (UnorderedTree (α ⊕ β))] {τ : UnorderedTree (α ⊕ β) → β}
  {F : Forest (UnorderedTree (α ⊕ β))} {s : CutChoice (α ⊕ β)}

/-- Under trace counting a term of Merge gains one accessible term for each object it takes whole
    ([marcolli-chomsky-berwick-2025] Propositions 1.6.4 and 1.6.8, for `Δ^c`). -/
theorem accessibleCount_merge_term (a : α) (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → x.1.value.isLeft) {S S' : UnorderedTree (α ⊕ β)}
    (hK : s.crown = {S, S'}) :
    Forest.accessibleCount ({UnorderedTree.node (Sum.inl a) {S, S'}} + s.trunk) =
      Forest.accessibleCount F + s.numWhole := by
  have h := sum_map_merge_term_add hs (hasExtractionCost_accessibleCount_cutSummandsCN hs hF) hK
    (accessibleCount_merge_of_crown_eq a hs hF hK)
  simp only [Forest.accessibleCount] at h ⊢
  omega

/-- Under trace counting every term of Merge grows the size `σ` of the workspace by exactly one. -/
theorem accessibleSize_merge_term (a : α) (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → x.1.value.isLeft) {S S' : UnorderedTree (α ⊕ β)}
    (hK : s.crown = {S, S'}) :
    Forest.accessibleSize ({UnorderedTree.node (Sum.inl a) {S, S'}} + s.trunk) =
      Forest.accessibleSize F + 1 := by
  have := accessibleCount_merge_term a hs hF hK
  have := card_singleton_add_trunk_add_numWhole hs (UnorderedTree.node (Sum.inl a) {S, S'})
  simp only [Forest.accessibleSize] at *
  omega

/-- Under trace counting, a Merge term satisfies Minimal Yield iff some merged object is an
unextracted workspace component ([marcolli-chomsky-berwick-2025] Proposition 1.6.8). -/
theorem MinimalYield.merge_term_accessibleCount_iff (a : α)
    (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → x.1.value.isLeft)
    {S S' : UnorderedTree (α ⊕ β)} (hK : s.crown = {S, S'}) :
    MinimalYield UnorderedTree.accessibleCount F
        ({UnorderedTree.node (Sum.inl a) {S, S'}} + s.trunk) ↔ s.numWhole ≠ 0 :=
  MinimalYield.merge_term_iff_of_extraction_one hs
    (hasExtractionCost_accessibleCount_cutSummandsCN hs hF) hK
    (accessibleCount_merge_of_crown_eq a hs hF hK)

/-- Under trace counting, a unit-stage term loses one accessible term unless `B` is an unextracted
workspace component ([marcolli-chomsky-berwick-2025] Remark 1.6.7, for `Δ^c`). -/
theorem accessibleCount_unit_term (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → x.1.value.isLeft) {B : UnorderedTree (α ⊕ β)}
    (hK : s.crown = {B}) :
    Forest.accessibleCount ({B} + s.trunk) + 1 = Forest.accessibleCount F + s.numWhole ∧
      Forest.accessibleSize ({B} + s.trunk) = Forest.accessibleSize F := by
  have h := sum_map_unit_term_add hs (hasExtractionCost_accessibleCount_cutSummandsCN hs hF) hK
  have := card_singleton_add_trunk_add_numWhole hs B
  simp only [Forest.accessibleSize, Forest.accessibleCount, one_mul] at *
  omega

end Trace

end Minimalist
