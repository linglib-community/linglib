module

public import Linglib.Semantics.Modality.Background
public import Linglib.Semantics.Modality.OrderingSemantics
public import Linglib.Semantics.Dynamic.Consequence

/-!
# Ordered information states

An ordered information state pairs a set of worlds, the information state of propositional update
semantics (`DynamicSemantics.State.worldOrderIso`), with a preorder ranking worlds: Veltman's
expectation pattern, the ordering of Portner's To-Do List, or a Kratzer ordering source. The states
form a complete lattice whose top is Veltman's minimal state and whose bottom is his absurd state.
Asserting `φ` and *normally φ* meet a state with [their static
meanings](##DynamicSemantics.OrderedInformationState.isAdditive_promote); a state accepts *normally
φ* when [the `φ`-worlds form a lower set of its
pattern](##DynamicSemantics.OrderedInformationState.isFixedPt_promote_iff), and rules [rank worlds
as premises do](##DynamicSemantics.OrderedInformationState.foldl_promote_order). *Presumably φ*
tests `φ` at the optimal worlds, where Portner's preferential necessity is evaluated.

## Implementation notes

States are ordered by inclusion in both coordinates, so that a state with more information and
more expectations lies lower; Veltman orders them the other way. Assertion and promotion never
crash. Veltman identifies every state with empty information or an incoherent pattern with the
absurd state, and his update with *normally φ* crashes when no normal world is a `φ`-world, so on
a text that crashes his validity₁ and the one here can differ. His crashing updates are in
`Studies/Veltman1996.lean`, as those of his section 4 on general rules.

## TODO

Rank the points of the states of `Dynamic/State.lean`, world–assignment pairs, rather than bare
worlds, so that a default can bind discourse referents, combining Veltman's defaults with the
coreference of Groenendijk, Stokhof and Veltman.

## References

* [F. Veltman, *Defaults in Update Semantics* (1996)][veltman-1996]
* [groenendijk-stokhof-veltman-1996]
* [P. Portner, *The Semantics of Imperatives within a Theory of Clause Types*
  (2004)][portner-2004]
* [P. Portner, *Mood* (2018)][portner-2018]
* [R. C. Stalnaker, *Assertion* (1978)][stalnaker-1978]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [D. F. Farkas, *Assertion, belief and mood choice* (2003)][farkas-2003]
* [portner-rubinstein-2020]
-/

@[expose] public section

namespace DynamicSemantics

open Function

/-- An ordered information state pairs the agent's information, the worlds compatible with what
is known, with a preorder ranking worlds. -/
@[ext]
structure OrderedInformationState (W : Type*) where
  /-- The worlds compatible with the agent's information. -/
  info : Set W
  /-- The preorder ranking worlds, an expectation pattern in Veltman's terms. -/
  order : Preorder W

namespace OrderedInformationState

variable {W : Type*} {σ τ : OrderedInformationState W} {φ : W → Prop}

/-! ### The lattice of states -/

instance : LE (OrderedInformationState W) := ⟨fun σ τ ↦ σ.info ⊆ τ.info ∧ σ.order ≤ τ.order⟩
instance : LT (OrderedInformationState W) := ⟨fun σ τ ↦ σ ≤ τ ∧ ¬τ ≤ σ⟩
instance : Max (OrderedInformationState W) := ⟨fun σ τ ↦ ⟨σ.info ∪ τ.info, σ.order ⊔ τ.order⟩⟩
instance : Min (OrderedInformationState W) := ⟨fun σ τ ↦ ⟨σ.info ∩ τ.info, σ.order ⊓ τ.order⟩⟩
instance : SupSet (OrderedInformationState W) := ⟨fun S ↦ ⟨⋃ σ ∈ S, σ.info, ⨆ σ ∈ S, σ.order⟩⟩
instance : InfSet (OrderedInformationState W) := ⟨fun S ↦ ⟨⋂ σ ∈ S, σ.info, ⨅ σ ∈ S, σ.order⟩⟩

/-- The top is Veltman's minimal state, in which every world is possible and all are equally
normal. -/
instance : Top (OrderedInformationState W) := ⟨⟨Set.univ, ⊤⟩⟩

/-- The bottom is Veltman's absurd state, in which no world is possible and the pattern relates
each world only to itself. -/
instance : Bot (OrderedInformationState W) := ⟨⟨∅, ⊥⟩⟩

/-- Ordered information states form a complete lattice, the product of the lattice of sets of
worlds and the lattice of preorders. -/
instance : CompleteLattice (OrderedInformationState W) :=
  Injective.completeLattice (fun σ ↦ (σ.info, σ.order))
    (fun _ _ h ↦ OrderedInformationState.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    Iff.rfl Iff.rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ by simp only [Prod.iSup_mk]; rfl)
    (fun _ ↦ by simp only [Prod.iInf_mk]; rfl) rfl rfl

theorem le_iff : σ ≤ τ ↔ σ.info ⊆ τ.info ∧ σ.order ≤ τ.order := Iff.rfl

@[simp] theorem info_top : (⊤ : OrderedInformationState W).info = Set.univ := rfl
@[simp] theorem order_top : (⊤ : OrderedInformationState W).order = ⊤ := rfl
@[simp] theorem info_bot : (⊥ : OrderedInformationState W).info = ∅ := rfl
@[simp] theorem order_bot : (⊥ : OrderedInformationState W).order = ⊥ := rfl
@[simp] theorem info_inf : (σ ⊓ τ).info = σ.info ∩ τ.info := rfl
@[simp] theorem order_inf : (σ ⊓ τ).order = σ.order ⊓ τ.order := rfl

/-! ### Optimal worlds and necessity modals -/

/-- The optimal worlds of a state are the most normal worlds compatible with the agent's
information. -/
def optimal (σ : OrderedInformationState W) : Set W := σ.order.minimals σ.info

/-- Informational necessity `□_cs` holds of `p` when `p` holds at every world of the information
state. This is entailment by the Stalnakerian context set and Portner's semantics of *believe*. -/
def boxCs (σ : OrderedInformationState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.info, p w

/-- Preferential necessity `□_≤` holds of `p` when `p` holds at every optimal world, the worlds
with no better-ranked competitor. This is Portner's semantics of *want*, the Kratzerian deontic
and bouletic necessity, and the condition that *presumably* tests. -/
def boxLe (σ : OrderedInformationState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.optimal, p w

/-- Local necessity holds of `p` when some world of the information sees only `p`-worlds among the
worlds of the information at least as normal as itself, so that `p` holds throughout a branch of
the pattern. This is good possibility in ordering semantics, Portner and Rubinstein's force of the
subjunctive. -/
def localNecessity (σ : OrderedInformationState W) (p : W → Prop) : Prop :=
  OrderingSemantics.IsGoodPossibility σ.order σ.info {v | p v}

/-- When the information has a world at least as normal as all of its worlds, local necessity is
preferential necessity. Without one they come apart, as when two incomparable optimal worlds each
make a different proposition locally necessary while neither is preferentially necessary. -/
theorem localNecessity_iff_boxLe {b : W} (hb : b ∈ σ.info)
    (hleast : ∀ v ∈ σ.info, σ.order.le b v) (p : W → Prop) :
    σ.localNecessity p ↔ σ.boxLe p :=
  (OrderingSemantics.isGoodPossibility_iff_of_least hb hleast).trans
    (OrderingSemantics.minimals_subset_iff_of_least hb hleast).symm

/-! ### Updates -/

/-- Assertion eliminates the worlds outside `φ` and leaves the pattern alone. -/
def assert (σ : OrderedInformationState W) (φ : W → Prop) : OrderedInformationState W :=
  ⟨{w ∈ σ.info | φ w}, σ.order⟩

/-- Promotion, the update with *normally φ*, meets the pattern with the ordering of the single
premise `φ` and leaves the information alone, so the agent learns that `φ` is expected and not
that it is true. The meet removes the pairs of the pattern that rank a world outside `φ` below a
world inside it, Veltman's refinement of the pattern with `φ` (Definition 3.5), so that his
Proposition 3.6 follows from the laws of the meet and `Preorder.ofCriterion_const`. -/
def promote (σ : OrderedInformationState W) (φ : W → Prop) : OrderedInformationState W :=
  ⟨σ.info, σ.order ⊓ .ofCriterion φ⟩

open Classical in
/-- The test *presumably φ* passes when `φ` holds at every optimal world and otherwise yields the
absurd state. -/
noncomputable def presumablyTest (φ : W → Prop) (σ : OrderedInformationState W) :
    OrderedInformationState W :=
  if σ.boxLe φ then σ else ⊥

@[simp] theorem assert_info (σ : OrderedInformationState W) (φ : W → Prop) :
    (σ.assert φ).info = {w ∈ σ.info | φ w} := rfl

@[simp] theorem assert_order (σ : OrderedInformationState W) (φ : W → Prop) :
    (σ.assert φ).order = σ.order := rfl

@[simp] theorem promote_info (σ : OrderedInformationState W) (φ : W → Prop) :
    (σ.promote φ).info = σ.info := rfl

@[simp] theorem promote_order (σ : OrderedInformationState W) (φ : W → Prop) :
    (σ.promote φ).order = σ.order ⊓ .ofCriterion φ := rfl

/-- Assertion meets a state with the static meaning of `φ`, the update of the minimal state. -/
theorem isAdditive_assert (φ : W → Prop) : IsAdditive (assert · φ) := fun _ ↦
  OrderedInformationState.ext
    (Set.ext fun _ ↦ ⟨fun ⟨hw, hφ⟩ ↦ ⟨hw, trivial, hφ⟩, fun ⟨hw, _, hφ⟩ ↦ ⟨hw, hφ⟩⟩)
    (inf_top_eq _).symm

/-- Promotion meets a state with the static meaning of *normally φ*, the update of the minimal
state, so that rules, like facts, carry context-independent information. -/
theorem isAdditive_promote (φ : W → Prop) : IsAdditive (promote · φ) := fun σ ↦
  OrderedInformationState.ext (Set.inter_univ _).symm (congrArg (σ.order ⊓ ·) (top_inf_eq _).symm)

/-! ### Acceptance -/

/-- A state accepts the assertion of `φ` exactly when `φ` is informationally necessary in it. -/
theorem isFixedPt_assert_iff : IsFixedPt (assert · φ) σ ↔ σ.boxCs φ :=
  (isAdditive_assert φ).isFixedPt_iff.trans
    ⟨fun h _ hw ↦ (h.1 hw).2, fun h ↦ ⟨fun _ hw ↦ ⟨trivial, h _ hw⟩, le_top⟩⟩

/-- A state accepts *normally φ* exactly when the `φ`-worlds form a lower set of its pattern
(`Preorder.le_ofCriterion_iff_isLowerSet`), so that no world outside `φ` is ranked below a world
inside it: a nonempty such `φ` is what Veltman calls a default of the pattern. A pattern is
determined by its defaults, his Proposition 3.7, by `Preorder.le_iff_forall_le_ofCriterion`. -/
theorem isFixedPt_promote_iff : IsFixedPt (promote · φ) σ ↔ σ.order ≤ .ofCriterion φ :=
  ⟨fun h ↦ inf_eq_left.1 (congrArg order h),
    fun h ↦ OrderedInformationState.ext rfl (inf_eq_left.2 h)⟩

/-- A state accepts *presumably φ* exactly when `φ` is preferentially necessary in it. -/
theorem isFixedPt_presumablyTest_iff : IsFixedPt (presumablyTest φ) σ ↔ σ.boxLe φ := by
  refine ⟨fun h ↦ by_contra fun hφ ↦ hφ ?_, fun h ↦ ite_eq_left h⟩
  rw [← show ⊥ = σ from (ite_eq_right hφ).symm.trans h]
  exact fun _ hw ↦ absurd hw.1 (Set.notMem_empty _)

/-- After *normally φ* in a state without expectations whose information has a `φ`-world, the
optimal worlds are the `φ`-worlds of the information, so *presumably φ* passes. -/
theorem optimal_promote_of_order_eq_top (h : σ.order = ⊤) (hex : ∃ w ∈ σ.info, φ w) :
    (σ.promote φ).optimal = {w ∈ σ.info | φ w} := by
  rw [optimal, promote_order, promote_info, h, top_inf_eq, Preorder.minimals_ofCriterion hex]

/-! ### Texts of facts and of rules -/

theorem mem_foldl_assert_info (ps : List (W → Prop)) (σ : OrderedInformationState W) (v : W) :
    v ∈ (ps.foldl assert σ).info ↔ v ∈ σ.info ∧ ∀ p ∈ ps, p v := by
  induction ps generalizing σ with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [assert_info, Set.mem_ofPred_eq, List.forall_mem_cons, and_assoc]

@[simp] theorem foldl_promote_info (ps : List (W → Prop)) (σ : OrderedInformationState W) :
    (ps.foldl promote σ).info = σ.info := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih]; rfl

/-- Promoting a list of propositions meets the pattern with the ordering they induce as premises,
so that a pattern learnt from the minimal state ranks `w` below `v` when every rule that holds
at `v` holds at `w`, as Veltman glosses patterns. -/
theorem foldl_promote_order (ps : List (W → Prop)) (σ : OrderedInformationState W) :
    (ps.foldl promote σ).order = σ.order ⊓ Modality.premisePreorder {p | p ∈ ps} := by
  induction ps generalizing σ with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, promote_order, show {q | q ∈ p :: ps} = insert p {q | q ∈ ps} by
      ext; simp, Modality.premisePreorder_insert, inf_assoc, inf_comm (Preorder.ofCriterion p)]

end OrderedInformationState

end DynamicSemantics
