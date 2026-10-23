module

public import Linglib.Core.Order.Minimals
public import Linglib.Semantics.Modality.OrderingSemantics
public import Linglib.Semantics.Dynamic.Consequence

/-!
# Expectation states

This file defines Veltman's expectation patterns and expectation states, the updates with
*normally φ* and *presumably φ*, and the necessity modals that Portner defines on such states.

An *expectation pattern* is a preorder on worlds, where `w ≤ v` means that `w` conforms to every
rule that `v` conforms to. Refining a pattern with a proposition takes its meet with the preorder
the proposition induces, and a pattern *respects* a proposition when refining with it changes
nothing; Veltman's defaults in a pattern are the nonempty propositions it respects. An *expectation
state* pairs a pattern with the agent's information. Asserting `φ` eliminates the worlds outside
`φ`, *normally φ* refines the pattern with `φ`, and *presumably φ* tests whether `φ` holds at the
optimal worlds, the minimal worlds of the information under the pattern. In Portner's account of
mood, assertion and promotion are the updates of the context set and of the To-Do List.

## Main definitions

* `ExpState.crit`, `ExpState.refine`: the pattern a proposition induces, and refinement by it.
* `ExpState.Respects`: refining the pattern with the proposition changes nothing.
* `ExpState`: a pattern with the agent's information; `init`, `optimal`, `assert`, `promote`.
* `ExpState.presumablyTest`, `ExpState.mightTest`: the tests *presumably φ* and *might φ*.
* `ExpState.boxCs`, `ExpState.boxLe`, `ExpState.localNecessity`: the three necessity modals.

## Main results

* `refine_empty`, `refine_univ`, `refine_idem`, `refine_mono`: the meet-semilattice laws.
* `le_iff_forall_respects`: a pattern is determined by the propositions it respects.
* `isAdditive_assert`, `isAdditive_promote`: assertion and promotion are additive.
* `le_assert_iff`, `isFixedPt_presumablyTest_iff`: acceptance as informational or preferential
  necessity.
* `normally_creates_respect`, `persistence_assert`, `persistence_normally`: expectations persist.
* `normally_presumably_succeeds`, `boxLe_of_respects`: *normally φ; presumably φ* passes.
* `conflicting_defaults_iff_agree`, `compatible_defaults_optimal`: conflict and reinforcement.
* `promote_respects_idempotent`, `promote_comm`: promotion is idempotent and commutative.
* `localNecessity_iff_boxLe`: with a most normal world, local necessity is preferential necessity.

## Implementation notes

Veltman's patterns are coherent, and his update with *normally φ* crashes when no normal world of
the pattern is a `φ`-world. Here promotion refines unconditionally, so a conflicting rule shows up
as a failed acceptability condition rather than a crash. The crashing update, with the restricted
rules and expectation frames of section 4, is in `Studies/Veltman1996.lean`. The preference
structures of Condoravdi and Lauer order propositions, one type level above the ordering of worlds
here.

## References

* [F. Veltman, *Defaults in Update Semantics* (1996)][veltman-1996]
* [P. Portner, *The Semantics of Imperatives within a Theory of Clause Types*
  (2004)][portner-2004]
* [P. Portner, *Mood* (2018)][portner-2018]
* [R. C. Stalnaker, *Assertion* (1978)][stalnaker-1978]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [D. F. Farkas, *Assertion, belief and mood choice* (2003)][farkas-2003]
* [C. Condoravdi and S. Lauer, *Imperatives: Meaning and Illocutionary Force*
  (2012)][condoravdi-lauer-2012]
* [portner-rubinstein-2020]
-/

@[expose] public section

namespace DynamicSemantics

variable {W : Type*} {p q : Preorder W} {φ : W → Prop} {w v : W}

/-! ### Expectation patterns -/

namespace ExpState

/-- The criterion pattern of `φ` ranks `w` below `v` when `φ v` implies `φ w`. It is defined
directly rather than through `Preorder.ofCriteria`, so that refinement reduces definitionally to
a conjunction. -/
@[reducible] def crit (φ : W → Prop) : Preorder W :=
  Preorder.ofLE (fun w v ↦ φ v → φ w) (fun _ ↦ id) (fun _ _ _ hab hbc h ↦ hab (hbc h))

theorem crit_le : (crit φ).le w v ↔ (φ v → φ w) := Iff.rfl

theorem crit_const (b : Prop) : crit (W := W) (fun _ ↦ b) = ⊤ :=
  le_antisymm le_top fun _ _ _ ↦ id

/-- The refinement of the pattern `p` with `φ` keeps the pairs of `p` that do not rank a world
outside `φ` below a world inside it. It is the meet of `p` with the criterion pattern of `φ`. -/
@[reducible] def refine (p : Preorder W) (φ : W → Prop) : Preorder W := p ⊓ crit φ

theorem refine_le : (refine p φ).le w v ↔ p.le w v ∧ (φ v → φ w) := Iff.rfl

theorem refine_empty (p : Preorder W) : refine p (fun _ ↦ False) = p := by
  rw [refine, crit_const, inf_top_eq]

theorem refine_univ (p : Preorder W) : refine p (fun _ ↦ True) = p := by
  rw [refine, crit_const, inf_top_eq]

theorem refine_idem (p : Preorder W) (φ : W → Prop) : refine (refine p φ) φ = refine p φ :=
  inf_right_idem _ _

theorem refine_comm (p : Preorder W) (φ ψ : W → Prop) :
    refine (refine p φ) ψ = refine (refine p ψ) φ :=
  inf_right_comm _ _ _

theorem refine_mono (h : p ≤ q) (φ : W → Prop) : refine p φ ≤ refine q φ :=
  inf_le_inf_right _ h

/-- The pattern `p` respects `φ` when it never ranks a world outside `φ` below a world inside
it, that is, when it refines the criterion pattern of `φ`. -/
def Respects (p : Preorder W) (φ : W → Prop) : Prop := p ≤ crit φ

theorem respects_iff : Respects p φ ↔ ∀ ⦃w v⦄, p.le w v → φ v → φ w := Iff.rfl

theorem Respects.mono (h : Respects q φ) (hpq : p ≤ q) : Respects p φ := hpq.trans h

theorem respects_refine (p : Preorder W) (φ : W → Prop) : Respects (refine p φ) φ :=
  inf_le_right

theorem refine_eq_self_iff : refine p φ = p ↔ Respects p φ := inf_eq_left

/-- A pattern ranks `w` below `v` exactly when every proposition it respects that holds at `v`
holds at `w`. -/
theorem le_iff_forall_respects : p.le w v ↔ ∀ φ, Respects p φ → φ v → φ w :=
  ⟨fun h _ hφ ↦ hφ h, fun h ↦
    h (p.le · v) (fun _ _ hab hbv ↦ p.le_trans _ _ _ hab hbv) (p.le_refl v)⟩

/-- Under a total pattern that respects `φ`, the minimal worlds of a domain containing a
`φ`-world are `φ`-worlds. Without totality, a world outside `φ` can be minimal by being
incomparable with every `φ`-world. -/
theorem minimals_subset_of_respects {d : Set W} (hr : Respects p φ) (ht : Std.Total p.le)
    (hex : ∃ w ∈ d, φ w) : p.minimals d ⊆ {w ∈ d | φ w} := by
  intro w hw
  obtain ⟨v, hvd, hφv⟩ := hex
  refine ⟨hw.1, ?_⟩
  rcases ht.total w v with hwv | hvw
  · exact hr hwv hφv
  · exact hr (hw.2 hvd hvw) hφv

/-- Refining the pattern under which all worlds are equally normal with `φ` makes the minimal
worlds of a domain containing a `φ`-world exactly its `φ`-worlds. -/
theorem minimals_refine_top (φ : W → Prop) (d : Set W) (hex : ∃ w ∈ d, φ w) :
    (refine ⊤ φ).minimals d = {w ∈ d | φ w} := by
  ext w
  constructor
  · rintro ⟨hwd, hmin⟩
    obtain ⟨v, hvd, hφv⟩ := hex
    exact ⟨hwd, by_contra fun hnφw ↦
      hnφw ((hmin hvd ⟨trivial, fun h ↦ absurd h hnφw⟩).2 hφv)⟩
  · rintro ⟨hwd, hφw⟩
    exact ⟨hwd, fun _ _ _ ↦ ⟨trivial, fun _ ↦ hφw⟩⟩

end ExpState

/-! ### Expectation states -/

/-- An expectation state pairs the agent's information, the worlds compatible with what is
known, with an expectation pattern on worlds. -/
@[ext]
structure ExpState (W : Type*) where
  /-- The worlds compatible with the agent's information. -/
  info : Set W
  /-- The expectation pattern. -/
  order : Preorder W

namespace ExpState

/-- In the initial state all worlds are possible and equally normal. -/
def init : ExpState W where
  info := Set.univ
  order := ⊤

/-- The optimal worlds of a state are the most normal worlds compatible with the agent's
information. -/
def optimal (σ : ExpState W) : Set W := σ.order.minimals σ.info

/-- Informational necessity `□_cs` holds of `p` when `p` holds at every world of the information
state. This is entailment by the Stalnakerian context set and Portner's semantics of *believe*. -/
def boxCs (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.info, p w

/-- Preferential necessity `□_≤` holds of `p` when `p` holds at every optimal world, the worlds
with no better-ranked competitor. This is Portner's semantics of *want*, the Kratzerian deontic
and bouletic necessity, and the condition that *presumably* tests. -/
def boxLe (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.optimal, p w

/-- Local necessity holds of `p` when some world of the information sees only `p`-worlds among the
worlds of the information at least as normal as itself, so that `p` holds throughout a branch of
the pattern. This is good possibility in ordering semantics, Portner and Rubinstein's force of the
subjunctive. -/
def localNecessity (σ : ExpState W) (p : W → Prop) : Prop :=
  OrderingSemantics.IsGoodPossibility σ.order σ.info {v | p v}

/-! ### Update operations -/

/-- Assertion eliminates the worlds outside `φ` and leaves the pattern alone. -/
def assert (σ : ExpState W) (φ : W → Prop) : ExpState W :=
  ⟨{ w ∈ σ.info | φ w }, σ.order⟩

/-- Promotion, the update with *normally φ*, refines the pattern with `φ` and leaves the
information alone, so the agent learns that `φ` is expected and not that it is true. -/
def promote (σ : ExpState W) (φ : W → Prop) : ExpState W :=
  ⟨σ.info, refine σ.order φ⟩

section Classical
open Classical

/-- The test *presumably φ* passes when every optimal world satisfies `φ`, and otherwise empties
the information. -/
noncomputable def presumablyTest (φ : W → Prop) (σ : ExpState W) : ExpState W :=
  if ∀ w ∈ σ.optimal, φ w then σ else ⟨∅, σ.order⟩

/-- The test *might φ* passes when the information contains a `φ`-world, and otherwise empties
the information. The pattern plays no role. -/
noncomputable def mightTest (φ : W → Prop) (σ : ExpState W) : ExpState W :=
  if ∃ w ∈ σ.info, φ w then σ else ⟨∅, σ.order⟩

end Classical

/-! ### Basic properties -/

@[simp] theorem assert_info (σ : ExpState W) (φ : W → Prop) :
    (σ.assert φ).info = { w ∈ σ.info | φ w } := rfl

@[simp] theorem assert_order (σ : ExpState W) (φ : W → Prop) :
    (σ.assert φ).order = σ.order := rfl

@[simp] theorem promote_info (σ : ExpState W) (φ : W → Prop) :
    (σ.promote φ).info = σ.info := rfl

@[simp] theorem promote_order (σ : ExpState W) (φ : W → Prop) :
    (σ.promote φ).order = refine σ.order φ := rfl

theorem assert_info_subset (σ : ExpState W) (φ : W → Prop) :
    (σ.assert φ).info ⊆ σ.info := fun _ hw ↦ hw.1

/-! Expectation states are ordered componentwise, with more constrained states below less
constrained ones, as finer setoids lie below coarser ones; `init` is the top. Veltman orders states
the other way, with the same content. Both updates are additive: they meet the input with the
update of `init`. So they are deflationary, monotone, idempotent and persistent, and Veltman's
acceptance of `φ` in `σ` (updating `σ` with `φ` returns `σ`) is the fixpoint condition
`σ ≤ σ[φ]`. -/

instance : PartialOrder (ExpState W) where
  le σ τ := σ.info ⊆ τ.info ∧ σ.order ≤ τ.order
  le_refl _ := ⟨subset_rfl, le_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ExpState.ext (h₁.1.antisymm h₂.1) (h₁.2.antisymm h₂.2)

instance : SemilatticeInf (ExpState W) where
  inf σ τ := ⟨σ.info ∩ τ.info, σ.order ⊓ τ.order⟩
  inf_le_left _ _ := ⟨Set.inter_subset_left, inf_le_left⟩
  inf_le_right _ _ := ⟨Set.inter_subset_right, inf_le_right⟩
  le_inf _ _ _ h₁ h₂ := ⟨Set.subset_inter h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩

instance : OrderTop (ExpState W) where
  top := init
  le_top _ := ⟨Set.subset_univ _, le_top⟩

theorem le_iff {σ τ : ExpState W} :
    σ ≤ τ ↔ σ.info ⊆ τ.info ∧ σ.order ≤ τ.order := Iff.rfl

theorem top_eq_init : (⊤ : ExpState W) = init := rfl

theorem isAdditive_assert (φ : W → Prop) : IsAdditive (ExpState.assert · φ) := fun _ ↦
  ExpState.ext (Set.ext fun _ ↦ ⟨fun ⟨hw, hφ⟩ ↦ ⟨hw, trivial, hφ⟩, fun ⟨hw, _, hφ⟩ ↦ ⟨hw, hφ⟩⟩)
    (inf_top_eq _).symm

theorem isAdditive_promote (φ : W → Prop) : IsAdditive (ExpState.promote · φ) := fun σ ↦
  ExpState.ext (Set.inter_univ _).symm (congrArg (σ.order ⊓ ·) (top_inf_eq (crit φ)).symm)

theorem assert_le_self (σ : ExpState W) (φ : W → Prop) : σ.assert φ ≤ σ :=
  ⟨σ.assert_info_subset φ, le_refl _⟩

theorem promote_le_self (σ : ExpState W) (φ : W → Prop) : σ.promote φ ≤ σ :=
  ⟨subset_rfl, inf_le_left⟩

theorem assert_mono {σ τ : ExpState W} (h : σ ≤ τ) (φ : W → Prop) :
    σ.assert φ ≤ τ.assert φ :=
  ⟨fun _ hw ↦ ⟨h.1 hw.1, hw.2⟩, h.2⟩

theorem promote_mono {σ τ : ExpState W} (h : σ ≤ τ) (φ : W → Prop) :
    σ.promote φ ≤ τ.promote φ :=
  ⟨h.1, refine_mono h.2 φ⟩

theorem mem_foldl_assert_info (ps : List (W → Prop)) (σ : ExpState W) (v : W) :
    v ∈ (ps.foldl ExpState.assert σ).info ↔ v ∈ σ.info ∧ ∀ p ∈ ps, p v := by
  induction ps generalizing σ with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [assert_info, Set.mem_ofPred_eq, List.mem_cons]
    constructor
    · rintro ⟨⟨hv, hp⟩, hps⟩
      exact ⟨hv, fun q hq ↦ hq.elim (fun h ↦ h ▸ hp) (hps q)⟩
    · rintro ⟨hv, hall⟩
      exact ⟨⟨hv, hall p (Or.inl rfl)⟩, fun q hq ↦ hall q (Or.inr hq)⟩

theorem foldl_promote_order_le (ps : List (W → Prop)) (σ : ExpState W) (w v : W) :
    (ps.foldl ExpState.promote σ).order.le w v ↔
      σ.order.le w v ∧ ∀ p ∈ ps, p v → p w := by
  induction ps generalizing σ with
  | nil => exact ⟨fun h ↦ ⟨h, by simp⟩, And.left⟩
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨⟨hle, hp⟩, hps⟩
      exact ⟨hle, fun q hq ↦ hq.elim (fun h ↦ h ▸ hp) (hps q)⟩
    · rintro ⟨hle, hall⟩
      exact ⟨⟨hle, hall p (Or.inl rfl)⟩, fun q hq ↦ hall q (Or.inr hq)⟩

@[simp] theorem foldl_promote_info (ps : List (W → Prop)) (σ : ExpState W) :
    (ps.foldl ExpState.promote σ).info = σ.info := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih]; rfl

/-- A state accepts the assertion of `φ` exactly when `φ` already holds throughout its
information. -/
theorem le_assert_iff (σ : ExpState W) (φ : W → Prop) :
    σ ≤ σ.assert φ ↔ σ.boxCs φ :=
  ⟨fun h _ hw ↦ (h.1 hw).2, fun h ↦ ⟨fun _ hw ↦ ⟨hw, h _ hw⟩, le_refl _⟩⟩

/-- A state accepts the promotion of `φ` exactly when its pattern already respects `φ`. This is
support for the preferential component, distinct from truth at the optimal worlds. -/
theorem le_promote_iff (σ : ExpState W) (φ : W → Prop) :
    σ ≤ σ.promote φ ↔ Respects σ.order φ :=
  ⟨fun h ↦ h.2.trans inf_le_right, fun h ↦ ⟨subset_rfl, le_inf (le_refl _) h⟩⟩

theorem presumably_isTest (φ : W → Prop) (σ : ExpState W) :
    (presumablyTest φ σ).info = σ.info ∨ (presumablyTest φ σ).info = ∅ := by
  unfold presumablyTest; split <;> simp

/-- A state accepts *presumably φ* exactly when `φ` is preferentially necessary in it. -/
theorem isFixedPt_presumablyTest_iff {σ : ExpState W} :
    Function.IsFixedPt (presumablyTest φ) σ ↔ σ.boxLe φ := by
  unfold Function.IsFixedPt presumablyTest
  split_ifs with h
  · exact iff_of_true rfl h
  · refine iff_of_false (fun he ↦ h fun w hw ↦ ?_) h
    rw [← he] at hw
    exact absurd hw.1 (Set.notMem_empty w)

theorem might_isTest (φ : W → Prop) (σ : ExpState W) :
    (mightTest φ σ).info = σ.info ∨ (mightTest φ σ).info = ∅ := by
  unfold mightTest; split <;> simp

theorem mightTest_preserves_order (φ : W → Prop) (σ : ExpState W) :
    (mightTest φ σ).order = σ.order := by
  unfold mightTest; split <;> rfl

theorem presumablyTest_preserves_order (φ : W → Prop) (σ : ExpState W) :
    (presumablyTest φ σ).order = σ.order := by
  unfold presumablyTest; split <;> rfl

/-! ### "Normally p; presumably p" succeeds -/

/-- After *normally φ* from a state with no expectations, the test *presumably φ* passes,
provided the information contains a `φ`-world. -/
theorem normally_presumably_succeeds (φ : W → Prop) (d : Set W)
    (hex : ∃ w ∈ d, φ w) :
    let σ : ExpState W := ⟨d, ⊤⟩
    presumablyTest φ (σ.promote φ) = σ.promote φ := by
  simp only [presumablyTest, ExpState.promote, ExpState.optimal]
  rw [ite_eq_left]
  intro w hw
  rw [minimals_refine_top φ d hex] at hw
  exact hw.2

/-! ### Persistence -/

/-- Asserting any `ψ` preserves respect for `φ`, so learning new facts does not undo
expectations. -/
theorem persistence_assert (σ : ExpState W) (φ ψ : W → Prop)
    (h : Respects σ.order φ) :
    Respects (σ.assert ψ).order φ := h

/-- Promoting any `ψ` preserves respect for `φ`, so later defaults do not undo earlier
ones. -/
theorem persistence_normally (σ : ExpState W) (φ ψ : W → Prop)
    (h : Respects σ.order φ) :
    Respects (σ.promote ψ).order φ :=
  h.mono inf_le_left

/-- After *normally φ* the pattern respects `φ`. With persistence, the promotion creates a
permanent expectation. -/
theorem normally_creates_respect (σ : ExpState W) (φ : W → Prop) :
    Respects (σ.promote φ).order φ :=
  respects_refine σ.order φ

/-! ### Idempotency and commutativity -/

theorem promote_respects_idempotent (σ : ExpState W) (φ : W → Prop)
    (h : Respects σ.order φ) :
    σ.promote φ = σ := by
  show ExpState.mk σ.info (refine σ.order φ) = σ
  congr 1
  exact refine_eq_self_iff.2 h

theorem promote_promote_self (σ : ExpState W) (φ : W → Prop) :
    (σ.promote φ).promote φ = σ.promote φ :=
  promote_respects_idempotent _ φ (normally_creates_respect σ φ)

theorem promote_comm (σ : ExpState W) (φ ψ : W → Prop) :
    (σ.promote φ).promote ψ = (σ.promote ψ).promote φ :=
  congrArg (ExpState.mk σ.info) (refine_comm σ.order φ ψ)

/-! ### Conflicting defaults -/

/-- After *normally φ* and *normally not φ* the pattern relates two worlds only when they agree
on `φ`, so neither *presumably φ* nor *presumably not φ* passes. The Nixon diamond, where
conditional defaults conflict, needs the expectation frames of the paper's section 4. -/
theorem conflicting_defaults_le (φ : W → Prop) (w v : W) :
    (refine (refine ⊤ φ) (fun x ↦ ¬φ x)).le w v ↔ (φ v → φ w) ∧ (¬φ v → ¬φ w) := by
  rw [refine_le, refine_le]
  exact ⟨fun ⟨⟨_, h1⟩, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨⟨trivial, h1⟩, h2⟩⟩

/-- Under two conflicting defaults `w` is at least as normal as `v` exactly when they agree on
`φ`. -/
theorem conflicting_defaults_iff_agree (φ : W → Prop) (w v : W) :
    (refine (refine ⊤ φ) (fun x ↦ ¬φ x)).le w v ↔ (φ w ↔ φ v) := by
  rw [conflicting_defaults_le]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨fun hw ↦ by_contra (fun hv ↦ h2 hv hw), h1⟩
  · intro ⟨h1, h2⟩
    exact ⟨h2, fun hv hw ↦ hv (h1 hw)⟩

/-! ### Compatible defaults -/

/-- When `φ` implies `ψ`, promoting both makes the `φ`-worlds optimal, so the two expectations
reinforce each other. -/
theorem compatible_defaults_optimal (φ ψ : W → Prop) (d : Set W)
    (hφψ : ∀ w, φ w → ψ w) (hex : ∃ w ∈ d, φ w) :
    (refine (refine ⊤ ψ) φ).minimals d ⊆ { w ∈ d | φ w } := by
  intro w hw
  obtain ⟨hwd, hopt⟩ := hw
  obtain ⟨v, hvd, hφv⟩ := hex
  refine ⟨hwd, by_contra fun hnφw ↦ ?_⟩
  have hle : (refine (refine ⊤ ψ) φ).le v w :=
    ⟨⟨trivial, fun _ ↦ hφψ v hφv⟩, fun h ↦ absurd h hnφw⟩
  exact hnφw ((hopt hvd hle).2 hφv)

/-! ### Necessity modals

Portner's mood semantics works with a context set and an ordering of worlds, that is, an
expectation state with `info` as the Stalnakerian context set and `order` as the Kratzerian
ordering source. A state accepts a sentence when updating with it changes nothing. Accepting an
assertion is informational necessity (`le_assert_iff`), and accepting *presumably φ* is
preferential necessity (`isFixedPt_presumablyTest_iff`); Portner, following Farkas, states these
conditions for *believe* and *want*. -/

theorem boxCs_mono (σ : ExpState W) (p q : W → Prop)
    (h : ∀ w, p w → q w) : σ.boxCs p → σ.boxCs q :=
  fun hp w hw ↦ h w (hp w hw)

theorem boxLe_mono (σ : ExpState W) (p q : W → Prop)
    (h : ∀ w, p w → q w) : σ.boxLe p → σ.boxLe q :=
  fun hp w hw ↦ h w (hp w hw)

/-- Asserting `p` makes `p` informationally necessary, which is Stalnaker's principle that an
assertion becomes common ground. -/
theorem boxCs_assert_self (σ : ExpState W) (p : W → Prop) :
    (σ.assert p).boxCs p :=
  fun _ hw ↦ hw.2

/-- Refining the state strengthens informational necessity. `boxLe` admits no parallel result, since
refinement changes which worlds are best, in either direction. -/
theorem boxCs_anti {σ τ : ExpState W} (h : σ ≤ τ) (p : W → Prop) :
    τ.boxCs p → σ.boxCs p :=
  fun hbox w hw ↦ hbox w (h.1 hw)

/-- If the pattern respects `p` and is total and the information has a `p`-world, then `p` is
preferentially necessary, so *presumably p* passes. This is Veltman's *normally φ ⊩ presumably φ*,
and it connects Portner's fixpoint semantics for *want* with his modal semantics. The converse
fails, and without totality so does this direction, as in Veltman's ambiguous states. -/
theorem boxLe_of_respects (σ : ExpState W) (p : W → Prop)
    (hresp : Respects σ.order p) (hconn : Std.Total σ.order.le)
    (hex : ∃ w ∈ σ.info, p w) : σ.boxLe p :=
  fun _ hw ↦ (minimals_subset_of_respects hresp hconn hex hw).2

theorem localNecessity_mono (σ : ExpState W) (p q : W → Prop)
    (h : ∀ w, p w → q w) : σ.localNecessity p → σ.localNecessity q :=
  fun hp ↦ hp.mono fun w ↦ h w

/-- When the information has a world at least as normal as all of its worlds, local necessity is
preferential necessity. Without one they come apart, as when two incomparable optimal worlds each
make a different proposition locally necessary while neither is preferentially necessary. -/
theorem localNecessity_iff_boxLe {σ : ExpState W} {b : W} (hb : b ∈ σ.info)
    (hleast : ∀ v ∈ σ.info, σ.order.le b v) (p : W → Prop) :
    σ.localNecessity p ↔ σ.boxLe p :=
  (OrderingSemantics.isGoodPossibility_iff_of_least hb hleast).trans
    (OrderingSemantics.minimals_subset_iff_of_least hb hleast).symm

end ExpState

end DynamicSemantics
