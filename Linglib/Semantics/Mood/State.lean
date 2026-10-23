/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.QUD.Issue
public import Linglib.Semantics.Dynamic.Expectation
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Questions.Partition.Inquisitive
public import Mathlib.Tactic.DeriveFintype

/-!
# The mood state

A mood state is Portner's partially ordered set of worlds, a context set with a preorder on
worlds, together with a partition of the worlds that records the open question. The first two
coordinates form Veltman's expectation state `DynamicSemantics.ExpState`, with its updates
`assert` and `promote` and its modals `boxCs` and `boxLe`. For interrogatives Portner (p. 237)
offers two options: replace the context set with a partition of it, or add a question set as a
third coordinate, as in the discourse contexts of Roberts and of his own earlier work. The mood
state takes the second option, with the question set reduced to the meet of its partitions.

Each of the three updates meets one coordinate with a fixed content. The modal `boxAns` holds
of what the open question settles within the context set.

## Main definitions

* `Mood.State`: an expectation state together with an inquiry partition.
* `Mood.Component`, `Mood.Component.boxOn`: the coordinates of a mood state and their modals,
  by which Portner classifies the mood-bearing categories.
* `Mood.State.inquire`: the update that refines the inquiry with a question.
* `Mood.State.boxAns`: answerhood, constancy on the inquiry cells within the context set.
* `Mood.stateAt`: the expectation state that a Kratzer pair induces at a world.

## Main statements

* `Mood.State.boxAns_iff_le_relativeTo`: `boxAns p` holds exactly when the current issue
  entails the polar question whether `p` relative to the context set.
* `Mood.State.isAdditive_assert`, `Mood.State.isAdditive_promote`,
  `Mood.State.isAdditive_inquire`: the three updates are additive.
* `Mood.simpleNecessity_iff_boxCs`, `Mood.necessity_iff_boxLe`: Kratzer's simple and human
  necessity are the two modals of the induced state, as Portner glosses his (3).

## Implementation notes

* The `?`-update and `boxAns` are additions of this library; Portner leaves interrogatives open.
  Mari and Portner's discourse context likewise keeps the question under discussion as a component
  of its own beside the common ground.
* The inquiry is a partition. Questions that are not partitions, such as mention-some questions,
  live in `Question W`, into which `Question.fromSetoid` embeds the partitions.

## References

* [portner-2018]
* [mari-portner-2021]
* [veltman-1996]
* [roberts-1996]
* [roberts-2012]
* [portner-2004]
* [groenendijk-stokhof-1984]
* [kratzer-1981]
-/

@[expose] public section

namespace Mood

open DynamicSemantics

/-- A mood state is an expectation state together with an inquiry partition, the open question,
where `⊤` is no question. -/
@[ext]
structure State (W : Type*) extends ExpState W where
  /-- Two worlds are related when they answer the open question alike. -/
  inquiry : Setoid W

namespace State

variable {W : Type*}

/-- The mood state with no open question. -/
def ofExpState (σ : ExpState W) : State W :=
  { σ with inquiry := ⊤ }

@[simp] theorem ofExpState_toExpState (σ : ExpState W) :
    (ofExpState σ).toExpState = σ := rfl

@[simp] theorem ofExpState_inquiry (σ : ExpState W) :
    (ofExpState σ).inquiry = (⊤ : Setoid W) := rfl

/-! ### Updates -/

/-- Assertion eliminates the worlds outside `p` from the context set. -/
def assert (c : State W) (p : W → Prop) : State W :=
  { c.toExpState.assert p with inquiry := c.inquiry }

/-- Promotion refines the ordering with `p`. -/
def promote (c : State W) (p : W → Prop) : State W :=
  { c.toExpState.promote p with inquiry := c.inquiry }

/-- The `?`-update refines the inquiry with the question `q`. -/
def inquire (c : State W) (q : Setoid W) : State W :=
  { c with inquiry := c.inquiry ⊓ q }

@[simp] theorem assert_toExpState (c : State W) (p : W → Prop) :
    (c.assert p).toExpState = c.toExpState.assert p := rfl

@[simp] theorem assert_inquiry (c : State W) (p : W → Prop) :
    (c.assert p).inquiry = c.inquiry := rfl

@[simp] theorem promote_toExpState (c : State W) (p : W → Prop) :
    (c.promote p).toExpState = c.toExpState.promote p := rfl

@[simp] theorem promote_inquiry (c : State W) (p : W → Prop) :
    (c.promote p).inquiry = c.inquiry := rfl

@[simp] theorem inquire_toExpState (c : State W) (q : Setoid W) :
    (c.inquire q).toExpState = c.toExpState := rfl

@[simp] theorem inquire_inquiry (c : State W) (q : Setoid W) :
    (c.inquire q).inquiry = c.inquiry ⊓ q := rfl

@[simp] theorem assert_promote_comm (c : State W) (p q : W → Prop) :
    (c.assert p).promote q = (c.promote q).assert p := rfl

@[simp] theorem assert_inquire_comm (c : State W) (p : W → Prop) (q : Setoid W) :
    (c.assert p).inquire q = (c.inquire q).assert p := rfl

@[simp] theorem promote_inquire_comm (c : State W) (p : W → Prop) (q : Setoid W) :
    (c.promote p).inquire q = (c.inquire q).promote p := rfl

theorem inquire_inquire_self (c : State W) (q : Setoid W) :
    (c.inquire q).inquire q = c.inquire q :=
  congrArg (State.mk c.toExpState) (inf_right_idem _ _)

/-! ### Order

Mood states are ordered componentwise, a more constrained state lying below a less constrained
one, and the state with no information, no expectations and no question is the top. -/

instance : PartialOrder (State W) where
  le c₁ c₂ := c₁.toExpState ≤ c₂.toExpState ∧ c₁.inquiry ≤ c₂.inquiry
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ :=
    State.ext (congrArg ExpState.info (h₁.1.antisymm h₂.1))
      (congrArg ExpState.order (h₁.1.antisymm h₂.1)) (h₁.2.antisymm h₂.2)

instance : SemilatticeInf (State W) where
  inf c₁ c₂ := ⟨c₁.toExpState ⊓ c₂.toExpState, c₁.inquiry ⊓ c₂.inquiry⟩
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩
  le_inf _ _ _ h₁ h₂ := ⟨le_inf h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩

instance : OrderTop (State W) where
  top := ofExpState ⊤
  le_top _ := ⟨le_top, le_top⟩

theorem le_iff {c₁ c₂ : State W} :
    c₁ ≤ c₂ ↔ c₁.toExpState ≤ c₂.toExpState ∧ c₁.inquiry ≤ c₂.inquiry :=
  Iff.rfl

theorem isAdditive_assert (p : W → Prop) : IsAdditive (assert · p) := fun c ↦
  congrArg₂ State.mk (ExpState.isAdditive_assert p c.toExpState) (inf_top_eq _).symm

theorem isAdditive_promote (p : W → Prop) : IsAdditive (promote · p) := fun c ↦
  congrArg₂ State.mk (ExpState.isAdditive_promote p c.toExpState) (inf_top_eq _).symm

theorem isAdditive_inquire (q : Setoid W) : IsAdditive (inquire · q) := fun c ↦
  congrArg₂ State.mk (inf_top_eq _).symm (congrArg (c.inquiry ⊓ ·) (top_inf_eq q).symm)

theorem le_inquire_iff (c : State W) (q : Setoid W) :
    c ≤ c.inquire q ↔ c.inquiry ≤ q :=
  ⟨fun h ↦ h.2.trans inf_le_right, fun h ↦ ⟨le_rfl, le_inf le_rfl h⟩⟩

/-! ### Discourse projections -/

/-- The inquiry partition, read as an issue. -/
instance : Discourse.HasIssue (State W) W := ⟨fun c ↦ Question.fromSetoid c.inquiry⟩

@[simp] theorem toIssue_eq (c : State W) :
    Discourse.HasIssue.toIssue c = Question.fromSetoid c.inquiry := rfl

/-- The context set is the common ground, and `assert` is Stalnakerian on it. -/
instance : HasAssertion (State W) W where
  commonGround c := Filter.principal c.info
  initial := ⊤
  assert c φ := c.assert (· ∈ φ)
  commonGround_initial := Filter.principal_univ
  commonGround_assert c φ :=
    show Filter.principal {w ∈ c.info | w ∈ φ} = Filter.principal c.info ⊓ Filter.principal φ by
      rw [Set.sep_mem_eq, Filter.inf_principal]

@[simp] theorem commonGround_eq (c : State W) :
    HasCommonGround.commonGround c = Filter.principal c.info := rfl

@[simp] theorem contextSet_eq (c : State W) : HasCommonGround.contextSet c = c.info := by
  simp [HasCommonGround.contextSet]

/-! ### Answerhood -/

/-- Answerhood holds of `p` when `p` is constant on the part of each inquiry cell inside the
context set. Unlike `boxCs` and `boxLe` it is not upward monotone in `p`. -/
def boxAns (c : State W) (p : W → Prop) : Prop :=
  ∀ w v, w ∈ c.info → v ∈ c.info → c.inquiry w v → (p w ↔ p v)

theorem boxAns_iff_le_relativeTo (c : State W) (p : W → Prop) :
    c.boxAns p ↔ Question.fromSetoid c.inquiry ≤ (Question.polar {w | p w}).relativeTo c.info := by
  rw [Question.le_def]
  refine ⟨fun h s hs ↦ ?_, fun h w v hw hv hwv ↦ ?_⟩
  · rw [Question.mem_props, Question.mem_fromSetoid] at hs
    rw [Question.mem_props, Question.mem_relativeTo, Question.mem_polar]
    by_cases hp : ∃ x ∈ c.info ∩ s, p x
    · obtain ⟨x, hx, hpx⟩ := hp
      exact Or.inl fun y hy ↦ (h x y hx.1 hy.1 (hs x hx.2 y hy.2)).1 hpx
    · exact Or.inr fun y hy hpy ↦ hp ⟨y, hy, hpy⟩
  · have hs : ({w, v} : Set W) ∈ Question.fromSetoid c.inquiry := by
      rw [Question.mem_fromSetoid]
      rintro x (rfl | rfl) y (rfl | rfl)
      exacts [c.inquiry.refl' _, hwv, c.inquiry.symm' hwv, c.inquiry.refl' _]
    have := h hs
    rw [Question.mem_props, Question.mem_relativeTo, Question.mem_polar] at this
    rcases this with hsub | hsub
    · exact iff_of_true (hsub ⟨hw, Or.inl rfl⟩) (hsub ⟨hv, Or.inr rfl⟩)
    · exact iff_of_false (hsub ⟨hw, Or.inl rfl⟩) (hsub ⟨hv, Or.inr rfl⟩)

theorem boxAns_of_decides (c : State W) {p : W → Prop} (h : c.inquiry.Decides {w | p w}) :
    c.boxAns p :=
  fun _ _ _ _ hwv ↦ h.iff hwv

theorem boxAns_iff_decides {c : State W} (h : c.info = Set.univ) (p : W → Prop) :
    c.boxAns p ↔ c.inquiry.Decides {w | p w} := by
  rw [boxAns_iff_le_relativeTo, h, Question.relativeTo_univ, Question.decides_iff_fromSetoid_le]

theorem boxAns_anti {c₁ c₂ : State W} (h : c₁ ≤ c₂) (p : W → Prop) :
    c₂.boxAns p → c₁.boxAns p :=
  fun hbox w v hw hv hwv ↦ hbox w v (h.1.1 hw) (h.1.1 hv) (h.2 hwv)

/-! The propositions a state settles are closed under the Boolean connectives. -/

theorem boxAns_not (c : State W) (p : W → Prop) :
    c.boxAns p → c.boxAns (fun w ↦ ¬ p w) :=
  fun hp w v hw hv hwv ↦ not_congr (hp w v hw hv hwv)

theorem boxAns_and (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w ∧ q w) :=
  fun hp hq w v hw hv hwv ↦ and_congr (hp w v hw hv hwv) (hq w v hw hv hwv)

theorem boxAns_or (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w ∨ q w) :=
  fun hp hq w v hw hv hwv ↦ or_congr (hp w v hw hv hwv) (hq w v hw hv hwv)

theorem boxAns_imp (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w → q w) :=
  fun hp hq w v hw hv hwv ↦ imp_congr (hp w v hw hv hwv) (hq w v hw hv hwv)

/-! ### Answerhood is not informational necessity -/

/-- The state over `Bool` with every world in the context set and the finest inquiry. -/
def sepInquiry : State Bool where
  info := Set.univ
  order := ⊤
  inquiry := ⊥

/-- The proposition true at `false` alone. -/
def sepProp : Bool → Prop := fun w ↦ w = false

theorem boxAns_not_reducible_to_boxCs :
    ∃ (c : State Bool) (p : Bool → Prop), c.boxAns p ∧ ¬ c.toExpState.boxCs p :=
  ⟨sepInquiry, sepProp, fun w v _ _ hwv ↦ by rw [show w = v from hwv],
    fun h ↦ Bool.noConfusion (h true trivial)⟩

end State

/-! ### Components -/

/-- A coordinate of the mood state. Portner classifies a mood-bearing category by the coordinate
that the context selecting it quantifies over: the indicative and the declarative relate to the
context set, the subjunctive and the imperative to the ordering. -/
inductive Component where
  /-- The context set, `State.info`. -/
  | informational
  /-- The ordering, `State.order`. -/
  | preferential
  /-- The inquiry, `State.inquiry`. -/
  | inquisitive
  deriving DecidableEq, Repr, Fintype

variable {W : Type*}

/-- The necessity modal of a component is `boxCs`, `boxLe` or `boxAns`. -/
def Component.boxOn : Component → State W → (W → Prop) → Prop
  | .informational, c, p => c.toExpState.boxCs p
  | .preferential,  c, p => c.toExpState.boxLe p
  | .inquisitive,   c, p => c.boxAns p

@[simp] theorem boxOn_informational (c : State W) (p : W → Prop) :
    Component.informational.boxOn c p = c.toExpState.boxCs p := rfl

@[simp] theorem boxOn_preferential (c : State W) (p : W → Prop) :
    Component.preferential.boxOn c p = c.toExpState.boxLe p := rfl

@[simp] theorem boxOn_inquisitive (c : State W) (p : W → Prop) :
    Component.inquisitive.boxOn c p = c.boxAns p := rfl

/-! ### Kratzer backgrounds induce states

Portner glosses his (3): read as a modal base and an ordering source, the two coordinates make
`boxCs` simple necessity and `boxLe` human necessity. Read the other way, a Kratzer pair is a
world-indexed family of expectation states. -/

open Modality

variable (f g : Background W)

/-- The expectation state that a modal base and an ordering source induce at a world. -/
def stateAt (w : W) : ExpState W :=
  ⟨f.accessibleWorlds w, premisePreorder (g w)⟩

@[simp] theorem stateAt_info (w : W) : (stateAt f g w).info = f.accessibleWorlds w := rfl

@[simp] theorem stateAt_order (w : W) : (stateAt f g w).order = premisePreorder (g w) := rfl

theorem bestWorlds_eq_optimal (w : W) : bestWorlds f g w = (stateAt f g w).optimal := rfl

theorem simpleNecessity_iff_boxCs (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ (stateAt f g w).boxCs p :=
  Iff.rfl

theorem necessity_iff_boxLe (p : W → Prop) (w : W) :
    necessity f g p w ↔ (stateAt f g w).boxLe p :=
  Iff.rfl

theorem goodPossibility_iff_localNecessity (p : W → Prop) (w : W) :
    goodPossibility f g p w ↔ (stateAt f g w).localNecessity p :=
  Iff.rfl

theorem le_assert_iff_simpleNecessity (p : W → Prop) (w : W) :
    stateAt f g w ≤ (stateAt f g w).assert p ↔ simpleNecessity f p w :=
  (stateAt f g w).le_assert_iff p

theorem isRealistic_iff_mem_stateAt_info : f.IsRealistic ↔ ∀ w, w ∈ (stateAt f g w).info :=
  Iff.rfl

end Mood
