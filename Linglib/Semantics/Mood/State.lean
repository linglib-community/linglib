/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Filter.Basic
public import Linglib.Semantics.Dynamic.OrderedInformationState
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Questions.Partition.Inquisitive
public import Mathlib.Tactic.DeriveFintype

/-!
# The mood state

A mood state is an ordered information state, a context set together with a preorder on worlds,
and an inquiry, a partition of the worlds that records the open question. Mood states are
ordered coordinatewise, a more constrained state lying below a less constrained one, and form a
complete lattice whose top is the state with no information, no expectations and no question.

We define three updates, each of which changes one coordinate: `Mood.State.assert` removes
worlds from the context set, `Mood.State.promote` refines the ordering, and `Mood.State.inquire`
refines the inquiry. Each meets the state with a fixed content (`Mood.State.isAdditive_assert`,
`Mood.State.isAdditive_promote`, `Mood.State.isAdditive_inquire`).

Beside the two modals of an ordered information state we define answerhood,
`Mood.State.boxAns`: a state settles `p` when `p` is constant on the part of each inquiry cell
inside the context set, or equivalently when its issue entails the polar question whether `p`
relative to the context set (`Mood.State.boxAns_iff_le_relativeTo`). `Mood.Component` names the
three coordinates and `Mood.Component.boxOn` the modal of each.

A modal base and an ordering source induce an ordered information state at each world,
`Mood.stateAt`, whose two modals are Kratzer's simple necessity and truth at the best worlds.

## Implementation notes

* For interrogatives Portner offers two options: replace the context set with a partition of
  it, or add a question set as a third coordinate, as in the discourse contexts of Roberts and of
  his own earlier work. The mood state takes the second, with the question set reduced to the
  meet of its partitions, as Mari and Portner's discourse context keeps the question under
  discussion as a component of its own beside the common ground.
* The `?`-update and `boxAns` are additions of this library; Portner leaves interrogatives open.
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

variable {W : Type*}

/-- A mood state is an ordered information state together with an inquiry partition, the open
question, where `⊤` is no question. -/
@[ext]
structure State (W : Type*) extends OrderedInformationState W where
  /-- Two worlds are related when they answer the open question alike. -/
  inquiry : Setoid W

namespace State

/-- The mood state with no open question. -/
def ofOrderedInformationState (σ : OrderedInformationState W) : State W :=
  { σ with inquiry := ⊤ }

@[simp] theorem ofOrderedInformationState_toOrderedInformationState
    (σ : OrderedInformationState W) :
    (ofOrderedInformationState σ).toOrderedInformationState = σ := rfl

@[simp] theorem ofOrderedInformationState_inquiry (σ : OrderedInformationState W) :
    (ofOrderedInformationState σ).inquiry = (⊤ : Setoid W) := rfl

/-! ### The lattice of mood states

Mood states are ordered componentwise, a more constrained state lying below a less constrained
one. They form a complete lattice, the product of the lattice of ordered information states and
the lattice of partitions, whose top is the state with no information, no expectations and no
question. -/

instance : LE (State W) :=
  ⟨fun c₁ c₂ ↦ c₁.toOrderedInformationState ≤ c₂.toOrderedInformationState ∧
    c₁.inquiry ≤ c₂.inquiry⟩
instance : LT (State W) := ⟨fun c₁ c₂ ↦ c₁ ≤ c₂ ∧ ¬c₂ ≤ c₁⟩
instance : Max (State W) :=
  ⟨fun c₁ c₂ ↦
    ⟨c₁.toOrderedInformationState ⊔ c₂.toOrderedInformationState, c₁.inquiry ⊔ c₂.inquiry⟩⟩
instance : Min (State W) :=
  ⟨fun c₁ c₂ ↦
    ⟨c₁.toOrderedInformationState ⊓ c₂.toOrderedInformationState, c₁.inquiry ⊓ c₂.inquiry⟩⟩
instance : SupSet (State W) := ⟨fun S ↦ ⟨⨆ c ∈ S, c.toOrderedInformationState, ⨆ c ∈ S, c.inquiry⟩⟩
instance : InfSet (State W) := ⟨fun S ↦ ⟨⨅ c ∈ S, c.toOrderedInformationState, ⨅ c ∈ S, c.inquiry⟩⟩
instance : Top (State W) := ⟨ofOrderedInformationState ⊤⟩
instance : Bot (State W) := ⟨⟨⊥, ⊥⟩⟩

instance : CompleteLattice (State W) :=
  Function.Injective.completeLattice (fun c ↦ (c.toOrderedInformationState, c.inquiry))
    (fun _ _ h ↦ State.ext (congrArg (·.1.info) h) (congrArg (·.1.order) h) (congrArg Prod.snd h))
    Iff.rfl Iff.rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ by simp only [Prod.iSup_mk]; rfl)
    (fun _ ↦ by simp only [Prod.iInf_mk]; rfl) rfl rfl

theorem le_iff {c₁ c₂ : State W} :
    c₁ ≤ c₂ ↔
      c₁.toOrderedInformationState ≤ c₂.toOrderedInformationState ∧ c₁.inquiry ≤ c₂.inquiry :=
  Iff.rfl

/-- Mood states are the pairs of an ordered information state and an inquiry partition. -/
@[simps apply]
def orderIsoProd : State W ≃o OrderedInformationState W × Setoid W where
  toFun c := (c.toOrderedInformationState, c.inquiry)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem orderIsoProd_symm_apply (σ : OrderedInformationState W) (q : Setoid W) :
    orderIsoProd.symm (σ, q) = ⟨σ, q⟩ := rfl

/-! ### Updates -/

/-- Assertion eliminates the worlds outside `p` from the context set. -/
def assert (c : State W) (p : W → Prop) : State W :=
  { c.toOrderedInformationState.assert p with inquiry := c.inquiry }

/-- Promotion refines the ordering with `p`. -/
def promote (c : State W) (p : W → Prop) : State W :=
  { c.toOrderedInformationState.promote p with inquiry := c.inquiry }

/-- The `?`-update refines the inquiry with the question `q`. -/
def inquire (c : State W) (q : Setoid W) : State W :=
  { c with inquiry := c.inquiry ⊓ q }

@[simp] theorem assert_toOrderedInformationState (c : State W) (p : W → Prop) :
    (c.assert p).toOrderedInformationState = c.toOrderedInformationState.assert p := rfl

@[simp] theorem assert_inquiry (c : State W) (p : W → Prop) :
    (c.assert p).inquiry = c.inquiry := rfl

@[simp] theorem promote_toOrderedInformationState (c : State W) (p : W → Prop) :
    (c.promote p).toOrderedInformationState = c.toOrderedInformationState.promote p := rfl

@[simp] theorem promote_inquiry (c : State W) (p : W → Prop) :
    (c.promote p).inquiry = c.inquiry := rfl

@[simp] theorem inquire_toOrderedInformationState (c : State W) (q : Setoid W) :
    (c.inquire q).toOrderedInformationState = c.toOrderedInformationState := rfl

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
  congrArg (State.mk c.toOrderedInformationState) (inf_right_idem _ _)

@[simp] theorem foldl_assert_toOrderedInformationState (ps : List (W → Prop)) (c : State W) :
    (ps.foldl assert c).toOrderedInformationState =
      ps.foldl OrderedInformationState.assert c.toOrderedInformationState := by
  induction ps generalizing c with
  | nil => rfl
  | cons p ps ih => exact ih (c.assert p)

@[simp] theorem foldl_promote_toOrderedInformationState (ps : List (W → Prop)) (c : State W) :
    (ps.foldl promote c).toOrderedInformationState =
      ps.foldl OrderedInformationState.promote c.toOrderedInformationState := by
  induction ps generalizing c with
  | nil => rfl
  | cons p ps ih => exact ih (c.promote p)

/-! ### Updates meet a state with a content -/

theorem isAdditive_assert (p : W → Prop) : IsAdditive (assert · p) := fun c ↦
  congrArg₂ State.mk (OrderedInformationState.isAdditive_assert p c.toOrderedInformationState)
    (inf_top_eq _).symm

theorem isAdditive_promote (p : W → Prop) : IsAdditive (promote · p) := fun c ↦
  congrArg₂ State.mk (OrderedInformationState.isAdditive_promote p c.toOrderedInformationState)
    (inf_top_eq _).symm

theorem isAdditive_inquire (q : Setoid W) : IsAdditive (inquire · q) := fun c ↦
  congrArg₂ State.mk (inf_top_eq _).symm (congrArg (c.inquiry ⊓ ·) (top_inf_eq q).symm)

/-- Promotion changes nothing exactly when the content's worlds form a lower set of the
ordering. -/
theorem promote_eq_self_iff {c : State W} {p : W → Prop} :
    c.promote p = c ↔ c.order ≤ .ofCriterion p :=
  ⟨fun h ↦ OrderedInformationState.isFixedPt_promote_iff.1 (congrArg toOrderedInformationState h),
    fun h ↦ congrArg (State.mk · c.inquiry) (OrderedInformationState.isFixedPt_promote_iff.2 h)⟩

theorem le_inquire_iff (c : State W) (q : Setoid W) :
    c ≤ c.inquire q ↔ c.inquiry ≤ q :=
  ⟨fun h ↦ h.2.trans inf_le_right, fun h ↦ ⟨le_rfl, le_inf le_rfl h⟩⟩

/-! ### Discourse projections -/

/-- Assertion is Stalnaker's: the principal filter of the context set semiconjugates it to the
meet with the asserted proposition. -/
theorem semiconj_assert (φ : Set W) :
    Function.Semiconj (fun c : State W ↦ Filter.principal c.info) (·.assert (· ∈ φ))
      (· ⊓ Filter.principal φ) :=
  fun c ↦ show Filter.principal {w ∈ c.info | w ∈ φ} = Filter.principal c.info ⊓ Filter.principal φ
    by rw [Set.sep_mem_eq, Filter.inf_principal]

/-- Inquiry is inquisitive update: the inquiry partition, read as an issue, semiconjugates
`inquire` to the meet with the question. -/
theorem semiconj_inquire (q : Setoid W) :
    Function.Semiconj (fun c : State W ↦ Question.fromSetoid c.inquiry) (·.inquire q)
      (· ⊓ Question.fromSetoid q) :=
  fun _ ↦ Question.fromSetoid_inf _ _

/-! ### Answerhood -/

/-- Answerhood holds of `p` when `p` is constant on the part of each inquiry cell inside the
context set. Unlike `boxCs` and `boxLe` it is not upward monotone in `p`. -/
def boxAns (c : State W) (p : W → Prop) : Prop := c.inquiry.DeterminesOn {w | p w} c.info

/-- A state settles `p` exactly when its issue entails the polar question whether `p` relative to
the context set. -/
theorem boxAns_iff_le_relativeTo (c : State W) (p : W → Prop) :
    c.boxAns p ↔ Question.fromSetoid c.inquiry ≤ (Question.polar {w | p w}).relativeTo c.info :=
  Question.determinesOn_iff_fromSetoid_le_relativeTo _ _ _

theorem boxAns_of_determines (c : State W) {p : W → Prop}
    (h : c.inquiry.Determines {w | p w}) : c.boxAns p :=
  h.determinesOn _

theorem boxAns_iff_determines {c : State W} (h : c.info = Set.univ) (p : W → Prop) :
    c.boxAns p ↔ c.inquiry.Determines {w | p w} := by
  rw [boxAns, h, Setoid.determinesOn_univ]

theorem boxAns_anti {c₁ c₂ : State W} (h : c₁ ≤ c₂) (p : W → Prop) :
    c₂.boxAns p → c₁.boxAns p :=
  fun hbox ↦ (hbox.mono h.1.1).mono_left h.2

/-! The propositions a state settles are closed under the Boolean connectives. -/

theorem boxAns_not (c : State W) (p : W → Prop) :
    c.boxAns p → c.boxAns (fun w ↦ ¬ p w) :=
  Setoid.DeterminesOn.compl

theorem boxAns_and (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w ∧ q w) :=
  Setoid.DeterminesOn.inter

theorem boxAns_or (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w ∨ q w) :=
  Setoid.DeterminesOn.union

theorem boxAns_imp (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w → q w) :=
  fun hp hq _ hw _ hv hwv ↦ imp_congr (hp hw hv hwv) (hq hw hv hwv)

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

/-- The necessity modal of a component is `boxCs`, `boxLe` or `boxAns`. -/
def Component.boxOn : Component → State W → (W → Prop) → Prop
  | .informational, c, p => c.toOrderedInformationState.boxCs p
  | .preferential,  c, p => c.toOrderedInformationState.boxLe p
  | .inquisitive,   c, p => c.boxAns p

@[simp] theorem Component.boxOn_informational (c : State W) (p : W → Prop) :
    Component.informational.boxOn c p = c.toOrderedInformationState.boxCs p := rfl

@[simp] theorem Component.boxOn_preferential (c : State W) (p : W → Prop) :
    Component.preferential.boxOn c p = c.toOrderedInformationState.boxLe p := rfl

@[simp] theorem Component.boxOn_inquisitive (c : State W) (p : W → Prop) :
    Component.inquisitive.boxOn c p = c.boxAns p := rfl

/-! ### Kratzer backgrounds induce states

Portner glosses his (3): read as a modal base and an ordering source, the two coordinates make
`boxCs` simple necessity and `boxLe` human necessity. Read the other way, a Kratzer pair is a
world-indexed family of ordered information states. -/

open Modality

variable (f g : Background W)

/-- The ordered information state that a modal base and an ordering source induce at a world. -/
def stateAt (w : W) : OrderedInformationState W :=
  ⟨f.accessibleWorlds w, premisePreorder (g w)⟩

@[simp] theorem stateAt_info (w : W) : (stateAt f g w).info = f.accessibleWorlds w := rfl

@[simp] theorem stateAt_order (w : W) : (stateAt f g w).order = premisePreorder (g w) := rfl

theorem bestWorlds_eq_optimal (w : W) : bestWorlds f g w = (stateAt f g w).optimal := rfl

theorem eventually_simpleNecessity_iff_boxCs (p : W → Prop) (w : W) :
    (∀ᶠ v in simpleNecessity f w, p v) ↔ (stateAt f g w).boxCs p :=
  Iff.rfl

theorem forall_mem_bestWorlds_iff_boxLe (p : W → Prop) (w : W) :
    (∀ v ∈ bestWorlds f g w, p v) ↔ (stateAt f g w).boxLe p :=
  Iff.rfl

theorem isFixedPt_assert_iff_eventually_simpleNecessity (p : W → Prop) (w : W) :
    Function.IsFixedPt (·.assert p) (stateAt f g w) ↔ ∀ᶠ v in simpleNecessity f w, p v :=
  OrderedInformationState.isFixedPt_assert_iff

theorem isRealistic_iff_mem_stateAt_info : f.IsRealistic ↔ ∀ w, w ∈ (stateAt f g w).info :=
  Iff.rfl

namespace State

/-! ### Answerhood is not informational necessity -/

/-- The state over `Bool` with every world in the context set and the finest inquiry. -/
def sepInquiry : State Bool where
  info := Set.univ
  order := ⊤
  inquiry := ⊥

/-- The proposition true at `false` alone. -/
def sepProp : Bool → Prop := fun w ↦ w = false

theorem boxAns_not_reducible_to_boxCs :
    ∃ (c : State Bool) (p : Bool → Prop), c.boxAns p ∧ ¬ c.toOrderedInformationState.boxCs p :=
  ⟨sepInquiry, sepProp, Setoid.bot_determines.determinesOn _,
    fun h ↦ Bool.noConfusion (h true trivial)⟩

end State

end Mood
