module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Causation.CausalModel.Dependence
public import Linglib.Core.Relation.ReflTransGen

/-!
# Nadathur and Lauer (2020)

Nadathur and Lauer analyse periphrastic *make* as asserting causal sufficiency and *cause* as
asserting causal necessity, both relative to a background situation in a structural-equation
dynamics. The two relations come apart: restoring power is necessary but not sufficient for a
fire whose other condition is unknown, so *cause* is felicitous and *make* is not, while Ava's
training is sufficient but not necessary for Lia's taking the bus. A temporal constraint on
backgrounds blocks *make* for the earlier of two necessary causes, and a constraint on volitional
action, presupposed by *make*, separates it from *let*.

## Main definitions

* `NadathurLauer2020.Make`, `NadathurLauer2020.Cause`: the lexical entries (25)
* `NadathurLauer2020.TemporalLocationConstraint`: the constraint (28) on backgrounds
* `NadathurLauer2020.VolitionalActionConstraint`: the constraint on volitional action (43)

## Main results

* `NadathurLauer2020.Make.solve_eq`: *make* entails that the effect occurs (footnote 20)
* `NadathurLauer2020.not_forall_causallySufficient_imp_causallyNecessary`,
  `NadathurLauer2020.not_forall_causallyNecessary_imp_causallySufficient`: neither relation
  implies the other
* the judgments on the circuit (26), fire (31), bus (33), lighthouse (35) and dancing (40)–(44)
  scenarios

## Implementation notes

A dynamics is a `CausalModel` whose exogenous variables read the context, a situation is a
partial assignment, and the evaluation world of an entry is the actual world of a context.
Necessity is (24) over every supersituation, `CausalModel.CausallyNecessary (· ≤ ·)`; a
supersituation settling a variable between cause and effect can then reach the effect without the
cause, as in the persuasion chain, but each of the paper's necessity claims concerns a parent of
the effect. Adding a fact (22a) is `Function.update`, which overrides a value the situation already
fixes, as (43) needs when the background fixes the intention. The subtraction `s ∖ (C = 1)` of
(25) clears the cause whether or not `s` fixes it, and the requirement `s ⊆ w_e` is a hypothesis
where it is used. In (43) a background determines the intention when its strict development
settles it. The paper sets preemption aside, and so does the formalization.

## References

* [nadathur-lauer-2020]
-/

@[expose] public section

namespace NadathurLauer2020

open CausalModel

/-! ### Lexical entries -/

section Entries

variable {U V : Type*} {α : V → Type*} [DecidableEq V] [∀ v, Nonempty (α v)]
  (M : CausalModel U V α) [M.IsAcyclic]

/-- The *make* entry (25a) says that, with the cause removed from the background `s`, `c = x` is
causally sufficient for `e = y`, and that the cause occurs in the actual world of the context
`u`. -/
def Make (s : ∀ v, Flat (α v)) (u : U) (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  M.CausallySufficient (Function.update s c ⊥) c x e y ∧ M.solve ⊥ u c = x

/-- The *cause* entry (25b) says that, with the cause removed from the background `s`, `c = x`
is causally necessary for `e = y`, and that cause and effect both occur in the actual world of the
context `u`. -/
def Cause (s : ∀ v, Flat (α v)) (u : U) (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  M.CausallyNecessary (· ≤ ·) (Function.update s c ⊥) c x e y ∧ M.solve ⊥ u c = x ∧
    M.solve ⊥ u e = y

variable {M}

/-- *Make* entails that the effect occurs (footnote 20). The background with the cause added holds
in the evaluation world, so the effect it settles occurs there. -/
theorem Make.solve_eq {s : ∀ v, Flat (α v)} {u : U} {c : V} {x : α c} {e : V} {y : α e}
    (h : Make M s u c x e y) (hu : u ∈ M.contexts s) : M.solve ⊥ u e = y :=
  h.1.solve_eq (contexts_anti (update_le_self_iff.2 bot_le) hu) h.2

variable [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)] [Fintype V]
  [DecidableRel M.graph.Adj]

instance (s : ∀ v, Flat (α v)) (u : U) (c : V) (x : α c) (e : V) (y : α e) :
    Decidable (Make M s u c x e y) :=
  haveI : Decidable (M.solve ⊥ u c = x) := decidableEqSolve ⊥ u c x
  inferInstanceAs (Decidable (_ ∧ _))

instance [∀ v, Fintype (α v)] (s : ∀ v, Flat (α v)) (u : U) (c : V) (x : α c) (e : V)
    (y : α e) : Decidable (Cause M s u c x e y) :=
  haveI : Decidable (M.solve ⊥ u c = x) := decidableEqSolve ⊥ u c x
  haveI : Decidable (M.solve ⊥ u e = y) := decidableEqSolve ⊥ u e y
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Entries

/-! ### Constraints on background situations -/

section Constraints

variable {U V : Type*} {α : V → Type*}

/-- A background `s` meets the temporal location constraint (28) at the evaluation time `t` when
every fact it fixes is settled by `t`, the time of each variable being given by `time`. -/
def TemporalLocationConstraint (time : V → ℕ) (t : ℕ) (s : ∀ v, Flat (α v)) : Prop :=
  ∀ v, s v ≠ ⊥ → time v ≤ t

instance [Fintype V] [∀ v, DecidableEq (α v)] (time : V → ℕ) (t : ℕ) (s : ∀ v, Flat (α v)) :
    Decidable (TemporalLocationConstraint time t s) :=
  inferInstanceAs (Decidable (∀ _, _))

variable [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]

/-- A *make* claim with cause `c` and effect `e` meets the constraint on volitional action (43)
for the agent's intention `w` to perform `e` unless `w = 0` is sufficient for `e = 0` relative to
the background `s` with the cause added and `w` is determined by `s` with the cause removed. -/
def VolitionalActionConstraint (s : V → Flat Bool) (c e w : V) : Prop :=
  ¬ (M.CausallySufficient (Function.update s c ↑true) w false e false ∧
    ∃ z, M.CausallyEntails (Function.update s c ⊥) w z)

instance [Fintype U] [Inhabited U] [Fintype V] [DecidableRel M.graph.Adj] (s : V → Flat Bool)
    (c e w : V) : Decidable (VolitionalActionConstraint M s c e w) :=
  inferInstanceAs (Decidable (¬ (_ ∧ _)))

end Constraints

/-! ### The circuit -/

namespace Circuit

/-- The circuit (20) has two switches `S₁` and `S₂`, each up or down, and a light `L`. -/
inductive V | S₁ | S₂ | L deriving DecidableEq, Fintype, Repr

/-- The light reads both switches. -/
def edges : Finset (V × V) := {(.S₁, .L), (.S₂, .L)}

/-- The context settles the two switches. -/
structure Context where
  S₁ : Bool
  S₂ : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- In the circuit dynamics (Figure 1) the light is on exactly when the switches agree. -/
def circuit : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .S₁ => fun u _ ↦ u.S₁ | .S₂ => fun u _ ↦ u.S₂ | .L => fun _ x ↦ x .S₁ == x .S₂

instance : DecidableRel circuit.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : circuit.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the situation (20b) switch 1 is down and switch 2 is up. -/
def actual : Context := ⟨false, true⟩

/-- (26a) *Turning the second switch on makes the light go off* is true when switch 1 is known
to be down. -/
theorem make : Make circuit [.S₁ ← false] actual .S₂ true .L false := by decide

/-- (26b) *Turning the second switch on causes the light to go off* is true when switch 1 is known
to be down. -/
theorem cause : Cause circuit [.S₁ ← false] actual .S₂ true .L false := by decide +kernel

end Circuit

/-! ### The fire scenario -/

namespace Fire

/-- The fire scenario (30) has the power restored `P`, the drought `D`, the grass inflammable
`G`, the line down `L`, and the field on fire `F`. -/
inductive V | P | D | G | L | F deriving DecidableEq, Fintype, Repr

/-- Inflammability reads drought, and fire reads inflammability, power, and the line. -/
def edges : Finset (V × V) := {(.D, .G), (.G, .F), (.P, .F), (.L, .F)}

/-- The context settles power, drought, and the line. -/
structure Context where
  P : Bool
  D : Bool
  L : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- In the fire dynamics (Figure 2) the grass is inflammable in a drought, and the field burns
when the grass is inflammable, the power is on and the line is down. -/
def fireModel : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .P => fun u _ ↦ u.P
    | .D => fun u _ ↦ u.D
    | .L => fun u _ ↦ u.L
    | .G => fun _ x ↦ x .D
    | .F => fun _ x ↦ x .G && x .P && x .L

instance : DecidableRel fireModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : fireModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the scenario the power was restored in a drought, and the line was down. -/
def actual : Context := ⟨true, true, true⟩

/-- The background `s_b` fixes the drought and the inflammable grass and leaves the line open. -/
def s_b : V → Flat Bool := [.D ← true, .G ← true]

/-- The background `s_b1` also fixes the line as down. -/
def s_b1 : V → Flat Bool := Function.update s_b .L ↑true

theorem power_of_fire {s : V → Flat Bool} (hs : s .F = ⊥)
    (h : fireModel.CausallyEntails s .F true) : fireModel.CausallyEntails s .P true :=
  h.parent_eq hs (by decide) fun _ y hy ↦ by
    simpa using (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hy).1).2

/-- (31a) *#Restoring power made the field catch fire* is infelicitous, since with the line open
the power is not sufficient for the fire. -/
theorem not_make : ¬ Make fireModel s_b actual .P true .F true := by decide

/-- (31b) *Restoring power caused the field to catch fire* is felicitous. The power is necessary
for the fire, the line being settled down in the supersituation that brings the fire about. -/
theorem cause : Cause fireModel s_b actual .P true .F true :=
  ⟨⟨by decide, ⟨[.D ← true, .G ← true, .P ← true, .L ← true], by decide, by decide, by decide⟩,
    fun _ _ ↦ power_of_fire⟩, by decide, by decide⟩

theorem make_of_line_down : Make fireModel s_b1 actual .P true .F true := by decide

theorem cause_of_line_down : Cause fireModel s_b1 actual .P true .F true :=
  ⟨⟨by decide, ⟨[.D ← true, .G ← true, .P ← true, .L ← true], by decide, by decide, by decide⟩,
    fun _ _ ↦ power_of_fire⟩, by decide, by decide⟩

end Fire

/-! ### The bus scenario -/

namespace Bus

/-- The bus scenario (32) has Ava visiting `Vis`, Ava training `Tr`, rain forecast `Rn`, the
bike gone `Bk`, and Lia taking the bus `Bs`. -/
inductive V | Vis | Tr | Rn | Bk | Bs deriving DecidableEq, Fintype, Repr

/-- The bike's absence reads the visit and the training; the bus reads the rain and the bike. -/
def edges : Finset (V × V) := {(.Vis, .Bk), (.Tr, .Bk), (.Rn, .Bs), (.Bk, .Bs)}

/-- The context settles Ava's visit, her training, and the forecast. -/
structure Context where
  Vis : Bool
  Tr : Bool
  Rn : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- In the bus dynamics (Figure 3) the bike is gone when Ava visits and trains, and Lia takes the
bus when rain is forecast or the bike is gone. -/
def busModel : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .Vis => fun u _ ↦ u.Vis
    | .Tr => fun u _ ↦ u.Tr
    | .Rn => fun u _ ↦ u.Rn
    | .Bk => fun _ x ↦ x .Vis && x .Tr
    | .Bs => fun _ x ↦ x .Rn || x .Bk

instance : DecidableRel busModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : busModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the scenario Ava is visiting and training, and rain is forecast. -/
def actual : Context := ⟨true, true, true⟩

/-- The background `s_b` fixes the visit and the forecast. -/
def s_b : V → Flat Bool := [.Vis ← true, .Rn ← true]

/-- (33a) *Ava's training made Lia take the bus to work* is felicitous. -/
theorem make : Make busModel s_b actual .Tr true .Bs true := by decide

/-- (33b) *#Ava's training caused Lia to take the bus to work* is infelicitous. The training is
not necessary, since the supersituation in which the bike stays takes Lia to the bus by the rain
alone. -/
theorem not_cause : ¬ Cause busModel s_b actual .Tr true .Bs true := fun h ↦
  absurd (h.1.2.2 [.Vis ← true, .Rn ← true, .Bk ← false] (by decide) (by decide) (by decide))
    (by decide)

end Bus

/-! ### The lighthouse scenario -/

namespace Lighthouse

/-- The lighthouse scenario (34) has the earthquake `Q`, the storms `S`, and the collapse `L`. -/
inductive V | Q | S | L deriving DecidableEq, Fintype, Repr

/-- The collapse reads the earthquake and the storms. -/
def edges : Finset (V × V) := {(.Q, .L), (.S, .L)}

/-- The context settles the earthquake and the storms. -/
structure Context where
  Q : Bool
  S : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- In the lighthouse dynamics (Figure 4) the tower collapses when both happen. -/
def lighthouseModel : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .Q => fun u _ ↦ u.Q
    | .S => fun u _ ↦ u.S
    | .L => fun _ x ↦ x .Q && x .S

instance : DecidableRel lighthouseModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : lighthouseModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the scenario both the earthquake and the storms happened. -/
def actual : Context := ⟨true, true⟩

/-- The earthquake precedes the storms, which precede the collapse. -/
def time : V → ℕ
  | .Q => 0 | .S => 1 | .L => 2

theorem earthquake_of_collapse {s : V → Flat Bool} (hs : s .L = ⊥)
    (h : lighthouseModel.CausallyEntails s .L true) : lighthouseModel.CausallyEntails s .Q true :=
  h.parent_eq hs (by decide) fun _ y hy ↦ by simpa using (Bool.and_eq_true_iff.1 hy).1

theorem storms_of_collapse {s : V → Flat Bool} (hs : s .L = ⊥)
    (h : lighthouseModel.CausallyEntails s .L true) : lighthouseModel.CausallyEntails s .S true :=
  h.parent_eq hs (by decide) fun _ y hy ↦ by simpa using (Bool.and_eq_true_iff.1 hy).2

/-- (35a) *The earthquake caused the tower to collapse* is felicitous relative to the empty
situation. -/
theorem cause_earthquake : Cause lighthouseModel ⊥ actual .Q true .L true :=
  ⟨⟨by decide, ⟨[.Q ← true, .S ← true], by decide, by decide, by decide⟩,
    fun _ _ ↦ earthquake_of_collapse⟩, by decide, by decide⟩

/-- (35b) *The storms caused the tower to collapse* is felicitous relative to the empty
situation. -/
theorem cause_storms : Cause lighthouseModel ⊥ actual .S true .L true :=
  ⟨⟨by decide, ⟨[.Q ← true, .S ← true], by decide, by decide, by decide⟩,
    fun _ _ ↦ storms_of_collapse⟩, by decide, by decide⟩

/-- (35d) *The storms made the tower collapse* is felicitous relative to the earthquake, a
background that meets the temporal location constraint at the time of the storms. -/
theorem make_storms : TemporalLocationConstraint time (time .S) ([.Q ← true] : V → Flat Bool) ∧
    Make lighthouseModel [.Q ← true] actual .S true .L true := by
  decide

/-- (35c) *#The earthquake made the tower collapse* is infelicitous. No background meeting the
temporal location constraint at the time of the earthquake makes it sufficient, since every such
background leaves the storms open. -/
theorem not_make_earthquake (s : V → Flat Bool)
    (hs : TemporalLocationConstraint time (time .Q) s) :
    ¬ Make lighthouseModel s actual .Q true .L true := by
  rintro ⟨⟨-, h⟩, -⟩
  rw [Function.update_idem] at h
  have hopen : ∀ v, v ≠ .Q → Function.update s .Q (↑true : Flat Bool) v = ⊥ := fun v hv ↦ by
    rw [Function.update_of_ne hv]
    by_contra hsv
    have := hs v hsv
    revert hv this; cases v <;> decide
  obtain ⟨z, hz⟩ := h.parent_settled (hopen .L (by decide)) (w := .S) (by decide)
  have hS := (causallyEntails_root_iff (by decide) (hopen .S (by decide))).1 hz
  exact absurd ((hS ⟨false, true⟩ default).trans (hS ⟨false, false⟩ default).symm) (by decide)

end Lighthouse

/-! ### Neither relation implies the other -/

/-- Causal sufficiency does not imply causal necessity, by the bus scenario. -/
theorem not_forall_causallySufficient_imp_causallyNecessary :
    ¬ ∀ (U V : Type) [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
      (s : V → Flat Bool) (c : V) (x : Bool) (e : V) (y : Bool),
      M.CausallySufficient s c x e y → M.CausallyNecessary (· ≤ ·) s c x e y :=
  fun h ↦ Bus.not_cause ⟨h _ _ _ _ _ _ _ _ Bus.make.1, Bus.make.2, by decide⟩

/-- Causal necessity does not imply causal sufficiency, by the fire scenario. -/
theorem not_forall_causallyNecessary_imp_causallySufficient :
    ¬ ∀ (U V : Type) [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
      (s : V → Flat Bool) (c : V) (x : Bool) (e : V) (y : Bool),
      M.CausallyNecessary (· ≤ ·) s c x e y → M.CausallySufficient s c x e y :=
  fun h ↦ Fire.not_make ⟨h _ _ _ _ _ _ _ _ Fire.cause.1, Fire.cause.2.1⟩

/-! ### The dancing scenarios -/

namespace Dancing

/-- The dancing scenarios have the children's wanting to dance `WD`, Gurung's action `G`, and the
children dancing `D`. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

/-- In the permission and command scenarios dancing reads the desire and Gurung's action. -/
def edges : Finset (V × V) := {(.WD, .D), (.G, .D)}

/-- The context of the permission and command scenarios settles the desire and the action. -/
structure Context where
  WD : Bool
  G : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- In the permission dynamics (Figure 5) the children dance when they want to and Gurung permits
it. -/
def permission : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .WD => fun u _ ↦ u.WD | .G => fun u _ ↦ u.G | .D => fun _ x ↦ x .WD && x .G

instance : DecidableRel permission.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : permission.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the command dynamics (Figure 6) the children dance when they want to or Gurung commands
it. -/
def command : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .WD => fun u _ ↦ u.WD | .G => fun u _ ↦ u.G | .D => fun _ x ↦ x .WD || x .G

instance : DecidableRel command.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : command.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the persuasion scenario the desire reads Gurung's song, and dancing reads the desire. -/
def chain : Finset (V × V) := {(.G, .WD), (.WD, .D)}

/-- The context of the persuasion scenario settles whether Gurung plays the song. -/
structure PersuasionContext where
  G : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- In the persuasion dynamics (Figure 7) the children want to dance when Gurung plays their
song, and dance when they want to. -/
def persuasion : CausalModel PersuasionContext V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ chain⟩
  eqn | .G => fun u _ ↦ u.G | .WD => fun _ x ↦ x .G | .D => fun _ x ↦ x .WD

instance : DecidableRel persuasion.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ chain))

instance : persuasion.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the permission scenario (40) the eager children dance once Gurung permits it, and his
permission is sufficient for the dancing. -/
theorem make_permission : Make permission [.WD ← true] ⟨true, true⟩ .G true .D true := by
  decide

/-- (40a) *??Gurung made the children dance* in the permission scenario. The children's desire
is fixed and suffices to stop the dancing, so the constraint on volitional action fails; this is
the context in which *let* is felicitous (46). -/
theorem not_volitionalActionConstraint_permission :
    ¬ VolitionalActionConstraint permission [.WD ← true] .G .D .WD := by
  decide

/-- In the command scenarios, with the children reluctant (41) or eager (42), Gurung's command is
sufficient for the dancing. -/
theorem make_command (b : Bool) : Make command [.WD ← b] ⟨b, true⟩ .G true .D true := by
  cases b <;> decide

/-- (41a), (42a) *Gurung made the children dance* in the command scenarios. Whatever the
children want, their desire cannot stop the dancing once Gurung commands it, so the constraint
on volitional action holds and *let* is out (46). -/
theorem volitionalActionConstraint_command (b : Bool) :
    VolitionalActionConstraint command [.WD ← b] .G .D .WD := by
  cases b <;> decide

/-- In the persuasion scenario (44) Gurung's song is sufficient for the dancing. -/
theorem make_persuasion : Make persuasion ⊥ ⟨true⟩ .G true .D true := by decide

/-- (44a) *Gurung made the children dance (by playing their favourite song)*. The children's
desire, though sufficient to stop the dancing, is settled only by the song, so the constraint on
volitional action holds and *let* is out (46). -/
theorem volitionalActionConstraint_persuasion :
    VolitionalActionConstraint persuasion ⊥ .G .D .WD := by
  decide

end Dancing

end NadathurLauer2020
