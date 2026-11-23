module

public import Linglib.Semantics.Dynamic.DRT.Verification.Partial
public import Linglib.Semantics.Dynamic.State
public import Linglib.Semantics.Dynamic.Update

/-!
# Context change potentials of DRSs

An *intensional model* is a family `interp : W → L.Structure M` of structures on a constant
domain. Over such a model a DRS `K` with universe `U` relates two possibilities when they share
their world `w` and their assignments `f`, `g` verify `K` at `w`: `g` extends `f` by exactly `U`
and verifies the conditions of `K` in `interp w`. This relation is `DRS.update`, the relation
of `K` on embeddings (`DRS.rel`) taken world by world (`Possibility.liftRel`), and the
*context change potential* `DRS.ccp` of `K` is its image on information states,
`K.ccp interp I = {⟨w, g⟩ | ∃ f, ⟨w, f⟩ ∈ I ∧ ⟨f, g⟩ verifies K at w}`.

The update of a DRS is a box: extension along the universe followed by the test of the
conditions (`DRS.update_eq`). On information states extension along `U` is merge with the stratum
at `U`, so a context change potential merges its input with that stratum and keeps the points
where the conditions hold (`DRS.ccp_eq`), which is the form of the atomic rule of file change
semantics. The potential therefore only adds information (`DRS.ccp_le`) and carries a state
uniform at `X` to one uniform at `X ∪ U` (`DRS.uniformAt_ccp`), and on a state uniform at `X` it
is merge with its own value on the stratum at `X` (`DRS.ccp_eq_mul_ccp_stratum`).

The empty DRS updates by the identity (`DRS.update_empty`), and the merge of two DRSs by the
sequence of their updates when the second universe captures no referent that the conditions of
the first use outside its own (`DRS.update_merge`, `DRS.ccp_merge`).

The information state a DRS expresses relative to an assignment `g` of its free referents is
`DRS.relState`, the points `⟨w, f⟩` that the update reaches from `⟨w, g⟩`, and the state it
expresses outright is `DRS.state`, its value at the empty assignment. That state is the value of
the context change potential on the initial state (`DRS.ccp_top`), and its worlds are those
where the DRS is true (`DRS.image_world_state`).

## Implementation notes

`DRS.ccp` is a total function on information states. On a state that leaves a free referent of
the DRS undefined, a condition on that referent fails and the value is the absurd state.

## References

* [kamp-vangenabith-reyle-2011]
* [heim-1982]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics SetRel

namespace DRT

universe u v w x y

variable {L : Language.{u, v}} {V : Type w} {M : Type x} {W : Type y}
variable (interp : W → L.Structure M)

/-! ### The update of a DRS -/

/-- The points whose assignment verifies the conditions of a DRS at their world. -/
def DRS.conditionSet (K : DRS L V) : Set (Possibility W V (Part M)) :=
  {q | letI := interp q.world; Condition.HoldsAll K.conditions q.assignment}

/-- The dynamic value of a DRS on possibilities: the world is kept, and the assignments are
related by verification in the structure at that world (Def. 19). -/
def DRS.update (K : DRS L V) : Update (Possibility W V (Part M)) :=
  Possibility.liftRel fun w ↦ letI := interp w; K.rel

variable {K K₁ K₂ : DRS L V} {p q : Possibility W V (Part M)} {I : State W V M}

/-- An update extends its input by exactly the universe, to a point where the conditions hold. -/
theorem DRS.mem_update_iff :
    p ~[K.update interp] q ↔
      p ≤ q ∧ q.domain = p.domain ∪ ↑K.referents ∧ q ∈ K.conditionSet interp := by
  obtain ⟨w, f⟩ := p
  obtain ⟨w', g⟩ := q
  constructor
  · rintro ⟨hw, hv⟩
    obtain rfl : w = w' := hw
    obtain ⟨hle, hdom, hh⟩ := (@DRS.verifies_iff L V M (interp w) K f g).mp hv
    exact ⟨⟨rfl, hle⟩, hdom, hh⟩
  · rintro ⟨⟨hw, hle⟩, hdom, hh⟩
    obtain rfl : w = w' := hw
    exact ⟨rfl, (@DRS.verifies_iff L V M (interp w) K f g).mpr ⟨hle, hdom, hh⟩⟩

/-- The update of a DRS is a box: extension along its universe, then the test of its
conditions. -/
theorem DRS.update_eq :
    K.update interp = State.extend ↑K.referents ○ Update.test (K.conditionSet interp) := by
  ext ⟨p, q⟩
  rw [Update.mem_comp_test, State.mem_extend, and_assoc]
  exact DRS.mem_update_iff interp

@[simp] theorem DRS.update_empty : (DRS.empty : DRS L V).update interp = SetRel.id := by
  simp only [DRS.update, DRS.rel_empty, Possibility.liftRel_id]

/-- Sequencing the dynamic values of two DRSs is the dynamic value of their merge, when the
second universe captures no referent the first DRS's conditions use outside its own. -/
theorem DRS.update_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    (K₁.merge K₂).update interp = K₁.update interp ○ K₂.update interp := by
  rw [DRS.update, DRS.update, DRS.update, ← Possibility.liftRel_comp]
  exact congrArg _ (funext fun w ↦ letI := interp w; DRS.rel_merge K₁ K₂ hfresh)

/-! ### The context change potential -/

/-- The context change potential of a DRS (Def. 24): the image of its dynamic value on
information states. -/
def DRS.ccp (K : DRS L V) (I : State W V M) : State W V M := (K.update interp).image I

theorem DRS.mem_ccp : q ∈ K.ccp interp I ↔ ∃ p ∈ I, p ~[K.update interp] q := mem_image

/-- A context change potential merges its input with the stratum at the universe and keeps the
points where the conditions hold. -/
theorem DRS.ccp_eq (I : State W V M) :
    K.ccp interp I = {q ∈ I * State.stratum ↑K.referents | q ∈ K.conditionSet interp} := by
  rw [DRS.ccp, DRS.update_eq, image_comp, Update.image_test, State.image_extend]
  rfl

/-- A context change potential only adds information (Def. 27(ii)). -/
theorem DRS.ccp_le (I : State W V M) : K.ccp interp I ≤ I := by
  rw [DRS.ccp_eq]
  exact le_trans (State.le_of_subset fun _ h ↦ h.1) State.mul_le_left

/-- A context change potential grows the base of a state by the universe. -/
theorem DRS.uniformAt_ccp {X : Set V} (hI : State.UniformAt X I) :
    State.UniformAt (X ∪ ↑K.referents) (K.ccp interp I) := by
  rw [DRS.ccp_eq]
  exact fun q hq ↦ hI.mul State.uniformAt_stratum q hq.1

/-- The value of a context change potential on a stratum: the points of the grown stratum where
the conditions hold. -/
theorem DRS.ccp_stratum (X : Set V) :
    K.ccp interp (State.stratum X) =
      {q ∈ (State.stratum (X ∪ ↑K.referents) : State W V M) | q ∈ K.conditionSet interp} := by
  rw [DRS.ccp_eq, State.stratum_union]

/-- On a state uniform at a base, context change is merge with the potential's value on the
stratum at that base. -/
theorem DRS.ccp_eq_mul_ccp_stratum {X : Set V} (hI : State.UniformAt X I) :
    K.ccp interp I = I * K.ccp interp (State.stratum X) := by
  have hmul : I * State.stratum (X ∪ ↑K.referents) = I * State.stratum ↑K.referents := by
    rw [State.stratum_union, ← mul_assoc,
      State.mul_stratum_eq_self fun p hp ↦ (hI p hp).symm.subset]
  rw [State.mul_eq_sep_of_uniformAt (DRS.uniformAt_ccp interp State.uniformAt_stratum), hmul,
    DRS.ccp_eq interp I]
  ext r
  refine and_congr_right fun hr ↦ ?_
  have hd : r.domain = X ∪ ↑K.referents := hI.mul State.uniformAt_stratum r hr
  rw [Possibility.restrict_eq_self hd, DRS.ccp_stratum]
  exact (and_iff_right hd).symm

theorem DRS.ccp_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents))
    (I : State W V M) :
    (K₁.merge K₂).ccp interp I = K₂.ccp interp (K₁.ccp interp I) := by
  rw [DRS.ccp, DRS.update_merge interp K₁ K₂ hfresh, image_comp]
  rfl

/-! ### The state a DRS expresses -/

/-- The information state a DRS expresses relative to an assignment of its free referents
(Def. 29(ii)). -/
def DRS.relState (K : DRS L V) (g : V → Part M) : State W V M :=
  {q | (⟨q.world, g⟩ : Possibility W V (Part M)) ~[K.update interp] q}

theorem DRS.mem_relState {g : V → Part M} :
    q ∈ K.relState interp g ↔ (⟨q.world, g⟩ : Possibility W V (Part M)) ~[K.update interp] q :=
  Iff.rfl

/-- The information state a proper DRS expresses (Def. 22), the state relative to the empty
assignment. -/
def DRS.state (K : DRS L V) : State W V M := K.relState interp ⊥

theorem DRS.mem_state : q ∈ K.state interp ↔ Possibility.bot q.world ~[K.update interp] q :=
  Iff.rfl

/-- The state a DRS expresses is the context change potential's value on the initial state. -/
theorem DRS.ccp_top : K.ccp interp (⊤ : State W V M) = K.state interp := by
  ext q
  rw [DRS.mem_ccp, DRS.mem_state]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, h⟩
    obtain rfl : w = q.world := h.1
    exact h
  · exact fun h ↦ ⟨_, ⟨q.world, rfl⟩, h⟩

theorem DRS.uniformAt_state : State.UniformAt ↑K.referents (K.state interp) := by
  simpa [DRS.ccp_top] using DRS.uniformAt_ccp interp (K := K) State.uniformAt_top

/-- Updating the state of a context DRS gives the state of the merge, as Kamp, van Genabith and
Reyle observe of their (43) after Def. 24. -/
theorem DRS.state_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    K₂.ccp interp (K₁.state interp) = (K₁.merge K₂).state interp := by
  rw [← DRS.ccp_top, ← DRS.ccp_top, DRS.ccp_merge interp K₁ K₂ hfresh]

/-- The proposition the state of a DRS determines (Def. 23(v)) is the set of worlds where the
DRS is true, for a proper DRS the proposition it expresses (Def. 20). -/
theorem DRS.image_world_state :
    Possibility.world '' K.state interp = {w | letI := interp w; K.IsTrue M} := by
  ext w
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.assignment, hq.2⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨w, g⟩, ⟨rfl, hg⟩, rfl⟩

end DRT
