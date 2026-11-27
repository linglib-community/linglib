module

public import Linglib.Semantics.Dynamic.DRT.Embedding
public import Linglib.Semantics.Dynamic.State

/-!
# Context change potentials of DRSs

An *intensional model* is a family `interp : W → L.Structure M` of structures on a constant
domain, and its embeddings are possibilities `⟨w, f⟩`, a world with a partial embedding. A
possibility `⟨w, g⟩` extends `⟨w, f⟩` when `g` extends `f`, and it verifies an atom when `g` does
in `interp w`. This is the interpretation `Interpretation.intensional interp`, an instance of the
interpretation `Interpretation.lift` that a family of interpretations determines world by world.

The *context change potential* of a DRS `K` is the image of its relation on information states,
`K.ccp interp I = {⟨w, g⟩ | ∃ f, ⟨w, f⟩ ∈ I ∧ f[K]g ∧ g ⊨ K}`. It merges its input with the
stratum at the universe of `K` and keeps the possibilities that verify `K` (`DRS.ccp_eq`), so it
only adds information (`DRS.ccp_le`). The information state `K` expresses relative to an
embedding `g` is `DRS.relState`, the possibilities `⟨w, f⟩` with `g[K]f` and `f ⊨ K` at `w`, and
`DRS.state` is its value at the empty embedding.

## Implementation notes

`DRS.ccp` is a total function on information states. On a state that leaves a free referent of
the DRS undefined, a condition on that referent fails and the value is the absurd state.

## References

* [kamp-vangenabith-reyle-2011]
* [heim-1982]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics SetRel

namespace DRT

universe u v w x y

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] {M : Type x} {W : Type y}

/-! ### Interpretations world by world -/

section Lift

variable {A : Type*} (I : W → Interpretation L V (V → A))

/-- The interpretation in possibilities that a family of interpretations in assignments
determines: a possibility is extended, and verifies an atom, as its assignment does at its
world. -/
def Interpretation.lift : Interpretation L V (Possibility W V A) where
  extend U := Possibility.liftRel fun w ↦ (I w).extend U
  atom a := {p | p.assignment ∈ (I p.world).atom a}
  eq x y := {p | p.assignment ∈ (I p.world).eq x y}
  extend_empty := by simp only [Interpretation.extend_empty, Possibility.liftRel_id]
  extend_union U U' := by simp only [Interpretation.extend_union, Possibility.liftRel_comp]

variable {I} {K : DRS L V} {p q : Possibility W V A}

private theorem DRS.eval_lift_of_forall
    (ih : ∀ c ∈ K.conditions,
      c.verifiers (.lift I) = {p | p.assignment ∈ c.verifiers (I p.world)}) :
    K.eval (.lift I) = Possibility.liftRel fun w ↦ K.eval (I w) := by
  have h (q : Possibility W V A) : q ⊨[.lift I] K ↔ q.assignment ⊨[I q.world] K :=
    DRS.mem_verifiers_iff.trans ((forall₂_congr fun c hc ↦ Set.ext_iff.mp (ih c hc) q).trans
      DRS.mem_verifiers_iff.symm)
  ext ⟨p, q⟩
  rw [Possibility.mem_liftRel, DRS.mem_eval_iff, DRS.mem_eval_iff, h]
  constructor
  · rintro ⟨⟨hw, he⟩, hv⟩
    exact ⟨hw, he, by rw [hw]; exact hv⟩
  · rintro ⟨hw, he, hv⟩
    exact ⟨⟨hw, he⟩, by rw [← hw]; exact hv⟩

/-- A possibility verifies a condition iff its assignment does at its world. -/
theorem Condition.verifiers_lift (c : Condition L V) :
    c.verifiers (.lift I) = {p | p.assignment ∈ c.verifiers (I p.world)} := by
  induction c with
  | atom a =>
    rw [Condition.verifiers_atom]
    rfl
  | eq x y =>
    rw [Condition.verifiers_eq]
    rfl
  | neg K ih =>
    ext p
    rw [Condition.mem_verifiers_neg]
    show _ ↔ p.assignment ⊨[I p.world] Condition.neg K
    rw [Condition.mem_verifiers_neg, DRS.eval_lift_of_forall ih]
    exact not_congr Possibility.mem_dom_liftRel
  | imp a c iha ihc =>
    ext p
    rw [Condition.mem_verifiers_imp]
    show _ ↔ p.assignment ⊨[I p.world] Condition.imp a c
    rw [Condition.mem_verifiers_imp, DRS.eval_lift_of_forall iha, DRS.eval_lift_of_forall ihc]
    constructor
    · intro h g hg
      obtain ⟨u, -, hu⟩ := h ⟨p.world, g⟩ ⟨rfl, hg⟩
      exact ⟨u.assignment, hu⟩
    · rintro h q ⟨hw, hq⟩
      obtain ⟨u, hu⟩ := h _ hq
      exact ⟨⟨q.world, u⟩, rfl, by rw [← hw]; exact hu⟩
  | dis l r ihl ihr =>
    ext p
    rw [Condition.mem_verifiers_dis]
    show _ ↔ p.assignment ⊨[I p.world] Condition.dis l r
    rw [Condition.mem_verifiers_dis, DRS.eval_lift_of_forall ihl, DRS.eval_lift_of_forall ihr]
    exact or_congr Possibility.mem_dom_liftRel Possibility.mem_dom_liftRel

/-- The relation a DRS denotes on possibilities is its relation on assignments, world by
world. -/
theorem DRS.eval_lift (K : DRS L V) :
    K.eval (.lift I) = Possibility.liftRel fun w ↦ K.eval (I w) :=
  DRS.eval_lift_of_forall fun c _ ↦ c.verifiers_lift

theorem DRS.mem_eval_lift :
    p ~[K.eval (.lift I)] q ↔
      p.world = q.world ∧ p.assignment ~[K.eval (I p.world)] q.assignment := by
  rw [DRS.eval_lift, Possibility.mem_liftRel]

theorem DRS.mem_verifiers_lift : p ⊨[.lift I] K ↔ p.assignment ⊨[I p.world] K :=
  DRS.mem_verifiers_iff.trans ((forall₂_congr fun c _ ↦ Set.ext_iff.mp c.verifiers_lift p).trans
    DRS.mem_verifiers_iff.symm)

end Lift

/-! ### Intensional models -/

variable (interp : W → L.Structure M)

/-- The interpretation of DRSs in the possibilities of an intensional model (Def. 19). -/
def Interpretation.intensional : Interpretation L V (Possibility W V (Part M)) :=
  .lift fun w ↦ letI := interp w; .embedding M

variable {K K₁ K₂ : DRS L V} {p q : Possibility W V (Part M)} {I : State W V M}

theorem Interpretation.intensional_extend (U : Finset V) :
    (Interpretation.intensional (V := V) interp).extend U = State.extend ↑U := by
  ext ⟨p, q⟩
  exact and_assoc.symm

/-- `⟨p, q⟩` verifies `K`: `q` extends `p` on the universe of `K` and verifies `K`. -/
theorem DRS.mem_eval_intensional :
    p ~[K.eval (.intensional interp)] q ↔
      p ≤ q ∧ q.domain = p.domain ∪ ↑K.referents ∧ q ⊨[.intensional interp] K := by
  rw [DRS.mem_eval_iff, Interpretation.intensional_extend]
  exact and_assoc

theorem DRS.eval_intensional_eq (K : DRS L V) :
    K.eval (.intensional interp) =
      State.extend ↑K.referents ○ Update.test (K.verifiers (.intensional interp)) := by
  rw [DRS.eval_eq, Interpretation.intensional_extend]
  rfl

/-- The Merging Lemma in an intensional model. -/
theorem DRS.eval_intensional_merge (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    (K₁.merge K₂).eval (.intensional interp) =
      K₁.eval (.intensional interp) ○ K₂.eval (.intensional interp) := by
  rw [Interpretation.intensional, DRS.eval_lift, DRS.eval_lift, DRS.eval_lift,
    ← Possibility.liftRel_comp]
  exact congrArg _ (funext fun w ↦ letI := interp w; DRS.eval_embedding_merge K₁ K₂ hfresh)

/-! ### The context change potential -/

/-- The context change potential of a DRS (Def. 24): the image of its relation on information
states. -/
def DRS.ccp (K : DRS L V) (I : State W V M) : State W V M :=
  (K.eval (.intensional interp)).image I

theorem DRS.mem_ccp : q ∈ K.ccp interp I ↔ ∃ p ∈ I, p ~[K.eval (.intensional interp)] q :=
  mem_image

/-- A context change potential merges its input with the stratum at the universe and keeps the
possibilities that verify the DRS. -/
theorem DRS.ccp_eq (I : State W V M) :
    K.ccp interp I = {q ∈ I * State.stratum ↑K.referents | q ⊨[.intensional interp] K} := by
  rw [DRS.ccp, DRS.eval_intensional_eq, image_comp, Update.image_test, State.image_extend]
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

theorem DRS.ccp_stratum (X : Set V) :
    K.ccp interp (State.stratum X) =
      {q ∈ (State.stratum (X ∪ ↑K.referents) : State W V M) | q ⊨[.intensional interp] K} := by
  rw [DRS.ccp_eq, State.stratum_union]

/-- On a state with base `X`, context change is merge with the potential's value on the stratum
at `X`. -/
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

theorem DRS.ccp_merge (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents))
    (I : State W V M) :
    (K₁.merge K₂).ccp interp I = K₂.ccp interp (K₁.ccp interp I) := by
  rw [DRS.ccp, DRS.eval_intensional_merge interp K₁ K₂ hfresh, image_comp]
  rfl

/-! ### The state a DRS expresses -/

/-- The information state a DRS expresses relative to an embedding of its free referents
(Def. 29(ii)). -/
def DRS.relState (K : DRS L V) (g : V → Part M) : State W V M :=
  {q | (⟨q.world, g⟩ : Possibility W V (Part M)) ~[K.eval (.intensional interp)] q}

theorem DRS.mem_relState {g : V → Part M} :
    q ∈ K.relState interp g ↔
      (⟨q.world, g⟩ : Possibility W V (Part M)) ~[K.eval (.intensional interp)] q :=
  Iff.rfl

/-- The information state a proper DRS expresses (Def. 22), the state relative to the empty
embedding. -/
def DRS.state (K : DRS L V) : State W V M := K.relState interp ⊥

theorem DRS.mem_state :
    q ∈ K.state interp ↔ Possibility.bot q.world ~[K.eval (.intensional interp)] q :=
  Iff.rfl

/-- A possibility is in the state of a DRS iff its embedding verifies the DRS from the empty
embedding in the structure at its world. -/
theorem DRS.mem_state_iff :
    q ∈ K.state interp ↔ letI := interp q.world; ⊥ ~[K.eval (.embedding M)] q.assignment :=
  DRS.mem_eval_lift.trans (and_iff_right rfl)

/-- The state a DRS expresses is the context change potential's value on the initial state. -/
theorem DRS.ccp_top : K.ccp interp (⊤ : State W V M) = K.state interp := by
  ext q
  rw [DRS.mem_ccp, DRS.mem_state]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, h⟩
    obtain rfl : w = q.world := ((DRS.mem_eval_intensional interp).mp h).1.1
    exact h
  · exact fun h ↦ ⟨_, ⟨q.world, rfl⟩, h⟩

theorem DRS.uniformAt_state : State.UniformAt ↑K.referents (K.state interp) := by
  simpa [DRS.ccp_top] using DRS.uniformAt_ccp interp (K := K) State.uniformAt_top

/-- Updating the state of a context DRS gives the state of the merge. -/
theorem DRS.state_merge (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    K₂.ccp interp (K₁.state interp) = (K₁.merge K₂).state interp := by
  rw [← DRS.ccp_top, ← DRS.ccp_top, DRS.ccp_merge interp K₁ K₂ hfresh]

/-- The proposition the state of a DRS determines (Def. 23(v)) is the set of worlds where the
DRS is true (Def. 20). -/
theorem DRS.image_world_state :
    Possibility.world '' K.state interp = {w | letI := interp w; K.IsTrue M} := by
  ext w
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.assignment, (DRS.mem_state_iff interp).mp hq⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨w, g⟩, (DRS.mem_state_iff interp).mpr hg, rfl⟩

end DRT
