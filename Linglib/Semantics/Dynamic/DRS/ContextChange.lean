module

public import Linglib.Semantics.Dynamic.DRS.Verification
public import Linglib.Semantics.Dynamic.State
public import Linglib.Semantics.Dynamic.Update

/-!
# Context change potentials of DRSs

Over an intensional model — a family `interp : W → L.Structure M` of structures on a constant
domain — a DRS updates possibilities: `DRS.update` relates two points of the same world whose
assignments are related by the verification of Kamp, van Genabith and Reyle's Def. 19, and the
*context change potential* `DRS.ccp` (Def. 24) is its image on information states. The state a
DRS expresses relative to an assignment is `DRS.relState` (Def. 29), with the state it expresses
outright (Def. 22) its value at the empty assignment.

## Main statements

* `DRS.ccp_le`: a context change potential only adds information (Def. 27(ii)).
* `DRS.ccp_eq_mul_ccp_stratum`: on a state uniform at a base, context change is merge with the
  potential's value on the stratum — Heim's assertive update.
* `DRS.state_merge`: updating the state of a context DRS gives the state of the merge.
* `DRS.image_world_state`: the proposition a state determines (Def. 23(v)) is the set of worlds
  where the DRS is true (Def. 20).

## References

* [kamp-vangenabith-reyle-2011]
* [heim-1982]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics SetRel

namespace DRT

universe u v w x y

variable {L : Language.{u, v}} {V : Type w} {M : Type x} {W : Type y}
variable (interp : W → L.Structure M)

/-- `⟨f, g⟩` verifies `K` in the model at the world `w` (Def. 19). -/
def DRS.VerifiesAt (w : W) (K : DRS L V) (f g : PartialAssign V M) : Prop :=
  letI := interp w
  K.Verifies f g

variable {K K₁ K₂ : DRS L V} {p q : Possibility W V (Flat M)} {I : State W V M}

theorem DRS.verifiesAt_iff {w : W} {f g : PartialAssign V M} :
    K.VerifiesAt interp w f g ↔
      f ≤ g ∧ g.domain = f.domain ∪ ↑K.referents ∧
        (letI := interp w; Condition.HoldsAll K.conditions g) :=
  letI := interp w
  DRS.verifies_iff

theorem DRS.VerifiesAt.le {w : W} {f g : PartialAssign V M}
    (h : K.VerifiesAt interp w f g) : f ≤ g :=
  ((DRS.verifiesAt_iff interp).mp h).1

theorem DRS.VerifiesAt.domain_eq {w : W} {f g : PartialAssign V M}
    (h : K.VerifiesAt interp w f g) : g.domain = f.domain ∪ ↑K.referents :=
  ((DRS.verifiesAt_iff interp).mp h).2.1

theorem DRS.VerifiesAt.holdsAll {w : W} {f g : PartialAssign V M}
    (h : K.VerifiesAt interp w f g) :
    letI := interp w; Condition.HoldsAll K.conditions g :=
  ((DRS.verifiesAt_iff interp).mp h).2.2

/-- The dynamic value of a DRS on possibilities: worlds are preserved and assignments related by
Def. 19. -/
def DRS.update (K : DRS L V) : Update (Possibility W V (Flat M)) :=
  {p | p.1.world = p.2.world ∧ K.VerifiesAt interp p.1.world p.1.assignment p.2.assignment}

theorem DRS.mem_update :
    p ~[K.update interp] q ↔
      p.world = q.world ∧ K.VerifiesAt interp p.world p.assignment q.assignment := Iff.rfl

/-- The context change potential of a DRS (Def. 24): the image of its dynamic value on
information states. -/
def DRS.ccp (K : DRS L V) (I : State W V M) : State W V M := (K.update interp).image I

theorem DRS.mem_ccp :
    q ∈ K.ccp interp I ↔
      ∃ p ∈ I, p.world = q.world ∧ K.VerifiesAt interp p.world p.assignment q.assignment :=
  mem_image

/-- The information state a DRS expresses relative to an assignment of its free referents
(Def. 29(ii)). -/
def DRS.relState (K : DRS L V) (g : PartialAssign V M) : State W V M :=
  {q | K.VerifiesAt interp q.world g q.assignment}

theorem DRS.mem_relState {g : PartialAssign V M} :
    q ∈ K.relState interp g ↔ K.VerifiesAt interp q.world g q.assignment := Iff.rfl

/-- The information state a proper DRS expresses (Def. 22), the state relative to the empty
assignment. -/
def DRS.state (K : DRS L V) : State W V M := K.relState interp ⊥

theorem DRS.mem_state : q ∈ K.state interp ↔ K.VerifiesAt interp q.world ⊥ q.assignment :=
  Iff.rfl

theorem DRS.uniformAt_state : State.UniformAt ↑K.referents (K.state interp) := by
  intro q hq
  have h := DRS.VerifiesAt.domain_eq interp hq
  rwa [PartialAssign.domain_bot, Set.empty_union, Possibility.domain_assignment] at h

/-- Def. 22 is the context change potential's value on the initial state. -/
theorem DRS.ccp_top : K.ccp interp (⊤ : State W V M) = K.state interp := by
  ext q
  rw [DRS.mem_ccp, DRS.mem_state]
  constructor
  · rintro ⟨p, hp, hw, hv⟩
    have hbot : p.assignment = ⊥ := funext fun v => State.mem_top.mp hp v
    rwa [hw, hbot] at hv
  · intro hv
    exact ⟨⟨q.world, fun _ => ⊥⟩, State.mem_top.mpr fun _ => rfl, rfl, hv⟩

/-- A context change potential only adds information (Def. 27(ii)). -/
theorem DRS.ccp_le (I : State W V M) : K.ccp interp I ≤ I :=
  State.le_def.mpr fun q hq => by
    obtain ⟨p, hp, hw, hv⟩ := (DRS.mem_ccp interp).mp hq
    exact ⟨p, hp, hw, Pi.le_def.mp (DRS.VerifiesAt.le interp hv)⟩

/-- The value of a context change potential on a stratum: the points of the grown stratum whose
conditions hold. -/
theorem DRS.mem_ccp_stratum {X : Set V} :
    q ∈ K.ccp interp (State.stratum X) ↔
      q.domain = X ∪ ↑K.referents ∧
        (letI := interp q.world; Condition.HoldsAll K.conditions q.assignment) := by
  rw [DRS.mem_ccp]
  constructor
  · rintro ⟨p, hp, hw, hv⟩
    have hdom := DRS.VerifiesAt.domain_eq interp hv
    have hh := DRS.VerifiesAt.holdsAll interp hv
    rw [hw] at hh
    rw [Possibility.domain_assignment, Possibility.domain_assignment,
      State.mem_stratum.mp hp] at hdom
    exact ⟨hdom, hh⟩
  · rintro ⟨hdom, hh⟩
    classical
    have hr : (q.restrict X).domain = X := by
      rw [Possibility.domain_restrict, hdom]
      exact Set.inter_eq_left.mpr Set.subset_union_left
    refine ⟨q.restrict X, hr, Possibility.restrict_world, ?_⟩
    rw [Possibility.restrict_world, DRS.verifiesAt_iff]
    exact ⟨fun x => (Possibility.restrict_le (X := X) (p := q)).2 x,
      by rw [Possibility.domain_assignment, Possibility.domain_assignment, hr, hdom], hh⟩

/-- On a state uniform at a base, context change is merge with the potential's value on the
stratum: the context change potential of Def. 24 is Heim's assertive update. -/
theorem DRS.ccp_eq_mul_ccp_stratum {X : Set V} (hI : State.UniformAt X I) :
    K.ccp interp I = I * K.ccp interp (State.stratum X) := by
  have huni : State.UniformAt (X ∪ ↑K.referents) (K.ccp interp (State.stratum X)) :=
    fun r hr => ((DRS.mem_ccp_stratum interp).mp hr).1
  rw [State.mul_eq_sep_of_uniformAt huni]
  ext q
  rw [DRS.mem_ccp]
  constructor
  · rintro ⟨p, hp, hw, hv⟩
    have hle := DRS.VerifiesAt.le interp hv
    have hdom := DRS.VerifiesAt.domain_eq interp hv
    have hh := DRS.VerifiesAt.holdsAll interp hv
    have hpd : p.domain = X := hI p hp
    have hqd : q.domain = X ∪ ↑K.referents := by
      rwa [Possibility.domain_assignment, Possibility.domain_assignment, hpd] at hdom
    have hrest : q.restrict (X ∪ ↑K.referents) = q := Possibility.restrict_eq_self hqd
    refine ⟨State.mem_mul_stratum.mpr ⟨p, hp, ⟨hw, Pi.le_def.mp hle⟩, ?_⟩, ?_⟩
    · rw [hqd, hpd, ← Set.union_assoc, Set.union_self]
    · rw [hrest, DRS.mem_ccp_stratum]
      rw [hw] at hh
      exact ⟨hqd, hh⟩
  · rintro ⟨hmul, hrest⟩
    obtain ⟨p, hp, hpq, hdom⟩ := State.mem_mul_stratum.mp hmul
    have hpd : p.domain = X := hI p hp
    have hqd : q.domain = X ∪ ↑K.referents := by
      rw [hdom, hpd, ← Set.union_assoc, Set.union_self]
    rw [Possibility.restrict_eq_self hqd, DRS.mem_ccp_stratum] at hrest
    refine ⟨p, hp, hpq.1, (DRS.verifiesAt_iff interp).mpr ⟨hpq.2, ?_, ?_⟩⟩
    · rw [Possibility.domain_assignment, Possibility.domain_assignment, hqd, hpd]
    · rw [hpq.1]
      exact hrest.2

set_option linter.style.haveILetI false in
/-- Sequencing the dynamic values of two DRSs is the dynamic value of their merge, when the
second universe captures no referent the first DRS's conditions use outside its own. -/
theorem DRS.update_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    (K₁.merge K₂).update interp = K₁.update interp ○ K₂.update interp := by
  ext ⟨p, q⟩
  rw [mem_comp]
  constructor
  · rintro ⟨hw, hv⟩
    letI := interp p.world
    obtain ⟨h, h₁, h₂⟩ := (DRS.verifies_merge K₁ K₂ hfresh).mp hv
    exact ⟨⟨p.world, h⟩, ⟨rfl, h₁⟩, hw, h₂⟩
  · rintro ⟨r, ⟨hw₁, hv₁⟩, hw₂, hv₂⟩
    rw [← hw₁] at hv₂
    refine ⟨hw₁.trans hw₂, ?_⟩
    letI := interp p.world
    exact (DRS.verifies_merge K₁ K₂ hfresh).mpr ⟨r.assignment, hv₁, hv₂⟩

theorem DRS.ccp_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents))
    (I : State W V M) :
    (K₁.merge K₂).ccp interp I = K₂.ccp interp (K₁.ccp interp I) := by
  ext q
  rw [DRS.ccp, DRS.update_merge interp K₁ K₂ hfresh]
  constructor
  · rintro ⟨p, hp, r, h₁, h₂⟩
    exact ⟨r, ⟨p, hp, h₁⟩, h₂⟩
  · rintro ⟨r, ⟨p, hp, h₁⟩, h₂⟩
    exact ⟨p, hp, r, h₁, h₂⟩

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
    exact ⟨q.assignment, hq⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨w, g⟩, hg, rfl⟩

end DRT
