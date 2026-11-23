module

public import Linglib.Semantics.ArgumentStructure.Relation.Control
public import Linglib.Semantics.ArgumentStructure.Relation.Denotation
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Syntax.Voice.Apply
public import Mathlib.Data.PFun

/-!
# Chierchia (1984): Topics in the syntax and semantics of infinitives and gerunds

On the theory of control of [chierchia-1984] an infinitive or gerund denotes a property, a verb
taking one denotes a relation `α` between a property and the verb's other arguments, and control
is an entailment of that relation. A *modal frame* is a quantificational force `q` together with
necessities `N x w`, a filter of propositions at each world `w` for each choice `x` of the
arguments: the propositions that follow from a conversational background of [kratzer-1981],
`simpleNecessity (a x) w`, which for *try* holds what its subject aims at and for *force* what
its subject imposes on its object. A thematic role is a partial function `θ` from the arguments
to the individual among them that bears it. The relation obeys the *Control Principle* for a role
and a frame, `ControlPrinciple α θ q N`, when

`w ∈ α P x ↔ ∃ e ∈ θ x, w ∈ q.claim (N x) (P e)`,

so that it holds of a property exactly where the bearer of the role has the property as a
necessity, or as a possibility, of the frame: it is the relation of the role,
`atRole θ fun φ x ↦ q.claim (N x) φ` (`controlPrinciple_iff`).

An argument manipulation, such as passive or detransitivization, deletes arguments of a relation
and quantifies them existentially. For `σ` the map from the arguments to those that remain, the
transform of `α` is `mapArgs σ α`.

A relation obeying the principle holds only of arguments among which the role has a bearer
(`ControlPrinciple.mem_dom`). So a relation one of whose transforms obeys the principle, for a role
that has no bearer among the transform's arguments, holds of nothing
(`ControlPrinciple.eq_bot_of_mapArgs`): a verb whose transforms all obey the principle has no
passive when its subject controls and no intransitive when its object does. A transform that
keeps the controller and the frame obeys the principle when the relation does
(`ControlPrinciple.mapArgs`). When only the relation obeys it, a transform that deletes the
controller holds where some value of the deleted argument has the property in the frame
(`ControlPrinciple.mem_mapArgs_iff`), the controller left implicit.

For a verb's relation of its participants and a diathesis that leaves the controlling participant
out, the hypothesis is computed: the relation the diathesis denotes obeys the principle, for the
role of that participant, only if the verb's relation holds of nothing
(`ControlPrinciple.eq_bot_of_denote`). The short passive leaves its agent at an implicit position,
which is no argument of the relation; with such positions closed (`closedPassive`), the passive
of every diathesis of an English verb whose controller is not its object leaves the controller
out, so a verb with such a passive obeying the principle holds of nothing (`eq_bot_of_passive`).

A relation obeying the principle is controlled at the role (`ControlPrinciple.isControlledAt`),
and raising at an argument position when the frame does not depend on the arguments, as that of
a modal or of *seem* does not (`ControlPrinciple.isRaisingAt`). Two relations with dual forces
over one frame, *force* and *allow*, are each the complement of the other at the negated property
(`ControlPrinciple.compl_eq_dual`), and a relation of necessity is factive exactly when its
conversational background is realistic (`ControlPrinciple.subset_iff_isRealistic`).

In the entries of the English verbs a participant that controls in one diathesis controls in
every diathesis of its verb with a nonfinite clausal complement, apart from the raising diathesis
of a verb like *begin* (`controller_eq_or_isRaising`): no entry has a diathesis that leaves its
controller out.

## Implementation notes

* The principle is a predicate on a bare relation, as `ArgumentStructure.IsControlledAt` is, and
  not a structure storing a relation with its role and frame: the classes of control predicates
  are told apart by which transforms of one relation obey it, and a relation determines neither
  its role nor its frame.
* The principle is stated for any family of necessities. The source's frames are simple necessity
  and simple possibility over one conversational background, the case `simpleNecessity (a x)`;
  an ordering source, which it sets aside, is the case `humanNecessity (a x) (g x)`.
* Where the role has no bearer the right side of the principle is false, the source's being
  undefined there.
* A role is a partial function of a relation's arguments, one for each relation, where the
  source's is one partial function on all tuples of a relation and its arguments; that its value
  is among the arguments is not imposed. That a transform lacks a bearer of the role is
  accordingly a hypothesis of `ControlPrinciple.eq_bot_of_mapArgs`; for the relation a diathesis
  denotes, where the role of a participant is the entity at its slot, it is that the diathesis
  leaves the participant out.

## TODO

* The condition that the controller be adjacent to the property in function-argument structure,
  and the rule filling in the role from the thematic hierarchy, are not formalized: the entries
  of the English control verbs record no entailment profiles from which a role could be read.
* The degenerate role borne by an argument with no thematic role, and the correspondence between
  virtual arguments and referential opacity derived from it, are not formalized.
* The source's judgments on passives and intransitives of control verbs are not entered as
  examples.
* A long passive expresses the agent in an adpositional phrase, which the source takes to
  modify the passive predicate; `closedPassive` is the short passive, and the long one is not
  formalized.

## References

* [chierchia-1984]
* [kratzer-1981]
-/

@[expose] public section

namespace Chierchia1984

open Modality ArgumentStructure Filter Function

variable {E W X Y : Type*}

/-! ### The Control Principle -/

/-- (60): the Control Principle for the relation `α`, the role `θ` and the modal frame of the
force `q` and the necessities `N`. The relation holds of a property and its arguments exactly
where the bearer of the role has the property as a necessity, or as a possibility, of the
frame. -/
def ControlPrinciple (α : (E → Set W) → X → Set W) (θ : X →. E) (q : QuantificationalForce)
    (N : X → W → Filter W) : Prop :=
  ∀ P x w, w ∈ α P x ↔ ∃ e ∈ θ x, w ∈ q.claim (N x) (P e)

variable {α β : (E → Set W) → X → Set W} {θ : X →. E} {q : QuantificationalForce}
  {N : X → W → Filter W} {P : E → Set W} {x : X} {w : W} {e : E}

theorem controlPrinciple_iff :
    ControlPrinciple α θ q N ↔ α = atRole θ fun φ x ↦ q.claim (N x) φ :=
  ⟨fun h ↦ funext₂ fun P x ↦ Set.ext fun w ↦
      (h P x w).trans (mem_atRole (S := fun φ x ↦ q.claim (N x) φ)).symm,
    fun h _ _ _ ↦ by rw [h]; exact mem_atRole⟩

namespace ControlPrinciple

theorem eq_atRole (h : ControlPrinciple α θ q N) : α = atRole θ fun φ x ↦ q.claim (N x) φ :=
  controlPrinciple_iff.1 h

-- (17e)
theorem mem_dom (h : ControlPrinciple α θ q N) (hw : w ∈ α P x) : x ∈ θ.Dom :=
  let ⟨e, he, _⟩ := (h P x w).1 hw
  Part.dom_iff_mem.2 ⟨e, he⟩

theorem eq_claim (h : ControlPrinciple α θ q N) (he : e ∈ θ x) (P : E → Set W) :
    α P x = q.claim (N x) (P e) := by
  rw [h.eq_atRole, atRole_apply_of_mem he]

theorem isControlledAt (h : ControlPrinciple α θ q N) : IsControlledAt α θ :=
  h.eq_atRole ▸ isControlledAt_atRole θ _

-- (118c)
theorem isRaisingAt {c : X → E} {N : W → Filter W}
    (h : ControlPrinciple α (c : X →. E) q fun _ ↦ N) : IsRaisingAt α c :=
  h.eq_atRole ▸ isRaisingAt_atRole c (q.claim N)

/-! ### Modal frames -/

/-- Two relations with dual forces over one frame and one role, as *force* and *allow*, are each
the complement of the other at the negated property, where the role has a bearer. -/
theorem compl_eq_dual (h : ControlPrinciple α θ q N) (h' : ControlPrinciple β θ q.dual N)
    (hx : x ∈ θ.Dom) (P : E → Set W) : (α P x)ᶜ = β (fun e ↦ (P e)ᶜ) x := by
  obtain ⟨e, he⟩ := Part.dom_iff_mem.1 hx
  rw [h.eq_claim he, h'.eq_claim he, QuantificationalForce.compl_claim]

-- (45)
theorem disjoint_dual (h : ControlPrinciple α θ q N) (h' : ControlPrinciple β θ q.dual N)
    (P : E → Set W) (x : X) : Disjoint (α P x) (β (fun e ↦ (P e)ᶜ) x) :=
  Set.disjoint_left.2 fun _ hw hw' ↦ (h.compl_eq_dual h' (h.mem_dom hw) P).ge hw' hw

-- (34)
theorem subset_iff_pure_le (h : ControlPrinciple α θ .universal N) (he : e ∈ θ x) :
    (∀ P, α P x ⊆ P e) ↔ ∀ w, pure w ≤ N x w := by
  simp only [h.eq_claim he, pure_le_iff]
  exact ⟨fun hf w s hs ↦ hf (fun _ ↦ s) hs, fun hT P w hw ↦ hT w _ hw⟩

/-- A relation of necessity over a conversational background, as *force* over what its subject
imposes, is factive exactly when the background is realistic. -/
theorem subset_iff_isRealistic {a : X → Background W}
    (h : ControlPrinciple α θ .universal fun x ↦ simpleNecessity (a x)) (he : e ∈ θ x) :
    (∀ P, α P x ⊆ P e) ↔ (a x).IsRealistic :=
  (h.subset_iff_pure_le he).trans isRealistic_iff_pure_le_simpleNecessity.symm

/-! ### Transforms -/

variable {σ : X → Y} {θ' : Y →. E} {N' : Y → W → Filter W} {y : Y}

theorem mem_dom_of_mapArgs (h : ControlPrinciple (mapArgs σ α) θ' q N') (hw : w ∈ α P x) :
    σ x ∈ θ'.Dom :=
  h.mem_dom (le_mapArgs σ α P x hw)

/-- A relation whose transform obeys the principle for a role that no arguments of the transform
bear holds of nothing: where the transforms of a verb obey the principle, none deletes its
controller, neither passive the controlling subject of *promise* nor detransitivization the
controlling object of *force*. -/
theorem eq_bot_of_mapArgs (h : ControlPrinciple (mapArgs σ α) θ' q N') (hθ : θ'.Dom = ∅) :
    α = ⊥ :=
  mapArgs_eq_bot.1 (h.eq_atRole.trans (atRole_eq_bot_of_dom_eq_empty hθ _))

/-- A transform of a relation obeying the principle holds where, for some value of the deleted
arguments, the bearer of the role has the property in the frame: the controller of *it was
decided to leave* is whoever decided. -/
theorem mem_mapArgs_iff (h : ControlPrinciple α θ q N) :
    w ∈ mapArgs σ α P y ↔ ∃ x, σ x = y ∧ ∃ e ∈ θ x, w ∈ q.claim (N x) (P e) := by
  simp only [mem_mapArgs, h P]

-- (82)
theorem mapArgs (h : ControlPrinciple α (fun x ↦ θ' (σ x)) q fun x ↦ N' (σ x))
    (hσ : Surjective σ) : ControlPrinciple (mapArgs σ α) θ' q N' :=
  controlPrinciple_iff.2 <| h.eq_atRole ▸
    mapArgs_comapArgs hσ (atRole θ' fun φ y ↦ q.claim (N' y) φ)

/-! ### Diatheses -/

section Diathesis

variable {I J : Type*} [Nonempty E] {R : (E → Set W) → (I → E) → Set W} {f : I → Option J}
  {i : I} {N : (J → E) → W → Filter W}

-- (84)
theorem eq_bot_of_mapIndex (hf : ∀ i i' j, f i = some j → f i' = some j → i = i')
    (hi : f i = none)
    (h : ControlPrinciple (mapIndex f R) (fun y ↦ ((f i).map y : Part E)) q N) : R = ⊥ :=
  (mapIndex_eq_bot f hf).1 <| h.eq_atRole.trans <|
    atRole_eq_bot_of_dom_eq_empty (Set.eq_empty_of_forall_notMem fun y hy ↦ by
      simp [PFun.Dom, hi] at hy) _

-- (86), (87)
theorem eq_bot_of_denote {n : ℕ} {d : Diathesis n} {R : (E → Set W) → (Fin n → E) → Set W}
    {i : Fin n} {N : (ArgumentFrame.Slot → E) → W → Filter W}
    (hd : ∀ i i' s, d.links.get i = some s → d.links.get i' = some s → i = i')
    (hi : d.links.get i = none)
    (h : ControlPrinciple (d.denote R) (fun y ↦ ((d.links.get i).map y : Part E)) q N) :
    R = ⊥ :=
  eq_bot_of_mapIndex hd hi h

end Diathesis

end ControlPrinciple

/-! ### A relation whose passive has no controller -/

section

variable (P : E → Set W) (y : Y) (w : W)

-- (22a)
example : ControlPrinciple (fun (P : E → Set W) (x : E × Y) ↦ P x.1) (Prod.fst : E × Y → E)
    .universal fun _ ↦ pure :=
  fun _ x _ ↦ ⟨fun hw ↦ ⟨x.1, Part.mem_some _, hw⟩, by
    rintro ⟨e, he, hw⟩
    rwa [Part.mem_some_iff.1 he] at hw⟩

-- (99)
example : w ∈ mapArgs Prod.snd (fun (P : E → Set W) (x : E × Y) ↦ P x.1) P y ↔ ∃ e, w ∈ P e := by
  simp

end

/-! ### The English verbs -/

open English.Verbs in
/-- (17c), (17e): the controller of a diathesis of an English verb is the controller of every
diathesis of the verb that has a clausal complement and no finite one, raising diatheses apart. -/
theorem controller_eq_or_isRaising : ∀ v ∈ verbs, ∀ c ∈ v.valency.diatheses, ∀ i ∈ c.controller,
    ∀ d ∈ v.valency.diatheses, d.HasClausal → ¬ d.HasFinite →
      d.controller = some i ∨ d.IsRaising := by
  decide +kernel

section Passive

open English.Verbs

variable {n : ℕ}

/-- The short passive of a diathesis with the positions that are not expressed closed: the agent,
left implicit, is no argument of the relation the passive denotes. -/
def closedPassive (d : Diathesis n) : Diathesis n :=
  ((Voice.passive d.toArgumentFrame).apply d).restrict fun p ↦ p.IsExpressed

-- (11), (87)
theorem links_closedPassive : ∀ v ∈ verbs, ∀ d ∈ v.valency.diatheses, ∀ i ∈ d.controller,
    d.controllerRole ≠ some .P →
      (closedPassive d).links.get i = none ∧ ∀ j j', ((closedPassive d).links.get j).isSome →
        (closedPassive d).links.get j = (closedPassive d).links.get j' → j = j' := by
  decide +kernel

-- (86), (87)
theorem eq_bot_of_passive [Nonempty E] {v : English.Verbs.Verb} (hv : v ∈ verbs)
    {d : Diathesis v.valency.arity} (hd : d ∈ v.valency.diatheses) {i : Fin v.valency.arity}
    (hi : i ∈ d.controller) (hP : d.controllerRole ≠ some .P)
    {R : (E → Set W) → (Fin v.valency.arity → E) → Set W}
    {N : (ArgumentFrame.Slot → E) → W → Filter W}
    (h : ControlPrinciple ((closedPassive d).denote R)
      (fun y ↦ (((closedPassive d).links.get i).map y : Part E)) q N) : R = ⊥ :=
  let ⟨h₁, h₂⟩ := links_closedPassive v hv d hd i hi hP
  h.eq_bot_of_denote
    (fun j j' _ hj hj' ↦ h₂ j j' (Option.isSome_iff_exists.2 ⟨_, hj⟩) (hj.trans hj'.symm)) h₁

end Passive

end Chierchia1984
