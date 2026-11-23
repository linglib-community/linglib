module

public import Linglib.Semantics.ArgumentStructure.Control
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Fragments.English.Verbs.Inventory
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

`w ∈ α P x ↔ ∃ e ∈ θ x, w ∈ claim (N x) (P e) q`,

so that it holds of a property exactly where the bearer of the role has the property as a
necessity, or as a possibility, of the frame.

An argument manipulation, such as passive or detransitivization, deletes arguments of a relation
and quantifies them existentially. For `σ` the map from the arguments to those that remain,
`drop σ α P y` is the join of `α P x` over the `x` with `σ x = y`, the lower adjoint of
substitution along `σ` (`gc_drop`).

A relation obeying the principle holds only of arguments among which the role has a bearer
(`ControlPrinciple.mem_dom`). So a relation one of whose transforms obeys the principle, for a role
that has no bearer among the transform's arguments, holds of nothing
(`ControlPrinciple.eq_bot_of_drop`): a verb whose transforms all obey the principle has no passive
when its subject controls and no intransitive when its object does. A transform that keeps the
controller and the frame obeys the principle when the relation does (`ControlPrinciple.drop`).
When only the relation obeys it, a transform that deletes the controller holds where some value
of the deleted argument has the property in the frame (`ControlPrinciple.mem_drop_iff`), the
controller left implicit.

The principle makes a relation one to a proposition and the arguments
(`ControlPrinciple.isControlledAt`), and one to the proposition alone when the frame does not
depend on the arguments, as that of a modal or of *seem* does not
(`ControlPrinciple.isRaisingAt`). Two relations with dual forces over one frame, *force* and
*allow*, are each the complement of the other at the negated property
(`ControlPrinciple.compl_eq_dual`), and a relation of necessity is factive exactly when its
conversational background is realistic (`ControlPrinciple.subset_iff_isRealistic`).

In the entries of the English verbs, the controller of a diathesis fills a slot in every diathesis
of its verb that has a nonfinite clausal complement (`controller_linked`).

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
  accordingly a hypothesis of `ControlPrinciple.eq_bot_of_drop`.

## TODO

* The condition that the controller be adjacent to the property in function-argument structure,
  and the rule filling in the role from the thematic hierarchy, are not formalized: the entries
  of the English control verbs record no entailment profiles from which a role could be read.
* The degenerate role borne by an argument with no thematic role, and the correspondence between
  virtual arguments and referential opacity derived from it, are not formalized.
* The source's judgments on passives and intransitives of control verbs are not entered as
  examples; the entries record no passive diatheses to pair them with.

## References

* [chierchia-1984]
* [kratzer-1981]
-/

@[expose] public section

namespace Chierchia1984

open Modality ArgumentStructure Filter Function

variable {E W X Y Z Φ Ψ : Type*}

/-! ### Argument manipulations -/

section Drop

variable [CompleteLattice Ψ]

/-- (30c): the argument manipulation along `σ`, the map from the arguments of a relation to those
that remain, holds of the remaining arguments when the relation holds for some value of the
deleted ones. -/
def drop (σ : X → Y) (R : (E → Φ) → X → Ψ) : (E → Φ) → Y → Ψ :=
  fun P y ↦ ⨆ x, ⨆ (_ : σ x = y), R P x

/-- Deleting arguments is the lower adjoint of substitution along the map that forgets them. -/
theorem gc_drop (σ : X → Y) :
    GaloisConnection (drop σ : ((E → Φ) → X → Ψ) → _) fun S P x ↦ S P (σ x) :=
  fun R _ ↦ ⟨fun h P x ↦ (le_iSup₂ (f := fun x (_ : σ x = σ x) ↦ R P x) x rfl).trans (h P (σ x)),
    fun h P _ ↦ iSup₂_le fun x hx ↦ hx ▸ h P x⟩

theorem le_drop (σ : X → Y) (R : (E → Φ) → X → Ψ) (P : E → Φ) (x : X) :
    R P x ≤ drop σ R P (σ x) :=
  (gc_drop σ).le_u_l R P x

@[simp] theorem drop_id (R : (E → Φ) → X → Ψ) : drop id R = R := by
  funext P y
  simp [drop]

theorem drop_comp (τ : Y → Z) (σ : X → Y) (R : (E → Φ) → X → Ψ) :
    drop (τ ∘ σ) R = drop τ (drop σ R) :=
  (gc_drop (τ ∘ σ)).l_unique ((gc_drop σ).compose (gc_drop τ)) fun _ ↦ rfl

@[simp] theorem mem_drop {σ : X → Y} {α : (E → Φ) → X → Set W} {P : E → Φ} {y : Y} {w : W} :
    w ∈ drop σ α P y ↔ ∃ x, σ x = y ∧ w ∈ α P x := by
  simp [drop]

end Drop

/-! ### The Control Principle -/

/-- (60): the Control Principle for the relation `α`, the role `θ` and the modal frame of the
force `q` and the necessities `N`. The relation holds of a property and its arguments exactly
where the bearer of the role has the property as a necessity, or as a possibility, of the
frame. -/
def ControlPrinciple (α : (E → Set W) → X → Set W) (θ : X →. E) (q : QuantificationalForce)
    (N : X → W → Filter W) : Prop :=
  ∀ P x w, w ∈ α P x ↔ ∃ e ∈ θ x, w ∈ claim (N x) (P e) q

namespace ControlPrinciple

variable {α β : (E → Set W) → X → Set W} {θ : X →. E} {q : QuantificationalForce}
  {N : X → W → Filter W} {P : E → Set W} {x : X} {w : W} {e : E}

-- (17e)
theorem mem_dom (h : ControlPrinciple α θ q N) (hw : w ∈ α P x) : x ∈ θ.Dom :=
  let ⟨e, he, _⟩ := (h P x w).1 hw
  Part.dom_iff_mem.2 ⟨e, he⟩

theorem eq_claim (h : ControlPrinciple α θ q N) (he : e ∈ θ x) (P : E → Set W) :
    α P x = claim (N x) (P e) q :=
  Set.ext fun w ↦ (h P x w).trans
    ⟨fun ⟨_, he', hw⟩ ↦ Part.mem_unique he he' ▸ hw, fun hw ↦ ⟨e, he, hw⟩⟩

theorem isControlledAt {c : X → E} (h : ControlPrinciple α (c : X →. E) q N) :
    IsControlledAt α c := fun P Q x hPQ ↦ by
  rw [h.eq_claim (Part.mem_some (c x)) P, h.eq_claim (Part.mem_some (c x)) Q, hPQ]

-- (118c)
theorem isRaisingAt {c : X → E} {N : W → Filter W}
    (h : ControlPrinciple α (c : X →. E) q fun _ ↦ N) : IsRaisingAt α c := fun P Q x y hPQ ↦ by
  rw [h.eq_claim (Part.mem_some (c x)) P, h.eq_claim (Part.mem_some (c y)) Q, hPQ]

/-! ### Modal frames -/

/-- Two relations with dual forces over one frame and one role, as *force* and *allow*, are each
the complement of the other at the negated property, where the role has a bearer. -/
theorem compl_eq_dual (h : ControlPrinciple α θ q N) (h' : ControlPrinciple β θ q.dual N)
    (hx : x ∈ θ.Dom) (P : E → Set W) : (α P x)ᶜ = β (fun e ↦ (P e)ᶜ) x := by
  obtain ⟨e, he⟩ := Part.dom_iff_mem.1 hx
  rw [h.eq_claim he, h'.eq_claim he, compl_claim]

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

theorem mem_dom_of_drop (h : ControlPrinciple (drop σ α) θ' q N') (hw : w ∈ α P x) :
    σ x ∈ θ'.Dom :=
  h.mem_dom (le_drop σ α P x hw)

/-- A relation whose transform obeys the principle for a role that no arguments of the transform
bear holds of nothing: where the transforms of a verb obey the principle, none deletes its
controller, neither passive the controlling subject of *promise* nor detransitivization the
controlling object of *force*. -/
theorem eq_bot_of_drop (h : ControlPrinciple (drop σ α) θ' q N') (hθ : θ'.Dom = ∅) : α = ⊥ := by
  funext P x
  exact Set.eq_empty_of_forall_notMem fun w hw ↦ by simpa [hθ] using h.mem_dom_of_drop hw

-- (82)
theorem drop (h : ControlPrinciple α (fun x ↦ θ' (σ x)) q fun x ↦ N' (σ x))
    (hσ : Surjective σ) : ControlPrinciple (drop σ α) θ' q N' := fun P y w ↦ by
  obtain ⟨x, rfl⟩ := hσ y
  simp only [mem_drop, h P]
  exact ⟨by rintro ⟨x', hx', hw⟩; rwa [hx'] at hw, fun hw ↦ ⟨x, rfl, hw⟩⟩

/-- A transform of a relation obeying the principle holds where, for some value of the deleted
arguments, the bearer of the role has the property in the frame: the controller of *it was
decided to leave* is whoever decided. -/
theorem mem_drop_iff (h : ControlPrinciple α θ q N) :
    w ∈ Chierchia1984.drop σ α P y ↔ ∃ x, σ x = y ∧ ∃ e ∈ θ x, w ∈ claim (N x) (P e) q := by
  simp only [mem_drop, h P]

end ControlPrinciple

/-! ### A relation whose passive has no controller -/

section

variable (P : E → Set W) (y : Y) (w : W)

-- (22a)
example : ControlPrinciple (fun (P : E → Set W) (x : E × Y) ↦ P x.1) (Prod.fst : E × Y → E)
    .universal fun _ ↦ pure :=
  fun _ x _ ↦ ⟨fun hw ↦ ⟨x.1, Part.mem_some _, hw⟩, fun ⟨_, he, hw⟩ ↦ Part.mem_some_iff.1 he ▸ hw⟩

-- (99)
example : w ∈ drop Prod.snd (fun (P : E → Set W) (x : E × Y) ↦ P x.1) P y ↔ ∃ e, w ∈ P e := by
  simp

end

/-! ### The English verbs -/

open English.Verbs in
/-- (17e): the controller of a diathesis of an English verb fills a slot in every diathesis of
the verb that has a clausal complement and no finite one. -/
theorem controller_linked : ∀ v ∈ verbs, ∀ c ∈ v.valency.diatheses, ∀ i ∈ c.controller,
    ∀ d ∈ v.valency.diatheses, d.HasClausal → ¬ d.HasFinite → (d.links.get i).isSome := by
  decide +kernel

end Chierchia1984
