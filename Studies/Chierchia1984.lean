module

public import Linglib.Semantics.ArgumentStructure.Relation.Control
public import Linglib.Semantics.ArgumentStructure.Relation.Denotation
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Languages.English.Verbs.Inventory
public import Linglib.Syntax.Voice.Apply
public import Mathlib.Data.PFun

/-!
# Chierchia (1984): Topics in the syntax and semantics of infinitives and gerunds

This file formalizes the theory of control in [chierchia-1984].

In this theory an infinitive or gerund denotes a property. A verb that takes one denotes a
relation `α : (E → Set W) → X → Set W` between a property and the verb's other arguments `X`.
Control is an entailment of that relation, stated by the *Control Principle*.

The principle has three parameters.

* A *role* `θ : X →. E` is a partial function. It picks out the controller among the arguments.
* A *force* `q` is necessity or possibility.
* The *necessities* `N x w` form a filter of propositions, for each choice of arguments `x` and
  each world `w`. In the source these are the propositions that follow from a conversational
  background of [kratzer-1981], `simpleNecessity (a x) w`. For *try* the background holds what
  the subject aims at. For *force* it holds what the subject imposes on the object.

We define `ControlPrinciple α θ q N` as

`w ∈ α P x ↔ ∃ e ∈ θ x, w ∈ q.claim (N x) (P e)`.

So `α P x` holds at `w` exactly when the controller exists and has the property `P` as a
necessity, or as a possibility, at `w`. Equivalently, `α = atRole θ fun φ x ↦ q.claim (N x) φ`
(`controlPrinciple_iff`).

We show that a relation obeying the principle holds only of arguments that include a controller
(`ControlPrinciple.mem_dom`). It is controlled at `θ` (`ControlPrinciple.isControlledAt`). It is
raising at a position when `N` does not depend on the arguments
(`ControlPrinciple.isRaisingAt`).

Two results concern the force. Suppose `α` and `β` obey the principle with dual forces and the
same role and necessities, as *force* and *allow* do. Then `(α P x)ᶜ = β (fun e ↦ (P e)ᶜ) x`
whenever a controller exists (`ControlPrinciple.compl_eq_dual`). Suppose `α` obeys the principle
with necessity over a conversational background. Then `α P x ⊆ P e` for all `P` exactly when the
background is realistic (`ControlPrinciple.subset_iff_isRealistic`).

Passive and detransitivization remove an argument of a relation and existentially quantify it.
We write the result as `mapArgs σ α`, where `σ` forgets the removed argument. We show that if
`mapArgs σ α` obeys the principle with a role that is nowhere defined, then `α = ⊥`
(`ControlPrinciple.eq_bot_of_mapArgs`). So a verb whose subject controls has no passive, and a
verb whose object controls has no intransitive use. If only `α` obeys the principle, then
`mapArgs σ α P y` holds exactly when some value of the removed argument is a controller with the
property (`ControlPrinciple.mem_mapArgs_iff`). This is the case of *it was decided to leave*.

For a diathesis `d` of a verb with relation `R`, the hypothesis of the first result is computed.
If `d` leaves participant `i` at no slot and `d.denote R` obeys the principle with the role of
`i`, then `R = ⊥` (`ControlPrinciple.eq_bot_of_denote`). We define `closedPassive d` as the short
passive of `d` with the participants at unexpressed positions unlinked. For every diathesis of an
English verb whose controller is not its object, `closedPassive d` leaves the controller at no
slot, so the result applies (`eq_bot_of_passive`).

We also show that in the entries of the English verbs, a participant that controls in one
diathesis controls in every diathesis of that verb with a nonfinite clausal complement, except in
a raising diathesis such as that of *begin* (`controller_eq_or_isRaising`).

## Implementation notes

* `ControlPrinciple` is a predicate on a bare relation, like `ArgumentStructure.IsControlledAt`.
  We do not bundle a relation with its role and necessities, because one relation can obey the
  principle while its passive does not.
* The source states the principle for simple necessity and simple possibility over one
  conversational background. We state it for any family of filters `N`. Simple necessity is the
  case `N x = simpleNecessity (a x)`.
* When `θ x` is undefined, the right side of the principle is false. In the source it is
  undefined.
* In the source a role is one partial function on all tuples of a relation and its arguments.
  Here each relation has its own role `θ : X →. E`.

## TODO

* The source requires the controller to be adjacent to the property in function-argument
  structure, and fills in the role from a hierarchy of thematic roles. Neither is formalized.
  The entries of the English control verbs record no entailment profiles to read a role from.
* The source defines a role for arguments that have no thematic role, and uses it to relate
  expletive subjects to referential opacity. This is not formalized.
* The source's judgments on passives and intransitives of control verbs are not entered as
  examples.
* `closedPassive` is the short passive. The long passive, with the agent in an adpositional
  phrase, is not formalized.

## References

* [chierchia-1984]
* [kratzer-1981]
-/

@[expose] public section

namespace Chierchia1984

open Modality ArgumentStructure Filter Function

variable {E W X Y : Type*}

/-! ### The Control Principle -/

/-- (60): the Control Principle. The relation `α P x` holds at `w` exactly when the controller
`θ x` exists and has the property `P` as a necessity, or as a possibility, of `N x w`. -/
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

/-- Relations that obey the principle with dual forces, as *force* and *allow* do, are
complements of each other at the negated property, when a controller exists. -/
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

/-- A relation that obeys the principle with necessity over a conversational background is
factive exactly when the background is realistic. -/
theorem subset_iff_isRealistic {a : X → Background W}
    (h : ControlPrinciple α θ .universal fun x ↦ simpleNecessity (a x)) (he : e ∈ θ x) :
    (∀ P, α P x ⊆ P e) ↔ (a x).IsRealistic :=
  (h.subset_iff_pure_le he).trans isRealistic_iff_pure_le_simpleNecessity.symm

/-! ### Transforms -/

variable {σ : X → Y} {θ' : Y →. E} {N' : Y → W → Filter W} {y : Y}

theorem mem_dom_of_mapArgs (h : ControlPrinciple (mapArgs σ α) θ' q N') (hw : w ∈ α P x) :
    σ x ∈ θ'.Dom :=
  h.mem_dom (le_mapArgs σ α P x hw)

/-- If `mapArgs σ α` obeys the principle with a role that is nowhere defined, then `α = ⊥`. So
passive cannot remove a controlling subject, and detransitivization cannot remove a controlling
object. -/
theorem eq_bot_of_mapArgs (h : ControlPrinciple (mapArgs σ α) θ' q N') (hθ : θ'.Dom = ∅) :
    α = ⊥ :=
  mapArgs_eq_bot.1 (h.eq_atRole.trans (atRole_eq_bot_of_dom_eq_empty hθ _))

/-- If `α` obeys the principle, `mapArgs σ α P y` holds exactly when some `x` with `σ x = y` has
a controller with the property. -/
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
/-- (17c), (17e): a participant that controls in one diathesis of an English verb controls in
each of its diatheses with a nonfinite clausal complement, unless that diathesis is raising. -/
theorem controller_eq_or_isRaising : ∀ v ∈ verbs, ∀ c ∈ v.valency.diatheses, ∀ i ∈ c.controller,
    ∀ d ∈ v.valency.diatheses, d.HasClausal → ¬ d.HasFinite →
      d.controller = some i ∨ d.IsRaising := by
  decide +kernel

section Passive

open English.Verbs

variable {n : ℕ}

/-- The short passive of a diathesis, with the participants at unexpressed positions unlinked.
The implicit agent is then at no slot. -/
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
