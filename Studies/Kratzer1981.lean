/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Data.Examples.Kratzer1981
public import Studies.Kratzer1977

/-!
# Kratzer (1981): The Notional Category of Modality

A modal depends on two conversational backgrounds, a modal base that fixes the accessible worlds
and an ordering source that ranks them. Where the two are consistent, what is necessary [is what
follows from both](##must_pub_of_wants_office). The split earns its keep where they are not: someone
who wants to become mayor and to avoid the pub that becoming mayor requires [may conclude neither
that they must go nor that they must stay away, nor that they could become mayor without
going](##practical_inference), and the earlier analysis, which pools the two backgrounds, [wrongly
allows the last](##facts_have_priority). An if-clause adds to the modal base, so that the kinds of
conditional are settings of the backgrounds: material implication, strict implication,
counterfactuals with [their vagueness about what is the case](##counterfactual_vague), and deontic
conditionals, on which [the paradox of the traditional analysis
disappears](##deontic_conditionals) and [strengthening the antecedent, transitivity and
contraposition fail](##inference_patterns_fail).

## Implementation notes

* The library's scan of the paper lacks pp. 48–49, which define human necessity and the graded
  notions, and repeats pp. 70–71. `humanNecessity` is the library's definition, checked here against
  how pp. 66–67 reason with it (`humanPossibility_of_goodPossibility`).
* The worlds of each example are finite, so its claims are decided once the backgrounds are
  unfolded.
* The ordering source of the deontic example, what is morally commanded, is left informal in the
  paper and is rendered by two ideals, that there is no injustice and that any injustice is amended
  for. The paper claims only that the verdicts on (76) and (77) are not excluded (p. 71). The
  revised version in [kratzer-2012] numbers the example (59)–(61) and has the injustice rewarded
  instead.
* Under a totally realistic modal base the ordering source is idle (`material_implication`), so the
  inference patterns the paper expects to fail with a non-empty ordering source fail only where the
  base leaves several worlds open.

## TODO

* The graded notions of §3 and the entailments (a)–(i) of p. 50 among sentences (11)–(18) need the
  missing pp. 48–49.
* Which modal bases and ordering sources each German modal admits (§§4–6), and the rule of
  accommodation (p. 61).
* The finite sequences of ordering sources of the conclusion (p. 72).

## References

* [kratzer-1981]
* [kratzer-1977]
* [kratzer-2012] — chapter 2, the revised version of the paper
* [lewis-1973b]
-/

@[expose] public section

namespace Kratzer1981

open Modality

/-! ### Grades of possibility -/

-- p. 67: a world below which `p` holds throughout makes `p` a human possibility.
theorem humanPossibility_of_goodPossibility {W : Type*} {f g : Background W} {p : W → Prop} {w : W}
    (h : goodPossibility f g p w) : humanPossibility f g p w := fun hN ↦ by
  obtain ⟨u, hu, hp⟩ := goodPossibility_iff.1 h
  obtain ⟨v, hv, hvu, hz⟩ := humanNecessity_iff.1 hN u hu
  exact hz v hv (@le_refl _ (premisePreorder (g w)) v) (hp v hv hvu)

-- p. 50: over the empty ordering source human necessity is simple necessity.
example {W : Type*} (f : Background W) (p : W → Prop) (w : W) :
    humanNecessity f ⊥ p w ↔ simpleNecessity f p w :=
  humanNecessity_bot_iff f p w

/-! ### The quest for certainty -/

-- (40), (41), p. 57: on a realistic base alone *must* would entail its prejacent, a stronger claim
-- than the bare sentence, contrary to fact.
theorem prejacent_of_humanNecessity_bot {W : Type*} {f : Background W} (hf : f.IsRealistic)
    {p : W → Prop} {w : W} (h : humanNecessity f ⊥ p w) : p w :=
  (simpleNecessity_iff f p w).1 ((humanNecessity_bot_iff f p w).1 h) w (hf w)

-- (41), p. 57: an ordering source of less reliable information frees *must* from its prejacent.
theorem must_without_prejacent :
    humanNecessity (⊥ : Background Bool) (Function.const Bool {(· = true)}) (· = true) false :=
  humanNecessity_iff.2 fun _ _ ↦ ⟨true, by simp, by simp [Preorder.ofCriteria_le_iff],
    fun z _ hz ↦ by simpa [Preorder.ofCriteria_le_iff] using hz⟩

/-! ### Two kinds of modal base -/

-- (26), p. 53: Kathl could make a pound of cheese given the general circumstances, though in view
-- of everything known she will not.
theorem can_circumstantial_not_epistemic :
    simplePossibility (⊥ : Background Bool) (· = true) false ∧
      ¬ simplePossibility (fun w ↦ {(· = w)}) (· = true) false := by
  simp [simplePossibility_iff]

/-! ### Practical inference -/

/-- A world records whether the speaker becomes mayor and whether they go to the pub regularly. -/
abbrev World := Bool × Bool

/-- The evaluation world, arbitrary since the backgrounds are constant. -/
def w₀ : World := (false, false)

/-- The relevant circumstances are that the speaker becomes mayor only by going to the pub. -/
def circumstances : Background World := Function.const World {fun w ↦ w.1 = true → w.2 = true}

/-- In the first inference all the speaker wants is to become mayor. -/
def wantsOffice : Background World := Function.const World {fun w ↦ w.1 = true}

/-- In the second the speaker wants to become mayor and to avoid the pub. -/
def desires : Background World :=
  Function.const World {fun w ↦ w.1 = true, fun w ↦ w.2 = false}

/-- Decide a claim about the backgrounds and the ordering over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| (simp only [Background.mem_accessibleWorlds, Preorder.ofCriteria_le_iff,
      circumstances, desires, wantsOffice, Function.const_apply, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true,
      Pi.sup_apply, Set.sup_eq_union, Set.mem_union, or_imp, forall_and]; try decide))

-- p. 65: the two backgrounds being consistent, what is necessary is what follows from their union.
theorem must_pub_of_wants_office : humanNecessity circumstances wantsOffice (·.2 = true) w₀ := by
  refine (humanNecessity_iff_simpleNecessity_sup ⟨(true, true), ?_⟩).2 ?_
  · decide_worlds
  · rw [simpleNecessity_iff]
    decide_worlds

-- p. 67: `h(w)` is inconsistent in the second inference.
theorem not_consistent_desires : (circumstances ⊔ desires).accessibleWorlds w₀ = ∅ :=
  Set.eq_empty_of_forall_notMem fun v ↦ by
    revert v
    decide_worlds

-- (c), p. 66
theorem mayor_pub_incomparable :
    ¬ ((true, true) ≤[desires w₀] (false, false)) ∧
      ¬ ((false, false) ≤[desires w₀] (true, true)) := by
  decide_worlds

-- (f), p. 66
theorem pub_no_mayor_worst :
    ∀ v ∈ ({(true, true), (false, false)} : Set World),
      (v ≤[desires w₀] (false, true)) ∧
        ¬ ((false, true) ≤[desires w₀] v) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  decide_worlds

theorem no_dominant_world :
    ¬ ∃ w ∈ circumstances.accessibleWorlds w₀,
      ∀ v ∈ circumstances.accessibleWorlds w₀, (w ≤[desires w₀] v) := by
  decide_worlds

theorem mem_bestWorlds_iff (w : World) :
    w ∈ bestWorlds circumstances desires w₀ ↔ w = (true, true) ∨ w = (false, false) := by
  revert w
  simp only [mem_bestWorlds]
  decide_worlds

theorem limitAssumption : LimitAssumption circumstances desires w₀ :=
  .of_finite _ _ _

/-- Decide a verdict of the limit-free operators through the best worlds. -/
scoped macro "decide_verdict" : tactic =>
  `(tactic| (simp only [humanPossibility, humanNecessity_iff_necessity limitAssumption,
      necessity, ModalLogic.Box, mem_bestAccessible, mem_bestWorlds_iff, forall_eq_or_imp,
      forall_eq]; decide))

/-- Of the five conclusions (p. 66), the speaker may conclude neither that they must go to the pub,
nor that they must stay away, nor that they could become mayor without going, and may conclude that
they could go and that they could stay away. -/
theorem practical_inference :
    ¬ humanNecessity circumstances desires (·.2 = true) w₀ ∧
      ¬ humanNecessity circumstances desires (·.2 = false) w₀ ∧
      ¬ humanPossibility circumstances desires (fun w ↦ w.2 = false ∧ w.1 = true) w₀ ∧
      humanPossibility circumstances desires (·.2 = true) w₀ ∧
      humanPossibility circumstances desires (·.2 = false) w₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide_verdict

-- p. 67: conclusion four by the paper's own route, from a world below which they go to the pub.
theorem can_pub_of_branch : humanPossibility circumstances desires (·.2 = true) w₀ :=
  humanPossibility_of_goodPossibility <| goodPossibility_iff.2 ⟨(true, true), by decide_worlds, by
    decide_worlds⟩

/-- Facts have priority over ideals: pooling the circumstances and the desires into one background,
as the earlier analysis of [kratzer-1977] does, makes it possible to become mayor without the pub,
since a maximal consistent subset contains all that is wanted, and the two-background analysis
rightly does not (p. 67). -/
theorem facts_have_priority :
    Kratzer1977.CanInView (circumstances ⊔ desires) (fun w ↦ w.2 = false ∧ w.1 = true) w₀ ∧
      ¬ humanPossibility circumstances desires (fun w ↦ w.2 = false ∧ w.1 = true) w₀ := by
  refine ⟨Kratzer1977.canInView_iff_humanPossibility.2
    (humanPossibility_of_goodPossibility (goodPossibility_iff.2 ⟨(true, false), by simp, ?_⟩)),
    practical_inference.2.2.1⟩
  simp only [Background.accessibleWorlds_bot, Set.mem_univ, forall_true_left]
  decide_worlds

/-! ### Conditionals

An if-clause adds its proposition to the modal base of the modal in its matrix clause (p. 68), so
`(if α) (necessarily β)` is the necessity of `β` at the base enlarged by `α`. -/

open Conditional.Restrictor

-- p. 68: the paper gives this for the empty ordering source; a totally realistic base leaves at
-- most the world of evaluation to rank, whatever the ordering source.
theorem material_implication {W : Type*} {f g : Background W} (hf : f.IsTotallyRealistic)
    (α β : W → Prop) (w : W) : conditionalNecessity f g α β w ↔ (α w → β w) := by
  have hacc (u : W) : u ∈ (f.restrict α).accessibleWorlds w ↔ u = w ∧ α u := by
    rw [Background.mem_accessibleWorlds_restrict, hf w]
    rfl
  have hrefl (u : W) : u ≤[g w] u := @le_refl _ (premisePreorder (g w)) u
  rw [conditionalNecessity, humanNecessity_iff]
  refine ⟨fun h hα ↦ ?_, fun h u hu ↦ ?_⟩
  · obtain ⟨v, hv, -, hz⟩ := h w ((hacc w).2 ⟨rfl, hα⟩)
    obtain ⟨rfl, -⟩ := (hacc v).1 hv
    exact hz v hv (hrefl v)
  · obtain ⟨rfl, hα⟩ := (hacc u).1 hu
    exact ⟨u, hu, hrefl u, fun z hz _ ↦ by obtain ⟨rfl, -⟩ := (hacc z).1 hz; exact h hα⟩

-- p. 69
theorem strict_implication {W : Type*} (α β : W → Prop) (w : W) :
    conditionalNecessity ⊥ ⊥ α β w ↔ ∀ v, α v → β v := by
  rw [restrictor_eq_strict, Conditional.mem_strictImp_forall, Background.accessibleWorlds_bot]
  simp

-- p. 69: where the antecedent is true, a counterfactual, with an empty base and a totally realistic
-- ordering source, is the mirror image of material implication.
theorem counterfactual_of_antecedent {W : Type*} {g : Background W} (hg : g.IsTotallyRealistic)
    {α β : W → Prop} {w : W} (hα : α w) : conditionalNecessity ⊥ g α β w ↔ β w := by
  have htrue : ∀ p ∈ g w, p w := Background.mem_accessibleWorlds.1 (by rw [hg w]; rfl)
  have hbelow (z : W) (hz : z ≤[g w] w) : z = w := by
    have hz' : z ∈ g.accessibleWorlds w := Background.mem_accessibleWorlds.2 fun p hp ↦
      (Preorder.ofCriteria_le_iff ..).1 hz p hp (htrue p hp)
    rwa [hg w] at hz'
  have hw : w ∈ (Background.restrict ⊥ α).accessibleWorlds w :=
    Background.mem_accessibleWorlds_restrict.2 ⟨by simp, hα⟩
  rw [conditionalNecessity, humanNecessity_iff]
  refine ⟨fun h ↦ ?_, fun h u _ ↦ ⟨w, hw, ?_, fun z _ hz ↦ hbelow z hz ▸ h⟩⟩
  · obtain ⟨v, hv, hvw, hz⟩ := h w hw
    obtain rfl := hbelow v hvw
    exact hz v hv (@le_refl _ (premisePreorder (g v)) v)
  · exact (Preorder.ofCriteria_le_iff ..).2 fun p hp _ ↦ htrue p hp

/-- Two totally realistic backgrounds at a world: its facts severally, `g₁`, and jointly, `g₂`. -/
def factsSeverally : Background World := fun w ↦ {fun v ↦ v.1 = w.1, fun v ↦ v.2 = w.2}

/-- The facts of a world jointly. -/
def factsJointly : Background World := fun w ↦ {fun v ↦ v = w}

theorem isTotallyRealistic_factsSeverally : factsSeverally.IsTotallyRealistic := fun w ↦ by
  ext v
  simp [factsSeverally, Prod.ext_iff]

theorem isTotallyRealistic_factsJointly : factsJointly.IsTotallyRealistic := fun w ↦ by
  ext v
  simp [factsJointly]

-- p. 70: `g₁(w) = {r, s}` and `g₂(w) = {r ∩ s}` order `u`, with `r` only, and `v`, with neither.
theorem ordering_differs {W : Type*} {r s : W → Prop} {u v : W} (hr : r u) (hs : ¬ s u)
    (hr' : ¬ r v) :
    (v ≤[({fun x ↦ r x ∧ s x} : Set (W → Prop))] u) ∧
      ¬ (v ≤[({r, s} : Set (W → Prop))] u) := by
  simp [Preorder.ofCriteria_le_iff, hr, hs, hr']

/-- Decide a claim about a conditional over a finite set of worlds. -/
scoped macro "decide_conditional" : tactic =>
  `(tactic| (simp only [conditionalNecessity_iff_necessity_of_finite, necessity, ModalLogic.Box,
      mem_bestAccessible, mem_bestWorlds, Background.mem_accessibleWorlds_restrict,
      Background.accessibleWorlds_bot, Set.mem_univ, true_and, Preorder.ofCriteria_le_iff,
      factsSeverally, factsJointly, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq, Prod.forall, Bool.forall_bool]; simp))

/-- The vagueness of counterfactuals (p. 70): two totally realistic ordering sources that differ
only in how they carve up the facts disagree on a counterfactual, whereas as modal bases they agree
on every material implication. -/
theorem counterfactual_vague :
    (conditionalNecessity ⊥ factsSeverally (fun w ↦ ¬ (w.1 = true ∧ w.2 = true))
        (fun w ↦ w.1 = true ∨ w.2 = true) (true, true) ∧
      ¬ conditionalNecessity ⊥ factsJointly (fun w ↦ ¬ (w.1 = true ∧ w.2 = true))
        (fun w ↦ w.1 = true ∨ w.2 = true) (true, true)) ∧
      ∀ (α β : World → Prop) (w : World), conditionalNecessity factsSeverally ⊥ α β w ↔
        conditionalNecessity factsJointly ⊥ α β w :=
  ⟨⟨by decide_conditional, by decide_conditional⟩, fun α β w ↦
    (material_implication isTotallyRealistic_factsSeverally α β w).trans
      (material_implication isTotallyRealistic_factsJointly α β w).symm⟩

theorem traditional_vacuous {W : Type*} (f : Background W) (α β : W → Prop) (w : W)
    (h : simpleNecessity f (fun v ↦ ¬ α v) w) : simpleNecessity f (fun v ↦ α v → β v) w :=
  fun v hv hα ↦ absurd hα (h v hv)

/-! #### The deontic example -/

/-- An injustice was amended for, its victim reduced to silence, or neither. -/
inductive Redress where
  | amended
  | silenced
  | neither
  deriving DecidableEq, Repr, Fintype

/-- A situation has no injustice, or an injustice and what became of it. -/
abbrev Situation := Option Redress

/-- Someone was treated unjustly. -/
def injustice (s : Situation) : Prop := s.isSome = true

/-- The injustice was amended for. -/
def amended (s : Situation) : Prop := s = some .amended

/-- The one treated unjustly was reduced to silence. -/
def silenced (s : Situation) : Prop := s = some .silenced

instance : DecidablePred injustice := fun s ↦ inferInstanceAs (Decidable (s.isSome = true))
instance : DecidablePred amended := fun s ↦ inferInstanceAs (Decidable (s = some .amended))
instance : DecidablePred silenced := fun s ↦ inferInstanceAs (Decidable (s = some .silenced))

/-- What is morally commanded is that there be no injustice and that any injustice be amended for. A
situation with amended injustice is not ideal, but it is closer to the ideal than one where the
victim is reduced to silence (p. 71). -/
def morallyCommanded : Background Situation :=
  Function.const Situation {fun s ↦ ¬ injustice s, fun s ↦ injustice s → amended s}

/-- Decide a claim about the backgrounds and the ordering over the four situations. -/
scoped macro "decide_situations" : tactic =>
  `(tactic| (simp only [conditionalNecessity_iff_necessity_of_finite, necessity, ModalLogic.Box,
      mem_bestAccessible, mem_bestWorlds, simpleNecessity_iff, Background.mem_accessibleWorlds,
      Background.mem_accessibleWorlds_restrict, Background.accessibleWorlds_bot, Set.mem_univ,
      true_and, Preorder.ofCriteria_le_iff, morallyCommanded, Function.const_apply,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, false_implies,
      implies_true, and_true, injustice, amended, silenced, Background.restrict, Pi.bot_apply,
      Set.bot_eq_empty, Set.mem_empty_iff_false, or_false]; decide))

/-- On the traditional analysis, with the worlds where the moral ideals are all realized accessible,
(75) makes (76) and (77) both vacuously true (p. 71). On the paper's it does not: with an empty base
restricted by the antecedent and the ordering source of what is morally commanded, (75) and (76) are
true and (77) is false. -/
theorem deontic_conditionals :
    (simpleNecessity morallyCommanded (fun s ↦ ¬ injustice s) none ∧
      simpleNecessity morallyCommanded (fun s ↦ injustice s → amended s) none ∧
      simpleNecessity morallyCommanded (fun s ↦ injustice s → silenced s) none) ∧
    necessity ⊥ morallyCommanded (fun s ↦ ¬ injustice s) none ∧
    conditionalNecessity ⊥ morallyCommanded injustice amended none ∧
    ¬ conditionalNecessity ⊥ morallyCommanded injustice silenced none := by
  have h : simpleNecessity morallyCommanded (fun s ↦ ¬ injustice s) none := by decide_situations
  refine ⟨⟨h, traditional_vacuous _ _ _ _ h, traditional_vacuous _ _ _ _ h⟩, ?_, ?_, ?_⟩
  all_goals decide_situations

/-! #### Inference patterns -/

-- p. 72: with the empty ordering source the patterns hold.
theorem inference_patterns_of_bot {W : Type*} (f : Background W) (α β γ : W → Prop) (w : W) :
    (conditionalNecessity f ⊥ α β w → conditionalNecessity f ⊥ (fun v ↦ α v ∧ γ v) β w) ∧
    (conditionalNecessity f ⊥ α β w → conditionalNecessity f ⊥ β γ w →
      conditionalNecessity f ⊥ α γ w) ∧
    (conditionalNecessity f ⊥ α β w →
      conditionalNecessity f ⊥ (fun v ↦ ¬ β v) (fun v ↦ ¬ α v) w) := by
  simp only [conditionalNecessity, humanNecessity_bot_iff, simpleNecessity_iff,
    Background.mem_accessibleWorlds_restrict]
  exact ⟨fun h v hv ↦ h v ⟨hv.1, hv.2.1⟩, fun h h' v hv ↦ h' v ⟨hv.1, h v hv⟩,
    fun h v hv hα ↦ hv.2 (h v ⟨hv.1, hα⟩)⟩

/-- With a non-empty ordering source strengthening the antecedent, transitivity and contraposition
fail (pp. 71–72): an injustice must be amended for, but not if the victim was silenced; anyone
silenced was treated unjustly, and an injustice must be amended for, but a silencing need not be;
and an injustice must leave things just, but a situation that is not just need not be free of
injustice. -/
theorem inference_patterns_fail :
    (conditionalNecessity ⊥ morallyCommanded injustice amended none ∧
      ¬ conditionalNecessity ⊥ morallyCommanded (fun s ↦ injustice s ∧ silenced s) amended none) ∧
    (conditionalNecessity ⊥ morallyCommanded silenced injustice none ∧
      conditionalNecessity ⊥ morallyCommanded injustice amended none ∧
      ¬ conditionalNecessity ⊥ morallyCommanded silenced amended none) ∧
    (conditionalNecessity ⊥ morallyCommanded injustice (fun s ↦ injustice s → amended s) none ∧
      ¬ conditionalNecessity ⊥ morallyCommanded (fun s ↦ ¬ (injustice s → amended s))
        (fun s ↦ ¬ injustice s) none) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals decide_situations

/-! ### The verdicts -/

-- pp. 65–66, 70–71: a row's verdict is true exactly when the model's prediction holds.
theorem rows_verdicts :
    (Examples.first.verdict = some true ↔
      humanNecessity circumstances wantsOffice (·.2 = true) w₀) ∧
    (Examples.one.verdict = some true ↔ humanNecessity circumstances desires (·.2 = true) w₀) ∧
    (Examples.two.verdict = some true ↔ humanNecessity circumstances desires (·.2 = false) w₀) ∧
    (Examples.three.verdict = some true ↔
      humanPossibility circumstances desires (fun w ↦ w.2 = false ∧ w.1 = true) w₀) ∧
    (Examples.four.verdict = some true ↔ humanPossibility circumstances desires (·.2 = true) w₀) ∧
    (Examples.five.verdict = some true ↔
      humanPossibility circumstances desires (·.2 = false) w₀) ∧
    (Examples.ex_75.verdict = some true ↔
      necessity ⊥ morallyCommanded (fun s ↦ ¬ injustice s) none) ∧
    (Examples.ex_76.verdict = some true ↔
      conditionalNecessity ⊥ morallyCommanded injustice amended none) ∧
    (Examples.ex_77.verdict = some true ↔
      conditionalNecessity ⊥ morallyCommanded injustice silenced none) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := practical_inference
  obtain ⟨-, h₇₅, h₇₆, h₇₇⟩ := deontic_conditionals
  exact ⟨iff_of_true rfl must_pub_of_wants_office, iff_of_false (by decide) h₁,
    iff_of_false (by decide) h₂, iff_of_false (by decide) h₃, iff_of_true rfl h₄,
    iff_of_true rfl h₅, iff_of_true rfl h₇₅, iff_of_true rfl h₇₆, iff_of_false (by decide) h₇₇⟩

end Kratzer1981
