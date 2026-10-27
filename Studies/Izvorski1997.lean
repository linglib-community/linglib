module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Izvorski (1997): The Present Perfect as an Epistemic Modal

This file formalizes the analysis by Izvorski of the perfect of evidentiality, the indirect
evidential that present perfect morphology expresses in Bulgarian, Turkish, Norwegian and other
languages, (1). The evidential is an epistemic modal, (8): it asserts that the proposition holds
in every accessible world closest to the speaker's beliefs about the evidence, in the
possible-worlds semantics of Kratzer with a modal base of indirect evidence and an ordering source
of beliefs about it, (17) to (19), and it presupposes that the speaker has indirect evidence for
the proposition, evidence that exists and does not establish it (`Ev`). Epistemic *must* has the
same force and no such presupposition (`must`), which is why an avowal of having no evidence, (12)
and (13), or of having witnessed the event, (14), is consistent with *must* and not with the
evidential; the presupposition projects through negation, (15), so that a denial targets the
proposition, (16). The variability between the report and inference readings comes from the
ordering source (`necessity_of_beliefs`), and the evidential does not entail its prejacent, as
*must* does not, (9). Section 5 derives the presupposition from the present perfect: the
consequent state of the event is known at speech time, giving the evidence, and the event itself
is not, giving its indirectness (`ev_ne_zero_of_perfect`), and the domain of quantification lies
within the epistemically accessible worlds, so that unlike the counterfactual inference of the
past the evidential meaning is no implicature (`bestWorlds_subset_accessible`).

## Implementation notes

* The presupposition "speaker has indirect evidence for `p`" is rendered as a nonempty
  evidence background whose worlds do not all verify `p`; the report and inference readings
  are not distinguished in the operator, as the paper intends.
* Section 4's temporal and aspectual diagnostics, (20) to (24), are recorded as rows; the
  evidential takes the temporal interpretation of the indicative, which the operator does not
  represent.

## References

* [R. Izvorski, *The Present Perfect as an Epistemic Modal* (1997)][izvorski-1997]
* [A. Kratzer, *Modality* (1991)][kratzer-1991]
-/

@[expose] public section

namespace Izvorski1997

open Modality

variable {W : Type*}

/-- The speaker knows `p` relative to the background `f` when `p` holds throughout the worlds
compatible with it. -/
def Known (f : Background W) (w : W) (p : W → Prop) : Prop := ∀ u ∈ f.accessibleWorlds w, p u

open Classical in
/-- The indirect evidential of (8) and (17) to (19). The background `f` assigns each world the
propositions the speaker counts as indirect evidence, and `g` assigns the speaker's beliefs about
that evidence. The presupposition is that there is such evidence and that it does not establish `p`,
and the assertion is that `p` holds in every accessible world closest to the beliefs. -/
noncomputable def Ev (f g : Background W) (p : W → Prop) : W → SignType :=
  {w | (f w).Nonempty ∧ ¬ Known f w p}.indicator fun w ↦ SignType.ofProp (necessity f g p w)

open Classical in
/-- Epistemic *must* is the same necessity over what is known, with no presupposition about the kind
of evidence. -/
noncomputable def must (f g : Background W) (p : W → Prop) : W → SignType :=
  fun w ↦ SignType.ofProp (necessity f g p w)

variable {f f' g : Background W} {p : W → Prop} {w : W}

-- (8a)
theorem ev_eq_must_of_ne_zero (h : Ev f g p w ≠ 0) : Ev f g p w = must f g p w := by
  rw [Ev, Set.indicator_apply_ne_zero] at h
  rw [Ev, Set.indicator_of_mem h.1, must]

-- (10), (11)
theorem accessible_must_subset (h : f w ⊆ f' w) : f'.accessibleWorlds w ⊆ f.accessibleWorlds w :=
  Background.accessibleWorlds_anti h

-- (12), (13)
theorem ev_eq_zero_of_no_evidence (h : f w = ∅) : Ev f g p w = 0 :=
  Set.indicator_of_notMem (fun hp ↦ hp.1.ne_empty h) _

-- (14)
theorem ev_eq_zero_of_known (h : Known f w p) : Ev f g p w = 0 :=
  Set.indicator_of_notMem (fun hp ↦ hp.2 h) _

-- (15), (16)
theorem support_neg_ev : Function.support (-Ev f g p) = Function.support (Ev f g p) := by
  ext w; simp

theorem necessity_of_beliefs (hex : ∃ u ∈ f.accessibleWorlds w, ∀ q ∈ g w, q u)
    (h : ∀ u ∈ f.accessibleWorlds w, (∀ q ∈ g w, q u) → p u) : necessity f g p w := by
  rw [necessity_iff]
  intro u hu
  rw [bestWorlds, Preorder.minimals_ofCriteria_eq hex] at hu
  exact h u hu.1 hu.2

/-- The best worlds lie within the epistemically accessible worlds, so the evidential meaning is
asserted and is no implicature (Section 5.3). -/
theorem bestWorlds_subset_accessible : bestWorlds f g w ⊆ f.accessibleWorlds w :=
  Preorder.minimals_subset _ _

/-- The evidential is defined when the speaker knows some proposition and does not know `p`, as the
present perfect supplies (Section 5.2). -/
theorem ev_ne_zero_of_perfect {p' : W → Prop} (hp' : p' ∈ f w) (hnot : ¬ Known f w p) :
    Ev f g p w ≠ 0 := by
  rw [Ev, Set.indicator_of_mem (s := {w | (f w).Nonempty ∧ ¬ Known f w p}) ⟨⟨_, hp'⟩, hnot⟩]
  simp

-- (9)
theorem ev_not_entails :
    ∃ (f : Background (Fin 2)) (g : Background (Fin 2)) (p : Fin 2 → Prop) (w : Fin 2),
      Ev f g p w = 1 ∧ ¬ p w := by
  refine ⟨fun _ ↦ {fun _ ↦ True}, fun _ ↦ {fun u ↦ u = 1}, (· = 1), 0, ?_, by decide⟩
  simp only [Ev, Trivalent.indicator_apply_eq_one_iff, Set.mem_ofPred_eq,
    SignType.ofProp_eq_one_iff]
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · intro h
    exact absurd (h 0 (by simp)) (by decide)
  · refine necessity_of_beliefs ⟨1, by simp, ?_⟩ ?_
    · simp
    · intro u _ hu
      exact hu _ (Set.mem_singleton _)

end Izvorski1997
