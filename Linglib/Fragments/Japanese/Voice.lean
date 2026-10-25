module

public import Linglib.Syntax.Voice.Basic

/-!
# Japanese voice

Japanese has two passives in *-(r)are-*. The direct passive makes the object the subject and
demotes the agent, which may be marked by *niyotte*; it needs a verb that introduces an
external argument, so an unaccusative has none. The indirect or adversative passive adds an
affected participant as subject to a verb of any frame, unaccusatives included, the initial
subject taking *ni* only; the substitution of *niyotte* is Jo and Seo's test for the two.

## Main definitions

* `Japanese.directPassive` — the direct passive of the transitive construction
* `Japanese.indirectPassive` — the indirect passive of a frame
* `Japanese.DirectPassivizable` — a verb that introduces an external argument

## Main results

* `Japanese.directPassive_isPassivization` — the direct passive is a passivization
* `Japanese.newParticipant_indirectPassive` — the indirect passive introduces an affected
  subject, the A of a transitive and the S of an intransitive construction

## References

* [jo-seo-2023]
* [ozaki-2026]
-/

@[expose] public section

namespace Japanese

open ArgumentFrame.Slot

/-- The direct passive: the object becomes the subject and the agent is demoted, expressible
with *niyotte*. -/
def directPassive : Voice := Voice.passive.marked [.suff "(r)are"]

/-- The indirect passive of a frame, the transitive one by default: an affected participant is
the new subject, the initial subject becomes a *ni*-phrase and the complements keep their
positions after it. -/
def indirectPassive (fr : ArgumentFrame := .np) : Voice :=
  (Voice.of fr
    ⟨some .nominal,
      (fr.external.map fun _ ↦ ArgumentFrame.Position.adpositional (some .grammatical)).toList ++
        fr.complements⟩
    ((fr.external.map fun _ ↦ some (complement 0)).toList ++
      (List.range fr.complements.length).map (fun i ↦
        some (complement (i + fr.external.toList.length))) ++ [some external])).marked
    [.suff "(r)are"]

/-- A verb the direct passive applies to: one whose voice type introduces an external
argument. -/
def DirectPassivizable (w : Verb) : Prop := ∃ vt ∈ w.voiceType, vt.AssignsTheta

instance (w : Verb) : Decidable (DirectPassivizable w) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem directPassive_isPassivization : directPassive.IsPassivization := by decide

/-- The indirect passive introduces an affected subject: the A of a transitive verb's derived
construction, the S of an intransitive verb's. -/
theorem newParticipant_indirectPassive :
    (indirectPassive).newParticipant = some .A ∧
      (indirectPassive .intransitive).newParticipant = some .S := by
  decide

end Japanese
