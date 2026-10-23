module

public import Mathlib.Data.List.MinMax
public import Linglib.Semantics.ArgumentStructure.LevinClass.Basic
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Studies.Pesetsky1995

/-!
# Hartshorne et al. (2016): Psych verbs, the linking problem, and the acquisition of language

This file formalizes Hartshorne et al.'s resolution of the psych-verb linking problem.
Fear-type verbs (*Agnes feared Bartholomew*) and frighten-type verbs (*Bartholomew frightened
Agnes*) describe the same emotions with reversed linking, the strongest apparent case against
systematic mappings from meaning to form. The paper's proposal is that they lexicalize two
conceptualizations of emotion, a habitual attitude of an experiencer directed at a target and an
episode in which a stimulus causes an experiencer to be in an emotional state, and nine
experiments show the distinction to be systematic (fear-type states are rated longer-lasting and
the subject of a frighten-type verb is judged causally responsible, in Mandarin and Korean as in
English), productive (adults in English, Japanese and Russian give novel verbs with attitude
meanings experiencer-subject syntax and those with episode meanings experiencer-object syntax)
and early (four- and five-year-olds do the same). The linking itself follows from one principle
over the semantic structures of Fig. 11, prominence preservation: `Sem.subject` is the
least embedded argument of such a structure, and since the causer of CAUSE and the holder of BE
are highest whatever they embed (`subject_cause`), the experiencer heads the attitude and the
stimulus the episode (`attitude_subject`, `episode_subject`), while the causation judgments
answer to whether the structure contains CAUSE at all. The linking agrees with Belletti and
Rizzi's Class I and Class II as recorded in `Pesetsky1995` and with Levin's admire and amuse
classes (`agrees_with_levin`).

## Implementation notes

The structures follow the prose of §5.4.1 rather than the figures: BE takes the entity in
a state and the state, the state of an attitude is the root directed at a target, and CAUSE takes
the causer and the caused BE, with no BECOME. Duration is not encoded in the structures, and the
experiments' rates stay in prose: fear-type verbs were rated longer-lasting than frighten-type
verbs, with 42 percent of the former above every one of the latter; causal responsibility fell on
the subject for 214 of 216 frighten-type verbs and on no consistent participant for fear-type
verbs; and frighten-type syntax was chosen for novel episode verbs over novel attitude verbs by
adults (68 against 38 percent in English) and by children (66 against 33 percent at ages four to
five). The paper's examples are the rows of `Data/Examples/HartshorneEtAl2016.json`.

## TODO

* §5.4.3: the Fig. 11 structures admit a target in the episode (`episodeWithTarget`),
  predicting the unattested (7); the mental-possession alternative that would exclude it.

## References

* [hartshorne-etal-2016]
* [belletti-rizzi-1988]
* [levin-1993]
* [levin-rappaport-hovav-2005]
-/

@[expose] public section

namespace HartshorneEtAl2016

open ArgumentStructure

/-- The argument positions of Fig. 11, the experiencer, the target an attitude is directed at,
and the stimulus that causes an episode. -/
inductive Participant where
  | experiencer
  | target
  | stimulus
  deriving DecidableEq, Repr

/-- A semantic structure of primitive predicates embedding one another, with variables marking
argument positions and the verbal root modifying a state (§5.4.1, Figs. 10–11). -/
inductive Sem (α : Type) where
  /-- An argument position. -/
  | var (x : α)
  /-- The verbal root: the kind of emotion. -/
  | root
  /-- BE(x, s): `x` is in the state `s`. -/
  | be (x s : Sem α)
  /-- CAUSE(x, e): `x` brings about `e`. -/
  | cause (x e : Sem α)
  /-- The state `s` directed at `y`. -/
  | about (s y : Sem α)
  deriving DecidableEq, Repr

variable {α : Type}

namespace Sem

/-- The argument positions of a structure with their depth of embedding, left to right. -/
def vars : Sem α → List (α × ℕ)
  | var x => [(x, 0)]
  | root => []
  | be x s => (x.vars ++ s.vars).map λ p => (p.1, p.2 + 1)
  | cause x e => (x.vars ++ e.vars).map λ p => (p.1, p.2 + 1)
  | about s y => (s.vars ++ y.vars).map λ p => (p.1, p.2 + 1)

/-- Under prominence preservation the least embedded argument position becomes the subject. -/
def subject (s : Sem α) : Option α := (s.vars.argmin Prod.snd).map Prod.fst

/-- Whether the structure contains CAUSE. -/
def HasCause : Sem α → Prop
  | var _ => False
  | root => False
  | be x s => x.HasCause ∨ s.HasCause
  | cause _ _ => True
  | about s y => s.HasCause ∨ y.HasCause

instance : DecidablePred (HasCause (α := α))
  | var _ => inferInstanceAs (Decidable False)
  | root => inferInstanceAs (Decidable False)
  | be x s => @instDecidableOr _ _ (instDecidablePredHasCause x) (instDecidablePredHasCause s)
  | cause _ _ => inferInstanceAs (Decidable True)
  | about s y => @instDecidableOr _ _ (instDecidablePredHasCause s) (instDecidablePredHasCause y)

theorem one_le_snd_of_mem_vars_map {l : List (α × ℕ)} {q : α × ℕ}
    (hq : q ∈ l.map λ p : α × ℕ => (p.1, p.2 + 1)) : 1 ≤ q.2 := by
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hq
  exact Nat.le_add_left 1 p.2

private theorem argmin_cons_of_le {p : α × ℕ} {l : List (α × ℕ)}
    (h : ∀ q ∈ l, p.2 ≤ q.2) : (p :: l).argmin Prod.snd = some p := by
  rw [List.argmin_cons]
  rcases hl : l.argmin Prod.snd with _ | q
  · rfl
  · simp [not_lt.mpr (h q (List.argmin_mem hl))]

theorem subject_cause (x : α) (e : Sem α) : (cause (var x) e).subject = some x := by
  simp only [subject, vars, List.singleton_append, List.map_cons]
  rw [argmin_cons_of_le λ _ hq => one_le_snd_of_mem_vars_map hq]
  rfl

theorem subject_be (x : α) (s : Sem α) : (be (var x) s).subject = some x := by
  simp only [subject, vars, List.singleton_append, List.map_cons]
  rw [argmin_cons_of_le λ _ hq => one_le_snd_of_mem_vars_map hq]
  rfl

end Sem

open Sem Participant

/-- The habitual attitude of Fig. 11a, in which the experiencer is in the emotional state the root
names, directed at the target. -/
def attitude : Sem Participant := be (var experiencer) (about root (var target))

/-- The caused emotional episode of Fig. 11b, in which the stimulus causes the experiencer to be in
the emotional state. -/
def episode : Sem Participant := cause (var stimulus) (be (var experiencer) root)

theorem attitude_subject : attitude.subject = some experiencer := subject_be _ _

theorem episode_subject : episode.subject = some stimulus := subject_cause _ _

theorem episode_hasCause_attitude_not : episode.HasCause ∧ ¬ attitude.HasCause := by decide

/-- The structures admit a target in the episode, still headed by the stimulus, which predicts the
unattested (7) (§5.4.3). -/
def episodeWithTarget : Sem Participant :=
  cause (var stimulus) (be (var experiencer) (about root (var target)))

theorem episodeWithTarget_subject : episodeWithTarget.subject = some stimulus := subject_cause _ _

/-! ### Agreement with the classifications the paper builds on -/

/-- The subject role of [belletti-rizzi-1988]'s classes, as `Pesetsky1995` records it. -/
def Participant.toSubjectRole : Participant → Option Pesetsky1995.SubjectRole
  | experiencer => some .experiencer
  | stimulus => some .stimulus
  | target => none

theorem agrees_with_belletti_rizzi :
    attitude.subject.bind Participant.toSubjectRole =
        Pesetsky1995.PsychVerbClass.expectedSubjectRole .classI ∧
      episode.subject.bind Participant.toSubjectRole =
        Pesetsky1995.PsychVerbClass.expectedSubjectRole .classII := by
  decide

/-- The argument positions as the shared role labels. -/
def Participant.thetaRole : Participant → ThetaRole
  | experiencer => .experiencer
  | stimulus => .stimulus
  | target => .goal

/-- The subject role of Levin's transitive psych-verb classes, which she sorts by "whether the
experiencer is the subject (the admire verbs) or the object (the amuse verbs)", the other argument
being the stimulus ([levin-1993] p. 189); an amuse verb's subject is "the cause of the change in
psychological state" (p. 191). -/
def levinSubjectRole : LevinClass → Option ThetaRole
  | .admire => some .experiencer
  | .amuse => some .stimulus
  | _ => none

theorem agrees_with_levin :
    attitude.subject.map Participant.thetaRole = levinSubjectRole .admire ∧
      episode.subject.map Participant.thetaRole = levinSubjectRole .amuse := by
  decide

end HartshorneEtAl2016
