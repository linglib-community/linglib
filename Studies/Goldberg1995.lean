module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fin.VecNotation
public import Linglib.Syntax.ConstructionGrammar.Constructicon
public import Linglib.Semantics.ArgumentStructure.Linking
public import Linglib.Syntax.Category.Verb.Argument
public import Linglib.Fragments.English.Verbs.Inventory

/-!
# Goldberg (1995): Constructions

This file formalizes Goldberg's account of argument structure, in which argument structure
constructions carry meaning of their own and a verb's participant roles fuse with a
construction's argument roles. A construction's meaning is a predicate, CAUSE-RECEIVE for the
ditransitive, CAUSE-MOVE for caused motion, CAUSE-BECOME for the resultative, MOVE for intransitive
motion and DIRECT-ACTION-AT for the conative, over an argument structure, a frame whose slots admit
thematic roles. The verbs are the English fragment's entries, so a verb's participant roles are the
slots of its lexical argument structure. The fusions the book draws follow from its Semantic
Coherence and Correspondence Principles, and the constructions form a network of normal-mode
inheritance links.

## Main results

* `isFusion_kick_iff`: *kick* fuses with the ditransitive in only one way (Fig. 2.9)
* `put_uses_exception`: *put* fuses with caused motion only through the three-role exception
  (Fig. 2.7)
* `isFusion_mail`: the ditransitive profiles *mail*'s mailee (Fig. 2.8)
* `wipe_talk_contributed`: the resultative adds a result-goal to *wipe* and a patient as well to
  *talk* (Fig. 8.2)
* `not_isFusion_become`: *become* cannot fuse with the resultative (p. 190)
* `exists_fused`: every construction shares a participant with its verb (p. 65)
* `network_wellTyped`, `inherited_statedForm`, `ditransitive_meaning_ne`: the network's links
  respect their types, and the ditransitive's senses share its form but not its meaning

## Implementation notes

Argument roles are `ThetaRole` labels: the cause of caused motion admits the labels whose Dowty
profile entails causation, and the resultative's result-goal is a goal, change of state being
change of location (pp. 81–84). A verb's participant roles are its fragment entry's argument
structure, extended by the roles the book construes them as; its lexical profiling is the book's
boldface. Caused motion's theme is contributable, as in Fig. 7.1 and the sneeze case, where
Fig. 2.6 draws it as required.

## TODO

The conative admits a verb of its intended result only if the verb is [+motion, +contact]
(Figs. 2.13–2.15, p. 63), features the book takes from Guerssel, Hale, Laughren, Levin and White
Eagle (1985). Until those features are formalized the conative lists only the subtype relation,
and no construction restricts a relation by features (`Feature` is empty). Adding the
intended-result relation will not by itself admit *kick at*: the conative's theme is oblique and
so not profiled, and the Correspondence Principle forbids a verb profiling two roles, as *kick*
does in Fig. 2.9, from fusing one with a nonprofiled role; the book does not say how a verb of the
intended result fuses. The intransitive resultative (Fig. 8.3), the passive's thematic hierarchy
(p. 57), *send* (Fig. 2.11) and the senses of caused motion (p. 76) are not modelled.

## References

* [goldberg-1995]
-/

@[expose] public section

namespace Goldberg1995

open ConstructionGrammar ArgumentStructure ArgumentFrame.Slot

/-! ### Meanings -/

/-- A `TransferModality` is the modality of CAUSE-RECEIVE that distinguishes a sense of the
ditransitive (pp. 75–77). -/
inductive TransferModality where
  /-- Actual transfer, the central sense, X CAUSES Y TO RECEIVE Z. -/
  | actual
  /-- Conditions of satisfaction imply X CAUSES Y TO RECEIVE Z. -/
  | satisfaction
  /-- X ENABLES Y TO RECEIVE Z. -/
  | enablement
  /-- X CAUSES Y NOT TO RECEIVE Z. -/
  | negated
  /-- X INTENDS TO CAUSE Y TO RECEIVE Z. -/
  | intended
  /-- X ACTS TO CAUSE Y TO RECEIVE Z at some future point in time. -/
  | future
  deriving DecidableEq, Fintype, Repr

/-- `Predicate` enumerates the constructions' predicates; the ditransitive's carries the modality
of its sense. -/
inductive Predicate where
  | causeReceive (m : TransferModality)
  | causeMove
  | causeBecome
  | move
  | directActionAt
  deriving DecidableEq, Repr

/-- `Feature` is the type of verb features that can restrict a relation, empty until the
features the conative uses are formalized. -/
abbrev Feature := Empty

/-- The meaning of an argument structure construction is a predicate over an argument structure,
with the relations a verb's event may bear to the construction's, each restricted to the verbs
with some features (§2.4.2, p. 64). -/
structure Sem where
  /-- The construction's predicate. -/
  pred : Predicate
  /-- The argument structure, linked to the construction's frame. -/
  link : LinkedFrame
  /-- The admissible relations, each with the features it requires of a verb. -/
  relations : List (SubeventRelation × Finset Feature)
  deriving DecidableEq

/-- A construction admits a verb with features `k` under the relation `R`. -/
def Sem.Admits (M : Sem) (k : Finset Feature) (R : SubeventRelation) : Prop :=
  ∃ x ∈ M.relations, x.1 = R ∧ x.2 ⊆ k

instance (M : Sem) (k : Finset Feature) (R : SubeventRelation) : Decidable (M.Admits k R) :=
  inferInstanceAs (Decidable (∃ x ∈ M.relations, _))

/-- `causers` is the set of labels whose Dowty profile entails causation, the roles a cause
admits: "a putter is a type of cause" (p. 52). -/
def causers : Finset ThetaRole := Finset.univ.filter fun r ↦ .causation ∈ r.canonicalProfile

example : causers = {.agent, .instrument, .stimulus} := by decide

/-- A fusion satisfies the Correspondence Principle when each profiled participant role fuses
with a profiled argument role, except that a verb profiling three roles may fuse one with a
nonprofiled argument role (p. 50). -/
def Corresponds (V C : LinkedFrame) (σ : ArgumentFrame.Slot → Option ArgumentFrame.Slot) :
    Prop :=
  (V.obligatory.filter fun s ↦ ∃ t ∈ σ s, ¬ C.IsProfiled t).length ≤
    if V.obligatory.length = 3 then 1 else 0

instance (V C : LinkedFrame) (σ) : Decidable (Corresponds V C σ) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ### The argument structure constructions -/

/-- The ditransitive [Subj V Obj Obj₂] in the sense `m` means CAUSE-RECEIVE ⟨agt rec pat⟩, with
the recipient contributable and the verb an instance or the means (Fig. 2.4; *Pat faxed Bill the
letter*). In the benefactive sense the verb designates a precondition (Fig. 3.2), and the other
senses keep the central sense's relations. -/
def ditransitive (m : TransferModality) : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .NOUN } ]
  , meaning :=
      { pred := .causeReceive m
        link :=
          { frame := .np_np
            roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.recipient}, false⟩),
              (complement 1, ⟨{.patient}, true⟩)] }
        relations :=
          if m = .intended then [(.precondition, ∅)] else [(.subtype, ∅), (.means, ∅)] } }

/-- The caused-motion construction [Subj V Obj Obl] means CAUSE-MOVE ⟨cause goal theme⟩, with goal
and theme contributable (Fig. 7.1), so that *sneeze* acquires motion and causation from it (*Pat
sneezed the napkin off the table*). -/
def causedMotion : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .ADP } ]
  , meaning :=
      { pred := .causeMove
        link :=
          { frame := .np_spatialPP
            roles := [(external, ⟨causers, true⟩), (complement 0, ⟨{.theme}, false⟩),
              (complement 1, ⟨{.goal}, false⟩)] }
        relations := [(.subtype, ∅), (.means, ∅)] } }

/-- The resultative [Subj V Obj Xcomp] means CAUSE-BECOME ⟨agt pat result-goal⟩, with patient and
result-goal contributable (Fig. 8.1; *She hammered the metal flat*). -/
def resultative : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .ADJ } ]
  , meaning :=
      { pred := .causeBecome
        link :=
          { frame := ⟨some .nominal, [.nominal, .clausal]⟩
            roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.patient}, false⟩),
              (complement 1, ⟨{.goal}, false⟩)] }
        relations := [(.subtype, ∅), (.means, ∅)] } }

/-- The intransitive motion construction [Subj V Obl] means MOVE ⟨theme goal⟩, with the goal
contributable (Fig. 7.2; *The fly buzzed into the room*). -/
def intransitiveMotion : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]
  , meaning :=
      { pred := .move
        link :=
          { frame := .spatialPP
            roles := [(external, ⟨{.theme}, true⟩), (complement 0, ⟨{.goal}, false⟩)] }
        relations := [(.subtype, ∅), (.means, ∅)] } }

/-- The conative [Subj V Obl_at] means DIRECT-ACTION-AT ⟨agt theme⟩ (Figs. 2.13–2.15; *Sam kicked
at Bill*); its at-phrase marks the target without entailing contact. -/
def conative : Construction Sem :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]
  , meaning :=
      { pred := .directActionAt
        link :=
          { frame := .pp (some English.Adpositions.at_)
            roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.theme}, true⟩)] }
        relations := [(.subtype, ∅)] } }

/-- The goal of caused motion is not profiled: "we can tell because it is linked to an oblique
function" (p. 53). -/
theorem not_isProfiled_goal : ¬ causedMotion.meaning.link.IsProfiled (complement 1) := by decide

/-! ### Verbs in constructions (§2.4)

Each verb is a fragment entry. Where the entry records the entailments of its arguments the
book's roles are derived from them; otherwise the book's construal extends the entry's argument
structure. -/

/-- The argument structure of *kick*, ⟨kicker kicked⟩ (Fig. 2.9). -/
def kickLF : LinkedFrame :=
  { frame := .np, roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.patient}, true⟩)] }

/-- The fragment's *kick* derives the book's construal, with kicker fused to agent and kicked to
patient (p. 54). -/
theorem kick_linkedFrame : English.Verbs.kick.linkedFrame? = some kickLF := by decide

/-- `kickFusion f` fuses *kick*'s two slots with the ditransitive's three by `f`. -/
def kickFusion (f : Fin 2 → Option (Fin 3)) : ArgumentFrame.Slot → Option ArgumentFrame.Slot :=
  ofFin [external, complement 0] [external, complement 0, complement 1] f

/-- *kick* fuses with the ditransitive in only one way: "The participant roles cannot fuse with
the argument roles in any other way" (p. 54). -/
theorem isFusion_kick_iff (f : Fin 2 → Option (Fin 3)) :
    IsFusionOn kickLF (ditransitive .actual).meaning.link (kickFusion f) ↔
      f = ![some 0, some 2] := by
  revert f; decide

/-- The ditransitive contributes the recipient to *kick*: "Crucially, the recipient role is
contributed by the construction" (p. 54). -/
theorem contributed_kick :
    contributed kickLF (ditransitive .actual).meaning.link (kickFusion ![some 0, some 2]) =
      [complement 0] := by
  decide

/-- The identity correspondence on three slots. -/
def id₃ : ArgumentFrame.Slot → Option ArgumentFrame.Slot :=
  ofFin [external, complement 0, complement 1] [external, complement 0, complement 1]
    ![some 0, some 1, some 2]

/-- *hand* profiles all three of its participant roles, each an instance of one argument role
of the ditransitive (Fig. 2.5). -/
def handLF : LinkedFrame :=
  { frame := .np_np
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.recipient}, true⟩),
      (complement 1, ⟨{.patient}, true⟩)] }

/-- *hand* fuses one-to-one with the ditransitive, which contributes nothing (Fig. 2.5). -/
theorem isFusion_hand :
    (English.Verbs.hand.linkedFrame?).all (·.Extends handLF) ∧
      IsFusionOn handLF (ditransitive .actual).meaning.link id₃ ∧
      Corresponds handLF (ditransitive .actual).meaning.link id₃ ∧
      contributed handLF (ditransitive .actual).meaning.link id₃ = [] := by
  decide

/-- *put* profiles all three roles: the putter is "a type of cause", the put.place role "is a
type of goal", and the put-thing is compatible with the theme (pp. 52–53). -/
def putLF : LinkedFrame :=
  { frame := .np_pp
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.theme}, true⟩),
      (complement 1, ⟨{.goal}, true⟩)] }

/-- `putFusion f` fuses *put*'s three slots with caused motion's by `f`. -/
def putFusion (f : Fin 3 → Option (Fin 3)) : ArgumentFrame.Slot → Option ArgumentFrame.Slot :=
  ofFin [external, complement 0, complement 1] [external, complement 0, complement 1] f

theorem isFusion_put :
    (English.Verbs.put.linkedFrame?).all (·.Extends putLF) ∧
      IsFusionOn putLF causedMotion.meaning.link (putFusion ![some 0, some 1, some 2]) ∧
      Corresponds putLF causedMotion.meaning.link (putFusion ![some 0, some 1, some 2]) := by
  decide

/-- *Put* fuses with caused motion only by linking a role to a nonprofiled argument role, the
three-role exception (p. 53). -/
theorem put_uses_exception (f : Fin 3 → Option (Fin 3))
    (h : IsFusionOn putLF causedMotion.meaning.link (putFusion f)) :
    ∃ s ∈ putLF.obligatory, ∃ t ∈ putFusion f s, ¬ causedMotion.meaning.link.IsProfiled t := by
  revert f; decide +kernel

/-- *mail* profiles only its mailer and mailed (*Paul mailed a letter*, p. 53); the mailee is its
*to*-phrase. -/
def mailLF : LinkedFrame :=
  { frame := .np_pp (some English.Adpositions.to_)
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.patient}, true⟩),
      (complement 1, ⟨{.recipient}, false⟩)] }

/-- `mailFusion` fuses the mailer with the agent, the mailee with the recipient and the mailed
with the patient (Fig. 2.8). -/
def mailFusion : ArgumentFrame.Slot → Option ArgumentFrame.Slot :=
  ofFin [external, complement 0, complement 1] [external, complement 0, complement 1]
    ![some 0, some 2, some 1]

/-- The ditransitive "imposes a profiled status" on the mailee: not lexically profiled, it fuses
with a profiled argument role (p. 53). -/
theorem isFusion_mail :
    mailLF.frame ∈ English.Verbs.mail.valency.frames ∧
      IsFusionOn mailLF (ditransitive .actual).meaning.link mailFusion ∧
      Corresponds mailLF (ditransitive .actual).meaning.link mailFusion ∧
      complement 1 ∉ mailLF.obligatory ∧
      ∃ t ∈ mailFusion (complement 1), (ditransitive .actual).meaning.link.IsProfiled t := by
  decide

/-- *sneeze* "has a single profiled participant role, a sneezer" (p. 54), which the book fuses
with the cause (Fig. 2.10). -/
def sneezeLF : LinkedFrame :=
  { frame := .intransitive, roles := [(external, ⟨causers, true⟩)] }

/-- *sneeze* fuses its sneezer with the cause, and caused motion contributes the goal and the
theme (Fig. 2.10). -/
theorem isFusion_sneeze :
    (English.Verbs.sneeze.linkedFrame?).all (·.Extends sneezeLF) ∧
      IsFusionOn sneezeLF causedMotion.meaning.link
        (ofFin [external] [external, complement 0, complement 1] ![some 0]) ∧
      contributed sneezeLF causedMotion.meaning.link
        (ofFin [external] [external, complement 0, complement 1] ![some 0]) =
          [complement 0, complement 1] := by
  decide

/-- *wipe* profiles its participant roles ⟨wiper wiped⟩ (p. 189). Its lexical entry leaves the
wiper's agentivity to pragmatics, a subject that only moves, and the book construes it as an
agent. -/
def wipeLF : LinkedFrame :=
  { frame := .np
    roles := [(external, ⟨{.agent, .theme}, true⟩), (complement 0, ⟨{.patient}, true⟩)] }

/-- *talk* profiles its single participant role ⟨talker⟩ (p. 189). -/
def talkLF : LinkedFrame :=
  { frame := .intransitive, roles := [(external, ⟨{.agent}, true⟩)] }

/-- The resultative adds only a result-goal to *wipe*, and both a patient and a result-goal to
*talk* (p. 190). -/
theorem wipe_talk_contributed :
    (English.Verbs.wipe.linkedFrame?).all (·.Extends wipeLF) ∧
      IsFusionOn wipeLF resultative.meaning.link
        (ofFin [external, complement 0] [external, complement 0, complement 1] ![some 0, some 1]) ∧
      contributed wipeLF resultative.meaning.link
        (ofFin [external, complement 0] [external, complement 0, complement 1] ![some 0, some 1]) =
          [complement 1] ∧
      (English.Verbs.talk.linkedFrame?).all (·.Extends talkLF) ∧
      IsFusionOn talkLF resultative.meaning.link
        (ofFin [external] [external, complement 0, complement 1] ![some 0]) ∧
      contributed talkLF resultative.meaning.link
        (ofFin [external] [external, complement 0, complement 1] ![some 0]) =
          [complement 0, complement 1] := by
  decide

/-- *become* profiles its participant roles ⟨patient result-goal⟩ (p. 190), a subject and a
predicative complement. -/
def becomeLF : LinkedFrame :=
  { frame := ⟨some .nominal, [.clausal]⟩
    roles := [(external, ⟨{.patient}, true⟩), (complement 0, ⟨{.goal}, true⟩)] }

/-- *Become* does not fuse with the resultative, which needs the agent fused with an existing
participant role of the verb (p. 190). -/
theorem not_isFusion_become (f : Fin 2 → Option (Fin 3)) :
    ¬ IsFusionOn becomeLF resultative.meaning.link
      (ofFin [external, complement 0] [external, complement 0, complement 1] f) := by
  revert f; decide

/-- *aim* ⟨aimer target⟩ profiles only its aimer, the target not being in boldface in Fig. 2.14;
it is an instance of DIRECT-ACTION-AT (p. 64). -/
def aimLF : LinkedFrame :=
  { frame := .pp (some English.Adpositions.at_)
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.theme}, false⟩)] }

/-- *aim* fuses with the conative as an instance of it (Fig. 2.14). -/
theorem isFusion_aim :
    (English.Verbs.aim.linkedFrame?).all (·.Extends aimLF) ∧
      IsFusionOn aimLF conative.meaning.link
        (ofFin [external, complement 0] [external, complement 0] ![some 0, some 1]) ∧
      Corresponds aimLF conative.meaning.link
        (ofFin [external, complement 0] [external, complement 0] ![some 0, some 1]) ∧
      conative.meaning.Admits ∅ .subtype := by
  decide

/-! ### The network (§3.3) -/

/-- `Node` enumerates the constructions of the book's network, the ditransitive in each of its
senses and the other argument structure constructions. -/
inductive Node where
  | ditransitive (m : TransferModality)
  | causedMotion
  | intransitiveMotion
  | resultative
  | conative
  deriving DecidableEq, Fintype

/-- `construction n` is the construction at the node `n`; the senses of the ditransitive share its
form. -/
def construction : Node → Construction Sem
  | .ditransitive m => ditransitive m
  | .causedMotion => causedMotion
  | .intransitiveMotion => intransitiveMotion
  | .resultative => resultative
  | .conative => conative

theorem obligatory_ne_nil (n : Node) : (construction n).meaning.link.obligatory ≠ [] := by
  revert n; decide

/-- The Shared Participant Condition holds of every construction of the network: it shares a
participant with any verb fused with it (p. 65). -/
theorem exists_fused (n : Node) {V : LinkedFrame}
    {σ : ArgumentFrame.Slot → Option ArgumentFrame.Slot}
    (h : IsFusion V (construction n).meaning.link σ) : ∃ s t, σ s = some t :=
  h.exists_fused (obligatory_ne_nil n)

/-- The senses of the ditransitive differ in meaning from its central sense (pp. 75–77). -/
theorem ditransitive_meaning_ne {m : TransferModality} (hm : m ≠ .actual) :
    (ditransitive m).meaning ≠ (ditransitive .actual).meaning := by
  revert m; decide

/-- `network` is the network of chapters 2 and 3, "the entire collection of constructions as
forming a lattice, with individual constructions related by specific types of asymmetric normal
mode inheritance links" (§3.7, p. 99). Each extension of the ditransitive inherits from the
central sense by a polysemy link (pp. 75–77), intransitive motion from caused motion by a subpart
link (p. 78), and the resultative from caused motion by a metaphorical link, change of state as
change of location (pp. 81–84). The conative is in the book's inventory (p. 4) but in no link. -/
def network : Constructicon Node Sem where
  cxn := construction
  mothers
    | .ditransitive .actual => []
    | .ditransitive _ => [(.ditransitive .actual, some .polysemy)]
    | .intransitiveMotion => [(.causedMotion, some .subpart)]
    | .resultative => [(.causedMotion, some .metaphorical)]
    | _ => []

/-- `Node.rank n` is the depth of `n` below the constructions it inherits from. -/
def Node.rank : Node → ℕ
  | .ditransitive .actual | .causedMotion | .conative => 0
  | _ => 1

instance : PartialOrder Node := network.partialOrder Node.rank (by decide)

instance : DecidableLE Node :=
  network.decidableLE [.ditransitive .actual, .causedMotion] (by decide)

/-- Every link respects its type: the extensions of the ditransitive have its form, and
intransitive motion is a proper subpart of caused motion. -/
theorem network_wellTyped : network.WellTyped := by decide

theorem isMother_resultative_iff (n : Node) :
    network.IsMother .resultative n ↔ n = .causedMotion := by
  revert n; decide

/-- `statedForm n` is the form the construction at `n` states itself, none for the extensions of
the ditransitive: "the syntactic specifications of the central sense are inherited by the
extensions; therefore we do not need to state the syntactic realization for each extension"
(p. 75). -/
def statedForm : Node → Option (TypedForm String)
  | .ditransitive .actual => some (ditransitive .actual).form
  | .ditransitive _ => none
  | n => some (construction n).form

/-- Each sense of the ditransitive inherits the central sense's form. -/
theorem inherited_statedForm (m : TransferModality) :
    DefaultInheritance.inherited statedForm (.ditransitive m) = {(ditransitive .actual).form} := by
  cases m <;> exact DefaultInheritance.inherited_eq_singleton_of_isLeast
    (m := .ditransitive .actual) (by decide) rfl

end Goldberg1995
