module

public import Mathlib.Tactic.DeriveFintype
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
thematic roles. A fusion is the set of lines the book draws between participant roles and argument
roles, and the fusions it draws are the only ones its Semantic Coherence and Correspondence
Principles allow. The constructions form a network of normal-mode inheritance links.

## Main results

* `fusions_kick`: *kick* fuses with the ditransitive in only one way (Fig. 2.9)
* `put_uses_exception`: *put* fuses with caused motion through the three-role exception (Fig. 2.7)
* `fusions_mail`: the ditransitive profiles *mail*'s mailee (Fig. 2.8) or contributes a recipient
* `contributed_wipe`, `contributed_talk`: the resultative adds a result-goal to *wipe* and a
  patient as well to *talk* (Fig. 8.2)
* `fusions_become`: *become* has no fusion with the resultative (p. 190)
* `nonempty_of_isFusion`: every construction shares a participant with its verb (p. 65)
* `network_wellTyped`, `inherited_statedForm`, `ditransitive_meaning_ne`: the network's links
  respect their types, and the ditransitive's senses share its form but not its meaning

## Implementation notes

Argument roles are `ThetaRole` labels: the cause of caused motion admits the labels whose Dowty
profile entails causation, and the resultative's result-goal is a goal, change of state being
change of location (pp. 81–84). A verb's participant roles are the slots of a frame its fragment
entry lists, linked to the labels the book construes them as; only *kick*'s entry records the
entailments its labels derive from. Lexical profiling is the book's boldface. Caused motion's
theme is contributable, as in Fig. 7.1 and the sneeze case, where Fig. 2.6 draws it as required.
A construction's form is its frame in English order (`linearize`), which the book states at the
subject-predicate construction (p. 110), so the conative's *at* and the resultative's AP or PP
result phrase (Fig. 8.1) come from the frame.

## TODO

The conative admits a verb of its intended result only if the verb is [+motion, +contact]
(Figs. 2.13–2.15, p. 63), features the book takes from Guerssel, Hale, Laughren, Levin and White
Eagle (1985); until they are formalized the conative lists only the subtype relation. The relation
alone would not admit *kick at*: *kick*'s kicked role is a patient, not the conative's theme
(`fusions_kick_conative`), and were the two compatible, the Correspondence Principle would forbid
a verb profiling two roles from fusing one with the theme, which is oblique and so not profiled;
the book does not say how a verb of the intended result fuses. The intransitive resultative
(Fig. 8.3), the passive's thematic hierarchy (p. 57), *send* (Fig. 2.11) and the senses of caused
motion (p. 76) are not modelled, nor are the transfer caused-motion construction of Fig. 4.1 and
the subject-predicate, transitive and intransitive constructions of Fig. 4.2, whose instance links
add complements, where `LinkType.instance` admits only a lexically filled version of a form.

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

/-- The meaning of an argument structure construction is a predicate over an argument structure,
with the relations a verb's event may bear to the construction's (§2.4.2, p. 64). -/
structure Sem where
  /-- The construction's predicate. -/
  pred : Predicate
  /-- The argument structure, linked to the construction's frame. -/
  link : LinkedFrame
  /-- The admissible relations. -/
  relations : List SubeventRelation
  deriving DecidableEq

/-- `causers` is the set of labels whose Dowty profile entails causation, the roles a cause
admits: "a putter is a type of cause" (p. 52). -/
def causers : Finset ThetaRole := Finset.univ.filter fun r ↦ .causation ∈ r.canonicalProfile

example : causers = {.agent, .instrument, .stimulus} := by decide

/-! ### The argument structure constructions -/

/-- The slot an expressed argument position fills in a form: a noun for a nominal, a phrase headed
by the adposition a PP selects, and any phrase for a predicative complement. -/
def slot? : ArgumentFrame.Position → Option (ConstructionGrammar.Slot String)
  | .nominal => some { filler := .open_ .NOUN }
  | .adpositional _ (some p) => some { filler := .headed p.form .ADP }
  | .adpositional _ none => some { filler := .open_ .ADP }
  | .clausal .. => some { filler := .phrasal }
  | .expletive => some { filler := .open_ .PRON }
  | .implicit _ => none

/-- `linearize fr` is the form of the frame `fr` in English order, the subject, the head verb and
the expressed complements, an order the book states once, at the subject-predicate construction
the argument structure constructions inherit from (p. 110, Fig. 4.2). -/
def linearize (fr : ArgumentFrame) : TypedForm String :=
  (fr.external.bind slot?).toList ++ [{ filler := .open_ .VERB, isHead := true }] ++
    fr.complements.filterMap slot?

/-- The argument structure construction meaning `pred` over `link`, with the relations
`relations`, whose form is its frame linearized. -/
def argumentStructure (pred : Predicate) (link : LinkedFrame) (relations : List SubeventRelation) :
    Construction Sem :=
  { form := linearize link.frame, meaning := ⟨pred, link, relations⟩ }

/-- The ditransitive [Subj V Obj Obj₂] in the sense `m` means CAUSE-RECEIVE ⟨agt rec pat⟩, with
the recipient contributable and the verb an instance or the means (Fig. 2.4; *Pat faxed Bill the
letter*). In the benefactive sense the verb designates a precondition (Fig. 3.2), and the other
senses keep the central sense's relations. -/
def ditransitive (m : TransferModality) : Construction Sem :=
  argumentStructure (.causeReceive m)
    { frame := .np_np
      roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.recipient}, false⟩),
        (complement 1, ⟨{.patient}, true⟩)] }
    (if m = .intended then [.precondition] else [.subtype, .means])

/-- The caused-motion construction [Subj V Obj Obl] means CAUSE-MOVE ⟨cause goal theme⟩, with goal
and theme contributable (Fig. 7.1), so that *sneeze* acquires motion and causation from it (*Pat
sneezed the napkin off the table*). -/
def causedMotion : Construction Sem :=
  argumentStructure .causeMove
    { frame := .np_spatialPP
      roles := [(external, ⟨causers, true⟩), (complement 0, ⟨{.theme}, false⟩),
        (complement 1, ⟨{.goal}, false⟩)] }
    [.subtype, .means]

/-- The resultative [Subj V Obj Xcomp] means CAUSE-BECOME ⟨agt pat result-goal⟩, with patient and
result-goal contributable (Fig. 8.1; *Pat hammered the metal flat*, p. 81). Its result phrase, an
AP or a PP, is the predicate of a small clause whose subject is the object. -/
def resultative : Construction Sem :=
  argumentStructure .causeBecome
    { frame := ArgumentFrame.smallClause.withObject
      roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.patient}, false⟩),
        (complement 1, ⟨{.goal}, false⟩)] }
    [.subtype, .means]

/-- The intransitive motion construction [Subj V Obl] means MOVE ⟨theme goal⟩, with the goal
contributable (Fig. 7.2; *The fly buzzed into the room*). -/
def intransitiveMotion : Construction Sem :=
  argumentStructure .move
    { frame := .spatialPP
      roles := [(external, ⟨{.theme}, true⟩), (complement 0, ⟨{.goal}, false⟩)] }
    [.subtype, .means]

/-- The conative [Subj V Obl_at] means DIRECT-ACTION-AT ⟨agt theme⟩ (Figs. 2.13–2.15; *Sam kicked
at Bill*); its at-phrase marks the target without entailing contact. -/
def conative : Construction Sem :=
  argumentStructure .directActionAt
    { frame := .pp (some English.Adpositions.at_)
      roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.theme}, true⟩)] }
    [.subtype]

/-! ### Verbs in constructions (§2.4)

A verb's participant roles are the slots of a frame its fragment entry lists, linked to the roles
the book construes them as. A fusion is written as its lines, each joining a slot of the verb to a
slot of the construction. -/

/-- The argument structure of *kick*, ⟨kicker kicked⟩ (Fig. 2.9). -/
def kickLF : LinkedFrame :=
  { frame := .np, roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.patient}, true⟩)] }

/-- The fragment's *kick* derives the book's construal, with kicker fused to agent and kicked to
patient (p. 54). -/
theorem kick_linkedFrame : English.Verbs.kick.linkedFrame? = some kickLF := by decide

/-- *kick* fuses with the ditransitive in only one way, kicker with agent and kicked with patient:
"The participant roles cannot fuse with the argument roles in any other way" (p. 54). -/
theorem fusions_kick : fusions kickLF (ditransitive .actual).meaning.link =
    {{(external, external), (complement 0, complement 1)}} := by
  decide +kernel

/-- The ditransitive contributes the recipient to *kick*: "Crucially, the recipient role is
contributed by the construction" (p. 54). -/
theorem contributed_kick :
    contributed (ditransitive .actual).meaning.link
      {(external, external), (complement 0, complement 1)} = {complement 0} := by
  decide

/-- The lines that join each of three slots to itself. -/
def diag₃ : Finset (ArgumentFrame.Slot × ArgumentFrame.Slot) :=
  ({external, complement 0, complement 1} : Finset ArgumentFrame.Slot).diag

/-- *hand* profiles all three of its participant roles, each an instance of one argument role
of the ditransitive (Fig. 2.5). -/
def handLF : LinkedFrame :=
  { frame := .np_np
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.recipient}, true⟩),
      (complement 1, ⟨{.patient}, true⟩)] }

/-- *hand* fuses with the ditransitive in one way, each of its roles with the matching argument
role (Fig. 2.5). -/
theorem fusions_hand : fusions handLF (ditransitive .actual).meaning.link = {diag₃} := by
  decide +kernel

/-- The profiled participant roles of *hand* fuse with the profiled argument roles of the
ditransitive, which contributes nothing (p. 51). -/
theorem corresponds_hand : Corresponds handLF (ditransitive .actual).meaning.link diag₃ ∧
    contributed (ditransitive .actual).meaning.link diag₃ = ∅ := by
  decide

/-- *put* profiles all three roles: the putter is "a type of cause", the put.place role "is a
type of goal", and the put-thing is compatible with the theme (pp. 52–53). -/
def putLF : LinkedFrame :=
  { frame := .np_pp
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.theme}, true⟩),
      (complement 1, ⟨{.goal}, true⟩)] }

theorem fusions_put : fusions putLF causedMotion.meaning.link = {diag₃} := by decide +kernel

/-- *put* fuses with caused motion by the three-role exception, its profiled put.place role
fusing with the goal, which is not profiled: "we can tell because it is linked to an oblique
function" (p. 53). -/
theorem put_uses_exception :
    profilingMismatches putLF causedMotion.meaning.link diag₃ = {(complement 1, complement 1)} ∧
      Corresponds putLF causedMotion.meaning.link diag₃ := by
  decide

/-- *mail* profiles only its mailer and mailed (*Paul mailed a letter*, p. 53); the mailee is its
*to*-phrase. -/
def mailLF : LinkedFrame :=
  { frame := .np_pp (some English.Adpositions.to_)
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.patient}, true⟩),
      (complement 1, ⟨{.recipient}, false⟩)] }

/-- `mailFusion` fuses the mailer with the agent, the mailee with the recipient and the mailed
with the patient (Fig. 2.8). -/
def mailFusion : Finset (ArgumentFrame.Slot × ArgumentFrame.Slot) :=
  {(external, external), (complement 0, complement 1), (complement 1, complement 0)}

/-- The book's principles let the ditransitive fuse with *mail* as in Fig. 2.8 or, the mailee not
being profiled, contribute the recipient as it does to *kick*. -/
theorem fusions_mail :
    fusions mailLF (ditransitive .actual).meaning.link =
      {mailFusion, mailFusion.erase (complement 1, complement 0)} := by
  decide +kernel

/-- The ditransitive "imposes a profiled status" on the mailee, which fuses with the profiled
recipient (p. 53). -/
theorem mailee_profiled :
    complement 1 ∉ mailLF.obligatory ∧ (complement 1, complement 0) ∈ mailFusion ∧
      (ditransitive .actual).meaning.link.IsProfiled (complement 0) := by
  decide

/-- *sneeze* "has a single profiled participant role, a sneezer" (p. 54), which the book fuses
with the cause (Fig. 2.10). -/
def sneezeLF : LinkedFrame :=
  { frame := .intransitive, roles := [(external, ⟨causers, true⟩)] }

/-- *sneeze* fuses its sneezer with the cause, and caused motion contributes the goal and the
theme (Fig. 2.10). -/
theorem fusions_sneeze : fusions sneezeLF causedMotion.meaning.link = {{(external, external)}} ∧
    contributed causedMotion.meaning.link {(external, external)} =
      {complement 0, complement 1} := by
  decide +kernel

/-- *wipe* profiles its participant roles ⟨wiper wiped⟩ (p. 189). -/
def wipeLF : LinkedFrame :=
  { frame := .np
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.patient}, true⟩)] }

/-- *talk* profiles its single participant role ⟨talker⟩ (p. 189). -/
def talkLF : LinkedFrame :=
  { frame := .intransitive, roles := [(external, ⟨{.agent}, true⟩)] }

/-- The resultative adds only a result-goal to *wipe* (Fig. 8.2). -/
theorem contributed_wipe :
    fusions wipeLF resultative.meaning.link =
        {{(external, external), (complement 0, complement 0)}} ∧
      contributed resultative.meaning.link {(external, external), (complement 0, complement 0)} =
        {complement 1} := by
  decide +kernel

/-- The resultative adds both a patient and a result-goal to *talk* (Fig. 8.2). -/
theorem contributed_talk :
    fusions talkLF resultative.meaning.link = {{(external, external)}} ∧
      contributed resultative.meaning.link {(external, external)} =
        {complement 0, complement 1} := by
  decide +kernel

/-- *become* profiles its participant roles ⟨patient result-goal⟩ (p. 190), a subject and a
predicative complement. -/
def becomeLF : LinkedFrame :=
  { frame := .smallClause
    roles := [(external, ⟨{.patient}, true⟩), (complement 0, ⟨{.goal}, true⟩)] }

/-- *Become* does not fuse with the resultative, which needs the agent fused with an existing
participant role of the verb (p. 190). -/
theorem fusions_become : fusions becomeLF resultative.meaning.link = ∅ := by decide +kernel

/-- *aim* ⟨aimer target⟩ profiles only its aimer, the target not being in boldface in Fig. 2.14;
it is an instance of DIRECT-ACTION-AT (p. 64). -/
def aimLF : LinkedFrame :=
  { frame := .pp (some English.Adpositions.at_)
    roles := [(external, ⟨{.agent}, true⟩), (complement 0, ⟨{.theme}, false⟩)] }

/-- *aim* fuses with the conative as an instance of it (Fig. 2.14). -/
theorem fusions_aim :
    fusions aimLF conative.meaning.link = {{(external, external), (complement 0, complement 0)}} ∧
      Corresponds aimLF conative.meaning.link {(external, external), (complement 0, complement 0)} ∧
      .subtype ∈ conative.meaning.relations := by
  decide +kernel

/-- *kick*, construed as in Fig. 2.9, has no fusion with the conative of Fig. 2.13, whose example
is *Sam kicked at Bill* (p. 4): its kicked role is a patient, not a theme. -/
theorem fusions_kick_conative : fusions kickLF conative.meaning.link = ∅ := by decide +kernel

/-- Each verb's construal is over a frame its fragment entry lists. -/
theorem mem_frames :
    ∀ x ∈ [(English.Verbs.hand, handLF), (English.Verbs.put, putLF), (English.Verbs.mail, mailLF),
      (English.Verbs.sneeze, sneezeLF), (English.Verbs.wipe, wipeLF), (English.Verbs.talk, talkLF),
      (English.Verbs.aim, aimLF)], x.2.frame ∈ x.1.valency.frames := by
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
theorem nonempty_of_isFusion (n : Node) {V : LinkedFrame}
    {σ : Finset (ArgumentFrame.Slot × ArgumentFrame.Slot)}
    (h : IsFusion V (construction n).meaning.link σ) : σ.Nonempty :=
  h.nonempty (obligatory_ne_nil n)

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
