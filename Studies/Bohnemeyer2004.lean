module

public import Linglib.Data.Wordlist.Bohnemeyer2004
public import Linglib.Languages.Mayan.Yukatek.Agreement
public import Linglib.Languages.HindiUrdu.Case
public import Linglib.Semantics.ArgumentStructure.EventStructure.Denotation
public import Linglib.Core.Relation.ReflTransGen
public import Studies.Lucy1994
public import Linglib.Syntax.Voice.Basic

/-!
# Bohnemeyer 2004: split intransitivity, linking, and lexical representation

Bohnemeyer accounts for argument linking in Yukatek Maya from event structure. Transitivizing an
intransitive base puts its event into a causal chain of two subevents, as the causing subevent
when the base is internally caused in the sense of [levin-hovav-1995] and as the caused one
otherwise, and the participant of a causing subevent outranks that of the subevent it causes. So
[the base's participant outranks the added one exactly when the base is internally
caused](##Bohnemeyer2004.baseSubevent_lt_other_iff): an internally-caused base gains an applied
object, an externally-caused one an instigator. [Stem class, and with it the inherent aspect on
which Krämer and Wunderlich's rule rests](##Bohnemeyer2004.underdetermines_stemClass), and [the
transitivizing suffix](##Bohnemeyer2004.underdetermines_suffix) each leave the linking open. The
same hierarchy [derives the aspect-conditioned split](##Bohnemeyer2004.linking_derives_split): an
imperfective viewpoint aligns with the initial subevent and a perfective one with the final, and
the sole argument of an intransitive follows the role at that end. Detransitivization keeps one
subevent of a transitive's chain, and [a passive stem keeps the causing process
too](##Bohnemeyer2004.Detransitivization.passive_template_bind_caused).

## Implementation notes

* The paper's event structures have a state-change predicate that covers change without a
  discrete end state, a process predicate, and a process predicate for internally-caused
  processes. `Template` has `BECOME` and one activity; both process predicates are read as `act`,
  and causation type is recorded apart from the template.
* The transitivization rules are represented by the place of the base's event in the derived
  chain. The event an internally-caused base gains is generic, and `Template` has no term for it.
* The verbs, their stem classes and the causation type of each intransitive base are rows of
  `Data/Wordlist/Bohnemeyer2004.json`, with each transitivized stem of the examples related to
  its base; the suffix of a base is read from the morphs of that stem.

## TODO

* The example sentences of the paper are not yet rows of `Data/Examples`.

## References

* [bohnemeyer-2004]
* [kraemer-wunderlich-1999]
* [levin-hovav-1995]
* [lucy-1994]
-/

@[expose] public section

namespace Bohnemeyer2004

open ArgumentStructure.EventStructure Aspect Mayan Voice
open Yukatek

/-! ### Stem classes -/

/-- The stem class of the language file that a class of the paper's word list names. -/
def stemClass : Wordlist.StemClass → VerbStemClass
  | .active => .active
  | .inactive => .inactive
  | .inchoative => .inchoative
  | .positional => .positional
  | .transitive => .transitiveActive

/-! ### Causal chain and thematic hierarchy -/

/-- A subevent is one of the two in the causal chain a clause expresses, the causing subevent or
the subevent it causes. Yukatek clauses have at most two core arguments, so two subevents suffice
for the hierarchy (31). -/
inductive Subevent where
  | causing
  | caused
  deriving DecidableEq, Fintype, Repr

/-- `Causes a b` holds when `a` is the causing and `b` the caused subevent, the causal edge of
(31). -/
def Subevent.Causes (a b : Subevent) : Prop := a = .causing ∧ b = .caused

instance : DecidableRel Subevent.Causes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Subevents in order of causal precedence, the causing subevent first. The thematic hierarchy
(31) ranks the participant of a causing subevent above the participant of the subevent it causes,
so a participant of `a` outranks a participant of `b` exactly when `a < b`. -/
instance : LinearOrder Subevent :=
  linearOrderOfCovers Subevent.Causes (OrderDual.toDual ∘ Subevent.ctorIdx) (by decide) (by decide)

instance : BoundedOrder Subevent where
  bot := .causing
  bot_le := by decide
  top := .caused
  le_top := by decide

/-- The other subevent of the chain. -/
def Subevent.other : Subevent → Subevent
  | .causing => .caused
  | .caused => .causing

/-- `termRole e` is the core term role of the participant of `e` (33a–b). The highest-ranking
role is the A of a transitive clause and the lowest-ranking role its P. -/
def termRole : Subevent → TermRole
  | .causing => .A
  | .caused => .P

/-- `markerOf r` is the marker set the core term role `r` takes in Yukatek (33), set A for A and
set B for P. The sole argument of an intransitive takes whichever the viewpoint selects, which is
the split (`sMarkerFromViewpoint`). -/
def markerOf : TermRole → Option MarkerSet
  | .A => some .setA
  | .P => some .setB
  | .S | .X => none

theorem markerOf_termRole_of_lt {a b : Subevent} (h : a < b) :
    markerOf (termRole a) = some .setA ∧ markerOf (termRole b) = some .setB := by
  revert a b; decide

/-! ### Transitivization -/

/-- The subevent of the derived causal chain that the base's event is. By (26) an
internally-caused process gains an event it causes, and by (27) an externally-caused event gains
an internally-caused process causing it. -/
def Wordlist.Causation.baseSubevent : Wordlist.Causation → Subevent
  | .internal => .causing
  | .external => .caused

/-- The role of the base's participant in the derived transitive. -/
def baseRole (c : Wordlist.Causation) : TermRole := termRole c.baseSubevent

/-- The role of the participant transitivization adds. -/
def addedRole (c : Wordlist.Causation) : TermRole := termRole c.baseSubevent.other

/-- The base's participant outranks the participant transitivization adds exactly when the base is
internally caused ((26)–(27) with (31)). -/
theorem baseSubevent_lt_other_iff (c : Wordlist.Causation) :
    c.baseSubevent < c.baseSubevent.other ↔ c = .internal := by
  cases c <;> decide

-- (33a–b): the base's participant is marked by set A when the base is internally caused and by
-- set B otherwise, and the added participant by the other set
theorem markerOf_baseRole (c : Wordlist.Causation) :
    markerOf (baseRole c) = some (if c = .internal then .setA else .setB) ∧
      markerOf (addedRole c) = some (if c = .internal then .setB else .setA) := by
  cases c <;> decide

/-- Transitivizing an internally-caused base nucleativizes an applied object as P while the
base's S is maintained, surfacing as the A of the derived transitive clause, a P-applicative over
an intransitive base. -/
def applicativeLinking : Voice := .of .intransitive .np [some .external, some (.complement 0)]

/-- The voice of the transitivization of a base, the applicative for an internally-caused base
and the causative for an externally-caused one. -/
def Wordlist.Causation.voice : Wordlist.Causation → Voice
  | .internal => applicativeLinking
  | .external => causative

/-- The base's S receives the role of the derived slot its participant occupies. -/
def originalRole (va : Voice) : Option TermRole :=
  (va.image .external).bind fun t ↦ (va.derived.status t).role

-- the applicative and the causative voice assign the roles the hierarchy derives
theorem voice_roles (c : Wordlist.Causation) :
    originalRole c.voice = some (baseRole c) ∧ c.voice.newParticipant = some (addedRole c) := by
  cases c <;> decide

/-! ### What does not fix the linking

The paper's argument is that the properties rival accounts appeal to leave the linking open:
stem class, the inherent aspect [kraemer-wunderlich-1999] read from it, the overt suffix, and
control. -/

/-- A property of verbs underdetermines the linking when an internally-caused and an
externally-caused base share a value of it. -/
def Underdetermines {α : Type*} (f : Wordlist.Analysis → Option α) : Prop :=
  ∃ v ∈ Wordlist.analyses, ∃ w ∈ Wordlist.analyses, v.causation = some .internal ∧
    w.causation = some .external ∧ ∃ x, f v = some x ∧ f w = some x

/-- Stem class underdetermines the linking, and so does anything read from it: *hàan* 'eat' and
*kim* 'die' are both inactive, and transitivization adds an applied object to the one (9) and an
instigator to the other (6). -/
theorem underdetermines_stemClass {α : Type*} (g : VerbStemClass → α) :
    Underdetermines fun a ↦ some (g (stemClass a.stemClass)) :=
  ⟨Wordlist.haan.analysis, by decide, Wordlist.kim.analysis, by decide, rfl, rfl, _, rfl, rfl⟩

/-- The inherent aspect [kraemer-wunderlich-1999] assign a stem class, imperfective for the active
class and perfective for the inactive, inchoative and positional classes. -/
def inherentAspect : VerbStemClass → Option Perfectivity
  | .active => some .imperfective
  | .inactive | .inchoative | .positional => some .perfective
  | .transitiveActive => none

-- pp. 80, 83: the inherent aspect of the active and of the inactive class is the viewpoint of
-- the status that leaves the class unmarked; the inchoative and positional classes, which are
-- also inherently perfective, are marked in every status
theorem exists_unmarked_viewpointAspect_iff (k : VerbStemClass) :
    (∃ s, statusSuffix k s = some [] ∧ s.viewpointAspect = inherentAspect k) ↔
      k = .active ∨ k = .inactive := by
  cases k <;> decide

/-- The place of the base's participant by rule (14) of [kraemer-wunderlich-1999]. An inherently
imperfective verb gains an affected object, an inherently perfective one a causer. -/
def kwBaseSubevent : Perfectivity → Subevent
  | .imperfective => .causing
  | .perfective => .caused

-- (14) agrees with (26)–(27) on a base exactly when active stem class and internal causation
-- coincide; *balak'* 'roll' (10), *tsíirin* 'buzz' (11) and *péek* 'move' (8) are active and
-- externally caused, *hàan* 'eat' (9) is inactive and internally caused
theorem kwBaseSubevent_eq_iff {k : VerbStemClass} {a : Perfectivity}
    (h : inherentAspect k = some a) (c : Wordlist.Causation) :
    kwBaseSubevent a = c.baseSubevent ↔ (k = .active ↔ c = .internal) := by
  cases k <;> cases c <;> cases h <;> decide

/-- The degree achievements of (17)–(18) among the paper's classified verbs, which behave
atelically in the test of realization under cessation (15). -/
def degreeAchievements : List Wordlist.Analysis :=
  [Wordlist.kan.analysis, Wordlist.lab.analysis, Wordlist.luub.analysis, Wordlist.nak.analysis,
    Wordlist.tiil.analysis, Wordlist.tsuk.analysis, Wordlist.booxtal.analysis,
    Wordlist.chichantal.analysis]

-- §5, (21): degree achievements are externally caused, so they gain an instigator, where (14)
-- applied to their atelicity adds an affected object
theorem degreeAchievements_external :
    ∀ a ∈ degreeAchievements, a.causation = some .external := by
  decide

/-- The positional stems of (24), which pass the control test (23). -/
def controlledPositionals : List Wordlist.Analysis :=
  [Wordlist.waltal.analysis, Wordlist.kultal.analysis, Wordlist.chiltal.analysis,
    Wordlist.xoltal.analysis]

-- (24)–(25): controlled bases that are externally caused, so control does not fix the linking
theorem controlledPositionals_external :
    ∀ a ∈ controlledPositionals, a.causation = some .external := by
  decide

/-- The suffix of the transitivized stem the paper gives a base, its last morph. -/
def transitivizer (a : Wordlist.Analysis) : Option String :=
  (Wordlist.analysisRelations.find? (·.form = a)).bind (·.target.form.morphs.getLast?)

/-- The suffix underdetermines the linking: *meyah* 'work' (4) and *balak'* 'roll' (10) both take
*-t*, which adds an applied object to the one and an instigator to the other. -/
theorem underdetermines_suffix : Underdetermines transitivizer :=
  ⟨Wordlist.meyah.analysis, by decide, Wordlist.balak.analysis, by decide, rfl, rfl, "t",
    by decide, by decide⟩

-- (8), (10): nor is the suffix fixed by stem class and causation type together
theorem transitivizer_balak_ne_peek :
    Wordlist.balak.analysis.stemClass = Wordlist.peek.analysis.stemClass ∧
      Wordlist.balak.analysis.causation = Wordlist.peek.analysis.causation ∧
      transitivizer Wordlist.balak.analysis ≠ transitivizer Wordlist.peek.analysis := by
  decide

/-! ### Linking by viewpoint -/

/-- By rule (32), viewpoint aspect aligns with an end of the causal chain, and the role there sets
the default for linking. An imperfective viewpoint aligns with the initial subevent, making the
highest-ranking role the default, the accusative pattern. A perfective one aligns with the final
subevent or the chain as a whole, making the lowest-ranking role the default, the ergative
pattern. -/
def linkingDefault {α : Type*} [LE α] [BoundedOrder α] : Perfectivity → α
  | .imperfective => ⊥
  | .perfective => ⊤

/-- The marker of the sole argument S of an intransitive. S is unranked, so by (33c) it follows
the default that the viewpoint selects by (32), and takes the marker of that role. -/
def sMarkerFromViewpoint (v : Perfectivity) : Option MarkerSet :=
  markerOf (termRole (linkingDefault v))

/-- Linking by viewpoint derives the split: under each status with a viewpoint aspect, the sole
argument takes the marker set the viewpoint selects by (32) ((31), (33)). -/
theorem linking_derives_split {s : StatusCategory} {v : Perfectivity}
    (h : s.viewpointAspect = some v) : markerSet s .S = sMarkerFromViewpoint v := by
  cases s <;> cases v <;> first | rfl | cases h

-- §4, §7: under each status with a viewpoint, the marking has the alignment Hindi case has
-- under that viewpoint
theorem aspect_conditioned_split_family {s : StatusCategory} {v : Perfectivity}
    (h : s.viewpointAspect = some v) : (HindiUrdu.alignment v).Classifies (markerSet s) := by
  cases s <;> cases v <;> first | decide | cases h

/-! ### Detransitivization

Only transitive verbs that encode a causal relation between two subevents detransitivize. An
antipassive stem denotes the causing event, an anticausative stem the caused event, and a passive
stem the caused event with an internally-caused process causing it, whose instigator is not a
core argument ((28)–(30)). -/

/-- The detransitivizations of Yukatek, (12). -/
inductive Detransitivization where
  | antipassive
  | anticausative
  | passive
  deriving DecidableEq, Repr

namespace Detransitivization

/-- The template of a stem detransitivized from one of template `t`. The antipassive (28) keeps
the causing subevent, which it requires to be a process. The anticausative (29) keeps the caused
subevent. The passive (30) keeps the caused subevent and a process causing it. -/
def template : Detransitivization → Template .event → Option (Template .event)
  | .antipassive, .cause .act _ => some .act
  | .anticausative, .cause (σ := .event) _ e => some e
  | .passive, .cause _ e => some (.cause .act e)
  | _, _ => none

-- (28)–(30) presuppose a causal relation between two subevents
theorem exists_cause_of_template_isSome {d : Detransitivization} {t : Template .event}
    (h : (d.template t).isSome) :
    ∃ (c : Template .event) (σ : Eventuality) (e : Template σ), t = .cause c e := by
  cases t with
  | cause c e => exact ⟨c, _, e, rfl⟩
  | _ => cases d <;> simp [template] at h

/-- A passive stem denotes the event its anticausative denotes together with a process causing
it (30). -/
theorem passive_template_bind_caused (t : Template .event) :
    (passive.template t).bind Template.caused = anticausative.template t := by
  cases t with
  | @cause c σ e => cases σ <;> cases c <;> rfl
  | _ => rfl

-- (12): on *p'eh* 'chip', the antipassive denotes the chipping process, the anticausative the
-- change, and the passive the whole chain
example : antipassive.template .accomplishment = some .act ∧
    anticausative.template .accomplishment = some .achievement ∧
    passive.template .accomplishment = some .accomplishment := ⟨rfl, rfl, rfl⟩

/-- The subevent whose participant is the sole argument of the detransitivized stem, the causing
event for the antipassive and the caused event for the anticausative and the passive. -/
def retained : Detransitivization → Subevent
  | .antipassive => .causing
  | .anticausative | .passive => .caused

/-- Each Yukatek detransitivization as a voice. The antipassive denucleativizes P and makes A the
S, the anticausative suppresses A and makes P the S, and the passive denucleativizes A, which
stays in participant structure, and makes P the S. -/
def toVoice : Detransitivization → Voice
  | .antipassive => Voice.antipassive
  | .anticausative => Voice.anticausative
  | .passive => Voice.passive

end Detransitivization

/-- The initial role of the participant that a voice's derived construction privileges. -/
def pivotSourceRole (va : Voice) : Option TermRole :=
  (va.pivot.bind fun p ↦ (va.preimages p).head?).bind fun s ↦
    (va.initial.argumentRole s).map TermRole.ofArgumentRole

-- the sole argument of a detransitivized stem bears the role (33) assigns its subevent
theorem pivotSourceRole_toVoice (d : Detransitivization) :
    pivotSourceRole d.toVoice = some (termRole d.retained) := by
  cases d <;> decide

-- the instigator a passive stem entails stays in participant structure; the anticausative has
-- none
theorem fateOfRole_passive_anticausative :
    (Detransitivization.toVoice .passive).fateOfRole .A = .denucleativized ∧
      (Detransitivization.toVoice .anticausative).fateOfRole .A = .suppressed := by
  decide

/-! ### Stem classes and Lucy's root classes

[lucy-1994] classifies underived Yukatek roots by the transitivizer they require, where the stem
classes here are those of status inflection (§3). A root of Lucy's sample and a stem of this
paper are compared where their rows name one concept. -/

/-- The salience class of [lucy-1994] to which a stem class corresponds. Inchoative stems derive
from adjectival roots, which Lucy holds outside the predicate-root cut, and positional roots form
a separate cross-cutting class. -/
def salienceClassOf : VerbStemClass → Option ArgumentStructure.SalienceClass
  | .active => some .agent
  | .inactive => some .patient
  | .transitiveActive => some .agentPatient
  | .inchoative => none
  | .positional => none

-- (8): where a root of Lucy's sample and a stem here express one concept, the classes
-- correspond, except for *péek* 'move', active by its status pattern and taking *-s*
theorem salienceClassOf_eq_predictedClass_iff :
    ∀ a ∈ Wordlist.analyses, ∀ r ∈ Lucy1994.sampledRoots,
      a.form.parameterId = r.form.parameterId →
        (salienceClassOf (stemClass a.stemClass) = Lucy1994.predictedClass r ↔
          a ≠ Wordlist.peek.analysis) := by
  decide

end Bohnemeyer2004
