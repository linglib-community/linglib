module

public import Linglib.Fragments.Mayan.Yukatek.VerbClasses
public import Linglib.Fragments.HindiUrdu.Case
public import Linglib.Semantics.ArgumentStructure.EventStructure.Basic
public import Linglib.Core.Relation.ReflTransGen
public import Studies.Lucy1994
public import Linglib.Syntax.Voice.Basic

/-!
# Bohnemeyer 2004: split intransitivity, linking, and lexical representation

Bohnemeyer accounts for split intransitivity in Yukatek Maya. Kraemer and Wunderlich derive the
language's argument linking from lexical aspect alone; Bohnemeyer argues that what the linking
rules see is event structure, specifically whether the intransitive base entails internal
causation. Transitivizing an internally-caused base gives
applicative linking, the added applied object realized as U with the original S left as A;
transitivizing an externally-caused base gives causative linking, the added instigator realized as
A with the original S demoted to U (rules (26)–(27)). Which overt suffix appears, *-t* or *-s*, is
lexically idiosyncratic and can dissociate from the linking, as *balak'* 'roll' and *péek* 'move'
show in opposite directions.

The aspect-conditioned split itself follows from the same causal chain: the participant of a
causing subevent outranks that of the caused subevent (31), and an imperfective viewpoint aligns
with the initial subevent while a perfective one aligns with the final subevent or the chain as a
whole (32) — accusative and ergative defaults respectively.

The verbs and their stem classes are the Yukatek fragment's; the event type the paper reads into
each class, the causation type of each base and the transitivizing suffixes are the paper's and
are recorded here.

## Main definitions

* `Verb`, `CausationType`, `stemTemplate`: the fragment's verbs with the paper's causation
  type, and the event-structure template of each stem class (§5).
* `Subevent`, `Subevent.Causes`, `linkingDefault`, `sMarkerFromViewpoint`: the thematic
  hierarchy of (31) as causal precedence along the CAUSE edge, the linking-by-viewpoint rule of
  (32), and the linking of (33).
* `applicativeLinking`, `causativeLinking`, `verbLinking`, `addedTermRole`: the two
  transitivizations as `Voice`s, and the role their added participant takes.
* `TransitivizerSuffix`, `transitivizerSuffix`: the overt suffix, kept apart from the linking.
* `DetransitivizationType`, `DetransitivizationType.retained`: the antipassive, anticausative
  and passive of (28)–(30), and the subevent each denotes, a projection of the base's template
  (`Subevent.of`).

## Main results

* `linking_derives_completive`, `linking_derives_incompletive`: the split follows from
  (31)–(33).
* `causation_determines_linking` against `template_underdetermines_linking`,
  `stemClass_underdetermines_linking`, `suffix_underdetermines_linking`: what fixes the linking
  and what does not.
* `linking_patterns_swap_roles`, `linking_markers`: the two alternations are mirror images, read
  off their records rather than stipulated.
* `degree_achievements_causativize`, `haanEat_applicative_despite_inactive`: the counterexamples
  to aspect- and class-based linking.
* `predictLinking_roles`, `pivotSourceRole_toVoice`: the roles of transitivization (26)–(27)
  and of detransitivization (28)–(30) follow from the subevent a participant occupies, by the
  hierarchy (31).
* `passive_anticausative_distinct_by_A_fate`: the fate of the initial A separates the two.
* `salience_agrees_on_shared_roots`, `haanEat_defies_transitiviser_diagnostic`: where this
  classification meets Lucy's.

## References

* [bohnemeyer-2004]
* [kraemer-wunderlich-1999]
* [levin-hovav-1995]
* [lucy-1994]
-/

@[expose] public section

namespace Bohnemeyer2004

open ArgumentStructure.EventStructure Aspect Mayan Voice
open Yukatek (sArgumentMarker VerbStemClass)

/-! ### The verbs and their event structure

The stem classes are the fragment's. The paper reads the active stems as processes and the
inactive, inchoative and positional stems as state changes, degree achievements included (§5),
so the template of an intransitive stem class has `BECOME` exactly when the class is one of
state change. Each documented intransitive base is classified by whether it entails internal
causation (§6). -/

/-- The event-structure template of a stem class, the activity for actives, the achievement for
the three state-change classes and the accomplishment for transitives. -/
def stemTemplate : VerbStemClass → Template .event
  | .active => .act
  | .inactive | .inchoative | .positional => .achievement
  | .transitiveActive => .accomplishment

/-- Whether an event is internally caused in the sense of [levin-hovav-1995], brought about by
its instigator, a participant of the first event of a causal chain (§2). -/
inductive CausationType where
  | internal
  | external
  deriving DecidableEq, Repr

/-- A verb of the paper's examples with the causation type of its intransitive base. -/
structure Verb extends Yukatek.Verb where
  /-- Whether the base entails internal causation. -/
  causationType : CausationType
  deriving DecidableEq, Repr

/-- *meyah* 'work', internally caused. -/
def meyah : Verb := { toVerb := Yukatek.meyah, causationType := .internal }

/-- *bàaxal* 'play', internally caused. -/
def bàaxal : Verb := { toVerb := Yukatek.bàaxal, causationType := .internal }

/-- *hàan* 'eat', internally caused though inactive by stem class ((9)). -/
def hàan : Verb := { toVerb := Yukatek.hàan, causationType := .internal }

/-- *hats'* 'hit', internally caused. -/
def hats' : Verb := { toVerb := Yukatek.hats', causationType := .internal }

/-- *balak'* 'roll', externally caused. -/
def balak' : Verb := { toVerb := Yukatek.balak', causationType := .external }

/-- *péek* 'move', externally caused. -/
def péek : Verb := { toVerb := Yukatek.péek, causationType := .external }

/-- *tsíirin* 'buzz', externally caused. -/
def tsíirin : Verb := { toVerb := Yukatek.tsíirin, causationType := .external }

/-- *chíik* 'shake', externally caused. -/
def chíik : Verb := { toVerb := Yukatek.chíik, causationType := .external }

/-- *háarax* 'slide', externally caused. -/
def háarax : Verb := { toVerb := Yukatek.háarax, causationType := .external }

/-- *húuy* 'stir', externally caused. -/
def húuy : Verb := { toVerb := Yukatek.húuy, causationType := .external }

/-- *mosòon* 'whirl', externally caused. -/
def mosòon : Verb := { toVerb := Yukatek.mosòon, causationType := .external }

/-- *pirix* 'flick', externally caused. -/
def pirix : Verb := { toVerb := Yukatek.pirix, causationType := .external }

/-- *walak'* 'turn', externally caused. -/
def walak' : Verb := { toVerb := Yukatek.walak', causationType := .external }

/-- *nik'ich* 'squeak', externally caused. -/
def nik'ich : Verb := { toVerb := Yukatek.nik'ich, causationType := .external }

/-- *kim* 'die', externally caused. -/
def kim : Verb := { toVerb := Yukatek.kim, causationType := .external }

/-- *lúub* 'fall', externally caused. -/
def lúub : Verb := { toVerb := Yukatek.lúub, causationType := .external }

/-- *ka'n* 'get tired', externally caused. -/
def ka'n : Verb := { toVerb := Yukatek.ka'n, causationType := .external }

/-- *na'k* 'ascend', externally caused. -/
def na'k : Verb := { toVerb := Yukatek.na'k, causationType := .external }

/-- *la'b* 'deteriorate', externally caused. -/
def la'b : Verb := { toVerb := Yukatek.la'b, causationType := .external }

/-- *t'íil* 'last', externally caused. -/
def t'íil : Verb := { toVerb := Yukatek.t'íil, causationType := .external }

/-- *ts'u'k* 'rot', externally caused. -/
def ts'u'k : Verb := { toVerb := Yukatek.ts'u'k, causationType := .external }

/-- *bòox-tal* 'blacken', externally caused. -/
def bòoxtal : Verb := { toVerb := Yukatek.bòoxtal, causationType := .external }

/-- *chichan-tal* 'shrink', externally caused. -/
def chichantal : Verb := { toVerb := Yukatek.chichantal, causationType := .external }

/-- *kul-tal* 'sit down', externally caused. -/
def kultal : Verb := { toVerb := Yukatek.kultal, causationType := .external }

/-- *wa'l-tal* 'stand up', externally caused. -/
def wa'ltal : Verb := { toVerb := Yukatek.wa'ltal, causationType := .external }

/-- *chil-tal* 'lie down', externally caused. -/
def chiltal : Verb := { toVerb := Yukatek.chiltal, causationType := .external }

/-- *xol-tal* 'kneel', externally caused. -/
def xoltal : Verb := { toVerb := Yukatek.xoltal, causationType := .external }

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

/-- `termRole e` is the core term role of the participant of `e` (33a–b). The highest-ranking
role is the A of a transitive clause and the lowest-ranking role its P. -/
def termRole : Subevent → TermRole
  | .causing => .A
  | .caused => .P

/-- The other subevent of the chain. -/
def Subevent.other : Subevent → Subevent
  | .causing => .caused
  | .caused => .causing

/-- `e.of t` is the subevent `e` of the causative template `t`, its causing or its caused
subevent, and `none` when `t` is not causative. -/
def Subevent.of : Subevent → Template .event → Option (Template .event)
  | .causing => Template.causing
  | .caused => Template.caused

/-- `markerOf r` is the marker set the core term role `r` takes in Yukatek (33), set A for A and
set B for P. The sole
argument of an intransitive takes whichever the viewpoint selects, which is the split
(`sMarkerFromViewpoint`). -/
def markerOf : TermRole → Option MarkerSet
  | .A => some .setA
  | .P => some .setB
  | .S | .X => none

theorem markerOf_termRole_of_lt {a b : Subevent} (h : a < b) :
    markerOf (termRole a) = some .setA ∧ markerOf (termRole b) = some .setB := by
  revert a b; decide

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

/-! ### Linking by viewpoint derives the split

The composed mechanism reproduces the Yukatek split recorded in the Fragment's
`sArgumentMarker`: perfective status → ergative (set-B), imperfective →
accusative (set-A). -/

theorem linking_derives_completive :
    sMarkerFromViewpoint .perfective = sArgumentMarker .completive := rfl

theorem linking_derives_subjunctive :
    sMarkerFromViewpoint .perfective = sArgumentMarker .subjunctive := rfl

theorem linking_derives_incompletive :
    sMarkerFromViewpoint .imperfective = sArgumentMarker .incompletive := rfl

/-! ### Linking pattern under transitivization -/

/-- By rule (26), transitivizing an internally-caused base nucleativizes an applied object as P
while the base's S is maintained, surfacing as the A of the derived transitive clause. This is
Creissels' P-applicativization over an intransitive base. -/
def applicativeLinking : Voice := .of .intransitive .np [some .external, some (.complement 0)]

/-- By rule (27), transitivizing an externally-caused base nucleativizes an instigator as A, the
base's S surfacing as P. This is the causative unchanged. -/
def causativeLinking : Voice := causative

/-- The causation type of the intransitive base selects the alternation (rules 26–27). -/
def predictLinking : CausationType → Voice
  | .internal => applicativeLinking
  | .external => causativeLinking

/-- The alternation a Yukatek verb undergoes under transitivization. -/
def verbLinking (v : Verb) : Voice :=
  predictLinking v.causationType

/-- The role the added participant receives, read off the alternation. -/
def addedRole (va : Voice) : Option TermRole := va.newParticipant

/-- The base's S receives the role of the derived slot its participant occupies. -/
def originalRole (va : Voice) : Option TermRole :=
  (va.image .external).bind fun t ↦ (va.derived.status t).role

/-- Under transitivization the participant of an internally-caused base occupies the causing
process (26), and that of an externally-caused base the caused event (27). -/
def CausationType.baseSubevent : CausationType → Subevent
  | .internal => .causing
  | .external => .caused

/-- Under transitivization (26)–(27) and the hierarchy (31), the base participant takes the role of
its subevent and the added participant that of the other. -/
theorem predictLinking_roles (c : CausationType) :
    originalRole (predictLinking c) = some (termRole c.baseSubevent) ∧
      addedRole (predictLinking c) = some (termRole c.baseSubevent.other) := by
  cases c <;> decide

/-- Applicative and causative linking are mirror images, and not by stipulation: each alternation
adds a participant in the role the other leaves to the base's S, so the marker one assigns to the
added argument is the marker the other assigns to the original S. -/
theorem linking_patterns_swap_roles :
    addedRole applicativeLinking = originalRole causativeLinking ∧
    originalRole applicativeLinking = addedRole causativeLinking := by decide

/-- The marker each participant receives follows from its role by `markerOf`: the applicative adds
a set-B argument and keeps the base's S as set A, the causative the reverse. -/
theorem linking_markers :
    (addedRole applicativeLinking).bind markerOf = some .setB ∧
    (originalRole applicativeLinking).bind markerOf = some .setA ∧
    (addedRole causativeLinking).bind markerOf = some .setA ∧
    (originalRole causativeLinking).bind markerOf = some .setB := by decide

/-- Both transitivizations are valency-increasing, which the detransitivizations of (28)–(30) are
not — the two halves of the system are one mechanism read in two directions. -/
theorem transitivizations_increase_valency :
    applicativeLinking.IsValencyIncreasing ∧ causativeLinking.IsValencyIncreasing := by decide

/-- The added participant of a verb takes P under applicative linking and A under causative
linking. -/
def addedTermRole (v : Verb) : Option TermRole := addedRole (verbLinking v)

/-! ### Transitivizing suffix vs linking

The overt transitivizing suffix is lexically specified and *usually* tracks the linking pattern,
but the two can dissociate — the paper's central argument against aspect-based linking. The suffix
is paper-specific lexical data, so it is recorded here against the Fragment's entries rather than
in the Fragment. -/

/-- A transitivizing suffix is the applicative *-t* or the causative *-s*. -/
inductive TransitivizerSuffix where
  | applicativeT
  | causativeS
  deriving DecidableEq, Repr

/-- The suffix each verb the paper documents takes under transitivization (4), (5), (6), (7), (8),
(9), (10), (11). The suffix is lexically idiosyncratic, since *balak'* and *péek* are both
active and externally caused yet take *-t* and *-s* respectively. -/
def suffixTable : List (Verb × TransitivizerSuffix) :=
  [(meyah, .applicativeT), (bàaxal, .applicativeT), (hàan, .applicativeT),
   (balak', .applicativeT), (tsíirin, .applicativeT),
   (kim, .causativeS), (lúub, .causativeS), (péek, .causativeS)]

/-- The suffix of a documented verb; `none` for verbs the paper does not exemplify. -/
def transitivizerSuffix (v : Verb) : Option TransitivizerSuffix :=
  suffixTable.lookup v

/-- The verbs whose transitivization the paper exemplifies. -/
def documented : List Verb := suffixTable.map (·.1)

/-! ### What determines the linking

Causation type determines the alternation by rules (26)–(27). The paper's argument is that the
properties competing accounts appeal to do not: each of lexical aspect (which is what
[kraemer-wunderlich-1999]'s rule (14) reads), stem class, and the overt suffix leaves the linking
open, witnessed by a minimal pair of documented verbs. -/

/-- Causation type settles the alternation. -/
theorem causation_determines_linking (v w : Verb)
    (h : v.causationType = w.causationType) : verbLinking v = verbLinking w := by
  simp [verbLinking, h]

/-- *Meyah* 'work' and *balak'* 'roll' share a template but link differently, against the
aspect-based rule (14) ((4) vs (10)). -/
theorem template_underdetermines_linking :
    stemTemplate meyah.stemClass = stemTemplate balak'.stemClass ∧
    addedTermRole meyah ≠ addedTermRole balak' := ⟨rfl, by decide⟩

/-- Stem class does not settle it either. *Hàan* 'eat' and *kim* 'die' are both inactive, and
they link differently ((9) vs (6)). -/
theorem stemClass_underdetermines_linking :
    hàan.stemClass = kim.stemClass ∧
    addedTermRole hàan ≠ addedTermRole kim := ⟨rfl, by decide⟩

/-- *Meyah* and *balak'* take the same suffix *-t* but link differently (§6). -/
theorem suffix_underdetermines_linking :
    transitivizerSuffix meyah = transitivizerSuffix balak' ∧
    addedTermRole meyah ≠ addedTermRole balak' := ⟨rfl, by decide⟩

/-- *Balak'* and *péek* share stem class and causation type but differ in suffix ((8), (10)). -/
theorem suffix_not_predictable :
    balak'.stemClass = péek.stemClass ∧ balak'.causationType = péek.causationType ∧
    transitivizerSuffix balak' ≠ transitivizerSuffix péek := ⟨rfl, rfl, by decide⟩

theorem documented_linking :
    documented.all (fun v ↦
      addedTermRole v == some (if v.causationType == .internal then .P else .A)) = true := by
  decide

/-! ### Degree achievements: event type vs aspect -/

/-- Degree achievements such as *ka'n* have a result state, as *-a'n* (19) and *láah* (20) attest,
despite behaving atelically under (15) (§5). -/
theorem kaan_is_state_change : (stemTemplate ka'n.stemClass).HasResultState := by decide

theorem naak_is_state_change : (stemTemplate na'k.stemClass).HasResultState := by decide

/-- Degree achievements causativize like state-change verbs, adding an A, against rule (14) ((17),
(21)). -/
theorem degree_achievements_causativize :
    addedTermRole ka'n = some .A ∧ addedTermRole na'k = some .A := ⟨rfl, rfl⟩

/-- *hàan* 'eat' is inactive by stem class yet internally caused, and it applicativizes ((9)): if
stem class determined transitivization it would causativize like *kim* 'die'. -/
theorem haanEat_applicative_despite_inactive :
    hàan.stemClass = .inactive ∧ addedTermRole hàan = some .P := ⟨rfl, rfl⟩

/-! ### Bridge to detransitivization

The three Yukatek detransitivizations are instances of the cross-linguistic
valency-alternation typology (`Syntax/Voice/Alternation.lean`).
That substrate keeps passive and anticausative distinct by the fate of the
initial A — passive *denucleativizes* it (retained in participant structure as
a possible oblique agent), anticausative *suppresses* it (removed entirely). -/

/-- The detransitivizations of Yukatek are those of rules (28)–(30). The antipassive (28) removes
the caused event and retains the causing process, and active intransitives inflect like
antipassive stems. The anticausative (29) removes the causing event and retains the caused one,
and inactive intransitives inflect like anticausative stems. The passive (30) is like the
anticausative but adds PROC_C and an instigator to the caused event. -/
inductive DetransitivizationType where
  | antipassive   -- retain causing process, remove caused event
  | anticausative -- retain caused event, remove causing process
  | passive       -- retain caused event, add instigator
  deriving DecidableEq, Repr

/-- Each Yukatek detransitivization is a cross-linguistic valency alternation. The antipassive
denucleativizes P and makes A the S, the anticausative suppresses A and makes P the S, and the
passive denucleativizes A but retains it and makes P the S. -/
def DetransitivizationType.toVoice : DetransitivizationType → Voice
  | .antipassive => Voice.antipassive
  | .anticausative => Voice.anticausative
  | .passive => Voice.passive

/-- All three detransitivizations are valency-decreasing, as in the antipassive *p'èeh*, the
passive *p'e'h-el* and the anticausative *p'éeh-el* of *p'eh* 'chip' (12). -/
theorem detransitivizations_decrease_valency :
    (DetransitivizationType.toVoice .antipassive).IsValencyDecreasing ∧
    (DetransitivizationType.toVoice .anticausative).IsValencyDecreasing ∧
    (DetransitivizationType.toVoice .passive).IsValencyDecreasing := by decide

/-- The fate of the initial A separates the passive from the anticausative, a distinction the
coarser intransitivization typology collapses. The passive denucleativizes A, which stays in
participant structure, and the anticausative suppresses it. -/
theorem passive_anticausative_distinct_by_A_fate :
    (DetransitivizationType.toVoice .passive).fateOfRole .A = .denucleativized ∧
    (DetransitivizationType.toVoice .anticausative).fateOfRole .A = .suppressed := by
  decide

/-! ### The subevent a detransitivized stem denotes

"Antipassives denote the causing event, while anticausatives and passives denote the caused
event" (§6): each detransitivization keeps one subevent of its base's causal chain, whose
participant is the derived stem's sole argument. (29) and (30) leave open whether the caused
event is a state change, and the contact verbs that passivize and anticausativize may not
entail one. -/

/-- A stem detransitivized by `d` denotes the subevent `d.retained`, the causing event for the
antipassive (28) and the caused event for the anticausative and the passive ((29)–(30)). The
passive differs from the
anticausative in participant structure, not in the subevent it denotes. -/
def DetransitivizationType.retained : DetransitivizationType → Subevent
  | .antipassive => .causing
  | .anticausative | .passive => .caused

/-- The template a detransitivized stem denotes, the retained subevent of its base's
template. -/
def DetransitivizationType.template (d : DetransitivizationType) :
    Template .event → Option (Template .event) :=
  d.retained.of

/-- Rules (28)–(30) presuppose that only verbs encoding a causal relation between two subevents
detransitivize. -/
theorem DetransitivizationType.isSome_template_iff (d : DetransitivizationType)
    (t : Template .event) :
    (d.template t).isSome ↔ ∃ c e, t = .cause c e := by
  cases d <;> cases t <;>
    simp [DetransitivizationType.template, DetransitivizationType.retained, Subevent.of,
      Template.causing, Template.caused]

/-- The initial role of the participant that a voice's derived construction privileges. -/
def pivotSourceRole (va : Voice) : Option TermRole :=
  (va.pivot.bind fun p ↦ (va.preimages p).head?).bind fun s ↦
    (va.initial.argumentRole s).map TermRole.ofArgumentRole

/-- The sole argument of a detransitivized stem bears the role (33) assigns its subevent, the A for
an antipassive and the P otherwise. -/
theorem pivotSourceRole_toVoice (d : DetransitivizationType) :
    pivotSourceRole d.toVoice = some (termRole d.retained) := by
  cases d <;> decide

/-- On a transitive stem, the antipassive denotes the causing process and the anticausative the
caused change. -/
example : DetransitivizationType.antipassive.template (stemTemplate .transitiveActive) = some .act ∧
    DetransitivizationType.anticausative.template (stemTemplate .transitiveActive) =
      some .achievement := ⟨rfl, rfl⟩

/-! ### The rest of the inventory -/

/-- The Fragment's externally-caused verbs span three stem classes, the manner-of-motion and
sound-emission actives, the positionals ((25)) and the inactive degree achievements ((17)). -/
def externallyCaused : List Verb :=
  [chíik, háarax, húuy, mosòon, pirix, walak', chiltal, xoltal, la'b, t'íil, ts'u'k, ka'n, na'k]

theorem externally_caused_causativize :
    externallyCaused.all (fun v ↦
      v.causationType == .external && addedTermRole v == some .A) = true := by decide

/-! ### Bridge to split ergativity -/

theorem linking_consistent_with_split :
    Yukatek.alignment .completive = .ergative ∧ Yukatek.alignment .incompletive = .accusative :=
  ⟨rfl, rfl⟩

theorem aspect_conditioned_split_family :
    Yukatek.alignment .completive = HindiUrdu.alignment .perfective := rfl

/-! ### Stem classes vs Lucy's root classes

[lucy-1994] classifies underived Yukatek roots by required transitiviser;
this paper's five stem classes cut the same lexicon by status inflection.
The comparison lives here because the paper engages Lucy's analysis
directly — §5 argues degree achievements defeat its Vendlerian construal
of these classes. -/

/-- `salienceClassOf c` is the salience class of Lucy's that the stem class `c` corresponds to.
The map is partial. `inchoative` stems derive from adjectival roots (completive *-chah*), which
Lucy holds outside the predicate-root cut, and `positional` roots form Lucy's separate
cross-cutting class (completive *-lah*); the two stem classes share only the anomalous
incompletive *-tal*. -/
def salienceClassOf : VerbStemClass → Option ArgumentStructure.SalienceClass
  | .active => some .agent
  | .inactive => some .patient
  | .transitiveActive => some .agentPatient
  | .inchoative => none
  | .positional => none

/-- Where the two samples share a lexeme, stem class and Lucy's derived root class agree, for
*kim* ~ *kíim* 'die', *lúub* ~ *lúub'* 'fall' and *na'k* ~ *ná'ak* 'ascend'. -/
theorem salience_agrees_on_shared_roots :
    salienceClassOf kim.stemClass = Lucy1994.predictedClass Lucy1994.kiim ∧
    salienceClassOf lúub.stemClass = Lucy1994.predictedClass Lucy1994.luub ∧
    salienceClassOf na'k.stemClass = Lucy1994.predictedClass Lucy1994.naak :=
  ⟨rfl, rfl, rfl⟩

/-- *Hàan* 'eat' is patient salient by stem class yet takes applicative *-t*, so the suffix tracks
internal causation (9). -/
theorem haanEat_defies_transitiviser_diagnostic :
    transitivizerSuffix hàan = some .applicativeT ∧
    salienceClassOf hàan.stemClass = some .patient := ⟨rfl, rfl⟩

/-- This paper classifies *péek* as agent salient, and Lucy's (4) as patient salient. -/
theorem peek_stem_vs_root_class_divergence :
    salienceClassOf péek.stemClass = some .agent ∧
    Lucy1994.predictedClass Lucy1994.peek = some .patient := ⟨rfl, rfl⟩

end Bohnemeyer2004
