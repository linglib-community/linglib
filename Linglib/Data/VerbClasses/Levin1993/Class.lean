module

public import Mathlib.Tactic.DeriveFintype

/-!
# Levin1993: the verb classes (generated)

Auto-generated from `Linglib/Data/VerbClasses/Levin1993.json` by `scripts/gen_verb_classes.py`.
**Do not edit by hand**: edit the JSON and re-run the generator.

The verb classes of Part II of the book, one constructor per class page with a member list, in the
book's order and named by the class's head word or the book's label, with the section number the
book prints (`LevinClass.number`). The class pages are in `Data/VerbClasses/Levin1993.lean` and the
classes of each verb in `Data/VerbClasses/Levin1993/Index.lean`.

## References

* [levin-1993]
-/

@[expose] public section

namespace ArgumentStructure

set_option maxRecDepth 4000 in
/-- The verb classes of [levin-1993] Part II. -/
inductive LevinClass where
  /-- 9.1, Put Verbs. -/
  | put
  /-- 9.2, Verbs of Putting in a Spatial Configuration. -/
  | putInSpatialConfiguration
  /-- 9.3, Funnel Verbs. -/
  | funnel
  /-- 9.4, Verbs of Putting with a Specified Direction. -/
  | putDirection
  /-- 9.5, Pour Verbs. -/
  | pour
  /-- 9.6, Coil Verbs. -/
  | coil
  /-- 9.7, Spray/Load Verbs. -/
  | sprayLoad
  /-- 9.8, Fill Verbs. -/
  | fill
  /-- 9.9, Butter Verbs. -/
  | butter
  /-- 9.10, Pocket Verbs. -/
  | pocket
  /-- 10.1, Remove Verbs. -/
  | remove
  /-- 10.2, Banish Verbs. -/
  | banish
  /-- 10.3, Clear Verbs. -/
  | clear
  /-- 10.4.1, Manner Subclass. -/
  | wipeManner
  /-- 10.4.2, Instrument Subclass. -/
  | wipeInstrument
  /-- 10.5, Verbs of Possessional Deprivation: Steal Verbs. -/
  | steal
  /-- 10.6, Verbs of Possessional Deprivation: Cheat Verbs. -/
  | cheat
  /-- 10.7, Pit Verbs. -/
  | pit
  /-- 10.8, Debone Verbs. -/
  | debone
  /-- 10.9, Mine Verbs. -/
  | mine
  /-- 11.1, Send Verbs. -/
  | send
  /-- 11.2, Slide Verbs. -/
  | slide
  /-- 11.3, Bring and Take. -/
  | bringTake
  /-- 11.4, Carry Verbs. -/
  | carry
  /-- 11.5, Drive Verbs. -/
  | drive
  /-- 12, Verbs of Exerting Force: Push/Pull Verbs. -/
  | pushPull
  /-- 13.1, Give Verbs. -/
  | give
  /-- 13.2, Contribute Verbs. -/
  | contribute
  /-- 13.3, Verbs of Future Having. -/
  | futureHaving
  /-- 13.4.1, Verbs of Fulfilling. -/
  | fulfilling
  /-- 13.4.2, Equip Verbs. -/
  | equip
  /-- 13.5.1, Get Verbs. -/
  | get
  /-- 13.5.2, Obtain Verbs. -/
  | obtain
  /-- 13.6, Verbs of Exchange. -/
  | exchange
  /-- 13.7, Berry Verbs. -/
  | berry
  /-- 14, Learn Verbs. -/
  | learn
  /-- 15.1, Hold Verbs. -/
  | hold
  /-- 15.2, Keep Verbs. -/
  | keep
  /-- 16, Verbs of Concealment. -/
  | conceal
  /-- 17.1, Throw Verbs. -/
  | throw
  /-- 17.2, Pelt Verbs. -/
  | pelt
  /-- 18.1, Hit Verbs. -/
  | hit
  /-- 18.2, Swat Verbs. -/
  | swat
  /-- 18.3, Spank Verbs. -/
  | spank
  /-- 18.4, Non-Agentive Verbs of Impact by Contact. -/
  | nonAgentiveImpact
  /-- 19, Poke Verbs. -/
  | poke
  /-- 20, Verbs of Contact: Touch Verbs. -/
  | touch
  /-- 21.1, Cut Verbs. -/
  | cut
  /-- 21.2, Carve Verbs. -/
  | carve
  /-- 22.1, Mix Verbs. -/
  | mix
  /-- 22.2, Amalgamate Verbs. -/
  | amalgamate
  /-- 22.3, Shake Verbs. -/
  | shake
  /-- 22.4, Tape Verbs. -/
  | tape
  /-- 22.5, Cling Verbs. -/
  | cling
  /-- 23.1, Separate Verbs. -/
  | separate
  /-- 23.2, Split Verbs. -/
  | split
  /-- 23.3, Disassemble Verbs. -/
  | disassemble
  /-- 23.4, Differ Verbs. -/
  | differ
  /-- 24, Verbs of Coloring. -/
  | color
  /-- 25.1, Verbs of Image Impression. -/
  | imageImpression
  /-- 25.2, Scribble Verbs. -/
  | scribble
  /-- 25.3, Illustrate Verbs. -/
  | illustrate
  /-- 25.4, Transcribe Verbs. -/
  | transcribe
  /-- 26.1, Build Verbs. -/
  | build
  /-- 26.2, Grow Verbs. -/
  | grow
  /-- 26.3, Verbs of Preparing. -/
  | prepare
  /-- 26.4, Create Verbs. -/
  | create
  /-- 26.5, Knead Verbs. -/
  | knead
  /-- 26.6, Turn Verbs. -/
  | turn
  /-- 26.7, Performance Verbs. -/
  | performance
  /-- 27, Engender Verbs. -/
  | engender
  /-- 28, Calve Verbs. -/
  | calve
  /-- 29.1, Appoint Verbs. -/
  | appoint
  /-- 29.2, Characterize Verbs. -/
  | characterize
  /-- 29.3, Dub Verbs. -/
  | dub
  /-- 29.4, Declare Verbs. -/
  | declare
  /-- 29.5, Conjecture Verbs. -/
  | conjecture
  /-- 29.6, Masquerade Verbs. -/
  | masquerade
  /-- 29.7, Orphan Verbs. -/
  | orphan
  /-- 29.8, Captain Verbs. -/
  | captain
  /-- 30.1, See Verbs. -/
  | see
  /-- 30.2, Sight Verbs. -/
  | sight
  /-- 30.3, Peer Verbs. -/
  | peer
  /-- 30.4, Stimulus Subject Perception Verbs. -/
  | stimulusSubjectPerception
  /-- 31.1, Amuse Verbs. -/
  | amuse
  /-- 31.2, Admire Verbs. -/
  | admire
  /-- 31.3, Marvel Verbs. -/
  | marvel
  /-- 31.4, Appeal Verbs. -/
  | appeal
  /-- 32.1, Want Verbs. -/
  | want
  /-- 32.2, Long Verbs. -/
  | long
  /-- 33, Judgment Verbs. -/
  | judgment
  /-- 34, Verbs of Assessment. -/
  | assessment
  /-- 35.1, Hunt Verbs. -/
  | hunt
  /-- 35.2, Search Verbs. -/
  | search
  /-- 35.3, Stalk Verbs. -/
  | stalk
  /-- 35.4, Investigate Verbs. -/
  | investigate
  /-- 35.5, Rummage Verbs. -/
  | rummage
  /-- 35.6, Ferret Verbs. -/
  | ferret
  /-- 36.1, Correspond Verbs. -/
  | correspond
  /-- 36.2, Marry Verbs. -/
  | marry
  /-- 36.3, Meet Verbs. -/
  | meet
  /-- 37.1, Verbs of Transfer of a Message. -/
  | transferOfMessage
  /-- 37.2, Tell. -/
  | tell
  /-- 37.3, Verbs of Manner of Speaking. -/
  | mannerOfSpeaking
  /-- 37.4, Verbs of Instrument of Communication. -/
  | instrumentOfCommunication
  /-- 37.5, Talk Verbs. -/
  | talk
  /-- 37.6, Chitchat Verbs. -/
  | chitchat
  /-- 37.7, Say Verbs. -/
  | say
  /-- 37.8, Complain Verbs. -/
  | complain
  /-- 37.9, Advise Verbs. -/
  | advise
  /-- 38, Verbs of Sounds Made by Animals. -/
  | animalSound
  /-- 39.1, Eat Verbs. -/
  | eat
  /-- 39.2, Chew Verbs. -/
  | chew
  /-- 39.3, Gobble Verbs. -/
  | gobble
  /-- 39.4, Devour Verbs. -/
  | devour
  /-- 39.5, Dine Verbs. -/
  | dine
  /-- 39.6, Gorge Verbs. -/
  | gorge
  /-- 39.7, Verbs of Feeding. -/
  | feed
  /-- 40.1.1, Hiccup Verbs. -/
  | hiccup
  /-- 40.1.2, Breathe Verbs. -/
  | breathe
  /-- 40.1.3, Exhale Verbs. -/
  | exhale
  /-- 40.2, Verbs of Nonverbal Expression. -/
  | nonverbalExpression
  /-- 40.3.1, Wink Verbs. -/
  | wink
  /-- 40.3.2, Crane Verbs. -/
  | crane
  /-- 40.3.3, Curtsey Verbs. -/
  | curtsey
  /-- 40.4, Snooze Verbs. -/
  | snooze
  /-- 40.5, Flinch Verbs. -/
  | flinch
  /-- 40.6, Verbs of Body-Internal States of Existence. -/
  | bodyInternalStateOfExistence
  /-- 40.7, Suffocate Verbs. -/
  | suffocate
  /-- 40.8.1, Pain Verbs. -/
  | pain
  /-- 40.8.2, Tingle Verbs. -/
  | tingle
  /-- 40.8.3, Hurt Verbs. -/
  | hurt
  /-- 40.8.4, Verbs of Change of Bodily State. -/
  | changeOfBodilyState
  /-- 41.1.1, Dress Verbs. -/
  | dress
  /-- 41.1.2, Groom Verbs. -/
  | groom
  /-- 41.2.1, Floss Verbs. -/
  | floss
  /-- 41.2.2, Braid Verbs. -/
  | braid
  /-- 41.3.1, Simple Verbs of Dressing. -/
  | simpleDressing
  /-- 41.3.2, Verbs of Dressing Well. -/
  | dressingWell
  /-- 41.3.3, Verbs of Being Dressed. -/
  | beingDressed
  /-- 42.1, Murder Verbs. -/
  | murder
  /-- 42.2, Poison Verbs. -/
  | poison
  /-- 43.1, Verbs of Light Emission. -/
  | lightEmission
  /-- 43.2, Verbs of Sound Emission. -/
  | soundEmission
  /-- 43.3, Verbs of Smell Emission. -/
  | smellEmission
  /-- 43.4, Verbs of Substance Emission. -/
  | substanceEmission
  /-- 44, Destroy Verbs. -/
  | destroy
  /-- 45.1, Break Verbs. -/
  | break_
  /-- 45.2, Bend Verbs. -/
  | bend
  /-- 45.3, Cooking Verbs. -/
  | cooking
  /-- 45.4, Other Alternating Verbs of Change of State. -/
  | otherChangeOfState
  /-- 45.5, Verbs of Entity-Specific Change of State. -/
  | entitySpecificChangeOfState
  /-- 45.6, Verbs of Calibratable Changes of State. -/
  | calibratableChangeOfState
  /-- 46, Lodge Verbs. -/
  | lodge
  /-- 47.1, Exist Verbs. -/
  | exist
  /-- 47.2, Verbs of Entity-Specific Modes of Being. -/
  | entitySpecificModeOfBeing
  /-- 47.3, Verbs of Modes of Being Involving Motion. -/
  | modeOfBeingInvolvingMotion
  /-- 47.4, Verbs of Sound Existence. -/
  | soundExistence
  /-- 47.5.1, Swarm Verbs. -/
  | swarm
  /-- 47.5.2, Herd Verbs. -/
  | herd
  /-- 47.5.3, Bulge Verbs. -/
  | bulge
  /-- 47.6, Verbs of Spatial Configuration. -/
  | spatialConfiguration
  /-- 47.7, Meander Verbs. -/
  | meander
  /-- 47.8, Verbs of Contiguous Location. -/
  | contiguousLocation
  /-- 48.1.1, Appear Verbs. -/
  | appear
  /-- 48.1.2, Reflexive Verbs of Appearance. -/
  | reflexiveAppearance
  /-- 48.2, Verbs of Disappearance. -/
  | disappearance
  /-- 48.3, Verbs of Occurrence. -/
  | occurrence
  /-- 49, Verbs of Body-Internal Motion. -/
  | bodyInternalMotion
  /-- 50, Verbs of Assuming a Position. -/
  | assumePosition
  /-- 51.1, Verbs of Inherently Directed Motion. -/
  | inherentlyDirectedMotion
  /-- 51.2, Leave Verbs. -/
  | leave
  /-- 51.3.1, Roll Verbs. -/
  | roll
  /-- 51.3.2, Run Verbs. -/
  | run
  /-- 51.4.1, Verbs That Are Vehicle Names. -/
  | vehicleName
  /-- 51.4.2, Verbs That Are Not Vehicle Names. -/
  | nonVehicleName
  /-- 51.5, Waltz Verbs. -/
  | waltz
  /-- 51.6, Chase Verbs. -/
  | chase
  /-- 51.7, Accompany Verbs. -/
  | accompany
  /-- 52, Avoid Verbs. -/
  | avoid
  /-- 53.1, Verbs of Lingering. -/
  | linger
  /-- 53.2, Verbs of Rushing. -/
  | rush
  /-- 54.1, Register Verbs. -/
  | register
  /-- 54.2, Cost Verbs. -/
  | cost
  /-- 54.3, Fit Verbs. -/
  | fit
  /-- 54.4, Price Verbs. -/
  | price
  /-- 54.5, Bill Verbs. -/
  | bill
  /-- 55.1, Begin Verbs. -/
  | begin
  /-- 55.2, Complete Verbs. -/
  | complete
  /-- 56, Weekend Verbs. -/
  | weekend
  /-- 57, Weather Verbs. -/
  | weather
  deriving DecidableEq, Repr, Fintype

namespace LevinClass

/-- The section number the book prints, as its list of numerals. -/
def number : LevinClass → List ℕ
  | .put => [9, 1]
  | .putInSpatialConfiguration => [9, 2]
  | .funnel => [9, 3]
  | .putDirection => [9, 4]
  | .pour => [9, 5]
  | .coil => [9, 6]
  | .sprayLoad => [9, 7]
  | .fill => [9, 8]
  | .butter => [9, 9]
  | .pocket => [9, 10]
  | .remove => [10, 1]
  | .banish => [10, 2]
  | .clear => [10, 3]
  | .wipeManner => [10, 4, 1]
  | .wipeInstrument => [10, 4, 2]
  | .steal => [10, 5]
  | .cheat => [10, 6]
  | .pit => [10, 7]
  | .debone => [10, 8]
  | .mine => [10, 9]
  | .send => [11, 1]
  | .slide => [11, 2]
  | .bringTake => [11, 3]
  | .carry => [11, 4]
  | .drive => [11, 5]
  | .pushPull => [12]
  | .give => [13, 1]
  | .contribute => [13, 2]
  | .futureHaving => [13, 3]
  | .fulfilling => [13, 4, 1]
  | .equip => [13, 4, 2]
  | .get => [13, 5, 1]
  | .obtain => [13, 5, 2]
  | .exchange => [13, 6]
  | .berry => [13, 7]
  | .learn => [14]
  | .hold => [15, 1]
  | .keep => [15, 2]
  | .conceal => [16]
  | .throw => [17, 1]
  | .pelt => [17, 2]
  | .hit => [18, 1]
  | .swat => [18, 2]
  | .spank => [18, 3]
  | .nonAgentiveImpact => [18, 4]
  | .poke => [19]
  | .touch => [20]
  | .cut => [21, 1]
  | .carve => [21, 2]
  | .mix => [22, 1]
  | .amalgamate => [22, 2]
  | .shake => [22, 3]
  | .tape => [22, 4]
  | .cling => [22, 5]
  | .separate => [23, 1]
  | .split => [23, 2]
  | .disassemble => [23, 3]
  | .differ => [23, 4]
  | .color => [24]
  | .imageImpression => [25, 1]
  | .scribble => [25, 2]
  | .illustrate => [25, 3]
  | .transcribe => [25, 4]
  | .build => [26, 1]
  | .grow => [26, 2]
  | .prepare => [26, 3]
  | .create => [26, 4]
  | .knead => [26, 5]
  | .turn => [26, 6]
  | .performance => [26, 7]
  | .engender => [27]
  | .calve => [28]
  | .appoint => [29, 1]
  | .characterize => [29, 2]
  | .dub => [29, 3]
  | .declare => [29, 4]
  | .conjecture => [29, 5]
  | .masquerade => [29, 6]
  | .orphan => [29, 7]
  | .captain => [29, 8]
  | .see => [30, 1]
  | .sight => [30, 2]
  | .peer => [30, 3]
  | .stimulusSubjectPerception => [30, 4]
  | .amuse => [31, 1]
  | .admire => [31, 2]
  | .marvel => [31, 3]
  | .appeal => [31, 4]
  | .want => [32, 1]
  | .long => [32, 2]
  | .judgment => [33]
  | .assessment => [34]
  | .hunt => [35, 1]
  | .search => [35, 2]
  | .stalk => [35, 3]
  | .investigate => [35, 4]
  | .rummage => [35, 5]
  | .ferret => [35, 6]
  | .correspond => [36, 1]
  | .marry => [36, 2]
  | .meet => [36, 3]
  | .transferOfMessage => [37, 1]
  | .tell => [37, 2]
  | .mannerOfSpeaking => [37, 3]
  | .instrumentOfCommunication => [37, 4]
  | .talk => [37, 5]
  | .chitchat => [37, 6]
  | .say => [37, 7]
  | .complain => [37, 8]
  | .advise => [37, 9]
  | .animalSound => [38]
  | .eat => [39, 1]
  | .chew => [39, 2]
  | .gobble => [39, 3]
  | .devour => [39, 4]
  | .dine => [39, 5]
  | .gorge => [39, 6]
  | .feed => [39, 7]
  | .hiccup => [40, 1, 1]
  | .breathe => [40, 1, 2]
  | .exhale => [40, 1, 3]
  | .nonverbalExpression => [40, 2]
  | .wink => [40, 3, 1]
  | .crane => [40, 3, 2]
  | .curtsey => [40, 3, 3]
  | .snooze => [40, 4]
  | .flinch => [40, 5]
  | .bodyInternalStateOfExistence => [40, 6]
  | .suffocate => [40, 7]
  | .pain => [40, 8, 1]
  | .tingle => [40, 8, 2]
  | .hurt => [40, 8, 3]
  | .changeOfBodilyState => [40, 8, 4]
  | .dress => [41, 1, 1]
  | .groom => [41, 1, 2]
  | .floss => [41, 2, 1]
  | .braid => [41, 2, 2]
  | .simpleDressing => [41, 3, 1]
  | .dressingWell => [41, 3, 2]
  | .beingDressed => [41, 3, 3]
  | .murder => [42, 1]
  | .poison => [42, 2]
  | .lightEmission => [43, 1]
  | .soundEmission => [43, 2]
  | .smellEmission => [43, 3]
  | .substanceEmission => [43, 4]
  | .destroy => [44]
  | .break_ => [45, 1]
  | .bend => [45, 2]
  | .cooking => [45, 3]
  | .otherChangeOfState => [45, 4]
  | .entitySpecificChangeOfState => [45, 5]
  | .calibratableChangeOfState => [45, 6]
  | .lodge => [46]
  | .exist => [47, 1]
  | .entitySpecificModeOfBeing => [47, 2]
  | .modeOfBeingInvolvingMotion => [47, 3]
  | .soundExistence => [47, 4]
  | .swarm => [47, 5, 1]
  | .herd => [47, 5, 2]
  | .bulge => [47, 5, 3]
  | .spatialConfiguration => [47, 6]
  | .meander => [47, 7]
  | .contiguousLocation => [47, 8]
  | .appear => [48, 1, 1]
  | .reflexiveAppearance => [48, 1, 2]
  | .disappearance => [48, 2]
  | .occurrence => [48, 3]
  | .bodyInternalMotion => [49]
  | .assumePosition => [50]
  | .inherentlyDirectedMotion => [51, 1]
  | .leave => [51, 2]
  | .roll => [51, 3, 1]
  | .run => [51, 3, 2]
  | .vehicleName => [51, 4, 1]
  | .nonVehicleName => [51, 4, 2]
  | .waltz => [51, 5]
  | .chase => [51, 6]
  | .accompany => [51, 7]
  | .avoid => [52]
  | .linger => [53, 1]
  | .rush => [53, 2]
  | .register => [54, 1]
  | .cost => [54, 2]
  | .fit => [54, 3]
  | .price => [54, 4]
  | .bill => [54, 5]
  | .begin => [55, 1]
  | .complete => [55, 2]
  | .weekend => [56]
  | .weather => [57]

end LevinClass

end ArgumentStructure
