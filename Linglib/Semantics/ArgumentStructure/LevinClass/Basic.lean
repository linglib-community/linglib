module

public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Selection
public import Linglib.Semantics.Events.Path
public import Linglib.Semantics.Aspect.Defs
public import Mathlib.Data.Finset.Fold
public import Mathlib.Tactic.DeriveFintype

/-!
# The verb classes of Levin 1993

`LevinClass` enumerates the verb classes of Part II of Levin's *English Verb Classes and
Alternations*, one constructor for each class page with a member list, with the section number and
title the book prints for it. The classes' property tables are in `Properties.lean`, their member
lists in `Members.lean` and their root entailments in `RootEntailment.lean`; the `levinClasses`
field of a `Verb` entry carries the classes listing it. A class may also carry a default
argument-structure template, from which a verb entry's argument profiles are derived.

## Implementation notes

The section numbers and titles were checked against the book's section headings. The
`maxRecDepth` setting on the inductive serves `deriving Fintype`, whose handler for enumerations
checks its list of the 191 constructors by `rfl`.

## References

* [B. Levin, *English verb classes and alternations: a preliminary investigation*
  (1993)][levin-1993]
* [D. Dowty, *Thematic proto-roles and argument selection* (1991)][dowty-1991]
* [B. Levin, M. Rappaport Hovav, *Argument realization* (2005)][levin-rappaport-hovav-2005]
-/

@[expose] public section

namespace ArgumentStructure

set_option maxRecDepth 4000 in
/-- The verb classes of [levin-1993] Part II, one constructor per class with a member list,
named by the class's head word or Levin's label, with the section number and the first members
of the class's list. -/
inductive LevinClass where
  -- Verbs of Putting (§ 9)
  | put                          -- 9.1: arrange, immerse, install, lodge, ...
  | putInSpatialConfiguration    -- 9.2: dangle, hang, lay, lean, ...
  | funnel                       -- 9.3: bang, channel, dip, dump, ...
  | putDirection                 -- 9.4: drop, hoist, lift, lower, ...
  | pour                         -- 9.5: dribble, drip, pour, slop, ...
  | coil                         -- 9.6: coil, curl, loop, roll, ...
  | sprayLoad                    -- 9.7: brush, cram, crowd, cultivate, ...
  | fill                         -- 9.8: adorn, anoint, bandage, bathe, ...
  | butter                       -- 9.9: asphalt, bait, blanket, blindfold, ...
  | pocket                       -- 9.10: archive, bag, bank, beach, ...
  -- Verbs of Removing (§ 10)
  | remove                       -- 10.1: abstract, cull, delete, discharge, ...
  | banish                       -- 10.2: banish, deport, evacuate, expel, ...
  | clear                        -- 10.3: clean, clear, drain, empty, ...
  | wipeManner                   -- 10.4.1: bail, buff, dab, distill, ...
  | wipeInstrument               -- 10.4.2: brush, comb, file, filter, ...
  | steal                        -- 10.5: abduct, cadge, capture, confiscate, ...
  | cheat                        -- 10.6: absolve, acquit, balk, bereave, ...
  | pit                          -- 10.7: bark, beard, bone, burl, ...
  | debone                       -- 10.8: deaccent, debark, debone, debowel, ...
  | mine                         -- 10.9: mine, quarry, ...
  -- Verbs of Sending and Carrying (§ 11)
  | send                         -- 11.1: airmail, convey, deliver, dispatch, ...
  | slide                        -- 11.2: bounce, float, move, roll, ...
  | bringTake                    -- 11.3: bring, take, ...
  | carry                        -- 11.4: carry, drag, haul, heave, ...
  | drive                        -- 11.5: barge, bus, cart, drive, ...
  -- Verbs of Exerting Force: Push/Pull Verbs (§ 12)
  | pushPull                     -- 12: draw, heave, jerk, press, ...
  -- Verbs of Change of Possession (§ 13)
  | give                         -- 13.1: feed, give, lease, lend, ...
  | contribute                   -- 13.2: administer, contribute, disburse, distribute, ...
  | futureHaving                 -- 13.3: advance, allocate, allot, assign, ...
  | fulfilling                   -- 13.4.1: credit, entrust, furnish, issue, ...
  | equip                        -- 13.4.2: arm, burden, charge, compensate, ...
  | get                          -- 13.5.1: book, buy, call, cash, ...
  | obtain                       -- 13.5.2: accept, accumulate, acquire, appropriate, ...
  | exchange                     -- 13.6: barter, change, exchange, substitute, ...
  | berry                        -- 13.7: antique, berry, birdnest, blackberry, ...
  -- Learn Verbs (§ 14)
  | learn                        -- 14: acquire, cram, glean, learn, ...
  -- Hold and Keep Verbs (§ 15)
  | hold                         -- 15.1: clasp, clutch, grasp, grip, ...
  | keep                         -- 15.2: hoard, keep, leave, store, ...
  -- Verbs of Concealment (§ 16)
  | conceal                      -- 16: block, cloister, conceal, curtain, ...
  -- Verbs of Throwing (§ 17)
  | throw                        -- 17.1: bash, bat, bunt, cast, ...
  | pelt                         -- 17.2: bombard, buffet, pelt, shower, ...
  -- Verbs of Contact by Impact (§ 18)
  | hit                          -- 18.1: bang, bash, batter, beat, ...
  | swat                         -- 18.2: bite, claw, paw, peck, ...
  | spank                        -- 18.3: belt, birch, bludgeon, bonk, ...
  | nonAgentiveImpact            -- 18.4: bang, brush, bump, crash, ...
  -- Poke Verbs (§ 19)
  | poke                         -- 19: dig, jab, pierce, poke, ...
  -- Verbs of Contact: Touch Verbs (§ 20)
  | touch                        -- 20: caress, graze, kiss, lick, ...
  -- Verbs of Cutting (§ 21)
  | cut                          -- 21.1: chip, clip, cut, hack, ...
  | carve                        -- 21.2: bore, bruise, carve, chip, ...
  -- Verbs of Combining and Attaching (§ 22)
  | mix                          -- 22.1: combine, commingle, concatenate, connect, ...
  | amalgamate                   -- 22.2: alternate, amalgamate, associate, coalesce, ...
  | shake                        -- 22.3: attach, baste, beat, bind, ...
  | tape                         -- 22.4: anchor, band, belt, bolt, ...
  | cling                        -- 22.5: adhere, cleave, cling, ...
  -- Verbs of Separating and Disassembling (§ 23)
  | separate                     -- 23.1: decouple, differentiate, disconnect, disentangle, ...
  | split                        -- 23.2: break, cut, draw, hack, ...
  | disassemble                  -- 23.3: detach, disassemble, disconnect, partition, ...
  | differ                       -- 23.4: differ, ...
  -- Verbs of Coloring (§ 24)
  | color                        -- 24: color, distemper, dye, enamel, ...
  -- Image Creation Verbs (§ 25)
  | imageImpression              -- 25.1: emboss, embroider, engrave, etch, ...
  | scribble                     -- 25.2: carve, chalk, charcoal, copy, ...
  | illustrate                   -- 25.3: address, adorn, autograph, brand, ...
  | transcribe                   -- 25.4: copy, film, forge, microfilm, ...
  -- Verbs of Creation and Transformation (§ 26)
  | build                        -- 26.1: arrange, assemble, bake, build, ...
  | grow                         -- 26.2: develop, evolve, grow, hatch, ...
  | prepare                      -- 26.3: bake, blend, brew, clean, ...
  | create                       -- 26.4: coin, compose, compute, concoct, ...
  | knead                        -- 26.5: beat, bend, coil, collect, ...
  | turn                         -- 26.6: alter, change, convert, metamorphose, ...
  | performance                  -- 26.7: chant, choreograph, compose, dance, ...
  -- Engender Verbs (§ 27)
  | engender                     -- 27: beget, cause, create, engender, ...
  -- Calve Verbs (§ 28)
  | calve                        -- 28: calve, cub, fawn, foal, ...
  -- Verbs with Predicative Complements (§ 29)
  | appoint                      -- 29.1: acknowledge, adopt, appoint, consider, ...
  | characterize                 -- 29.2: accept, address, appreciate, bill, ...
  | dub                          -- 29.3: anoint, baptize, brand, call, ...
  | declare                      -- 29.4: adjudge, adjudicate, assume, avow, ...
  | conjecture                   -- 29.5: admit, allow, assert, conjecture, ...
  | masquerade                   -- 29.6: act, behave, camouflage, count, ...
  | orphan                       -- 29.7: apprentice, canonize, cripple, cuckold, ...
  | captain                      -- 29.8: boss, bully, butcher, butler, ...
  -- Verbs of Perception (§ 30)
  | see                          -- 30.1: detect, discern, feel, hear, ...
  | sight                        -- 30.2: descry, discover, espy, examine, ...
  | peer                         -- 30.3: check, gape, gawk, gaze, ...
  | stimulusSubjectPerception    -- 30.4: feel, look, smell, sound, ...
  -- Psych-Verbs (Verbs of Psychological State) (§ 31)
  | amuse                        -- 31.1: abash, affect, afflict, affront, ...
  | admire                       -- 31.2: abhor, admire, adore, appreciate, ...
  | marvel                       -- 31.3: anguish, beware, care, cringe, ...
  | appeal                       -- 31.4: matter, ...
  -- Verbs of Desire (§ 32)
  | want                         -- 32.1: covet, crave, desire, fancy, ...
  | long                         -- 32.2: crave, fall, hanker, hope, ...
  -- Judgment Verbs (§ 33)
  | judgment                     -- 33: abuse, acclaim, applaud, backbite, ...
  -- Verbs of Assessment (§ 34)
  | assessment                   -- 34: analyze, assess, audit, evaluate, ...
  -- Verbs of Searching (§ 35)
  | hunt                         -- 35.1: dig, feel, fish, hunt, ...
  | search                       -- 35.2: advertise, check, comb, dive, ...
  | stalk                        -- 35.3: smell, stalk, taste, track, ...
  | investigate                  -- 35.4: canvass, examine, explore, frisk, ...
  | rummage                      -- 35.5: bore, burrow, delve, forage, ...
  | ferret                       -- 35.6: ferret, nose, seek, tease, ...
  -- Correspond Verbs (§ 36)
  | correspond                   -- 36.1: agree, argue, banter, bargain, ...
  | marry                        -- 36.2: court, cuddle, date, divorce, ...
  | meet                         -- 36.3: battle, box, consult, debate, ...
  -- Verbs of Communication (§ 37)
  | transferOfMessage            -- 37.1: ask, cite, demonstrate, dictate, ...
  | tell                         -- 37.2: tell, ...
  | mannerOfSpeaking             -- 37.3: babble, bark, bawl, bellow, ...
  | instrumentOfCommunication    -- 37.4: cable, e-mail, fax, modem, ...
  | talk                         -- 37.5: speak, talk, ...
  | chitchat                     -- 37.6: argue, chat, chatter, chitchat, ...
  | say                          -- 37.7: announce, articulate, blab, blurt, ...
  | complain                     -- 37.8: boast, brag, complain, crab, ...
  | advise                       -- 37.9: admonish, advise, alert, caution, ...
  -- Verbs of Sounds Made by Animals (§ 38)
  | animalSound                  -- 38: baa, bark, bay, bellow, ...
  -- Verbs of Ingesting (§ 39)
  | eat                          -- 39.1: drink, eat, ...
  | chew                         -- 39.2: chew, chomp, crunch, gnaw, ...
  | gobble                       -- 39.3: bolt, gobble, gulp, guzzle, ...
  | devour                       -- 39.4: consume, devour, imbibe, ingest, ...
  | dine                         -- 39.5: banquet, breakfast, luncheon, nosh, ...
  | gorge                        -- 39.6: exist, feed, flourish, gorge, ...
  | feed                         -- 39.7: bottlefeed, breastfeed, feed, forcefeed, ...
  -- Verbs Involving the Body (§ 40)
  | hiccup                       -- 40.1.1: belch, blush, burp, flush, ...
  | breathe                      -- 40.1.2: bleed, breathe, cough, cry, ...
  | exhale                       -- 40.1.3: exhale, inhale, perspire, ...
  | nonverbalExpression          -- 40.2: beam, cackle, chortle, chuckle, ...
  | wink                         -- 40.3.1: blink, clap, nod, point, ...
  | crane                        -- 40.3.2: bare, bat, beat, blow, ...
  | curtsey                      -- 40.3.3: bob, bow, curtsey, genuflect, ...
  | snooze                       -- 40.4: catnap, doze, drowse, nap, ...
  | flinch                       -- 40.5: balk, cower, cringe, flinch, ...
  | bodyInternalStateOfExistence -- 40.6: convulse, cower, quake, quiver, ...
  | suffocate                    -- 40.7: asphyxiate, choke, drown, stifle, ...
  | pain                         -- 40.8.1: ache, bother, hurt, itch, ...
  | tingle                       -- 40.8.2: burn, hum, prickle, pucker, ...
  | hurt                         -- 40.8.3: back, bark, bite, break, ...
  | changeOfBodilyState          -- 40.8.4: blanch, faint, sicken, ...
  -- Verbs of Grooming and Bodily Care (§ 41)
  | dress                        -- 41.1.1: bathe, change, disrobe, dress, ...
  | groom                        -- 41.1.2: curry, groom, ...
  | floss                        -- 41.2.1: brush, floss, ...
  | braid                        -- 41.2.2: bob, braid, brush, clip, ...
  | simpleDressing               -- 41.3.1: doff, don, wear, ...
  | dressingWell                 -- 41.3.2: doll, dress, spruce, ...
  | beingDressed                 -- 41.3.3: attire, clad, garb, robe, ...
  -- Verbs of Killing (§ 42)
  | murder                       -- 42.1: assassinate, butcher, dispatch, eliminate, ...
  | poison                       -- 42.2: asphyxiate, crucify, drown, electrocute, ...
  -- Verbs of Emission (§ 43)
  | lightEmission                -- 43.1: beam, blaze, blink, burn, ...
  | soundEmission                -- 43.2: babble, bang, beat, beep, ...
  | smellEmission                -- 43.3: reek, smell, stink, ...
  | substanceEmission            -- 43.4: belch, bleed, bubble, dribble, ...
  -- Destroy Verbs (§ 44)
  | destroy                      -- 44: annihilate, blitz, decimate, demolish, ...
  -- Verbs of Change of State (§ 45)
  | break_                       -- 45.1: break, chip, crack, crash, ...
  | bend                         -- 45.2: bend, crease, crinkle, crumple, ...
  | cooking                      -- 45.3: bake, barbecue, blanch, boil, ...
  | otherChangeOfState           -- 45.4: abate, accelerate, acetify, acidify, ...
  | entitySpecificChangeOfState  -- 45.5: blister, bloom, blossom, burn, ...
  | calibratableChangeOfState    -- 45.6: appreciate, balloon, climb, decline, ...
  -- Lodge Verbs (§ 46)
  | lodge                        -- 46: bivouac, board, camp, dwell, ...
  -- Verbs of Existence (§ 47)
  | exist                        -- 47.1: coexist, correspond, depend, dwell, ...
  | entitySpecificModeOfBeing    -- 47.2: billow, bloom, blossom, blow, ...
  | modeOfBeingInvolvingMotion   -- 47.3: bob, bow, creep, dance, ...
  | soundExistence               -- 47.4: din, echo, resonate, resound, ...
  | swarm                        -- 47.5.1: abound, bustle, crawl, creep, ...
  | herd                         -- 47.5.2: accumulate, aggregate, amass, assemble, ...
  | bulge                        -- 47.5.3: bristle, bulge, seethe, ...
  | spatialConfiguration         -- 47.6: bend, bow, crouch, dangle, ...
  | meander                      -- 47.7: cascade, climb, crawl, cut, ...
  | contiguousLocation           -- 47.8: abut, adjoin, blanket, border, ...
  -- Verbs of Appearance, Disappearance, (§ 48)
  | appear                       -- 48.1.1: appear, arise, awake, awaken, ...
  | reflexiveAppearance          -- 48.1.2: assert, declare, define, express, ...
  | disappearance                -- 48.2: die, disappear, expire, lapse, ...
  | occurrence                   -- 48.3: ensue, eventuate, happen, occur, ...
  -- Verbs of Body-Internal Motion (§ 49)
  | bodyInternalMotion           -- 49: buck, fidget, flap, gyrate, ...
  -- Verbs of Assuming a Position (§ 50)
  | assumePosition               -- 50: bend, bow, crouch, flop, ...
  -- Verbs of Motion (§ 51)
  | inherentlyDirectedMotion     -- 51.1: advance, arrive, ascend, climb, ...
  | leave                        -- 51.2: abandon, desert, leave, ...
  | roll                         -- 51.3.1: bounce, coil, drift, drop, ...
  | run                          -- 51.3.2: amble, backpack, bolt, bounce, ...
  | vehicleName                  -- 51.4.1: balloon, bicycle, bike, boat, ...
  | nonVehicleName               -- 51.4.2: cruise, drive, fly, oar, ...
  | waltz                        -- 51.5: boogie, bop, cancan, clog, ...
  | chase                        -- 51.6: chase, follow, pursue, shadow, ...
  | accompany                    -- 51.7: accompany, conduct, escort, guide, ...
  -- Avoid Verbs (§ 52)
  | avoid                        -- 52: avoid, boycott, dodge, duck, ...
  -- Verbs of Lingering and Rushing (§ 53)
  | linger                       -- 53.1: dally, dawdle, delay, dither, ...
  | rush                         -- 53.2: hasten, hurry, rush, ...
  -- Measure Verbs (§ 54)
  | register                     -- 54.1: measure, read, register, total, ...
  | cost                         -- 54.2: carry, cost, last, take, ...
  | fit                          -- 54.3: carry, contain, feed, fit, ...
  | price                        -- 54.4: appraise, assess, estimate, fix, ...
  | bill                         -- 54.5: bet, bill, charge, fine, ...
  -- Aspectual Verbs (§ 55)
  | begin                        -- 55.1: begin, cease, commence, continue, ...
  | complete                     -- 55.2: complete, discontinue, initiate, quit, ...
  -- Weekend Verbs (§ 56)
  | weekend                      -- 56: summer, vacation, weekend, ...
  -- Weather Verbs (§ 57)
  | weather                      -- 57: blow, clear, drizzle, fog, ...
  deriving DecidableEq, Repr, Fintype

namespace LevinClass

/-- The section number as the book prints it. -/
def numberString : LevinClass → String
  | .put => "9.1"
  | .putInSpatialConfiguration => "9.2"
  | .funnel => "9.3"
  | .putDirection => "9.4"
  | .pour => "9.5"
  | .coil => "9.6"
  | .sprayLoad => "9.7"
  | .fill => "9.8"
  | .butter => "9.9"
  | .pocket => "9.10"
  | .remove => "10.1"
  | .banish => "10.2"
  | .clear => "10.3"
  | .wipeManner => "10.4.1"
  | .wipeInstrument => "10.4.2"
  | .steal => "10.5"
  | .cheat => "10.6"
  | .pit => "10.7"
  | .debone => "10.8"
  | .mine => "10.9"
  | .send => "11.1"
  | .slide => "11.2"
  | .bringTake => "11.3"
  | .carry => "11.4"
  | .drive => "11.5"
  | .pushPull => "12"
  | .give => "13.1"
  | .contribute => "13.2"
  | .futureHaving => "13.3"
  | .fulfilling => "13.4.1"
  | .equip => "13.4.2"
  | .get => "13.5.1"
  | .obtain => "13.5.2"
  | .exchange => "13.6"
  | .berry => "13.7"
  | .learn => "14"
  | .hold => "15.1"
  | .keep => "15.2"
  | .conceal => "16"
  | .throw => "17.1"
  | .pelt => "17.2"
  | .hit => "18.1"
  | .swat => "18.2"
  | .spank => "18.3"
  | .nonAgentiveImpact => "18.4"
  | .poke => "19"
  | .touch => "20"
  | .cut => "21.1"
  | .carve => "21.2"
  | .mix => "22.1"
  | .amalgamate => "22.2"
  | .shake => "22.3"
  | .tape => "22.4"
  | .cling => "22.5"
  | .separate => "23.1"
  | .split => "23.2"
  | .disassemble => "23.3"
  | .differ => "23.4"
  | .color => "24"
  | .imageImpression => "25.1"
  | .scribble => "25.2"
  | .illustrate => "25.3"
  | .transcribe => "25.4"
  | .build => "26.1"
  | .grow => "26.2"
  | .prepare => "26.3"
  | .create => "26.4"
  | .knead => "26.5"
  | .turn => "26.6"
  | .performance => "26.7"
  | .engender => "27"
  | .calve => "28"
  | .appoint => "29.1"
  | .characterize => "29.2"
  | .dub => "29.3"
  | .declare => "29.4"
  | .conjecture => "29.5"
  | .masquerade => "29.6"
  | .orphan => "29.7"
  | .captain => "29.8"
  | .see => "30.1"
  | .sight => "30.2"
  | .peer => "30.3"
  | .stimulusSubjectPerception => "30.4"
  | .amuse => "31.1"
  | .admire => "31.2"
  | .marvel => "31.3"
  | .appeal => "31.4"
  | .want => "32.1"
  | .long => "32.2"
  | .judgment => "33"
  | .assessment => "34"
  | .hunt => "35.1"
  | .search => "35.2"
  | .stalk => "35.3"
  | .investigate => "35.4"
  | .rummage => "35.5"
  | .ferret => "35.6"
  | .correspond => "36.1"
  | .marry => "36.2"
  | .meet => "36.3"
  | .transferOfMessage => "37.1"
  | .tell => "37.2"
  | .mannerOfSpeaking => "37.3"
  | .instrumentOfCommunication => "37.4"
  | .talk => "37.5"
  | .chitchat => "37.6"
  | .say => "37.7"
  | .complain => "37.8"
  | .advise => "37.9"
  | .animalSound => "38"
  | .eat => "39.1"
  | .chew => "39.2"
  | .gobble => "39.3"
  | .devour => "39.4"
  | .dine => "39.5"
  | .gorge => "39.6"
  | .feed => "39.7"
  | .hiccup => "40.1.1"
  | .breathe => "40.1.2"
  | .exhale => "40.1.3"
  | .nonverbalExpression => "40.2"
  | .wink => "40.3.1"
  | .crane => "40.3.2"
  | .curtsey => "40.3.3"
  | .snooze => "40.4"
  | .flinch => "40.5"
  | .bodyInternalStateOfExistence => "40.6"
  | .suffocate => "40.7"
  | .pain => "40.8.1"
  | .tingle => "40.8.2"
  | .hurt => "40.8.3"
  | .changeOfBodilyState => "40.8.4"
  | .dress => "41.1.1"
  | .groom => "41.1.2"
  | .floss => "41.2.1"
  | .braid => "41.2.2"
  | .simpleDressing => "41.3.1"
  | .dressingWell => "41.3.2"
  | .beingDressed => "41.3.3"
  | .murder => "42.1"
  | .poison => "42.2"
  | .lightEmission => "43.1"
  | .soundEmission => "43.2"
  | .smellEmission => "43.3"
  | .substanceEmission => "43.4"
  | .destroy => "44"
  | .break_ => "45.1"
  | .bend => "45.2"
  | .cooking => "45.3"
  | .otherChangeOfState => "45.4"
  | .entitySpecificChangeOfState => "45.5"
  | .calibratableChangeOfState => "45.6"
  | .lodge => "46"
  | .exist => "47.1"
  | .entitySpecificModeOfBeing => "47.2"
  | .modeOfBeingInvolvingMotion => "47.3"
  | .soundExistence => "47.4"
  | .swarm => "47.5.1"
  | .herd => "47.5.2"
  | .bulge => "47.5.3"
  | .spatialConfiguration => "47.6"
  | .meander => "47.7"
  | .contiguousLocation => "47.8"
  | .appear => "48.1.1"
  | .reflexiveAppearance => "48.1.2"
  | .disappearance => "48.2"
  | .occurrence => "48.3"
  | .bodyInternalMotion => "49"
  | .assumePosition => "50"
  | .inherentlyDirectedMotion => "51.1"
  | .leave => "51.2"
  | .roll => "51.3.1"
  | .run => "51.3.2"
  | .vehicleName => "51.4.1"
  | .nonVehicleName => "51.4.2"
  | .waltz => "51.5"
  | .chase => "51.6"
  | .accompany => "51.7"
  | .avoid => "52"
  | .linger => "53.1"
  | .rush => "53.2"
  | .register => "54.1"
  | .cost => "54.2"
  | .fit => "54.3"
  | .price => "54.4"
  | .bill => "54.5"
  | .begin => "55.1"
  | .complete => "55.2"
  | .weekend => "56"
  | .weather => "57"

/-- The class whose section number the book prints as `s`, the inverse of `numberString`. -/
def ofNumberString? (s : String) : Option LevinClass :=
  LevinClass.enumList.find? (·.numberString = s)

/-- Levin's title of the class. -/
def name : LevinClass → String
  | .put => "Put Verbs"
  | .putInSpatialConfiguration => "Verbs of Putting in a Spatial Configuration"
  | .funnel => "Funnel Verbs"
  | .putDirection => "Verbs of Putting with a Specified Direction"
  | .pour => "Pour Verbs"
  | .coil => "Coil Verbs"
  | .sprayLoad => "Spray/Load Verbs"
  | .fill => "Fill Verbs"
  | .butter => "Butter Verbs"
  | .pocket => "Pocket Verbs"
  | .remove => "Remove Verbs"
  | .banish => "Banish Verbs"
  | .clear => "Clear Verbs"
  | .wipeManner => "Manner Subclass"
  | .wipeInstrument => "Instrument Subclass"
  | .steal => "Verbs of Possessional Deprivation: Steal Verbs"
  | .cheat => "Verbs of Possessional Deprivation: Cheat Verbs"
  | .pit => "Pit Verbs"
  | .debone => "Debone Verbs"
  | .mine => "Mine Verbs"
  | .send => "Send Verbs"
  | .slide => "Slide Verbs"
  | .bringTake => "Bring and Take"
  | .carry => "Carry Verbs"
  | .drive => "Drive Verbs"
  | .pushPull => "Verbs of Exerting Force: Push/Pull Verbs"
  | .give => "Give Verbs"
  | .contribute => "Contribute Verbs"
  | .futureHaving => "Verbs of Future Having"
  | .fulfilling => "Verbs of Fulfilling"
  | .equip => "Equip Verbs"
  | .get => "Get Verbs"
  | .obtain => "Obtain Verbs"
  | .exchange => "Verbs of Exchange"
  | .berry => "Berry Verbs"
  | .learn => "Learn Verbs"
  | .hold => "Hold Verbs"
  | .keep => "Keep Verbs"
  | .conceal => "Verbs of Concealment"
  | .throw => "Throw Verbs"
  | .pelt => "Pelt Verbs"
  | .hit => "Hit Verbs"
  | .swat => "Swat Verbs"
  | .spank => "Spank Verbs"
  | .nonAgentiveImpact => "Non-Agentive Verbs of Impact by Contact"
  | .poke => "Poke Verbs"
  | .touch => "Verbs of Contact: Touch Verbs"
  | .cut => "Cut Verbs"
  | .carve => "Carve Verbs"
  | .mix => "Mix Verbs"
  | .amalgamate => "Amalgamate Verbs"
  | .shake => "Shake Verbs"
  | .tape => "Tape Verbs"
  | .cling => "Cling Verbs"
  | .separate => "Separate Verbs"
  | .split => "Split Verbs"
  | .disassemble => "Disassemble Verbs"
  | .differ => "Differ Verbs"
  | .color => "Verbs of Coloring"
  | .imageImpression => "Verbs of Image Impression"
  | .scribble => "Scribble Verbs"
  | .illustrate => "Illustrate Verbs"
  | .transcribe => "Transcribe Verbs"
  | .build => "Build Verbs"
  | .grow => "Grow Verbs"
  | .prepare => "Verbs of Preparing"
  | .create => "Create Verbs"
  | .knead => "Knead Verbs"
  | .turn => "Turn Verbs"
  | .performance => "Performance Verbs"
  | .engender => "Engender Verbs"
  | .calve => "Calve Verbs"
  | .appoint => "Appoint Verbs"
  | .characterize => "Characterize Verbs"
  | .dub => "Dub Verbs"
  | .declare => "Declare Verbs"
  | .conjecture => "Conjecture Verbs"
  | .masquerade => "Masquerade Verbs"
  | .orphan => "Orphan Verbs"
  | .captain => "Captain Verbs"
  | .see => "See Verbs"
  | .sight => "Sight Verbs"
  | .peer => "Peer Verbs"
  | .stimulusSubjectPerception => "Stimulus Subject Perception Verbs"
  | .amuse => "Amuse Verbs"
  | .admire => "Admire Verbs"
  | .marvel => "Marvel Verbs"
  | .appeal => "Appeal Verbs"
  | .want => "Want Verbs"
  | .long => "Long Verbs"
  | .judgment => "Judgment Verbs"
  | .assessment => "Verbs of Assessment"
  | .hunt => "Hunt Verbs"
  | .search => "Search Verbs"
  | .stalk => "Stalk Verbs"
  | .investigate => "Investigate Verbs"
  | .rummage => "Rummage Verbs"
  | .ferret => "Ferret Verbs"
  | .correspond => "Correspond Verbs"
  | .marry => "Marry Verbs"
  | .meet => "Meet Verbs"
  | .transferOfMessage => "Verbs of Transfer of a Message"
  | .tell => "Tell"
  | .mannerOfSpeaking => "Verbs of Manner of Speaking"
  | .instrumentOfCommunication => "Verbs of Instrument of Communication"
  | .talk => "Talk Verbs"
  | .chitchat => "Chitchat Verbs"
  | .say => "Say Verbs"
  | .complain => "Complain Verbs"
  | .advise => "Advise Verbs"
  | .animalSound => "Verbs of Sounds Made by Animals"
  | .eat => "Eat Verbs"
  | .chew => "Chew Verbs"
  | .gobble => "Gobble Verbs"
  | .devour => "Devour Verbs"
  | .dine => "Dine Verbs"
  | .gorge => "Gorge Verbs"
  | .feed => "Verbs of Feeding"
  | .hiccup => "Hiccup Verbs"
  | .breathe => "Breathe Verbs"
  | .exhale => "Exhale Verbs"
  | .nonverbalExpression => "Verbs of Nonverbal Expression"
  | .wink => "Wink Verbs"
  | .crane => "Crane Verbs"
  | .curtsey => "Curtsey Verbs"
  | .snooze => "Snooze Verbs"
  | .flinch => "Flinch Verbs"
  | .bodyInternalStateOfExistence => "Verbs of Body-Internal States of Existence"
  | .suffocate => "Suffocate Verbs"
  | .pain => "Pain Verbs"
  | .tingle => "Tingle Verbs"
  | .hurt => "Hurt Verbs"
  | .changeOfBodilyState => "Verbs of Change of Bodily State"
  | .dress => "Dress Verbs"
  | .groom => "Groom Verbs"
  | .floss => "Floss Verbs"
  | .braid => "Braid Verbs"
  | .simpleDressing => "Simple Verbs of Dressing"
  | .dressingWell => "Verbs of Dressing Well"
  | .beingDressed => "Verbs of Being Dressed"
  | .murder => "Murder Verbs"
  | .poison => "Poison Verbs"
  | .lightEmission => "Verbs of Light Emission"
  | .soundEmission => "Verbs of Sound Emission"
  | .smellEmission => "Verbs of Smell Emission"
  | .substanceEmission => "Verbs of Substance Emission"
  | .destroy => "Destroy Verbs"
  | .break_ => "Break Verbs"
  | .bend => "Bend Verbs"
  | .cooking => "Cooking Verbs"
  | .otherChangeOfState => "Other Alternating Verbs of Change of State"
  | .entitySpecificChangeOfState => "Verbs of Entity-Specific Change of State"
  | .calibratableChangeOfState => "Verbs of Calibratable Changes of State"
  | .lodge => "Lodge Verbs"
  | .exist => "Exist Verbs"
  | .entitySpecificModeOfBeing => "Verbs of Entity-Specific Modes of Being"
  | .modeOfBeingInvolvingMotion => "Verbs of Modes of Being Involving Motion"
  | .soundExistence => "Verbs of Sound Existence"
  | .swarm => "Swarm Verbs"
  | .herd => "Herd Verbs"
  | .bulge => "Bulge Verbs"
  | .spatialConfiguration => "Verbs of Spatial Configuration"
  | .meander => "Meander Verbs"
  | .contiguousLocation => "Verbs of Contiguous Location"
  | .appear => "Appear Verbs"
  | .reflexiveAppearance => "Reflexive Verbs of Appearance"
  | .disappearance => "Verbs of Disappearance"
  | .occurrence => "Verbs of Occurrence"
  | .bodyInternalMotion => "Verbs of Body-Internal Motion"
  | .assumePosition => "Verbs of Assuming a Position"
  | .inherentlyDirectedMotion => "Verbs of Inherently Directed Motion"
  | .leave => "Leave Verbs"
  | .roll => "Roll Verbs"
  | .run => "Run Verbs"
  | .vehicleName => "Verbs That Are Vehicle Names"
  | .nonVehicleName => "Verbs That Are Not Vehicle Names"
  | .waltz => "Waltz Verbs"
  | .chase => "Chase Verbs"
  | .accompany => "Accompany Verbs"
  | .avoid => "Avoid Verbs"
  | .linger => "Verbs of Lingering"
  | .rush => "Verbs of Rushing"
  | .register => "Register Verbs"
  | .cost => "Cost Verbs"
  | .fit => "Fit Verbs"
  | .price => "Price Verbs"
  | .bill => "Bill Verbs"
  | .begin => "Begin Verbs"
  | .complete => "Complete Verbs"
  | .weekend => "Weekend Verbs"
  | .weather => "Weather Verbs"

end LevinClass

/-! ### Templates

Each class realizes an argument-structure template, a `RoleList`, from which `Verb.Basic` derives
a verb entry's default argument profiles; classes whose template has not been determined map to
`none`. -/

/-- The argument-structure template a class realizes, `none` where it has not been
determined. -/
def LevinClass.roleList : LevinClass → Option RoleList
  -- § 18: Contact by Impact — manner verbs, no CoS entailment
  | .hit | .swat | .spank      => some mannerContact
  -- § 20: Contact: Touch — like hit but lighter force
  | .touch                    => some mannerContact
  -- § 21: Cutting — manner + result (CoS entailed)
  | .cut | .carve             => some resultChange
  -- § 44: Destroy
  | .destroy                  => some resultChange
  -- § 42: Killing
  | .murder | .poison         => some resultChange
  -- § 45: Change of State (causative/inchoative alternation)
  | .break_ | .bend | .cooking
  | .otherChangeOfState | .entitySpecificChangeOfState
  | .calibratableChangeOfState          => some resultChange
  -- § 26: Creation and Transformation
  | .build | .create | .knead => some creation
  | .grow                     => some creation
  -- § 25: Image Creation
  | .imageImpression | .scribble | .illustrate | .transcribe            => some creation
  -- § 39: Ingesting
  | .eat | .devour            => some consumption
  -- § 51.3: Manner of Motion
  | .roll                     => some nonagentiveMotion
  | .run                      => some selfMotion
  -- § 51.6: Chase
  | .chase                    => some selfMotion
  -- § 51.1: Inherently Directed Motion
  | .inherentlyDirectedMotion => some directedMotion
  -- § 30: Perception
  | .see | .sight             => some perception
  -- § 31.1: Amuse-class psych verbs (stimulus subject)
  | .amuse                    => some psychCausal
  -- § 31.2: Admire-class psych verbs (experiencer subject)
  | .admire                   => some psychState
  -- § 32.1: Want verbs (desire states)
  | .want | .long              => some desire
  -- § 13.1 / § 13.5: Change of possession (give / obtain)
  | .give | .get | .obtain        => some possessionTransfer
  -- § 10.4: Wipe verbs (manner-subclass default; instrument-sense
  -- entries override with `wipeInstrument` per verb)
  | .wipeManner | .wipeInstrument                     => some ArgumentStructure.wipeManner
  -- § 48.2: Disappearance
  | .disappearance            => some ArgumentStructure.disappearance
  -- Not yet classified
  | _                         => none

/-! ### Profiles -/

/-- The entailment profile of the subject in a class's template. -/
def LevinClass.subjectProfile (c : LevinClass) : Option EntailmentProfile :=
  c.roleList.map (·.subjectProfile)

/-- The entailment profile of the object in a class's template, if it has one. -/
def LevinClass.objectProfile (c : LevinClass) : Option EntailmentProfile :=
  c.roleList.bind (·.objectProfile)

/-- Two votes on a profile combine by agreement, where `none` abstains and `some none` records a
disagreement. -/
def agree :
    Option (Option EntailmentProfile) → Option (Option EntailmentProfile) →
      Option (Option EntailmentProfile)
  | none, b => b
  | a, none => a
  | some x, some y => if x = y then some x else some none

instance : Std.Commutative agree :=
  ⟨fun a b ↦ by
    rcases a with _ | a <;> rcases b with _ | b <;> simp [agree]; split_ifs <;> simp_all⟩

instance : Std.Associative agree :=
  ⟨fun a b c ↦ by
    rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;> simp [agree] <;>
      split_ifs <;> simp_all⟩

/-- The profile the classes assigning one agree on, `none` when none does or they disagree. -/
def LevinClass.commonProfile (f : LevinClass → Option EntailmentProfile)
    (s : Finset LevinClass) : Option EntailmentProfile :=
  (s.fold agree none fun c ↦ (f c).map some).bind id

@[simp] theorem LevinClass.commonProfile_empty (f : LevinClass → Option EntailmentProfile) :
    LevinClass.commonProfile f ∅ = none :=
  rfl

/-- In no class's template does the object outrank the subject under [dowty-1991]'s Argument
    Selection Principle, as [levin-rappaport-hovav-2005] present it. Where dominance is strict
    the principle derives the stored linking; at the psych doublets *like* and *please*
    (`Dowty1991.psychStative_alternation`) neither argument outranks the other, and the linking is
    a lexical choice the template underdetermines. -/
theorem roleList_not_asp_reversed {c : LevinClass} {r : RoleList}
    {o : EntailmentProfile} (hr : c.roleList = some r)
    (ho : r.objectProfile = some o) :
    ¬ OutranksForSubject o r.subjectProfile := by
  cases c <;> cases hr <;> cases ho <;> decide

end ArgumentStructure
