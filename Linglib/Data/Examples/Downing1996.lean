module

public import Linglib.Data.Examples.Schema

/-!
# `Downing1996` — typed example data

Auto-generated from `Linglib/Data/Examples/Downing1996.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Downing1996.Examples`.
-/

@[expose] public section

namespace Downing1996.Examples

def ex_1_14 : Datum :=
  { id := "downing1996_1_14"
    source := ⟨"downing-1996", "(14), Chapter 1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ik-ken-no mise-ga hiraite-ita node, hairu koto-ni shita."
    glossedTokens := [("Ik-ken-no", "one-building-ATT"), ("mise-ga", "shop-NOM"), ("hiraite-ita", "was.open"), ("node", "since"), ("hairu", "enter"), ("koto-ni", "NMLZ-DAT"), ("shita", "did")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("classifier", "kenBuilding"), ("criterion", "cooccursWithNoun")] }

def ex_1_15 : Datum :=
  { id := "downing1996_1_15"
    source := ⟨"downing-1996", "(15), Chapter 1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mik-ka tatte"
    glossedTokens := [("mik-ka", "three-day"), ("tatte", "passing")]
    context := ""
    judgment := .acceptable
    alternatives := [("hi-ga mik-ka tatte", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "1"), ("criterion", "cooccursWithNoun")] }

def ex_3_2a : Datum :=
  { id := "downing1996_3_2a"
    source := ⟨"downing-1996", "(2a), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ni-rooru-o sono hikidashi-ni irete kudasai."
    glossedTokens := [("Ni-rooru-o", "2-roll-ACC"), ("sono", "that"), ("hikidashi-ni", "drawer-LOC"), ("irete", "put"), ("kudasai", "please")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "3"), ("trait", "withoutNoun")] }

def ex_3_2b : Datum :=
  { id := "downing1996_3_2b"
    source := ⟨"downing-1996", "(2b), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ashi-no ura-to kutsu-no aida-ni hito-tsubu-mo hairu-to aruku koto-ga kurushiku naru."
    glossedTokens := [("Ashi-no", "foot-GEN"), ("ura-to", "other.side-COM"), ("kutsu-no", "shoe-GEN"), ("aida-ni", "space-LOC"), ("hito-tsubu-mo", "1-small.grainlike.object-even"), ("hairu-to", "enter-and"), ("aruku", "walk"), ("koto-ga", "NMLZ-NOM"), ("kurushiku", "painful"), ("naru", "become")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "3"), ("classifier", "tsubu"), ("trait", "withoutNoun")] }

def ex_3_3 : Datum :=
  { id := "downing1996_3_3"
    source := ⟨"downing-1996", "(3), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono ori-no naka-ni hebi-ga san-biki mieru."
    glossedTokens := [("Kono", "this"), ("ori-no", "cage-GEN"), ("naka-ni", "inside-LOC"), ("hebi-ga", "snake-NOM"), ("san-biki", "3-animal"), ("mieru", "can.be.seen")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kono ori-no naka-ni hebi-ga san-bon mieru.", .ungrammatical), ("Kono ori-no naka-ni hebi-ga mi-suji mieru.", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "3"), ("classifier", "hiki"), ("trait", "alternation")] }

def ex_3_4 : Datum :=
  { id := "downing1996_3_4"
    source := ⟨"downing-1996", "(4), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Dewa, ringo san-ko-to banana ni-hon-de-wa doo ka, to iu to, ichi-nensei-wa magotsuku. Zenbu-de itsu-tsu da."
    glossedTokens := [("ringo", "apple"), ("san-ko-to", "3-small.3-D.object-COM"), ("banana", "banana"), ("ni-hon-de-wa", "2-long.slender.object-COP-CONTR"), ("ichi-nensei-wa", "first-grader-TOP"), ("magotsuku", "be.confused"), ("Zenbu-de", "together"), ("itsu-tsu", "5-inanimate"), ("da", "COP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "3"), ("classifier", "tsu"), ("trait", "alternation")] }

def ex_3_5a : Datum :=
  { id := "downing1996_3_5a"
    source := ⟨"downing-1996", "(5a), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Boku-wa inu-to futari-de sanpo shi-nagara ..."
    glossedTokens := [("Boku-wa", "I-TOP"), ("inu-to", "dog-COM"), ("futari-de", "2.person-INST"), ("sanpo", "walk"), ("shi-nagara", "do-while")]
    context := ""
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "3"), ("classifier", "nin"), ("trait", "alternation")] }

def ex_3_33 : Datum :=
  { id := "downing1996_3_33"
    source := ⟨"downing-1996", "(33), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "denwa ichi-dai"
    glossedTokens := [("denwa", "telephone"), ("ichi-dai", "1-furniture.vehicle.or.machine")]
    context := ""
    judgment := .acceptable
    alternatives := [("denwa it-tsuu", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "3"), ("cohesion", "kind"), ("function", "disambiguation")] }

def ex_3_35 : Datum :=
  { id := "downing1996_3_35"
    source := ⟨"downing-1996", "(35), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "budoo hito-tsubu"
    glossedTokens := [("budoo", "grape"), ("hito-tsubu", "1-small.grainlike.object")]
    context := ""
    judgment := .acceptable
    alternatives := [("budoo ik-ko", .acceptable), ("budoo hito-fusa", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "3"), ("cohesion", "quality"), ("function", "disambiguation")] }

def ex_3_36 : Datum :=
  { id := "downing1996_3_36"
    source := ⟨"downing-1996", "(36), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ume ip-pon"
    glossedTokens := [("ume", "plum"), ("ip-pon", "1-long.slender.object")]
    context := ""
    judgment := .acceptable
    alternatives := [("ume ik-ko", .acceptable), ("ume ichi-rin", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "3"), ("cohesion", "quality"), ("function", "disambiguation")] }

def ex_3_37a : Datum :=
  { id := "downing1996_3_37a"
    source := ⟨"downing-1996", "(37a), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hoosu-no saki-o yubi-de tsubusu-to, mizu-wa ni-hon-no kiri-ni natte ..."
    glossedTokens := [("Hoosu-no", "hose-GEN"), ("saki-o", "end-ACC"), ("yubi-de", "finger-INST"), ("tsubusu-to", "squeeze-and"), ("mizu-wa", "water-TOP"), ("ni-hon-no", "2-long.slender.object-ATT"), ("kiri-ni", "mist-DAT"), ("natte", "becoming")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "3"), ("classifier", "hon"), ("cohesion", "quality"), ("function", "addingInformation")] }

def ex_3_38 : Datum :=
  { id := "downing1996_3_38"
    source := ⟨"downing-1996", "(38), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mottomo igi aru kichoona nihon-no yuubin-kitte go-jut-ten-o hajimete gin-de saigen-shita shinseina fukusei-no korekushon"
    glossedTokens := [("nihon-no", "Japan-ATT"), ("yuubin-kitte", "postage.stamp"), ("go-jut-ten-o", "50-work.of.art-ACC"), ("hajimete", "first"), ("gin-de", "silver-INST"), ("saigen-shita", "re-issue-did")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "3"), ("classifier", "ten"), ("function", "addingInformation")] }

def ex_3_39 : Datum :=
  { id := "downing1996_3_39"
    source := ⟨"downing-1996", "(39), Chapter 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ashi yon-mai"
    glossedTokens := [("ashi", "foot"), ("yon-mai", "4-flat.thin.object")]
    context := "On a doll pattern."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "3"), ("classifier", "mai"), ("cohesion", "quality"), ("function", "addingInformation")] }

def ex_5_7 : Datum :=
  { id := "downing1996_5_7"
    source := ⟨"downing-1996", "(7), Chapter 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ni-wa-no hoo desu."
    glossedTokens := [("Ni-wa-no", "2-bird-ATT"), ("hoo", "side"), ("desu", "COP")]
    context := "Speaker A, offering a choice between two birds and two turtles: Hoshii-no-wa dochira desu ka? 'Which is it that you want?'"
    judgment := .ungrammatical
    alternatives := [("Tori-no hoo desu.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "5"), ("classifier", "wa"), ("function", "predication")] }

def ex_5_9 : Datum :=
  { id := "downing1996_5_9"
    source := ⟨"downing-1996", "(9), Chapter 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kitte ichi-shiito"
    glossedTokens := [("kitte", "stamp"), ("ichi-shiito", "one-sheet")]
    context := ""
    judgment := .acceptable
    alternatives := [("kitte ichi-mai", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "5"), ("function", "disambiguation")] }

def ex_6_2 : Datum :=
  { id := "downing1996_6_2"
    source := ⟨"downing-1996", "(2), Chapter 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ip-piki desu."
    glossedTokens := [("Ip-piki", "1-animal"), ("desu", "COP")]
    context := "A, continuing a conversation about goldfish: Nan-biki-gurai katte-iru no? 'How many are you raising?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("classifier", "hiki"), ("use", "predicate")] }

def ex_6_5 : Datum :=
  { id := "downing1996_6_5"
    source := ⟨"downing-1996", "(5), Chapter 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sono asa, komori-zawa-ni-wa, nana-hiki-no iwana-ga nobotte-ita. Jootaroo-zawa-ni-wa san-biki, ushiro-zawa-ni yon-hiki, koiwake-zawa-ni san-biki-ga ita."
    glossedTokens := [("nana-hiki-no", "7-animal-ATT"), ("iwana-ga", "bull.trout-NOM"), ("nobotte-ita", "risen-had"), ("san-biki", "3-animal"), ("yon-hiki", "4-animal"), ("san-biki-ga", "3-animal-NOM"), ("ita", "existed")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("classifier", "hiki"), ("use", "additionalMembers")] }

def ex_6_6 : Datum :=
  { id := "downing1996_6_6"
    source := ⟨"downing-1996", "(6), Chapter 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "... mae-ni futari suwattete sa, hitori-wa taaban-o maita indojin de sa, kore-ga unten shiteru. De, moo hitori-wa arabiajin da yo ne, futari-tomo ushiro-nanka minai-n da yo."
    glossedTokens := [("mae-ni", "front-LOC"), ("futari", "2.person"), ("suwattete", "were.sitting"), ("hitori-wa", "1.person-CONTR"), ("indojin", "Indian"), ("moo", "other"), ("hitori-wa", "1.person-TOP"), ("arabiajin", "Arab"), ("futari-tomo", "2.person-both")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("classifier", "nin"), ("use", "subsets")] }

def ex_6_9 : Datum :=
  { id := "downing1996_6_9"
    source := ⟨"downing-1996", "(9), Chapter 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Shuuichi-wa Shingo-no musuko da keredomo, Kikuko-ga kono-yoo-ni-shite-made Shuuichi-to musubarete inakereba naranai hodo, futari-wa risoo-no fuufu na-no ka, Shingo-wa utagai dasu to kagiri-ga nakatta."
    glossedTokens := [("Shuuichi-wa", "Shuichi-TOP"), ("Shingo-no", "Shingo-GEN"), ("musuko", "son"), ("futari-wa", "2.person-TOP"), ("risoo-no", "ideal-ATT"), ("fuufu", "couple")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("classifier", "nin"), ("use", "anaphoric")] }

def ex_6_13 : Datum :=
  { id := "downing1996_6_13"
    source := ⟨"downing-1996", "(13), Chapter 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mukashi-mukashi, soko-ni hitori-no ryooshi-ga arimashita."
    glossedTokens := [("Mukashi-mukashi", "long.ago-long.ago"), ("soko-ni", "there-LOC"), ("hitori-no", "1.person-ATT"), ("ryooshi-ga", "fisherman-NOM"), ("arimashita", "existed")]
    context := "The beginning of a folk tale, after the island Kikaigashima has been introduced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("classifier", "nin"), ("construction", "preNominal"), ("use", "introduction")] }

def ex_6_20 : Datum :=
  { id := "downing1996_6_20"
    source := ⟨"downing-1996", "(20), Chapter 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yasuko-no imooto-no omokage-wa, futari-no kokoro-no soko-ni atta wake da."
    glossedTokens := [("Yasuko-no", "Yasuko-GEN"), ("imooto-no", "younger.sister-GEN"), ("omokage-wa", "image-TOP"), ("futari-no", "2.person-GEN"), ("kokoro-no", "heart-GEN"), ("soko-ni", "bottom-LOC"), ("atta", "existed")]
    context := "Of the couple Yasuko and Shingo."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("classifier", "nin"), ("use", "anaphoric")] }

def ex_7_2b : Datum :=
  { id := "downing1996_7_2b"
    source := ⟨"downing-1996", "(2b), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ojisan-to, sono futari-no otoko-no ko-tachi-to kaeko-to kotatsu-ni atatte-imashita."
    glossedTokens := [("Ojisan-to", "uncle-COM"), ("sono", "that"), ("futari-no", "2.person-ATT"), ("otoko-no", "male-ATT"), ("ko-tachi-to", "child-PL-COM"), ("kaeko-to", "Kaeko-COM"), ("kotatsu-ni", "heated.table-LOC"), ("atatte-imashita", "warming-were")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "7"), ("classifier", "nin"), ("number", "classifierAndPlural")] }

def ex_7_3 : Datum :=
  { id := "downing1996_7_3"
    source := ⟨"downing-1996", "(3), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takai hana-to aoi iro-no me-o motta ningyoo-wa ichi-nichi-juu nazo-no yoona bishoo-o ukabete-iru."
    glossedTokens := [("Takai", "long"), ("hana-to", "nose-COM"), ("aoi", "blue"), ("iro-no", "color-ATT"), ("me-o", "eye-ACC"), ("motta", "had"), ("ningyoo-wa", "mannequin-TOP"), ("ichi-nichi-juu", "all.day.long")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "7"), ("number", "transnumeral")] }

def ex_7_4 : Datum :=
  { id := "downing1996_7_4"
    source := ⟨"downing-1996", "(4), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sono ashi-ni-wa yubi-ga rop-pon aru."
    glossedTokens := [("Sono", "that"), ("ashi-ni-wa", "leg-LOC-TOP"), ("yubi-ga", "digit-NOM"), ("rop-pon", "6-long.slender.object"), ("aru", "exist")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "7"), ("classifier", "hon"), ("construction", "qFloat"), ("number", "unitizing")] }

def ex_7_6a : Datum :=
  { id := "downing1996_7_6a"
    source := ⟨"downing-1996", "(6a), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ima, tookyoo-to-iu daitokai-ni iru kodomo-tachi-o mite-iru to, zuibun kawaisoo da to omou-no-wa ..."
    glossedTokens := [("Ima", "now"), ("tookyoo-to-iu", "Tokyo-QUOT"), ("daitokai-ni", "large.city-LOC"), ("iru", "be"), ("kodomo-tachi-o", "child-PL-ACC"), ("mite-iru", "seeing-be"), ("zuibun", "really"), ("kawaisoo", "sad")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ima, tookyoo-to iu daitokai-ni iru kodomo-o mite-iru to, zuibun kawaisoo da to omou no wa, ...", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "human"), ("head", "commonNoun"), ("number", "pluralPossible")] }

def ex_7_7a : Datum :=
  { id := "downing1996_7_7a"
    source := ⟨"downing-1996", "(7a), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ima, tookyoo-to iu daitokai-ni iru neko-tachi-o mite-iru to, zuibun kawaisoo da to omou no wa, ..."
    glossedTokens := [("neko-tachi-o", "cat-PL-ACC")]
    context := ""
    judgment := .questionable
    alternatives := [("Ima, tookyoo-to iu daitokai-ni iru neko-o mite-iru to, zuibun kawaisoo da to omou no wa, ...", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "animate"), ("head", "commonNoun"), ("number", "pluralRare")] }

def ex_7_8a : Datum :=
  { id := "downing1996_7_8a"
    source := ⟨"downing-1996", "(8a), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ima, tookyoo-to iu daitokai-ni aru tatemono-tachi-o mite-iru to, zuibun kawaisoo da to omou no wa, ..."
    glossedTokens := [("tatemono-tachi-o", "building-PL-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Ima, tookyoo-to iu daitokai-ni aru tatemono-o mite-iru to, zuibun kawaisoo da to omou no wa, ...", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "inanimate"), ("head", "commonNoun"), ("number", "pluralImpossible")] }

def ex_7_9 : Datum :=
  { id := "downing1996_7_9"
    source := ⟨"downing-1996", "(9), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kore-ra-no kao-no naka-ni-wa, ..."
    glossedTokens := [("Kore-ra-no", "this-PL-GEN"), ("kao-no", "face-GEN"), ("naka-ni-wa", "middle-LOC-TOP")]
    context := "Fathers with children and youths with their lovers have gone in and out of the shop."
    judgment := .acceptable
    alternatives := [("Kono kao-tachi-no naka-ni-wa, ...", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "inanimate"), ("head", "pronoun"), ("number", "pluralRequired")] }

def ex_7_10 : Datum :=
  { id := "downing1996_7_10"
    source := ⟨"downing-1996", "(10), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kanja-wa hyakushoo-no okami-ya sono kodomo-ga ooi. Kare-ra-wa genkan-no agarikuchi-ni koshi-o oroshite ... matte-ita."
    glossedTokens := [("Kanja-wa", "patient-TOP"), ("hyakushoo-no", "farmer-GEN"), ("okami-ya", "wife-and"), ("sono", "that"), ("kodomo-ga", "child-NOM"), ("ooi", "many"), ("Kare-ra-wa", "he-PL-TOP"), ("matte-ita", "waiting-were")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kanja-tachi-wa hyakushoo-no okami-ya sono kodomo-ga ooi. Kare-ra-wa genkan-no agarikuchi-ni koshi-o oroshite ... matte-ita.", .acceptable), ("Kanja-wa hyakushoo-no okami-ya sono kodomo-ga ooi. Kare-wa genkan-no agarikuchi-ni koshi-o oroshite ... matte-ita.", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "human"), ("head", "pronoun"), ("number", "pluralRequired")] }

def ex_7_11 : Datum :=
  { id := "downing1996_7_11"
    source := ⟨"downing-1996", "(11), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Endoo-san-tachi-to hanashi-o suru to, watashi-no gehinna bubun-ga hikidasarete-kuru-no."
    glossedTokens := [("Endoo-san-tachi-to", "Endō-HON-PL-COM"), ("hanashi-o", "talk-ACC"), ("suru", "do"), ("to", "when"), ("watashi-no", "I-GEN"), ("gehinna", "low.class"), ("bubun-ga", "part-NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "human"), ("head", "properNoun"), ("number", "associativePlural")] }

def ex_7_12 : Datum :=
  { id := "downing1996_7_12"
    source := ⟨"downing-1996", "(12), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kodomo-tachi-ga shiken-o ukeru aida-ni okaasan-tachi-ga kono heya-de matsu yotei desu ga."
    glossedTokens := [("Kodomo-tachi-ga", "child-PL-NOM"), ("shiken-o", "test-ACC"), ("ukeru", "receive"), ("aida-ni", "period-LOC"), ("okaasan-tachi-ga", "mother-PL-NOM"), ("kono", "this"), ("heya-de", "room-LOC"), ("matsu", "wait"), ("yotei", "plan"), ("desu", "COP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("class plural: the mothers", .acceptable), ("associative: Mother and the others", .acceptable)]
    paperFeatures := [("chapter", "7"), ("referent", "human"), ("head", "commonNoun"), ("number", "classPlural")] }

def ex_7_16 : Datum :=
  { id := "downing1996_7_16"
    source := ⟨"downing-1996", "(16), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Masutaa-to onaji-yoona katachi-no kitsune-no yoona kao-o motta otoko-ga iku-nin-mo suwatte-ita. ... kare-ra-no hosonagai zoo-no yoona me-wa ... Ano otoko-tachi-mo ima-wa doko-ka-de gasorin-sutando-no shujin-ni natte-iru kamoshirenai."
    glossedTokens := [("otoko-ga", "man-NOM"), ("iku-nin-mo", "a.number-people-EMPH"), ("suwatte-ita", "sitting-were"), ("kare-ra-no", "he-PL-GEN"), ("Ano", "that"), ("otoko-tachi-mo", "male-PL-too")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "human"), ("number", "tracking"), ("mentions", "classifierPhrase,pluralMarked,pluralMarked")] }

def ex_7_18 : Datum :=
  { id := "downing1996_7_18"
    source := ⟨"downing-1996", "(18), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "neko-wa ne, kawaii kodomo-no toki dat-tara, go-rop-piki, kai-tai kedomo ..."
    glossedTokens := [("neko-wa", "cat-TOP"), ("kawaii", "cute"), ("kodomo-no", "child-GEN"), ("toki", "time"), ("dat-tara", "COP-when"), ("go-rop-piki", "5-6-animal"), ("kai-tai", "raise-DESID")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "7"), ("classifier", "hiki"), ("number", "unitizing")] }

def ex_7_23 : Datum :=
  { id := "downing1996_7_23"
    source := ⟨"downing-1996", "(23), Chapter 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iku-nin-mo-no onna-no kao-ga me-no mae-no kuukan-ni naranda. Sono onna-tachi-no naka-de-wa, watashi-no kodomo-o oroshita kao-mo majitte-ita."
    glossedTokens := [("Iku-nin-mo-no", "a.number-person-EMPH-GEN"), ("onna-no", "female-ATT"), ("kao-ga", "face-NOM"), ("naranda", "lined.up"), ("Sono", "that"), ("onna-tachi-no", "female-PL-GEN"), ("naka-de-wa", "middle-LOC-TOP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "7"), ("referent", "human"), ("number", "tracking"), ("mentions", "classifierPhrase,pluralMarked")] }

def ex_8_1 : Datum :=
  { id := "downing1996_8_1"
    source := ⟨"downing-1996", "(1), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mae-o hashitte-ita ni-dai-no jooyoosha-ga tsukamatta."
    glossedTokens := [("Mae-o", "front-ACC"), ("hashitte-ita", "traversing-were"), ("ni-dai-no", "2-vehicle-ATT"), ("jooyoosha-ga", "car-NOM"), ("tsukamatta", "were.caught")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mae-o hashitte-ita jooyoosha-ga ni-dai tsukamatta.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "dai"), ("construction", "preNominal")] }

def ex_8_2 : Datum :=
  { id := "downing1996_8_2"
    source := ⟨"downing-1996", "(2), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ip-pon-no tabako-o sutte-mimashoo."
    glossedTokens := [("Ip-pon-no", "1-long.slender.object-ATT"), ("tabako-o", "cigarette-ACC"), ("sutte-mimashoo", "smoking-let's.try")]
    context := ""
    judgment := .marginal
    alternatives := [("Tabako-o ip-pon sutte-mimashoo.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "hon"), ("construction", "preNominal")] }

def ex_8_3 : Datum :=
  { id := "downing1996_8_3"
    source := ⟨"downing-1996", "(3), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "San-nin-no tomodachi-o matte-imasu."
    glossedTokens := [("San-nin-no", "3-person-ATT"), ("tomodachi-o", "friend-ACC"), ("matte-imasu", "waiting.for-be")]
    context := "The speaker has particular individuals in mind."
    judgment := .acceptable
    alternatives := [("Tomodachi-o san-nin matte-imasu.", .marginal)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "preNominal")] }

def ex_8_4 : Datum :=
  { id := "downing1996_8_4"
    source := ⟨"downing-1996", "(4), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hisho-o san-nin sagashite-imasu."
    glossedTokens := []
    context := "Any three secretaries will do; their identities are not known to the speaker."
    judgment := .acceptable
    alternatives := [("San-nin-no hisho-o sagashite-imasu.", .marginal)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "qFloat")] }

def ex_8_5 : Datum :=
  { id := "downing1996_8_5"
    source := ⟨"downing-1996", "(5), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kare-ra futari-ga kita."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Futari-no kare-ra-ga kita.", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "appositive")] }

def ex_8_8 : Datum :=
  { id := "downing1996_8_8"
    source := ⟨"downing-1996", "(8), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sore-ga, atashi-tachi-no, otona-no hito-tsu-no tsutome demo-aru-n desu yo."
    glossedTokens := [("Sore-ga", "that-NOM"), ("atashi-tachi-no", "I-PL-GEN"), ("otona-no", "adult-GEN"), ("hito-tsu-no", "1-inanimate-ATT"), ("tsutome", "duty"), ("demo-aru-n", "COP-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "tsu"), ("construction", "preNominal"), ("use", "definitenessBlocking")] }

def ex_8_17 : Datum :=
  { id := "downing1996_8_17"
    source := ⟨"downing-1996", "(17), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-tachi go-nin-ga haitte-kita."
    glossedTokens := [("Taroo-tachi", "Taro-PL"), ("go-nin-ga", "5-person-NOM"), ("haitte-kita", "entering-came")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "appositive"), ("number", "associativePlural")] }

def ex_8_19 : Datum :=
  { id := "downing1996_8_19"
    source := ⟨"downing-1996", "(19), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Haha-no nakunatta yoru, hitobito-no doojoo-wa, Kaeko hitori-ni atsumarimashita."
    glossedTokens := [("Haha-no", "Mother-SSUB"), ("nakunatta", "died"), ("yoru", "evening"), ("hitobito-no", "people-GEN"), ("doojoo-wa", "sympathy-TOP"), ("Kaeko", "Kaeko"), ("hitori-ni", "1.person-DAT"), ("atsumarimashita", "collected")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "appositive"), ("use", "exhaustive")] }

def ex_8_25 : Datum :=
  { id := "downing1996_8_25"
    source := ⟨"downing-1996", "(25), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Shiroi shinsatsuki-o kita oyaji, Asai joshu, kangofuchoo Toda, Suguro-no go-nin-ga byooshitsu-ni hairu to ..."
    glossedTokens := [("oyaji", "old.man"), ("Asai", "Asai"), ("joshu", "assistant"), ("kangofuchoo", "head.nurse"), ("Toda", "Toda"), ("Suguro-no", "Suguro-ATT"), ("go-nin-ga", "5-person-NOM"), ("byooshitsu-ni", "sickroom-LOC"), ("hairu", "enter")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "summativeAppositive")] }

def ex_8_28 : Datum :=
  { id := "downing1996_8_28"
    source := ⟨"downing-1996", "(28), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Enban-wa ichi-mai-zutsu tonde-iki, ..."
    glossedTokens := [("Enban-wa", "disk-TOP"), ("ichi-mai-zutsu", "1-flat.thin.object-each"), ("tonde-iki", "flying-go")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "mai"), ("construction", "qFloat"), ("use", "distributive")] }

def ex_8_30 : Datum :=
  { id := "downing1996_8_30"
    source := ⟨"downing-1996", "(30), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kodomo-ga san-nin heya-ni haitte-kita."
    glossedTokens := [("Kodomo-ga", "child-NOM"), ("san-nin", "3-person"), ("heya-ni", "room-LOC"), ("haitte-kita", "entering-came")]
    context := ""
    judgment := .acceptable
    alternatives := [("San-nin-no kodomo-ga heya-ni haitte-kita.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "qFloat"), ("use", "introduction")] }

def ex_8_31 : Datum :=
  { id := "downing1996_8_31"
    source := ⟨"downing-1996", "(31), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kantoku-ga hitori-no onna-shashoo-to modotte-kita."
    glossedTokens := [("Kantoku-ga", "director-NOM"), ("hitori-no", "1.person-ATT"), ("onna-shashoo-to", "woman-conductor-COM"), ("modotte-kita", "returning-came")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kantoku-ga onna-shashoo-to hitori modotte-kita.", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "preNominal"), ("role", "oblique")] }

def ex_8_33 : Datum :=
  { id := "downing1996_8_33"
    source := ⟨"downing-1996", "(33), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kore-ra-no san-nin-no gakusei-ni furansu-go-ga wakarimasu."
    glossedTokens := [("Kore-ra-no", "this-PL-ATT"), ("san-nin-no", "3-person-ATT"), ("gakusei-ni", "student-DAT"), ("furansu-go-ga", "France-language-NOM"), ("wakarimasu", "understand")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kore-ra-no gakusei-ni, san-nin furansu-go-ga wakarimasu.", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "preNominal"), ("role", "dativeSubject")] }

def ex_8_34 : Datum :=
  { id := "downing1996_8_34"
    source := ⟨"downing-1996", "(34), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kore-ra-no gakusei-ga, san-nin furansu-go-ga wakarimasu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Kore-ra-no san-nin-no gakusei-ga furansu-go-ga wakarimasu.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "qFloat"), ("role", "nominativeSubject")] }

def ex_8_38 : Datum :=
  { id := "downing1996_8_38"
    source := ⟨"downing-1996", "(38a), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Otoko-ga kodomo-o san-nin yuukai shita."
    glossedTokens := [("Otoko-ga", "man-NOM"), ("kodomo-o", "child-ACC"), ("san-nin", "3-person"), ("yuukai", "abduction"), ("shita", "did")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("quantifies the object: three children", .acceptable), ("quantifies the transitive subject: three men", .marginal)]
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "qFloat"), ("role", "object")] }

def ex_8_39 : Datum :=
  { id := "downing1996_8_39"
    source := ⟨"downing-1996", "(39), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-ga fune-ga roku-soo boofuu-de shizunda to omotte-iru."
    glossedTokens := [("Hanako-ga", "Hanako-NOM"), ("fune-ga", "ship-NOM"), ("roku-soo", "6-ship"), ("boofuu-de", "storm-INST"), ("shizunda", "sank"), ("to", "QUOT"), ("omotte-iru", "thinking-be")]
    context := ""
    judgment := .acceptable
    alternatives := [("Hanako-ga kodomo-ga roku-nin tylenol-ni seisankari-o ireta to omotte-iru.", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "soo"), ("construction", "qFloat"), ("role", "unaccusativeSubject")] }

def ex_8_42 : Datum :=
  { id := "downing1996_8_42"
    source := ⟨"downing-1996", "(42), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ta-ni, boku-no deshi-ga nan-nin-ka ite, ..."
    glossedTokens := [("Ta-ni", "in.addition"), ("boku-no", "I-GEN"), ("deshi-ga", "student-NOM"), ("nan-nin-ka", "Q-person-Q"), ("ite", "being")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "nin"), ("construction", "qFloat"), ("use", "partitive")] }

def ex_8_43 : Datum :=
  { id := "downing1996_8_43"
    source := ⟨"downing-1996", "(43), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kenjuu-o koshi-ni sageta heishi-ga ni-mei doa-o akete ikioiyoku tobi-orita. ... kogara-no futari-no heishi-tachi-no yoko-de kare-ra-no sei-ga amarini takai."
    glossedTokens := [("heishi-ga", "soldier-NOM"), ("ni-mei", "2-person.HON"), ("kogara-no", "small.stature-ATT"), ("futari-no", "2.person-ATT"), ("heishi-tachi-no", "soldier-PL-GEN"), ("kare-ra-no", "he-PL-GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "8"), ("construction", "qFloat"), ("use", "introduction"), ("mentions", "classifierPhrase,pluralMarked")] }

def ex_8_44 : Datum :=
  { id := "downing1996_8_44"
    source := ⟨"downing-1996", "(44), Chapter 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mai-nichi, mai-nichi, hito-tsu-no burausu-o kite, sooji-o shite-ita."
    glossedTokens := [("Mai-nichi", "every-day"), ("hito-tsu-no", "1-inan-ATT"), ("burausu-o", "blouse-ACC"), ("kite", "wearing"), ("sooji-o", "cleaning-ACC"), ("shite-ita", "doing-was")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mai-nichi, mai-nichi, burausu hito-tsu-o kite, sooji-o shite-ita.", .acceptable), ("Mai-nichi, mai-nichi burausu-o hito-tsu kite, sooji-o shite-ita.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("classifier", "tsu"), ("construction", "preNominal")] }

def all : List Datum := [ex_1_14, ex_1_15, ex_3_2a, ex_3_2b, ex_3_3, ex_3_4, ex_3_5a, ex_3_33, ex_3_35, ex_3_36, ex_3_37a, ex_3_38, ex_3_39, ex_5_7, ex_5_9, ex_6_2, ex_6_5, ex_6_6, ex_6_9, ex_6_13, ex_6_20, ex_7_2b, ex_7_3, ex_7_4, ex_7_6a, ex_7_7a, ex_7_8a, ex_7_9, ex_7_10, ex_7_11, ex_7_12, ex_7_16, ex_7_18, ex_7_23, ex_8_1, ex_8_2, ex_8_3, ex_8_4, ex_8_5, ex_8_8, ex_8_17, ex_8_19, ex_8_25, ex_8_28, ex_8_30, ex_8_31, ex_8_33, ex_8_34, ex_8_38, ex_8_39, ex_8_42, ex_8_43, ex_8_44]

end Downing1996.Examples
