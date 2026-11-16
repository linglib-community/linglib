module

public import Linglib.Data.Examples.Schema

/-!
# `Huijsmans2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Huijsmans2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Huijsmans2025.Examples`.
-/

@[expose] public section

namespace Huijsmans2025.Examples

def ex37 : Datum :=
  { id := "huijsmans2025_ex37"
    source := ⟨"huijsmans-2025", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She seems to be very sick."
    glossedTokens := []
    context := "P visits M in the hospital. P sees through the window of the hospital room that the doctors look worried. P says:"
    judgment := .acceptable
    alternatives := [("She should be very sick.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "seems"), ("timing", "evidence acquired after the event")] }

def ex38 : Datum :=
  { id := "huijsmans2025_ex38"
    source := ⟨"huijsmans-2025", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She should be very sick."
    glossedTokens := []
    context := "P poisons M's food and leaves. Later P says:"
    judgment := .acceptable
    alternatives := [("She seems to be very sick.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "should"), ("timing", "evidence acquired before the event")] }

def ex40 : Datum :=
  { id := "huijsmans2025_ex40"
    source := ⟨"huijsmans-2025", "(40)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi č̓ɛχ."
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("č̓əx̌", "get.cooked")]
    glossedWords := [⟨[['s', 'ə', 'm'], ['k', 'ʷ', 'i']], [['F', 'U', 'T'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['č', '̓', 'ə', 'x', '̌']], [['g', 'e', 't', '.', 'c', 'o', 'o', 'k', 'e', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "We're outside, but I have a fish cooking in the oven. I check my watch and realize that it should be cooked. I say to you:"
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi č̓ɛχ.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT")] }

def ex41 : Datum :=
  { id := "huijsmans2025_ex41"
    source := ⟨"huijsmans-2025", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It will be cooked (by now)."
    glossedTokens := []
    context := "Same as (40)."
    judgment := .acceptable
    alternatives := [("It must be cooked (by now).", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT")] }

def ex42 : Datum :=
  { id := "huijsmans2025_ex42"
    source := ⟨"huijsmans-2025", "(42)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi θo hɛwt."
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("θu", "go"), ("hiwt", "get.home")]
    glossedWords := [⟨[['s', 'ə', 'm'], ['k', 'ʷ', 'i']], [['F', 'U', 'T'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['θ', 'u']], [['g', 'o']]⟩, ⟨[['h', 'i', 'w', 't']], [['g', 'e', 't', '.', 'h', 'o', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Daniel left from t̓ɩšosəm to go back home to Vancouver. We know he left pretty early, so in the evening when we see the time, I say:"
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi θo hɛwt.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT")] }

def ex43 : Datum :=
  { id := "huijsmans2025_ex43"
    source := ⟨"huijsmans-2025", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will have gotten home (by now)."
    glossedTokens := []
    context := "Same as (42)."
    judgment := .acceptable
    alternatives := [("He must have gotten home (by now).", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT")] }

def ex44 : Datum :=
  { id := "huijsmans2025_ex44"
    source := ⟨"huijsmans-2025", "(44)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi qey."
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("qəy", "die")]
    glossedWords := [⟨[['s', 'ə', 'm'], ['k', 'ʷ', 'i']], [['F', 'U', 'T'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['q', 'ə', 'y']], [['d', 'i', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The villain puts poison in the hero's food that he has prepped for dinner and then leaves. An hour or so after dinnertime, the villain tells his sidekick:"
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi qey.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT")] }

def ex45 : Datum :=
  { id := "huijsmans2025_ex45"
    source := ⟨"huijsmans-2025", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will be dead (by now)."
    glossedTokens := []
    context := "Same as (44)."
    judgment := .acceptable
    alternatives := [("He must be dead (by now).", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT")] }

def ex46 : Datum :=
  { id := "huijsmans2025_ex46"
    source := ⟨"huijsmans-2025", "(46)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "χʷɛt səmkʷa ƛəm̓mot Felipe. saymot kʷ č̓ɩɬ ʔi xʷukʷt č̓ɩɬukʷts."
    glossedTokens := [("x̌ʷit", "really"), ("səm=kʷa", "FUT=CL.DEM"), ("ƛ̓əm̓-mut", "get.wet-INT"), ("Felipe", "Felipe"), ("saymut", "intense"), ("kʷ=č̓əɬ", "DET=rain"), ("ʔiy", "CONJ"), ("xʷukʷt", "not.exist"), ("č̓əɬ-ukʷt-s", "rain-jacket-3POSS")]
    glossedWords := [⟨[['x', '̌', 'ʷ', 'i', 't']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['s', 'ə', 'm'], ['k', 'ʷ', 'a']], [['F', 'U', 'T'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['ƛ', '̓', 'ə', 'm', '̓'], ['m', 'u', 't']], [['g', 'e', 't', '.', 'w', 'e', 't'], ['I', 'N', 'T']]⟩, ⟨[['F', 'e', 'l', 'i', 'p', 'e']], [['F', 'e', 'l', 'i', 'p', 'e']]⟩, ⟨[['s', 'a', 'y', 'm', 'u', 't']], [['i', 'n', 't', 'e', 'n', 's', 'e']]⟩, ⟨[['k', 'ʷ'], ['č', '̓', 'ə', 'ɬ']], [['D', 'E', 'T'], ['r', 'a', 'i', 'n']]⟩, ⟨[['ʔ', 'i', 'y']], [['C', 'O', 'N', 'J']]⟩, ⟨[['x', 'ʷ', 'u', 'k', 'ʷ', 't']], [['n', 'o', 't', '.', 'e', 'x', 'i', 's', 't']]⟩, ⟨[['č', '̓', 'ə', 'ɬ'], ['u', 'k', 'ʷ', 't'], ['s']], [['r', 'a', 'i', 'n'], ['j', 'a', 'c', 'k', 'e', 't'], ['3', 'P', 'O', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Felipe always bikes home at 5. I haven't been paying attention to the weather, but at 6 I look out the window and see that it is pouring and has been for some time—the ground is really soaked. Then I notice that Felipe left his coat in my bag, which is with me on campus. I figure Felipe will be just home by now, but must have been soaked on his way. I say:"
    judgment := .acceptable
    alternatives := [("χʷɛt č̓ɛkʷa ƛəm̓mot Felipe.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT but ET < EAT"), ("role", "wedge against the EAT analysis")] }

def ex47 : Datum :=
  { id := "huijsmans2025_ex47"
    source := ⟨"huijsmans-2025", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Felipe will have gotten really soaked. It's pouring, and he didn't have a rain jacket."
    glossedTokens := []
    context := "Same as (46)."
    judgment := .acceptable
    alternatives := [("Felipe must have gotten really soaked.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT but ET < EAT"), ("role", "wedge against the EAT analysis")] }

def ex48 : Datum :=
  { id := "huijsmans2025_ex48"
    source := ⟨"huijsmans-2025", "(48)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "hɛhɛw səmkʷa č̓ɩmč̓ɛʔmamot."
    glossedTokens := [("hihiw", "really"), ("səm=kʷa", "FUT=CL.DEM"), ("č̓əm̓~č̓əm-əm-mut", "cold~CHAR-MD-INT")]
    glossedWords := [⟨[['h', 'i', 'h', 'i', 'w']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['s', 'ə', 'm'], ['k', 'ʷ', 'a']], [['F', 'U', 'T'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['č', '̓', 'ə', 'm', '̓', '~', 'č', '̓', 'ə', 'm'], ['ə', 'm'], ['m', 'u', 't']], [['c', 'o', 'l', 'd', '~', 'C', 'H', 'A', 'R'], ['M', 'D'], ['I', 'N', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "It's winter. Last night, it was very cold, with strong winds and some snow. Today, I find out that my friend had been clam-digging last night."
    judgment := .acceptable
    alternatives := [("hɛhɛw č̓ɛkʷa č̓ɩmč̓ɛʔmamot.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT but ET < EAT")] }

def ex49 : Datum :=
  { id := "huijsmans2025_ex49"
    source := ⟨"huijsmans-2025", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She will have been really cold!"
    glossedTokens := []
    context := "Same as (48)."
    judgment := .acceptable
    alternatives := [("She must have been really cold!", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT but ET < EAT")] }

def ex50 : Datum :=
  { id := "huijsmans2025_ex50"
    source := ⟨"huijsmans-2025", "(50)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɛkʷi č̓ɛχ."
    glossedTokens := [("č̓a=kʷi", "INFER=CL.DEM"), ("č̓əx̌", "get.cooked")]
    glossedWords := [⟨[['č', '̓', 'a'], ['k', 'ʷ', 'i']], [['I', 'N', 'F', 'E', 'R'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['č', '̓', 'ə', 'x', '̌']], [['g', 'e', 't', '.', 'c', 'o', 'o', 'k', 'e', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "I'm cooking a fish, and I'm guessing by the smell that it is cooked. I remark to you:"
    judgment := .acceptable
    alternatives := [("səmkʷi č̓ɛχ.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "PrejT ≤ MBT")] }

def ex51 : Datum :=
  { id := "huijsmans2025_ex51"
    source := ⟨"huijsmans-2025", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be cooked (by now)."
    glossedTokens := []
    context := "Same as (50)."
    judgment := .acceptable
    alternatives := [("It will be cooked (by now).", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "PrejT ≤ MBT")] }

def ex52 : Datum :=
  { id := "huijsmans2025_ex52"
    source := ⟨"huijsmans-2025", "(52)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɛkʷi θo hɛwt."
    glossedTokens := [("č̓a=kʷi", "INFER=CL.DEM"), ("θu", "go"), ("hiwt", "get.home")]
    glossedWords := [⟨[['č', '̓', 'a'], ['k', 'ʷ', 'i']], [['I', 'N', 'F', 'E', 'R'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['θ', 'u']], [['g', 'o']]⟩, ⟨[['h', 'i', 'w', 't']], [['g', 'e', 't', '.', 'h', 'o', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Someone was out earlier, and now I see his car in his driveway."
    judgment := .acceptable
    alternatives := [("səmkʷi θo hɛwt.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "PrejT ≤ MBT")] }

def ex53 : Datum :=
  { id := "huijsmans2025_ex53"
    source := ⟨"huijsmans-2025", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have gotten home."
    glossedTokens := []
    context := "Same as (52)."
    judgment := .acceptable
    alternatives := [("He will have gotten home.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "PrejT ≤ MBT")] }

def ex54 : Datum :=
  { id := "huijsmans2025_ex54"
    source := ⟨"huijsmans-2025", "(54)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "qəqey=č̓ɛ."
    glossedTokens := [("qəqey=č̓a", "dead=INFER")]
    glossedWords := [⟨[['q', 'ə', 'q', 'e', 'y'], ['č', '̓', 'a']], [['d', 'e', 'a', 'd'], ['I', 'N', 'F', 'E', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "My brother was hiking, and at one point there was a cliff looking out over the water. Looking down, he could see a bear, but it was just laid out, not moving."
    judgment := .acceptable
    alternatives := [("qəqey=səm.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "PrejT ≤ MBT")] }

def ex55 : Datum :=
  { id := "huijsmans2025_ex55"
    source := ⟨"huijsmans-2025", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be dead."
    glossedTokens := []
    context := "Same as (54)."
    judgment := .acceptable
    alternatives := [("It will be dead.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "PrejT ≤ MBT")] }

def ex56 : Datum :=
  { id := "huijsmans2025_ex56"
    source := ⟨"huijsmans-2025", "(56)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "qʷol č̓ɛ səmt χəpi. xʷaʔčxʷ χaχƛɛmaxʷ."
    glossedTokens := [("qʷəl̓=č̓a=səm=ʔut", "come=INFER=FUT=EXCL"), ("χəpəy", "return"), ("xʷaʔ=čxʷ", "NEG=2SG.SBJ"), ("χaχƛim=axʷ", "worry=2SG.SBJV")]
    glossedWords := [⟨[['q', 'ʷ', 'ə', 'l', '̓'], ['č', '̓', 'a'], ['s', 'ə', 'm'], ['ʔ', 'u', 't']], [['c', 'o', 'm', 'e'], ['I', 'N', 'F', 'E', 'R'], ['F', 'U', 'T'], ['E', 'X', 'C', 'L']]⟩, ⟨[['χ', 'ə', 'p', 'ə', 'y']], [['r', 'e', 't', 'u', 'r', 'n']]⟩, ⟨[['x', 'ʷ', 'a', 'ʔ'], ['č', 'x', 'ʷ']], [['N', 'E', 'G'], ['2', 'S', 'G', '.', 'S', 'B', 'J']]⟩, ⟨[['χ', 'a', 'χ', 'ƛ', 'i', 'm'], ['a', 'x', 'ʷ']], [['w', 'o', 'r', 'r', 'y'], ['2', 'S', 'G', '.', 'S', 'B', 'J', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Tim is Bailey's cat that's gone missing. He hasn't been seen for a while now. Even though she doesn't have any knowledge of what is going on with him, Gloria is trying to reassure Bailey:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "no evidence")] }

def ex57 : Datum :=
  { id := "huijsmans2025_ex57"
    source := ⟨"huijsmans-2025", "(57)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɛkʷi nɛʔ ʔamot."
    glossedTokens := [("č̓a=kʷi", "INFER=CL.DEM"), ("niʔ", "be.there"), ("ʔamut", "be.home")]
    glossedWords := [⟨[['č', '̓', 'a'], ['k', 'ʷ', 'i']], [['I', 'N', 'F', 'E', 'R'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['n', 'i', 'ʔ']], [['b', 'e', '.', 't', 'h', 'e', 'r', 'e']]⟩, ⟨[['ʔ', 'a', 'm', 'u', 't']], [['b', 'e', '.', 'h', 'o', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "It's after 6, so it's the time when my brother would usually be home from work. I drive past his place and see that his car is in the driveway and his lights are on. I think to myself."
    judgment := .acceptable
    alternatives := [("səmkʷi nɛʔ ʔamot.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "evidence before and at PrejT")] }

def ex58 : Datum :=
  { id := "huijsmans2025_ex58"
    source := ⟨"huijsmans-2025", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must be home."
    glossedTokens := []
    context := "Same as (57)."
    judgment := .acceptable
    alternatives := [("He will be home.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "evidence before and at PrejT")] }

def ex59 : Datum :=
  { id := "huijsmans2025_ex59"
    source := ⟨"huijsmans-2025", "(59)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi č̓ɛχ šɛtᶿ kʷukʷ."
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("č̓əx̌", "get.cooked"), ("šə=tᶿ=kʷukʷ", "DET=1SG.POSS=cook")]
    glossedWords := [⟨[['s', 'ə', 'm'], ['k', 'ʷ', 'i']], [['F', 'U', 'T'], ['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['č', '̓', 'ə', 'x', '̌']], [['g', 'e', 't', '.', 'c', 'o', 'o', 'k', 'e', 'd']]⟩, ⟨[['š', 'ə'], ['t', 'ᶿ'], ['k', 'ʷ', 'u', 'k', 'ʷ']], [['D', 'E', 'T'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['c', 'o', 'o', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := "This fish has been in the oven for 20 min, which should be sufficient given its size. In addition, the fish is starting to smell cooked."
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi č̓ɛχ šɛtᶿ kʷukʷ.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm or č̓ɛ"), ("timing", "the smell may be set aside")] }

def ex60 : Datum :=
  { id := "huijsmans2025_ex60"
    source := ⟨"huijsmans-2025", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fish will be cooked."
    glossedTokens := []
    context := "Same as (59)."
    judgment := .acceptable
    alternatives := [("The fish must be cooked.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will or must"), ("timing", "the smell may be set aside")] }

def ex68 : Datum :=
  { id := "huijsmans2025_ex68"
    source := ⟨"huijsmans-2025", "(68)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "hoθotoɬ Freddie sqʷols səm ʔəkʷ meeting, ʔi kʷa xʷaʔ qʷol̓əs. kʷʊnas čɛməm? χaχyɛmot hɛhɛw."
    glossedTokens := [("huθut-uɬ", "say-PST"), ("Freddie", "Freddie"), ("s=qʷəl̓=s=səm", "NMLZ=come=3POSS=FUT"), ("ʔə=kʷ=meeting", "OBL=DET=meeting"), ("ʔiy", "CONJ"), ("kʷa=xʷaʔ", "CL.DEM=NEG"), ("qʷəl̓=as", "come=3SBJV"), ("kʷən=as", "COMP=3SBJV"), ("čəm̓-əm", "what.is.with-MD"), ("x̌ax̌ya-mut", "strange-INT"), ("hihiw", "really")]
    glossedWords := [⟨[['h', 'u', 'θ', 'u', 't'], ['u', 'ɬ']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩, ⟨[['F', 'r', 'e', 'd', 'd', 'i', 'e']], [['F', 'r', 'e', 'd', 'd', 'i', 'e']]⟩, ⟨[['s'], ['q', 'ʷ', 'ə', 'l', '̓'], ['s'], ['s', 'ə', 'm']], [['N', 'M', 'L', 'Z'], ['c', 'o', 'm', 'e'], ['3', 'P', 'O', 'S', 'S'], ['F', 'U', 'T']]⟩, ⟨[['ʔ', 'ə'], ['k', 'ʷ'], ['m', 'e', 'e', 't', 'i', 'n', 'g']], [['O', 'B', 'L'], ['D', 'E', 'T'], ['m', 'e', 'e', 't', 'i', 'n', 'g']]⟩, ⟨[['ʔ', 'i', 'y']], [['C', 'O', 'N', 'J']]⟩, ⟨[['k', 'ʷ', 'a'], ['x', 'ʷ', 'a', 'ʔ']], [['C', 'L', '.', 'D', 'E', 'M'], ['N', 'E', 'G']]⟩, ⟨[['q', 'ʷ', 'ə', 'l', '̓'], ['a', 's']], [['c', 'o', 'm', 'e'], ['3', 'S', 'B', 'J', 'V']]⟩, ⟨[['k', 'ʷ', 'ə', 'n'], ['a', 's']], [['C', 'O', 'M', 'P'], ['3', 'S', 'B', 'J', 'V']]⟩, ⟨[['č', 'ə', 'm', '̓'], ['ə', 'm']], [['w', 'h', 'a', 't', '.', 'i', 's', '.', 'w', 'i', 't', 'h'], ['M', 'D']]⟩, ⟨[['x', '̌', 'a', 'x', '̌', 'y', 'a'], ['m', 'u', 't']], [['s', 't', 'r', 'a', 'n', 'g', 'e'], ['I', 'N', 'T']]⟩, ⟨[['h', 'i', 'h', 'i', 'w']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "We had a meeting this morning, and Freddie had told me he would come, but never showed up. Later I tell you, 'Freddie was going to come but he never came.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("perspective", "past"), ("orientation", "future"), ("environment", "embedded")] }

def ex69 : Datum :=
  { id := "huijsmans2025_ex69"
    source := ⟨"huijsmans-2025", "(69)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "payɛ ʔot t̓ᶿɛt̓ᶿɛyʔəm ʔəkʷ tam kʷ yɛtɛt ʔi manom səm."
    glossedTokens := [("payaʔ=ʔut", "always=EXCL"), ("t̓ᶿi~t̓iy-ʔəm", "PROG~search-ACT.INTR"), ("ʔə=kʷ=tam", "OBL=DET=thing"), ("kʷ", "DET"), ("yəʔ-t=it", "do-CTR=3PL.POSS"), ("ʔi", "CONJ"), ("məʔ-nu-m=səm", "get-NCTR-PASS=FUT")]
    glossedWords := [⟨[['p', 'a', 'y', 'a', 'ʔ'], ['ʔ', 'u', 't']], [['a', 'l', 'w', 'a', 'y', 's'], ['E', 'X', 'C', 'L']]⟩, ⟨[['t', '̓', 'ᶿ', 'i', '~', 't', '̓', 'i', 'y'], ['ʔ', 'ə', 'm']], [['P', 'R', 'O', 'G', '~', 's', 'e', 'a', 'r', 'c', 'h'], ['A', 'C', 'T', '.', 'I', 'N', 'T', 'R']]⟩, ⟨[['ʔ', 'ə'], ['k', 'ʷ'], ['t', 'a', 'm']], [['O', 'B', 'L'], ['D', 'E', 'T'], ['t', 'h', 'i', 'n', 'g']]⟩, ⟨[['k', 'ʷ']], [['D', 'E', 'T']]⟩, ⟨[['y', 'ə', 'ʔ'], ['t'], ['i', 't']], [['d', 'o'], ['C', 'T', 'R'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['ʔ', 'i']], [['C', 'O', 'N', 'J']]⟩, ⟨[['m', 'ə', 'ʔ'], ['n', 'u'], ['m'], ['s', 'ə', 'm']], [['g', 'e', 't'], ['N', 'C', 'T', 'R'], ['P', 'A', 'S', 'S'], ['F', 'U', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "From a traditional story about Mink and Wolf."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("perspective", "past"), ("orientation", "future"), ("environment", "narrative")] }

def ex70 : Datum :=
  { id := "huijsmans2025_ex70"
    source := ⟨"huijsmans-2025", "(70)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ƛ̓ič̓t səm maʔnas"
    glossedTokens := [("ƛ̓<i>č̓t=səm", "fall.asleep<STAT>=FUT"), ("maʔna-s", "child-3POSS")]
    glossedWords := [⟨[['ƛ', '̓', '<', 'i', '>', 'č', '̓', 't'], ['s', 'ə', 'm']], [['f', 'a', 'l', 'l', '.', 'a', 's', 'l', 'e', 'e', 'p', '<', 'S', 'T', 'A', 'T', '>'], ['F', 'U', 'T']]⟩, ⟨[['m', 'a', 'ʔ', 'n', 'a'], ['s']], [['c', 'h', 'i', 'l', 'd'], ['3', 'P', 'O', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "I know my friend's baby's naptime. I take a look at the clock and decide not to call because the baby will be asleep, and she'll wake up if her mum tries to talk on the phone."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("orientation", "present")] }

def ex71 : Datum :=
  { id := "huijsmans2025_ex71"
    source := ⟨"huijsmans-2025", "(71)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ƛ̓ič̓t səm maʔnas"
    glossedTokens := [("ƛ̓<i>č̓t=səm", "fall.asleep<STAT>=FUT"), ("maʔna-s", "child-3POSS")]
    glossedWords := [⟨[['ƛ', '̓', '<', 'i', '>', 'č', '̓', 't'], ['s', 'ə', 'm']], [['f', 'a', 'l', 'l', '.', 'a', 's', 'l', 'e', 'e', 'p', '<', 'S', 'T', 'A', 'T', '>'], ['F', 'U', 'T']]⟩, ⟨[['m', 'a', 'ʔ', 'n', 'a'], ['s']], [['c', 'h', 'i', 'l', 'd'], ['3', 'P', 'O', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Over breakfast on a Saturday Felipe suggests going to drop in on our cousin in the afternoon, but I know the time he's thinking after lunch is when her baby will be napping."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("orientation", "future")] }

def ex75 : Datum :=
  { id := "huijsmans2025_ex75"
    source := ⟨"huijsmans-2025", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man came in at four. He would leave at eight. For the four hours he would be here, he would simply sit quietly in the corner looking out the window."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("modal", "would"), ("perspective", "past")] }

def ex76 : Datum :=
  { id := "huijsmans2025_ex76"
    source := ⟨"huijsmans-2025", "(76)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her baby will be asleep."
    glossedTokens := []
    context := "I know my friend's baby's naptime. I take a look at the clock and decide not to call because the baby will be asleep, and she'll wake up if her mum tries to talk on the phone."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("modal", "will"), ("orientation", "present")] }

def ex77 : Datum :=
  { id := "huijsmans2025_ex77"
    source := ⟨"huijsmans-2025", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her baby will be asleep."
    glossedTokens := []
    context := "Over breakfast on a Saturday Felipe suggests going to drop in on our cousin in the afternoon, but I know the time he's thinking after lunch is when her baby will be napping."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("modal", "will"), ("orientation", "future")] }

def ex91 : Datum :=
  { id := "huijsmans2025_ex91"
    source := ⟨"huijsmans-2025", "(91)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ʔamot č̓ɛ Freddie. χʷaʔwɩ́t tə nɩkʷayus."
    glossedTokens := [("ʔamut=č̓a", "be.home=INFER"), ("Freddie", "Freddie"), ("x̌ʷəw̓-ít", "get.lit-STAT"), ("tə=nikʷayu-s", "DET=light-3POSS")]
    glossedWords := [⟨[['ʔ', 'a', 'm', 'u', 't'], ['č', '̓', 'a']], [['b', 'e', '.', 'h', 'o', 'm', 'e'], ['I', 'N', 'F', 'E', 'R']]⟩, ⟨[['F', 'r', 'e', 'd', 'd', 'i', 'e']], [['F', 'r', 'e', 'd', 'd', 'i', 'e']]⟩, ⟨[['x', '̌', 'ʷ', 'ə', 'w', '̓'], ['í', 't']], [['g', 'e', 't', '.', 'l', 'i', 't'], ['S', 'T', 'A', 'T']]⟩, ⟨[['t', 'ə'], ['n', 'i', 'k', 'ʷ', 'a', 'y', 'u'], ['s']], [['D', 'E', 'T'], ['l', 'i', 'g', 'h', 't'], ['3', 'P', 'O', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "We go past Freddie's home, and I say that he must be home because his lights are on."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "č̓ɛ"), ("orientation", "present")] }

def ex92 : Datum :=
  { id := "huijsmans2025_ex92"
    source := ⟨"huijsmans-2025", "(92)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ʔɛʔɛχaǰɛʔoɬ č̓ɛ Betty. niš kʷikʷʔɛ́t tə k̓ʷimɛns."
    glossedTokens := [("ʔi~ʔix̌aǰa-uɬ=č̓a", "PROG~clean.roots-PST=INFER"), ("Betty", "Betty"), ("niš", "be.here"), ("kʷi<kʷ>ʔ-ít", "laid.out<PL>-STAT"), ("tə=k̓ʷimin-s", "DET=waste-3POSS")]
    glossedWords := [⟨[['ʔ', 'i', '~', 'ʔ', 'i', 'x', '̌', 'a', 'ǰ', 'a'], ['u', 'ɬ'], ['č', '̓', 'a']], [['P', 'R', 'O', 'G', '~', 'c', 'l', 'e', 'a', 'n', '.', 'r', 'o', 'o', 't', 's'], ['P', 'S', 'T'], ['I', 'N', 'F', 'E', 'R']]⟩, ⟨[['B', 'e', 't', 't', 'y']], [['B', 'e', 't', 't', 'y']]⟩, ⟨[['n', 'i', 'š']], [['b', 'e', '.', 'h', 'e', 'r', 'e']]⟩, ⟨[['k', 'ʷ', 'i', '<', 'k', 'ʷ', '>', 'ʔ'], ['í', 't']], [['l', 'a', 'i', 'd', '.', 'o', 'u', 't', '<', 'P', 'L', '>'], ['S', 'T', 'A', 'T']]⟩, ⟨[['t', 'ə'], ['k', '̓', 'ʷ', 'i', 'm', 'i', 'n'], ['s']], [['D', 'E', 'T'], ['w', 'a', 's', 't', 'e'], ['3', 'P', 'O', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "I go over to Betty's house for dinner, and as I'm approaching her front door, I see fresh shavings of cedar roots scattered on the grass. I say to Gloria, who's with me:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "č̓ɛ"), ("orientation", "past")] }

def ex93 : Datum :=
  { id := "huijsmans2025_ex93"
    source := ⟨"huijsmans-2025", "(93)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɩɬ č̓ɛ səm. ti qʷol nɛʔayɩtanəm."
    glossedTokens := [("č̓əɬ=č̓a=səm", "rain=INFER=FUT"), ("ti", "CL.DEM"), ("qʷəl̓", "come"), ("niʔayitanəm", "cloudy")]
    glossedWords := [⟨[['č', '̓', 'ə', 'ɬ'], ['č', '̓', 'a'], ['s', 'ə', 'm']], [['r', 'a', 'i', 'n'], ['I', 'N', 'F', 'E', 'R'], ['F', 'U', 'T']]⟩, ⟨[['t', 'i']], [['C', 'L', '.', 'D', 'E', 'M']]⟩, ⟨[['q', 'ʷ', 'ə', 'l', '̓']], [['c', 'o', 'm', 'e']]⟩, ⟨[['n', 'i', 'ʔ', 'a', 'y', 'i', 't', 'a', 'n', 'ə', 'm']], [['c', 'l', 'o', 'u', 'd', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "You feel a change in the weather and see storm clouds gathering."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "č̓ɛ over səm"), ("timing", "two presuppositions")] }

def ex97 : Datum :=
  { id := "huijsmans2025_ex97"
    source := ⟨"huijsmans-2025", "(97)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her baby will be asleep."
    glossedTokens := []
    context := "I know my friend's baby's naptime. I take a look at the clock and decide not to call because the baby will be asleep, and she'll wake up if her mum tries to talk on the phone."
    judgment := .acceptable
    alternatives := [("Her baby must be asleep.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "will"), ("pragmatics", "Maximize Presupposition")] }

def all : List Datum := [ex37, ex38, ex40, ex41, ex42, ex43, ex44, ex45, ex46, ex47, ex48, ex49, ex50, ex51, ex52, ex53, ex54, ex55, ex56, ex57, ex58, ex59, ex60, ex68, ex69, ex70, ex71, ex75, ex76, ex77, ex91, ex92, ex93, ex97]

end Huijsmans2025.Examples
