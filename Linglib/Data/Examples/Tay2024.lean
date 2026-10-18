module

public import Linglib.Data.Examples.Schema

/-!
# `Tay2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Tay2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Tay2024.Examples`.
-/

@[expose] public section

namespace Tay2024.Examples

def ex_41 : Datum :=
  { id := "tay2024_41"
    source := ⟨"tay-2024", "(41), (43)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao fǎnfǎnfùfùde kū de māma xǐng-le."
    glossedTokens := [("Bǎobao", "baby"), ("fǎnfǎnfùfùde", "repeatedly"), ("kū", "cry"), ("de", "DE"), ("māma", "mother"), ("xǐng-le", "awake-PFV")]
    context := "A V-de resultative modified by 'repeatedly'."
    judgment := .acceptable
    alternatives := []
    readings := [("the whole resultative is modified: repeated wakings", .acceptable), ("V1 alone is modified: the baby cried repeatedly until Mother woke once", .questionable)]
    paperFeatures := [] }

def ex_42 : Datum :=
  { id := "tay2024_42"
    source := ⟨"tay-2024", "(42), (44)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao fǎnfǎnfùfùde kū-xǐng-le māma."
    glossedTokens := [("Bǎobao", "baby"), ("fǎnfǎnfùfùde", "repeatedly"), ("kū-xǐng-le", "cry-awake-PFV"), ("māma", "mother")]
    context := "A V-V resultative modified by 'repeatedly'."
    judgment := .acceptable
    alternatives := []
    readings := [("the whole resultative is modified: repeated wakings", .acceptable), ("V1 alone is modified: the baby cried repeatedly until Mother woke once", .ungrammatical)]
    paperFeatures := [] }

def ex_45 : Datum :=
  { id := "tay2024_45"
    source := ⟨"tay-2024", "(45)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao zài jiā lǐ kū de línjū xǐng-le."
    glossedTokens := [("Bǎobao", "baby"), ("zài", "at"), ("jiā", "house"), ("lǐ", "inside"), ("kū", "cry"), ("de", "DE"), ("línjū", "neighbour"), ("xǐng-le", "awake-PFV")]
    context := "The baby cried at home until the neighbours woke up next door."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_46 : Datum :=
  { id := "tay2024_46"
    source := ⟨"tay-2024", "(46)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao zài jiā lǐ kū-xǐng-le línjū."
    glossedTokens := [("Bǎobao", "baby"), ("zài", "at"), ("jiā", "house"), ("lǐ", "inside"), ("kū-xǐng-le", "cry-awake-PFV"), ("línjū", "neighbour")]
    context := "The baby cried at home until the neighbours woke up next door."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_107 : Datum :=
  { id := "tay2024_107"
    source := ⟨"tay-2024", "(107)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān shè-sǐ-le Lǐsì."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("shè-sǐ-le", "shoot-die-PFV"), ("Lǐsì", "Lisi")]
    context := "Zhangsan shoots Lisi, who is fatally wounded but does not die at once: the shooting and the dying overlap only at the moment the bullet makes contact."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_131 : Datum :=
  { id := "tay2024_131"
    source := ⟨"tay-2024", "(131)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao kū-xǐng-le māma."
    glossedTokens := [("Bǎobao", "baby"), ("kū-xǐng-le", "cry-awake-PFV"), ("māma", "mother")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_132 : Datum :=
  { id := "tay2024_132"
    source := ⟨"tay-2024", "(132)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wǒ qiē-suì-le yángcōng."
    glossedTokens := [("Wǒ", "I"), ("qiē-suì-le", "cut-in.pieces-PFV"), ("yángcōng", "onion")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_133 : Datum :=
  { id := "tay2024_133"
    source := ⟨"tay-2024", "(133)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Mìyǔ xià-hēi-le tiāndì."
    glossedTokens := [("Mìyǔ", "dense.rain"), ("xià-hēi-le", "fall-black-PFV"), ("tiāndì", "earth")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "theme")] }

def ex_134 : Datum :=
  { id := "tay2024_134"
    source := ⟨"tay-2024", "(134)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Yīfú xǐ-lèi-le jiějiě."
    glossedTokens := [("Yīfú", "clothes"), ("xǐ-lèi-le", "wash-tired-PFV"), ("jiějiě", "elder.sister")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "theme")] }

def ex_137 : Datum :=
  { id := "tay2024_137"
    source := ⟨"tay-2024", "(137)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Éjūn jī-chén-le yī sōu xúnyángjiàn."
    glossedTokens := [("Éjūn", "Russian.forces"), ("jī-chén-le", "strike-sink-PFV"), ("yī", "one"), ("sōu", "CLF"), ("xúnyángjiàn", "cruiser")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_139 : Datum :=
  { id := "tay2024_139"
    source := ⟨"tay-2024", "(139)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Éjūn chōng-chén-le yī sōu xúnyángjiàn."
    glossedTokens := [("Éjūn", "Russian.forces"), ("chōng-chén-le", "rush-sink-PFV"), ("yī", "one"), ("sōu", "CLF"), ("xúnyángjiàn", "cruiser")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_146 : Datum :=
  { id := "tay2024_146"
    source := ⟨"tay-2024", "(146)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Jiàoliàn zǒu-lèi-le John."
    glossedTokens := [("Jiàoliàn", "coach"), ("zǒu-lèi-le", "walk-tired-PFV"), ("John", "John")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_148 : Datum :=
  { id := "tay2024_148"
    source := ⟨"tay-2024", "(148)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān liè-kāi-le jīdàn."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("liè-kāi-le", "crack-open-PFV"), ("jīdàn", "egg")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_149 : Datum :=
  { id := "tay2024_149"
    source := ⟨"tay-2024", "(149)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Qiēcàibǎn qiē-dùn-le wǒ de càidāo."
    glossedTokens := [("Qiēcàibǎn", "cutting.board"), ("qiē-dùn-le", "cut-dull-PFV"), ("wǒ", "1SG"), ("de", "DE"), ("càidāo", "knife")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_150 : Datum :=
  { id := "tay2024_150"
    source := ⟨"tay-2024", "(150)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhè bù diànyǐng kū-hóng-le wǒ de yǎnjīng."
    glossedTokens := [("Zhè", "this"), ("bù", "CLF"), ("diànyǐng", "movie"), ("kū-hóng-le", "cry-red-PFV"), ("wǒ", "1SG"), ("de", "DE"), ("yǎnjīng", "eye")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "subjectMatter")] }

def ex_151 : Datum :=
  { id := "tay2024_151"
    source := ⟨"tay-2024", "(151)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nèi ge xiàohuà xiào-téng-le Zhāngsān de dùzi."
    glossedTokens := [("Nèi", "that"), ("ge", "CLF"), ("xiàohuà", "joke"), ("xiào-téng-le", "laugh-hurt-PFV"), ("Zhāngsān", "Zhangsan"), ("de", "DE"), ("dùzi", "belly")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "subjectMatter")] }

def ex_202 : Datum :=
  { id := "tay2024_202"
    source := ⟨"tay-2024", "(202)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wǒ qiē-dùn-le càidāo."
    glossedTokens := [("Wǒ", "I"), ("qiē-dùn-le", "cut-dull-PFV"), ("càidāo", "knife")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_205 : Datum :=
  { id := "tay2024_205"
    source := ⟨"tay-2024", "(205)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhè dùn fàn chī-qióng-le wǒ."
    glossedTokens := [("Zhè", "this"), ("dùn", "CLF"), ("fàn", "meal"), ("chī-qióng-le", "eat-poor-PFV"), ("wǒ", "me")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("I ate the meal", .acceptable), ("someone else ate the meal I paid for", .acceptable)]
    paperFeatures := [("externalArgument", "theme")] }

def ex_206 : Datum :=
  { id := "tay2024_206"
    source := ⟨"tay-2024", "(206)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhè shǒu gē chàng-kū-le guānzhòng."
    glossedTokens := [("Zhè", "this"), ("shǒu", "CLF"), ("gē", "song"), ("chàng-kū-le", "sing-cry-PFV"), ("guānzhòng", "audience")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the audience sang", .acceptable), ("the performer sang", .acceptable)]
    paperFeatures := [("externalArgument", "theme")] }

def ex_216 : Datum :=
  { id := "tay2024_216"
    source := ⟨"tay-2024", "(216)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Yīfú xǐ-gānjìng-le."
    glossedTokens := [("Yīfú", "clothes"), ("xǐ-gānjìng-le", "wash-clean-PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_217 : Datum :=
  { id := "tay2024_217"
    source := ⟨"tay-2024", "(217)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wǒ de càidāo qiē-dùn-le."
    glossedTokens := [("Wǒ", "1SG"), ("de", "DE"), ("càidāo", "knife"), ("qiē-dùn-le", "cut-dull-PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_219 : Datum :=
  { id := "tay2024_219"
    source := ⟨"tay-2024", "(219)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān kū-lèi-le."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("kū-lèi-le", "cry-tired-PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_221 : Datum :=
  { id := "tay2024_221"
    source := ⟨"tay-2024", "(221)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Shǒujuǎn kū-shī-le."
    glossedTokens := [("Shǒujuǎn", "handkerchief"), ("kū-shī-le", "cry-wet-PFV")]
    context := "Out of the blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_224 : Datum :=
  { id := "tay2024_224"
    source := ⟨"tay-2024", "(224)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Māma kū-xǐng-le."
    glossedTokens := [("Māma", "mother"), ("kū-xǐng-le", "cry-awake-PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Mother cries herself awake", .acceptable), ("Mother wakes from someone else crying", .unacceptable)]
    paperFeatures := [] }

def ex_330 : Datum :=
  { id := "tay2024_330"
    source := ⟨"tay-2024", "(330), (349)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān qí-lèi-le mǎ."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("qí-lèi-le", "ride-tired-PFV"), ("mǎ", "horse")]
    context := "A hybrid resultative, commonly described as a subject-oriented transitive resultative."
    judgment := .acceptable
    alternatives := []
    readings := [("the horse became tired", .acceptable), ("Zhangsan became tired", .variable)]
    paperFeatures := [("externalArgument", "agent")] }

def ex_668 : Datum :=
  { id := "tay2024_668"
    source := ⟨"tay-2024", "(668), (673)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān dǎ-pò-le huāpíng."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("dǎ-pò-le", "hit-break-PFV"), ("huāpíng", "vase")]
    context := "A transitive V-V resultative whose result verb is an intransitive change-of-state verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def all : List Datum := [ex_41, ex_42, ex_45, ex_46, ex_107, ex_131, ex_132, ex_133, ex_134, ex_137, ex_139, ex_146, ex_148, ex_149, ex_150, ex_151, ex_202, ex_205, ex_206, ex_216, ex_217, ex_219, ex_221, ex_224, ex_330, ex_668]

end Tay2024.Examples
