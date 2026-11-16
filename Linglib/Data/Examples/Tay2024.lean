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
    glossedWords := [⟨[['B', 'ǎ', 'o', 'b', 'a', 'o']], [['b', 'a', 'b', 'y']]⟩, ⟨[['f', 'ǎ', 'n', 'f', 'ǎ', 'n', 'f', 'ù', 'f', 'ù', 'd', 'e']], [['r', 'e', 'p', 'e', 'a', 't', 'e', 'd', 'l', 'y']]⟩, ⟨[['k', 'ū']], [['c', 'r', 'y']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['m', 'ā', 'm', 'a']], [['m', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['x', 'ǐ', 'n', 'g'], ['l', 'e']], [['a', 'w', 'a', 'k', 'e'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['B', 'ǎ', 'o', 'b', 'a', 'o']], [['b', 'a', 'b', 'y']]⟩, ⟨[['f', 'ǎ', 'n', 'f', 'ǎ', 'n', 'f', 'ù', 'f', 'ù', 'd', 'e']], [['r', 'e', 'p', 'e', 'a', 't', 'e', 'd', 'l', 'y']]⟩, ⟨[['k', 'ū'], ['x', 'ǐ', 'n', 'g'], ['l', 'e']], [['c', 'r', 'y'], ['a', 'w', 'a', 'k', 'e'], ['P', 'F', 'V']]⟩, ⟨[['m', 'ā', 'm', 'a']], [['m', 'o', 't', 'h', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['B', 'ǎ', 'o', 'b', 'a', 'o']], [['b', 'a', 'b', 'y']]⟩, ⟨[['z', 'à', 'i']], [['a', 't']]⟩, ⟨[['j', 'i', 'ā']], [['h', 'o', 'u', 's', 'e']]⟩, ⟨[['l', 'ǐ']], [['i', 'n', 's', 'i', 'd', 'e']]⟩, ⟨[['k', 'ū']], [['c', 'r', 'y']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['l', 'í', 'n', 'j', 'ū']], [['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r']]⟩, ⟨[['x', 'ǐ', 'n', 'g'], ['l', 'e']], [['a', 'w', 'a', 'k', 'e'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['B', 'ǎ', 'o', 'b', 'a', 'o']], [['b', 'a', 'b', 'y']]⟩, ⟨[['z', 'à', 'i']], [['a', 't']]⟩, ⟨[['j', 'i', 'ā']], [['h', 'o', 'u', 's', 'e']]⟩, ⟨[['l', 'ǐ']], [['i', 'n', 's', 'i', 'd', 'e']]⟩, ⟨[['k', 'ū'], ['x', 'ǐ', 'n', 'g'], ['l', 'e']], [['c', 'r', 'y'], ['a', 'w', 'a', 'k', 'e'], ['P', 'F', 'V']]⟩, ⟨[['l', 'í', 'n', 'j', 'ū']], [['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['s', 'h', 'è'], ['s', 'ǐ'], ['l', 'e']], [['s', 'h', 'o', 'o', 't'], ['d', 'i', 'e'], ['P', 'F', 'V']]⟩, ⟨[['L', 'ǐ', 's', 'ì']], [['L', 'i', 's', 'i']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['B', 'ǎ', 'o', 'b', 'a', 'o']], [['b', 'a', 'b', 'y']]⟩, ⟨[['k', 'ū'], ['x', 'ǐ', 'n', 'g'], ['l', 'e']], [['c', 'r', 'y'], ['a', 'w', 'a', 'k', 'e'], ['P', 'F', 'V']]⟩, ⟨[['m', 'ā', 'm', 'a']], [['m', 'o', 't', 'h', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['W', 'ǒ']], [['I']]⟩, ⟨[['q', 'i', 'ē'], ['s', 'u', 'ì'], ['l', 'e']], [['c', 'u', 't'], ['i', 'n', '.', 'p', 'i', 'e', 'c', 'e', 's'], ['P', 'F', 'V']]⟩, ⟨[['y', 'á', 'n', 'g', 'c', 'ō', 'n', 'g']], [['o', 'n', 'i', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['M', 'ì', 'y', 'ǔ']], [['d', 'e', 'n', 's', 'e', '.', 'r', 'a', 'i', 'n']]⟩, ⟨[['x', 'i', 'à'], ['h', 'ē', 'i'], ['l', 'e']], [['f', 'a', 'l', 'l'], ['b', 'l', 'a', 'c', 'k'], ['P', 'F', 'V']]⟩, ⟨[['t', 'i', 'ā', 'n', 'd', 'ì']], [['e', 'a', 'r', 't', 'h']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Y', 'ī', 'f', 'ú']], [['c', 'l', 'o', 't', 'h', 'e', 's']]⟩, ⟨[['x', 'ǐ'], ['l', 'è', 'i'], ['l', 'e']], [['w', 'a', 's', 'h'], ['t', 'i', 'r', 'e', 'd'], ['P', 'F', 'V']]⟩, ⟨[['j', 'i', 'ě', 'j', 'i', 'ě']], [['e', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['É', 'j', 'ū', 'n']], [['R', 'u', 's', 's', 'i', 'a', 'n', '.', 'f', 'o', 'r', 'c', 'e', 's']]⟩, ⟨[['j', 'ī'], ['c', 'h', 'é', 'n'], ['l', 'e']], [['s', 't', 'r', 'i', 'k', 'e'], ['s', 'i', 'n', 'k'], ['P', 'F', 'V']]⟩, ⟨[['y', 'ī']], [['o', 'n', 'e']]⟩, ⟨[['s', 'ō', 'u']], [['C', 'L', 'F']]⟩, ⟨[['x', 'ú', 'n', 'y', 'á', 'n', 'g', 'j', 'i', 'à', 'n']], [['c', 'r', 'u', 'i', 's', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['É', 'j', 'ū', 'n']], [['R', 'u', 's', 's', 'i', 'a', 'n', '.', 'f', 'o', 'r', 'c', 'e', 's']]⟩, ⟨[['c', 'h', 'ō', 'n', 'g'], ['c', 'h', 'é', 'n'], ['l', 'e']], [['r', 'u', 's', 'h'], ['s', 'i', 'n', 'k'], ['P', 'F', 'V']]⟩, ⟨[['y', 'ī']], [['o', 'n', 'e']]⟩, ⟨[['s', 'ō', 'u']], [['C', 'L', 'F']]⟩, ⟨[['x', 'ú', 'n', 'y', 'á', 'n', 'g', 'j', 'i', 'à', 'n']], [['c', 'r', 'u', 'i', 's', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['J', 'i', 'à', 'o', 'l', 'i', 'à', 'n']], [['c', 'o', 'a', 'c', 'h']]⟩, ⟨[['z', 'ǒ', 'u'], ['l', 'è', 'i'], ['l', 'e']], [['w', 'a', 'l', 'k'], ['t', 'i', 'r', 'e', 'd'], ['P', 'F', 'V']]⟩, ⟨[['J', 'o', 'h', 'n']], [['J', 'o', 'h', 'n']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['l', 'i', 'è'], ['k', 'ā', 'i'], ['l', 'e']], [['c', 'r', 'a', 'c', 'k'], ['o', 'p', 'e', 'n'], ['P', 'F', 'V']]⟩, ⟨[['j', 'ī', 'd', 'à', 'n']], [['e', 'g', 'g']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Q', 'i', 'ē', 'c', 'à', 'i', 'b', 'ǎ', 'n']], [['c', 'u', 't', 't', 'i', 'n', 'g', '.', 'b', 'o', 'a', 'r', 'd']]⟩, ⟨[['q', 'i', 'ē'], ['d', 'ù', 'n'], ['l', 'e']], [['c', 'u', 't'], ['d', 'u', 'l', 'l'], ['P', 'F', 'V']]⟩, ⟨[['w', 'ǒ']], [['1', 'S', 'G']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['c', 'à', 'i', 'd', 'ā', 'o']], [['k', 'n', 'i', 'f', 'e']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'è']], [['t', 'h', 'i', 's']]⟩, ⟨[['b', 'ù']], [['C', 'L', 'F']]⟩, ⟨[['d', 'i', 'à', 'n', 'y', 'ǐ', 'n', 'g']], [['m', 'o', 'v', 'i', 'e']]⟩, ⟨[['k', 'ū'], ['h', 'ó', 'n', 'g'], ['l', 'e']], [['c', 'r', 'y'], ['r', 'e', 'd'], ['P', 'F', 'V']]⟩, ⟨[['w', 'ǒ']], [['1', 'S', 'G']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['y', 'ǎ', 'n', 'j', 'ī', 'n', 'g']], [['e', 'y', 'e']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['N', 'è', 'i']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e']], [['C', 'L', 'F']]⟩, ⟨[['x', 'i', 'à', 'o', 'h', 'u', 'à']], [['j', 'o', 'k', 'e']]⟩, ⟨[['x', 'i', 'à', 'o'], ['t', 'é', 'n', 'g'], ['l', 'e']], [['l', 'a', 'u', 'g', 'h'], ['h', 'u', 'r', 't'], ['P', 'F', 'V']]⟩, ⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['d', 'ù', 'z', 'i']], [['b', 'e', 'l', 'l', 'y']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['W', 'ǒ']], [['I']]⟩, ⟨[['q', 'i', 'ē'], ['d', 'ù', 'n'], ['l', 'e']], [['c', 'u', 't'], ['d', 'u', 'l', 'l'], ['P', 'F', 'V']]⟩, ⟨[['c', 'à', 'i', 'd', 'ā', 'o']], [['k', 'n', 'i', 'f', 'e']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'è']], [['t', 'h', 'i', 's']]⟩, ⟨[['d', 'ù', 'n']], [['C', 'L', 'F']]⟩, ⟨[['f', 'à', 'n']], [['m', 'e', 'a', 'l']]⟩, ⟨[['c', 'h', 'ī'], ['q', 'i', 'ó', 'n', 'g'], ['l', 'e']], [['e', 'a', 't'], ['p', 'o', 'o', 'r'], ['P', 'F', 'V']]⟩, ⟨[['w', 'ǒ']], [['m', 'e']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'è']], [['t', 'h', 'i', 's']]⟩, ⟨[['s', 'h', 'ǒ', 'u']], [['C', 'L', 'F']]⟩, ⟨[['g', 'ē']], [['s', 'o', 'n', 'g']]⟩, ⟨[['c', 'h', 'à', 'n', 'g'], ['k', 'ū'], ['l', 'e']], [['s', 'i', 'n', 'g'], ['c', 'r', 'y'], ['P', 'F', 'V']]⟩, ⟨[['g', 'u', 'ā', 'n', 'z', 'h', 'ò', 'n', 'g']], [['a', 'u', 'd', 'i', 'e', 'n', 'c', 'e']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Y', 'ī', 'f', 'ú']], [['c', 'l', 'o', 't', 'h', 'e', 's']]⟩, ⟨[['x', 'ǐ'], ['g', 'ā', 'n', 'j', 'ì', 'n', 'g'], ['l', 'e']], [['w', 'a', 's', 'h'], ['c', 'l', 'e', 'a', 'n'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['W', 'ǒ']], [['1', 'S', 'G']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['c', 'à', 'i', 'd', 'ā', 'o']], [['k', 'n', 'i', 'f', 'e']]⟩, ⟨[['q', 'i', 'ē'], ['d', 'ù', 'n'], ['l', 'e']], [['c', 'u', 't'], ['d', 'u', 'l', 'l'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['k', 'ū'], ['l', 'è', 'i'], ['l', 'e']], [['c', 'r', 'y'], ['t', 'i', 'r', 'e', 'd'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['S', 'h', 'ǒ', 'u', 'j', 'u', 'ǎ', 'n']], [['h', 'a', 'n', 'd', 'k', 'e', 'r', 'c', 'h', 'i', 'e', 'f']]⟩, ⟨[['k', 'ū'], ['s', 'h', 'ī'], ['l', 'e']], [['c', 'r', 'y'], ['w', 'e', 't'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['M', 'ā', 'm', 'a']], [['m', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['k', 'ū'], ['x', 'ǐ', 'n', 'g'], ['l', 'e']], [['c', 'r', 'y'], ['a', 'w', 'a', 'k', 'e'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['q', 'í'], ['l', 'è', 'i'], ['l', 'e']], [['r', 'i', 'd', 'e'], ['t', 'i', 'r', 'e', 'd'], ['P', 'F', 'V']]⟩, ⟨[['m', 'ǎ']], [['h', 'o', 'r', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['d', 'ǎ'], ['p', 'ò'], ['l', 'e']], [['h', 'i', 't'], ['b', 'r', 'e', 'a', 'k'], ['P', 'F', 'V']]⟩, ⟨[['h', 'u', 'ā', 'p', 'í', 'n', 'g']], [['v', 'a', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A transitive V-V resultative whose result verb is an intransitive change-of-state verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def all : List Datum := [ex_41, ex_42, ex_45, ex_46, ex_107, ex_131, ex_132, ex_133, ex_134, ex_137, ex_139, ex_146, ex_148, ex_149, ex_150, ex_151, ex_202, ex_205, ex_206, ex_216, ex_217, ex_219, ex_221, ex_224, ex_330, ex_668]

end Tay2024.Examples
