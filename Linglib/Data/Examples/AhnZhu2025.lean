module

public import Linglib.Data.Examples.Schema

/-!
# `AhnZhu2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AhnZhu2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AhnZhu2025.Examples`.
-/

@[expose] public section

namespace AhnZhu2025.Examples

def ex14a_bare : Datum :=
  { id := "ahnzhu2025_ex14a_bare"
    source := ⟨"ahn-zhu-2025", "(14a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "gou yao guo malu."
    glossedTokens := [("gou", "dog"), ("yao", "want"), ("guo", "cross"), ("malu", "road")]
    glossedWords := [⟨[['g', 'o', 'u']], [['d', 'o', 'g']]⟩, ⟨[['y', 'a', 'o']], [['w', 'a', 'n', 't']]⟩, ⟨[['g', 'u', 'o']], [['c', 'r', 'o', 's', 's']]⟩, ⟨[['m', 'a', 'l', 'u']], [['r', 'o', 'a', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := "Out of the blue; the bare noun read as definite."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "none")] }

def ex14b_na : Datum :=
  { id := "ahnzhu2025_ex14b_na"
    source := ⟨"ahn-zhu-2025", "(14b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "na tiao gou yao guo malu."
    glossedTokens := [("na", "that"), ("tiao", "CL"), ("gou", "dog"), ("yao", "want"), ("guo", "cross"), ("malu", "road")]
    glossedWords := [⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['t', 'i', 'a', 'o']], [['C', 'L']]⟩, ⟨[['g', 'o', 'u']], [['d', 'o', 'g']]⟩, ⟨[['y', 'a', 'o']], [['w', 'a', 'n', 't']]⟩, ⟨[['g', 'u', 'o']], [['c', 'r', 'o', 's', 's']]⟩, ⟨[['m', 'a', 'l', 'u']], [['r', 'o', 'a', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := "Out of the blue; na-CL-N as the demonstrative description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "none")] }

def ex17_partwhole_bare : Datum :=
  { id := "ahnzhu2025_ex17_partwhole_bare"
    source := ⟨"jenks-2018", "(14a)"⟩
    reportedIn := some ⟨"ahn-zhu-2025", "(17)"⟩
    language := "mand1415"
    primaryText := "chezi bei jingcha lanjie le yinwei mei you tiezhi zai paizhao shang."
    glossedTokens := [("chezi", "car"), ("bei", "PASS"), ("jingcha", "police"), ("lanjie", "intercept"), ("le", "ASP"), ("yinwei", "because"), ("mei", "NEG"), ("you", "have"), ("tiezhi", "sticker"), ("zai", "at"), ("paizhao", "license.plate"), ("shang", "on")]
    glossedWords := [⟨[['c', 'h', 'e', 'z', 'i']], [['c', 'a', 'r']]⟩, ⟨[['b', 'e', 'i']], [['P', 'A', 'S', 'S']]⟩, ⟨[['j', 'i', 'n', 'g', 'c', 'h', 'a']], [['p', 'o', 'l', 'i', 'c', 'e']]⟩, ⟨[['l', 'a', 'n', 'j', 'i', 'e']], [['i', 'n', 't', 'e', 'r', 'c', 'e', 'p', 't']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['y', 'i', 'n', 'w', 'e', 'i']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['m', 'e', 'i']], [['N', 'E', 'G']]⟩, ⟨[['y', 'o', 'u']], [['h', 'a', 'v', 'e']]⟩, ⟨[['t', 'i', 'e', 'z', 'h', 'i']], [['s', 't', 'i', 'c', 'k', 'e', 'r']]⟩, ⟨[['z', 'a', 'i']], [['a', 't']]⟩, ⟨[['p', 'a', 'i', 'z', 'h', 'a', 'o']], [['l', 'i', 'c', 'e', 'n', 's', 'e', '.', 'p', 'l', 'a', 't', 'e']]⟩, ⟨[['s', 'h', 'a', 'n', 'g']], [['o', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := "Part-whole bridging from 'car' to its license plate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "none")] }

def ex18_anaphoric_na : Datum :=
  { id := "ahnzhu2025_ex18_anaphoric_na"
    source := ⟨"jenks-2018", "(15a), (15b)"⟩
    reportedIn := some ⟨"ahn-zhu-2025", "(18)"⟩
    language := "mand1415"
    primaryText := "jiaoshi li zuo-zhe yi ge nansheng he yi ge nüsheng. wo zuotian yudao na ge nansheng."
    glossedTokens := [("jiaoshi", "classroom"), ("li", "inside"), ("zuo-zhe", "sit-PROG"), ("yi", "one"), ("ge", "CL"), ("nansheng", "boy"), ("he", "and"), ("yi", "one"), ("ge", "CL"), ("nüsheng", "girl"), ("wo", "I"), ("zuotian", "yesterday"), ("yudao", "meet"), ("na", "that"), ("ge", "CL"), ("nansheng", "boy")]
    glossedWords := [⟨[['j', 'i', 'a', 'o', 's', 'h', 'i']], [['c', 'l', 'a', 's', 's', 'r', 'o', 'o', 'm']]⟩, ⟨[['l', 'i']], [['i', 'n', 's', 'i', 'd', 'e']]⟩, ⟨[['z', 'u', 'o'], ['z', 'h', 'e']], [['s', 'i', 't'], ['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['n', 'a', 'n', 's', 'h', 'e', 'n', 'g']], [['b', 'o', 'y']]⟩, ⟨[['h', 'e']], [['a', 'n', 'd']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['n', 'ü', 's', 'h', 'e', 'n', 'g']], [['g', 'i', 'r', 'l']]⟩, ⟨[['w', 'o']], [['I']]⟩, ⟨[['z', 'u', 'o', 't', 'i', 'a', 'n']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['y', 'u', 'd', 'a', 'o']], [['m', 'e', 'e', 't']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['n', 'a', 'n', 's', 'h', 'e', 'n', 'g']], [['b', 'o', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anaphoric reference to a boy introduced by an indefinite in the previous sentence."
    judgment := .acceptable
    alternatives := [("wo zuotian yudao nansheng.", .unacceptable)]
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "none"), ("use", "anaphoric")] }

def ex21_partwhole_na : Datum :=
  { id := "ahnzhu2025_ex21_partwhole_na"
    source := ⟨"ahn-zhu-2025", "(21)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "zixingche zai houyuan li, wo zhunbei qu ca yixia na ge chezuo."
    glossedTokens := [("zixingche", "bike"), ("zai", "at"), ("houyuan", "backyard"), ("li", "inside"), ("wo", "I"), ("zhunbei", "plan"), ("qu", "go"), ("ca", "wipe"), ("yixia", "once"), ("na", "that"), ("ge", "CL"), ("chezuo", "seat")]
    glossedWords := [⟨[['z', 'i', 'x', 'i', 'n', 'g', 'c', 'h', 'e']], [['b', 'i', 'k', 'e']]⟩, ⟨[['z', 'a', 'i']], [['a', 't']]⟩, ⟨[['h', 'o', 'u', 'y', 'u', 'a', 'n']], [['b', 'a', 'c', 'k', 'y', 'a', 'r', 'd']]⟩, ⟨[['l', 'i']], [['i', 'n', 's', 'i', 'd', 'e']]⟩, ⟨[['w', 'o']], [['I']]⟩, ⟨[['z', 'h', 'u', 'n', 'b', 'e', 'i']], [['p', 'l', 'a', 'n']]⟩, ⟨[['q', 'u']], [['g', 'o']]⟩, ⟨[['c', 'a']], [['w', 'i', 'p', 'e']]⟩, ⟨[['y', 'i', 'x', 'i', 'a']], [['o', 'n', 'c', 'e']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['c', 'h', 'e', 'z', 'u', 'o']], [['s', 'e', 'a', 't']]⟩]
    lgrConformance := some .wordAligned
    context := "Part-whole bridging: the minimal situation with the bike contains a unique seat."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "none")] }

def ex22_relational_na : Datum :=
  { id := "ahnzhu2025_ex22_relational_na"
    source := ⟨"ahn-zhu-2025", "(22)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "zuotian wo mai le shu. wo hen xiang jianjian na wei zuozhe."
    glossedTokens := [("zuotian", "yesterday"), ("wo", "I"), ("mai", "buy"), ("le", "ASP"), ("shu", "book"), ("wo", "I"), ("hen", "very"), ("xiang", "want"), ("jianjian", "meet"), ("na", "that"), ("wei", "CL"), ("zuozhe", "author")]
    glossedWords := [⟨[['z', 'u', 'o', 't', 'i', 'a', 'n']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['w', 'o']], [['I']]⟩, ⟨[['m', 'a', 'i']], [['b', 'u', 'y']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['s', 'h', 'u']], [['b', 'o', 'o', 'k']]⟩, ⟨[['w', 'o']], [['I']]⟩, ⟨[['h', 'e', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['x', 'i', 'a', 'n', 'g']], [['w', 'a', 'n', 't']]⟩, ⟨[['j', 'i', 'a', 'n', 'j', 'i', 'a', 'n']], [['m', 'e', 'e', 't']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['w', 'e', 'i']], [['C', 'L']]⟩, ⟨[['z', 'u', 'o', 'z', 'h', 'e']], [['a', 'u', 't', 'h', 'o', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := "Relational bridging: the author is not contained in the situation of buying the book, so situational uniqueness cannot resolve reference."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "none")] }

def ex24a_de_child : Datum :=
  { id := "ahnzhu2025_ex24a_de_child"
    source := ⟨"ahn-zhu-2025", "(24a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "mou-ren de haizi"
    glossedTokens := [("mou-ren", "some-person"), ("de", "DE"), ("haizi", "child")]
    glossedWords := [⟨[['m', 'o', 'u'], ['r', 'e', 'n']], [['s', 'o', 'm', 'e'], ['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['h', 'a', 'i', 'z', 'i']], [['c', 'h', 'i', 'l', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The de-possessive diagnostic for relational nouns."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "relational"), ("diagnostic", "de")] }

def ex24b_de_person : Datum :=
  { id := "ahnzhu2025_ex24b_de_person"
    source := ⟨"ahn-zhu-2025", "(24b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "mou-ren de ren"
    glossedTokens := [("mou-ren", "some-person"), ("de", "DE"), ("ren", "person")]
    glossedWords := [⟨[['m', 'o', 'u'], ['r', 'e', 'n']], [['s', 'o', 'm', 'e'], ['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['r', 'e', 'n']], [['p', 'e', 'r', 's', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The de-possessive diagnostic for relational nouns."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "sortal"), ("diagnostic", "de")] }

def ex25_de_flower : Datum :=
  { id := "ahnzhu2025_ex25_de_flower"
    source := ⟨"ahn-zhu-2025", "(25)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "mou-ren de hua"
    glossedTokens := [("mou-ren", "some-person"), ("de", "DE"), ("hua", "flower")]
    glossedWords := [⟨[['m', 'o', 'u'], ['r', 'e', 'n']], [['s', 'o', 'm', 'e'], ['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['h', 'u', 'a']], [['f', 'l', 'o', 'w', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The de-possessive diagnostic for relational nouns."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "sortal"), ("diagnostic", "de")] }

def ex28a_study1_partwhole_na : Datum :=
  { id := "ahnzhu2025_ex28a_study1_partwhole_na"
    source := ⟨"ahn-zhu-2025", "(28a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Chen Haoran ba zixingche ting zai le houyuan, jieguo ta de gou zhua-po le na ge chezuo."
    glossedTokens := [("Chen", "Chen"), ("Haoran", "Haoran"), ("ba", "BA"), ("zixingche", "bike"), ("ting", "park"), ("zai", "at"), ("le", "ASP"), ("houyuan", "backyard"), ("jieguo", "as.a.result"), ("ta", "he"), ("de", "POSS"), ("gou", "dog"), ("zhua-po", "scratch-break"), ("le", "ASP"), ("na", "that"), ("ge", "CL"), ("chezuo", "seat")]
    glossedWords := [⟨[['C', 'h', 'e', 'n']], [['C', 'h', 'e', 'n']]⟩, ⟨[['H', 'a', 'o', 'r', 'a', 'n']], [['H', 'a', 'o', 'r', 'a', 'n']]⟩, ⟨[['b', 'a']], [['B', 'A']]⟩, ⟨[['z', 'i', 'x', 'i', 'n', 'g', 'c', 'h', 'e']], [['b', 'i', 'k', 'e']]⟩, ⟨[['t', 'i', 'n', 'g']], [['p', 'a', 'r', 'k']]⟩, ⟨[['z', 'a', 'i']], [['a', 't']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['h', 'o', 'u', 'y', 'u', 'a', 'n']], [['b', 'a', 'c', 'k', 'y', 'a', 'r', 'd']]⟩, ⟨[['j', 'i', 'e', 'g', 'u', 'o']], [['a', 's', '.', 'a', '.', 'r', 'e', 's', 'u', 'l', 't']]⟩, ⟨[['t', 'a']], [['h', 'e']]⟩, ⟨[['d', 'e']], [['P', 'O', 'S', 'S']]⟩, ⟨[['g', 'o', 'u']], [['d', 'o', 'g']]⟩, ⟨[['z', 'h', 'u', 'a'], ['p', 'o']], [['s', 'c', 'r', 'a', 't', 'c', 'h'], ['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['c', 'h', 'e', 'z', 'u', 'o']], [['s', 'e', 'a', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 1 target item (bike, seat): the seat is uniquely identified as a part of the bike."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "1")] }

def ex28b_study1_relational_bare : Datum :=
  { id := "ahnzhu2025_ex28b_study1_relational_bare"
    source := ⟨"ahn-zhu-2025", "(28b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Chen Yue shang-zhou mai-lai le changpian, ta mei-tian dou xiang-zhe qu zhao geshou qian-ming."
    glossedTokens := [("Chen", "Chen"), ("Yue", "Yue"), ("shang-zhou", "last-week"), ("mai-lai", "buy-come"), ("le", "ASP"), ("changpian", "CD"), ("ta", "she"), ("mei-tian", "every-day"), ("dou", "DOU"), ("xiang-zhe", "think-PROG"), ("qu", "go"), ("zhao", "find"), ("geshou", "singer"), ("qian-ming", "sign-name")]
    glossedWords := [⟨[['C', 'h', 'e', 'n']], [['C', 'h', 'e', 'n']]⟩, ⟨[['Y', 'u', 'e']], [['Y', 'u', 'e']]⟩, ⟨[['s', 'h', 'a', 'n', 'g'], ['z', 'h', 'o', 'u']], [['l', 'a', 's', 't'], ['w', 'e', 'e', 'k']]⟩, ⟨[['m', 'a', 'i'], ['l', 'a', 'i']], [['b', 'u', 'y'], ['c', 'o', 'm', 'e']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['c', 'h', 'a', 'n', 'g', 'p', 'i', 'a', 'n']], [['C', 'D']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['m', 'e', 'i'], ['t', 'i', 'a', 'n']], [['e', 'v', 'e', 'r', 'y'], ['d', 'a', 'y']]⟩, ⟨[['d', 'o', 'u']], [['D', 'O', 'U']]⟩, ⟨[['x', 'i', 'a', 'n', 'g'], ['z', 'h', 'e']], [['t', 'h', 'i', 'n', 'k'], ['P', 'R', 'O', 'G']]⟩, ⟨[['q', 'u']], [['g', 'o']]⟩, ⟨[['z', 'h', 'a', 'o']], [['f', 'i', 'n', 'd']]⟩, ⟨[['g', 'e', 's', 'h', 'o', 'u']], [['s', 'i', 'n', 'g', 'e', 'r']]⟩, ⟨[['q', 'i', 'a', 'n'], ['m', 'i', 'n', 'g']], [['s', 'i', 'g', 'n'], ['n', 'a', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 1 target item (CD, singer): one-to-one association; the singer is not physically contained in the CD."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "1")] }

def ex32_study1_painter : Datum :=
  { id := "ahnzhu2025_ex32_study1_painter"
    source := ⟨"ahn-zhu-2025", "(32)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhou Yuxuan jia-li gua-zhe youhua, dan ta wanquan bu renshi na ge huajia."
    glossedTokens := [("Zhou", "Zhou"), ("Yuxuan", "Yuxuan"), ("jia-li", "home-in"), ("gua-zhe", "hang-PROG"), ("youhua", "painting"), ("dan", "but"), ("ta", "he"), ("wanquan", "totally"), ("bu", "NEG"), ("renshi", "know"), ("na", "DEM"), ("ge", "CL"), ("huajia", "painter")]
    glossedWords := [⟨[['Z', 'h', 'o', 'u']], [['Z', 'h', 'o', 'u']]⟩, ⟨[['Y', 'u', 'x', 'u', 'a', 'n']], [['Y', 'u', 'x', 'u', 'a', 'n']]⟩, ⟨[['j', 'i', 'a'], ['l', 'i']], [['h', 'o', 'm', 'e'], ['i', 'n']]⟩, ⟨[['g', 'u', 'a'], ['z', 'h', 'e']], [['h', 'a', 'n', 'g'], ['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'u', 'h', 'u', 'a']], [['p', 'a', 'i', 'n', 't', 'i', 'n', 'g']]⟩, ⟨[['d', 'a', 'n']], [['b', 'u', 't']]⟩, ⟨[['t', 'a']], [['h', 'e']]⟩, ⟨[['w', 'a', 'n', 'q', 'u', 'a', 'n']], [['t', 'o', 't', 'a', 'l', 'l', 'y']]⟩, ⟨[['b', 'u']], [['N', 'E', 'G']]⟩, ⟨[['r', 'e', 'n', 's', 'h', 'i']], [['k', 'n', 'o', 'w']]⟩, ⟨[['n', 'a']], [['D', 'E', 'M']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['h', 'u', 'a', 'j', 'i', 'a']], [['p', 'a', 'i', 'n', 't', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 1 item REL2 (painting, painter), the only item where demonstratives were rated significantly higher than bare nouns (p = 0.02)."
    judgment := .acceptable
    alternatives := [("Zhou Yuxuan jia-li gua-zhe youhua, dan ta wanquan bu renshi huajia.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "1")] }

def ex33a_study1_steeringwheel : Datum :=
  { id := "ahnzhu2025_ex33a_study1_steeringwheel"
    source := ⟨"ahn-zhu-2025", "(33a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Lin Zixuan xin mai-le qiche, dan ta hen-kuai faxian you-ren touzou-le fangxiangpan."
    glossedTokens := [("Lin", "Lin"), ("Zixuan", "Zixuan"), ("xin", "new"), ("mai-le", "buy-ASP"), ("qiche", "car"), ("dan", "but"), ("ta", "he"), ("hen-kuai", "very-fast"), ("faxian", "discover"), ("you-ren", "have-person"), ("touzou-le", "steal.away-ASP"), ("fangxiangpan", "steering.wheel")]
    glossedWords := [⟨[['L', 'i', 'n']], [['L', 'i', 'n']]⟩, ⟨[['Z', 'i', 'x', 'u', 'a', 'n']], [['Z', 'i', 'x', 'u', 'a', 'n']]⟩, ⟨[['x', 'i', 'n']], [['n', 'e', 'w']]⟩, ⟨[['m', 'a', 'i'], ['l', 'e']], [['b', 'u', 'y'], ['A', 'S', 'P']]⟩, ⟨[['q', 'i', 'c', 'h', 'e']], [['c', 'a', 'r']]⟩, ⟨[['d', 'a', 'n']], [['b', 'u', 't']]⟩, ⟨[['t', 'a']], [['h', 'e']]⟩, ⟨[['h', 'e', 'n'], ['k', 'u', 'a', 'i']], [['v', 'e', 'r', 'y'], ['f', 'a', 's', 't']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r']]⟩, ⟨[['y', 'o', 'u'], ['r', 'e', 'n']], [['h', 'a', 'v', 'e'], ['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['t', 'o', 'u', 'z', 'o', 'u'], ['l', 'e']], [['s', 't', 'e', 'a', 'l', '.', 'a', 'w', 'a', 'y'], ['A', 'S', 'P']]⟩, ⟨[['f', 'a', 'n', 'g', 'x', 'i', 'a', 'n', 'g', 'p', 'a', 'n']], [['s', 't', 'e', 'e', 'r', 'i', 'n', 'g', '.', 'w', 'h', 'e', 'e', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 1 item PW1 (car, steering wheel), where bare nouns were rated significantly higher than demonstratives (p = 0.00134)."
    judgment := .acceptable
    alternatives := [("Lin Zixuan xin mai-le qiche, dan ta hen-kuai faxian you-ren touzou-le na ge fangxiangpan.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "1")] }

def ex37_study3_partwhole_bare : Datum :=
  { id := "ahnzhu2025_ex37_study3_partwhole_bare"
    source := ⟨"ahn-zhu-2025", "(37), option (38a) pingmu"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen zhengzai yong diannao. ta faxian pingmu haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("zhengzai", "PROG"), ("yong", "use"), ("diannao", "computer"), ("ta", "she"), ("faxian", "find"), ("pingmu", "screen"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'n', 'g']], [['u', 's', 'e']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['p', 'i', 'n', 'g', 'm', 'u']], [['s', 'c', 'r', 'e', 'e', 'n']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 production item: the background sentence introduces 'computer'; participants choose the nominal form filling the blank."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "3"), ("pct_chosen", "83.2")] }

def ex37_study3_partwhole_na : Datum :=
  { id := "ahnzhu2025_ex37_study3_partwhole_na"
    source := ⟨"ahn-zhu-2025", "(37), option (38a) na kuai pingmu"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen zhengzai yong diannao. ta faxian na kuai pingmu haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("zhengzai", "PROG"), ("yong", "use"), ("diannao", "computer"), ("ta", "she"), ("faxian", "find"), ("na", "that"), ("kuai", "CL"), ("pingmu", "screen"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'n', 'g']], [['u', 's', 'e']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['k', 'u', 'a', 'i']], [['C', 'L']]⟩, ⟨[['p', 'i', 'n', 'g', 'm', 'u']], [['s', 'c', 'r', 'e', 'e', 'n']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 production item, demonstrative option in the part-whole condition."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "3"), ("pct_chosen", "51.3")] }

def ex38_study3_relational_bare : Datum :=
  { id := "ahnzhu2025_ex38_study3_relational_bare"
    source := ⟨"ahn-zhu-2025", "(37), option (38b) chongdianqi"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen zhengzai yong diannao. ta faxian chongdianqi haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("zhengzai", "PROG"), ("yong", "use"), ("diannao", "computer"), ("ta", "she"), ("faxian", "find"), ("chongdianqi", "charger"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'n', 'g']], [['u', 's', 'e']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['c', 'h', 'o', 'n', 'g', 'd', 'i', 'a', 'n', 'q', 'i']], [['c', 'h', 'a', 'r', 'g', 'e', 'r']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 production item, relational condition: the computer is the relatum of the relational noun 'charger'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "3"), ("pct_chosen", "73.4")] }

def ex38_study3_relational_na : Datum :=
  { id := "ahnzhu2025_ex38_study3_relational_na"
    source := ⟨"ahn-zhu-2025", "(37), option (38b) na kuai chongdianqi"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen zhengzai yong diannao. ta faxian na kuai chongdianqi haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("zhengzai", "PROG"), ("yong", "use"), ("diannao", "computer"), ("ta", "she"), ("faxian", "find"), ("na", "that"), ("kuai", "CL"), ("chongdianqi", "charger"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'n', 'g']], [['u', 's', 'e']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['k', 'u', 'a', 'i']], [['C', 'L']]⟩, ⟨[['c', 'h', 'o', 'n', 'g', 'd', 'i', 'a', 'n', 'q', 'i']], [['c', 'h', 'a', 'r', 'g', 'e', 'r']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 production item, demonstrative option in the relational condition."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "3"), ("pct_chosen", "51.9")] }

def ex39_study3_sn : Datum :=
  { id := "ahnzhu2025_ex39_study3_sn"
    source := ⟨"ahn-zhu-2025", "(39)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen zhengzai yong yi tai diannao; ta faxian diannao haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("zhengzai", "PROG"), ("yong", "use"), ("yi", "one"), ("tai", "CL"), ("diannao", "computer"), ("ta", "she"), ("faxian", "find"), ("diannao", "computer"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'n', 'g']], [['u', 's', 'e']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['t', 'a', 'i']], [['C', 'L']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 SN control: a singular indefinite antecedent; the blank is filled by the same noun (bare or with na)."
    judgment := .acceptable
    alternatives := [("Wang Yawen zhengzai yong yi tai diannao; ta faxian na tai diannao haoxiang turan huai le.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "3"), ("condition", "SN"), ("pct_bn", "67"), ("pct_dem", "80.2")] }

def ex40_study3_pn : Datum :=
  { id := "ahnzhu2025_ex40_study3_pn"
    source := ⟨"ahn-zhu-2025", "(40)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen zhengzai yong liang tai diannao; ta faxian diannao haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("zhengzai", "PROG"), ("yong", "use"), ("liang", "two"), ("tai", "CL"), ("diannao", "computer"), ("ta", "she"), ("faxian", "find"), ("diannao", "computer"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'n', 'g']], [['u', 's', 'e']]⟩, ⟨[['l', 'i', 'a', 'n', 'g']], [['t', 'w', 'o']]⟩, ⟨[['t', 'a', 'i']], [['C', 'L']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 PN control: a plural indefinite antecedent, where neither singular form was expected to be chosen."
    judgment := .acceptable
    alternatives := [("Wang Yawen zhengzai yong liang tai diannao; ta faxian na tai diannao haoxiang turan huai le.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "3"), ("condition", "PN"), ("pct_bn", "53.8"), ("pct_dem", "38.8")] }

def ex41_study3_rn : Datum :=
  { id := "ahnzhu2025_ex41_study3_rn"
    source := ⟨"ahn-zhu-2025", "(41)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen zhengzai yong diannao; ta faxian diannao haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("zhengzai", "PROG"), ("yong", "use"), ("diannao", "computer"), ("ta", "she"), ("faxian", "find"), ("diannao", "computer"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['y', 'o', 'n', 'g']], [['u', 's', 'e']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 RN control: a bare-noun antecedent repeated in the test sentence."
    judgment := .acceptable
    alternatives := [("Wang Yawen zhengzai yong diannao; ta faxian na tai diannao haoxiang turan huai le.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "3"), ("condition", "RN"), ("pct_bn", "68"), ("pct_dem", "75")] }

def ex42_study3_nn : Datum :=
  { id := "ahnzhu2025_ex42_study3_nn"
    source := ⟨"ahn-zhu-2025", "(42)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen ganggang zai gongzuo; ta faxian diannao haoxiang turan huai le."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("ganggang", "just.now"), ("zai", "PROG"), ("gongzuo", "work"), ("ta", "she"), ("faxian", "find"), ("diannao", "computer"), ("haoxiang", "seem.to"), ("turan", "suddenly"), ("huai", "break"), ("le", "ASP")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['g', 'a', 'n', 'g', 'g', 'a', 'n', 'g']], [['j', 'u', 's', 't', '.', 'n', 'o', 'w']]⟩, ⟨[['z', 'a', 'i']], [['P', 'R', 'O', 'G']]⟩, ⟨[['g', 'o', 'n', 'g', 'z', 'u', 'o']], [['w', 'o', 'r', 'k']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['f', 'i', 'n', 'd']]⟩, ⟨[['d', 'i', 'a', 'n', 'n', 'a', 'o']], [['c', 'o', 'm', 'p', 'u', 't', 'e', 'r']]⟩, ⟨[['h', 'a', 'o', 'x', 'i', 'a', 'n', 'g']], [['s', 'e', 'e', 'm', '.', 't', 'o']]⟩, ⟨[['t', 'u', 'r', 'a', 'n']], [['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y']]⟩, ⟨[['h', 'u', 'a', 'i']], [['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Study 3 NN control: no nominal antecedent; a computer cannot be uniquely identified from the working situation."
    judgment := .acceptable
    alternatives := [("Wang Yawen ganggang zai gongzuo; ta faxian na tai diannao haoxiang turan huai le.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "3"), ("condition", "NN"), ("pct_bn", "89.5"), ("pct_dem", "29.6")] }

def ex59_study4_bare_author : Datum :=
  { id := "ahnzhu2025_ex59_study4_bare_author"
    source := ⟨"ahn-zhu-2025", "(59) zuozhe"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen xihuan shoucang tushu. ta mei-ci zhao-dao le yi ben xihuan de xiaoshuo, zuihou dou hui faxian ziji du-guo zuozhe xie de ling yi ge gushi."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("xihuan", "like"), ("shoucang", "collect"), ("tushu", "book"), ("ta", "she"), ("mei-ci", "every-time"), ("zhao-dao", "find-arrive"), ("le", "ASP"), ("yi", "one"), ("ben", "CL"), ("xihuan", "like"), ("de", "DE"), ("xiaoshuo", "novel"), ("zuihou", "finally"), ("dou", "always"), ("hui", "will"), ("faxian", "discover"), ("ziji", "self"), ("du-guo", "read-pass"), ("zuozhe", "author"), ("xie", "write"), ("de", "DE"), ("ling", "another"), ("yi", "one"), ("ge", "CL"), ("gushi", "story")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['s', 'h', 'o', 'u', 'c', 'a', 'n', 'g']], [['c', 'o', 'l', 'l', 'e', 'c', 't']]⟩, ⟨[['t', 'u', 's', 'h', 'u']], [['b', 'o', 'o', 'k']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['m', 'e', 'i'], ['c', 'i']], [['e', 'v', 'e', 'r', 'y'], ['t', 'i', 'm', 'e']]⟩, ⟨[['z', 'h', 'a', 'o'], ['d', 'a', 'o']], [['f', 'i', 'n', 'd'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['b', 'e', 'n']], [['C', 'L']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['z', 'u', 'i', 'h', 'o', 'u']], [['f', 'i', 'n', 'a', 'l', 'l', 'y']]⟩, ⟨[['d', 'o', 'u']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['h', 'u', 'i']], [['w', 'i', 'l', 'l']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r']]⟩, ⟨[['z', 'i', 'j', 'i']], [['s', 'e', 'l', 'f']]⟩, ⟨[['d', 'u'], ['g', 'u', 'o']], [['r', 'e', 'a', 'd'], ['p', 'a', 's', 's']]⟩, ⟨[['z', 'u', 'o', 'z', 'h', 'e']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['x', 'i', 'e']], [['w', 'r', 'i', 't', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['l', 'i', 'n', 'g']], [['a', 'n', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['g', 'u', 's', 'h', 'i']], [['s', 't', 'o', 'r', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 4 target: the bridged noun is the lexically relational zuozhe 'author', covarying with the novel."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "4")] }

def ex59_study4_na_author : Datum :=
  { id := "ahnzhu2025_ex59_study4_na_author"
    source := ⟨"ahn-zhu-2025", "(59) na wei zuozhe"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen xihuan shoucang tushu. ta mei-ci zhao-dao le yi ben xihuan de xiaoshuo, zuihou dou hui faxian ziji du-guo na wei zuozhe xie de ling yi ge gushi."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("xihuan", "like"), ("shoucang", "collect"), ("tushu", "book"), ("ta", "she"), ("mei-ci", "every-time"), ("zhao-dao", "find-arrive"), ("le", "ASP"), ("yi", "one"), ("ben", "CL"), ("xihuan", "like"), ("de", "DE"), ("xiaoshuo", "novel"), ("zuihou", "finally"), ("dou", "always"), ("hui", "will"), ("faxian", "discover"), ("ziji", "self"), ("du-guo", "read-pass"), ("na", "that"), ("wei", "CL"), ("zuozhe", "author"), ("xie", "write"), ("de", "DE"), ("ling", "another"), ("yi", "one"), ("ge", "CL"), ("gushi", "story")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['s', 'h', 'o', 'u', 'c', 'a', 'n', 'g']], [['c', 'o', 'l', 'l', 'e', 'c', 't']]⟩, ⟨[['t', 'u', 's', 'h', 'u']], [['b', 'o', 'o', 'k']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['m', 'e', 'i'], ['c', 'i']], [['e', 'v', 'e', 'r', 'y'], ['t', 'i', 'm', 'e']]⟩, ⟨[['z', 'h', 'a', 'o'], ['d', 'a', 'o']], [['f', 'i', 'n', 'd'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['b', 'e', 'n']], [['C', 'L']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['z', 'u', 'i', 'h', 'o', 'u']], [['f', 'i', 'n', 'a', 'l', 'l', 'y']]⟩, ⟨[['d', 'o', 'u']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['h', 'u', 'i']], [['w', 'i', 'l', 'l']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r']]⟩, ⟨[['z', 'i', 'j', 'i']], [['s', 'e', 'l', 'f']]⟩, ⟨[['d', 'u'], ['g', 'u', 'o']], [['r', 'e', 'a', 'd'], ['p', 'a', 's', 's']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['w', 'e', 'i']], [['C', 'L']]⟩, ⟨[['z', 'u', 'o', 'z', 'h', 'e']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['x', 'i', 'e']], [['w', 'r', 'i', 't', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['l', 'i', 'n', 'g']], [['a', 'n', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['g', 'u', 's', 'h', 'i']], [['s', 't', 'o', 'r', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 4 target: demonstrative with the relational noun."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "4")] }

def ex59_study4_bare_novelist : Datum :=
  { id := "ahnzhu2025_ex59_study4_bare_novelist"
    source := ⟨"ahn-zhu-2025", "(59) xiaoshuo-jia"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen xihuan shoucang tushu. ta mei-ci zhao-dao le yi ben xihuan de xiaoshuo, zuihou dou hui faxian ziji du-guo xiaoshuo-jia xie de ling yi ge gushi."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("xihuan", "like"), ("shoucang", "collect"), ("tushu", "book"), ("ta", "she"), ("mei-ci", "every-time"), ("zhao-dao", "find-arrive"), ("le", "ASP"), ("yi", "one"), ("ben", "CL"), ("xihuan", "like"), ("de", "DE"), ("xiaoshuo", "novel"), ("zuihou", "finally"), ("dou", "always"), ("hui", "will"), ("faxian", "discover"), ("ziji", "self"), ("du-guo", "read-pass"), ("xiaoshuo-jia", "novel-person"), ("xie", "write"), ("de", "DE"), ("ling", "another"), ("yi", "one"), ("ge", "CL"), ("gushi", "story")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['s', 'h', 'o', 'u', 'c', 'a', 'n', 'g']], [['c', 'o', 'l', 'l', 'e', 'c', 't']]⟩, ⟨[['t', 'u', 's', 'h', 'u']], [['b', 'o', 'o', 'k']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['m', 'e', 'i'], ['c', 'i']], [['e', 'v', 'e', 'r', 'y'], ['t', 'i', 'm', 'e']]⟩, ⟨[['z', 'h', 'a', 'o'], ['d', 'a', 'o']], [['f', 'i', 'n', 'd'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['b', 'e', 'n']], [['C', 'L']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['z', 'u', 'i', 'h', 'o', 'u']], [['f', 'i', 'n', 'a', 'l', 'l', 'y']]⟩, ⟨[['d', 'o', 'u']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['h', 'u', 'i']], [['w', 'i', 'l', 'l']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r']]⟩, ⟨[['z', 'i', 'j', 'i']], [['s', 'e', 'l', 'f']]⟩, ⟨[['d', 'u'], ['g', 'u', 'o']], [['r', 'e', 'a', 'd'], ['p', 'a', 's', 's']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o'], ['j', 'i', 'a']], [['n', 'o', 'v', 'e', 'l'], ['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['x', 'i', 'e']], [['w', 'r', 'i', 't', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['l', 'i', 'n', 'g']], [['a', 'n', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['g', 'u', 's', 'h', 'i']], [['s', 't', 'o', 'r', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 4 target: the bridged noun is the non-relational xiaoshuo-jia 'novelist', which fails the de diagnostic."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "relational"), ("noun_arity", "sortal"), ("study", "4")] }

def ex59_study4_na_novelist : Datum :=
  { id := "ahnzhu2025_ex59_study4_na_novelist"
    source := ⟨"ahn-zhu-2025", "(59) na wei xiaoshuo-jia"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen xihuan shoucang tushu. ta mei-ci zhao-dao le yi ben xihuan de xiaoshuo, zuihou dou hui faxian ziji du-guo na wei xiaoshuo-jia xie de ling yi ge gushi."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("xihuan", "like"), ("shoucang", "collect"), ("tushu", "book"), ("ta", "she"), ("mei-ci", "every-time"), ("zhao-dao", "find-arrive"), ("le", "ASP"), ("yi", "one"), ("ben", "CL"), ("xihuan", "like"), ("de", "DE"), ("xiaoshuo", "novel"), ("zuihou", "finally"), ("dou", "always"), ("hui", "will"), ("faxian", "discover"), ("ziji", "self"), ("du-guo", "read-pass"), ("na", "that"), ("wei", "CL"), ("xiaoshuo-jia", "novel-person"), ("xie", "write"), ("de", "DE"), ("ling", "another"), ("yi", "one"), ("ge", "CL"), ("gushi", "story")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['s', 'h', 'o', 'u', 'c', 'a', 'n', 'g']], [['c', 'o', 'l', 'l', 'e', 'c', 't']]⟩, ⟨[['t', 'u', 's', 'h', 'u']], [['b', 'o', 'o', 'k']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['m', 'e', 'i'], ['c', 'i']], [['e', 'v', 'e', 'r', 'y'], ['t', 'i', 'm', 'e']]⟩, ⟨[['z', 'h', 'a', 'o'], ['d', 'a', 'o']], [['f', 'i', 'n', 'd'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['b', 'e', 'n']], [['C', 'L']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['z', 'u', 'i', 'h', 'o', 'u']], [['f', 'i', 'n', 'a', 'l', 'l', 'y']]⟩, ⟨[['d', 'o', 'u']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['h', 'u', 'i']], [['w', 'i', 'l', 'l']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r']]⟩, ⟨[['z', 'i', 'j', 'i']], [['s', 'e', 'l', 'f']]⟩, ⟨[['d', 'u'], ['g', 'u', 'o']], [['r', 'e', 'a', 'd'], ['p', 'a', 's', 's']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['w', 'e', 'i']], [['C', 'L']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o'], ['j', 'i', 'a']], [['n', 'o', 'v', 'e', 'l'], ['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['x', 'i', 'e']], [['w', 'r', 'i', 't', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['l', 'i', 'n', 'g']], [['a', 'n', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['g', 'u', 's', 'h', 'i']], [['s', 't', 'o', 'r', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Study 4 target: demonstrative with the non-relational noun."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "sortal"), ("study", "4")] }

def fn13_intersentential_novelist : Datum :=
  { id := "ahnzhu2025_fn13_intersentential_novelist"
    source := ⟨"ahn-zhu-2025", "fn. 13 (i)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wang Yawen xihuan shoucang tushu. ta zhao-dao le yi ben xihuan de xiaoshuo. ta zuihou faxian ziji du-guo na wei xiaoshuo-jia xie de ling yi ge gushi."
    glossedTokens := [("Wang", "Wang"), ("Yawen", "Yawen"), ("xihuan", "like"), ("shoucang", "collect"), ("tushu", "book"), ("ta", "she"), ("zhao-dao", "find-arrive"), ("le", "ASP"), ("yi", "one"), ("ben", "CL"), ("xihuan", "like"), ("de", "DE"), ("xiaoshuo", "novel"), ("ta", "she"), ("zuihou", "finally"), ("faxian", "discover"), ("ziji", "self"), ("du-guo", "read-pass"), ("na", "that"), ("wei", "CL"), ("xiaoshuo-jia", "novel-person"), ("xie", "write"), ("de", "DE"), ("ling", "another"), ("yi", "one"), ("ge", "CL"), ("gushi", "story")]
    glossedWords := [⟨[['W', 'a', 'n', 'g']], [['W', 'a', 'n', 'g']]⟩, ⟨[['Y', 'a', 'w', 'e', 'n']], [['Y', 'a', 'w', 'e', 'n']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['s', 'h', 'o', 'u', 'c', 'a', 'n', 'g']], [['c', 'o', 'l', 'l', 'e', 'c', 't']]⟩, ⟨[['t', 'u', 's', 'h', 'u']], [['b', 'o', 'o', 'k']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['z', 'h', 'a', 'o'], ['d', 'a', 'o']], [['f', 'i', 'n', 'd'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['b', 'e', 'n']], [['C', 'L']]⟩, ⟨[['x', 'i', 'h', 'u', 'a', 'n']], [['l', 'i', 'k', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['t', 'a']], [['s', 'h', 'e']]⟩, ⟨[['z', 'u', 'i', 'h', 'o', 'u']], [['f', 'i', 'n', 'a', 'l', 'l', 'y']]⟩, ⟨[['f', 'a', 'x', 'i', 'a', 'n']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r']]⟩, ⟨[['z', 'i', 'j', 'i']], [['s', 'e', 'l', 'f']]⟩, ⟨[['d', 'u'], ['g', 'u', 'o']], [['r', 'e', 'a', 'd'], ['p', 'a', 's', 's']]⟩, ⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['w', 'e', 'i']], [['C', 'L']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o'], ['j', 'i', 'a']], [['n', 'o', 'v', 'e', 'l'], ['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['x', 'i', 'e']], [['w', 'r', 'i', 't', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['l', 'i', 'n', 'g']], [['a', 'n', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['g', 'e']], [['C', 'L']]⟩, ⟨[['g', 'u', 's', 'h', 'i']], [['s', 't', 'o', 'r', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The intersentential version of the Study 4 item, reported in a footnote."
    judgment := .acceptable
    alternatives := [("... ta zuihou faxian ziji du-guo xiaoshuo-jia xie de ling yi ge gushi.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "sortal"), ("study", "none")] }

def ex61a_de_owner : Datum :=
  { id := "ahnzhu2025_ex61a_de_owner"
    source := ⟨"ahn-zhu-2025", "(61a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yi zhi mao de zhuren"
    glossedTokens := [("yi", "one"), ("zhi", "CL"), ("mao", "cat"), ("de", "DE"), ("zhuren", "owner")]
    glossedWords := [⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['z', 'h', 'i']], [['C', 'L']]⟩, ⟨[['m', 'a', 'o']], [['c', 'a', 't']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['z', 'h', 'u', 'r', 'e', 'n']], [['o', 'w', 'n', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := "The de diagnostic used to classify Study 4 nouns."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "relational"), ("diagnostic", "de")] }

def ex61b_de_person : Datum :=
  { id := "ahnzhu2025_ex61b_de_person"
    source := ⟨"ahn-zhu-2025", "(61b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yi zhi mao de ren"
    glossedTokens := [("yi", "one"), ("zhi", "CL"), ("mao", "cat"), ("de", "DE"), ("ren", "person")]
    glossedWords := [⟨[['y', 'i']], [['o', 'n', 'e']]⟩, ⟨[['z', 'h', 'i']], [['C', 'L']]⟩, ⟨[['m', 'a', 'o']], [['c', 'a', 't']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['r', 'e', 'n']], [['p', 'e', 'r', 's', 'o', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := "The de diagnostic used to classify Study 4 nouns."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "sortal"), ("diagnostic", "de")] }

def ex62a_de_author : Datum :=
  { id := "ahnzhu2025_ex62a_de_author"
    source := ⟨"ahn-zhu-2025", "(62a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "na ben xiaoshuo de zuozhe"
    glossedTokens := [("na", "that"), ("ben", "CL"), ("xiaoshuo", "novel"), ("de", "DE"), ("zuozhe", "author")]
    glossedWords := [⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'n']], [['C', 'L']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['z', 'u', 'o', 'z', 'h', 'e']], [['a', 'u', 't', 'h', 'o', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := "Norming study (n = 8) rating the naturalness of de-constructions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "relational"), ("diagnostic", "de"), ("norming_rating", "4.88")] }

def ex62b_de_novelist : Datum :=
  { id := "ahnzhu2025_ex62b_de_novelist"
    source := ⟨"ahn-zhu-2025", "(62b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "na ben xiaoshuo de xiaoshuo-jia"
    glossedTokens := [("na", "that"), ("ben", "CL"), ("xiaoshuo", "novel"), ("de", "DE"), ("xiaoshuo-jia", "novelist")]
    glossedWords := [⟨[['n', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'n']], [['C', 'L']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'a', 'o', 's', 'h', 'u', 'o'], ['j', 'i', 'a']], [['n', 'o', 'v', 'e', 'l', 'i', 's', 't']]⟩]
    lgrConformance := some .wordAligned
    context := "Norming study (n = 8) rating the naturalness of de-constructions."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "sortal"), ("diagnostic", "de"), ("norming_rating", "1.50")] }

def ex63_moon : Datum :=
  { id := "ahnzhu2025_ex63_moon"
    source := ⟨"ahn-zhu-2025", "(15), (63)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yueliang sheng shang lai le."
    glossedTokens := [("yueliang", "moon"), ("sheng", "rise"), ("shang", "up"), ("lai", "come"), ("le", "ASP")]
    glossedWords := [⟨[['y', 'u', 'e', 'l', 'i', 'a', 'n', 'g']], [['m', 'o', 'o', 'n']]⟩, ⟨[['s', 'h', 'e', 'n', 'g']], [['r', 'i', 's', 'e']]⟩, ⟨[['s', 'h', 'a', 'n', 'g']], [['u', 'p']]⟩, ⟨[['l', 'a', 'i']], [['c', 'o', 'm', 'e']]⟩, ⟨[['l', 'e']], [['A', 'S', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "The unique moon; the demonstrative variant is degraded."
    judgment := .acceptable
    alternatives := [("na ge yueliang sheng shang lai le.", .unacceptable)]
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "none")] }

def ex20a_the_roof : Datum :=
  { id := "ahnzhu2025_ex20a_the_roof"
    source := ⟨"ahn-zhu-2025", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought a house. The roof needed to be replaced."
    glossedTokens := []
    context := "Part-whole bridging from 'house' to its roof; the continuation introduces no second roof."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "none")] }

def ex20b_that_roof : Datum :=
  { id := "ahnzhu2025_ex20b_that_roof"
    source := ⟨"ahn-zhu-2025", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought a house. That roof needed to be replaced."
    glossedTokens := []
    context := "Part-whole bridging with a demonstrative; no reason to extend the situation to another roof."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "none")] }

def ex34a_study2_partwhole_the : Datum :=
  { id := "ahnzhu2025_ex34a_study2_partwhole_the"
    source := ⟨"ahn-zhu-2025", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David parked his bike in the backyard, and then his dog scratched the seat."
    glossedTokens := []
    context := "Study 2 target: English translation of the Study 1 (bike, seat) item with a definite description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "2")] }

def ex34a_study2_partwhole_that : Datum :=
  { id := "ahnzhu2025_ex34a_study2_partwhole_that"
    source := ⟨"ahn-zhu-2025", "(34a), demonstrative variant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David parked his bike in the backyard, and then his dog scratched that seat."
    glossedTokens := []
    context := "Study 2 target, demonstrative description in the part-whole condition."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "partWhole"), ("noun_arity", "sortal"), ("study", "2")] }

def ex34b_study2_relational_that : Datum :=
  { id := "ahnzhu2025_ex34b_study2_relational_that"
    source := ⟨"ahn-zhu-2025", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Grace bought a CD last week, and every day she dreams about obtaining an autograph from that singer."
    glossedTokens := []
    context := "Study 2 target: English translation of the Study 1 (CD, singer) item with a demonstrative description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "2")] }

def ex34b_study2_relational_the : Datum :=
  { id := "ahnzhu2025_ex34b_study2_relational_the"
    source := ⟨"ahn-zhu-2025", "(34b), definite variant; Fig. 5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Grace bought a CD last week, and every day she dreams about obtaining an autograph from the singer."
    glossedTokens := []
    context := "Study 2 target, definite description in the relational condition."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "2")] }

def ex36a_study2_author : Datum :=
  { id := "ahnzhu2025_ex36a_study2_author"
    source := ⟨"ahn-zhu-2025", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucas read a novel yesterday, and if possible, he really wants to meet the author."
    glossedTokens := []
    context := "Study 2 item REL1 (novel, author), one of two items without a significant definite vs demonstrative difference (p = 0.189)."
    judgment := .acceptable
    alternatives := [("Lucas read a novel yesterday, and if possible, he really wants to meet that author.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "2")] }

def ex36b_study2_director : Datum :=
  { id := "ahnzhu2025_ex36b_study2_director"
    source := ⟨"ahn-zhu-2025", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ryan watched a movie last week, and he believed that he ran into the director after the movie."
    glossedTokens := []
    context := "Study 2 item REL3 (movie, director), the other item without a significant difference (p = 0.124)."
    judgment := .acceptable
    alternatives := [("Ryan watched a movie last week, and he believed that he ran into that director after the movie.", .acceptable)]
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "2")] }

def ex49_author_at_issue : Datum :=
  { id := "ahnzhu2025_ex49_author_at_issue"
    source := ⟨"ahn-zhu-2025", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: There was a book reading event here yesterday. B: Yes I know. In fact, I was here and met the author. A: No you didn't. The person you met was not the author of that particular book but another book that was on sale yesterday."
    glossedTokens := []
    context := "B's 'the author' is intended as the author of the featured book; A rejects it because the book-author relation fails, although the person B met is an author."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "relational"), ("noun_arity", "relational"), ("study", "none"), ("at_issue", "relation")] }

def ex54_deferred : Datum :=
  { id := "ahnzhu2025_ex54_deferred"
    source := ⟨"ahn-zhu-2025", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I liked that movie."
    glossedTokens := []
    context := "Said while pointing to a poster of the movie."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "none"), ("noun_arity", "sortal"), ("study", "none"), ("use", "deferred")] }

def ex60a_of_author : Datum :=
  { id := "ahnzhu2025_ex60a_of_author"
    source := ⟨"ahn-zhu-2025", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the author of a novel"
    glossedTokens := []
    context := "The of-diagnostic for relational nouns."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "relational"), ("diagnostic", "of")] }

def ex60b_of_novelist : Datum :=
  { id := "ahnzhu2025_ex60b_of_novelist"
    source := ⟨"ahn-zhu-2025", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the novelist of a novel"
    glossedTokens := []
    context := "The of-diagnostic for relational nouns."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun_arity", "sortal"), ("diagnostic", "of")] }

def all : List Datum := [ex14a_bare, ex14b_na, ex17_partwhole_bare, ex18_anaphoric_na, ex21_partwhole_na, ex22_relational_na, ex24a_de_child, ex24b_de_person, ex25_de_flower, ex28a_study1_partwhole_na, ex28b_study1_relational_bare, ex32_study1_painter, ex33a_study1_steeringwheel, ex37_study3_partwhole_bare, ex37_study3_partwhole_na, ex38_study3_relational_bare, ex38_study3_relational_na, ex39_study3_sn, ex40_study3_pn, ex41_study3_rn, ex42_study3_nn, ex59_study4_bare_author, ex59_study4_na_author, ex59_study4_bare_novelist, ex59_study4_na_novelist, fn13_intersentential_novelist, ex61a_de_owner, ex61b_de_person, ex62a_de_author, ex62b_de_novelist, ex63_moon, ex20a_the_roof, ex20b_that_roof, ex34a_study2_partwhole_the, ex34a_study2_partwhole_that, ex34b_study2_relational_that, ex34b_study2_relational_the, ex36a_study2_author, ex36b_study2_director, ex49_author_at_issue, ex54_deferred, ex60a_of_author, ex60b_of_novelist]

end AhnZhu2025.Examples
