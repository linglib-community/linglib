module

public import Linglib.Data.Examples.Schema

/-!
# `Oswalt1986` — typed example data

Auto-generated from `Linglib/Data/Examples/Oswalt1986.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Oswalt1986.Examples`.
-/

@[expose] public section

namespace Oswalt1986.Examples

def s1 : Datum :=
  { id := "oswalt1986_s1"
    source := ⟨"oswalt-1986", "(S1)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowá·qala"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "performative")] }

def s2 : Datum :=
  { id := "oswalt1986_s2"
    source := ⟨"oswalt-1986", "(S2)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowáhmela"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")] }

def s4 : Datum :=
  { id := "oswalt1986_s4"
    source := ⟨"oswalt-1986", "(S4)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtócʰmela"
    glossedTokens := []
    context := "Said in the situation in which an English speaker says good-bye."
    judgment := .acceptable
    alternatives := [("cohtocéla", .ungrammatical)]
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")] }

def s6 : Datum :=
  { id := "oswalt1986_s6"
    source := ⟨"oswalt-1986", "(S6)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mi·-li ʔa me-ʔe-l pʰak̓úm-mela"
    glossedTokens := [("mi·-li", "there-VISIBLE"), ("ʔa", "I"), ("me-ʔe-l", "your-father-OBJ"), ("pʰak̓úm-mela", "kill-PERFORM")]
    glossedWords := [⟨[['m', 'i', '·'], ['l', 'i']], [['t', 'h', 'e', 'r', 'e'], ['V', 'I', 'S', 'I', 'B', 'L', 'E']]⟩, ⟨[['ʔ', 'a']], [['I']]⟩, ⟨[['m', 'e'], ['ʔ', 'e'], ['l']], [['y', 'o', 'u', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], ['O', 'B', 'J']]⟩, ⟨[['p', 'ʰ', 'a', 'k', '̓', 'ú', 'm'], ['m', 'e', 'l', 'a']], [['k', 'i', 'l', 'l'], ['P', 'E', 'R', 'F', 'O', 'R', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The sight of the children of a man the speaker killed years earlier prompts the remark."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")] }

def s7 : Datum :=
  { id := "oswalt1986_s7"
    source := ⟨"oswalt-1986", "(S7)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "hú·ʔ men s̓í-ya-m ṭa ʔa"
    glossedTokens := [("hú·ʔ", "Yes"), ("men", "thus"), ("s̓í-ya-m", "do-VISUAL-RESP"), ("ṭa", ""), ("ʔa", "I")]
    glossedWords := [⟨[['h', 'ú', '·', 'ʔ']], [['Y', 'e', 's']]⟩, ⟨[['m', 'e', 'n']], [['t', 'h', 'u', 's']]⟩, ⟨[['s', '̓', 'í'], ['y', 'a'], ['m']], [['d', 'o'], ['V', 'I', 'S', 'U', 'A', 'L'], ['R', 'E', 'S', 'P']]⟩, ⟨[['ṭ', 'a']], [[]]⟩, ⟨[['ʔ', 'a']], [['I']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A response to a remark by someone else."
    judgment := .acceptable
    alternatives := [("men s̓ímela", .acceptable), ("men s̓ímelam", .ungrammatical)]
    readings := []
    paperFeatures := [("mode", "responsive"), ("aspect", "perfective"), ("evidential", "factualVisual")] }

def s8 : Datum :=
  { id := "oswalt1986_s8"
    source := ⟨"oswalt-1986", "(S8)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowá·qʰ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "factualVisual")] }

def s9 : Datum :=
  { id := "oswalt1986_s9"
    source := ⟨"oswalt-1986", "(S9)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowahy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "factualVisual")] }

def s13 : Datum :=
  { id := "oswalt1986_s13"
    source := ⟨"oswalt-1986", "(S13)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "s̓ihta=yacʰma cahno-w"
    glossedTokens := [("s̓ihta=yacʰma", "bird=PL.SUBJ"), ("cahno-w", "sound-FACTUAL")]
    glossedWords := [⟨[['s', '̓', 'i', 'h', 't', 'a'], ['y', 'a', 'c', 'ʰ', 'm', 'a']], [['b', 'i', 'r', 'd'], ['P', 'L', '.', 'S', 'U', 'B', 'J']]⟩, ⟨[['c', 'a', 'h', 'n', 'o'], ['w']], [['s', 'o', 'u', 'n', 'd'], ['F', 'A', 'C', 'T', 'U', 'A', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("general truth", .acceptable), ("witnessed", .acceptable)]
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "factualVisual")] }

def s14 : Datum :=
  { id := "oswalt1986_s14"
    source := ⟨"oswalt-1986", "(S14)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mo·dun"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "auditory")] }

def s15 : Datum :=
  { id := "oswalt1986_s15"
    source := ⟨"oswalt-1986", "(S15)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "momá·cin"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "auditory")] }

def s16 : Datum :=
  { id := "oswalt1986_s16"
    source := ⟨"oswalt-1986", "(S16)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "hayu cáhno-n"
    glossedTokens := []
    context := "Opens a conversation, prompted by the barking."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "auditory")] }

def s17 : Datum :=
  { id := "oswalt1986_s17"
    source := ⟨"oswalt-1986", "(S17)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mu hayu cáhno-nna-m"
    glossedTokens := []
    context := "A continuation of the conversation S16 opens."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "auditory")] }

def s19 : Datum :=
  { id := "oswalt1986_s19"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mu cohtocʰqʰ"
    glossedTokens := []
    context := "Said on discovering that the person is no longer present; the leaving itself was neither seen nor heard."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "inferential")] }

def s19_visual : Datum :=
  { id := "oswalt1986_s19_visual"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtó·y"
    glossedTokens := []
    context := "The leaving was seen."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "factualVisual")] }

def s19_auditory : Datum :=
  { id := "oswalt1986_s19_auditory"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtocin"
    glossedTokens := []
    context := "The leaving was heard."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "auditory")] }

def s22 : Datum :=
  { id := "oswalt1986_s22"
    source := ⟨"oswalt-1986", "(S22)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "kalikakʰ dima· s̓i-qa-c̓-qʰ"
    glossedTokens := [("kalikakʰ", "book"), ("dima·", "holding"), ("s̓i-qa-c̓-qʰ", "make-cause-self-INFER")]
    glossedWords := [⟨[['k', 'a', 'l', 'i', 'k', 'a', 'k', 'ʰ']], [['b', 'o', 'o', 'k']]⟩, ⟨[['d', 'i', 'm', 'a', '·']], [['h', 'o', 'l', 'd', 'i', 'n', 'g']]⟩, ⟨[['s', '̓', 'i'], ['q', 'a'], ['c', '̓'], ['q', 'ʰ']], [['m', 'a', 'k', 'e'], ['c', 'a', 'u', 's', 'e'], ['s', 'e', 'l', 'f'], ['I', 'N', 'F', 'E', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The picture is seen; the act of taking it was not."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "inferential")] }

def s25 : Datum :=
  { id := "oswalt1986_s25"
    source := ⟨"oswalt-1986", "(S25)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mul =í-yow-e· hayu cáhno-w"
    glossedTokens := [("mul", "then"), ("=í-yow-e·", "=ASS-P.E.-NONFINAL"), ("hayu", "dog"), ("cáhno-w", "sound-ABS")]
    glossedWords := [⟨[['m', 'u', 'l']], [['t', 'h', 'e', 'n']]⟩, ⟨[[], ['í'], ['y', 'o', 'w'], ['e', '·']], [[], ['A', 'S', 'S'], ['P', '.', 'E', '.'], ['N', 'O', 'N', 'F', 'I', 'N', 'A', 'L']]⟩, ⟨[['h', 'a', 'y', 'u']], [['d', 'o', 'g']]⟩, ⟨[['c', 'á', 'h', 'n', 'o'], ['w']], [['s', 'o', 'u', 'n', 'd'], ['A', 'B', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "narrative"), ("evidential", "personalExperience")] }

def s26 : Datum :=
  { id := "oswalt1986_s26"
    source := ⟨"oswalt-1986", "(S26)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "men s̓i-yíʔciʔ-tʰi-miy"
    glossedTokens := [("men", "thus"), ("s̓i-yíʔciʔ-tʰi-miy", "do-PL.HABITUAL-NEG-REMOTE")]
    glossedWords := [⟨[['m', 'e', 'n']], [['t', 'h', 'u', 's']]⟩, ⟨[['s', '̓', 'i'], ['y', 'í', 'ʔ', 'c', 'i', 'ʔ'], ['t', 'ʰ', 'i'], ['m', 'i', 'y']], [['d', 'o'], ['P', 'L', '.', 'H', 'A', 'B', 'I', 'T', 'U', 'A', 'L'], ['N', 'E', 'G'], ['R', 'E', 'M', 'O', 'T', 'E']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "remote"), ("evidential", "remotePast")] }

def s27 : Datum :=
  { id := "oswalt1986_s27"
    source := ⟨"oswalt-1986", "(S27)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mul =í-do-· hayu cáhno-w"
    glossedTokens := [("mul", "then"), ("=í-do-·", "=ASS-QUOT-NONFINAL"), ("hayu", "dog"), ("cáhno-w", "sound-ABS")]
    glossedWords := [⟨[['m', 'u', 'l']], [['t', 'h', 'e', 'n']]⟩, ⟨[[], ['í'], ['d', 'o'], ['·']], [[], ['A', 'S', 'S'], ['Q', 'U', 'O', 'T'], ['N', 'O', 'N', 'F', 'I', 'N', 'A', 'L']]⟩, ⟨[['h', 'a', 'y', 'u']], [['d', 'o', 'g']]⟩, ⟨[['c', 'á', 'h', 'n', 'o'], ['w']], [['s', 'o', 'u', 'n', 'd'], ['A', 'B', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "narrative"), ("evidential", "quotative")] }

def s28 : Datum :=
  { id := "oswalt1986_s28"
    source := ⟨"oswalt-1986", "(S28)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "meʔ mu mi· sikúhtimeʔ=yacʰma ʔi-do-m ʔul"
    glossedTokens := [("meʔ", "but"), ("mu", "that"), ("mi·", "there"), ("sikúhtimeʔ=yacʰma", "drinking=people"), ("ʔi-do-m", "be-QUOT-RESP"), ("ʔul", "already")]
    glossedWords := [⟨[['m', 'e', 'ʔ']], [['b', 'u', 't']]⟩, ⟨[['m', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['m', 'i', '·']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['s', 'i', 'k', 'ú', 'h', 't', 'i', 'm', 'e', 'ʔ'], ['y', 'a', 'c', 'ʰ', 'm', 'a']], [['d', 'r', 'i', 'n', 'k', 'i', 'n', 'g'], ['p', 'e', 'o', 'p', 'l', 'e']]⟩, ⟨[['ʔ', 'i'], ['d', 'o'], ['m']], [['b', 'e'], ['Q', 'U', 'O', 'T'], ['R', 'E', 'S', 'P']]⟩, ⟨[['ʔ', 'u', 'l']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "From a conversation in the responsive mode; the event takes place elsewhere."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "quotative")] }

def s29 : Datum :=
  { id := "oswalt1986_s29"
    source := ⟨"oswalt-1986", "(S29)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qacúhse hqamac̓-kʰe =ʔ-do-m ṭa"
    glossedTokens := [("qacúhse", "grass game"), ("hqamac̓-kʰe", "play-FUT"), ("=ʔ-do-m", "=ASS-QUOT-RESP"), ("ṭa", "")]
    glossedWords := [⟨[['q', 'a', 'c', 'ú', 'h', 's', 'e']], [['g', 'r', 'a', 's', 's', ' ', 'g', 'a', 'm', 'e']]⟩, ⟨[['h', 'q', 'a', 'm', 'a', 'c', '̓'], ['k', 'ʰ', 'e']], [['p', 'l', 'a', 'y'], ['F', 'U', 'T']]⟩, ⟨[[], ['ʔ'], ['d', 'o'], ['m']], [[], ['A', 'S', 'S'], ['Q', 'U', 'O', 'T'], ['R', 'E', 'S', 'P']]⟩, ⟨[['ṭ', 'a']], [[]]⟩]
    lgrConformance := some .morphemeAligned
    context := "From the same conversation as S28."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "quotative")] }

def s32 : Datum :=
  { id := "oswalt1986_s32"
    source := ⟨"oswalt-1986", "(S32)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "kʰe híʔbaya=ʔ-bi-w"
    glossedTokens := [("kʰe", "My"), ("híʔbaya=ʔ-bi-w", "man=ASS-II-ABS")]
    glossedWords := [⟨[['k', 'ʰ', 'e']], [['M', 'y']]⟩, ⟨[['h', 'í', 'ʔ', 'b', 'a', 'y', 'a'], ['ʔ'], ['b', 'i'], ['w']], [['m', 'a', 'n'], ['A', 'S', 'S'], ['I', 'I'], ['A', 'B', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A woman saw a man approaching but could not recognize him until he arrived."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "inferentialII")] }

def all : List Datum := [s1, s2, s4, s6, s7, s8, s9, s13, s14, s15, s16, s17, s19, s19_visual, s19_auditory, s22, s25, s26, s27, s28, s29, s32]

end Oswalt1986.Examples
