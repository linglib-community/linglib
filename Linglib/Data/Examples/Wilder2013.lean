module

public import Linglib.Data.Examples.Schema

/-!
# `Wilder2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Wilder2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wilder2013.Examples`.
-/

@[expose] public section

namespace Wilder2013.Examples

def ex10b : Datum :=
  { id := "wilder2013_ex10b"
    source := ⟨"wilder-2013", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He does have a lot of patients."
    glossedTokens := []
    context := "They said he didn't have a lot of patients, but …"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "root"), ("antecedent", "assertedNegation")] }

def ex11b : Datum :=
  { id := "wilder2013_ex11b"
    source := ⟨"wilder-2013", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, he does have a lot of patients."
    glossedTokens := []
    context := "A: Is he a good doctor?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "root"), ("ctConstituent", "vp")] }

def ex12b : Datum :=
  { id := "wilder2013_ex12b"
    source := ⟨"wilder-2013", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary does have a lot of patients."
    glossedTokens := []
    context := "I can't imagine that Bill has a lot of patients, but.."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "root"), ("ctConstituent", "subject")] }

def ex51 : Datum :=
  { id := "wilder2013_ex51"
    source := ⟨"wilder-2013", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're wrong – she did leave her husband."
    glossedTokens := []
    context := "A: Sue didn't leave her husband."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "root"), ("antecedent", "assertedNegation")] }

def ex52 : Datum :=
  { id := "wilder2013_ex52"
    source := ⟨"wilder-2013", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In fact, she did leave her husband."
    glossedTokens := []
    context := "A: Sue might have left her husband."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "root"), ("antecedent", "modal")] }

def ex53 : Datum :=
  { id := "wilder2013_ex53"
    source := ⟨"wilder-2013", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "But she did leave her husband."
    glossedTokens := []
    context := "A: We are surprised that Sue didn't leave her husband."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "root"), ("antecedent", "presupposedNegation")] }

def ex74b : Datum :=
  { id := "wilder2013_ex74b"
    source := ⟨"wilder-2013", "(74b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary does have a lot of patients."
    glossedTokens := []
    context := "Bill doesn't have a lot of patients, but …"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "root"), ("antecedent", "parallelNegation")] }

def ex27a : Datum :=
  { id := "wilder2013_ex27a"
    source := ⟨"wilder-2013", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that he does treat his patients politely."
    glossedTokens := []
    context := "Although you say that your doctor doesn't treat his patients politely, …"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "believeComplement")] }

def ex27b : Datum :=
  { id := "wilder2013_ex27b"
    source := ⟨"wilder-2013", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that he does treat his patients politely."
    glossedTokens := []
    context := "Is he good doctor? …"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "believeComplement"), ("ctConstituent", "vp")] }

def ex27c : Datum :=
  { id := "wilder2013_ex27c"
    source := ⟨"wilder-2013", "(27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that Dr. Smith does treat them politely."
    glossedTokens := []
    context := "Do the doctors in this hospital treat their patients politely? …"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "believeComplement"), ("ctConstituent", "subject")] }

def ex27d : Datum :=
  { id := "wilder2013_ex27d"
    source := ⟨"wilder-2013", "(27d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "However, it would appear that they did win it."
    glossedTokens := []
    context := "Nobody expected that France would win their first game."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "believeComplement")] }

def ex27e : Datum :=
  { id := "wilder2013_ex27e"
    source := ⟨"wilder-2013", "(27e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It would appear that the French did win against England."
    glossedTokens := []
    context := "Is the French team doing well this time?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "believeComplement"), ("ctConstituent", "vp")] }

def ex27f : Datum :=
  { id := "wilder2013_ex27f"
    source := ⟨"wilder-2013", "(27f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Spain did beat the Italians."
    glossedTokens := []
    context := "Did the French beat the Italians?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "believeComplement"), ("ctConstituent", "subject")] }

def ex28a : Datum :=
  { id := "wilder2013_ex28a"
    source := ⟨"wilder-2013", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm beginning to wonder if he does treat his patients politely."
    glossedTokens := []
    context := "A: We heard that your doctor doesn't treat his patients politely."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "interrogativeComplement"), ("sentenceType", "polar")] }

def ex28b : Datum :=
  { id := "wilder2013_ex28b"
    source := ⟨"wilder-2013", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm beginning to wonder if he does treat his patients politely."
    glossedTokens := []
    context := "Is he good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "interrogativeComplement"), ("sentenceType", "polar"), ("ctConstituent", "vp")] }

def ex28c : Datum :=
  { id := "wilder2013_ex28c"
    source := ⟨"wilder-2013", "(28c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't know if Dr. Smith does treat his patients politely."
    glossedTokens := []
    context := "Do the doctors in this hospital treat their patients politely?"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "interrogativeComplement"), ("sentenceType", "polar"), ("ctConstituent", "subject")] }

def ex28d : Datum :=
  { id := "wilder2013_ex28d"
    source := ⟨"wilder-2013", "(28d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She asked which doctor does treat his patients politely."
    glossedTokens := []
    context := "When she heard that your doctor doesn't treat his patients politely,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "interrogativeComplement"), ("sentenceType", "constituent")] }

def ex28e : Datum :=
  { id := "wilder2013_ex28e"
    source := ⟨"wilder-2013", "(28e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary asked me which doctor does treat his patients politely."
    glossedTokens := []
    context := "Is he good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "interrogativeComplement"), ("sentenceType", "constituent"), ("ctConstituent", "vp")] }

def ex29a : Datum :=
  { id := "wilder2013_ex29a"
    source := ⟨"wilder-2013", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue resents it that he does treat his patients politely."
    glossedTokens := []
    context := "Paul would be horrified if he wouldn't treat his patients politely, while"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "factiveComplement")] }

def ex29b : Datum :=
  { id := "wilder2013_ex29b"
    source := ⟨"wilder-2013", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue resents it that he does treat his patients politely."
    glossedTokens := []
    context := "Is he a good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "factiveComplement"), ("ctConstituent", "vp")] }

def ex29c : Datum :=
  { id := "wilder2013_ex29c"
    source := ⟨"wilder-2013", "(29c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue resents it that Dr. Smith does treat his patients politely."
    glossedTokens := []
    context := "Do the doctors in this hospital treat their patients politely? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "factiveComplement"), ("ctConstituent", "subject")] }

def ex30a : Datum :=
  { id := "wilder2013_ex30a"
    source := ⟨"wilder-2013", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's precisely this doctor who does treat his patients politely."
    glossedTokens := []
    context := "Sue claimed that Dr. Smith doesn't treat his patients politely, but"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "itCleft")] }

def ex30b : Datum :=
  { id := "wilder2013_ex30b"
    source := ⟨"wilder-2013", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's precisely this doctor who does treat his patients politely."
    glossedTokens := []
    context := "Is Dr. Smith a good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "itCleft"), ("ctConstituent", "vp")] }

def ex30c : Datum :=
  { id := "wilder2013_ex30c"
    source := ⟨"wilder-2013", "(30c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's his patients that he does treat politely."
    glossedTokens := []
    context := "Although Sue claimed that he doesn't treat his patients politely,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "itCleft")] }

def ex30d : Datum :=
  { id := "wilder2013_ex30d"
    source := ⟨"wilder-2013", "(30d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's his patients that he does treat politely."
    glossedTokens := []
    context := "Is Dr. Smith a good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "itCleft"), ("ctConstituent", "vp")] }

def ex31a : Datum :=
  { id := "wilder2013_ex31a"
    source := ⟨"wilder-2013", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've chosen another doctor who does treat his patients politely."
    glossedTokens := []
    context := "Dr. Smith doesn't treat his patients politely, so"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "restrictiveRelative")] }

def ex31b : Datum :=
  { id := "wilder2013_ex31b"
    source := ⟨"wilder-2013", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've chosen another doctor who does treat his patients politely."
    glossedTokens := []
    context := "Is Dr. Smith a good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "restrictiveRelative"), ("ctConstituent", "vp")] }

def ex31c : Datum :=
  { id := "wilder2013_ex31c"
    source := ⟨"wilder-2013", "(31c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've spoken to several patients who he does treat politely."
    glossedTokens := []
    context := "Although Sue claimed that Dr. Smith doesn't treat patients politely,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "restrictiveRelative")] }

def ex31d : Datum :=
  { id := "wilder2013_ex31d"
    source := ⟨"wilder-2013", "(31d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've spoken to several patients who he does treat politely."
    glossedTokens := []
    context := "Is Dr. Smith a good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "restrictiveRelative"), ("ctConstituent", "vp")] }

def ex32a : Datum :=
  { id := "wilder2013_ex32a"
    source := ⟨"wilder-2013", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I chose him precisely because he does treat his patients politely."
    glossedTokens := []
    context := "She claimed that he doesn't treat his patients politely, but …"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "adverbialClause")] }

def ex32b : Datum :=
  { id := "wilder2013_ex32b"
    source := ⟨"wilder-2013", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue likes him because he does treat his patients politely."
    glossedTokens := []
    context := "Is he a good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "adverbialClause"), ("ctConstituent", "vp")] }

def ex33a : Datum :=
  { id := "wilder2013_ex33a"
    source := ⟨"wilder-2013", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I refused to pay him until he did treat her politely."
    glossedTokens := []
    context := "She told me that he didn't treat her politely, so …"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "adverbialClause")] }

def ex33b : Datum :=
  { id := "wilder2013_ex33b"
    source := ⟨"wilder-2013", "(33b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People won't choose him until he does have a lot of patients."
    glossedTokens := []
    context := "Is he a good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "adverbialClause"), ("ctConstituent", "vp")] }

def ex40b : Datum :=
  { id := "wilder2013_ex40b"
    source := ⟨"wilder-2013", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which doctor does treat his patients politely?"
    glossedTokens := []
    context := "We heard that your doctor doesn't treat his patients politely."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "whSubjectQuestion")] }

def ex41b : Datum :=
  { id := "wilder2013_ex41b"
    source := ⟨"wilder-2013", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which doctor does treat his patients politely?"
    glossedTokens := []
    context := "Is he good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "whSubjectQuestion"), ("ctConstituent", "vp")] }

def ex44b : Datum :=
  { id := "wilder2013_ex44b"
    source := ⟨"wilder-2013", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "His patients, he does treat politely."
    glossedTokens := []
    context := "We heard that your doctor doesn't treat his patients politely."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "VF"), ("environment", "objectPreposing")] }

def ex45b : Datum :=
  { id := "wilder2013_ex45b"
    source := ⟨"wilder-2013", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "His patients, he does treat politely."
    glossedTokens := []
    context := "Is he good doctor? …"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CT"), ("environment", "objectPreposing"), ("ctConstituent", "vp")] }

def ex113b : Datum :=
  { id := "wilder2013_ex113b"
    source := ⟨"wilder-2013", "(113b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred did eat the beans."
    glossedTokens := []
    context := "What about Fred? What did he eat?"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CTwh"), ("environment", "root"), ("ctConstituent", "subject")] }

def ex114b : Datum :=
  { id := "wilder2013_ex114b"
    source := ⟨"wilder-2013", "(114b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred did eat the beans."
    glossedTokens := []
    context := "What about the beans? Who ate those?"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "CTwh"), ("environment", "root"), ("ctConstituent", "object")] }

def ex126a : Datum :=
  { id := "wilder2013_ex126a"
    source := ⟨"wilder-2013", "(126a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, I believe that he does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "believeComplement")] }

def ex126b : Datum :=
  { id := "wilder2013_ex126b"
    source := ⟨"wilder-2013", "(126b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, it would appear that he does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "believeComplement")] }

def ex127a : Datum :=
  { id := "wilder2013_ex127a"
    source := ⟨"wilder-2013", "(127a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, I wonder if he does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "interrogativeComplement"), ("sentenceType", "polar")] }

def ex127b : Datum :=
  { id := "wilder2013_ex127b"
    source := ⟨"wilder-2013", "(127b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, Mary asked me which doctor does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "interrogativeComplement"), ("sentenceType", "constituent")] }

def ex127c : Datum :=
  { id := "wilder2013_ex127c"
    source := ⟨"wilder-2013", "(127c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, Sue resents it that he does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "factiveComplement")] }

def ex127d : Datum :=
  { id := "wilder2013_ex127d"
    source := ⟨"wilder-2013", "(127d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, it's precisely this doctor who does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "itCleft")] }

def ex127e : Datum :=
  { id := "wilder2013_ex127e"
    source := ⟨"wilder-2013", "(127e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, I've chosen another doctor who does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "restrictiveRelative")] }

def ex127f : Datum :=
  { id := "wilder2013_ex127f"
    source := ⟨"wilder-2013", "(127f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, Sue likes him because he does treat his patients politely."
    glossedTokens := []
    context := "Does he treat his patients politely?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "adverbialClause")] }

def ex137c : Datum :=
  { id := "wilder2013_ex137c"
    source := ⟨"wilder-2013", "(137c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, he works hard."
    glossedTokens := []
    context := "Does he work hard?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "yesAnswer"), ("environment", "root")] }

def all : List Datum := [ex10b, ex11b, ex12b, ex51, ex52, ex53, ex74b, ex27a, ex27b, ex27c, ex27d, ex27e, ex27f, ex28a, ex28b, ex28c, ex28d, ex28e, ex29a, ex29b, ex29c, ex30a, ex30b, ex30c, ex30d, ex31a, ex31b, ex31c, ex31d, ex32a, ex32b, ex33a, ex33b, ex40b, ex41b, ex44b, ex45b, ex113b, ex114b, ex126a, ex126b, ex127a, ex127b, ex127c, ex127d, ex127e, ex127f, ex137c]

end Wilder2013.Examples
