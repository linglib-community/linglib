module

public import Linglib.Data.Examples.Schema

/-!
# `Zheng2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Zheng2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zheng2025.Examples`.
-/

@[expose] public section

namespace Zheng2025.Examples

def ex1 : Datum :=
  { id := "zheng2025_ex1"
    source := ⟨"zheng-2025", "(1)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "nandao ta fafeng-le ma?"
    glossedTokens := [("nandao", "nandao"), ("ta", "he"), ("fafeng-le", "go.crazy-PERF"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['f', 'a', 'f', 'e', 'n', 'g', '-', 'l', 'e'], ['g', 'o', '.', 'c', 'r', 'a', 'z', 'y', '-', 'P', 'E', 'R', 'F'], [⟨['f', 'a', 'f', 'e', 'n', 'g'], ['g', 'o', '.', 'c', 'r', 'a', 'z', 'y'], none⟩, ⟨['l', 'e'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A and B are talking about a colleague, Lee, who is going to work on Sunday. B does not think people usually go to work on Sunday."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "true"), ("epistemic_bias", "true"), ("unexpected_evidence", "true")] }

def ex2 : Datum :=
  { id := "zheng2025_ex2"
    source := ⟨"zheng-2025", "(2)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['x', 'i', 'a', 'y', 'u', '-', 'l', 'e'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n', '-', 'P', 'E', 'R', 'F'], [⟨['x', 'i', 'a', 'y', 'u'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n'], none⟩, ⟨['l', 'e'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A sits in a windowless room working. A believes it is not raining. At 10, B enters the room with a dripping raincoat."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "true"), ("epistemic_bias", "true"), ("unexpected_evidence", "true")] }

def ex3 : Datum :=
  { id := "zheng2025_ex3"
    source := ⟨"zheng-2025", "(3)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['x', 'i', 'a', 'y', 'u', '-', 'l', 'e'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n', '-', 'P', 'E', 'R', 'F'], [⟨['x', 'i', 'a', 'y', 'u'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n'], none⟩, ⟨['l', 'e'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A sits in a windowless room working. A has no expectation about the weather. At 10, B enters the room with a dripping raincoat."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "true"), ("epistemic_bias", "false"), ("unexpected_evidence", "true")] }

def ex4b : Datum :=
  { id := "zheng2025_ex4b"
    source := ⟨"xu-2018", "p. 449"⟩
    reportedIn := some ⟨"zheng-2025", "(4b)"⟩
    language := "mand1415"
    primaryText := "Nandao wuli you ren?"
    glossedTokens := [("nandao", "nandao"), ("wuli", "room.in"), ("you", "exist"), ("ren", "person")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['w', 'u', 'l', 'i'], ['r', 'o', 'o', 'm', '.', 'i', 'n'], [⟨['w', 'u', 'l', 'i'], ['r', 'o', 'o', 'm', '.', 'i', 'n'], none⟩]⟩, ⟨['y', 'o', 'u'], ['e', 'x', 'i', 's', 't'], [⟨['y', 'o', 'u'], ['e', 'x', 'i', 's', 't'], none⟩]⟩, ⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker believes that there is no one in a room."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "false"), ("epistemic_bias", "true"), ("unexpected_evidence", "false")] }

def ex5_ctx1 : Datum :=
  { id := "zheng2025_ex5_ctx1"
    source := ⟨"zheng-2025", "(5) ctx 1"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['x', 'i', 'a', 'y', 'u', '-', 'l', 'e'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n', '-', 'P', 'E', 'R', 'F'], [⟨['x', 'i', 'a', 'y', 'u'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n'], none⟩, ⟨['l', 'e'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A is sitting in a windowless room working. A doesn't know the weather or have any expectations that people will wear raincoats. At 10, B enters the room with a dripping raincoat."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "true"), ("epistemic_bias", "false"), ("unexpected_evidence", "true")] }

def ex5_ctx2 : Datum :=
  { id := "zheng2025_ex5_ctx2"
    source := ⟨"zheng-2025", "(5) ctx 2"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['x', 'i', 'a', 'y', 'u', '-', 'l', 'e'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n', '-', 'P', 'E', 'R', 'F'], [⟨['x', 'i', 'a', 'y', 'u'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n'], none⟩, ⟨['l', 'e'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A is sitting in a windowless room working. A doesn't know the weather or have any expectations that people will wear raincoats. At 10, B enters the room."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "false"), ("epistemic_bias", "false"), ("unexpected_evidence", "false")] }

def ex5_ctx3 : Datum :=
  { id := "zheng2025_ex5_ctx3"
    source := ⟨"zheng-2025", "(5) ctx 3"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['w', 'a', 'i', 'm', 'i', 'a', 'n'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['x', 'i', 'a', 'y', 'u', '-', 'l', 'e'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n', '-', 'P', 'E', 'R', 'F'], [⟨['x', 'i', 'a', 'y', 'u'], ['f', 'a', 'l', 'l', '.', 'r', 'a', 'i', 'n'], none⟩, ⟨['l', 'e'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A thinks it will not rain today. At 10, B enters the room."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "false"), ("epistemic_bias", "true"), ("unexpected_evidence", "false")] }

def ex6_ctx1 : Datum :=
  { id := "zheng2025_ex6_ctx1"
    source := ⟨"zheng-2025", "(6) ctx 1"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "nandao ta hen.mang ma?"
    glossedTokens := [("nandao", "nandao"), ("ta", "he"), ("hen.mang", "very.busy"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['h', 'e', 'n', '.', 'm', 'a', 'n', 'g'], ['v', 'e', 'r', 'y', '.', 'b', 'u', 's', 'y'], [⟨['h', 'e', 'n', 'm', 'a', 'n', 'g'], ['v', 'e', 'r', 'y', '.', 'b', 'u', 's', 'y'], none⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A says Lee is planning to work on weekends too. B does not think that people, including Lee, usually go to work on Sunday."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "true"), ("epistemic_bias", "true"), ("unexpected_evidence", "true")] }

def ex6_ctx2 : Datum :=
  { id := "zheng2025_ex6_ctx2"
    source := ⟨"zheng-2025", "(6) ctx 2"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "nandao ta hen.mang ma?"
    glossedTokens := [("nandao", "nandao"), ("ta", "he"), ("hen.mang", "very.busy"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['h', 'e', 'n', '.', 'm', 'a', 'n', 'g'], ['v', 'e', 'r', 'y', '.', 'b', 'u', 's', 'y'], [⟨['h', 'e', 'n', 'm', 'a', 'n', 'g'], ['v', 'e', 'r', 'y', '.', 'b', 'u', 's', 'y'], none⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := "A says Lee is planning to work on weekends too. B knows Lee usually goes to work on Sunday."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "true"), ("epistemic_bias", "false"), ("unexpected_evidence", "false")] }

def ex4a : Datum :=
  { id := "zheng2025_ex4a"
    source := ⟨"xu-2018", "p. 449"⟩
    reportedIn := some ⟨"zheng-2025", "(4a)"⟩
    language := "mand1415"
    primaryText := "Nandao wuli mei ren?"
    glossedTokens := [("nandao", "nandao"), ("wuli", "room.in"), ("mei", "no"), ("ren", "person")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['w', 'u', 'l', 'i'], ['r', 'o', 'o', 'm', '.', 'i', 'n'], [⟨['w', 'u', 'l', 'i'], ['r', 'o', 'o', 'm', '.', 'i', 'n'], none⟩]⟩, ⟨['m', 'e', 'i'], ['n', 'o'], [⟨['m', 'e', 'i'], ['n', 'o'], none⟩]⟩, ⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker believes that there is no one in a room."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "polar"), ("evidential_bias", "false"), ("epistemic_bias", "true"), ("unexpected_evidence", "false")] }

def ex12a : Datum :=
  { id := "zheng2025_ex12a"
    source := ⟨"xu-2012", "p. 510"⟩
    reportedIn := some ⟨"zheng-2025", "(12a)"⟩
    language := "mand1415"
    primaryText := "Nandao Lisi hui lai"
    glossedTokens := [("nandao", "nandao"), ("Lisi", "Lisi"), ("hui", "will"), ("lai", "come")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], [⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], none⟩]⟩, ⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], [⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], [⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "declarative")] }

def ex12b : Datum :=
  { id := "zheng2025_ex12b"
    source := ⟨"xu-2012", "p. 512"⟩
    reportedIn := some ⟨"zheng-2025", "(12b)"⟩
    language := "mand1415"
    primaryText := "Nandao Zhangsan weishenme qu xuexiao ma?"
    glossedTokens := [("nandao", "nandao"), ("Zhangsan", "Zhangsan"), ("weishenme", "why"), ("qu", "go"), ("xuexiao", "school"), ("ma", "Y/N-Q")]
    glossedWords := [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], [⟨['n', 'a', 'n', 'd', 'a', 'o'], ['n', 'a', 'n', 'd', 'a', 'o'], none⟩]⟩, ⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['w', 'e', 'i', 's', 'h', 'e', 'n', 'm', 'e'], ['w', 'h', 'y'], [⟨['w', 'e', 'i', 's', 'h', 'e', 'n', 'm', 'e'], ['w', 'h', 'y'], none⟩]⟩, ⟨['q', 'u'], ['g', 'o'], [⟨['q', 'u'], ['g', 'o'], none⟩]⟩, ⟨['x', 'u', 'e', 'x', 'i', 'a', 'o'], ['s', 'c', 'h', 'o', 'o', 'l'], [⟨['x', 'u', 'e', 'x', 'i', 'a', 'o'], ['s', 'c', 'h', 'o', 'o', 'l'], none⟩]⟩, ⟨['m', 'a'], ['Y', '/', 'N', '-', 'Q'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause_type", "wh-question")] }

def all : List Datum := [ex1, ex2, ex3, ex4b, ex5_ctx1, ex5_ctx2, ex5_ctx3, ex6_ctx1, ex6_ctx2, ex4a, ex12a, ex12b]

end Zheng2025.Examples
