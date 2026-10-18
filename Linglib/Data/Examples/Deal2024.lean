module

public import Linglib.Data.Examples.Schema

/-!
# `Deal2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Deal2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deal2024.Examples`.
-/

@[expose] public section

namespace Deal2024.Examples

def ex16a_1 : Datum :=
  { id := "deal2024_ex16a_1"
    source := ⟨"deal-2024", "(16a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Lucille me la présentera."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "3"), ("pattern", "strong")] }

def ex16a_2 : Datum :=
  { id := "deal2024_ex16a_2"
    source := ⟨"deal-2024", "(16a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Lucille te la présentera."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "3"), ("pattern", "strong")] }

def ex16b_1 : Datum :=
  { id := "deal2024_ex16b_1"
    source := ⟨"deal-2024", "(16b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Lucille la leur présentera."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "3"), ("pattern", "strong")] }

def ex16b_2 : Datum :=
  { id := "deal2024_ex16b_2"
    source := ⟨"deal-2024", "(16b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Lucille me leur présentera."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "1"), ("pattern", "strong")] }

def ex16b_3 : Datum :=
  { id := "deal2024_ex16b_3"
    source := ⟨"deal-2024", "(16b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Lucille te leur présentera."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "2"), ("pattern", "strong")] }

def ex16c_1 : Datum :=
  { id := "deal2024_ex16c_1"
    source := ⟨"deal-2024", "(16c)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Lucille te me présentera."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "2"), ("pattern", "strong")] }

def ex16c_2 : Datum :=
  { id := "deal2024_ex16c_2"
    source := ⟨"deal-2024", "(16c)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Lucille me te présentera."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "1"), ("pattern", "strong")] }

def ex32a_1 : Datum :=
  { id := "deal2024_ex32a_1"
    source := ⟨"deal-2024", "(32a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Preporâčaha mu te entusiaziarano."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "2"), ("pattern", "meFirst")] }

def ex32a_2 : Datum :=
  { id := "deal2024_ex32a_2"
    source := ⟨"deal-2024", "(32a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Preporâčaha mi te entusiaziarano."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "2"), ("pattern", "meFirst")] }

def ex32b_1 : Datum :=
  { id := "deal2024_ex32b_1"
    source := ⟨"deal-2024", "(32b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Preporâčaha mu me entusiaziarano."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "1"), ("pattern", "meFirst")] }

def ex32b_2 : Datum :=
  { id := "deal2024_ex32b_2"
    source := ⟨"deal-2024", "(32b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Preporâčaha ti me entusiaziarano."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "1"), ("pattern", "meFirst")] }

def ex39a_1 : Datum :=
  { id := "deal2024_ex39a_1"
    source := ⟨"deal-2024", "(39a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi ti ha affidato."
    glossedTokens := []
    context := ""
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "1"), ("pattern", "weak")] }

def ex39a_2 : Datum :=
  { id := "deal2024_ex39a_2"
    source := ⟨"deal-2024", "(39a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi ti ha affidato."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "2"), ("pattern", "weak")] }

def ex39b : Datum :=
  { id := "deal2024_ex39b"
    source := ⟨"deal-2024", "(39b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Me lo ha affidato."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "3"), ("pattern", "weak")] }

def ex39c : Datum :=
  { id := "deal2024_ex39c"
    source := ⟨"deal-2024", "(39c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gli mi ha affidato."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "1"), ("pattern", "weak")] }

def ex51a_1 : Datum :=
  { id := "deal2024_ex51a_1"
    source := ⟨"deal-2024", "(51a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Me lo recomendaron."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "3"), ("pattern", "strictlyDescending")] }

def ex51a_2 : Datum :=
  { id := "deal2024_ex51a_2"
    source := ⟨"deal-2024", "(51a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Te lo recomendaron."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "3"), ("pattern", "strictlyDescending")] }

def ex51a_3 : Datum :=
  { id := "deal2024_ex51a_3"
    source := ⟨"deal-2024", "(51a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Se lo recomendaron."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "3"), ("pattern", "strictlyDescending")] }

def ex51b_1 : Datum :=
  { id := "deal2024_ex51b_1"
    source := ⟨"deal-2024", "(51b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "El te me recomendó."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "2"), ("pattern", "strictlyDescending")] }

def ex51b_2 : Datum :=
  { id := "deal2024_ex51b_2"
    source := ⟨"deal-2024", "(51b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "El te me recomendó."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "1"), ("pattern", "strictlyDescending")] }

def ex51c_1 : Datum :=
  { id := "deal2024_ex51c_1"
    source := ⟨"deal-2024", "(51c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Me le recomendaron."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "1"), ("pattern", "strictlyDescending")] }

def ex51c_2 : Datum :=
  { id := "deal2024_ex51c_2"
    source := ⟨"deal-2024", "(51c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Te le recomendaron."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "2"), ("pattern", "strictlyDescending")] }

def ex60a : Datum :=
  { id := "deal2024_ex60a"
    source := ⟨"deal-2024", "(60a)"⟩
    reportedIn := none
    language := "adyg1241"
    primaryText := "Se wo Ali-jəm wə-sə-tə."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "2"), ("pattern", "strictlyDescending"), ("preference", "io")] }

def ex60b : Datum :=
  { id := "deal2024_ex60b"
    source := ⟨"deal-2024", "(60b)"⟩
    reportedIn := none
    language := "adyg1241"
    primaryText := "Wo se Ali-jəm sə-wə-tə."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "1"), ("pattern", "strictlyDescending"), ("preference", "io")] }

def ex60c : Datum :=
  { id := "deal2024_ex60c"
    source := ⟨"deal-2024", "(60c)"⟩
    reportedIn := none
    language := "adyg1241"
    primaryText := "Sine-m se wo sə-wə-rə-tə."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "1"), ("pattern", "strictlyDescending"), ("preference", "io")] }

def ex61a : Datum :=
  { id := "deal2024_ex61a"
    source := ⟨"deal-2024", "(61a)"⟩
    reportedIn := none
    language := "adyg1241"
    primaryText := "Se Ali-jə wo wə-sə-tə."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "3"), ("pattern", "strictlyDescending"), ("preference", "io")] }

def ex61b : Datum :=
  { id := "deal2024_ex61b"
    source := ⟨"deal-2024", "(61b)"⟩
    reportedIn := none
    language := "adyg1241"
    primaryText := "Wo Ali-jə se sə-wə-tə."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "3"), ("pattern", "strictlyDescending"), ("preference", "io")] }

def ex61c : Datum :=
  { id := "deal2024_ex61c"
    source := ⟨"deal-2024", "(61c)"⟩
    reportedIn := none
    language := "adyg1241"
    primaryText := "Hasan-əm wo se wə-sə-rə-tə."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "2"), ("pattern", "strictlyDescending"), ("preference", "io")] }

def ex62a_1 : Datum :=
  { id := "deal2024_ex62a_1"
    source := ⟨"deal-2024", "(62a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama mi ga bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "3"), ("pattern", "strongOrWeak")] }

def ex62a_2 : Datum :=
  { id := "deal2024_ex62a_2"
    source := ⟨"deal-2024", "(62a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama ti ga bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "3"), ("pattern", "strongOrWeak")] }

def ex62a_3 : Datum :=
  { id := "deal2024_ex62a_3"
    source := ⟨"deal-2024", "(62a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama mu ga bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "3"), ("pattern", "strongOrWeak")] }

def ex62b_1 : Datum :=
  { id := "deal2024_ex62b_1"
    source := ⟨"deal-2024", "(62b)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama mu me bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "1"), ("pattern", "strongOrWeak")] }

def ex62b_2 : Datum :=
  { id := "deal2024_ex62b_2"
    source := ⟨"deal-2024", "(62b)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama mu te bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "2"), ("pattern", "strongOrWeak")] }

def ex63a_1 : Datum :=
  { id := "deal2024_ex63a_1"
    source := ⟨"deal-2024", "(63a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama me mu bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "1"), ("pattern", "strongOrWeak"), ("preference", "io")] }

def ex63a_2 : Datum :=
  { id := "deal2024_ex63a_2"
    source := ⟨"deal-2024", "(63a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama te mu bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "2"), ("pattern", "strongOrWeak"), ("preference", "io")] }

def ex63a_3 : Datum :=
  { id := "deal2024_ex63a_3"
    source := ⟨"deal-2024", "(63a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama ga mu bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("io", "3"), ("do", "3"), ("pattern", "strongOrWeak"), ("preference", "io")] }

def ex63b_1 : Datum :=
  { id := "deal2024_ex63b_1"
    source := ⟨"deal-2024", "(63b)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama ga mi bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "1"), ("do", "3"), ("pattern", "strongOrWeak"), ("preference", "io")] }

def ex63b_2 : Datum :=
  { id := "deal2024_ex63b_2"
    source := ⟨"deal-2024", "(63b)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Mama ga ti bo predstavila."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("io", "2"), ("do", "3"), ("pattern", "strongOrWeak"), ("preference", "io")] }

def all : List Datum := [ex16a_1, ex16a_2, ex16b_1, ex16b_2, ex16b_3, ex16c_1, ex16c_2, ex32a_1, ex32a_2, ex32b_1, ex32b_2, ex39a_1, ex39a_2, ex39b, ex39c, ex51a_1, ex51a_2, ex51a_3, ex51b_1, ex51b_2, ex51c_1, ex51c_2, ex60a, ex60b, ex60c, ex61a, ex61b, ex61c, ex62a_1, ex62a_2, ex62a_3, ex62b_1, ex62b_2, ex63a_1, ex63a_2, ex63a_3, ex63b_1, ex63b_2]

end Deal2024.Examples
