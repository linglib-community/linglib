module

public import Linglib.Data.Examples.Schema

/-!
# `AhnKocabDavidson2026` — typed example data

Auto-generated from `Linglib/Data/Examples/AhnKocabDavidson2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AhnKocabDavidson2026.Examples`.
-/

@[expose] public section

namespace AhnKocabDavidson2026.Examples

def ex9 : Datum :=
  { id := "ahnkocabdavidson2026_ex9"
    source := ⟨"ahn-kocab-davidson-2026", "(9)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY ENTER CLUB. MUSIC ON. DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "consultant"), ("verb", "DANCE")] }

def ex10a : Datum :=
  { id := "ahnkocabdavidson2026_ex10a"
    source := ⟨"ahn-kocab-davidson-2026", "(10a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amer1248"
    primaryText := "BOY ENTER CLUB. MUSIC ON. SEE GIRL READ. DANCE."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "consultant"), ("verb", "DANCE")] }

def ex10b : Datum :=
  { id := "ahnkocabdavidson2026_ex10b"
    source := ⟨"ahn-kocab-davidson-2026", "(10b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY IXA ENTER CLUB. SEE GIRL IXB READ. MUSIC ON. (IXA) DANCEA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "consultant"), ("verb", "DANCE")] }

def ex11a : Datum :=
  { id := "ahnkocabdavidson2026_ex11a"
    source := ⟨"ahn-kocab-davidson-2026", "(11a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "SUE HANG-OUT MARY. PUSH."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "consultant"), ("verb", "PUSH")] }

def ex11b : Datum :=
  { id := "ahnkocabdavidson2026_ex11b"
    source := ⟨"ahn-kocab-davidson-2026", "(11b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "SUE IXA HANG-OUT MARY IXB. (IXA) PUSHB (IXB)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "consultant"), ("verb", "PUSH")] }

def ex11c : Datum :=
  { id := "ahnkocabdavidson2026_ex11c"
    source := ⟨"ahn-kocab-davidson-2026", "(11c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "SUE HANG-OUT MARY. MARY SAY SOMETHING BAD. SUE ANGRY. PUSH."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "consultant"), ("verb", "PUSH")] }

def ex18 : Datum :=
  { id := "ahnkocabdavidson2026_ex18"
    source := ⟨"ahn-kocab-davidson-2026", "(18)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY ENTER CLUB. MUSIC ON. BOY DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("BOY ENTER CLUB. MUSIC ON. ∅ DANCE.", .acceptable)]
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "consultant"), ("verb", "DANCE")] }

def ex19 : Datum :=
  { id := "ahnkocabdavidson2026_ex19"
    source := ⟨"ahn-kocab-davidson-2026", "(19)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY IXA ENTER CLUB. MUSIC ON. IXA DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "consultant"), ("verb", "DANCE")] }

def ex20 : Datum :=
  { id := "ahnkocabdavidson2026_ex20"
    source := ⟨"ahn-kocab-davidson-2026", "(20)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY ENTER CLUB. MUSIC ON. SEE GIRL READ. BOY DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("BOY ENTER CLUB. MUSIC ON. SEE GIRL READ. ∅ DANCE.", .marginal)]
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "consultant"), ("verb", "DANCE")] }

def ex20null : Datum :=
  { id := "ahnkocabdavidson2026_ex20null"
    source := ⟨"ahn-kocab-davidson-2026", "(20), null argument"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY ENTER CLUB. MUSIC ON. SEE GIRL READ. DANCE."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "consultant"), ("verb", "DANCE")] }

def ex21 : Datum :=
  { id := "ahnkocabdavidson2026_ex21"
    source := ⟨"ahn-kocab-davidson-2026", "(21)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY IXA ENTER CLUB. MUSIC ON. SEE GIRL IXB READ. IXA DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "consultant"), ("verb", "DANCE")] }

def a1_1_one_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_1_one_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 1. DANCE [1,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY SIT CLASS. CLASS FINISH, DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "number"), ("verb", "DANCE")] }

def a1_1_one_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_1_one_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 1. DANCE [1,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY IXA SIT CLASS. CLASS FINISH, IXA DANCEA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "number"), ("verb", "DANCE")] }

def a1_1_two_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_1_two_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 1. DANCE [2,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY SIT CLASS. GIRL READ. CLASS FINISH, DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "number"), ("verb", "DANCE")] }

def a1_1_two_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_1_two_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 1. DANCE [2,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY IXA SIT-IN CLASS. GIRL IXB READ. CLASS FINISH, IXA DANCE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "number"), ("verb", "DANCE")] }

def a1_2_one_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_2_one_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 2. FALL [1,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LINDA GO-TO BEACH. LINDA WALK NEAR WATER. FALL."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "number"), ("verb", "FALL")] }

def a1_2_one_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_2_one_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 2. FALL [1,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LINDA IXA GO-TO BEACH. IXA WALK NEAR WATER. IXA FALLA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "number"), ("verb", "FALL")] }

def a1_2_two_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_2_two_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 2. FALL [2,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LINDA GO-TO BEACH. WILL WALK NEAR WATER. FALL."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "number"), ("verb", "FALL")] }

def a1_2_two_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_2_two_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 2. FALL [2,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LINDA IXA GO-TO BEACH. WILL IXB WALK NEAR WATER. IXA FALLA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "number"), ("verb", "FALL")] }

def a1_3_one_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_3_one_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 3. JUMP [1,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL GO-TO MALL. GIRL WALK. JUMP."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "number"), ("verb", "JUMP")] }

def a1_3_one_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_3_one_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 3. JUMP [1,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL IXA GO-TO MALL. IXA WALK. IXA JUMPA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "number"), ("verb", "JUMP")] }

def a1_3_two_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_3_two_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 3. JUMP [2,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL GO-TO MALL. BOY WALK. JUMP."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "number"), ("verb", "JUMP")] }

def a1_3_two_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_3_two_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 3. JUMP [2,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL IXA GO-TO MALL. BOY IXB WALK. IXA JUMPA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "number"), ("verb", "JUMP")] }

def a1_4_one_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_4_one_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 4. RUN [1,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "DOCTOR GO-TO PARK. DOCTOR DRINK WATER."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "number"), ("verb", "RUN")] }

def a1_4_one_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_4_one_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 4. RUN [1,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "DOCTOR IXA GO-TO PARK. IXA DRINK WATER. IXA RUNA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "number"), ("verb", "RUN")] }

def a1_4_two_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_4_two_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 4. RUN [2,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "DOCTOR GO-TO PARK. POLICE-OFFICER DRINK WATER. RUN."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "number"), ("verb", "RUN")] }

def a1_4_two_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_4_two_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 4. RUN [2,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "DOCTOR IXA GO-TO PARK. POLICE-OFFICER IXB DRINK WATER. IXA RUNA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "number"), ("verb", "RUN")] }

def a1_5_narr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_5_narr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 5. VISIT [+narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LISA GO-TO PARK. DONNA NEED HELP MOVE COUCH. TOMORROW VISIT."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "narrative"), ("verb", "VISIT")] }

def a1_5_noNarr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_5_noNarr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 5. VISIT [-narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LISA GO-TO PARK. DONNA READ. TOMORROW VISIT."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "narrative"), ("verb", "VISIT")] }

def a1_5_narr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_5_narr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 5. VISIT [+narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LISA IXA GO-TO PARK. DONNA IXB NEED HELP MOVE COUCH. TOMORROW IXA AVISITB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "narrative"), ("verb", "VISIT")] }

def a1_5_noNarr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_5_noNarr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 5. VISIT [-narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "LISA IXA GO-TO PARK. DONNA IXB READ. TOMORROW IXA AVISITB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "narrative"), ("verb", "VISIT")] }

def a1_6_narr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_6_narr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 6. YELL [+narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "SUE GO-TO SCHOOL. MARY SAY SOMETHING BAD. YELL."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "narrative"), ("verb", "YELL")] }

def a1_6_narr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_6_narr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 6. YELL [+narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "SUE IXA GO-TO SCHOOL. MARY IXB SAY SOMETHING BAD. IXA AYELLB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "narrative"), ("verb", "YELL")] }

def a1_6_noNarr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_6_noNarr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 6. YELL [-narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "SUE GO-TO SCHOOL. MARY READ. YELL."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "narrative"), ("verb", "YELL")] }

def a1_6_noNarr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_6_noNarr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 6. YELL [-narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "SUE IXA GO-TO SCHOOL. MARY IXB READ. IXA AYELLB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "narrative"), ("verb", "YELL")] }

def a1_7_narr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_7_narr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 7. HELP [+narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JAMES DAVID GO-TO WORK. DAVID NEED HELP LIFT HEAVY BOX. HELP."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "narrative"), ("verb", "HELP")] }

def a1_7_narr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_7_narr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 7. HELP [+narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JAMES IXA DAVID IXB GO-TO WORK. IXB NEED HELP LIFT HEAVY BOX. IXA AHELPB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "narrative"), ("verb", "HELP")] }

def a1_7_noNarr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_7_noNarr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 7. HELP [-narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JAMES DAVID GO-TO WORK. HELP."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "narrative"), ("verb", "HELP")] }

def a1_7_noNarr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_7_noNarr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 7. HELP [-narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JAMES IXA DAVID IXB GO-TO WORK. IXA AHELPB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "narrative"), ("verb", "HELP")] }

def a1_8_narr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_8_narr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 8. ASK DIRECTION [+narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL TRAVEL. GIRL LOST. WOMAN SIT. ASK DIRECTION."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "narrative"), ("verb", "ASK")] }

def a1_8_narr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_8_narr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 8. ASK DIRECTION [+narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL IXA TRAVEL. IXA LOST. WOMAN IXB SIT. IXA AASKB IXB DIRECTION."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "narrative"), ("verb", "ASK")] }

def a1_8_noNarr_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_8_noNarr_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 8. ASK DIRECTION [-narr,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL TRAVEL. GIRL READ. WOMAN SIT. ASK DIRECTION."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "narrative"), ("verb", "ASK")] }

def a1_8_noNarr_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_8_noNarr_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 8. ASK DIRECTION [-narr,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIRL IXA TRAVEL. IXA READ. WOMAN IXB SIT. IXA AASKB IXB DIRECTION."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "narrative"), ("verb", "ASK")] }

def a1_9_inanimate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_9_inanimate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 9. PUNCH [-animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JANE VISIT PARK. JANE SEE TREE. PUNCH."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "animacy"), ("verb", "PUNCH")] }

def a1_9_inanimate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_9_inanimate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 9. PUNCH [-animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JANE IXA VISIT PARK. IXA SEE TREE IXB. IXA APUNCHB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "animacy"), ("verb", "PUNCH")] }

def a1_9_animate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_9_animate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 9. PUNCH [+animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JANE VISIT PARK. JANE SEE ANA. PUNCH."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "animacy"), ("verb", "PUNCH")] }

def a1_9_animate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_9_animate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 9. PUNCH [+animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JANE IXA VISIT PARK. IXA SEE ANA IXB. IXA APUNCHB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "animacy"), ("verb", "PUNCH")] }

def a1_10_inanimate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_10_inanimate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 10. KICK [-animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JOHN SIT CLASS. JOHN SEE CABINET. CLASS FINISH, KICK."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "animacy"), ("verb", "KICK")] }

def a1_10_inanimate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_10_inanimate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 10. KICK [-animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JOHN IXA SIT CLASS. IXA SEE CABINET IXB. CLASS FINISH, IXA AKICKB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "animacy"), ("verb", "KICK")] }

def a1_10_animate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_10_animate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 10. KICK [+animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JOHN SIT CLASS. JOHN SEE BILL. CLASS FINISH, KICK."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "animacy"), ("verb", "KICK")] }

def a1_10_animate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_10_animate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 10. KICK [+animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JOHN IXA SIT CLASS. IXA SEE BILL IXB. CLASS FINISH, IXA AKICKB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "animacy"), ("verb", "KICK")] }

def a1_11_inanimate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_11_inanimate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 11. PUSH [-animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "MIKE ENTER LIVING-ROOM. MIKE SEE TV. PUSH."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "animacy"), ("verb", "PUSH")] }

def a1_11_inanimate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_11_inanimate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 11. PUSH [-animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "MIKE IXA ENTER LIVING-ROOM. IXA SEE TV IXB. IXA APUSHB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "animacy"), ("verb", "PUSH")] }

def a1_11_animate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_11_animate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 11. PUSH [+animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "MIKE ENTER LIVING-ROOM. MIKE SEE BOB. PUSH."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "animacy"), ("verb", "PUSH")] }

def a1_11_animate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_11_animate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 11. PUSH [+animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "MIKE IXA ENTER LIVING-ROOM. IXA SEE BOB IXB. IXA APUSHB IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "animacy"), ("verb", "PUSH")] }

def a1_12_inanimate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_12_inanimate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 12. TAKE-PIC [-animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY ENTER STORE. BOY SEE FLOWER. TAKE PICTURE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "true"), ("condition", "animacy"), ("verb", "TAKE-PICTURE")] }

def a1_12_inanimate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_12_inanimate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 12. TAKE-PIC [-animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY IXA ENTER STORE. IXA SEE FLOWER IXB. IXA BTAKE-PICTUREA IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "true"), ("condition", "animacy"), ("verb", "TAKE-PICTURE")] }

def a1_12_animate_noLocus : Datum :=
  { id := "ahnkocabdavidson2026_a1_12_animate_noLocus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 12. TAKE-PIC [+animate,-locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY ENTER STORE. BOY SEE MAN. TAKE-PICTURE."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "false"), ("resolved", "false"), ("condition", "animacy"), ("verb", "TAKE-PICTURE")] }

def a1_12_animate_locus : Datum :=
  { id := "ahnkocabdavidson2026_a1_12_animate_locus"
    source := ⟨"ahn-kocab-davidson-2026", "Appendix A1, 12. TAKE-PIC [+animate,+locus]"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "BOY IXA ENTER STORE. IXA SEE MAN IXB. IXA BTAKE-PICTUREA IXB."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("locus", "true"), ("resolved", "false"), ("condition", "animacy"), ("verb", "TAKE-PICTURE")] }

def all : List Datum := [ex9, ex10a, ex10b, ex11a, ex11b, ex11c, ex18, ex19, ex20, ex20null, ex21, a1_1_one_noLocus, a1_1_one_locus, a1_1_two_noLocus, a1_1_two_locus, a1_2_one_noLocus, a1_2_one_locus, a1_2_two_noLocus, a1_2_two_locus, a1_3_one_noLocus, a1_3_one_locus, a1_3_two_noLocus, a1_3_two_locus, a1_4_one_noLocus, a1_4_one_locus, a1_4_two_noLocus, a1_4_two_locus, a1_5_narr_noLocus, a1_5_noNarr_noLocus, a1_5_narr_locus, a1_5_noNarr_locus, a1_6_narr_noLocus, a1_6_narr_locus, a1_6_noNarr_noLocus, a1_6_noNarr_locus, a1_7_narr_noLocus, a1_7_narr_locus, a1_7_noNarr_noLocus, a1_7_noNarr_locus, a1_8_narr_noLocus, a1_8_narr_locus, a1_8_noNarr_noLocus, a1_8_noNarr_locus, a1_9_inanimate_noLocus, a1_9_inanimate_locus, a1_9_animate_noLocus, a1_9_animate_locus, a1_10_inanimate_noLocus, a1_10_inanimate_locus, a1_10_animate_noLocus, a1_10_animate_locus, a1_11_inanimate_noLocus, a1_11_inanimate_locus, a1_11_animate_noLocus, a1_11_animate_locus, a1_12_inanimate_noLocus, a1_12_inanimate_locus, a1_12_animate_noLocus, a1_12_animate_locus]

end AhnKocabDavidson2026.Examples
