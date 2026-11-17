module

public import Linglib.Data.Examples.Schema

/-!
# `Herce2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Herce2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Herce2023.Examples`.
-/

@[expose] public section

namespace Herce2023.Examples

def venir_1sg_ind : Datum :=
  { id := "herce2023_venir_1sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "veng-o"
    glossedTokens := [("veng-o", "come-1SG.PRS.IND")]
    glossedWords := [⟨['v', 'e', 'n', 'g', '-', 'o'], ['c', 'o', 'm', 'e', '-', '1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], [⟨['v', 'e', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩, ⟨['o'], ['1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.IND"), ("lexeme", "venir"), ("stem", "veng")] }

def venir_2sg_ind : Datum :=
  { id := "herce2023_venir_2sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "vien-es"
    glossedTokens := [("vien-es", "come-2SG.PRS.IND")]
    glossedWords := [⟨['v', 'i', 'e', 'n', '-', 'e', 's'], ['c', 'o', 'm', 'e', '-', '2', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], [⟨['v', 'i', 'e', 'n'], ['c', 'o', 'm', 'e'], none⟩, ⟨['e', 's'], ['2', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "2SG.PRS.IND"), ("lexeme", "venir"), ("stem", "vien")] }

def venir_1pl_ind : Datum :=
  { id := "herce2023_venir_1pl_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "ven-imos"
    glossedTokens := [("ven-imos", "come-1PL.PRS.IND")]
    glossedWords := [⟨['v', 'e', 'n', '-', 'i', 'm', 'o', 's'], ['c', 'o', 'm', 'e', '-', '1', 'P', 'L', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], [⟨['v', 'e', 'n'], ['c', 'o', 'm', 'e'], none⟩, ⟨['i', 'm', 'o', 's'], ['1', 'P', 'L', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "1PL.PRS.IND"), ("lexeme", "venir"), ("stem", "ven")] }

def venir_1sg_sbjv : Datum :=
  { id := "herce2023_venir_1sg_sbjv"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "veng-a"
    glossedTokens := [("veng-a", "come-1SG.PRS.SBJV")]
    glossedWords := [⟨['v', 'e', 'n', 'g', '-', 'a'], ['c', 'o', 'm', 'e', '-', '1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V'], [⟨['v', 'e', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩, ⟨['a'], ['1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.SBJV"), ("lexeme", "venir"), ("stem", "veng")] }

def nacer_1sg_ind : Datum :=
  { id := "herce2023_nacer_1sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "naθk-o"
    glossedTokens := [("naθk-o", "be.born-1SG.PRS.IND")]
    glossedWords := [⟨['n', 'a', 'θ', 'k', '-', 'o'], ['b', 'e', '.', 'b', 'o', 'r', 'n', '-', '1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], [⟨['n', 'a', 'θ', 'k'], ['b', 'e', '.', 'b', 'o', 'r', 'n'], none⟩, ⟨['o'], ['1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.IND"), ("lexeme", "nacer"), ("stem", "naθk")] }

def nacer_1pl_ind : Datum :=
  { id := "herce2023_nacer_1pl_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "naθ-emos"
    glossedTokens := [("naθ-emos", "be.born-1PL.PRS.IND")]
    glossedWords := [⟨['n', 'a', 'θ', '-', 'e', 'm', 'o', 's'], ['b', 'e', '.', 'b', 'o', 'r', 'n', '-', '1', 'P', 'L', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], [⟨['n', 'a', 'θ'], ['b', 'e', '.', 'b', 'o', 'r', 'n'], none⟩, ⟨['e', 'm', 'o', 's'], ['1', 'P', 'L', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "1PL.PRS.IND"), ("lexeme", "nacer"), ("stem", "naθ")] }

def caber_1sg_ind : Datum :=
  { id := "herce2023_caber_1sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "kep-o"
    glossedTokens := [("kep-o", "fit-1SG.PRS.IND")]
    glossedWords := [⟨['k', 'e', 'p', '-', 'o'], ['f', 'i', 't', '-', '1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], [⟨['k', 'e', 'p'], ['f', 'i', 't'], none⟩, ⟨['o'], ['1', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.IND"), ("lexeme", "caber"), ("stem", "kep")] }

def caber_2sg_ind : Datum :=
  { id := "herce2023_caber_2sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "kab-es"
    glossedTokens := [("kab-es", "fit-2SG.PRS.IND")]
    glossedWords := [⟨['k', 'a', 'b', '-', 'e', 's'], ['f', 'i', 't', '-', '2', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], [⟨['k', 'a', 'b'], ['f', 'i', 't'], none⟩, ⟨['e', 's'], ['2', 'S', 'G', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "2SG.PRS.IND"), ("lexeme", "caber"), ("stem", "kab")] }

def ra_npst_1sg : Datum :=
  { id := "herce2023_ra_npst_1sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-hi"
    glossedTokens := [("ra-hi", "come-NPST.1SG")]
    glossedWords := [⟨['r', 'a', '-', 'h', 'i'], ['c', 'o', 'm', 'e', '-', 'N', 'P', 'S', 'T', '.', '1', 'S', 'G'], [⟨['r', 'a'], ['c', 'o', 'm', 'e'], none⟩, ⟨['h', 'i'], ['N', 'P', 'S', 'T', '.', '1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "NPST.1SG"), ("lexeme", "ra")] }

def ra_npst_2sg : Datum :=
  { id := "herce2023_ra_npst_2sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-he-n"
    glossedTokens := [("ra-he-n", "come-NPST-1PL/2")]
    glossedWords := [⟨['r', 'a', '-', 'h', 'e', '-', 'n'], ['c', 'o', 'm', 'e', '-', 'N', 'P', 'S', 'T', '-', '1', 'P', 'L', '/', '2'], [⟨['r', 'a'], ['c', 'o', 'm', 'e'], none⟩, ⟨['h', 'e'], ['N', 'P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'P', 'L', '/', '2'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "NPST.2SG"), ("lexeme", "ra")] }

def ra_npst_3sg : Datum :=
  { id := "herce2023_ra_npst_3sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-ni"
    glossedTokens := [("ra-ni", "come-NPST.3")]
    glossedWords := [⟨['r', 'a', '-', 'n', 'i'], ['c', 'o', 'm', 'e', '-', 'N', 'P', 'S', 'T', '.', '3'], [⟨['r', 'a'], ['c', 'o', 'm', 'e'], none⟩, ⟨['n', 'i'], ['N', 'P', 'S', 'T', '.', '3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "NPST.3SG"), ("lexeme", "ra")] }

def ra_pst_2sg : Datum :=
  { id := "herce2023_ra_pst_2sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-n-su"
    glossedTokens := [("ra-n-su", "come-1PL/2-PST")]
    glossedWords := [⟨['r', 'a', '-', 'n', '-', 's', 'u'], ['c', 'o', 'm', 'e', '-', '1', 'P', 'L', '/', '2', '-', 'P', 'S', 'T'], [⟨['r', 'a'], ['c', 'o', 'm', 'e'], none⟩, ⟨['n'], ['1', 'P', 'L', '/', '2'], some '-'⟩, ⟨['s', 'u'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "PST.2SG"), ("lexeme", "ra")] }

def ra_pst_1sg : Datum :=
  { id := "herce2023_ra_pst_1sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-ju"
    glossedTokens := [("ra-ju", "come-PST")]
    glossedWords := [⟨['r', 'a', '-', 'j', 'u'], ['c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], [⟨['r', 'a'], ['c', 'o', 'm', 'e'], none⟩, ⟨['j', 'u'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "PST.1SG"), ("lexeme", "ra")] }

def all : List Datum := [venir_1sg_ind, venir_2sg_ind, venir_1pl_ind, venir_1sg_sbjv, nacer_1sg_ind, nacer_1pl_ind, caber_1sg_ind, caber_2sg_ind, ra_npst_1sg, ra_npst_2sg, ra_npst_3sg, ra_pst_2sg, ra_pst_1sg]

end Herce2023.Examples
