module

public import Linglib.Data.Examples.Schema

/-!
# `WechslerZlatic2000` — typed example data

Auto-generated from `Linglib/Data/Examples/WechslerZlatic2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WechslerZlatic2000.Examples`.
-/

@[expose] public section

namespace WechslerZlatic2000.Examples

def ex_1 : Datum :=
  { id := "wechslerzlatic2000_1"
    source := ⟨"wechsler-zlatic-2000", "(6)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova stara knjiga stalno pada. Molim vas, podignite je."
    glossedTokens := [("Ova", "this-NOM.F.SG"), ("stara", "old-NOM.F.SG"), ("knjiga", "book(F)-NOM.SG"), ("stalno", "always"), ("pada", "fall-3SG"), ("Molim", "please"), ("vas", "you"), ("podignite", "pick.2PL"), ("je", "it.F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "determiner adjective"), ("index", "verb pronoun")] }

def ex_2 : Datum :=
  { id := "wechslerzlatic2000_2"
    source := ⟨"wechsler-zlatic-2000", "(11a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ovo malo devojče je ušlo. Ono je htelo da telefonira."
    glossedTokens := [("Ovo", "this.NT.SG"), ("malo", "little.NT.SG"), ("devojče", "girl.(NT).SG"), ("je", "AUX.3SG"), ("ušlo", "entered.NT.SG"), ("Ono", "it.NT.SG"), ("je", "AUX.SG"), ("htelo", "wanted.NT.SG"), ("da", "that"), ("telefonira", "telephone.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "neuter singular"), ("agreement", "index")] }

def ex_3 : Datum :=
  { id := "wechslerzlatic2000_3"
    source := ⟨"wechsler-zlatic-2000", "(11b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ovo malo devojče je ušlo. Ona je htela da telefonira."
    glossedTokens := [("Ovo", "this.NT.SG"), ("malo", "little.NT.SG"), ("devojče", "girl.(NT).SG"), ("je", "AUX.3SG"), ("ušlo", "entered.NT.SG"), ("Ona", "she.F.SG"), ("je", "AUX.SG"), ("htela", "wanted.F.SG"), ("da", "that"), ("telefonira", "telephone.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "feminine singular"), ("agreement", "pragmatic")] }

def ex_4 : Datum :=
  { id := "wechslerzlatic2000_4"
    source := ⟨"wechsler-zlatic-2000", "(12)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ova stara knjiga"
    glossedTokens := [("ova", "this-NOM.F.SG"), ("stara", "old-NOM.F.SG"), ("knjiga", "book(F)-NOM.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agreement", "concord")] }

def ex_5 : Datum :=
  { id := "wechslerzlatic2000_5"
    source := ⟨"wechsler-zlatic-2000", "(13)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova stara knjiga je pala."
    glossedTokens := [("Ova", "this-F.SG"), ("stara", "old-F.SG"), ("knjiga", "book(F)-NOM.SG"), ("je", "AUX.3SG"), ("pala", "fall-PPRT-F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "participle")] }

def ex_6 : Datum :=
  { id := "wechslerzlatic2000_6"
    source := ⟨"wechsler-zlatic-2000", "(19a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Taj stari sudija je dobro sudio. On ..."
    glossedTokens := [("Taj", "that.M"), ("stari", "old.M"), ("sudija", "judge"), ("je", "AUX"), ("dobro", "well"), ("sudio", "judged.M"), ("On", "3M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "sudija"), ("sex", "male"), ("gender", "masculine")] }

def ex_7 : Datum :=
  { id := "wechslerzlatic2000_7"
    source := ⟨"wechsler-zlatic-2000", "(19b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta stara sudija je dobro sudila. Ona ..."
    glossedTokens := [("Ta", "that.F"), ("stara", "old.F"), ("sudija", "judge"), ("je", "AUX"), ("dobro", "well"), ("sudila", "judged.F"), ("Ona", "3F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "sudija"), ("sex", "female"), ("gender", "feminine")] }

def ex_8 : Datum :=
  { id := "wechslerzlatic2000_8"
    source := ⟨"wechsler-zlatic-2000", "(21a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "taj kit"
    glossedTokens := [("taj", "that.M"), ("kit", "whale")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "kit"), ("sex", "unspecified")] }

def ex_9 : Datum :=
  { id := "wechslerzlatic2000_9"
    source := ⟨"wechsler-zlatic-2000", "(21b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Kit je podojio svoje mladunče."
    glossedTokens := [("Kit", "whale"), ("je", "AUX.SG"), ("podojio", "nursed.3.M.SG"), ("svoje", "self"), ("mladunče", "offspring")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "kit"), ("gender", "masculine")] }

def ex_10 : Datum :=
  { id := "wechslerzlatic2000_10"
    source := ⟨"wechsler-zlatic-2000", "(23a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova telad je pasla."
    glossedTokens := [("Ova", "this.F.SG"), ("telad", "calves"), ("je", "AUX.3SG"), ("pasla", "grazed.F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ova telad su pasla.", .acceptable)]
    readings := []
    paperFeatures := [("noun", "telad"), ("predicate", "nondistributive")] }

def ex_11 : Datum :=
  { id := "wechslerzlatic2000_11"
    source := ⟨"wechsler-zlatic-2000", "(23b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova telad imaju po dva roga."
    glossedTokens := [("Ova", "this.NT.PL"), ("telad", "calves"), ("imaju", "have.PL"), ("po", "each"), ("dva", "two"), ("roga", "horns")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ova telad ima po dva roga.", .ungrammatical), ("Ova telad ima po dva roga.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "telad"), ("predicate", "distributive")] }

def ex_12 : Datum :=
  { id := "wechslerzlatic2000_12"
    source := ⟨"wechsler-zlatic-2000", "(28)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Vratio mi je ovaj ludi Steva violinu koju sam mu pozajmio."
    glossedTokens := [("Vratio", "returned.1SG"), ("mi", "me"), ("je", "AUX.3SG"), ("ovaj", "this.NOM.M.SG"), ("ludi", "crazy.NOM.M.SG"), ("Steva", "Steve.NOM"), ("violinu", "violin-ACC"), ("koju", "which"), ("sam", "AUX.1SG"), ("mu", "3DAT.M.SG"), ("pozajmio", "loaned")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "Steva"), ("declension", "II"), ("gender", "masculine")] }

def ex_13 : Datum :=
  { id := "wechslerzlatic2000_13"
    source := ⟨"wechsler-zlatic-2000", "(30a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta mušterija je došla."
    glossedTokens := [("Ta", "that.F"), ("mušterija", "customer"), ("je", "AUX"), ("došla", "came.F")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mušterija"), ("sex", "unspecified")] }

def ex_14 : Datum :=
  { id := "wechslerzlatic2000_14"
    source := ⟨"wechsler-zlatic-2000", "(30b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Taj mušterija je došao."
    glossedTokens := [("Taj", "that.M"), ("mušterija", "customer"), ("je", "AUX"), ("došao", "came.M")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mušterija"), ("sex", "male")] }

def ex_15 : Datum :=
  { id := "wechslerzlatic2000_15"
    source := ⟨"wechsler-zlatic-2000", "(33)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Te sudije su došle."
    glossedTokens := [("Te", "those.F.PL"), ("sudije", "judge(F).PL"), ("su", "AUX.3PL"), ("došle", "came.F.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "sudije"), ("number", "plural")] }

def ex_16 : Datum :=
  { id := "wechslerzlatic2000_16"
    source := ⟨"wechsler-zlatic-2000", "(34)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ove naočare su nove. One ..."
    glossedTokens := [("Ove", "this.PL"), ("naočare", "glasses"), ("su", "be.3PL"), ("nove", "new.PL"), ("One", "3PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "naočare"), ("type", "plurale tantum")] }

def ex_17 : Datum :=
  { id := "wechslerzlatic2000_17"
    source := ⟨"wechsler-zlatic-2000", "(36)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Sreo sam braću. Ona su došla."
    glossedTokens := [("Sreo", "met.1SG"), ("sam", "AUX"), ("braću", "brothers.ACC"), ("Ona", "they.N.PL"), ("su", "AUX.3.PL"), ("došla", "came.N.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "braća"), ("pronoun", "neuter plural")] }

def ex_18 : Datum :=
  { id := "wechslerzlatic2000_18"
    source := ⟨"wechsler-zlatic-2000", "(37)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ovu dobru braću"
    glossedTokens := [("ovu", "this-ACC.F.SG"), ("dobru", "good-ACC.F.SG"), ("braću", "brothers-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "braća"), ("concord", "feminine singular")] }

def ex_19 : Datum :=
  { id := "wechslerzlatic2000_19"
    source := ⟨"wechsler-zlatic-2000", "(38)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ovom dobrom braćom"
    glossedTokens := [("ovom", "this-INS.F.SG"), ("dobrom", "good-INS.F.SG"), ("braćom", "brothers-INS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "braća"), ("concord", "feminine singular")] }

def ex_20 : Datum :=
  { id := "wechslerzlatic2000_20"
    source := ⟨"wechsler-zlatic-2000", "(40)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Sreo sam gospodu. Oni su bili jako ljubazni."
    glossedTokens := [("Sreo", "met.1SG"), ("sam", "AUX"), ("gospodu", "gentlemen.ACC"), ("Oni", "they.M.PL"), ("su", "AUX.PL"), ("bili", "were.M.PL"), ("jako", "very"), ("ljubazni", "kind.M.PL")]
    context := ""
    judgment := .acceptable
    alternatives := [("Sreo sam gospodu. Ona su bila jako ljubazna.", .ungrammatical), ("Sreo sam gospodu. Ona su bila jako ljubazna.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "gospoda"), ("pronoun", "masculine plural")] }

def ex_21 : Datum :=
  { id := "wechslerzlatic2000_21"
    source := ⟨"wechsler-zlatic-2000", "(41)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Posmatrali smo ovu dobru decu. Ona su spavala."
    glossedTokens := [("Posmatrali", "watched.1.PL"), ("smo", "AUX"), ("ovu", "this.F.SG"), ("dobru", "good.F.SG"), ("decu", "children.F.SG"), ("Ona", "they.N.PL"), ("su", "AUX.3PL"), ("spavala", "slept.NT.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("concord", "feminine singular"), ("index", "neuter plural")] }

def ex_22 : Datum :=
  { id := "wechslerzlatic2000_22"
    source := ⟨"wechsler-zlatic-2000", "(42)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Deca su spavala. Mi smo ih videli."
    glossedTokens := [("Deca", "children"), ("su", "AUX.3PL"), ("spavala", "slept.NT.PL"), ("Mi", "we"), ("smo", "AUX.PL"), ("ih", "them.ACC.PL"), ("videli", "saw")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("index", "neuter plural")] }

def ex_23 : Datum :=
  { id := "wechslerzlatic2000_23"
    source := ⟨"wechsler-zlatic-2000", "(43)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta dobra deca su došla."
    glossedTokens := [("Ta", "that.F.SG"), ("dobra", "good.F.SG"), ("deca", "children(F.SG)"), ("su", "AUX.3PL"), ("došla", "come-PPRT.N.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "participle")] }

def ex_24 : Datum :=
  { id := "wechslerzlatic2000_24"
    source := ⟨"wechsler-zlatic-2000", "(44)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta dobra deca dolaze."
    glossedTokens := [("Ta", "that.F.SG"), ("dobra", "good.F.SG"), ("deca", "children(F.SG)"), ("dolaze", "come.3.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "finite verb")] }

def ex_25 : Datum :=
  { id := "wechslerzlatic2000_25"
    source := ⟨"wechsler-zlatic-2000", "(50)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ja smatram decu gladnom."
    glossedTokens := [("Ja", "I"), ("smatram", "consider"), ("decu", "children.ACC(F.SG[N.PL])"), ("gladnom", "hungry.INST.FEM.SG")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ja smatram decu gladnim.", .ungrammatical), ("Ja smatram decu gladnim.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "secondary predicate")] }

def ex_26 : Datum :=
  { id := "wechslerzlatic2000_26"
    source := ⟨"wechsler-zlatic-2000", "(51)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jelena i deca su došli."
    glossedTokens := [("Jelena", "Yelena(F.SG[F.SG])"), ("i", "and"), ("deca", "children(F.SG[N.PL])"), ("su", "AUX.3.PL"), ("došli", "came.M.PL")]
    context := ""
    judgment := .acceptable
    alternatives := [("Jelena i deca su došle.", .ungrammatical), ("Jelena i deca su došle.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "coordination")] }

def ex_27 : Datum :=
  { id := "wechslerzlatic2000_27"
    source := ⟨"wechsler-zlatic-2000", "(52)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jelena i deca su gladni."
    glossedTokens := [("Jelena", "Yelena(F.SG[F.SG])"), ("i", "and"), ("deca", "children(F.SG[N.PL])"), ("su", "AUX.3.PL"), ("gladni", "hungry.M.PL")]
    context := ""
    judgment := .acceptable
    alternatives := [("Jelena i deca su gladne.", .ungrammatical), ("Jelena i deca su gladne.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "coordination")] }

def ex_28 : Datum :=
  { id := "wechslerzlatic2000_28"
    source := ⟨"wechsler-zlatic-2000", "(53)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta deca i ta čudovišta su se lepo igrala."
    glossedTokens := [("Ta", "that"), ("deca", "children(F.SG[N.PL])"), ("i", "and"), ("ta", "those"), ("čudovišta", "monsters(N.PL[N.PL])"), ("su", "AUX"), ("se", "REFL"), ("lepo", "well"), ("igrala", "played.N.PL")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ta deca i ta čudovišta su se lepo igrali.", .marginal), ("Ta deca i ta čudovišta su se lepo igrali.", .marginal)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "coordination")] }

def ex_29 : Datum :=
  { id := "wechslerzlatic2000_29"
    source := ⟨"wechsler-zlatic-2000", "(54)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "deca koja su tada bila"
    glossedTokens := [("deca", "children"), ("koja", "who.N.PL"), ("su", "AUX.PL"), ("tada", "then"), ("bila", "were")]
    context := ""
    judgment := .acceptable
    alternatives := [("deca koja je tada bila", .ungrammatical), ("deca koja je tada bila", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "nominative")] }

def ex_30 : Datum :=
  { id := "wechslerzlatic2000_30"
    source := ⟨"wechsler-zlatic-2000", "(55)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "deca koju sam video"
    glossedTokens := [("deca", "children"), ("koju", "who.ACC.F.SG"), ("sam", "AUX.1.SG"), ("video", "saw")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "accusative")] }

def ex_31 : Datum :=
  { id := "wechslerzlatic2000_31"
    source := ⟨"wechsler-zlatic-2000", "(56)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "deca koje se svi plaše"
    glossedTokens := [("deca", "children"), ("koje", "who.GEN.F.SG"), ("se", "REFL"), ("svi", "all"), ("plaše", "fear")]
    context := ""
    judgment := .acceptable
    alternatives := [("deca kojih se svi plaše", .acceptable), ("deca kojih se svi plaše", .acceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "genitive")] }

def ex_32 : Datum :=
  { id := "wechslerzlatic2000_32"
    source := ⟨"wechsler-zlatic-2000", "(59)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "moja deca, što ih nije briga nizašta"
    glossedTokens := [("moja", "my"), ("deca", "children"), ("što", "that"), ("ih", "3.ACC.PL"), ("nije", "NEG.AUX"), ("briga", "care"), ("nizašta", "nothing")]
    context := ""
    judgment := .acceptable
    alternatives := [("moja deca, što je nije briga nizašta", .ungrammatical), ("moja deca, što je nije briga nizašta", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "što")] }

def ex_33 : Datum :=
  { id := "wechslerzlatic2000_33"
    source := ⟨"wechsler-zlatic-2000", "(61b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "moja deca, što ih se svi plaše"
    glossedTokens := [("moja", "my"), ("deca", "children"), ("što", "that"), ("ih", "3.GEN.PL"), ("se", "REFL"), ("svi", "all"), ("plaše", "fear")]
    context := ""
    judgment := .acceptable
    alternatives := [("moja deca, što je se svi plaše", .ungrammatical)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "što")] }

def ex_34 : Datum :=
  { id := "wechslerzlatic2000_34"
    source := ⟨"wechsler-zlatic-2000", "(64)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Su Majestad suprema está contento. Él ..."
    glossedTokens := [("Su", "his"), ("Majestad", "majesty"), ("suprema", "supreme.F"), ("está", "is"), ("contento", "happy.M"), ("Él", "he")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "Majestad"), ("concord", "feminine"), ("index", "masculine")] }

def ex_35 : Datum :=
  { id := "wechslerzlatic2000_35"
    source := ⟨"wechsler-zlatic-2000", "(62)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "moja deca, što je se svi plaše"
    glossedTokens := [("moja", "my"), ("deca", "children"), ("što", "that"), ("je", "3.GEN.F.SG"), ("se", "REFL"), ("svi", "all"), ("plaše", "fear")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "što"), ("resumptive", "singular")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27, ex_28, ex_29, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35]

end WechslerZlatic2000.Examples
