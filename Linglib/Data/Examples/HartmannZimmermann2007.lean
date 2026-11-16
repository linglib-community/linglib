module

public import Linglib.Data.Examples.Schema

/-!
# `HartmannZimmermann2007` — typed example data

Auto-generated from `Linglib/Data/Examples/HartmannZimmermann2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartmannZimmermann2007.Examples`.
-/

@[expose] public section

namespace HartmannZimmermann2007.Examples

def ex3a : Datum :=
  { id := "hartmannzimmermann2007_ex3a"
    source := ⟨"hartmann-zimmermann-2007", "(3a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kandè cee ta-kèe dafà kiifii."
    glossedTokens := [("Kandè", "Kande"), ("cee", "PRT"), ("ta-kèe", "3SG-REL.CONT"), ("dafà", "cooking"), ("kiifii", "fish")]
    glossedWords := [⟨[['K', 'a', 'n', 'd', 'è']], [['K', 'a', 'n', 'd', 'e']]⟩, ⟨[['c', 'e', 'e']], [['P', 'R', 'T']]⟩, ⟨[['t', 'a'], ['k', 'è', 'e']], [['3', 'S', 'G'], ['R', 'E', 'L', '.', 'C', 'O', 'N', 'T']]⟩, ⟨[['d', 'a', 'f', 'à']], [['c', 'o', 'o', 'k', 'i', 'n', 'g']]⟩, ⟨[['k', 'i', 'i', 'f', 'i', 'i']], [['f', 'i', 's', 'h']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "subject"), ("stabilizer", "cee"), ("host_tone", "L"), ("stab_tone", "H")] }

def ex3b : Datum :=
  { id := "hartmannzimmermann2007_ex3b"
    source := ⟨"hartmann-zimmermann-2007", "(3b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kiifii nèe Kande ta-kèe dafàawaa."
    glossedTokens := [("Kiifii", "fish"), ("nèe", "PRT"), ("Kande", "Kande"), ("ta-kèe", "3SG-REL.CONT"), ("dafàawaa", "cooking")]
    glossedWords := [⟨[['K', 'i', 'i', 'f', 'i', 'i']], [['f', 'i', 's', 'h']]⟩, ⟨[['n', 'è', 'e']], [['P', 'R', 'T']]⟩, ⟨[['K', 'a', 'n', 'd', 'e']], [['K', 'a', 'n', 'd', 'e']]⟩, ⟨[['t', 'a'], ['k', 'è', 'e']], [['3', 'S', 'G'], ['R', 'E', 'L', '.', 'C', 'O', 'N', 'T']]⟩, ⟨[['d', 'a', 'f', 'à', 'a', 'w', 'a', 'a']], [['c', 'o', 'o', 'k', 'i', 'n', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "nonSubject"), ("stabilizer", "nee"), ("host_tone", "H"), ("stab_tone", "L")] }

def ex8 : Datum :=
  { id := "hartmannzimmermann2007_ex8"
    source := ⟨"hartmann-zimmermann-2007", "(8)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Audù zâi tàfi Jamùs."
    glossedTokens := [("Audù", "Audu"), ("zâi", "FUT.3SG"), ("tàfi", "go"), ("Jamùs", "Germany")]
    glossedWords := [⟨[['A', 'u', 'd', 'ù']], [['A', 'u', 'd', 'u']]⟩, ⟨[['z', 'â', 'i']], [['F', 'U', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['t', 'à', 'f', 'i']], [['g', 'o']]⟩, ⟨[['J', 'a', 'm', 'ù', 's']], [['G', 'e', 'r', 'm', 'a', 'n', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Wàaneenèe zâi tàfi Jamùs? 'Who will go to Germany?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("focused", "subject"), ("stabilizer", "none"), ("tam", "future")] }

def ex17a1 : Datum :=
  { id := "hartmannzimmermann2007_ex17a1"
    source := ⟨"hartmann-zimmermann-2007", "(17 A1)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Daudàa nee ya-kèe kirà-ntà."
    glossedTokens := [("Daudàa", "Dauda"), ("nee", "PRT"), ("ya-kèe", "3SG-REL.CONT"), ("kirà-ntà", "call-her")]
    glossedWords := [⟨[['D', 'a', 'u', 'd', 'à', 'a']], [['D', 'a', 'u', 'd', 'a']]⟩, ⟨[['n', 'e', 'e']], [['P', 'R', 'T']]⟩, ⟨[['y', 'a'], ['k', 'è', 'e']], [['3', 'S', 'G'], ['R', 'E', 'L', '.', 'C', 'O', 'N', 'T']]⟩, ⟨[['k', 'i', 'r', 'à'], ['n', 't', 'à']], [['c', 'a', 'l', 'l'], ['h', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to: Wàa ya-kèe kirà-ntà? 'Who is calling her?'"
    judgment := .acceptable
    alternatives := [("Daudàa ya-kèe kirà-ntà.", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "newInfo"), ("focused", "subject"), ("stabilizer", "nee"), ("tam", "continuous")] }

def ex17a2 : Datum :=
  { id := "hartmannzimmermann2007_ex17a2"
    source := ⟨"hartmann-zimmermann-2007", "(17 A2)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Daudàa ya-nàa kirà-ntà."
    glossedTokens := [("Daudàa", "Dauda"), ("ya-nàa", "3SG-CONT"), ("kirà-ntà", "call-her")]
    glossedWords := [⟨[['D', 'a', 'u', 'd', 'à', 'a']], [['D', 'a', 'u', 'd', 'a']]⟩, ⟨[['y', 'a'], ['n', 'à', 'a']], [['3', 'S', 'G'], ['C', 'O', 'N', 'T']]⟩, ⟨[['k', 'i', 'r', 'à'], ['n', 't', 'à']], [['c', 'a', 'l', 'l'], ['h', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to: Wàa ya-kèe kirà-ntà? 'Who is calling her?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "newInfo"), ("focused", "subject"), ("stabilizer", "none"), ("tam", "continuous")] }

def ex22 : Datum :=
  { id := "hartmannzimmermann2007_ex22"
    source := ⟨"hartmann-zimmermann-2007", "(22)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Kiifii nèe Kandè takèe dafàawaa."
    glossedTokens := [("Kiifii", "fish"), ("nèe", "PRT"), ("Kandè", "Kande"), ("takèe", "3SG-REL.CONT"), ("dafàawaa", "cooking")]
    glossedWords := [⟨[['K', 'i', 'i', 'f', 'i', 'i']], [['f', 'i', 's', 'h']]⟩, ⟨[['n', 'è', 'e']], [['P', 'R', 'T']]⟩, ⟨[['K', 'a', 'n', 'd', 'è']], [['K', 'a', 'n', 'd', 'e']]⟩, ⟨[['t', 'a', 'k', 'è', 'e']], [['3', 'S', 'G'], ['R', 'E', 'L', '.', 'C', 'O', 'N', 'T']]⟩, ⟨[['d', 'a', 'f', 'à', 'a', 'w', 'a', 'a']], [['c', 'o', 'o', 'k', 'i', 'n', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Mèenee nèe Kandè ta-kèe dafàawaa? 'What is Kande cooking?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "newInfo"), ("focused", "nonSubject"), ("stabilizer", "nee")] }

def ex23 : Datum :=
  { id := "hartmannzimmermann2007_ex23"
    source := ⟨"randell-bature-schuh-1998", "HB 1.11"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(23)"⟩
    language := "haus1257"
    primaryText := "Naa tahoo dàgà Bir̃nin Ƙwànni."
    glossedTokens := [("Naa", "1SG.PERF"), ("tahoo", "come"), ("dàgà", "from"), ("Bir̃nin", "Birnin"), ("Ƙwànni", "Konni")]
    glossedWords := [⟨[['N', 'a', 'a']], [['1', 'S', 'G', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['t', 'a', 'h', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩, ⟨[['d', 'à', 'g', 'à']], [['f', 'r', 'o', 'm']]⟩, ⟨[['B', 'i', 'r', '̃', 'n', 'i', 'n']], [['B', 'i', 'r', 'n', 'i', 'n']]⟩, ⟨[['Ƙ', 'w', 'à', 'n', 'n', 'i']], [['K', 'o', 'n', 'n', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Dàgà wànè gàrii ka zoo? 'From which city do you come?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "newInfo"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex24 : Datum :=
  { id := "hartmannzimmermann2007_ex24"
    source := ⟨"hartmann-zimmermann-2007", "(24)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Aa'àa, màatar̃-sa cèe ta mutù."
    glossedTokens := [("Aa'àa", "no"), ("màatar̃-sa", "wife.of-3M"), ("cèe", "PRT"), ("ta", "3SG.REL.PERF"), ("mutù", "die")]
    glossedWords := [⟨[['A', 'a', '\'', 'à', 'a']], [['n', 'o']]⟩, ⟨[['m', 'à', 'a', 't', 'a', 'r', '̃'], ['s', 'a']], [['w', 'i', 'f', 'e', '.', 'o', 'f'], ['3', 'M']]⟩, ⟨[['c', 'è', 'e']], [['P', 'R', 'T']]⟩, ⟨[['t', 'a']], [['3', 'S', 'G', '.', 'R', 'E', 'L', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['m', 'u', 't', 'ù']], [['d', 'i', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Corrective reply to: Tsoohowar̃-sà cee ta mutù? 'Was it his mother who died?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "corrective"), ("focused", "subject"), ("stabilizer", "cee")] }

def ex25 : Datum :=
  { id := "hartmannzimmermann2007_ex25"
    source := ⟨"randell-bature-schuh-1998", "HB 3.03"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(25)"⟩
    language := "haus1257"
    primaryText := "A'a, zân biyaa shâ bìyar̃ nèe."
    glossedTokens := [("A'a", "no"), ("zân", "FUT.1SG"), ("biyaa", "pay"), ("shâ bìyar̃", "fifteen"), ("nèe", "PRT")]
    glossedWords := [⟨[['A', '\'', 'a']], [['n', 'o']]⟩, ⟨[['z', 'â', 'n']], [['F', 'U', 'T', '.', '1', 'S', 'G']]⟩, ⟨[['b', 'i', 'y', 'a', 'a']], [['p', 'a', 'y']]⟩, ⟨[['s', 'h', 'â', ' ', 'b', 'ì', 'y', 'a', 'r', '̃']], [['f', 'i', 'f', 't', 'e', 'e', 'n']]⟩, ⟨[['n', 'è', 'e']], [['P', 'R', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := "Corrective reply to: Nair̃àa àshìr̃in zaa kà biyaa in yaa yi makà. 'It is twenty Naira that you will pay if he makes it for you.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "corrective"), ("focused", "nonSubject"), ("stabilizer", "nee")] }

def ex26 : Datum :=
  { id := "hartmannzimmermann2007_ex26"
    source := ⟨"randell-bature-schuh-1998", "HB 1.10"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(26)"⟩
    language := "haus1257"
    primaryText := "Tô, zân iyà bî ta baayansà?"
    glossedTokens := [("Tô", "alright"), ("zân", "1SG.FUT"), ("iyà", "can"), ("bî", "follow"), ("ta", "in"), ("baayansà", "back.of.him")]
    glossedWords := [⟨[['T', 'ô']], [['a', 'l', 'r', 'i', 'g', 'h', 't']]⟩, ⟨[['z', 'â', 'n']], [['1', 'S', 'G', '.', 'F', 'U', 'T']]⟩, ⟨[['i', 'y', 'à']], [['c', 'a', 'n']]⟩, ⟨[['b', 'î']], [['f', 'o', 'l', 'l', 'o', 'w']]⟩, ⟨[['t', 'a']], [['i', 'n']]⟩, ⟨[['b', 'a', 'a', 'y', 'a', 'n', 's', 'à']], [['b', 'a', 'c', 'k', '.', 'o', 'f', '.', 'h', 'i', 'm']]⟩]
    lgrConformance := some .wordAligned
    context := "Contrastive reply to: In mùtûm yanàa yîn sallàa, baa àa bî ta gàbansà. 'If a man is praying, you shouldn't pass in front of him.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "contrastive"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex27 : Datum :=
  { id := "hartmannzimmermann2007_ex27"
    source := ⟨"randell-bature-schuh-1998", "HB 2.03"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(27)"⟩
    language := "haus1257"
    primaryText := "Koo hiir̃a baa àa yî, sai dai cî kawài a-kèe ta yî."
    glossedTokens := [("Koo", "and"), ("hiir̃a", "chatting"), ("baa àa", "NEG.4SG.CONT"), ("yî", "do"), ("sai", "PRT"), ("dai", "PRT"), ("cî", "eat"), ("kawài", "only"), ("a-kèe", "4SG-REL.CONT"), ("ta", "keep.on"), ("yî", "do")]
    glossedWords := [⟨[['K', 'o', 'o']], [['a', 'n', 'd']]⟩, ⟨[['h', 'i', 'i', 'r', '̃', 'a']], [['c', 'h', 'a', 't', 't', 'i', 'n', 'g']]⟩, ⟨[['b', 'a', 'a', ' ', 'à', 'a']], [['N', 'E', 'G', '.', '4', 'S', 'G', '.', 'C', 'O', 'N', 'T']]⟩, ⟨[['y', 'î']], [['d', 'o']]⟩, ⟨[['s', 'a', 'i']], [['P', 'R', 'T']]⟩, ⟨[['d', 'a', 'i']], [['P', 'R', 'T']]⟩, ⟨[['c', 'î']], [['e', 'a', 't']]⟩, ⟨[['k', 'a', 'w', 'à', 'i']], [['o', 'n', 'l', 'y']]⟩, ⟨[['a'], ['k', 'è', 'e']], [['4', 'S', 'G'], ['R', 'E', 'L', '.', 'C', 'O', 'N', 'T']]⟩, ⟨[['t', 'a']], [['k', 'e', 'e', 'p', '.', 'o', 'n']]⟩, ⟨[['y', 'î']], [['d', 'o']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "contrastive"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex29 : Datum :=
  { id := "hartmannzimmermann2007_ex29"
    source := ⟨"randell-bature-schuh-1998", "HB 1.10"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(29)"⟩
    language := "haus1257"
    primaryText := "Gùdaa nakèe sô!"
    glossedTokens := [("Gùdaa", "full"), ("nakèe", "1SG.REL.CONT"), ("sô", "want")]
    glossedWords := [⟨[['G', 'ù', 'd', 'a', 'a']], [['f', 'u', 'l', 'l']]⟩, ⟨[['n', 'a', 'k', 'è', 'e']], [['1', 'S', 'G', '.', 'R', 'E', 'L', '.', 'C', 'O', 'N', 'T']]⟩, ⟨[['s', 'ô']], [['w', 'a', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Gùdaa koo ɓaarìi? '(Do you want) a whole or a half?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "exSitu"), ("pragType", "selective"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def ex30 : Datum :=
  { id := "hartmannzimmermann2007_ex30"
    source := ⟨"jaggar-2001", "p. 498"⟩
    reportedIn := some ⟨"hartmann-zimmermann-2007", "(30)"⟩
    language := "haus1257"
    primaryText := "Zân shaa shaayìi."
    glossedTokens := [("Zân", "FUT.1SG"), ("shaa", "drink"), ("shaayìi", "tea")]
    glossedWords := [⟨[['Z', 'â', 'n']], [['F', 'U', 'T', '.', '1', 'S', 'G']]⟩, ⟨[['s', 'h', 'a', 'a']], [['d', 'r', 'i', 'n', 'k']]⟩, ⟨[['s', 'h', 'a', 'a', 'y', 'ì', 'i']], [['t', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Kòofii zaa-kà shaa koo kùwa shaayìi? 'Will you drink coffee or tea?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("pragType", "selective"), ("focused", "nonSubject"), ("stabilizer", "none")] }

def all : List Datum := [ex3a, ex3b, ex8, ex17a1, ex17a2, ex22, ex23, ex24, ex25, ex26, ex27, ex29, ex30]

end HartmannZimmermann2007.Examples
