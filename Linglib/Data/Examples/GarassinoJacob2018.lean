module

public import Linglib.Data.Examples.Schema

/-!
# `GarassinoJacob2018` — typed example data

Auto-generated from `Linglib/Data/Examples/GarassinoJacob2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GarassinoJacob2018.Examples`.
-/

@[expose] public section

namespace GarassinoJacob2018.Examples

def ex1 : Datum :=
  { id := "garassinojacob2018_ex1"
    source := ⟨"garassino-jacob-2018", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John DID read it."
    glossedTokens := []
    context := "A: John did not read 'War and Peace'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "emphaticDo"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex3 : Datum :=
  { id := "garassinojacob2018_ex3"
    source := ⟨"hohle-1992", "p. 112"⟩
    reportedIn := some ⟨"garassino-jacob-2018", "(3)"⟩
    language := "stan1295"
    primaryText := "Karl SCHREIBT ein Drehbuch."
    glossedTokens := []
    context := "A: Ich habe Hanna gefragt, was Karl gerade macht, und sie hat die alberne Behauptung aufgestellt, dass er ein Drehbuch schreibt."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "verumAccent"), ("antecedent", "positive"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex4 : Datum :=
  { id := "garassinojacob2018_ex4"
    source := ⟨"garassino-jacob-2018", "(4)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Nein) Karl HAT nicht gelogen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "verumAccent"), ("antecedent", "inferredNegation"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex5a : Datum :=
  { id := "garassinojacob2018_ex5a"
    source := ⟨"garassino-jacob-2018", "(5a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je t'assure qu'il est en train d'écrire un scénario."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "embedding"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex5b : Datum :=
  { id := "garassinojacob2018_ex5b"
    source := ⟨"garassino-jacob-2018", "(5b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ti assicuro / ti dico che sta scrivendo una sceneggiatura."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "embedding"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex6 : Datum :=
  { id := "garassinojacob2018_ex6"
    source := ⟨"garassino-jacob-2018", "(6)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Ya lo creo que fue a la reunión."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "embedding"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex7a : Datum :=
  { id := "garassinojacob2018_ex7a"
    source := ⟨"garassino-jacob-2018", "(7a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il écrit un scénario, je t'assure."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "juxtaposed"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex7b : Datum :=
  { id := "garassinojacob2018_ex7b"
    source := ⟨"garassino-jacob-2018", "(7b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Sta scrivendo una sceneggiatura, ti dico."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "juxtaposed"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex7c : Datum :=
  { id := "garassinojacob2018_ex7c"
    source := ⟨"garassino-jacob-2018", "(7c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Escribe un guión, te digo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "juxtaposed"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex8 : Datum :=
  { id := "garassinojacob2018_ex8"
    source := ⟨"garassino-jacob-2018", "(8)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Bien sûr qu'il est en train d'écrire un scénario."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "ellipticEmbedding"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex9 : Datum :=
  { id := "garassinojacob2018_ex9"
    source := ⟨"garassino-jacob-2018", "(9)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¡Claro que te escucho!"
    glossedTokens := []
    context := "A: No me escuchas."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "ellipticEmbedding"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex10 : Datum :=
  { id := "garassinojacob2018_ex10"
    source := ⟨"garassino-jacob-2018", "(10)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Certo che ti ascolto!"
    glossedTokens := []
    context := "A: Non mi ascolti."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "ellipticEmbedding"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex11 : Datum :=
  { id := "garassinojacob2018_ex11"
    source := ⟨"garassino-jacob-2018", "(11)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Algo debe saber."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "fronting"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex12 : Datum :=
  { id := "garassinojacob2018_ex12"
    source := ⟨"garassino-jacob-2018", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Qualcosa avrà fatto, nelle vacanze."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "fronting"), ("antecedent", "none"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex13 : Datum :=
  { id := "garassinojacob2018_ex13"
    source := ⟨"garassino-jacob-2018", "(13)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Dije que terminaría el libro, y el libro he terminado."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "fronting"), ("antecedent", "modal"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex14 : Datum :=
  { id := "garassinojacob2018_ex14"
    source := ⟨"garassino-jacob-2018", "(14)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mais c'est ce qu'elle fait!"
    glossedTokens := []
    context := "A: Marie devrait passer son permis de conduire."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "faireCleft"), ("antecedent", "modal"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex15 : Datum :=
  { id := "garassinojacob2018_ex15"
    source := ⟨"frascarelli-2003", "p. 557"⟩
    reportedIn := some ⟨"garassino-jacob-2018", "(15)"⟩
    method := some .corpus
    language := "ital1282"
    primaryText := "Non è questione che il tempo non te l'ho dato; io te l'ho dato il tempo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "rightDislocation"), ("antecedent", "explicitNegation"), ("dislocated", "object"), ("relation", "unstated"), ("subquestion", "no")] }

def ex16 : Datum :=
  { id := "garassinojacob2018_ex16"
    source := ⟨"brunetti-2009", "p. 763"⟩
    reportedIn := some ⟨"garassino-jacob-2018", "(16)"⟩
    method := some .corpus
    language := "ital1282"
    primaryText := "ah va be', la soluzione gliela troviamo."
    glossedTokens := []
    context := "A: no, niente, eh, trovare una soluzione."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "leftDislocation"), ("antecedent", "openQuestion"), ("dislocated", "object"), ("relation", "unstated"), ("subquestion", "no")] }

def ex17 : Datum :=
  { id := "garassinojacob2018_ex17"
    source := ⟨"poletto-zanuttini-2013", "p. 124"⟩
    reportedIn := some ⟨"garassino-jacob-2018", "(17)"⟩
    language := "ital1282"
    primaryText := "Sì che è arrivato."
    glossedTokens := []
    context := "A: È poi arrivato Gianni?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siChe"), ("antecedent", "explicitQuestion"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex18 : Datum :=
  { id := "garassinojacob2018_ex18"
    source := ⟨"batllori-hernanz-2013", "p. 3"⟩
    reportedIn := some ⟨"garassino-jacob-2018", "(18)"⟩
    language := "stan1288"
    primaryText := "Sí que ha cantado la soprano."
    glossedTokens := []
    context := "A: No ha cantado la soprano."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex19 : Datum :=
  { id := "garassinojacob2018_ex19"
    source := ⟨"batllori-hernanz-2013", "pp. 4-5"⟩
    reportedIn := some ⟨"garassino-jacob-2018", "(19)"⟩
    language := "stan1288"
    primaryText := "Carrefour le ofrece este fin de semana precios de vértigo… ¡Esto sí que es un aniversario!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "positive"), ("dislocated", "subject"), ("relation", "unstated"), ("subquestion", "no")] }

def fn11 : Datum :=
  { id := "garassinojacob2018_fn11"
    source := ⟨"garassino-jacob-2018", "fn. 11 (i)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si (il fait beau)."
    glossedTokens := []
    context := "A: Il ne fait pas beau."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siParticle"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "unstated"), ("subquestion", "no")] }

def ex21 : Datum :=
  { id := "garassinojacob2018_ex21"
    source := ⟨"garassino-jacob-2018", "(21)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ma le ho prese, le pastiglie!"
    glossedTokens := []
    context := "A: Non hai preso le pastiglie."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "rightDislocation"), ("antecedent", "explicitNegation"), ("dislocated", "object"), ("relation", "unstated"), ("subquestion", "no")] }

def ex22 : Datum :=
  { id := "garassinojacob2018_ex22"
    source := ⟨"garassino-jacob-2018", "(22)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Le pastiglie, le ho prese (ma il resto delle medicine no)!"
    glossedTokens := []
    context := "A: Non hai preso le pastiglie."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "leftDislocation"), ("antecedent", "explicitNegation"), ("dislocated", "object"), ("relation", "unstated"), ("subquestion", "no")] }

def ex23a : Datum :=
  { id := "garassinojacob2018_ex23a"
    source := ⟨"garassino-jacob-2018", "(23a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "…parce que, lui, il a une vision."
    glossedTokens := []
    context := "Monsieur le Président, (…) il faut rendre honneur à la présidence française, il faut rendre honneur au président Chirac, qui a été au charbon, qui a combattu et qui a vaincu sur sa vision de l'Europe,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "leftDislocation"), ("antecedent", "inferredNegation"), ("dislocated", "subject"), ("relation", "analogy"), ("subquestion", "no")] }

def ex23b : Datum :=
  { id := "garassinojacob2018_ex23b"
    source := ⟨"garassino-jacob-2018", "(23b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "…porque él sí tiene una visión."
    glossedTokens := []
    context := "Señor Presidente, (…) hay que rendir honores a la Presidencia francesa, hay que rendir honores al Presidente Chirac, que se ha dejado la piel, que ha luchido y que ha vencido con su visión de Europa,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siOnly"), ("antecedent", "inferredNegation"), ("dislocated", "subject"), ("relation", "analogy"), ("subquestion", "no")] }

def ex23c : Datum :=
  { id := "garassinojacob2018_ex23c"
    source := ⟨"garassino-jacob-2018", "(23c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "…perché lui sì che ha una visione."
    glossedTokens := []
    context := "Signor Presidente, (…) occorre rendere omaggio alla Presidenza francese, occorre rendere omaggio al Presidente Chirac che, costretto a un'opera improba, ha combattuto e ha vinto con la sua visione dell'Europa,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siChe"), ("antecedent", "inferredNegation"), ("dislocated", "subject"), ("relation", "analogy"), ("subquestion", "no")] }

def ex24 : Datum :=
  { id := "garassinojacob2018_ex24"
    source := ⟨"garassino-jacob-2018", "(24)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "…gli strumenti li abbiamo."
    glossedTokens := []
    context := "Dovremmo, credo, dare maggiore informazione sugli strumenti a disposizione, valutare le cose positive che sono state fatte – anche se noi non siamo contente fino in fondo, perché ancora resta molto da fare – ma non dobbiamo abbatterci per il fatto che non abbiamo strumenti a disposizione:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "leftDislocation"), ("antecedent", "explicitNegation"), ("dislocated", "object"), ("relation", "identity"), ("subquestion", "no")] }

def ex25 : Datum :=
  { id := "garassinojacob2018_ex25"
    source := ⟨"garassino-jacob-2018", "(25)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "…però le premesse per la tolleranza zero le abbiamo davvero messe."
    glossedTokens := []
    context := "Onorevole Maes, lei ha sollevato problemi di importanza fondamentale, il primo dei quali sulla tolleranza zero. (…) E' di solito un lavoro che nessuno vuole affrontare, (…)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "leftDislocation"), ("antecedent", "inferredNegation"), ("dislocated", "object"), ("relation", "identity"), ("subquestion", "no")] }

def ex26 : Datum :=
  { id := "garassinojacob2018_ex26"
    source := ⟨"garassino-jacob-2018", "(26)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "…ma i problemi della macroeconomia, del lavoro e dei problemi strutturali li mettiamo assieme davvero, adesso."
    glossedTokens := []
    context := "È chiaro allora che diventa indispensabile mettere assieme i tre processi. Purtroppo la nostra terminologia è orrenda,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "leftDislocation"), ("antecedent", "modal"), ("dislocated", "object"), ("relation", "analogy"), ("subquestion", "no")] }

def ex27 : Datum :=
  { id := "garassinojacob2018_ex27"
    source := ⟨"garassino-jacob-2018", "(27)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Noi questo sforzo lo abbiamo sempre fatto e continueremo a farlo."
    glossedTokens := []
    context := "Per riuscirci è indispensabile tener fede a un principio che è alla base del nostro stare nell'Unione europea. (…) È quello secondo il quale nello sviluppo della costruzione europea occorre sempre fare uno sforzo per comprendere le ragioni degli altri, farsene in qualche modo carico."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "leftDislocation"), ("antecedent", "modal"), ("dislocated", "both"), ("relation", "analogy"), ("subquestion", "no")] }

def ex28 : Datum :=
  { id := "garassinojacob2018_ex28"
    source := ⟨"garassino-jacob-2018", "(28)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Sí señor Presidente, sí que puedo responder."
    glossedTokens := []
    context := "Pienso que el Sr. Ramón de Miguel puede manifestar que consultará al Consejo y que más tarde dará una respuesta más detallada, que ahora no está en disposición de dar. Pero pienso que manifestar simplemente que no puede dar una respuesta no forma parte de las reglas del juego. Considero que puede someter a la Presidencia, al Consejo, las preguntas que se le han formulado, y que puede declarar que, con respecto a algunas de ellas, ahora no está en disposición de dar una respuesta. Pero considero que, por regla general, corresponde al Consejo responder a todas las preguntas."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "identity"), ("subquestion", "no")] }

def ex29 : Datum :=
  { id := "garassinojacob2018_ex29"
    source := ⟨"garassino-jacob-2018", "(29)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "En eso, sí que Turquía es un Estado absolutamente europeo."
    glossedTokens := []
    context := "(…) sigue habiendo detenciones arbitrarias y violaciones de los derechos humanos. (…) se sigue poniendo en dificultades a los defensores de los derechos humanos (…) permanece todavía en la cárcel una Premio Sajarov, como la Sra. Leyla Zana. (…) Turquía, en el lugar estratégico que ocupa, es el único Estado completamente laico (…)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "inferredNegation"), ("dislocated", "adverbial"), ("relation", "identity"), ("subquestion", "no")] }

def ex30 : Datum :=
  { id := "garassinojacob2018_ex30"
    source := ⟨"garassino-jacob-2018", "(30)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "…momentos en el que el Consejo Europeo sí que ha estado con las manos cruzadas."
    glossedTokens := []
    context := "Sí quisiera decirle a mi buen amigo, el diputado Jacques Poos, que creo que aquí alguien se ha podido quedar con las manos cruzadas. Sus Señorías saben muy bien que quien les habla nunca ha estado con las manos cruzadas, ni cuando era ministro representando a su país –cuando era colega suyo y tuvimos muchos momentos para hablar –; por lo tanto, seamos también respetuosos con las palabras que utilizamos. Si su Señoría piensa que yo he estado con las manos cruzadas en este conflicto, creo que se equivoca y, si me lo permite, podría hasta echar la vista atrás para ver"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "inferredNegation"), ("dislocated", "subject"), ("relation", "analogy"), ("subquestion", "yes")] }

def ex32 : Datum :=
  { id := "garassinojacob2018_ex32"
    source := ⟨"garassino-jacob-2018", "(32)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "…pero sí que se pueden hacer unos diques móviles y también se puede hacer un metro subterráneo."
    glossedTokens := []
    context := "No podemos evitar el acqua alta – eso es un fenómeno de la naturaleza –"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "analogy"), ("subquestion", "yes")] }

def ex33 : Datum :=
  { id := "garassinojacob2018_ex33"
    source := ⟨"garassino-jacob-2018", "(33)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "…pero sí que es satisfactorio en alguno de ellos."
    glossedTokens := []
    context := "Con ello no quiero decirles que el acuerdo alcanzado sea óptimo en todos sus aspectos,"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "explicitNegation"), ("dislocated", "none"), ("relation", "analogy"), ("subquestion", "yes")] }

def ex35 : Datum :=
  { id := "garassinojacob2018_ex35"
    source := ⟨"garassino-jacob-2018", "(35)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Eso sí que es de escándalo."
    glossedTokens := []
    context := "Esto es escandaloso, esto merecería un titular: sólo seis Estados miembros nos dicen qué hacen con la recuperación de los fondos que han usado mal."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "siQue"), ("antecedent", "positive"), ("dislocated", "subject"), ("relation", "unstated"), ("subquestion", "no")] }

def all : List Datum := [ex1, ex3, ex4, ex5a, ex5b, ex6, ex7a, ex7b, ex7c, ex8, ex9, ex10, ex11, ex12, ex13, ex14, ex15, ex16, ex17, ex18, ex19, fn11, ex21, ex22, ex23a, ex23b, ex23c, ex24, ex25, ex26, ex27, ex28, ex29, ex30, ex32, ex33, ex35]

end GarassinoJacob2018.Examples
