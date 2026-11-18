module

public import Linglib.Data.Examples.Schema

/-!
# `AnandHardtMcCloskey2021` — typed example data

Auto-generated from `Linglib/Data/Examples/AnandHardtMcCloskey2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AnandHardtMcCloskey2021.Examples`.
-/

@[expose] public section

namespace AnandHardtMcCloskey2021.Examples

def ex_1 : Datum :=
  { id := "anandhardtmccloskey2021_1"
    source := ⟨"anand-hardt-mccloskey-2021", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She will resign, but we don't know when."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("remnant", "when"), ("semantic_type", "temporal"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "She will resign")] }

def ex_2 : Datum :=
  { id := "anandhardtmccloskey2021_2"
    source := ⟨"anand-hardt-mccloskey-2021", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Brady said the new approach saves time, but she didn't know how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "100452"), ("remnant", "how much"), ("semantic_type", "degree"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "the new approach saves time"), ("correlate", "time"), ("correlate_type", "mass/range"), ("kind", "merger"), ("paraphrase", "the new approach saves"), ("main_predicate", "saves")] }

def ex_3 : Datum :=
  { id := "anandhardtmccloskey2021_3"
    source := ⟨"anand-hardt-mccloskey-2021", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For some reason or other that is one of the kids jumping out at me. And I don't know why."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "15397"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("tag", "e_type"), ("e_type_span", "one of the kids")] }

def ex_4 : Datum :=
  { id := "anandhardtmccloskey2021_4"
    source := ⟨"anand-hardt-mccloskey-2021", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There was always something new ... improved equipment, innovative means of transmission, original shows coming down the network line from New York and Chicago and above all, the knowledge that thousands upon thousands of people clustered around a box that sat like a shrine in their living rooms, listening. It didn't really matter to what."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("minimal antecedent (4)", .acceptable), ("larger antecedent (5): those thousands upon thousands of people clustered around that box, listening", .acceptable)]
    paperFeatures := [("corpus_id", "36225"), ("remnant", "to what"), ("position", "embedded"), ("qembedder", "matter"), ("antecedent", "thousands upon thousands of people ... listening"), ("antecedent_status", "discontinuous"), ("paraphrase", "those thousands upon thousands of people were listening"), ("mismatch", "new_words"), ("new_words", "copula")] }

def ex_6 : Datum :=
  { id := "anandhardtmccloskey2021_6"
    source := ⟨"anand-hardt-mccloskey-2021", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'We were very concerned that the mortality pattern seemed to be so abrupt and sudden from women, but without research,' she said, 'we did not know why.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "57485"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "the mortality pattern ... to be so abrupt and sudden from women"), ("antecedent_status", "discontinuous"), ("paraphrase", "the mortality pattern was so abrupt and sudden from women"), ("mismatch", "tense"), ("mismatch_detail", "finiteness")] }

def ex_7a : Datum :=
  { id := "anandhardtmccloskey2021_7a"
    source := ⟨"anand-hardt-mccloskey-2021", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'It will make some difference, but I don't know how much,' said A. Michael Lipper, president of Lipper Analytical Services Inc."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "100549"), ("remnant", "how much"), ("semantic_type", "degree"), ("position", "embedded"), ("qembedder", "know"), ("correlate", "some difference"), ("kind", "merger")] }

def ex_7b : Datum :=
  { id := "anandhardtmccloskey2021_7b"
    source := ⟨"anand-hardt-mccloskey-2021", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For the first time, Silver indicated that he was ready to vote on the plan, although he declined to say which way."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "100447"), ("remnant", "which way"), ("position", "embedded"), ("qembedder", "say"), ("kind", "sprouting")] }

def ex_8 : Datum :=
  { id := "anandhardtmccloskey2021_8"
    source := ⟨"anand-hardt-mccloskey-2021", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unisys said it would fire more employees, though it didn't say how many, and write off another $400 million against profits."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("absolute number of employees", .acceptable), ("comparative: how many more (9)", .acceptable)]
    paperFeatures := [("corpus_id", "44148"), ("remnant", "how many"), ("semantic_type", "degree"), ("position", "embedded"), ("qembedder", "say"), ("tag", "remnant_ellipsis")] }

def ex_10 : Datum :=
  { id := "anandhardtmccloskey2021_10"
    source := ⟨"anand-hardt-mccloskey-2021", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't know why, but I said yes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "144127"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "I said yes"), ("antecedent_status", "cataphoric")] }

def ex_11 : Datum :=
  { id := "anandhardtmccloskey2021_11"
    source := ⟨"anand-hardt-mccloskey-2021", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A lot of people, I don't know for what reason, are telling lies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("A lot of people, I don't know for what reason they are telling lies, are telling lies.", .questionable)]
    readings := []
    paperFeatures := [("corpus_id", "57184"), ("remnant", "for what reason"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "A lot of people ... are telling lies"), ("antecedent_status", "interpolated")] }

def ex_13 : Datum :=
  { id := "anandhardtmccloskey2021_13"
    source := ⟨"anand-hardt-mccloskey-2021", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He turned toward that part of the sky, which then remained dark for a few seconds. 'It's hard to know how long,' he said."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "125447"), ("remnant", "how long"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "that part of the sky ... remained dark for a few seconds"), ("antecedent_status", "discontinuous"), ("paraphrase", "that part of the sky remained dark for")] }

def ex_14a : Datum :=
  { id := "anandhardtmccloskey2021_14a"
    source := ⟨"anand-hardt-mccloskey-2021", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'I get into the cupboards. Then for one year, I call them on a weekly basis and hold them accountable.' In what way?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "157514"), ("remnant", "in what way"), ("semantic_type", "manner"), ("position", "root"), ("antecedent_status", "coordination"), ("paraphrase", "do you hold them accountable"), ("tag", "ignore")] }

def ex_14b : Datum :=
  { id := "anandhardtmccloskey2021_14b"
    source := ⟨"anand-hardt-mccloskey-2021", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Messier was a distant second at 22 but has demanded a trade. He won't say why, and he declined to play this year."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "53758"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "say"), ("antecedent_status", "coordination"), ("paraphrase", "Messier has demanded a trade"), ("tag", "ignore")] }

def ex_15a : Datum :=
  { id := "anandhardtmccloskey2021_15a"
    source := ⟨"anand-hardt-mccloskey-2021", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam Kamvar, manager of the Childe Harold pub and restaurant, is proud of the framed poster that hangs on a brightly lit brick wall. 'The Only Sign of Life in Dallas,' it reads, above a highway sign: 'Washington, D.C., 1304 Miles.' Under that, it says, 'Go Redskins.' 'I didn't ask how much,' he said. 'I bought it.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "104061"), ("remnant", "how much"), ("semantic_type", "degree"), ("position", "embedded"), ("qembedder", "ask"), ("antecedent_status", "missing"), ("conventionalized", "how much")] }

def ex_15b : Datum :=
  { id := "anandhardtmccloskey2021_15b"
    source := ⟨"anand-hardt-mccloskey-2021", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'I wanted to see everything that happens—I wanted to hear everything that happens,' said Charles Tomlin, whose 46-year-old son, Rick, an enforcement officer for the Federal Transportation Department, was killed in the blast. 'I had also wanted to know why. I wanted to look up and see McVeigh, a nice-looking man, and try to understand what drove him to kill this many people.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "283235"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent_status", "missing")] }

def ex_16 : Datum :=
  { id := "anandhardtmccloskey2021_16"
    source := ⟨"anand-hardt-mccloskey-2021", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "While the study consumed a $275,000 grant, the device it produced is a relative bargain. How much, installation included? 'Oh,' said Mehta, 'I would suspect no more than $50 or so.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "19606"), ("remnant", "how much"), ("semantic_type", "degree"), ("position", "root"), ("antecedent_status", "missing"), ("conventionalized", "how much")] }

def ex_17 : Datum :=
  { id := "anandhardtmccloskey2021_17"
    source := ⟨"anand-hardt-mccloskey-2021", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every day brings new evidence that the once-booming national economy is slowing; even Alan Greenspan says so. But take a walk almost anywhere in Manhattan jostled by the leather-wearing, cell-phone-wielding, taxicab-grabbing, shopping-bag-swinging hordes and you have to wonder: What slowdown? Economists here are wondering, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "29529"), ("remnant", "what slowdown"), ("position", "root"), ("antecedent_status", "missing"), ("tag", "echoq"), ("interpretation", "negative existential")] }

def ex_18a : Datum :=
  { id := "anandhardtmccloskey2021_18a"
    source := ⟨"anand-hardt-mccloskey-2021", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Should we go to the beach? B: Why not?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("remnant", "why not"), ("position", "root"), ("why_not", "free_modal")] }

def ex_18b : Datum :=
  { id := "anandhardtmccloskey2021_18b"
    source := ⟨"anand-hardt-mccloskey-2021", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Frank doesn't believe in minimalism. B: Why not?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("remnant", "why not"), ("position", "root"), ("why_not", "anaphoric"), ("antecedent", "Frank doesn't believe in minimalism")] }

def ex_19a : Datum :=
  { id := "anandhardtmccloskey2021_19a"
    source := ⟨"anand-hardt-mccloskey-2021", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He learned English by listening to the radio. His first years were difficult. He lived in the basement of a building in Elmhurst, Queens, where Chinese immigrants paid $175 a month for beds separated by hanging blankets. He worked long hours in a laundry. Then he noticed some musicians in the subway. Why not? 'I was so scared,' Chen said. 'I hesitated almost an hour. Then I counted to 100. Then I counted to 50. Then I finally opened the case.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "95457"), ("remnant", "why not"), ("position", "root"), ("why_not", "free_modal"), ("antecedent_status", "missing")] }

def ex_19b : Datum :=
  { id := "anandhardtmccloskey2021_19b"
    source := ⟨"anand-hardt-mccloskey-2021", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whelan said Ellison was an excellent student. He hadn't had a name athlete come through his door before. But Brown had read about Whelan in a fitness magazine and the gym was near Ellison's summer home. Why not? 'I had heard and read that Pervis didn't work hard, but that was not the case with me,' Whelan said."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "241354"), ("remnant", "why not"), ("position", "root"), ("why_not", "free_modal"), ("antecedent_status", "missing")] }

def ex_20a : Datum :=
  { id := "anandhardtmccloskey2021_20a"
    source := ⟨"anand-hardt-mccloskey-2021", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To read some accounts of his brief tenure at Georgia, one imagines a befuddled and confused Jim Harrick, huddled behind a locked door in his Stegeman Coliseum office, fighting back tears and wailing, 'Why, Lord, why?'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "103083"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "root"), ("antecedent_status", "missing"), ("why", "situational")] }

def ex_20b : Datum :=
  { id := "anandhardtmccloskey2021_20b"
    source := ⟨"anand-hardt-mccloskey-2021", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "McCann said Jonesboro, a town of 51,000 on the Mississippi River, drew closer together as a result of the March 24, 1998, shooting rampage during which four junior high school girls and one teacher died, 'but there's a lot of anger,' he said. 'The biggest problem for people I've talked to is there's never been an answer to why. I think if anyone could ever answer why, it would help a lot, but I don't think that's going to happen.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "109969"), ("remnant", "why"), ("semantic_type", "reason"), ("antecedent_status", "missing"), ("why", "situational")] }

def ex_21 : Datum :=
  { id := "anandhardtmccloskey2021_21"
    source := ⟨"anand-hardt-mccloskey-2021", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She remembered Ronnie spending six months in some kind of 'school for boys' when he was a youth but she doesn't know why."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "125278"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "Ronnie spending six months in some kind of 'school for boys'"), ("paraphrase", "Ronnie spent six months in some kind of school for boys"), ("mismatch", "tense"), ("mismatch_detail", "gerund antecedent")] }

def ex_22 : Datum :=
  { id := "anandhardtmccloskey2021_22"
    source := ⟨"anand-hardt-mccloskey-2021", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From what I can make out, it must have been written sometime during the Vietnam War, but I don't know by whom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "72508"), ("remnant", "by whom"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "it must have been written"), ("paraphrase", "it was written"), ("mismatch", "tense"), ("mismatch_detail", "modal auxiliary dropped")] }

def ex_23 : Datum :=
  { id := "anandhardtmccloskey2021_23"
    source := ⟨"anand-hardt-mccloskey-2021", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You heard the question, 'Why are people watching this?' ... For once, I didn't care why."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "48694"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "care"), ("antecedent", "are people watching this"), ("paraphrase", "people were watching this"), ("mismatch", "tense"), ("mismatch_detail", "quotation perspective")] }

def ex_24 : Datum :=
  { id := "anandhardtmccloskey2021_24"
    source := ⟨"anand-hardt-mccloskey-2021", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'I told him I'd support him in his efforts and be an investor,' Kemper said Monday. 'I don't know to what extent yet, because I've just decided to do it this morning.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "15852"), ("remnant", "to what extent"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "I'd support him in his efforts and be an investor"), ("paraphrase", "I will support him in his efforts and be an investor"), ("mismatch", "tense"), ("mismatch_detail", "sequence of tense")] }

def ex_25 : Datum :=
  { id := "anandhardtmccloskey2021_25"
    source := ⟨"anand-hardt-mccloskey-2021", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone exhibits it, of course. People misplace their keys. They enter a room only to realize they don't know why."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "211474"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "They enter a room"), ("paraphrase", "they entered that room"), ("mismatch", "tense"), ("mismatch_detail", "historical present")] }

def ex_26 : Datum :=
  { id := "anandhardtmccloskey2021_26"
    source := ⟨"anand-hardt-mccloskey-2021", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rob and Mike both still fish, but they don't know for how long."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "138058"), ("remnant", "for how long"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "Rob and Mike both still fish"), ("paraphrase", "they {will, might, could, ...} fish"), ("mismatch", "tense"), ("mismatch_detail", "present antecedent, modal or future paraphrase")] }

def ex_27a : Datum :=
  { id := "anandhardtmccloskey2021_27a"
    source := ⟨"anand-hardt-mccloskey-2021", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In his state of the union message last week, Clinton said he favored raising the minimum wage but did not say by how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("(i) he modal raise the minimum wage", .acceptable), ("(ii) he favored raising the minimum wage", .acceptable)]
    paperFeatures := [("corpus_id", "15642"), ("remnant", "by how much"), ("position", "embedded"), ("qembedder", "say"), ("antecedent", "he ... raising the minimum wage"), ("antecedent_status", "discontinuous"), ("paraphrase", "he modal raise the minimum wage"), ("mismatch", "modality")] }

def ex_27b : Datum :=
  { id := "anandhardtmccloskey2021_27b"
    source := ⟨"anand-hardt-mccloskey-2021", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Arizona officials concede this year's exports are likely to slow, but they do not know by how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("(i) this year's exports modal slow", .acceptable), ("(ii) this year's exports are likely to slow", .acceptable)]
    paperFeatures := [("corpus_id", "54079"), ("remnant", "by how much"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "this year's exports ... to slow"), ("antecedent_status", "discontinuous"), ("paraphrase", "this year's exports modal slow"), ("mismatch", "modality")] }

def ex_28a : Datum :=
  { id := "anandhardtmccloskey2021_28a"
    source := ⟨"anand-hardt-mccloskey-2021", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now comes the hard part. With all this banter about cyberspace, is it worth it to get your student on line? If so, how? With what company?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "23721"), ("remnant", "how"), ("semantic_type", "manner"), ("position", "root"), ("antecedent", "to get your student on line"), ("paraphrase", "modal you get your student on line"), ("mismatch", "modality"), ("mismatch_detail", "nonfinite antecedent")] }

def ex_28b : Datum :=
  { id := "anandhardtmccloskey2021_28b"
    source := ⟨"anand-hardt-mccloskey-2021", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Oz Chairman Robert Kory vowed to push ahead but would not say how."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "30594"), ("remnant", "how"), ("semantic_type", "manner"), ("position", "embedded"), ("qembedder", "say"), ("antecedent", "to push ahead"), ("paraphrase", "Oz Chairman Robert Kory modal push ahead"), ("mismatch", "modality"), ("mismatch_detail", "nonfinite antecedent")] }

def ex_29a : Datum :=
  { id := "anandhardtmccloskey2021_29a"
    source := ⟨"anand-hardt-mccloskey-2021", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'Turn at the next corner,' my wife said. I didn't ask why."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "142535"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "ask"), ("antecedent", "Turn at the next corner"), ("paraphrase", "I modal turn at the next corner"), ("mismatch", "modality"), ("mismatch_detail", "imperative antecedent")] }

def ex_29b : Datum :=
  { id := "anandhardtmccloskey2021_29b"
    source := ⟨"anand-hardt-mccloskey-2021", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When it comes to mail-order purchases, always use a credit card. Never pay cash. And you know why?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "47922"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "Never pay cash"), ("paraphrase", "you modal never pay cash"), ("mismatch", "modality"), ("mismatch_detail", "imperative antecedent")] }

def ex_30a : Datum :=
  { id := "anandhardtmccloskey2021_30a"
    source := ⟨"anand-hardt-mccloskey-2021", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A minute later, though, he denounced the release anyway, saying it should have happened three or four years ago. How, he didn't reveal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "F50"), ("remnant", "how"), ("semantic_type", "manner"), ("position", "embedded"), ("qembedder", "reveal"), ("antecedent", "it should have happened"), ("paraphrase", "it modal have happened"), ("mismatch", "modality"), ("mismatch_detail", "ability/possibility modal")] }

def ex_30b : Datum :=
  { id := "anandhardtmccloskey2021_30b"
    source := ⟨"anand-hardt-mccloskey-2021", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "And then you get (Pam) Shriver finding a bald man standing at the fence with a giant-sized tennis ball in his hand, asking, 'Would you sign my ball?' So, she darted her red eyes from his head to the ball: 'Which one?'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "205304"), ("remnant", "which one"), ("position", "root"), ("antecedent", "Would you sign my ball"), ("paraphrase", "modal I sign"), ("mismatch", "modality"), ("mismatch_detail", "closest to should")] }

def ex_30c : Datum :=
  { id := "anandhardtmccloskey2021_30c"
    source := ⟨"anand-hardt-mccloskey-2021", "(30c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some anti-AOL types are using cyberspace bulletin boards to try to rally users to oppose it, as well. If enough users opt out—I don't know how many; the number's not disclosed—the settlement will be voided."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "71495"), ("remnant", "how many"), ("semantic_type", "degree"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "enough users opt out"), ("paraphrase", "users modal opt out"), ("mismatch", "modality"), ("mismatch_detail", "necessity modal from the conditional")] }

def ex_31a : Datum :=
  { id := "anandhardtmccloskey2021_31a"
    source := ⟨"anand-hardt-mccloskey-2021", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Among the proposals are new power plants in the region, although the report does not specify where."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "143606"), ("remnant", "where"), ("semantic_type", "locative"), ("position", "embedded"), ("qembedder", "specify"), ("antecedent", "new power plants in the region"), ("antecedent_status", "small clause"), ("paraphrase", "those new power plants modal be in the region"), ("mismatch", "modality"), ("mismatch_detail", "possibility modal, subclausal antecedent")] }

def ex_31b : Datum :=
  { id := "anandhardtmccloskey2021_31b"
    source := ⟨"anand-hardt-mccloskey-2021", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The rediscovered inspiration for 'Ted Williams' brought the burglar back, but his creator can't say for how long."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "124186"), ("remnant", "for how long"), ("position", "embedded"), ("qembedder", "say"), ("antecedent", "the burglar back"), ("antecedent_status", "small clause"), ("paraphrase", "the burglar modal be back"), ("mismatch", "modality"), ("mismatch_detail", "possibility modal, subclausal antecedent")] }

def ex_32 : Datum :=
  { id := "anandhardtmccloskey2021_32"
    source := ⟨"anand-hardt-mccloskey-2021", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'Coach O'Leary doesn't do things without letting you know why,' Hamilton said."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "99992"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "Coach O'Leary doesn't do things"), ("paraphrase", "Coach O'Leary did those things"), ("mismatch", "polarity"), ("polarity_context", "without adjunct"), ("reversal", "negative to positive")] }

def ex_33 : Datum :=
  { id := "anandhardtmccloskey2021_33"
    source := ⟨"anand-hardt-mccloskey-2021", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'I don't think Steve Jobs will let it be a boring MacWorld,' Reynolds said. 'We just don't know how.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "111174"), ("remnant", "how"), ("semantic_type", "manner"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "Steve Jobs will let it be a boring MacWorld"), ("paraphrase", "Steve Jobs will let it be not a boring MacWorld"), ("mismatch", "polarity"), ("polarity_context", "neg-raising"), ("reversal", "positive to negative")] }

def ex_34a : Datum :=
  { id := "anandhardtmccloskey2021_34a"
    source := ⟨"anand-hardt-mccloskey-2021", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Angela J. Campbell, an attorney for opponents to the deal, told the Globe that McCain's letter likely 'tipped' the scales in favor of the decision. 'Senator McCain said, \"Do it by December 15 or explain why,\" and the commission jumped to it and did it that very day,' Campbell told the Globe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "22987"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "explain"), ("antecedent", "Do it"), ("paraphrase", "you did not do it"), ("mismatch", "polarity"), ("polarity_context", "disjunction"), ("reversal", "positive to negative")] }

def ex_34b : Datum :=
  { id := "anandhardtmccloskey2021_34b"
    source := ⟨"anand-hardt-mccloskey-2021", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'It raises real doubts as to whether Iraq is ready to give full, final and complete disclosure' of its weapons programs, said the UK's Weston. 'One has to ask oneself why?' he said earlier in his briefing with reporters."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "99105"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "ask"), ("antecedent", "Iraq is ready to give full, final and complete disclosure"), ("paraphrase", "Iraq is not ready to give full, final and complete disclosure"), ("mismatch", "polarity"), ("polarity_context", "doubt"), ("reversal", "positive to negative")] }

def ex_34c : Datum :=
  { id := "anandhardtmccloskey2021_34c"
    source := ⟨"anand-hardt-mccloskey-2021", "(34c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "But he was handed a small Belgian pistol, and he had little choice but to stay and help, harassing Japanese patrols by night and trying to defend a small patch of land against a communist takeover. 'I don't know why, but I really cannot remember being scared,' he said. 'It all seemed like great fun.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "91594"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "being scared"), ("antecedent_status", "cataphoric"), ("paraphrase", "I was not scared"), ("mismatch", "polarity"), ("polarity_context", "remember"), ("reversal", "positive to negative")] }

def ex_35a : Datum :=
  { id := "anandhardtmccloskey2021_35a"
    source := ⟨"anand-hardt-mccloskey-2021", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of money is now the biggest challenge to America's democracy. And yet since both sides were flinging it around, money can't be said to have determined the outcome. What then?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "41116"), ("remnant", "what"), ("semantic_type", "entity"), ("position", "root"), ("antecedent", "money can't be said to have determined the outcome"), ("paraphrase", "can be said to have determined the outcome"), ("mismatch", "polarity"), ("polarity_context", "QUD with then"), ("reversal", "negative to positive")] }

def ex_35b : Datum :=
  { id := "anandhardtmccloskey2021_35b"
    source := ⟨"anand-hardt-mccloskey-2021", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'He came back and asked me why I had put the two ballets together,' she says. He had wanted it, she reminded Balanchine. 'But that doesn't mean all the time,' Balanchine chided her. How many times then? 'Well, four,' he said at last."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "152316"), ("remnant", "how many times"), ("semantic_type", "degree"), ("position", "root"), ("antecedent", "that doesn't mean all the time"), ("paraphrase", "does it mean"), ("mismatch", "polarity"), ("polarity_context", "QUD with then"), ("reversal", "negative to positive")] }

def ex_36a : Datum :=
  { id := "anandhardtmccloskey2021_36a"
    source := ⟨"anand-hardt-mccloskey-2021", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'They obviously haven't tried any cases in a long time, and obviously don't know how, but this is cross-examination.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "123640"), ("remnant", "how"), ("semantic_type", "manner"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "They obviously haven't tried any cases in a long time"), ("paraphrase", "they modal try cases"), ("mismatch", "polarity"), ("polarity_context", "don't know how"), ("reversal", "negative to positive")] }

def ex_36b : Datum :=
  { id := "anandhardtmccloskey2021_36b"
    source := ⟨"anand-hardt-mccloskey-2021", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Republicans cannot compete with Clinton at this level of the game. They don't know how."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "132033"), ("remnant", "how"), ("semantic_type", "manner"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "Republicans cannot compete with Clinton"), ("paraphrase", "they modal compete with Clinton"), ("mismatch", "polarity"), ("polarity_context", "don't know how"), ("reversal", "negative to positive")] }

def ex_37a : Datum :=
  { id := "anandhardtmccloskey2021_37a"
    source := ⟨"anand-hardt-mccloskey-2021", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He says America was once a better place and that he knows it because he was there. ... What decade?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "138872"), ("remnant", "what decade"), ("position", "root"), ("antecedent", "America was once a better place"), ("paraphrase", "was America a better place in"), ("mismatch", "new_words"), ("new_words", "stranded preposition")] }

def ex_37b : Datum :=
  { id := "anandhardtmccloskey2021_37b"
    source := ⟨"anand-hardt-mccloskey-2021", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Then you see where they're going to place it: What night?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "138731"), ("remnant", "what night"), ("position", "root"), ("antecedent", "they're going to place it"), ("paraphrase", "are they going to place it on"), ("mismatch", "new_words"), ("new_words", "stranded preposition")] }

def ex_37c : Datum :=
  { id := "anandhardtmccloskey2021_37c"
    source := ⟨"anand-hardt-mccloskey-2021", "(37c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'The first thing he said was so interesting that he thought it was a period piece,' Scardino recalled. 'I said \"What period?\" He said, \"Nineteen ninety-one.\"'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "195676"), ("remnant", "what period"), ("position", "root"), ("antecedent", "he thought it was a period piece"), ("paraphrase", "DO YOU THINK it IS a piece from"), ("mismatch", "new_words"), ("new_words", "stranded preposition")] }

def ex_37d : Datum :=
  { id := "anandhardtmccloskey2021_37d"
    source := ⟨"anand-hardt-mccloskey-2021", "(37d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Decker was weaned in the world of investing by his father, who had also been a mutual fund manager. (Decker won't say which firm)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "89932"), ("remnant", "which firm"), ("semantic_type", "classificatory"), ("position", "embedded"), ("qembedder", "say"), ("antecedent", "his father had also been a mutual fund manager"), ("paraphrase", "his father had been a mutual fund manager at"), ("mismatch", "new_words"), ("new_words", "stranded preposition")] }

def ex_38a : Datum :=
  { id := "anandhardtmccloskey2021_38a"
    source := ⟨"anand-hardt-mccloskey-2021", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bradley said that he has not shut the door to a presidential race, though he would not say when."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "176498"), ("remnant", "when"), ("semantic_type", "temporal"), ("position", "embedded"), ("qembedder", "say"), ("antecedent", "a presidential race"), ("antecedent_status", "nominal"), ("paraphrase", "a presidential race modal be"), ("mismatch", "new_words"), ("new_words", "copular clause")] }

def ex_38b : Datum :=
  { id := "anandhardtmccloskey2021_38b"
    source := ⟨"anand-hardt-mccloskey-2021", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The doctors anticipate a full recovery for me, but they really don't know when."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "76117"), ("remnant", "when"), ("semantic_type", "temporal"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "a full recovery"), ("antecedent_status", "nominal"), ("paraphrase", "a full recovery modal be"), ("mismatch", "new_words"), ("new_words", "copular clause")] }

def ex_39a : Datum :=
  { id := "anandhardtmccloskey2021_39a"
    source := ⟨"anand-hardt-mccloskey-2021", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A cut appears almost certain this year; the question is how soon, and by how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "15811"), ("remnant", "how soon"), ("position", "embedded"), ("antecedent", "A cut"), ("antecedent_status", "nominal"), ("paraphrase", "there modal be a cut"), ("mismatch", "new_words"), ("new_words", "existential")] }

def ex_39b : Datum :=
  { id := "anandhardtmccloskey2021_39b"
    source := ⟨"anand-hardt-mccloskey-2021", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even the most conservative voices in the state seem resigned to the prospect of a long costly court battle. To what end?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "135056"), ("remnant", "to what end"), ("position", "root"), ("antecedent", "a long costly court battle"), ("antecedent_status", "nominal"), ("paraphrase", "modal there be a long costly court battle"), ("mismatch", "new_words"), ("new_words", "existential")] }

def ex_40a : Datum :=
  { id := "anandhardtmccloskey2021_40a"
    source := ⟨"anand-hardt-mccloskey-2021", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bodies were discovered just before 1 a.m. when an employee of the shop happened to drive by, noticed lights still on almost three hours after closing time and went inside to see why."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "72082"), ("remnant", "why"), ("semantic_type", "reason"), ("position", "embedded"), ("qembedder", "see"), ("antecedent", "lights still on"), ("antecedent_status", "small clause"), ("paraphrase", "lights were still on"), ("mismatch", "new_words"), ("new_words", "copular clause")] }

def ex_40b : Datum :=
  { id := "anandhardtmccloskey2021_40b"
    source := ⟨"anand-hardt-mccloskey-2021", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't know when, but I can see a couple of major league teams in Japan, one in Seoul, and one in Hawaii, as the stopover on the way."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("corpus_id", "72698"), ("remnant", "when"), ("semantic_type", "temporal"), ("position", "embedded"), ("qembedder", "know"), ("antecedent", "a couple of major league teams in Japan, one in Seoul and one in Hawaii"), ("antecedent_status", "cataphoric"), ("paraphrase", "there modal be a couple of major league teams in Japan, one in Seoul, and one in Hawaii"), ("mismatch", "new_words"), ("new_words", "existential")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_6, ex_7a, ex_7b, ex_8, ex_10, ex_11, ex_13, ex_14a, ex_14b, ex_15a, ex_15b, ex_16, ex_17, ex_18a, ex_18b, ex_19a, ex_19b, ex_20a, ex_20b, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27a, ex_27b, ex_28a, ex_28b, ex_29a, ex_29b, ex_30a, ex_30b, ex_30c, ex_31a, ex_31b, ex_32, ex_33, ex_34a, ex_34b, ex_34c, ex_35a, ex_35b, ex_36a, ex_36b, ex_37a, ex_37b, ex_37c, ex_37d, ex_38a, ex_38b, ex_39a, ex_39b, ex_40a, ex_40b]

end AnandHardtMcCloskey2021.Examples
