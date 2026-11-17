module

public import Linglib.Data.Examples.Schema

/-!
# `RitchieSchiller2024` — typed example data

Auto-generated from `Linglib/Data/Examples/RitchieSchiller2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RitchieSchiller2024.Examples`.
-/

@[expose] public section

namespace RitchieSchiller2024.Examples

def ex_1 : Datum :=
  { id := "ritchieschiller2024_1"
    source := ⟨"ritchie-schiller-2024", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book is on the table."
    glossedTokens := []
    context := "A room with one book, on a table, and no other books or tables."
    judgment := .acceptable
    contrasts := []
    readings := [("(1′) The book in this room is on the table.", .acceptable)]
    paperFeatures := [("restriction", "location"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_1_fig2 : Datum :=
  { id := "ritchieschiller2024_1_fig2"
    source := ⟨"ritchie-schiller-2024", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book is on the table."
    glossedTokens := []
    context := "Three books on a table, differing in genre, author, year, and cover colour; no other books in the room."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "location"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_2a : Datum :=
  { id := "ritchieschiller2024_2a"
    source := ⟨"ritchie-schiller-2024", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book is on the table."
    glossedTokens := []
    context := "Three books on a table, differing in genre, author, year, and cover colour; no other books in the room."
    judgment := .unacceptable
    contrasts := []
    readings := [("The funniest book ever written is on the table.", .unacceptable)]
    paperFeatures := [("restriction", "aesthetic"), ("setup", "none")] }

def ex_2b : Datum :=
  { id := "ritchieschiller2024_2b"
    source := ⟨"ritchie-schiller-2024", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book is on the table."
    glossedTokens := []
    context := "Three books on a table, differing in genre, author, year, and cover colour; no other books in the room."
    judgment := .unacceptable
    contrasts := []
    readings := [("The book on structuralism I read in graduate school is on the table.", .unacceptable)]
    paperFeatures := [("restriction", "history"), ("setup", "none")] }

def ex_2c : Datum :=
  { id := "ritchieschiller2024_2c"
    source := ⟨"ritchie-schiller-2024", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book is on the table."
    glossedTokens := []
    context := "Three books on a table, differing in genre, author, year, and cover colour; no other books in the room. The speaker aims to talk about the blue things in the room."
    judgment := .unacceptable
    contrasts := []
    readings := [("The blue book in this room is on the table.", .unacceptable)]
    paperFeatures := [("restriction", "color"), ("setup", "none")] }

def ex_3 : Datum :=
  { id := "ritchieschiller2024_3"
    source := ⟨"ritchie-schiller-2024", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is on the table."
    glossedTokens := []
    context := "A room with three books, on a table."
    judgment := .acceptable
    contrasts := []
    readings := [("(3′) Every book in this room is on the table.", .acceptable)]
    paperFeatures := [("restriction", "location"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_4a : Datum :=
  { id := "ritchieschiller2024_4a"
    source := ⟨"ritchie-schiller-2024", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is on the table."
    glossedTokens := []
    context := "Three books on a table and several stacks of books on the floor; the books on the table are all the hardcover books in the room."
    judgment := .unacceptable
    contrasts := []
    readings := [("Every hardcover book in this room is on the table.", .unacceptable)]
    paperFeatures := [("restriction", "subkind"), ("setup", "none")] }

def ex_4b : Datum :=
  { id := "ritchieschiller2024_4b"
    source := ⟨"ritchie-schiller-2024", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is on the table."
    glossedTokens := []
    context := "Three books on a table and several stacks on the floor; the books on the table are all the depressing books in the room."
    judgment := .unacceptable
    contrasts := []
    readings := [("Every depressing book in this room is on the table.", .unacceptable)]
    paperFeatures := [("restriction", "aesthetic"), ("setup", "none")] }

def ex_4c : Datum :=
  { id := "ritchieschiller2024_4c"
    source := ⟨"ritchie-schiller-2024", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is on the table."
    glossedTokens := []
    context := "Three books on a table and several stacks on the floor; the books on the table are all the coffee-stained books in the room."
    judgment := .unacceptable
    contrasts := []
    readings := [("Every coffee-stained book in this room is on the table.", .unacceptable)]
    paperFeatures := [("restriction", "history"), ("setup", "none")] }

def ex_3_now : Datum :=
  { id := "ritchieschiller2024_3_now"
    source := ⟨"ritchie-schiller-2024", "(3″)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is on the table."
    glossedTokens := []
    context := "A room with three books, on a table."
    judgment := .acceptable
    contrasts := []
    readings := [("Every book is on the table right now.", .acceptable)]
    paperFeatures := [("restriction", "time"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_3_tomorrow : Datum :=
  { id := "ritchieschiller2024_3_tomorrow"
    source := ⟨"ritchie-schiller-2024", "(3‴)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is on the table."
    glossedTokens := []
    context := "A room with three books, on a table."
    judgment := .unacceptable
    contrasts := []
    readings := [("Every book is on the table tomorrow.", .unacceptable)]
    paperFeatures := [("restriction", "time"), ("setup", "none"), ("anchor", "elsewhere")] }

def fn4 : Datum :=
  { id := "ritchieschiller2024_fn4"
    source := ⟨"ritchie-schiller-2024", "fn. 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is on the table."
    glossedTokens := []
    context := "Asked to describe what the room will look like tomorrow."
    judgment := .acceptable
    contrasts := []
    readings := [("Every book is on the table tomorrow.", .acceptable)]
    paperFeatures := [("restriction", "time"), ("setup", "question"), ("anchor", "elsewhere")] }

def ex_5 : Datum :=
  { id := "ritchieschiller2024_5"
    source := ⟨"ritchie-schiller-2024", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well the shirts are near the register, and the book is on the table."
    glossedTokens := []
    context := "A and B work in a department store and must create a display of blue merchandise; A asks: Where are the blue things? There are three books on the table."
    judgment := .acceptable
    contrasts := []
    readings := [("The blue book in this room is on the table.", .acceptable)]
    paperFeatures := [("restriction", "color"), ("setup", "question")] }

def ex_7 : Datum :=
  { id := "ritchieschiller2024_7"
    source := ⟨"ritchie-schiller-2024", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The front door is locked."
    glossedTokens := []
    context := "Question under discussion: What is the way things are at Civil Coffee on Figueroa today?"
    judgment := .acceptable
    contrasts := []
    readings := [("(8) The front door of Civil Coffee on Figueroa is locked.", .acceptable)]
    paperFeatures := [("restriction", "location"), ("setup", "question"), ("anchor", "elsewhere")] }

def ex_9 : Datum :=
  { id := "ritchieschiller2024_9"
    source := ⟨"ritchie-schiller-2024", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The table is wobbly and has three laptops on it."
    glossedTokens := []
    context := "Question under discussion: What is the way things are at Civil Coffee today? The tables are mostly square, with one round and one rectangular table."
    judgment := .unacceptable
    contrasts := []
    readings := [("(9′) The round table at Civil Coffee on Figueroa is wobbly and has three laptops on it.", .unacceptable)]
    paperFeatures := [("restriction", "shape"), ("setup", "question")] }

def ex_10 : Datum :=
  { id := "ritchieschiller2024_10"
    source := ⟨"ritchie-schiller-2024", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone is here."
    glossedTokens := []
    context := "Leto and Duncan are discussing potential co-conspirators."
    judgment := .acceptable
    contrasts := []
    readings := [("(11) Leto, Duncan, Amir, Jessica, and Yueh are here.", .acceptable)]
    paperFeatures := [("restriction", "plan"), ("setup", "priorGoal")] }

def ex_16 : Datum :=
  { id := "ritchieschiller2024_16"
    source := ⟨"ritchie-schiller-2024", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They’re all green."
    glossedTokens := []
    context := "A room with green books visible on the shelves; it is common knowledge that numerous books in the room are hidden from view."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "availability"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_17 : Datum :=
  { id := "ritchieschiller2024_17"
    source := ⟨"ritchie-schiller-2024", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book is green."
    glossedTokens := []
    context := "A room with green books visible on the shelves; it is common knowledge that numerous books in the room are hidden from view."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "availability"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_18_room : Datum :=
  { id := "ritchieschiller2024_18_room"
    source := ⟨"ritchie-schiller-2024", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every plant is blooming."
    glossedTokens := []
    context := "An enclosed room; the plants within arm’s reach are blooming but some plants near the door are not."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "salience"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_18_window : Datum :=
  { id := "ritchieschiller2024_18_window"
    source := ⟨"ritchie-schiller-2024", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every plant is blooming."
    glossedTokens := []
    context := "An enclosed room; every plant in the room is blooming but some plants visible through a window are not."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "location"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_18_meadow : Datum :=
  { id := "ritchieschiller2024_18_meadow"
    source := ⟨"ritchie-schiller-2024", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every plant is blooming."
    glossedTokens := []
    context := "A large open meadow; the plants near the conversationalists are blooming but some at the meadow’s edges are not."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "salience"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_19 : Datum :=
  { id := "ritchieschiller2024_19"
    source := ⟨"ritchie-schiller-2024", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everything’s covered in snow!"
    glossedTokens := []
    context := "A backyard on a winter night after a snowfall: the lawn furniture, potted plants, and garden gnomes are covered, the clouds, the moon, and the trees in the near distance are not."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "manipulability"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_20_hands : Datum :=
  { id := "ritchieschiller2024_20_hands"
    source := ⟨"ritchie-schiller-2024", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We’re going to destroy everything."
    glossedTokens := []
    context := "Entering a room with bare hands."
    judgment := .acceptable
    contrasts := []
    readings := [("smaller objects and some furniture", .acceptable)]
    paperFeatures := [("restriction", "manipulability"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_20_hammers : Datum :=
  { id := "ritchieschiller2024_20_hammers"
    source := ⟨"ritchie-schiller-2024", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We’re going to destroy everything."
    glossedTokens := []
    context := "Entering the same room armed with sledgehammers."
    judgment := .acceptable
    contrasts := []
    readings := [("the sheetrock walls included", .acceptable)]
    paperFeatures := [("restriction", "manipulability"), ("setup", "none"), ("anchor", "hereNow")] }

def ex_21 : Datum :=
  { id := "ritchieschiller2024_21"
    source := ⟨"ritchie-schiller-2024", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I’ll go grab the book and the shirts."
    glossedTokens := []
    context := "A: The blue merchandise belongs in the display by the door. The items may be in another room or a warehouse across town."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "color"), ("setup", "assertion")] }

def ex_22 : Datum :=
  { id := "ritchieschiller2024_22"
    source := ⟨"ritchie-schiller-2024", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "OK! I’ll go grab the book and the shirts."
    glossedTokens := []
    context := "A: Bring the blue merchandise to the display by the door."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "color"), ("setup", "directive")] }

def ex_23 : Datum :=
  { id := "ritchieschiller2024_23"
    source := ⟨"ritchie-schiller-2024", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The painting is even bigger and more erratic than I had expected."
    glossedTokens := []
    context := "Arman and Bea planned to see a newly acquired Cy Twombly painting and meet in the room where it hangs with many other paintings, some more salient."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "plan"), ("setup", "priorGoal")] }

def library : Datum :=
  { id := "ritchieschiller2024_library"
    source := ⟨"ritchie-schiller-2024", "§4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I think we’re done! I put all the books on the table."
    glossedTokens := []
    context := "Two parents have the aim of collecting all the library books their children checked out, from under couches, the car, and backpacks."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("restriction", "plan"), ("setup", "priorGoal")] }

def ex_25 : Datum :=
  { id := "ritchieschiller2024_25"
    source := ⟨"ritchie-schiller-2024", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carl managed to have his sensitive phone call overheard by everyone again."
    glossedTokens := []
    context := "Discourse-initial, at a cafe; common knowledge that Carl works in the UCLA linguistics department."
    judgment := .acceptable
    contrasts := []
    readings := [("everyone in the UCLA linguistics department", .acceptable)]
    paperFeatures := [("restriction", "location"), ("setup", "displacement"), ("anchor", "elsewhere")] }

def ex_26 : Datum :=
  { id := "ritchieschiller2024_26"
    source := ⟨"ritchie-schiller-2024", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dan’s daughter was trying to make a cake, and apparently everything is covered in flour!"
    glossedTokens := []
    context := "On the phone with Dan, who reports on the state of his kitchen, while shopping for his party."
    judgment := .acceptable
    contrasts := []
    readings := [("everything in Dan’s kitchen", .acceptable)]
    paperFeatures := [("restriction", "location"), ("setup", "displacement"), ("anchor", "elsewhere")] }

def all : List Datum := [ex_1, ex_1_fig2, ex_2a, ex_2b, ex_2c, ex_3, ex_4a, ex_4b, ex_4c, ex_3_now, ex_3_tomorrow, fn4, ex_5, ex_7, ex_9, ex_10, ex_16, ex_17, ex_18_room, ex_18_window, ex_18_meadow, ex_19, ex_20_hands, ex_20_hammers, ex_21, ex_22, ex_23, library, ex_25, ex_26]

end RitchieSchiller2024.Examples
