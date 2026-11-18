module

public import Linglib.Data.Examples.Schema

/-!
# `Theiler2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Theiler2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Theiler2021.Examples`.
-/

@[expose] public section

namespace Theiler2021.Examples

def ex_1a : Datum :=
  { id := "theiler2021_1a"
    source := ⟨"theiler-2021", "(1a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kann Tim denn schwimmen?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2a : Datum :=
  { id := "theiler2021_2a"
    source := ⟨"theiler-2021", "(2a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Warum lachst du denn?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_3a : Datum :=
  { id := "theiler2021_3a"
    source := ⟨"theiler-2021", "(3a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kritik ist willkommen, wenn sie denn konstruktiv ist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_4a : Datum :=
  { id := "theiler2021_4a"
    source := ⟨"theiler-2021", "(4a), (20a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Welche Anna meinst du denn?"
    glossedTokens := []
    context := "Two Annas: A and B know exactly two people called Anna, one in Munich and one in Berlin. A: Earlier today, Anna called."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_4b : Datum :=
  { id := "theiler2021_4b"
    source := ⟨"theiler-2021", "(4b), (20b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Meinst du denn Anna aus München?"
    glossedTokens := []
    context := "Two Annas: A and B know exactly two people called Anna, one in Munich and one in Berlin. A: Earlier today, Anna called."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_6 : Datum :=
  { id := "theiler2021_6"
    source := ⟨"theiler-2021", "(6)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Entschuldigen Sie, ist heute denn Montag?"
    glossedTokens := []
    context := "A approaches a stranger on the street."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_7 : Datum :=
  { id := "theiler2021_7"
    source := ⟨"theiler-2021", "(7)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist heute denn Montag?"
    glossedTokens := []
    context := "Garbage is collected on Mondays. A: Can you put out the garbage later today?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_8 : Datum :=
  { id := "theiler2021_8"
    source := ⟨"theiler-2021", "(8)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wie spät ist es denn?"
    glossedTokens := []
    context := "Early waking 1: A wakes B in the middle of the night and asks."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_9 : Datum :=
  { id := "theiler2021_9"
    source := ⟨"theiler-2021", "(9)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wie spät ist es denn?"
    glossedTokens := []
    context := "Early waking 2: B wakes A in the middle of the night, and A asks."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_12 : Datum :=
  { id := "theiler2021_12"
    source := ⟨"theiler-2021", "(12)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist denn Peter auch hier?"
    glossedTokens := []
    context := "Party: Peter only goes to a party if Sophie goes, not conversely; commonly known. A: Sophie is over there!"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_13 : Datum :=
  { id := "theiler2021_13"
    source := ⟨"theiler-2021", "(13)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist denn Sophie auch hier?"
    glossedTokens := []
    context := "Party: Peter only goes to a party if Sophie goes, not conversely; commonly known. A: Peter is over there!"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_14a : Datum :=
  { id := "theiler2021_14a"
    source := ⟨"theiler-2021", "(14a), (27)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Schau mal! War es denn diesen Winter kälter als normal?"
    glossedTokens := []
    context := "Frozen Lake: A and B walk by a lake that usually does not freeze; A notices it is frozen."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "theiler2021_14b"
    source := ⟨"theiler-2021", "(14b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Schau mal! Sollen wir denn Schlittschuh laufen gehen?"
    glossedTokens := []
    context := "Frozen Lake: A and B walk by a lake that usually does not freeze; A notices it is frozen."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_21 : Datum :=
  { id := "theiler2021_21"
    source := ⟨"theiler-2021", "(21)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Weißt du das denn auch sicher?"
    glossedTokens := []
    context := "A: an arbitrary assertion."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_22 : Datum :=
  { id := "theiler2021_22"
    source := ⟨"theiler-2021", "(22)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wann genau kommt er denn an?"
    glossedTokens := []
    context := "A: This afternoon, please pick up Karl from the station!"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_23 : Datum :=
  { id := "theiler2021_23"
    source := ⟨"theiler-2021", "(23)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wie viel verdienst du denn?"
    glossedTokens := []
    context := "A: Which tax bracket am I in?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_24 : Datum :=
  { id := "theiler2021_24"
    source := ⟨"theiler-2021", "(24)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bist du denn noch unter achtzehn?"
    glossedTokens := []
    context := "Only people younger than eighteen can buy discounted tickets. A: Am I eligible for the discount?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_25 : Datum :=
  { id := "theiler2021_25"
    source := ⟨"theiler-2021", "(25)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Oh, wo wohnt sie denn nochmal?"
    glossedTokens := []
    context := "A: I'm just gonna look up how to get to Lisa's party. [Takes out his phone.]"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_26a : Datum :=
  { id := "theiler2021_26a"
    source := ⟨"theiler-2021", "(26a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat er denn eine Freundin?"
    glossedTokens := []
    context := "A: Is Anton's girlfriend also coming?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_29 : Datum :=
  { id := "theiler2021_29"
    source := ⟨"theiler-2021", "(29)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Oh! Ist es denn schon nach Mitternacht?"
    glossedTokens := []
    context := "Night Bus: a night bus, which runs only after midnight, drives by A and B."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_31a : Datum :=
  { id := "theiler2021_31a"
    source := ⟨"theiler-2021", "(31a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Brauche ich denn keinen Schlüssel?"
    glossedTokens := []
    context := "Opening doors: only A has keys. A: You go on and open the door! I'm coming in a minute."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_31b : Datum :=
  { id := "theiler2021_31b"
    source := ⟨"theiler-2021", "(31b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Brauche ich denn einen Schlüssel?"
    glossedTokens := []
    context := "Opening doors: only A has keys. A: You go on and open the door! I'm coming in a minute."
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_32a : Datum :=
  { id := "theiler2021_32a"
    source := ⟨"theiler-2021", "(32a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat sie denn im Lotto gewonnen, oder hat sie denn reich geerbt?"
    glossedTokens := []
    context := "A: Did you hear? Sarah is going on a world trip next week!"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_32b : Datum :=
  { id := "theiler2021_32b"
    source := ⟨"theiler-2021", "(32b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat sie denn im Lotto gewonnen?"
    glossedTokens := []
    context := "A: Did you hear? Sarah is going on a world trip next week!"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_32c : Datum :=
  { id := "theiler2021_32c"
    source := ⟨"theiler-2021", "(32c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat sie denn schon eine Route geplant und hat sie denn die Flüge schon gebucht?"
    glossedTokens := []
    context := "A: Did you hear? Sarah is going on a world trip next week!"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_35 : Datum :=
  { id := "theiler2021_35"
    source := ⟨"theiler-2021", "(35)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kommst du denn am Montag↑ oder am Dienstag↓?"
    glossedTokens := []
    context := "A: Can you pick me up from the station?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_36 : Datum :=
  { id := "theiler2021_36"
    source := ⟨"theiler-2021", "(36)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Haben Sie denn eine Kundenkarte oder einen Studentenausweis↑?"
    glossedTokens := []
    context := "At the ticket counter. A: One discounted ticket please."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_38 : Datum :=
  { id := "theiler2021_38"
    source := ⟨"theiler-2021", "(38)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Welchen Wein möchtest du denn?"
    glossedTokens := []
    context := "Host asking guest at a dinner party."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_45 : Datum :=
  { id := "theiler2021_45"
    source := ⟨"theiler-2021", "(45)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wenn sie das denn will."
    glossedTokens := []
    context := "A: Caro can win."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_47b : Datum :=
  { id := "theiler2021_47b"
    source := ⟨"theiler-2021", "(47b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kritik ist willkommen, wenn sie denn konstruktiv ist – und auch wenn sie nicht konstruktiv ist."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_48a : Datum :=
  { id := "theiler2021_48a"
    source := ⟨"theiler-2021", "(48a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wir gehen morgen Squash spielen, wenn denn Court 1 frei ist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_48b : Datum :=
  { id := "theiler2021_48b"
    source := ⟨"theiler-2021", "(48b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wir gehen morgen Squash spielen, wenn Court 1 frei ist oder wenn denn Court 2 frei ist."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_52 : Datum :=
  { id := "theiler2021_52"
    source := ⟨"theiler-2021", "(52)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er kann Bundespräsident werden, wenn er denn mindestens 40 Jahre alt ist."
    glossedTokens := []
    context := "Tina asks whether Grandpa Erich can become president; her father knows the answer but wants her to work it out."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_61a : Datum :=
  { id := "theiler2021_61a"
    source := ⟨"theiler-2021", "(61a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Trinkst du überhaupt/#denn Alkohol?"
    glossedTokens := []
    context := "A offered wine, then beer; B declined both. QUD: what alcohol does B want?"
    judgment := .acceptable
    contrasts := []
    readings := [("with überhaupt", .acceptable), ("with denn", .unacceptable)]
    paperFeatures := [] }

def ex_61b : Datum :=
  { id := "theiler2021_61b"
    source := ⟨"theiler-2021", "(61b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Trinkst du #überhaupt/denn keinen Alkohol?"
    glossedTokens := []
    context := "A offered wine, then beer; B declined both. QUD: what alcohol does B want?"
    judgment := .acceptable
    contrasts := []
    readings := [("with überhaupt", .unacceptable), ("with denn", .acceptable)]
    paperFeatures := [] }

def ex_70 : Datum :=
  { id := "theiler2021_70"
    source := ⟨"theiler-2021", "(70)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Karl muss ins Gefängnis, denn er hat Drogen verkauft."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_71 : Datum :=
  { id := "theiler2021_71"
    source := ⟨"theiler-2021", "(71)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat er denn Drogen verkauft?"
    glossedTokens := []
    context := "A: Karl has to go to jail."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_72 : Datum :=
  { id := "theiler2021_72"
    source := ⟨"theiler-2021", "(72)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat er denn ein Verbrechen begangen?"
    glossedTokens := []
    context := "A: Karl has to go to jail."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1a, ex_2a, ex_3a, ex_4a, ex_4b, ex_6, ex_7, ex_8, ex_9, ex_12, ex_13, ex_14a, ex_14b, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26a, ex_29, ex_31a, ex_31b, ex_32a, ex_32b, ex_32c, ex_35, ex_36, ex_38, ex_45, ex_47b, ex_48a, ex_48b, ex_52, ex_61a, ex_61b, ex_70, ex_71, ex_72]

end Theiler2021.Examples
