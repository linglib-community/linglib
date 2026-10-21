module

public import Linglib.Data.Examples.Schema

/-!
# `YuAusensiSmith2023` — typed example data

Auto-generated from `Linglib/Data/Examples/YuAusensiSmith2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace YuAusensiSmith2023.Examples`.
-/

@[expose] public section

namespace YuAusensiSmith2023.Examples

def ex_16a : Datum :=
  { id := "yuausensismith2023_16a"
    source := ⟨"yu-ausensi-smith-2023", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The toddler broke his hands bloody."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state"), ("judgedBy", "Rappaport Hovav and Levin")] }

def ex_16b : Datum :=
  { id := "yuausensismith2023_16b"
    source := ⟨"yu-ausensi-smith-2023", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The clumsy child broke the beauty out of the vase."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state"), ("judgedBy", "Rappaport Hovav and Levin")] }

def ex_17a : Datum :=
  { id := "yuausensismith2023_17a"
    source := ⟨"yu-ausensi-smith-2023", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kelly broke the dishes valueless."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state"), ("judgedBy", "Rappaport Hovav and Levin")] }

def ex_17b : Datum :=
  { id := "yuausensismith2023_17b"
    source := ⟨"yu-ausensi-smith-2023", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill broke the vase worthless."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state"), ("judgedBy", "Jackendoff")] }

def ex_18a : Datum :=
  { id := "yuausensismith2023_18a"
    source := ⟨"yu-ausensi-smith-2023", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The rocket burned into the hotel."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state"), ("judgedBy", "Jackendoff")] }

def ex_18b : Datum :=
  { id := "yuausensismith2023_18b"
    source := ⟨"yu-ausensi-smith-2023", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The water froze out of the bottle."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state"), ("judgedBy", "Jackendoff")] }

def ex_23 : Datum :=
  { id := "yuausensismith2023_23"
    source := ⟨"yu-ausensi-smith-2023", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John opened the door again."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")] }

def ex_24a : Datum :=
  { id := "yuausensismith2023_24a"
    source := ⟨"yu-ausensi-smith-2023", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sharpened the knife again."
    glossedTokens := []
    context := "John buys a knife that was forged in such a way that it was already sharp. John uses it until it becomes blunt. He uses a whetting stone to make it sharp once more."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")] }

def ex_24b : Datum :=
  { id := "yuausensismith2023_24b"
    source := ⟨"yu-ausensi-smith-2023", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The producer lengthened the film again."
    glossedTokens := []
    context := "A film producer makes a 4 hour long film, which is significantly longer than the norm. She is pressured to reduce its length, so cuts it to be two hours. But then the director and actors protest, so she restores it to 4 hours."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")] }

def ex_24c : Datum :=
  { id := "yuausensismith2023_24c"
    source := ⟨"yu-ausensi-smith-2023", "(24c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim enlarged the photograph again."
    glossedTokens := []
    context := "Kim takes a photo that is too large to use as a Facebook profile photo. She shrinks it to a more appropriate size, but thinks it does not look good. So she restores it to its original size and puts it on her personal website instead."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")] }

def ex_25a : Datum :=
  { id := "yuausensismith2023_25a"
    source := ⟨"yu-ausensi-smith-2023", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the plate again."
    glossedTokens := []
    context := "Mary requested a potter to make a plate in separate pieces so she can practice her pottery-mending skills. She took a day to put the pieces together. John, who was secretly angry with Mary for previously breaking his favorite bowl, snatched the mended plate from Mary and broke it."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")] }

def ex_25b : Datum :=
  { id := "yuausensismith2023_25b"
    source := ⟨"yu-ausensi-smith-2023", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leah thawed the meat again."
    glossedTokens := []
    context := "Leah kills a rabbit, takes it home and skins and butchers it and then puts the fresh meat in the freezer for three days. She then takes it out and puts it on the table to thaw."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")] }

def ex_25c : Datum :=
  { id := "yuausensismith2023_25c"
    source := ⟨"yu-ausensi-smith-2023", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim melted the ice cream again."
    glossedTokens := []
    context := "An ice cream factory manufactures ice cream from a package of ingredients by adding water and then freezing the result. After adding the contents of the package to water and freezing it, Kim lets it melt into a liquid state."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")] }

def ex_26 : Datum :=
  { id := "yuausensismith2023_26"
    source := ⟨"yu-ausensi-smith-2023", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan opened the door for two hours."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .acceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "property concept")] }

def ex_27 : Datum :=
  { id := "yuausensismith2023_27"
    source := ⟨"yu-ausensi-smith-2023", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan broke the vase for 5 minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")] }

def ex_28 : Datum :=
  { id := "yuausensismith2023_28"
    source := ⟨"yu-ausensi-smith-2023", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jill thawed the meat for 30 minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")] }

def ex_29 : Datum :=
  { id := "yuausensismith2023_29"
    source := ⟨"yu-ausensi-smith-2023", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Johannes melted the cheese for 10 minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")] }

def fn11i : Datum :=
  { id := "yuausensismith2023_fn11i"
    source := ⟨"yu-ausensi-smith-2023", "fn. 11 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jill thawed the meat for 1 minute."
    glossedTokens := []
    context := "Jill is an astronaut in a space station currently in outer space and had a piece of frozen meat she wanted to eat. She left it out to thaw but because things freeze so quickly in outer space, it only managed to stay thawed for 1 minute before it refroze."
    judgment := .unacceptable
    alternatives := []
    readings := [("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")] }

def ex_30 : Datum :=
  { id := "yuausensismith2023_30"
    source := ⟨"yu-ausensi-smith-2023", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim opened the door into the garden."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31a : Datum :=
  { id := "yuausensismith2023_31a"
    source := ⟨"yu-ausensi-smith-2023", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The citizens darkened the city invisible."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31b : Datum :=
  { id := "yuausensismith2023_31b"
    source := ⟨"yu-ausensi-smith-2023", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dentist whitened his teeth clean."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31c : Datum :=
  { id := "yuausensismith2023_31c"
    source := ⟨"yu-ausensi-smith-2023", "(31c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We cooled the people out of the room with the air-conditioner on too high."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31d : Datum :=
  { id := "yuausensismith2023_31d"
    source := ⟨"yu-ausensi-smith-2023", "(31d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim dimmed her eyes sore."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31e : Datum :=
  { id := "yuausensismith2023_31e"
    source := ⟨"yu-ausensi-smith-2023", "(31e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I thinned the soup tasteless."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31f : Datum :=
  { id := "yuausensismith2023_31f"
    source := ⟨"yu-ausensi-smith-2023", "(31f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My kid cleared his bedroom empty."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_35a : Datum :=
  { id := "yuausensismith2023_35a"
    source := ⟨"yu-ausensi-smith-2023", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "With a few slices of her claws, she tore him free."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")] }

def ex_35b : Datum :=
  { id := "yuausensismith2023_35b"
    source := ⟨"yu-ausensi-smith-2023", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A couple of monks broke the corpse loose from the deck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")] }

def ex_35c : Datum :=
  { id := "yuausensismith2023_35c"
    source := ⟨"yu-ausensi-smith-2023", "(35c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Scientists just melted a hole through 3,500 feet of ice."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")] }

def ex_36 : Datum :=
  { id := "yuausensismith2023_36"
    source := ⟨"yu-ausensi-smith-2023", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "With a few slices of her claws, she tore him free... but nothing actually got torn."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "entailment denial"), ("root class", "change of state")] }

def ex_37a : Datum :=
  { id := "yuausensismith2023_37a"
    source := ⟨"yu-ausensi-smith-2023", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The hammer-head broke off but nothing broke."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "entailment denial"), ("root class", "change of state"), ("judgedBy", "Rappaport Hovav")] }

def ex_37b : Datum :=
  { id := "yuausensismith2023_37b"
    source := ⟨"yu-ausensi-smith-2023", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The squash split open but there was no split in it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "entailment denial"), ("root class", "change of state"), ("judgedBy", "Rappaport Hovav")] }

def ex_44 : Datum :=
  { id := "yuausensismith2023_44"
    source := ⟨"yu-ausensi-smith-2023", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke his hands bloody."
    glossedTokens := []
    context := "John broke his hands. It was such a severe fracture that the sharp edges of the broken bones in his hand pierced through his flesh when they broke and he bled profusely."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")] }

def ex_45 : Datum :=
  { id := "yuausensismith2023_45"
    source := ⟨"yu-ausensi-smith-2023", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John opened the door into the garden."
    glossedTokens := []
    context := "There was a door leading to the garden. The hinges were really loose and the door was on the verge of falling off them. John wanted to go out to his garden to tend to his plants. He opened the door with too much force, however, and the door broke off its hinges and fell onto his garden lawn."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def all : List Datum := [ex_16a, ex_16b, ex_17a, ex_17b, ex_18a, ex_18b, ex_23, ex_24a, ex_24b, ex_24c, ex_25a, ex_25b, ex_25c, ex_26, ex_27, ex_28, ex_29, fn11i, ex_30, ex_31a, ex_31b, ex_31c, ex_31d, ex_31e, ex_31f, ex_35a, ex_35b, ex_35c, ex_36, ex_37a, ex_37b, ex_44, ex_45]

end YuAusensiSmith2023.Examples
