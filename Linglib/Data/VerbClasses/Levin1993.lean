module

public import Linglib.Data.VerbClasses.Schema

/-!
# Levin1993: verb classes (generated)

Auto-generated from `Linglib/Data/VerbClasses/Levin1993.json` by `scripts/gen_verb_classes.py`.
**Do not edit by hand**: edit the JSON and re-run the generator.

The verb classes of Part II of Levin's English Verb Classes and Alternations, one per class page
with a member list, in the book's order: the section number and title the book prints, the book page
on which the class begins, the members by citation form, with her parenthetical glosses dropped, and
those she marks with a question mark, and the property table. A property line names an alternation
by its section number in Part One or a further property of the page, with the mark the page puts
before it, the members it applies to ('some verbs', 'most verbs', 'except kill'), and any further
qualifier it prints. An attested family heading is the Part One subsection that lists the class: an
unqualified 'Causative Alternation' is Part One's other causative alternations (1.1.2.3), as the
book states in 1.1.2, and an attested 'Locative Alternation' is the spray/load, wipe or swarm
alternation whose Part One list carries the class; the unintentional-interpretation headings that
print a reflexive and a body-part sub-line are two lines. The lists and tables were checked against
the book's pages.

## References

* [levin-1993]
-/

@[expose] public section

namespace Data.VerbClasses.Levin1993

open Data.VerbClasses

/-- The classes of chapter 9. -/
def chapter9 : List VerbClass := [
  { number := "9.1", page := 111,
    title := "Put Verbs",
    members :=
      ["arrange", "immerse", "install", "lodge", "mount", "place", "position", "put", "set",
      "situate", "sling", "stash", "stow"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "9.2", page := 112,
    title := "Verbs of Putting in a Spatial Configuration",
    members :=
      ["dangle", "hang", "lay", "lean", "perch", "rest", "sit", "stand", "suspend"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .most, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "9.3", page := 113,
    title := "Funnel Verbs",
    members :=
      ["bang", "channel", "dip", "dump", "funnel", "hammer", "ladle", "pound", "push", "rake",
      "ram", "scoop", "scrape", "shake", "shovel", "siphon", "spoon", "squash", "squeeze",
      "squish", "sweep", "tuck", "wad", "wedge", "wipe", "wring"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "9.4", page := 114,
    title := "Verbs of Putting with a Specified Direction",
    members :=
      ["drop", "hoist", "lift", "lower", "raise"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "9.5", page := 115,
    title := "Pour Verbs",
    members :=
      ["dribble", "drip", "pour", "slop", "slosh", "spew", "spill", "spurt"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
      ⟨.alternation [7, 7], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .few, none⟩] },
  { number := "9.6", page := 116,
    title := "Coil Verbs",
    members :=
      ["coil", "curl", "loop", "roll", "spin", "twirl", "twist", "whirl", "wind"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [7, 7], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "9.7", page := 117,
    title := "Spray/Load Verbs",
    members :=
      ["brush", "cram", "crowd", "cultivate", "dab", "daub", "drape", "drizzle", "dust", "hang",
      "heap", "inject", "jam", "load", "mound", "pack", "pile", "plant", "plaster", "prick",
      "pump", "rub", "scatter", "seed", "settle", "sew", "shower", "slather", "smear",
      "smudge", "sow", "spatter", "splash", "splatter", "spray", "spread", "sprinkle",
      "spritz", "squirt", "stack", "stick", "stock", "strew", "string", "stuff", "swab",
      "vest", "wash", "wrap"],
    doubtful := ["prick", "vest", "wash"],
    properties :=
      [⟨.alternation [2, 3, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .some, some "based on locative variant"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, some "based on with variant"⟩,
      ⟨.alternation [1, 3], .acceptable, .some, none⟩,
      ⟨.alternation [7, 7], .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "9.8", page := 119,
    title := "Fill Verbs",
    members :=
      ["adorn", "anoint", "bandage", "bathe", "bestrew", "bind", "blanket", "block", "blot",
      "bombard", "carpet", "choke", "cloak", "clog", "clutter", "coat", "contaminate",
      "cover", "dam", "dapple", "deck", "decorate", "deluge", "dirty", "dot", "douse",
      "drench", "edge", "embellish", "emblazon", "encircle", "encrust", "endow", "enrich",
      "entangle", "face", "festoon", "fill", "fleck", "flood", "frame", "garland", "garnish",
      "imbue", "impregnate", "infect", "inlay", "interlace", "interlard", "interleave",
      "intersperse", "interweave", "inundate", "lard", "lash", "line", "litter", "mask",
      "mottle", "ornament", "pad", "pave", "plate", "plug", "pollute", "replenish",
      "repopulate", "riddle", "ring", "ripple", "robe", "saturate", "season", "shroud",
      "smother", "soak", "soil", "speckle", "splotch", "spot", "staff", "stain", "stipple",
      "stop up", "stud", "suffuse", "surround", "swaddle", "swathe", "taint", "tile", "trim",
      "veil", "vein", "wreathe"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 5], .acceptable, .all, none⟩,
      ⟨.property .withAlternatesWithIn, .acceptable, .some, none⟩] },
  { number := "9.9", page := 120,
    title := "Butter Verbs",
    members :=
      ["asphalt", "bait", "blanket", "blindfold", "board", "bread", "brick", "bridle", "bronze",
      "butter", "buttonhole", "cap", "carpet", "caulk", "chrome", "cloak", "cork", "crown",
      "diaper", "drug", "feather", "fence", "flour", "forest", "frame", "fuel", "gag",
      "garland", "glove", "graffiti", "gravel", "grease", "groove", "halter", "harness",
      "heel", "ink", "label", "leash", "leaven", "lipstick", "mantle", "mulch", "muzzle",
      "nickel", "oil", "ornament", "panel", "paper", "parquet", "patch", "pepper", "perfume",
      "pitch", "plank", "plaster", "poison", "polish", "pomade", "poster", "postmark",
      "powder", "putty", "robe", "roof", "rosin", "rouge", "rut", "saddle", "salt", "salve",
      "sand", "seed", "sequin", "shawl", "shingle", "shoe", "shutter", "silver", "slate",
      "slipcover", "sod", "sole", "spice", "stain", "starch", "stopper", "stress", "string",
      "stucco", "sugar", "sulphur", "tag", "tar", "tarmac", "tassel", "thatch", "ticket",
      "tile", "turf", "veil", "veneer", "wallpaper", "water", "wax", "whitewash", "wreathe",
      "yoke", "zipcode"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 2], .acceptable, .all, none⟩,
      ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "9.10", page := 121,
    title := "Pocket Verbs",
    members :=
      ["archive", "bag", "bank", "beach", "bed", "bench", "berth", "billet", "bin", "bottle", "box",
      "cage", "can", "case", "cellar", "cloister", "coop", "corral", "crate", "dock",
      "drydock", "file", "fork", "garage", "ground", "hangar", "house", "jail", "jar", "jug",
      "kennel", "land", "lodge", "pasture", "pen", "pillory", "pocket", "pot", "sheathe",
      "shelter", "shelve", "shoulder", "skewer", "snare", "spindle", "spit", "spool",
      "stable", "string", "tin", "trap", "tree", "warehouse"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 10. -/
def chapter10 : List VerbClass := [
  { number := "10.1", page := 122,
    title := "Remove Verbs",
    members :=
      ["abstract", "cull", "delete", "discharge", "disengage", "disgorge", "dislodge", "dismiss",
      "draw", "eject", "eliminate", "eradicate", "evict", "excise", "excommunicate", "expel",
      "extirpate", "extract", "extrude", "lop", "omit", "ostracize", "oust", "partition",
      "pry", "reap", "remove", "separate", "sever", "shoo", "subtract", "uproot", "winkle",
      "withdraw", "wrench"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "10.2", page := 123,
    title := "Banish Verbs",
    members :=
      ["banish", "deport", "evacuate", "expel", "extradite", "recall", "remove"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "10.3", page := 124,
    title := "Clear Verbs",
    members :=
      ["clean", "clear", "drain", "empty"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3, 2], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 3, 5], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, (.all ["clean"]), none⟩,
      ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedAdjective, .acceptable, .some, none⟩,
      ⟨.alternation [5, 3], .acceptable, .all, none⟩] },
  { number := "10.4.1", page := 125,
    title := "Manner Subclass",
    members :=
      ["bail", "buff", "dab", "distill", "dust", "erase", "expunge", "flush", "leach", "lick",
      "pluck", "polish", "prune", "purge", "rinse", "rub", "scour", "scrape", "scratch",
      "scrub", "shave", "skim", "smooth", "soak", "squeeze", "strain", "strip", "suck",
      "suction", "swab", "sweep", "trim", "wash", "wear", "weed", "whisk", "winnow", "wipe",
      "wring"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 2, 1], .acceptable, .some, none⟩,
      ⟨.property .unspecifiedObjectPlusLocativePP, .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "10.4.2", page := 127,
    title := "Instrument Subclass",
    members :=
      ["brush", "comb", "file", "filter", "hoover", "hose", "iron", "mop", "plow", "rake",
      "sandpaper", "shear", "shovel", "siphon", "sponge", "towel", "vacuum"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 2, 1], .acceptable, .some, none⟩,
      ⟨.property .unspecifiedObjectPlusLocativePP, .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "10.5", page := 128,
    title := "Verbs of Possessional Deprivation: Steal Verbs",
    members :=
      ["abduct", "cadge", "capture", "confiscate", "cop", "emancipate", "embezzle", "exorcise",
      "extort", "extract", "filch", "flog", "grab", "impound", "kidnap", "liberate", "lift",
      "nab", "pilfer", "pinch", "pirate", "plagiarize", "purloin", "reclaim", "recover",
      "redeem", "regain", "repossess", "rescue", "retrieve", "rustle", "seize", "smuggle",
      "snatch", "sneak", "sponge", "steal", "swipe", "take", "thieve", "wangle", "weasel",
      "winkle", "withdraw", "wrest"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "10.6", page := 129,
    title := "Verbs of Possessional Deprivation: Cheat Verbs",
    members :=
      ["absolve", "acquit", "balk", "bereave", "bilk", "bleed", "break", "burgle", "cheat",
      "cleanse", "con", "cull", "cure", "defraud", "denude", "deplete", "depopulate",
      "deprive", "despoil", "disabuse", "disarm", "disencumber", "dispossess", "divest",
      "drain", "ease", "exonerate", "fleece", "free", "gull", "milk", "mulct", "pardon",
      "plunder", "purge", "purify", "ransack", "relieve", "render", "rid", "rifle", "rob",
      "sap", "strip", "swindle", "unburden", "void", "wean"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.property .ofAlternatesWithOut, .acceptable, .few, none⟩] },
  { number := "10.7", page := 130,
    title := "Pit Verbs",
    members :=
      ["bark", "beard", "bone", "burl", "core", "gill", "gut", "head", "hull", "husk", "lint",
      "louse", "milk", "peel", "pinion", "pip", "pit", "pith", "pod", "poll", "pulp", "rind",
      "scale", "scalp", "seed", "shell", "shuck", "skin", "snail", "stalk", "stem", "stone",
      "string", "tail", "tassel", "top", "vein", "weed", "wind", "worm", "zest"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "10.8", page := 130,
    title := "Debone Verbs",
    members :=
      ["deaccent", "debark", "debone", "debowel", "debug", "debur", "declaw", "defang", "defat",
      "defeather", "deflea", "deflesh", "defoam", "defog", "deforest", "defrost", "defuzz",
      "degas", "degerm", "deglaze", "degrease", "degrit", "degum", "degut", "dehair",
      "dehead", "dehorn", "dehull", "dehusk", "deice", "deink", "delint", "delouse",
      "deluster", "demast", "derat", "derib", "derind", "desalt", "descale", "desex",
      "desprout", "destarch", "destress", "detassel", "detusk", "devein", "dewater", "dewax",
      "deworm"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "10.9", page := 131,
    title := "Mine Verbs",
    members :=
      ["mine", "quarry"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 2], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 11. -/
def chapter11 : List VerbClass := [
  { number := "11.1", page := 132,
    title := "Send Verbs",
    members :=
      ["airmail", "convey", "deliver", "dispatch", "express", "FedEx", "forward", "hand", "mail",
      "pass", "port", "post", "return", "send", "shift", "ship", "shunt", "slip", "smuggle",
      "sneak", "transfer", "transport", "UPS"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .some, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 7], .ungrammatical, .all, none⟩] },
  { number := "11.2", page := 133,
    title := "Slide Verbs",
    members :=
      ["bounce", "float", "move", "roll", "slide"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, (.all ["move"]), none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.property .coreferentialInterpretationVaries, .acceptable, .all, none⟩] },
  { number := "11.3", page := 134,
    title := "Bring and Take",
    members :=
      ["bring", "take"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 7], .acceptable, .all, none⟩] },
  { number := "11.4", page := 135,
    title := "Carry Verbs",
    members :=
      ["carry", "drag", "haul", "heave", "heft", "hoist", "kick", "lug", "pull", "push", "schlep",
      "shove", "tote", "tow", "tug"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.property .coreferentialInterpretationVaries, .acceptable, .all, none⟩] },
  { number := "11.5", page := 136,
    title := "Drive Verbs",
    members :=
      ["barge", "bus", "cart", "drive", "ferry", "fly", "row", "shuttle", "truck", "wheel",
      "wire"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .marginal, .some, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 7], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 12. -/
def chapter12 : List VerbClass := [
  { number := "12", page := 137,
    title := "Verbs of Exerting Force: Push/Pull Verbs",
    members :=
      ["draw", "heave", "jerk", "press", "pull", "push", "shove", "thrust", "tug", "yank"],
    doubtful := ["draw", "thrust"],
    properties :=
      [⟨.alternation [1, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 2, 7], .acceptable, .some, none⟩,
      ⟨.alternation [7, 7], .acceptable, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] }]

/-- The classes of chapter 13. -/
def chapter13 : List VerbClass := [
  { number := "13.1", page := 138,
    title := "Give Verbs",
    members :=
      ["feed", "give", "lease", "lend", "loan", "pass", "pay", "peddle", "refund", "render", "rent",
      "repay", "sell", "serve", "trade"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "13.2", page := 138,
    title := "Contribute Verbs",
    members :=
      ["administer", "contribute", "disburse", "distribute", "donate", "extend", "forfeit",
      "proffer", "refer", "reimburse", "relinquish", "remit", "restore", "return",
      "sacrifice", "submit", "surrender", "transfer"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "13.3", page := 139,
    title := "Verbs of Future Having",
    members :=
      ["advance", "allocate", "allot", "assign", "award", "bequeath", "cede", "concede", "extend",
      "grant", "guarantee", "issue", "leave", "offer", "owe", "promise", "vote", "will",
      "yield"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "13.4.1", page := 140,
    title := "Verbs of Fulfilling",
    members :=
      ["credit", "entrust", "furnish", "issue", "leave", "present", "provide", "serve", "supply",
      "trust"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 6], .acceptable, .all, none⟩] },
  { number := "13.4.2", page := 141,
    title := "Equip Verbs",
    members :=
      ["arm", "burden", "charge", "compensate", "equip", "invest", "ply", "regale", "reward",
      "saddle"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩] },
  { number := "13.5.1", page := 141,
    title := "Get Verbs",
    members :=
      ["book", "buy", "call", "cash", "catch", "charter", "choose", "earn", "fetch", "find", "gain",
      "gather", "get", "hire", "keep", "lease", "leave", "order", "phone", "pick", "pluck",
      "procure", "pull", "reach", "rent", "reserve", "save", "secure", "shoot", "slaughter",
      "steal", "vote", "win"],
    doubtful := ["choose"],
    properties :=
      [⟨.property .fromPhrase, .acceptable, .most, none⟩,
      ⟨.alternation [2, 2], .acceptable, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 9], .acceptable, .some, none⟩] },
  { number := "13.5.2", page := 142,
    title := "Obtain Verbs",
    members :=
      ["accept", "accumulate", "acquire", "appropriate", "borrow", "cadge", "collect", "exact",
      "grab", "inherit", "obtain", "purchase", "receive", "recover", "regain", "retrieve",
      "seize", "select", "snatch"],
    doubtful := ["cadge"],
    properties :=
      [⟨.property .fromPhrase, .acceptable, .most, none⟩,
      ⟨.alternation [2, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 9], .acceptable, .few, none⟩] },
  { number := "13.6", page := 143,
    title := "Verbs of Exchange",
    members :=
      ["barter", "change", "exchange", "substitute", "swap", "trade"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 2], .ungrammatical, .all, none⟩] },
  { number := "13.7", page := 144,
    title := "Berry Verbs",
    members :=
      ["antique", "berry", "birdnest", "blackberry", "clam", "crab", "fish", "fowl", "grouse",
      "hay", "log", "mushroom", "nest", "nut", "oyster", "pearl", "prawn", "rabbit", "seal",
      "shark", "shrimp", "snail", "snipe", "sponge", "whale", "whelk"],
    doubtful := [],
    properties :=
      [] }]

/-- The classes of chapter 14. -/
def chapter14 : List VerbClass := [
  { number := "14", page := 144,
    title := "Learn Verbs",
    members :=
      ["acquire", "cram", "glean", "learn", "memorize", "read", "study"],
    doubtful := [],
    properties :=
      [] }]

/-- The classes of chapter 15. -/
def chapter15 : List VerbClass := [
  { number := "15.1", page := 145,
    title := "Hold Verbs",
    members :=
      ["clasp", "clutch", "grasp", "grip", "handle", "hold", "wield"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 12], .acceptable, .some, none⟩] },
  { number := "15.2", page := 145,
    title := "Keep Verbs",
    members :=
      ["hoard", "keep", "leave", "store"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] }]

/-- The classes of chapter 16. -/
def chapter16 : List VerbClass := [
  { number := "16", page := 146,
    title := "Verbs of Concealment",
    members :=
      ["block", "cloister", "conceal", "curtain", "hide", "isolate", "quarantine", "screen",
      "seclude", "sequester", "shelter"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 17. -/
def chapter17 : List VerbClass := [
  { number := "17.1", page := 146,
    title := "Throw Verbs",
    members :=
      ["bash", "bat", "bunt", "cast", "catapult", "chuck", "fire", "flick", "fling", "flip", "hit",
      "hurl", "kick", "knock", "lob", "loft", "nudge", "pass", "pitch", "punt", "shoot",
      "shove", "slam", "slap", "sling", "smash", "tap", "throw", "tip", "toss"],
    doubtful := ["cast", "loft"],
    properties :=
      [⟨.alternation [7, 8], .acceptable, .all, none⟩,
      ⟨.alternation [2, 1], .acceptable, .most, none⟩,
      ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "17.2", page := 147,
    title := "Pelt Verbs",
    members :=
      ["bombard", "buffet", "pelt", "shower", "stone"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 18. -/
def chapter18 : List VerbClass := [
  { number := "18.1", page := 148,
    title := "Hit Verbs",
    members :=
      ["bang", "bash", "batter", "beat", "bump", "butt", "dash", "drum", "hammer", "hit", "kick",
      "knock", "lash", "pound", "rap", "slap", "smack", "smash", "strike", "tamp", "tap",
      "thump", "thwack", "whack"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 8], .acceptable, .all, none⟩,
      ⟨.alternation [2, 9], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .acceptable, .all, none⟩,
      ⟨.alternation [2, 12], .acceptable, .all, none⟩,
      ⟨.alternation [2, 5, 2], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [7, 6, 1], .acceptable, .some, none⟩,
      ⟨.alternation [7, 6, 2], .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "18.2", page := 150,
    title := "Swat Verbs",
    members :=
      ["bite", "claw", "paw", "peck", "punch", "scratch", "shoot", "slug", "stab", "swat",
      "swipe"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 9], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .acceptable, .all, none⟩,
      ⟨.alternation [2, 12], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "18.3", page := 151,
    title := "Spank Verbs",
    members :=
      ["belt", "birch", "bludgeon", "bonk", "brain", "cane", "clobber", "club", "conk", "cosh",
      "cudgel", "cuff", "flog", "knife", "paddle", "paddywhack", "pummel", "sock", "spank",
      "strap", "thrash", "truncheon", "wallop", "whip", "whisk"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 9], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 12], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .ingNominal, .acceptable, .most, none⟩] },
  { number := "18.4", page := 153,
    title := "Non-Agentive Verbs of Impact by Contact",
    members :=
      ["bang", "brush", "bump", "crash", "hit", "knock", "ram", "slam", "smash", "thud"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 5], .acceptable, .some, some "intransitive"⟩] }]

/-- The classes of chapter 19. -/
def chapter19 : List VerbClass := [
  { number := "19", page := 154,
    title := "Poke Verbs",
    members :=
      ["dig", "jab", "pierce", "poke", "prick", "stick"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 9], .acceptable, .all, none⟩,
      ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .acceptable, .some, none⟩,
      ⟨.alternation [2, 12], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] }]

/-- The classes of chapter 20. -/
def chapter20 : List VerbClass := [
  { number := "20", page := 155,
    title := "Verbs of Contact: Touch Verbs",
    members :=
      ["caress", "graze", "kiss", "lick", "nudge", "pat", "peck", "pinch", "prod", "sting",
      "stroke", "tickle", "touch"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 9], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 12], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 6, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 6, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] }]

/-- The classes of chapter 21. -/
def chapter21 : List VerbClass := [
  { number := "21.1", page := 156,
    title := "Cut Verbs",
    members :=
      ["chip", "clip", "cut", "hack", "hew", "saw", "scrape", "scratch", "slash", "snip"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 3], .acceptable, .all, none⟩,
      ⟨.alternation [2, 12], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 2, 6, 2], .acceptable, .some, none⟩,
      ⟨.alternation [7, 6, 1], .acceptable, .some, none⟩,
      ⟨.alternation [7, 6, 2], .acceptable, .some, none⟩,
      ⟨.property .pathPhrase, .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩] },
  { number := "21.2", page := 157,
    title := "Carve Verbs",
    members :=
      ["bore", "bruise", "carve", "chip", "chop", "crop", "crush", "cube", "dent", "dice", "drill",
      "file", "fillet", "gash", "gouge", "grate", "grind", "mangle", "mash", "mince", "mow",
      "nick", "notch", "perforate", "prune", "pulverize", "punch", "shred", "slice", "slit",
      "spear", "squash", "squish"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 12], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 2, 6, 2], .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] }]

/-- The classes of chapter 22. -/
def chapter22 : List VerbClass := [
  { number := "22.1", page := 159,
    title := "Mix Verbs",
    members :=
      ["add", "blend", "combine", "commingle", "concatenate", "connect", "cream", "fuse", "join",
      "link", "merge", "mingle", "mix", "network", "pool"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 1], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 4], .acceptable, .most, some "intransitive"⟩,
      ⟨.alternation [2, 5, 2], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 5], .acceptable, .most, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩] },
  { number := "22.2", page := 160,
    title := "Amalgamate Verbs",
    members :=
      ["affiliate", "alternate", "amalgamate", "associate", "coalesce", "coincide", "compare",
      "confederate", "confuse", "conjoin", "consolidate", "contrast", "correlate",
      "criss-cross", "engage", "entangle", "entwine", "harmonize", "incorporate", "integrate",
      "interchange", "interconnect", "interlace", "interlink", "interlock", "intermingle",
      "interrelate", "intersperse", "intertwine", "interweave", "introduce", "marry", "mate",
      "muddle", "oppose", "pair", "rhyme", "team", "total", "unify", "unite", "wed"],
    doubtful := ["pair", "team"],
    properties :=
      [⟨.alternation [2, 5, 1], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 2], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 5], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩] },
  { number := "22.3", page := 161,
    title := "Shake Verbs",
    members :=
      ["append", "attach", "band", "baste", "beat", "bind", "bond", "bundle", "cluster", "collate",
      "collect", "fasten", "fuse", "gather", "glom", "graft", "group", "herd", "jumble",
      "lump", "mass", "moor", "package", "pair", "roll", "scramble", "sew", "shake",
      "shuffle", "splice", "stick", "stir", "swirl", "weld", "whip", "whisk"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 2], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .most, some "with a few exceptions"⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩] },
  { number := "22.4", page := 162,
    title := "Tape Verbs",
    members :=
      ["anchor", "band", "belt", "bolt", "bracket", "buckle", "button", "cement", "chain", "clamp",
      "clasp", "clip", "epoxy", "fetter", "glue", "gum", "handcuff", "harness", "hinge",
      "hitch", "hook", "knot", "lace", "lash", "lasso", "latch", "leash", "link", "lock",
      "loop", "manacle", "moor", "muzzle", "nail", "padlock", "paste", "peg", "pin",
      "plaster", "rivet", "rope", "screw", "seal", "shackle", "skewer", "solder", "staple",
      "stitch", "strap", "string", "tack", "tape", "tether", "thumbtack", "tie", "trammel",
      "wire", "yoke", "zip"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 2], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.alternation [7, 2], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "22.5", page := 164,
    title := "Cling Verbs",
    members :=
      ["adhere", "cleave", "cling"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 5], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 23. -/
def chapter23 : List VerbClass := [
  { number := "23.1", page := 165,
    title := "Separate Verbs",
    members :=
      ["decouple", "differentiate", "disconnect", "disentangle", "dissociate", "distinguish",
      "divide", "divorce", "part", "segregate", "separate", "sever"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 1], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 3], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 6], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 3], .ungrammatical, .all, none⟩] },
  { number := "23.2", page := 166,
    title := "Split Verbs",
    members :=
      ["blow", "break", "cut", "draw", "hack", "hew", "kick", "knock", "pry", "pull", "push", "rip",
      "roll", "saw", "shove", "slip", "split", "tear", "tug", "yank"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 3], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 6], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩] },
  { number := "23.3", page := 167,
    title := "Disassemble Verbs",
    members :=
      ["detach", "disassemble", "disconnect", "partition", "sift", "sunder", "unbolt", "unbuckle",
      "unbutton", "unchain", "unclamp", "unclasp", "unclip", "unfasten", "unglue", "unhinge",
      "unhitch", "unhook", "unlace", "unlatch", "unleash", "unlock", "unpeg", "unpin",
      "unscrew", "unshackle", "unstaple", "unstitch", "untie", "unzip"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 5, 3], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .most, some "a few exceptions"⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩] },
  { number := "23.4", page := 167,
    title := "Differ Verbs",
    members :=
      ["differ", "diverge"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 6], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 24. -/
def chapter24 : List VerbClass := [
  { number := "24", page := 168,
    title := "Verbs of Coloring",
    members :=
      ["color", "distemper", "dye", "enamel", "glaze", "japan", "lacquer", "paint", "shellac",
      "spraypaint", "stain", "tint", "varnish"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.alternation [7, 2], .acceptable, .all, none⟩] }]

/-- The classes of chapter 25. -/
def chapter25 : List VerbClass := [
  { number := "25.1", page := 169,
    title := "Verbs of Image Impression",
    members :=
      ["appliqué", "emboss", "embroider", "engrave", "etch", "imprint", "incise", "inscribe",
      "mark", "paint", "set", "sign", "stamp", "tattoo"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 7], .acceptable, .all, none⟩,
      ⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
      ⟨.property .processNominal, .acceptable, .all, none⟩,
      ⟨.property .resultNominal, .acceptable, .all, none⟩] },
  { number := "25.2", page := 170,
    title := "Scribble Verbs",
    members :=
      ["carve", "chalk", "charcoal", "copy", "crayon", "doodle", "draw", "forge", "ink", "paint",
      "pencil", "plot", "print", "scratch", "scrawl", "scribble", "sketch", "spraypaint",
      "stencil", "trace", "type", "write"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 7], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 2, 1], .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "25.3", page := 171,
    title := "Illustrate Verbs",
    members :=
      ["address", "adorn", "autograph", "brand", "date", "decorate", "embellish", "endorse",
      "illuminate", "illustrate", "initial", "label", "letter", "monogram", "ornament",
      "tag"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 7], .ungrammatical, .all, none⟩,
      ⟨.property .processNominal, .acceptable, .some, none⟩,
      ⟨.property .resultNominal, .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "25.4", page := 171,
    title := "Transcribe Verbs",
    members :=
      ["copy", "film", "forge", "microfilm", "photocopy", "photograph", "record", "tape",
      "televise", "transcribe", "type"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 7], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] }]

/-- The classes of chapter 26. -/
def chapter26 : List VerbClass := [
  { number := "26.1", page := 173,
    title := "Build Verbs",
    members :=
      ["arrange", "assemble", "bake", "blow", "build", "carve", "cast", "chisel", "churn",
      "compile", "cook", "crochet", "cut", "develop", "embroider", "fashion", "fold", "forge",
      "grind", "grow", "hack", "hammer", "hatch", "knit", "make", "mold", "pound", "roll",
      "sculpt", "sew", "shape", "spin", "stitch", "weave", "whittle"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 4, 1], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 4, 3], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 2], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 8], .acceptable, .some, none⟩,
      ⟨.alternation [3, 9], .acceptable, .few, none⟩] },
  { number := "26.2", page := 174,
    title := "Grow Verbs",
    members :=
      ["develop", "evolve", "grow", "hatch", "mature"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 4, 2], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [2, 4, 4], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩] },
  { number := "26.3", page := 175,
    title := "Verbs of Preparing",
    members :=
      ["bake", "blend", "boil", "brew", "clean", "clear", "cook", "fix", "fry", "grill", "hardboil",
      "iron", "light", "mix", "poach", "pour", "prepare", "roast", "roll", "run", "scramble",
      "set", "softboil", "toast", "toss", "wash"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 2], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "26.4", page := 175,
    title := "Create Verbs",
    members :=
      ["coin", "compose", "compute", "concoct", "construct", "create", "derive", "design", "dig",
      "fabricate", "form", "invent", "manufacture", "mint", "model", "organize", "produce",
      "recreate", "style", "synthesize"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 2], .ungrammatical, .most, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 8], .ungrammatical, .all, none⟩] },
  { number := "26.5", page := 176,
    title := "Knead Verbs",
    members :=
      ["beat", "bend", "coil", "collect", "compress", "fold", "freeze", "knead", "melt", "shake",
      "squash", "squeeze", "squish", "twirl", "twist", "wad", "whip", "wind", "work"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .some, none⟩,
      ⟨.alternation [3, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 4, 3], .ungrammatical, .all, some "transitive"⟩] },
  { number := "26.6", page := 177,
    title := "Turn Verbs",
    members :=
      ["alter", "change", "convert", "metamorphose", "transform", "transmute", "turn"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 4, 3], .acceptable, .all, some "transitive"⟩,
      ⟨.alternation [2, 4, 4], .acceptable, .most, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
      ⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 4, 2], .ungrammatical, .all, some "intransitive"⟩] },
  { number := "26.7", page := 178,
    title := "Performance Verbs",
    members :=
      ["chant", "choreograph", "compose", "dance", "direct", "draw", "hum", "intone", "paint",
      "perform", "play", "produce", "recite", "silkscreen", "sing", "spin", "take", "whistle",
      "write"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .some, none⟩,
      ⟨.alternation [2, 2], .acceptable, .some, none⟩,
      ⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 27. -/
def chapter27 : List VerbClass := [
  { number := "27", page := 179,
    title := "Engender Verbs",
    members :=
      ["beget", "cause", "create", "engender", "generate", "shape", "spawn"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 28. -/
def chapter28 : List VerbClass := [
  { number := "28", page := 180,
    title := "Calve Verbs",
    members :=
      ["calve", "cub", "fawn", "foal", "kitten", "lamb", "litter", "pup", "spawn", "whelp"],
    doubtful := [],
    properties :=
      [] }]

/-- The classes of chapter 29. -/
def chapter29 : List VerbClass := [
  { number := "29.1", page := 181,
    title := "Appoint Verbs",
    members :=
      ["acknowledge", "adopt", "appoint", "consider", "crown", "deem", "designate", "elect",
      "esteem", "imagine", "mark", "nominate", "ordain", "proclaim", "rate", "reckon",
      "report", "want"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 14], .acceptable, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.property .infinitivalCopularClause, .acceptable, .some, none⟩] },
  { number := "29.2", page := 181,
    title := "Characterize Verbs",
    members :=
      ["accept", "address", "appreciate", "bill", "cast", "certify", "characterize", "choose",
      "cite", "class", "classify", "confirm", "count", "define", "describe", "diagnose",
      "disguise", "employ", "engage", "enlist", "enroll", "enter", "envisage", "establish",
      "esteem", "hail", "herald", "hire", "honor", "identify", "imagine", "incorporate",
      "induct", "intend", "lampoon", "offer", "oppose", "paint", "portray", "praise",
      "qualify", "rank", "recollect", "recommend", "regard", "reinstate", "reject",
      "remember", "represent", "repudiate", "reveal", "salute", "see", "select", "stigmatize",
      "take", "train", "treat", "use", "value", "view", "visualize"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
      ⟨.property .infinitivalCopularClause, .acceptable, .few, none⟩] },
  { number := "29.3", page := 182,
    title := "Dub Verbs",
    members :=
      ["anoint", "baptize", "brand", "call", "christen", "consecrate", "crown", "decree", "dub",
      "label", "make", "name", "nickname", "pronounce", "rule", "stamp", "style", "term",
      "vote"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.property .infinitivalCopularClause, .ungrammatical, .all, none⟩] },
  { number := "29.4", page := 182,
    title := "Declare Verbs",
    members :=
      ["adjudge", "adjudicate", "assume", "avow", "believe", "confess", "declare", "fancy", "find",
      "judge", "presume", "profess", "prove", "suppose", "think", "warrant"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.property .infinitivalCopularClause, .acceptable, .all, none⟩] },
  { number := "29.5", page := 183,
    title := "Conjecture Verbs",
    members :=
      ["admit", "allow", "assert", "conjecture", "deny", "discover", "feel", "figure", "grant",
      "guarantee", "guess", "hold", "know", "maintain", "mean", "observe", "recognize",
      "repute", "show", "suspect"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
      ⟨.property .infinitivalCopularClause, .acceptable, .all, none⟩] },
  { number := "29.6", page := 183,
    title := "Masquerade Verbs",
    members :=
      ["act", "behave", "camouflage", "count", "masquerade", "officiate", "qualify", "rank", "rate",
      "serve"],
    doubtful := [],
    properties :=
      [] },
  { number := "29.7", page := 184,
    title := "Orphan Verbs",
    members :=
      ["apprentice", "canonize", "cripple", "cuckold", "knight", "martyr", "orphan", "outlaw",
      "pauper", "recruit", "widow"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 1], .acceptable, .all, none⟩] },
  { number := "29.8", page := 184,
    title := "Captain Verbs",
    members :=
      ["boss", "bully", "butcher", "butler", "caddy", "captain", "champion", "chaperone",
      "chauffeur", "clerk", "coach", "cox", "crew", "doctor", "emcee", "escort", "guard",
      "host", "model", "mother", "nurse", "partner", "pilot", "pioneer", "police", "referee",
      "shepherd", "skipper", "sponsor", "star", "tailor", "tutor", "umpire", "understudy",
      "usher", "valet", "volunteer", "witness"],
    doubtful := [],
    properties :=
      [] }]

/-- The classes of chapter 30. -/
def chapter30 : List VerbClass := [
  { number := "30.1", page := 185,
    title := "See Verbs",
    members :=
      ["detect", "discern", "feel", "hear", "notice", "see", "sense", "smell", "taste"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 13, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 13, 2], .acceptable, .all, none⟩] },
  { number := "30.2", page := 186,
    title := "Sight Verbs",
    members :=
      ["descry", "discover", "espy", "examine", "eye", "glimpse", "inspect", "investigate", "note",
      "observe", "overhear", "perceive", "recognize", "regard", "savor", "scan", "scent",
      "scrutinize", "sight", "spot", "spy", "study", "survey", "view", "watch", "witness"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩] },
  { number := "30.3", page := 187,
    title := "Peer Verbs",
    members :=
      ["check", "gape", "gawk", "gaze", "glance", "glare", "goggle", "leer", "listen", "look",
      "ogle", "peek", "peep", "peer", "sniff", "snoop", "squint", "stare"],
    doubtful := [],
    properties :=
      [] },
  { number := "30.4", page := 187,
    title := "Stimulus Subject Perception Verbs",
    members :=
      ["feel", "look", "smell", "sound", "taste"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 1], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 31. -/
def chapter31 : List VerbClass := [
  { number := "31.1", page := 189,
    title := "Amuse Verbs",
    members :=
      ["abash", "affect", "afflict", "affront", "aggravate", "agitate", "agonize", "alarm",
      "alienate", "amaze", "amuse", "anger", "annoy", "antagonize", "appall", "appease",
      "arouse", "asperate", "assuage", "astonish", "astound", "awe", "baffle", "beguile",
      "bewilder", "bewitch", "boggle", "bore", "bother", "bug", "calm", "captivate",
      "chagrin", "charm", "cheer", "chill", "comfort", "concern", "confound", "confuse",
      "console", "content", "convince", "cow", "crush", "cut", "daunt", "daze", "dazzle",
      "deject", "delight", "demolish", "demoralize", "depress", "devastate", "disappoint",
      "disarm", "discombobulate", "discomfit", "discompose", "disconcert", "discourage",
      "disgrace", "disgruntle", "disgust", "dishearten", "disillusion", "dismay", "dispirit",
      "disquiet", "dissatisfy", "distract", "distress", "disturb", "dumbfound", "elate",
      "elecdisplease", "embarrass", "embolden", "enchant", "encourage", "engage", "engross",
      "enlighten", "enrage", "enrapture", "entertain", "enthrall", "enthuse", "entice",
      "entrance", "excite", "exenliven", "exhaust", "exhilarate", "fascinate", "faze",
      "flabbergast", "flatter", "floor", "fluster", "frighten", "frustrate", "gall",
      "galvanize", "gladden", "gratify", "grieve", "harass", "haunt", "hearten", "horrify",
      "humble", "humiliate", "hurt", "hypnotize", "impress", "incense", "infuriate",
      "inspire", "insult", "interest", "intimidate", "intoxicate", "intrigue", "invigorate",
      "irk", "irritate", "ize", "jar", "jollify", "jolt", "lull", "madden", "mesmerize",
      "miff", "mollify", "mortify", "move", "muddle", "mystify", "nauseate", "nettle", "numb",
      "obsess", "offend", "outrage", "overawe", "overwhelm", "pacify", "pain", "peeve",
      "perplex", "perturb", "pique", "placate", "plague", "please", "preoccupy", "puzzle",
      "rankle", "reassure", "refresh", "relax", "relieve", "repel", "repulse",
      "revitalprovoke", "revolt", "rile", "ruffle", "sadden", "satisfy", "scandalize",
      "scare", "shake", "shame", "shock", "sicken", "sober", "solace", "soothe", "spellbind",
      "spook", "stagger", "startle", "stimulate", "sting", "stir", "strike", "stump", "stun",
      "stupefy", "surprise", "tantalize", "tease", "tempt", "terrify", "terrorize",
      "threaten", "thrill", "throw", "tickle", "tire", "titillate", "torment", "touch",
      "transport", "trify", "trouble", "try", "unnerve", "unsettle", "uplift", "upset", "vex",
      "weary", "worry", "wound", "wow"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .most, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .most, none⟩,
      ⟨.alternation [1, 2, 5], .acceptable, .all, none⟩,
      ⟨.alternation [2, 13, 4], .acceptable, .all, some "transitive"⟩,
      ⟨.property .extraposition, .acceptable, .all, none⟩,
      ⟨.property .passivePrepositionChoice, .acceptable, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property (.derivedNominal .passive), .acceptable, .all, none⟩,
      ⟨.property .erNominal, .acceptable, .some, none⟩,
      ⟨.property .ableAdjective, .acceptable, .some, none⟩] },
  { number := "31.2", page := 191,
    title := "Admire Verbs",
    members :=
      ["abhor", "admire", "adore", "appreciate", "cherish", "deplore", "despise", "detest",
      "disdain", "dislike", "distrust", "dread", "enjoy", "envy", "esteem", "exalt",
      "execrate", "fancy", "favor", "fear", "hate", "idolize", "lament", "like", "loathe",
      "love", "miss", "mourn", "pity", "prize", "regret", "relish", "resent", "respect",
      "revere", "rue", "savor", "stand", "support", "tolerate", "treasure", "trust", "value",
      "venerate", "worship"],
    doubtful := ["rue"],
    properties :=
      [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 13, 2], .acceptable, .all, none⟩,
      ⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
      ⟨.property (.sententialComplement .unspecified), .acceptable, .some, none⟩,
      ⟨.property .extraposition, .acceptable, .some, none⟩,
      ⟨.property (.derivedNominal .active), .acceptable, .all, none⟩,
      ⟨.property .ableAdjective, .acceptable, .all, none⟩,
      ⟨.property .erNominal, .acceptable, .all, none⟩] },
  { number := "31.3", page := 192,
    title := "Marvel Verbs",
    members :=
      ["ache", "anger", "anguish", "approve", "bask", "beware", "bleed", "bother", "care", "cheer",
      "cringe", "cry", "delight", "despair", "disapprove", "enthuse", "exult", "fear", "feel",
      "fret", "fume", "gladden", "gloat", "glory", "grieve", "groove", "gush", "hunger",
      "hurt", "luxuriate", "madden", "marvel", "mind", "moon", "mope", "mourn", "obsess",
      "puzzle", "rage", "rave", "react", "rejoice", "revel", "rhapsodize", "sadden",
      "salivate", "seethe", "sicken", "sorrow", "suffer", "swoon", "thrill", "tire", "wallow",
      "weary", "weep", "wonder", "worry"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 1], .acceptable, .some, none⟩] },
  { number := "31.4", page := 193,
    title := "Appeal Verbs",
    members :=
      ["appeal", "grate", "jar", "matter", "niggle"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 1], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 32. -/
def chapter32 : List VerbClass := [
  { number := "32.1", page := 194,
    title := "Want Verbs",
    members :=
      ["covet", "crave", "desire", "fancy", "need", "want"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 13, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 1], .marginal, .all, none⟩] },
  { number := "32.2", page := 194,
    title := "Long Verbs",
    members :=
      ["ache", "crave", "dangle", "fall", "hanker", "hope", "hunger", "itch", "long", "lust",
      "pine", "pray", "thirst", "wish", "yearn"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 1], .marginal, .all, none⟩] }]

/-- The classes of chapter 33. -/
def chapter33 : List VerbClass := [
  { number := "33", page := 195,
    title := "Judgment Verbs",
    members :=
      ["abuse", "acclaim", "applaud", "backbite", "bless", "calumniate", "castigate", "celebrate",
      "censure", "chasten", "chastise", "chide", "commend", "compensate", "compliment",
      "condemn", "congratulate", "criticize", "decry", "defame", "denigrate", "denounce",
      "deprecate", "deride", "disparage", "eulogize", "excuse", "extol", "fault",
      "felicitate", "fine", "forgive", "greet", "hail", "honor", "impeach", "insult",
      "lambaste", "laud", "malign", "mock", "pardon", "penalize", "persecute", "praise",
      "prosecute", "punish", "rebuke", "recompense", "remunerate", "repay", "reprimand",
      "reproach", "reprove", "revile", "reward", "ridicule", "salute", "scold", "scorn",
      "shame", "snub", "thank", "toast", "upbraid", "victimize", "vilify", "welcome"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 13, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 14], .acceptable, .some, none⟩,
      ⟨.property .processNominal, .acceptable, .some, none⟩] }]

/-- The classes of chapter 34. -/
def chapter34 : List VerbClass := [
  { number := "34", page := 196,
    title := "Verbs of Assessment",
    members :=
      ["analyze", "assess", "audit", "evaluate", "review", "scrutinize", "study"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
      ⟨.alternation [2, 13, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 35. -/
def chapter35 : List VerbClass := [
  { number := "35.1", page := 197,
    title := "Hunt Verbs",
    members :=
      ["dig", "feel", "fish", "hunt", "mine", "poach", "scrounge"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 1], .acceptable, .all, none⟩] },
  { number := "35.2", page := 198,
    title := "Search Verbs",
    members :=
      ["advertise", "check", "comb", "dive", "drag", "dredge", "excavate", "patrol", "plumb",
      "probe", "prospect", "prowl", "quarry", "rake", "rifle", "scavenge", "scour", "scout",
      "search", "shop", "sift", "trawl", "troll", "watch"],
    doubtful := [],
    properties :=
      [] },
  { number := "35.3", page := 198,
    title := "Stalk Verbs",
    members :=
      ["smell", "stalk", "taste", "track"],
    doubtful := [],
    properties :=
      [] },
  { number := "35.4", page := 198,
    title := "Investigate Verbs",
    members :=
      ["canvass", "examine", "explore", "frisk", "inspect", "investigate", "observe", "quiz",
      "raid", "ransack", "riffle", "scan", "scrutinize", "survey", "tap"],
    doubtful := [],
    properties :=
      [] },
  { number := "35.5", page := 199,
    title := "Rummage Verbs",
    members :=
      ["bore", "burrow", "delve", "forage", "fumble", "grope", "leaf", "listen", "look", "page",
      "paw", "poke", "rifle", "root", "rummage", "scrabble", "scratch", "snoop", "thumb",
      "tunnel"],
    doubtful := [],
    properties :=
      [] },
  { number := "35.6", page := 199,
    title := "Ferret Verbs",
    members :=
      ["ferret", "nose", "seek", "tease"],
    doubtful := [],
    properties :=
      [] }]

/-- The classes of chapter 36. -/
def chapter36 : List VerbClass := [
  { number := "36.1", page := 200,
    title := "Correspond Verbs",
    members :=
      ["agree", "argue", "banter", "bargain", "bicker", "brawl", "clash", "coexist", "collaborate",
      "collide", "combat", "commiserate", "communicate", "compete", "concur", "confabulate",
      "conflict", "consort", "cooperate", "correspond", "dicker", "differ", "disagree",
      "dispute", "dissent", "duel", "elope", "feud", "flirt", "haggle", "hobnob", "jest",
      "joke", "joust", "mate", "mingle", "mix", "neck", "negotiate", "pair", "plot",
      "quarrel", "quibble", "rendezvous", "scuffle", "skirmish", "spar", "spat", "spoon",
      "squabble", "struggle", "tilt", "tussle", "vie", "war", "wrangle", "wrestle"],
    doubtful := [],
    properties :=
      [⟨.property .collectiveNPSubject, .acceptable, .all, none⟩,
      ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [1, 2, 4], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩] },
  { number := "36.2", page := 201,
    title := "Marry Verbs",
    members :=
      ["court", "cuddle", "date", "divorce", "embrace", "hug", "kiss", "marry", "nuzzle", "pass",
      "pet"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [1, 2, 4], .acceptable, .all, none⟩,
      ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩] },
  { number := "36.3", page := 201,
    title := "Meet Verbs",
    members :=
      ["battle", "box", "consult", "debate", "fight", "meet", "play", "visit"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [1, 2, 4], .acceptable, .all, none⟩,
      ⟨.alternation [1, 4, 2], .acceptable, .all, none⟩] }]

/-- The classes of chapter 37. -/
def chapter37 : List VerbClass := [
  { number := "37.1", page := 202,
    title := "Verbs of Transfer of a Message",
    members :=
      ["ask", "cite", "demonstrate", "dictate", "explain", "explicate", "narrate", "pose", "preach",
      "quote", "read", "recite", "relay", "show", "teach", "tell", "write"],
    doubtful := ["pose"],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .most, none⟩] },
  { number := "37.2", page := 203,
    title := "Tell",
    members :=
      ["tell"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .all, none⟩,
      ⟨.property (.sententialComplement (.required .object)), .acceptable, .all, none⟩,
      ⟨.property (.sententialComplement (.required .toPhrase)), .ungrammatical, .all, none⟩,
      ⟨.property (.sententialComplement .absent), .ungrammatical, .all, none⟩,
      ⟨.property .directSpeech, .acceptable, .all, none⟩,
      ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
      ⟨.alternation [5, 1], .acceptable, .all, none⟩,
      ⟨.property .impersonalPassive, .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩] },
  { number := "37.3", page := 204,
    title := "Verbs of Manner of Speaking",
    members :=
      ["babble", "bark", "bawl", "bellow", "bleat", "boom", "bray", "burble", "cackle", "call",
      "carol", "chant", "chatter", "chirp", "cluck", "coo", "croak", "croon", "crow", "cry",
      "drawl", "drone", "gabble", "gibber", "groan", "growl", "grumble", "grunt", "hiss",
      "holler", "hoot", "howl", "jabber", "lilt", "lisp", "moan", "mumble", "murmur",
      "mutter", "purr", "rage", "rasp", "roar", "rumble", "scream", "screech", "shout",
      "shriek", "sing", "snap", "snarl", "snuffle", "splutter", "squall", "squawk", "squeak",
      "squeal", "stammer", "stutter", "thunder", "tisk", "trill", "trumpet", "twitter",
      "wail", "warble", "wheeze", "whimper", "whine", "whisper", "whistle", "whoop", "yammer",
      "yap", "yell", "yelp", "yodel"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.property (.sententialComplement (.optional .toPhrase)), .acceptable, .all, none⟩,
      ⟨.property .directSpeech, .acceptable, .all, none⟩,
      ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
      ⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 3], .acceptable, .all, none⟩,
      ⟨.alternation [7, 1], .marginal, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "37.4", page := 206,
    title := "Verbs of Instrument of Communication",
    members :=
      ["cable", "e-mail", "fax", "modem", "netmail", "phone", "radio", "relay", "satellite",
      "semaphore", "sign", "signal", "telecast", "telegraph", "telephone", "telex", "wire",
      "wireless"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .all, none⟩,
      ⟨.property (.sententialComplement (.optional .object)), .acceptable, .all, none⟩,
      ⟨.property (.sententialComplement (.optional .toPhrase)), .acceptable, .all, none⟩,
      ⟨.property .directSpeech, .acceptable, .all, none⟩,
      ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "37.5", page := 207,
    title := "Talk Verbs",
    members :=
      ["speak", "talk"],
    doubtful := [],
    properties :=
      [⟨.property (.sententialComplement .unspecified), .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 5], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [1, 2, 4], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "37.6", page := 208,
    title := "Chitchat Verbs",
    members :=
      ["argue", "chat", "chatter", "chitchat", "confer", "converse", "gab", "gossip", "rap",
      "schmooze", "yak"],
    doubtful := [],
    properties :=
      [⟨.property (.sententialComplement .unspecified), .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [2, 5, 5], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [1, 2, 4], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩] },
  { number := "37.7", page := 209,
    title := "Say Verbs",
    members :=
      ["announce", "articulate", "blab", "blurt", "claim", "confess", "confide", "convey",
      "declare", "mention", "note", "observe", "proclaim", "propose", "recount", "reiterate",
      "relate", "remark", "repeat", "report", "reveal", "say", "state", "suggest"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .ungrammatical, .all, none⟩] },
  { number := "37.8", page := 210,
    title := "Complain Verbs",
    members :=
      ["boast", "brag", "complain", "crab", "gripe", "grouch", "grouse", "grumble", "kvetch",
      "object"],
    doubtful := [],
    properties :=
      [⟨.property (.sententialComplement (.optional .toPhrase)), .acceptable, .all, none⟩,
      ⟨.property .directSpeech, .acceptable, .all, none⟩,
      ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩] },
  { number := "37.9", page := 211,
    title := "Advise Verbs",
    members :=
      ["admonish", "advise", "alert", "caution", "counsel", "instruct", "warn"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 5], .acceptable, (.all ["alert"]), none⟩,
      ⟨.property (.sententialComplement (.optional .object)), .acceptable, .all, none⟩,
      ⟨.property .directSpeech, .acceptable, .all, none⟩,
      ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .ungrammatical, .most, none⟩] }]

/-- The classes of chapter 38. -/
def chapter38 : List VerbClass := [
  { number := "38", page := 212,
    title := "Verbs of Sounds Made by Animals",
    members :=
      ["baa", "bark", "bay", "bellow", "blat", "bleat", "bray", "buzz", "cackle", "call", "caw",
      "chatter", "cheep", "chirp", "chirrup", "chitter", "cluck", "coo", "croak", "crow",
      "cuckoo", "drone", "gobble", "growl", "grunt", "hee-haw", "hiss", "honk", "hoot",
      "howl", "low", "meow", "mew", "moo", "neigh", "oink", "peep", "pipe", "purr", "quack",
      "roar", "scrawk", "scream", "screech", "sing", "snap", "snarl", "snort", "snuffle",
      "squawk", "squeak", "squeal", "stridulate", "trill", "tweet", "twitter", "wail",
      "warble", "whimper", "whinny", "whistle", "woof", "yap", "yell", "yelp", "yip",
      "yowl"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 3], .acceptable, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩] }]

/-- The classes of chapter 39. -/
def chapter39 : List VerbClass := [
  { number := "39.1", page := 213,
    title := "Eat Verbs",
    members :=
      ["drink", "eat"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .acceptable, .all, none⟩,
      ⟨.alternation [3, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "39.2", page := 214,
    title := "Chew Verbs",
    members :=
      ["chew", "chomp", "crunch", "gnaw", "lick", "munch", "nibble", "peck", "pick", "sip", "slurp",
      "suck"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "39.3", page := 214,
    title := "Gobble Verbs",
    members :=
      ["bolt", "gobble", "gulp", "guzzle", "quaff", "swallow", "swig", "wolf"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "39.4", page := 215,
    title := "Devour Verbs",
    members :=
      ["consume", "devour", "imbibe", "ingest", "swill"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩] },
  { number := "39.5", page := 215,
    title := "Dine Verbs",
    members :=
      ["banquet", "breakfast", "luncheon", "nosh", "picnic", "snack", "sup"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩] },
  { number := "39.6", page := 216,
    title := "Gorge Verbs",
    members :=
      ["exist", "feed", "flourish", "gorge", "live", "prosper", "survive", "thrive"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩] },
  { number := "39.7", page := 216,
    title := "Verbs of Feeding",
    members :=
      ["bottlefeed", "breastfeed", "feed", "forcefeed", "handfeed", "spoonfeed"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .acceptable, .all, none⟩] }]

/-- The classes of chapter 40. -/
def chapter40 : List VerbClass := [
  { number := "40.1.1", page := 217,
    title := "Hiccup Verbs",
    members :=
      ["belch", "blush", "burp", "flush", "hiccup", "pant", "sneeze", "sniffle", "snore", "snuffle",
      "swallow", "wheeze", "yawn"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 1], .marginal, .all, none⟩, ⟨.alternation [7, 5], .marginal, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "40.1.2", page := 218,
    title := "Breathe Verbs",
    members :=
      ["bleed", "breathe", "cough", "cry", "dribble", "drool", "puke", "spit", "sweat", "vomit",
      "weep"],
    doubtful := ["weep"],
    properties :=
      [⟨.alternation [7, 1], .acceptable, .few, none⟩,
      ⟨.property .substanceObject, .acceptable, .most, none⟩,
      ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩] },
  { number := "40.1.3", page := 218,
    title := "Exhale Verbs",
    members :=
      ["exhale", "inhale", "perspire"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩] },
  { number := "40.2", page := 219,
    title := "Verbs of Nonverbal Expression",
    members :=
      ["beam", "cackle", "chortle", "chuckle", "cough", "cry", "frown", "gape", "gasp", "gawk",
      "giggle", "glare", "glower", "goggle", "grimace", "grin", "groan", "growl", "guffaw",
      "howl", "jeer", "laugh", "moan", "pout", "scowl", "sigh", "simper", "smile", "smirk",
      "sneeze", "snicker", "sniff", "snigger", "snivel", "snore", "snort", "sob", "titter",
      "weep", "whistle", "yawn"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 1], .acceptable, .some, none⟩,
      ⟨.alternation [7, 3], .acceptable, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .most, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩] },
  { number := "40.3.1", page := 220,
    title := "Wink Verbs",
    members :=
      ["blink", "clap", "nod", "point", "shrug", "squint", "wag", "wave", "wink"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 2], .acceptable, .all, none⟩,
      ⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 3], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "40.3.2", page := 221,
    title := "Crane Verbs",
    members :=
      ["arch", "bare", "bat", "beat", "blow", "clench", "click", "close", "cock", "crane", "crook",
      "cross", "drum", "flap", "flash", "flex", "flick", "flutter", "fold", "gnash", "grind",
      "hang", "hunch", "kick", "knit", "open", "pucker", "purse", "raise", "roll", "rub",
      "shake", "show", "shuffle", "smack", "snap", "stamp", "stretch", "toss", "turn",
      "twiddle", "twitch", "wag", "waggle", "wiggle", "wring", "wrinkle"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 2], .acceptable, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "40.3.3", page := 222,
    title := "Curtsey Verbs",
    members :=
      ["bob", "bow", "curtsey", "genuflect", "kneel", "salaam", "salute"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 3], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "40.4", page := 222,
    title := "Snooze Verbs",
    members :=
      ["catnap", "doze", "drowse", "nap", "sleep", "slumber", "snooze"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, (.all ["sleep"]), none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "40.5", page := 223,
    title := "Flinch Verbs",
    members :=
      ["balk", "cower", "cringe", "flinch", "recoil", "shrink", "wince"],
    doubtful := ["balk"],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 3], .ungrammatical, .all, none⟩] },
  { number := "40.6", page := 223,
    title := "Verbs of Body-Internal States of Existence",
    members :=
      ["convulse", "cower", "quake", "quiver", "shake", "shiver", "shudder", "tremble",
      "writhe"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "40.7", page := 224,
    title := "Suffocate Verbs",
    members :=
      ["asphyxiate", "choke", "drown", "stifle", "suffocate"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 1], .marginal, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .some, none⟩] },
  { number := "40.8.1", page := 224,
    title := "Pain Verbs",
    members :=
      ["ache", "bother", "hurt", "itch", "pain"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 1], .ungrammatical, .all, none⟩] },
  { number := "40.8.2", page := 225,
    title := "Tingle Verbs",
    members :=
      ["burn", "hum", "pound", "prickle", "pucker", "reel", "smart", "spin", "split", "sting",
      "swim", "throb", "tickle", "tingle"],
    doubtful := [],
    properties :=
      [⟨.alternation [7, 1], .ungrammatical, .all, none⟩] },
  { number := "40.8.3", page := 225,
    title := "Hurt Verbs",
    members :=
      ["bark", "bite", "break", "bruise", "bump", "burn", "chip", "cut", "fracture", "hurt",
      "injure", "nick", "prick", "pull", "rupture", "scald", "scratch", "skin", "split",
      "sprain", "strain", "stub", "turn", "twist"],
    doubtful := [],
    properties :=
      [] },
  { number := "40.8.4", page := 226,
    title := "Verbs of Change of Bodily State",
    members :=
      ["blanch", "faint", "sicken", "swoon"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 41. -/
def chapter41 : List VerbClass := [
  { number := "41.1.1", page := 227,
    title := "Dress Verbs",
    members :=
      ["bathe", "change", "disrobe", "dress", "exercise", "preen", "primp", "shave", "shower",
      "strip", "undress", "wash"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 2, 3], .acceptable, .all, none⟩] },
  { number := "41.1.2", page := 228,
    title := "Groom Verbs",
    members :=
      ["curry", "groom"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩] },
  { number := "41.2.1", page := 228,
    title := "Floss Verbs",
    members :=
      ["brush", "floss", "shave", "wash"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 2, 2], .acceptable, .all, none⟩] },
  { number := "41.2.2", page := 229,
    title := "Braid Verbs",
    members :=
      ["bob", "braid", "brush", "clip", "coldcream", "comb", "condition", "crimp", "crop", "curl",
      "cut", "dye", "file", "henna", "lather", "manicure", "part", "perm", "plait", "pluck",
      "powder", "rinse", "rouge", "set", "shampoo", "soap", "talc", "tease", "towel", "trim",
      "wave"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩] },
  { number := "41.3.1", page := 229,
    title := "Simple Verbs of Dressing",
    members :=
      ["doff", "don", "wear"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩] },
  { number := "41.3.2", page := 229,
    title := "Verbs of Dressing Well",
    members :=
      ["doll", "dress", "spruce", "tog"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 3], .acceptable, .all, none⟩] },
  { number := "41.3.3", page := 230,
    title := "Verbs of Being Dressed",
    members :=
      ["attire", "clad", "garb", "robe"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 42. -/
def chapter42 : List VerbClass := [
  { number := "42.1", page := 230,
    title := "Murder Verbs",
    members :=
      ["assassinate", "butcher", "dispatch", "eliminate", "execute", "immolate", "kill",
      "liquidate", "massacre", "murder", "slaughter", "slay"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 3], .ungrammatical, (.all ["kill"]), none⟩,
      ⟨.alternation [7, 5], .ungrammatical, (.all ["kill"]), none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "42.2", page := 232,
    title := "Poison Verbs",
    members :=
      ["asphyxiate", "crucify", "drown", "electrocute", "garrotte", "hang", "knife", "poison",
      "shoot", "smother", "stab", "strangle", "suffocate"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, (.all ["asphyxiate", "drown", "suffocate"]), none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 43. -/
def chapter43 : List VerbClass := [
  { number := "43.1", page := 233,
    title := "Verbs of Light Emission",
    members :=
      ["beam", "blaze", "blink", "burn", "flame", "flare", "flash", "flicker", "glare", "gleam",
      "glimmer", "glint", "glisten", "glitter", "glow", "incandesce", "scintillate",
      "shimmer", "shine", "sparkle", "twinkle"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3, 4], .acceptable, .all, none⟩,
      ⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.alternation [6, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
      ⟨.property .erNominal, .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "43.2", page := 234,
    title := "Verbs of Sound Emission",
    members :=
      ["babble", "bang", "beat", "beep", "bellow", "blare", "blast", "blat", "boom", "bubble",
      "burble", "burr", "buzz", "chatter", "chime", "chink", "chir", "chitter", "chug",
      "clack", "clang", "clank", "clap", "clash", "clatter", "click", "cling", "clink",
      "clomp", "clump", "clunk", "crack", "crackle", "crash", "creak", "crepitate", "crunch",
      "cry", "ding", "dong", "explode", "fizz", "fizzle", "groan", "growl", "gurgle", "hiss",
      "hoot", "howl", "hum", "jangle", "jingle", "knell", "knock", "lilt", "moan", "murmur",
      "patter", "peal", "ping", "pink", "pipe", "plink", "plonk", "plop", "plunk", "pop",
      "purr", "putter", "rap", "rasp", "rattle", "ring", "roar", "roll", "rumble", "rustle",
      "scream", "screech", "shriek", "shrill", "sing", "sizzle", "snap", "splash", "splutter",
      "sputter", "squawk", "squeak", "squeal", "squelch", "strike", "swish", "swoosh",
      "thrum", "thud", "thump", "thunder", "thunk", "tick", "ting", "tinkle", "toll", "toot",
      "tootle", "trill", "trumpet", "twang", "ululate", "vroom", "wail", "wheeze", "whine",
      "whir", "whish", "whistle", "whoosh", "whump", "zing"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3, 4], .acceptable, .most, none⟩,
      ⟨.alternation [6, 2], .acceptable, .some, none⟩,
      ⟨.alternation [6, 1], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
      ⟨.alternation [7, 8], .acceptable, .all, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
      ⟨.property .erNominal, .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "43.3", page := 236,
    title := "Verbs of Smell Emission",
    members :=
      ["reek", "smell", "stink"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "43.4", page := 237,
    title := "Verbs of Substance Emission",
    members :=
      ["belch", "bleed", "bubble", "dribble", "drip", "drool", "emanate", "exude", "foam", "gush",
      "leak", "ooze", "pour", "puff", "radiate", "seep", "shed", "slop", "spew", "spill",
      "spout", "sprout", "spurt", "squirt", "steam", "stream", "sweat"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 3], .acceptable, .all, none⟩,
      ⟨.alternation [2, 3, 4], .acceptable, .some, none⟩,
      ⟨.alternation [6, 2], .acceptable, .some, none⟩,
      ⟨.alternation [6, 1], .acceptable, .some, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
      ⟨.property .erNominal, .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] }]

/-- The classes of chapter 44. -/
def chapter44 : List VerbClass := [
  { number := "44", page := 239,
    title := "Destroy Verbs",
    members :=
      ["annihilate", "blitz", "decimate", "demolish", "destroy", "devastate", "exterminate",
      "extirpate", "obliterate", "ravage", "raze", "ruin", "waste", "wreck"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [2, 4, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 45. -/
def chapter45 : List VerbClass := [
  { number := "45.1", page := 241,
    title := "Break Verbs",
    members :=
      ["break", "chip", "crack", "crash", "crush", "fracture", "rip", "shatter", "smash", "snap",
      "splinter", "split", "tear"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 12], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 6, 1], .ungrammatical, .some, none⟩,
      ⟨.alternation [7, 6, 2], .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩] },
  { number := "45.2", page := 242,
    title := "Bend Verbs",
    members :=
      ["bend", "crease", "crinkle", "crumple", "fold", "rumple", "wrinkle"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 12], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩] },
  { number := "45.3", page := 243,
    title := "Cooking Verbs",
    members :=
      ["bake", "barbecue", "blanch", "boil", "braise", "broil", "brown", "charbroil",
      "charcoal-broil", "coddle", "cook", "crisp", "deep-fry", "French fry", "fry", "grill",
      "hardboil", "heat", "microwave", "oven-fry", "oven-poach", "overcook", "pan-broil",
      "pan-fry", "parboil", "parch", "percolate", "perk", "plank", "poach", "pot-roast",
      "rissole", "roast", "sauté", "scald", "scallop", "shirr", "simmer", "softboil", "steam",
      "steam-bake", "stew", "stir-fry", "toast"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.alternation [5, 3], .acceptable, .all, none⟩] },
  { number := "45.4", page := 244,
    title := "Other Alternating Verbs of Change of State",
    members :=
      ["abate", "accelerate", "acetify", "acidify", "advance", "age", "agglomerate", "air",
      "alkalify", "alter", "ameliorate", "americanize", "atrophy", "attenuate", "awake",
      "awaken", "balance", "blacken", "blast", "blunt", "blur", "brighten", "broaden",
      "brown", "burn", "burst", "calcify", "capsize", "caramelize", "carbonify", "carbonize",
      "change", "char", "cheapen", "chill", "clean", "clear", "clog", "close", "coagulate",
      "coarsen", "collapse", "collect", "compress", "condense", "contract", "cool", "corrode",
      "crimson", "crisp", "crumble", "crystallize", "dampen", "darken", "de-escalate",
      "decelerate", "decentralize", "decompose", "decrease", "deepen", "deflate", "defrost",
      "degenerate", "degrade", "dehumidify", "demagnetize", "democratize", "depressurize",
      "desiccate", "destabilize", "deteriorate", "detonate", "dim", "diminish", "dirty",
      "disintegrate", "dissipate", "dissolve", "distend", "divide", "double", "drain", "dry",
      "dull", "ease", "empty", "emulsify", "energize", "enlarge", "equalize", "evaporate",
      "even", "expand", "explode", "fade", "fatten", "federate", "fill", "firm", "flatten",
      "flood", "fossilize", "fray", "freeze", "freshen", "frost", "fructify", "fuse",
      "gasify", "gelatinize", "gladden", "glutenize", "granulate", "gray", "green", "grow",
      "halt", "harden", "harmonize", "hasten", "heal", "heat", "heighten", "humidify", "hush",
      "hybridize", "ignite", "improve", "increase", "incubate", "inflate", "intensify",
      "iodize", "ionize", "kindle", "lengthen", "lessen", "level", "levitate", "light",
      "lighten", "lignify", "liquefy", "loop", "loose", "loosen", "macerate", "magnetize",
      "magnify", "mature", "mellow", "melt", "moisten", "muddy", "multiply", "narrow",
      "neaten", "neutralize", "nitrify", "open", "operate", "ossify", "overturn", "oxidize",
      "pale", "petrify", "polarize", "pop", "proliferate", "propagate", "pulverize", "purify",
      "purple", "putrefy", "quadruple", "quicken", "quiet", "quieten", "redden", "regularize",
      "rekindle", "reopen", "reproduce", "ripen", "roughen", "round", "rupture", "scorch",
      "sear", "sharpen", "short", "shortcircuit", "shorten", "shrink", "shrivel", "shut",
      "sicken", "silicify", "silver", "singe", "sink", "slack", "slacken", "slim", "slow",
      "smarten", "smooth", "soak", "sober", "soften", "solidify", "sour", "splay", "sprout",
      "stabilize", "steady", "steep", "steepen", "stiffen", "straighten", "stratify",
      "strengthen", "stretch", "submerge", "subside", "sweeten", "tame", "tan", "taper",
      "tauten", "tense", "thaw", "thicken", "thin", "tighten", "tilt", "tire", "topple",
      "toughen", "triple", "ulcerate", "unfold", "unionize", "vaporize", "vary", "vibrate",
      "vitrify", "volatilize", "waken", "warm", "warp", "weaken", "westernize", "whiten",
      "widen", "worsen", "yellow"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
      ⟨.alternation [3, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 3, 4], .ungrammatical, .all, some "intransitive"⟩,
      ⟨.alternation [2, 3, 1], .ungrammatical, .all, some "transitive"⟩,
      ⟨.alternation [6, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.alternation [5, 3], .acceptable, .all, none⟩] },
  { number := "45.5", page := 246,
    title := "Verbs of Entity-Specific Change of State",
    members :=
      ["blister", "bloom", "blossom", "burn", "corrode", "decay", "deteriorate", "erode", "ferment",
      "flower", "germinate", "molder", "molt", "rot", "rust", "sprout", "stagnate", "swell",
      "tarnish", "wilt", "wither"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 4], .acceptable, .some, none⟩] },
  { number := "45.6", page := 247,
    title := "Verbs of Calibratable Changes of State",
    members :=
      ["appreciate", "balloon", "climb", "decline", "decrease", "depreciate", "differ", "diminish",
      "drop", "fall", "fluctuate", "gain", "grow", "increase", "jump", "mushroom", "plummet",
      "plunge", "rise", "rocket", "skyrocket", "soar", "surge", "tumble", "vary"],
    doubtful := ["mushroom"],
    properties :=
      [⟨.alternation [2, 13, 5], .acceptable, .all, some "intransitive"⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [6, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 46. -/
def chapter46 : List VerbClass := [
  { number := "46", page := 248,
    title := "Lodge Verbs",
    members :=
      ["bivouac", "board", "camp", "dwell", "live", "lodge", "reside", "settle", "shelter", "stay",
      "stop"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [6, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
      ⟨.alternation [5, 3], .ungrammatical, .all, none⟩,
      ⟨.property .erNominal, .acceptable, .some, none⟩] }]

/-- The classes of chapter 47. -/
def chapter47 : List VerbClass := [
  { number := "47.1", page := 249,
    title := "Exist Verbs",
    members :=
      ["coexist", "correspond", "depend", "dwell", "endure", "exist", "extend", "flourish",
      "languish", "linger", "live", "loom", "lurk", "overspread", "persist", "predominate",
      "prevail", "prosper", "remain", "reside", "shelter", "stay", "survive", "thrive",
      "tower", "wait"],
    doubtful := ["correspond", "depend"],
    properties :=
      [⟨.alternation [6, 1], .acceptable, .all, none⟩,
      ⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩] },
  { number := "47.2", page := 250,
    title := "Verbs of Entity-Specific Modes of Being",
    members :=
      ["billow", "bloom", "blossom", "blow", "breathe", "bristle", "bulge", "burn", "cascade",
      "corrode", "decay", "decompose", "effervesce", "erode", "ferment", "fester", "fizz",
      "flow", "flower", "foam", "froth", "germinate", "grow", "molt", "propagate", "rage",
      "ripple", "roil", "rot", "rust", "seethe", "smoke", "smolder", "spread", "sprout",
      "stagnate", "stream", "sweep", "tarnish", "trickle", "wilt", "wither"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .acceptable, .some, none⟩,
      ⟨.alternation [6, 2], .acceptable, .some, none⟩,
      ⟨.alternation [2, 3, 4], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .most, some "with a few exceptions"⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
      ⟨.property .erNominal, .ungrammatical, .all, none⟩] },
  { number := "47.3", page := 251,
    title := "Verbs of Modes of Being Involving Motion",
    members :=
      ["bob", "bow", "creep", "dance", "drift", "eddy", "flap", "float", "flutter", "hover",
      "jiggle", "joggle", "oscillate", "pulsate", "quake", "quiver", "revolve", "rock",
      "rotate", "shake", "stir", "sway", "swirl", "teeter", "throb", "totter", "tremble",
      "undulate", "vibrate", "waft", "wave", "waver", "wiggle", "wobble", "writhe"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [6, 1], .acceptable, .some, none⟩,
      ⟨.alternation [6, 2], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩] },
  { number := "47.4", page := 252,
    title := "Verbs of Sound Existence",
    members :=
      ["din", "echo", "resonate", "resound", "reverberate", "sound"],
    doubtful := ["din"],
    properties :=
      [⟨.alternation [2, 3, 4], .acceptable, .all, none⟩,
      ⟨.alternation [6, 1], .acceptable, .all, none⟩,
      ⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
      ⟨.property .erNominal, .ungrammatical, .all, none⟩] },
  { number := "47.5.1", page := 253,
    title := "Swarm Verbs",
    members :=
      ["abound", "bustle", "crawl", "creep", "hop", "run", "swarm", "swim", "teem", "throng"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3, 4], .acceptable, .all, none⟩,
      ⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.alternation [6, 1], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "47.5.2", page := 254,
    title := "Herd Verbs",
    members :=
      ["accumulate", "aggregate", "amass", "assemble", "cluster", "collect", "congregate",
      "convene", "flock", "gather", "group", "herd", "huddle", "mass"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "47.5.3", page := 254,
    title := "Bulge Verbs",
    members :=
      ["bristle", "bulge", "seethe"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "47.6", page := 255,
    title := "Verbs of Spatial Configuration",
    members :=
      ["balance", "bend", "bow", "crouch", "dangle", "flop", "fly", "hang", "hover", "jut", "kneel",
      "lean", "lie", "loll", "loom", "lounge", "nestle", "open", "perch", "plop", "project",
      "protrude", "recline", "rest", "rise", "roost", "sag", "sit", "slope", "slouch",
      "slump", "sprawl", "squat", "stand", "stoop", "straddle", "swing", "tilt", "tower"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .acceptable, .all, none⟩,
      ⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩] },
  { number := "47.7", page := 256,
    title := "Meander Verbs",
    members :=
      ["cascade", "climb", "crawl", "cut", "drop", "go", "meander", "plunge", "run", "straggle",
      "stretch", "sweep", "tumble", "turn", "twist", "wander", "weave", "wind"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.alternation [6, 1], .acceptable, .all, none⟩] },
  { number := "47.8", page := 257,
    title := "Verbs of Contiguous Location",
    members :=
      ["abut", "adjoin", "blanket", "border", "bound", "bracket", "bridge", "cap", "contain",
      "cover", "cross", "dominate", "edge", "encircle", "enclose", "fence", "fill", "flank",
      "follow", "frame", "head", "hit", "hug", "intersect", "line", "meet", "miss",
      "overhang", "precede", "rim", "ring", "skirt", "span", "straddle", "support",
      "surmount", "surround", "top", "touch", "underlie"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 3], .acceptable, .all, none⟩,
      ⟨.alternation [1, 2, 4], .acceptable, .some, none⟩] }]

/-- The classes of chapter 48. -/
def chapter48 : List VerbClass := [
  { number := "48.1.1", page := 258,
    title := "Appear Verbs",
    members :=
      ["appear", "arise", "awake", "awaken", "break", "burst", "come", "dawn", "derive", "develop",
      "emanate", "emerge", "erupt", "evolve", "exude", "flow", "form", "grow", "gush",
      "issue", "materialize", "open", "plop", "pop up", "result", "rise", "show up", "spill",
      "spread", "steal", "stem", "stream", "supervene", "surge", "turn up", "wax"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .acceptable, .most, none⟩,
      ⟨.alternation [6, 2], .acceptable, .most, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .many, none⟩,
      ⟨.alternation [5, 4], .acceptable, .all, none⟩] },
  { number := "48.1.2", page := 259,
    title := "Reflexive Verbs of Appearance",
    members :=
      ["assert", "declare", "define", "express", "form", "intrude", "manifest", "offer", "pose",
      "present", "proffer", "recommend", "shape", "show", "suggest"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [6, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [4, 2], .acceptable, (.all ["intrude"]), none⟩] },
  { number := "48.2", page := 260,
    title := "Verbs of Disappearance",
    members :=
      ["die", "disappear", "expire", "lapse", "perish", "vanish"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .marginal, .all, none⟩, ⟨.alternation [6, 2], .marginal, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 4], .acceptable, .all, none⟩] },
  { number := "48.3", page := 260,
    title := "Verbs of Occurrence",
    members :=
      ["ensue", "eventuate", "happen", "occur", "recur", "transpire"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .acceptable, .all, none⟩,
      ⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 49. -/
def chapter49 : List VerbClass := [
  { number := "49", page := 261,
    title := "Verbs of Body-Internal Motion",
    members :=
      ["buck", "fidget", "flap", "gyrate", "kick", "rock", "squirm", "sway", "teeter", "totter",
      "twitch", "waggle", "wiggle", "wobble", "wriggle"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.property .bodyPartObject, .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .some, none⟩,
      ⟨.alternation [7, 8], .acceptable, .all, none⟩] }]

/-- The classes of chapter 50. -/
def chapter50 : List VerbClass := [
  { number := "50", page := 262,
    title := "Verbs of Assuming a Position",
    members :=
      ["bend", "bow", "crouch", "flop", "hang", "kneel", "lean", "lie", "perch", "plop", "rise",
      "sit", "slouch", "slump", "sprawl", "squat", "stand", "stoop", "straddle"],
    doubtful := [],
    properties :=
      [⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [6, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 51. -/
def chapter51 : List VerbClass := [
  { number := "51.1", page := 263,
    title := "Verbs of Inherently Directed Motion",
    members :=
      ["advance", "arrive", "ascend", "climb", "come", "cross", "depart", "descend", "enter",
      "escape", "exit", "fall", "flee", "go", "leave", "plunge", "recede", "return", "rise",
      "tumble"],
    doubtful := ["climb", "cross"],
    properties :=
      [⟨.alternation [1, 4, 1], .acceptable, .some, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
      ⟨.property .measurePhrase, .ungrammatical, .all, none⟩,
      ⟨.alternation [5, 4], .acceptable, .all, none⟩,
      ⟨.property .depictivePhrase, .acceptable, .all, none⟩,
      ⟨.alternation [7, 5], .ungrammatical, .all, none⟩] },
  { number := "51.2", page := 264,
    title := "Leave Verbs",
    members :=
      ["abandon", "desert", "leave"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 3], .acceptable, .some, none⟩] },
  { number := "51.3.1", page := 264,
    title := "Roll Verbs",
    members :=
      ["bounce", "coil", "drift", "drop", "float", "glide", "move", "revolve", "roll", "rotate",
      "slide", "spin", "swing", "turn", "twirl", "twist", "whirl", "wind"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
      ⟨.alternation [1, 4, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.alternation [5, 3], .acceptable, .all, none⟩] },
  { number := "51.3.2", page := 265,
    title := "Run Verbs",
    members :=
      ["amble", "backpack", "bolt", "bounce", "bound", "bowl", "canter", "carom", "cavort",
      "charge", "clamber", "climb", "clump", "coast", "crawl", "creep", "dart", "dash",
      "dodder", "drift", "file", "flit", "float", "fly", "frolic", "gallop", "gambol",
      "glide", "goosestep", "hasten", "hike", "hobble", "hop", "hurry", "hurtle", "inch",
      "jog", "journey", "jump", "leap", "limp", "lollop", "lope", "lumber", "lurch", "march",
      "meander", "mince", "mosey", "nip", "pad", "parade", "perambulate", "plod", "prance",
      "promenade", "prowl", "race", "ramble", "roam", "roll", "romp", "rove", "run", "rush",
      "sashay", "saunter", "scamper", "scoot", "scram", "scramble", "scud", "scurry",
      "scutter", "scuttle", "shamble", "shuffle", "sidle", "skedaddle", "skip", "skitter",
      "skulk", "sleepwalk", "slide", "slink", "slither", "slog", "slouch", "sneak",
      "somersault", "speed", "stagger", "stomp", "stray", "streak", "stride", "stroll",
      "strut", "stumble", "stump", "swagger", "sweep", "swim", "tack", "tear", "tiptoe",
      "toddle", "totter", "traipse", "tramp", "travel", "trek", "troop", "trot", "trudge",
      "trundle", "vault", "waddle", "wade", "walk", "wander", "whiz", "zigzag", "zoom"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 2], .acceptable, .some, none⟩,
      ⟨.alternation [1, 4, 1], .acceptable, .some, none⟩,
      ⟨.alternation [6, 1], .acceptable, .all, none⟩,
      ⟨.alternation [6, 2], .acceptable, .all, none⟩,
      ⟨.property .measurePhrase, .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.alternation [5, 3], .acceptable, .some, none⟩,
      ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
      ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
      ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩] },
  { number := "51.4.1", page := 267,
    title := "Verbs That Are Vehicle Names",
    members :=
      ["balloon", "bicycle", "bike", "boat", "bobsled", "bus", "cab", "canoe", "chariot", "coach",
      "cycle", "dogsled", "ferry", "gondola", "helicopter", "jeep", "jet", "kayak", "moped",
      "motor", "motorbike", "motorcycle", "parachute", "punt", "raft", "rickshaw", "rocket",
      "skate", "skateboard", "ski", "sled", "sledge", "sleigh", "taxi", "toboggan", "tram",
      "trolley", "van", "yacht"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 2], .acceptable, .some, none⟩,
      ⟨.alternation [1, 4, 1], .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩] },
  { number := "51.4.2", page := 268,
    title := "Verbs That Are Not Vehicle Names",
    members :=
      ["cruise", "drive", "fly", "oar", "paddle", "pedal", "ride", "row", "sail", "tack"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 2], .acceptable, .some, none⟩,
      ⟨.alternation [1, 4, 1], .acceptable, .some, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩] },
  { number := "51.5", page := 268,
    title := "Waltz Verbs",
    members :=
      ["boogie", "bop", "cancan", "clog", "conga", "dance", "foxtrot", "jig", "jitterbug", "jive",
      "pirouette", "polka", "quickstep", "rumba", "samba", "shuffle", "squaredance", "tango",
      "tapdance", "waltz"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 2], .acceptable, .all, none⟩,
      ⟨.alternation [7, 5], .acceptable, .all, none⟩,
      ⟨.alternation [7, 1], .acceptable, .all, none⟩] },
  { number := "51.6", page := 269,
    title := "Chase Verbs",
    members :=
      ["chase", "follow", "pursue", "shadow", "tail", "track", "trail"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "51.7", page := 270,
    title := "Accompany Verbs",
    members :=
      ["accompany", "conduct", "escort", "guide", "lead", "shepherd"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 52. -/
def chapter52 : List VerbClass := [
  { number := "52", page := 270,
    title := "Avoid Verbs",
    members :=
      ["avoid", "boycott", "dodge", "duck", "elude", "evade", "shun", "sidestep"],
    doubtful := ["boycott"],
    properties :=
      [] }]

/-- The classes of chapter 53. -/
def chapter53 : List VerbClass := [
  { number := "53.1", page := 271,
    title := "Verbs of Lingering",
    members :=
      ["dally", "dawdle", "delay", "dither", "hesitate", "linger", "loiter", "tarry"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "53.2", page := 271,
    title := "Verbs of Rushing",
    members :=
      ["hasten", "hurry", "rush"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩] }]

/-- The classes of chapter 54. -/
def chapter54 : List VerbClass := [
  { number := "54.1", page := 272,
    title := "Register Verbs",
    members :=
      ["measure", "read", "register", "total", "weigh"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "54.2", page := 272,
    title := "Cost Verbs",
    members :=
      ["carry", "cost", "last", "take"],
    doubtful := [],
    properties :=
      [⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "54.3", page := 273,
    title := "Fit Verbs",
    members :=
      ["carry", "contain", "feed", "fit", "hold", "house", "seat", "serve", "sleep", "store",
      "take", "use"],
    doubtful := [],
    properties :=
      [] },
  { number := "54.4", page := 273,
    title := "Price Verbs",
    members :=
      ["appraise", "assess", "estimate", "fix", "peg", "price", "rate", "value"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] },
  { number := "54.5", page := 274,
    title := "Bill Verbs",
    members :=
      ["bet", "bill", "charge", "fine", "mulct", "overcharge", "save", "spare", "tax", "tip",
      "undercharge", "wager"],
    doubtful := [],
    properties :=
      [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
      ⟨.alternation [2, 14], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 55. -/
def chapter55 : List VerbClass := [
  { number := "55.1", page := 274,
    title := "Begin Verbs",
    members :=
      ["begin", "cease", "commence", "continue", "end", "finish", "halt", "keep", "proceed",
      "repeat", "resume", "start", "stop", "terminate"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩] },
  { number := "55.2", page := 275,
    title := "Complete Verbs",
    members :=
      ["complete", "discontinue", "initiate", "quit"],
    doubtful := [],
    properties :=
      [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩] }]

/-- The classes of chapter 56. -/
def chapter56 : List VerbClass := [
  { number := "56", page := 275,
    title := "Weekend Verbs",
    members :=
      ["summer", "vacation", "weekend", "winter"],
    doubtful := [],
    properties :=
      [] }]

/-- The classes of chapter 57. -/
def chapter57 : List VerbClass := [
  { number := "57", page := 276,
    title := "Weather Verbs",
    members :=
      ["blow", "clear", "drizzle", "fog", "freeze", "gust", "hail", "howl", "lightning", "mist",
      "mizzle", "pelt", "pour", "precipitate", "rain", "roar", "shower", "sleet", "snow",
      "spit", "spot", "sprinkle", "storm", "swelter", "teem", "thaw", "thunder"],
    doubtful := [],
    properties :=
      [] }]

/-- The classes, in the book's order. -/
def classes : List VerbClass :=
  chapter9 ++ chapter10 ++ chapter11 ++ chapter12 ++ chapter13 ++ chapter14 ++ chapter15 ++
  chapter16 ++ chapter17 ++ chapter18 ++ chapter19 ++ chapter20 ++ chapter21 ++ chapter22 ++
  chapter23 ++ chapter24 ++ chapter25 ++ chapter26 ++ chapter27 ++ chapter28 ++ chapter29 ++
  chapter30 ++ chapter31 ++ chapter32 ++ chapter33 ++ chapter34 ++ chapter35 ++ chapter36 ++
  chapter37 ++ chapter38 ++ chapter39 ++ chapter40 ++ chapter41 ++ chapter42 ++ chapter43 ++
  chapter44 ++ chapter45 ++ chapter46 ++ chapter47 ++ chapter48 ++ chapter49 ++ chapter50 ++
  chapter51 ++ chapter52 ++ chapter53 ++ chapter54 ++ chapter55 ++ chapter56 ++ chapter57

end Data.VerbClasses.Levin1993
