module

public import Linglib.Data.VerbClasses.Schema
public import Linglib.Data.VerbClasses.Levin1993.Class

/-!
# Levin1993: the class pages (generated)

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

namespace Data.VerbClasses.Levin1993.Entry

open Data.VerbClasses

/-- 9.1, Put Verbs. -/
def put : VerbClass where
  number := "9.1"
  title := "Put Verbs"
  page := 111
  members :=
    ["arrange", "immerse", "install", "lodge", "mount", "place", "position", "put", "set",
    "situate", "sling", "stash", "stow"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 9.2, Verbs of Putting in a Spatial Configuration. -/
def putInSpatialConfiguration : VerbClass where
  number := "9.2"
  title := "Verbs of Putting in a Spatial Configuration"
  page := 112
  members :=
    ["dangle", "hang", "lay", "lean", "perch", "rest", "sit", "stand", "suspend"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .most, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 9.3, Funnel Verbs. -/
def funnel : VerbClass where
  number := "9.3"
  title := "Funnel Verbs"
  page := 113
  members :=
    ["bang", "channel", "dip", "dump", "funnel", "hammer", "ladle", "pound", "push", "rake", "ram",
    "scoop", "scrape", "shake", "shovel", "siphon", "spoon", "squash", "squeeze", "squish",
    "sweep", "tuck", "wad", "wedge", "wipe", "wring"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 9.4, Verbs of Putting with a Specified Direction. -/
def putDirection : VerbClass where
  number := "9.4"
  title := "Verbs of Putting with a Specified Direction"
  page := 114
  members :=
    ["drop", "hoist", "lift", "lower", "raise"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 9.5, Pour Verbs. -/
def pour : VerbClass where
  number := "9.5"
  title := "Pour Verbs"
  page := 115
  members :=
    ["dribble", "drip", "pour", "slop", "slosh", "spew", "spill", "spurt"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
    ⟨.alternation [7, 7], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .few, none⟩]

/-- 9.6, Coil Verbs. -/
def coil : VerbClass where
  number := "9.6"
  title := "Coil Verbs"
  page := 116
  members :=
    ["coil", "curl", "loop", "roll", "spin", "twirl", "twist", "whirl", "wind"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
    ⟨.alternation [7, 7], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 9.7, Spray/Load Verbs. -/
def sprayLoad : VerbClass where
  number := "9.7"
  title := "Spray/Load Verbs"
  page := 117
  members :=
    ["brush", "cram", "crowd", "cultivate", "dab", "daub", "drape", "drizzle", "dust", "hang",
    "heap", "inject", "jam", "load", "mound", "pack", "pile", "plant", "plaster", "prick",
    "pump", "rub", "scatter", "seed", "settle", "sew", "shower", "slather", "smear", "smudge",
    "sow", "spatter", "splash", "splatter", "spray", "spread", "sprinkle", "spritz", "squirt",
    "stack", "stick", "stock", "strew", "string", "stuff", "swab", "vest", "wash", "wrap"]
  doubtful := ["prick", "vest", "wash"]
  properties :=
    [⟨.alternation [2, 3, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .some, some "based on locative variant"⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, some "based on with variant"⟩,
    ⟨.alternation [1, 3], .acceptable, .some, none⟩,
    ⟨.alternation [7, 7], .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 9.8, Fill Verbs. -/
def fill : VerbClass where
  number := "9.8"
  title := "Fill Verbs"
  page := 119
  members :=
    ["adorn", "anoint", "bandage", "bathe", "bestrew", "bind", "blanket", "block", "blot",
    "bombard", "carpet", "choke", "cloak", "clog", "clutter", "coat", "contaminate", "cover",
    "dam", "dapple", "deck", "decorate", "deluge", "dirty", "dot", "douse", "drench", "edge",
    "embellish", "emblazon", "encircle", "encrust", "endow", "enrich", "entangle", "face",
    "festoon", "fill", "fleck", "flood", "frame", "garland", "garnish", "imbue", "impregnate",
    "infect", "inlay", "interlace", "interlard", "interleave", "intersperse", "interweave",
    "inundate", "lard", "lash", "line", "litter", "mask", "mottle", "ornament", "pad", "pave",
    "plate", "plug", "pollute", "replenish", "repopulate", "riddle", "ring", "ripple", "robe",
    "saturate", "season", "shroud", "smother", "soak", "soil", "speckle", "splotch", "spot",
    "staff", "stain", "stipple", "stop up", "stud", "suffuse", "surround", "swaddle", "swathe",
    "taint", "tile", "trim", "veil", "vein", "wreathe"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 5], .acceptable, .all, none⟩,
    ⟨.property .withAlternatesWithIn, .acceptable, .some, none⟩]

/-- 9.9, Butter Verbs. -/
def butter : VerbClass where
  number := "9.9"
  title := "Butter Verbs"
  page := 120
  members :=
    ["asphalt", "bait", "blanket", "blindfold", "board", "bread", "brick", "bridle", "bronze",
    "butter", "buttonhole", "cap", "carpet", "caulk", "chrome", "cloak", "cork", "crown",
    "diaper", "drug", "feather", "fence", "flour", "forest", "frame", "fuel", "gag", "garland",
    "glove", "graffiti", "gravel", "grease", "groove", "halter", "harness", "heel", "ink",
    "label", "leash", "leaven", "lipstick", "mantle", "mulch", "muzzle", "nickel", "oil",
    "ornament", "panel", "paper", "parquet", "patch", "pepper", "perfume", "pitch", "plank",
    "plaster", "poison", "polish", "pomade", "poster", "postmark", "powder", "putty", "robe",
    "roof", "rosin", "rouge", "rut", "saddle", "salt", "salve", "sand", "seed", "sequin",
    "shawl", "shingle", "shoe", "shutter", "silver", "slate", "slipcover", "sod", "sole",
    "spice", "stain", "starch", "stopper", "stress", "string", "stucco", "sugar", "sulphur",
    "tag", "tar", "tarmac", "tassel", "thatch", "ticket", "tile", "turf", "veil", "veneer",
    "wallpaper", "water", "wax", "whitewash", "wreathe", "yoke", "zipcode"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 2], .acceptable, .all, none⟩,
    ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 9.10, Pocket Verbs. -/
def pocket : VerbClass where
  number := "9.10"
  title := "Pocket Verbs"
  page := 121
  members :=
    ["archive", "bag", "bank", "beach", "bed", "bench", "berth", "billet", "bin", "bottle", "box",
    "cage", "can", "case", "cellar", "cloister", "coop", "corral", "crate", "dock", "drydock",
    "file", "fork", "garage", "ground", "hangar", "house", "jail", "jar", "jug", "kennel",
    "land", "lodge", "pasture", "pen", "pillory", "pocket", "pot", "sheathe", "shelter",
    "shelve", "shoulder", "skewer", "snare", "spindle", "spit", "spool", "stable", "string",
    "tin", "trap", "tree", "warehouse"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 10.1, Remove Verbs. -/
def remove : VerbClass where
  number := "10.1"
  title := "Remove Verbs"
  page := 122
  members :=
    ["abstract", "cull", "delete", "discharge", "disengage", "disgorge", "dislodge", "dismiss",
    "draw", "eject", "eliminate", "eradicate", "evict", "excise", "excommunicate", "expel",
    "extirpate", "extract", "extrude", "lop", "omit", "ostracize", "oust", "partition", "pry",
    "reap", "remove", "separate", "sever", "shoo", "subtract", "uproot", "winkle", "withdraw",
    "wrench"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 10.2, Banish Verbs. -/
def banish : VerbClass where
  number := "10.2"
  title := "Banish Verbs"
  page := 123
  members :=
    ["banish", "deport", "evacuate", "expel", "extradite", "recall", "remove"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 10.3, Clear Verbs. -/
def clear : VerbClass where
  number := "10.3"
  title := "Clear Verbs"
  page := 124
  members :=
    ["clean", "clear", "drain", "empty"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3, 2], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 3, 5], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, (.all ["clean"]), none⟩,
    ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedAdjective, .acceptable, .some, none⟩,
    ⟨.alternation [5, 3], .acceptable, .all, none⟩]

/-- 10.4.1, Manner Subclass. -/
def wipeManner : VerbClass where
  number := "10.4.1"
  title := "Manner Subclass"
  page := 125
  members :=
    ["bail", "buff", "dab", "distill", "dust", "erase", "expunge", "flush", "leach", "lick",
    "pluck", "polish", "prune", "purge", "rinse", "rub", "scour", "scrape", "scratch", "scrub",
    "shave", "skim", "smooth", "soak", "squeeze", "strain", "strip", "suck", "suction", "swab",
    "sweep", "trim", "wash", "wear", "weed", "whisk", "winnow", "wipe", "wring"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 2, 1], .acceptable, .some, none⟩,
    ⟨.property .unspecifiedObjectPlusLocativePP, .acceptable, .some, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 10.4.2, Instrument Subclass. -/
def wipeInstrument : VerbClass where
  number := "10.4.2"
  title := "Instrument Subclass"
  page := 127
  members :=
    ["brush", "comb", "file", "filter", "hoover", "hose", "iron", "mop", "plow", "rake",
    "sandpaper", "shear", "shovel", "siphon", "sponge", "towel", "vacuum"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 2, 1], .acceptable, .some, none⟩,
    ⟨.property .unspecifiedObjectPlusLocativePP, .acceptable, .some, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 10.5, Verbs of Possessional Deprivation: Steal Verbs. -/
def steal : VerbClass where
  number := "10.5"
  title := "Verbs of Possessional Deprivation: Steal Verbs"
  page := 128
  members :=
    ["abduct", "cadge", "capture", "confiscate", "cop", "emancipate", "embezzle", "exorcise",
    "extort", "extract", "filch", "flog", "grab", "impound", "kidnap", "liberate", "lift",
    "nab", "pilfer", "pinch", "pirate", "plagiarize", "purloin", "reclaim", "recover", "redeem",
    "regain", "repossess", "rescue", "retrieve", "rustle", "seize", "smuggle", "snatch",
    "sneak", "sponge", "steal", "swipe", "take", "thieve", "wangle", "weasel", "winkle",
    "withdraw", "wrest"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 10.6, Verbs of Possessional Deprivation: Cheat Verbs. -/
def cheat : VerbClass where
  number := "10.6"
  title := "Verbs of Possessional Deprivation: Cheat Verbs"
  page := 129
  members :=
    ["absolve", "acquit", "balk", "bereave", "bilk", "bleed", "break", "burgle", "cheat", "cleanse",
    "con", "cull", "cure", "defraud", "denude", "deplete", "depopulate", "deprive", "despoil",
    "disabuse", "disarm", "disencumber", "dispossess", "divest", "drain", "ease", "exonerate",
    "fleece", "free", "gull", "milk", "mulct", "pardon", "plunder", "purge", "purify",
    "ransack", "relieve", "render", "rid", "rifle", "rob", "sap", "strip", "swindle",
    "unburden", "void", "wean"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.property .ofAlternatesWithOut, .acceptable, .few, none⟩]

/-- 10.7, Pit Verbs. -/
def pit : VerbClass where
  number := "10.7"
  title := "Pit Verbs"
  page := 130
  members :=
    ["bark", "beard", "bone", "burl", "core", "gill", "gut", "head", "hull", "husk", "lint",
    "louse", "milk", "peel", "pinion", "pip", "pit", "pith", "pod", "poll", "pulp", "rind",
    "scale", "scalp", "seed", "shell", "shuck", "skin", "snail", "stalk", "stem", "stone",
    "string", "tail", "tassel", "top", "vein", "weed", "wind", "worm", "zest"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 10.8, Debone Verbs. -/
def debone : VerbClass where
  number := "10.8"
  title := "Debone Verbs"
  page := 130
  members :=
    ["deaccent", "debark", "debone", "debowel", "debug", "debur", "declaw", "defang", "defat",
    "defeather", "deflea", "deflesh", "defoam", "defog", "deforest", "defrost", "defuzz",
    "degas", "degerm", "deglaze", "degrease", "degrit", "degum", "degut", "dehair", "dehead",
    "dehorn", "dehull", "dehusk", "deice", "deink", "delint", "delouse", "deluster", "demast",
    "derat", "derib", "derind", "desalt", "descale", "desex", "desprout", "destarch",
    "destress", "detassel", "detusk", "devein", "dewater", "dewax", "deworm"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 10.9, Mine Verbs. -/
def mine : VerbClass where
  number := "10.9"
  title := "Mine Verbs"
  page := 131
  members :=
    ["mine", "quarry"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 2], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 11.1, Send Verbs. -/
def send : VerbClass where
  number := "11.1"
  title := "Send Verbs"
  page := 132
  members :=
    ["airmail", "convey", "deliver", "dispatch", "express", "FedEx", "forward", "hand", "mail",
    "pass", "port", "post", "return", "send", "shift", "ship", "shunt", "slip", "smuggle",
    "sneak", "transfer", "transport", "UPS"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .some, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 7], .ungrammatical, .all, none⟩]

/-- 11.2, Slide Verbs. -/
def slide : VerbClass where
  number := "11.2"
  title := "Slide Verbs"
  page := 133
  members :=
    ["bounce", "float", "move", "roll", "slide"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, (.all ["move"]), none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
    ⟨.property .coreferentialInterpretationVaries, .acceptable, .all, none⟩]

/-- 11.3, Bring and Take. -/
def bringTake : VerbClass where
  number := "11.3"
  title := "Bring and Take"
  page := 134
  members :=
    ["bring", "take"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 7], .acceptable, .all, none⟩]

/-- 11.4, Carry Verbs. -/
def carry : VerbClass where
  number := "11.4"
  title := "Carry Verbs"
  page := 135
  members :=
    ["carry", "drag", "haul", "heave", "heft", "hoist", "kick", "lug", "pull", "push", "schlep",
    "shove", "tote", "tow", "tug"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.property .coreferentialInterpretationVaries, .acceptable, .all, none⟩]

/-- 11.5, Drive Verbs. -/
def drive : VerbClass where
  number := "11.5"
  title := "Drive Verbs"
  page := 136
  members :=
    ["barge", "bus", "cart", "drive", "ferry", "fly", "row", "shuttle", "truck", "wheel",
    "wire"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .marginal, .some, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 7], .ungrammatical, .all, none⟩]

/-- 12, Verbs of Exerting Force: Push/Pull Verbs. -/
def pushPull : VerbClass where
  number := "12"
  title := "Verbs of Exerting Force: Push/Pull Verbs"
  page := 137
  members :=
    ["draw", "heave", "jerk", "press", "pull", "push", "shove", "thrust", "tug", "yank"]
  doubtful := ["draw", "thrust"]
  properties :=
    [⟨.alternation [1, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 2, 7], .acceptable, .some, none⟩,
    ⟨.alternation [7, 7], .acceptable, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 13.1, Give Verbs. -/
def give : VerbClass where
  number := "13.1"
  title := "Give Verbs"
  page := 138
  members :=
    ["feed", "give", "lease", "lend", "loan", "pass", "pay", "peddle", "refund", "render", "rent",
    "repay", "sell", "serve", "trade"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 13.2, Contribute Verbs. -/
def contribute : VerbClass where
  number := "13.2"
  title := "Contribute Verbs"
  page := 138
  members :=
    ["administer", "contribute", "disburse", "distribute", "donate", "extend", "forfeit", "proffer",
    "refer", "reimburse", "relinquish", "remit", "restore", "return", "sacrifice", "submit",
    "surrender", "transfer"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 13.3, Verbs of Future Having. -/
def futureHaving : VerbClass where
  number := "13.3"
  title := "Verbs of Future Having"
  page := 139
  members :=
    ["advance", "allocate", "allot", "assign", "award", "bequeath", "cede", "concede", "extend",
    "grant", "guarantee", "issue", "leave", "offer", "owe", "promise", "vote", "will",
    "yield"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 13.4.1, Verbs of Fulfilling. -/
def fulfilling : VerbClass where
  number := "13.4.1"
  title := "Verbs of Fulfilling"
  page := 140
  members :=
    ["credit", "entrust", "furnish", "issue", "leave", "present", "provide", "serve", "supply",
    "trust"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 6], .acceptable, .all, none⟩]

/-- 13.4.2, Equip Verbs. -/
def equip : VerbClass where
  number := "13.4.2"
  title := "Equip Verbs"
  page := 141
  members :=
    ["arm", "burden", "charge", "compensate", "equip", "invest", "ply", "regale", "reward",
    "saddle"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 6], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩]

/-- 13.5.1, Get Verbs. -/
def get : VerbClass where
  number := "13.5.1"
  title := "Get Verbs"
  page := 141
  members :=
    ["book", "buy", "call", "cash", "catch", "charter", "choose", "earn", "fetch", "find", "gain",
    "gather", "get", "hire", "keep", "lease", "leave", "order", "phone", "pick", "pluck",
    "procure", "pull", "reach", "rent", "reserve", "save", "secure", "shoot", "slaughter",
    "steal", "vote", "win"]
  doubtful := ["choose"]
  properties :=
    [⟨.property .fromPhrase, .acceptable, .most, none⟩,
    ⟨.alternation [2, 2], .acceptable, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 9], .acceptable, .some, none⟩]

/-- 13.5.2, Obtain Verbs. -/
def obtain : VerbClass where
  number := "13.5.2"
  title := "Obtain Verbs"
  page := 142
  members :=
    ["accept", "accumulate", "acquire", "appropriate", "borrow", "cadge", "collect", "exact",
    "grab", "inherit", "obtain", "purchase", "receive", "recover", "regain", "retrieve",
    "seize", "select", "snatch"]
  doubtful := ["cadge"]
  properties :=
    [⟨.property .fromPhrase, .acceptable, .most, none⟩,
    ⟨.alternation [2, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 9], .acceptable, .few, none⟩]

/-- 13.6, Verbs of Exchange. -/
def exchange : VerbClass where
  number := "13.6"
  title := "Verbs of Exchange"
  page := 143
  members :=
    ["barter", "change", "exchange", "substitute", "swap", "trade"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 2], .ungrammatical, .all, none⟩]

/-- 13.7, Berry Verbs. -/
def berry : VerbClass where
  number := "13.7"
  title := "Berry Verbs"
  page := 144
  members :=
    ["antique", "berry", "birdnest", "blackberry", "clam", "crab", "fish", "fowl", "grouse", "hay",
    "log", "mushroom", "nest", "nut", "oyster", "pearl", "prawn", "rabbit", "seal", "shark",
    "shrimp", "snail", "snipe", "sponge", "whale", "whelk"]
  doubtful := []
  properties :=
    []

/-- 14, Learn Verbs. -/
def learn : VerbClass where
  number := "14"
  title := "Learn Verbs"
  page := 144
  members :=
    ["acquire", "cram", "glean", "learn", "memorize", "read", "study"]
  doubtful := []
  properties :=
    []

/-- 15.1, Hold Verbs. -/
def hold : VerbClass where
  number := "15.1"
  title := "Hold Verbs"
  page := 145
  members :=
    ["clasp", "clutch", "grasp", "grip", "handle", "hold", "wield"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 12], .acceptable, .some, none⟩]

/-- 15.2, Keep Verbs. -/
def keep : VerbClass where
  number := "15.2"
  title := "Keep Verbs"
  page := 145
  members :=
    ["hoard", "keep", "leave", "store"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 16, Verbs of Concealment. -/
def conceal : VerbClass where
  number := "16"
  title := "Verbs of Concealment"
  page := 146
  members :=
    ["block", "cloister", "conceal", "curtain", "hide", "isolate", "quarantine", "screen",
    "seclude", "sequester", "shelter"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩]

/-- 17.1, Throw Verbs. -/
def throw : VerbClass where
  number := "17.1"
  title := "Throw Verbs"
  page := 146
  members :=
    ["bash", "bat", "bunt", "cast", "catapult", "chuck", "fire", "flick", "fling", "flip", "hit",
    "hurl", "kick", "knock", "lob", "loft", "nudge", "pass", "pitch", "punt", "shoot", "shove",
    "slam", "slap", "sling", "smash", "tap", "throw", "tip", "toss"]
  doubtful := ["cast", "loft"]
  properties :=
    [⟨.alternation [7, 8], .acceptable, .all, none⟩,
    ⟨.alternation [2, 1], .acceptable, .most, none⟩,
    ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 17.2, Pelt Verbs. -/
def pelt : VerbClass where
  number := "17.2"
  title := "Pelt Verbs"
  page := 147
  members :=
    ["bombard", "buffet", "pelt", "shower", "stone"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩]

/-- 18.1, Hit Verbs. -/
def hit : VerbClass where
  number := "18.1"
  title := "Hit Verbs"
  page := 148
  members :=
    ["bang", "bash", "batter", "beat", "bump", "butt", "dash", "drum", "hammer", "hit", "kick",
    "knock", "lash", "pound", "rap", "slap", "smack", "smash", "strike", "tamp", "tap", "thump",
    "thwack", "whack"]
  doubtful := []
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
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 18.2, Swat Verbs. -/
def swat : VerbClass where
  number := "18.2"
  title := "Swat Verbs"
  page := 150
  members :=
    ["bite", "claw", "paw", "peck", "punch", "scratch", "shoot", "slug", "stab", "swat",
    "swipe"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 9], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .acceptable, .all, none⟩,
    ⟨.alternation [2, 12], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 18.3, Spank Verbs. -/
def spank : VerbClass where
  number := "18.3"
  title := "Spank Verbs"
  page := 151
  members :=
    ["belt", "birch", "bludgeon", "bonk", "brain", "cane", "clobber", "club", "conk", "cosh",
    "cudgel", "cuff", "flog", "knife", "paddle", "paddywhack", "pummel", "sock", "spank",
    "strap", "thrash", "truncheon", "wallop", "whip", "whisk"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 9], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 12], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.property .ingNominal, .acceptable, .most, none⟩]

/-- 18.4, Non-Agentive Verbs of Impact by Contact. -/
def nonAgentiveImpact : VerbClass where
  number := "18.4"
  title := "Non-Agentive Verbs of Impact by Contact"
  page := 153
  members :=
    ["bang", "brush", "bump", "crash", "hit", "knock", "ram", "slam", "smash", "thud"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 5], .acceptable, .some, some "intransitive"⟩]

/-- 19, Poke Verbs. -/
def poke : VerbClass where
  number := "19"
  title := "Poke Verbs"
  page := 154
  members :=
    ["dig", "jab", "pierce", "poke", "prick", "stick"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 9], .acceptable, .all, none⟩,
    ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .acceptable, .some, none⟩,
    ⟨.alternation [2, 12], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 3], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 20, Verbs of Contact: Touch Verbs. -/
def touch : VerbClass where
  number := "20"
  title := "Verbs of Contact: Touch Verbs"
  page := 155
  members :=
    ["caress", "graze", "kiss", "lick", "nudge", "pat", "peck", "pinch", "prod", "sting", "stroke",
    "tickle", "touch"]
  doubtful := []
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
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 21.1, Cut Verbs. -/
def cut : VerbClass where
  number := "21.1"
  title := "Cut Verbs"
  page := 156
  members :=
    ["chip", "clip", "cut", "hack", "hew", "saw", "scrape", "scratch", "slash", "snip"]
  doubtful := []
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
    ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩]

/-- 21.2, Carve Verbs. -/
def carve : VerbClass where
  number := "21.2"
  title := "Carve Verbs"
  page := 157
  members :=
    ["bore", "bruise", "carve", "chip", "chop", "crop", "crush", "cube", "dent", "dice", "drill",
    "file", "fillet", "gash", "gouge", "grate", "grind", "mangle", "mash", "mince", "mow",
    "nick", "notch", "perforate", "prune", "pulverize", "punch", "shred", "slice", "slit",
    "spear", "squash", "squish"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 12], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
    ⟨.alternation [3, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 2, 6, 2], .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 22.1, Mix Verbs. -/
def mix : VerbClass where
  number := "22.1"
  title := "Mix Verbs"
  page := 159
  members :=
    ["add", "blend", "combine", "commingle", "concatenate", "connect", "cream", "fuse", "join",
    "link", "merge", "mingle", "mix", "network", "pool"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 1], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 4], .acceptable, .most, some "intransitive"⟩,
    ⟨.alternation [2, 5, 2], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 5], .acceptable, .most, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩]

/-- 22.2, Amalgamate Verbs. -/
def amalgamate : VerbClass where
  number := "22.2"
  title := "Amalgamate Verbs"
  page := 160
  members :=
    ["affiliate", "alternate", "amalgamate", "associate", "coalesce", "coincide", "compare",
    "confederate", "confuse", "conjoin", "consolidate", "contrast", "correlate", "criss-cross",
    "engage", "entangle", "entwine", "harmonize", "incorporate", "integrate", "interchange",
    "interconnect", "interlace", "interlink", "interlock", "intermingle", "interrelate",
    "intersperse", "intertwine", "interweave", "introduce", "marry", "mate", "muddle", "oppose",
    "pair", "rhyme", "team", "total", "unify", "unite", "wed"]
  doubtful := ["pair", "team"]
  properties :=
    [⟨.alternation [2, 5, 1], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 2], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 5], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩]

/-- 22.3, Shake Verbs. -/
def shake : VerbClass where
  number := "22.3"
  title := "Shake Verbs"
  page := 161
  members :=
    ["append", "attach", "band", "baste", "beat", "bind", "bond", "bundle", "cluster", "collate",
    "collect", "fasten", "fuse", "gather", "glom", "graft", "group", "herd", "jumble", "lump",
    "mass", "moor", "package", "pair", "roll", "scramble", "sew", "shake", "shuffle", "splice",
    "stick", "stir", "swirl", "weld", "whip", "whisk"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 2], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .most, some "with a few exceptions"⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩]

/-- 22.4, Tape Verbs. -/
def tape : VerbClass where
  number := "22.4"
  title := "Tape Verbs"
  page := 162
  members :=
    ["anchor", "band", "belt", "bolt", "bracket", "buckle", "button", "cement", "chain", "clamp",
    "clasp", "clip", "epoxy", "fetter", "glue", "gum", "handcuff", "harness", "hinge", "hitch",
    "hook", "knot", "lace", "lash", "lasso", "latch", "leash", "link", "lock", "loop",
    "manacle", "moor", "muzzle", "nail", "padlock", "paste", "peg", "pin", "plaster", "rivet",
    "rope", "screw", "seal", "shackle", "skewer", "solder", "staple", "stitch", "strap",
    "string", "tack", "tape", "tether", "thumbtack", "tie", "trammel", "wire", "yoke",
    "zip"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 2], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.alternation [7, 2], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 22.5, Cling Verbs. -/
def cling : VerbClass where
  number := "22.5"
  title := "Cling Verbs"
  page := 164
  members :=
    ["adhere", "cleave", "cling"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 5], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 23.1, Separate Verbs. -/
def separate : VerbClass where
  number := "23.1"
  title := "Separate Verbs"
  page := 165
  members :=
    ["decouple", "differentiate", "disconnect", "disentangle", "dissociate", "distinguish",
    "divide", "divorce", "part", "segregate", "separate", "sever"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 1], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 3], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 6], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 3], .ungrammatical, .all, none⟩]

/-- 23.2, Split Verbs. -/
def split : VerbClass where
  number := "23.2"
  title := "Split Verbs"
  page := 166
  members :=
    ["blow", "break", "cut", "draw", "hack", "hew", "kick", "knock", "pry", "pull", "push", "rip",
    "roll", "saw", "shove", "slip", "split", "tear", "tug", "yank"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 3], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 6], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩]

/-- 23.3, Disassemble Verbs. -/
def disassemble : VerbClass where
  number := "23.3"
  title := "Disassemble Verbs"
  page := 167
  members :=
    ["detach", "disassemble", "disconnect", "partition", "sift", "sunder", "unbolt", "unbuckle",
    "unbutton", "unchain", "unclamp", "unclasp", "unclip", "unfasten", "unglue", "unhinge",
    "unhitch", "unhook", "unlace", "unlatch", "unleash", "unlock", "unpeg", "unpin", "unscrew",
    "unshackle", "unstaple", "unstitch", "untie", "unzip"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 5, 3], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .most, some "a few exceptions"⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩]

/-- 23.4, Differ Verbs. -/
def differ : VerbClass where
  number := "23.4"
  title := "Differ Verbs"
  page := 167
  members :=
    ["differ", "diverge"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 6], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 24, Verbs of Coloring. -/
def color : VerbClass where
  number := "24"
  title := "Verbs of Coloring"
  page := 168
  members :=
    ["color", "distemper", "dye", "enamel", "glaze", "japan", "lacquer", "paint", "shellac",
    "spraypaint", "stain", "tint", "varnish"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.alternation [7, 2], .acceptable, .all, none⟩]

/-- 25.1, Verbs of Image Impression. -/
def imageImpression : VerbClass where
  number := "25.1"
  title := "Verbs of Image Impression"
  page := 169
  members :=
    ["appliqué", "emboss", "embroider", "engrave", "etch", "imprint", "incise", "inscribe", "mark",
    "paint", "set", "sign", "stamp", "tattoo"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 7], .acceptable, .all, none⟩,
    ⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
    ⟨.property .processNominal, .acceptable, .all, none⟩,
    ⟨.property .resultNominal, .acceptable, .all, none⟩]

/-- 25.2, Scribble Verbs. -/
def scribble : VerbClass where
  number := "25.2"
  title := "Scribble Verbs"
  page := 170
  members :=
    ["carve", "chalk", "charcoal", "copy", "crayon", "doodle", "draw", "forge", "ink", "paint",
    "pencil", "plot", "print", "scratch", "scrawl", "scribble", "sketch", "spraypaint",
    "stencil", "trace", "type", "write"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 7], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 2, 1], .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 25.3, Illustrate Verbs. -/
def illustrate : VerbClass where
  number := "25.3"
  title := "Illustrate Verbs"
  page := 171
  members :=
    ["address", "adorn", "autograph", "brand", "date", "decorate", "embellish", "endorse",
    "illuminate", "illustrate", "initial", "label", "letter", "monogram", "ornament", "tag"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 7], .ungrammatical, .all, none⟩,
    ⟨.property .processNominal, .acceptable, .some, none⟩,
    ⟨.property .resultNominal, .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 25.4, Transcribe Verbs. -/
def transcribe : VerbClass where
  number := "25.4"
  title := "Transcribe Verbs"
  page := 171
  members :=
    ["copy", "film", "forge", "microfilm", "photocopy", "photograph", "record", "tape", "televise",
    "transcribe", "type"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 7], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 26.1, Build Verbs. -/
def build : VerbClass where
  number := "26.1"
  title := "Build Verbs"
  page := 173
  members :=
    ["arrange", "assemble", "bake", "blow", "build", "carve", "cast", "chisel", "churn", "compile",
    "cook", "crochet", "cut", "develop", "embroider", "fashion", "fold", "forge", "grind",
    "grow", "hack", "hammer", "hatch", "knit", "make", "mold", "pound", "roll", "sculpt", "sew",
    "shape", "spin", "stitch", "weave", "whittle"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 4, 1], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 4, 3], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 2], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 8], .acceptable, .some, none⟩,
    ⟨.alternation [3, 9], .acceptable, .few, none⟩]

/-- 26.2, Grow Verbs. -/
def grow : VerbClass where
  number := "26.2"
  title := "Grow Verbs"
  page := 174
  members :=
    ["develop", "evolve", "grow", "hatch", "mature"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 4, 2], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [2, 4, 4], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩]

/-- 26.3, Verbs of Preparing. -/
def prepare : VerbClass where
  number := "26.3"
  title := "Verbs of Preparing"
  page := 175
  members :=
    ["bake", "blend", "boil", "brew", "clean", "clear", "cook", "fix", "fry", "grill", "hardboil",
    "iron", "light", "mix", "poach", "pour", "prepare", "roast", "roll", "run", "scramble",
    "set", "softboil", "toast", "toss", "wash"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 2], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 26.4, Create Verbs. -/
def create : VerbClass where
  number := "26.4"
  title := "Create Verbs"
  page := 175
  members :=
    ["coin", "compose", "compute", "concoct", "construct", "create", "derive", "design", "dig",
    "fabricate", "form", "invent", "manufacture", "mint", "model", "organize", "produce",
    "recreate", "style", "synthesize"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 2], .ungrammatical, .most, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 8], .ungrammatical, .all, none⟩]

/-- 26.5, Knead Verbs. -/
def knead : VerbClass where
  number := "26.5"
  title := "Knead Verbs"
  page := 176
  members :=
    ["beat", "bend", "coil", "collect", "compress", "fold", "freeze", "knead", "melt", "shake",
    "squash", "squeeze", "squish", "twirl", "twist", "wad", "whip", "wind", "work"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .some, none⟩,
    ⟨.alternation [3, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 4, 3], .ungrammatical, .all, some "transitive"⟩]

/-- 26.6, Turn Verbs. -/
def turn : VerbClass where
  number := "26.6"
  title := "Turn Verbs"
  page := 177
  members :=
    ["alter", "change", "convert", "metamorphose", "transform", "transmute", "turn"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 4, 3], .acceptable, .all, some "transitive"⟩,
    ⟨.alternation [2, 4, 4], .acceptable, .most, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
    ⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 4, 2], .ungrammatical, .all, some "intransitive"⟩]

/-- 26.7, Performance Verbs. -/
def performance : VerbClass where
  number := "26.7"
  title := "Performance Verbs"
  page := 178
  members :=
    ["chant", "choreograph", "compose", "dance", "direct", "draw", "hum", "intone", "paint",
    "perform", "play", "produce", "recite", "silkscreen", "sing", "spin", "take", "whistle",
    "write"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .some, none⟩,
    ⟨.alternation [2, 2], .acceptable, .some, none⟩,
    ⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 27, Engender Verbs. -/
def engender : VerbClass where
  number := "27"
  title := "Engender Verbs"
  page := 179
  members :=
    ["beget", "cause", "create", "engender", "generate", "shape", "spawn"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 28, Calve Verbs. -/
def calve : VerbClass where
  number := "28"
  title := "Calve Verbs"
  page := 180
  members :=
    ["calve", "cub", "fawn", "foal", "kitten", "lamb", "litter", "pup", "spawn", "whelp"]
  doubtful := []
  properties :=
    []

/-- 29.1, Appoint Verbs. -/
def appoint : VerbClass where
  number := "29.1"
  title := "Appoint Verbs"
  page := 181
  members :=
    ["acknowledge", "adopt", "appoint", "consider", "crown", "deem", "designate", "elect", "esteem",
    "imagine", "mark", "nominate", "ordain", "proclaim", "rate", "reckon", "report", "want"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 14], .acceptable, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.property .infinitivalCopularClause, .acceptable, .some, none⟩]

/-- 29.2, Characterize Verbs. -/
def characterize : VerbClass where
  number := "29.2"
  title := "Characterize Verbs"
  page := 181
  members :=
    ["accept", "address", "appreciate", "bill", "cast", "certify", "characterize", "choose", "cite",
    "class", "classify", "confirm", "count", "define", "describe", "diagnose", "disguise",
    "employ", "engage", "enlist", "enroll", "enter", "envisage", "establish", "esteem", "hail",
    "herald", "hire", "honor", "identify", "imagine", "incorporate", "induct", "intend",
    "lampoon", "offer", "oppose", "paint", "portray", "praise", "qualify", "rank", "recollect",
    "recommend", "regard", "reinstate", "reject", "remember", "represent", "repudiate",
    "reveal", "salute", "see", "select", "stigmatize", "take", "train", "treat", "use", "value",
    "view", "visualize"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
    ⟨.property .infinitivalCopularClause, .acceptable, .few, none⟩]

/-- 29.3, Dub Verbs. -/
def dub : VerbClass where
  number := "29.3"
  title := "Dub Verbs"
  page := 182
  members :=
    ["anoint", "baptize", "brand", "call", "christen", "consecrate", "crown", "decree", "dub",
    "label", "make", "name", "nickname", "pronounce", "rule", "stamp", "style", "term",
    "vote"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.property .infinitivalCopularClause, .ungrammatical, .all, none⟩]

/-- 29.4, Declare Verbs. -/
def declare : VerbClass where
  number := "29.4"
  title := "Declare Verbs"
  page := 182
  members :=
    ["adjudge", "adjudicate", "assume", "avow", "believe", "confess", "declare", "fancy", "find",
    "judge", "presume", "profess", "prove", "suppose", "think", "warrant"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.property .infinitivalCopularClause, .acceptable, .all, none⟩]

/-- 29.5, Conjecture Verbs. -/
def conjecture : VerbClass where
  number := "29.5"
  title := "Conjecture Verbs"
  page := 183
  members :=
    ["admit", "allow", "assert", "conjecture", "deny", "discover", "feel", "figure", "grant",
    "guarantee", "guess", "hold", "know", "maintain", "mean", "observe", "recognize", "repute",
    "show", "suspect"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
    ⟨.property .infinitivalCopularClause, .acceptable, .all, none⟩]

/-- 29.6, Masquerade Verbs. -/
def masquerade : VerbClass where
  number := "29.6"
  title := "Masquerade Verbs"
  page := 183
  members :=
    ["act", "behave", "camouflage", "count", "masquerade", "officiate", "qualify", "rank", "rate",
    "serve"]
  doubtful := []
  properties :=
    []

/-- 29.7, Orphan Verbs. -/
def orphan : VerbClass where
  number := "29.7"
  title := "Orphan Verbs"
  page := 184
  members :=
    ["apprentice", "canonize", "cripple", "cuckold", "knight", "martyr", "orphan", "outlaw",
    "pauper", "recruit", "widow"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 1], .acceptable, .all, none⟩]

/-- 29.8, Captain Verbs. -/
def captain : VerbClass where
  number := "29.8"
  title := "Captain Verbs"
  page := 184
  members :=
    ["boss", "bully", "butcher", "butler", "caddy", "captain", "champion", "chaperone", "chauffeur",
    "clerk", "coach", "cox", "crew", "doctor", "emcee", "escort", "guard", "host", "model",
    "mother", "nurse", "partner", "pilot", "pioneer", "police", "referee", "shepherd",
    "skipper", "sponsor", "star", "tailor", "tutor", "umpire", "understudy", "usher", "valet",
    "volunteer", "witness"]
  doubtful := []
  properties :=
    []

/-- 30.1, See Verbs. -/
def see : VerbClass where
  number := "30.1"
  title := "See Verbs"
  page := 185
  members :=
    ["detect", "discern", "feel", "hear", "notice", "see", "sense", "smell", "taste"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 13, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 13, 2], .acceptable, .all, none⟩]

/-- 30.2, Sight Verbs. -/
def sight : VerbClass where
  number := "30.2"
  title := "Sight Verbs"
  page := 186
  members :=
    ["descry", "discover", "espy", "examine", "eye", "glimpse", "inspect", "investigate", "note",
    "observe", "overhear", "perceive", "recognize", "regard", "savor", "scan", "scent",
    "scrutinize", "sight", "spot", "spy", "study", "survey", "view", "watch", "witness"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩]

/-- 30.3, Peer Verbs. -/
def peer : VerbClass where
  number := "30.3"
  title := "Peer Verbs"
  page := 187
  members :=
    ["check", "gape", "gawk", "gaze", "glance", "glare", "goggle", "leer", "listen", "look", "ogle",
    "peek", "peep", "peer", "sniff", "snoop", "squint", "stare"]
  doubtful := []
  properties :=
    []

/-- 30.4, Stimulus Subject Perception Verbs. -/
def stimulusSubjectPerception : VerbClass where
  number := "30.4"
  title := "Stimulus Subject Perception Verbs"
  page := 187
  members :=
    ["feel", "look", "smell", "sound", "taste"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 1], .ungrammatical, .all, none⟩]

/-- 31.1, Amuse Verbs. -/
def amuse : VerbClass where
  number := "31.1"
  title := "Amuse Verbs"
  page := 189
  members :=
    ["abash", "affect", "afflict", "affront", "aggravate", "agitate", "agonize", "alarm",
    "alienate", "amaze", "amuse", "anger", "annoy", "antagonize", "appall", "appease", "arouse",
    "asperate", "assuage", "astonish", "astound", "awe", "baffle", "beguile", "bewilder",
    "bewitch", "boggle", "bore", "bother", "bug", "calm", "captivate", "chagrin", "charm",
    "cheer", "chill", "comfort", "concern", "confound", "confuse", "console", "content",
    "convince", "cow", "crush", "cut", "daunt", "daze", "dazzle", "deject", "delight",
    "demolish", "demoralize", "depress", "devastate", "disappoint", "disarm", "discombobulate",
    "discomfit", "discompose", "disconcert", "discourage", "disgrace", "disgruntle", "disgust",
    "dishearten", "disillusion", "dismay", "dispirit", "disquiet", "dissatisfy", "distract",
    "distress", "disturb", "dumbfound", "elate", "elecdisplease", "embarrass", "embolden",
    "enchant", "encourage", "engage", "engross", "enlighten", "enrage", "enrapture",
    "entertain", "enthrall", "enthuse", "entice", "entrance", "excite", "exenliven", "exhaust",
    "exhilarate", "fascinate", "faze", "flabbergast", "flatter", "floor", "fluster", "frighten",
    "frustrate", "gall", "galvanize", "gladden", "gratify", "grieve", "harass", "haunt",
    "hearten", "horrify", "humble", "humiliate", "hurt", "hypnotize", "impress", "incense",
    "infuriate", "inspire", "insult", "interest", "intimidate", "intoxicate", "intrigue",
    "invigorate", "irk", "irritate", "ize", "jar", "jollify", "jolt", "lull", "madden",
    "mesmerize", "miff", "mollify", "mortify", "move", "muddle", "mystify", "nauseate",
    "nettle", "numb", "obsess", "offend", "outrage", "overawe", "overwhelm", "pacify", "pain",
    "peeve", "perplex", "perturb", "pique", "placate", "plague", "please", "preoccupy",
    "puzzle", "rankle", "reassure", "refresh", "relax", "relieve", "repel", "repulse",
    "revitalprovoke", "revolt", "rile", "ruffle", "sadden", "satisfy", "scandalize", "scare",
    "shake", "shame", "shock", "sicken", "sober", "solace", "soothe", "spellbind", "spook",
    "stagger", "startle", "stimulate", "sting", "stir", "strike", "stump", "stun", "stupefy",
    "surprise", "tantalize", "tease", "tempt", "terrify", "terrorize", "threaten", "thrill",
    "throw", "tickle", "tire", "titillate", "torment", "touch", "transport", "trify", "trouble",
    "try", "unnerve", "unsettle", "uplift", "upset", "vex", "weary", "worry", "wound",
    "wow"]
  doubtful := []
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
    ⟨.property .ableAdjective, .acceptable, .some, none⟩]

/-- 31.2, Admire Verbs. -/
def admire : VerbClass where
  number := "31.2"
  title := "Admire Verbs"
  page := 191
  members :=
    ["abhor", "admire", "adore", "appreciate", "cherish", "deplore", "despise", "detest", "disdain",
    "dislike", "distrust", "dread", "enjoy", "envy", "esteem", "exalt", "execrate", "fancy",
    "favor", "fear", "hate", "idolize", "lament", "like", "loathe", "love", "miss", "mourn",
    "pity", "prize", "regret", "relish", "resent", "respect", "revere", "rue", "savor", "stand",
    "support", "tolerate", "treasure", "trust", "value", "venerate", "worship"]
  doubtful := ["rue"]
  properties :=
    [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 13, 2], .acceptable, .all, none⟩,
    ⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
    ⟨.property (.sententialComplement .unspecified), .acceptable, .some, none⟩,
    ⟨.property .extraposition, .acceptable, .some, none⟩,
    ⟨.property (.derivedNominal .active), .acceptable, .all, none⟩,
    ⟨.property .ableAdjective, .acceptable, .all, none⟩,
    ⟨.property .erNominal, .acceptable, .all, none⟩]

/-- 31.3, Marvel Verbs. -/
def marvel : VerbClass where
  number := "31.3"
  title := "Marvel Verbs"
  page := 192
  members :=
    ["ache", "anger", "anguish", "approve", "bask", "beware", "bleed", "bother", "care", "cheer",
    "cringe", "cry", "delight", "despair", "disapprove", "enthuse", "exult", "fear", "feel",
    "fret", "fume", "gladden", "gloat", "glory", "grieve", "groove", "gush", "hunger", "hurt",
    "luxuriate", "madden", "marvel", "mind", "moon", "mope", "mourn", "obsess", "puzzle",
    "rage", "rave", "react", "rejoice", "revel", "rhapsodize", "sadden", "salivate", "seethe",
    "sicken", "sorrow", "suffer", "swoon", "thrill", "tire", "wallow", "weary", "weep",
    "wonder", "worry"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 1], .acceptable, .some, none⟩]

/-- 31.4, Appeal Verbs. -/
def appeal : VerbClass where
  number := "31.4"
  title := "Appeal Verbs"
  page := 193
  members :=
    ["appeal", "grate", "jar", "matter", "niggle"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 1], .ungrammatical, .all, none⟩]

/-- 32.1, Want Verbs. -/
def want : VerbClass where
  number := "32.1"
  title := "Want Verbs"
  page := 194
  members :=
    ["covet", "crave", "desire", "fancy", "need", "want"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 13, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 14], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 1], .marginal, .all, none⟩]

/-- 32.2, Long Verbs. -/
def long : VerbClass where
  number := "32.2"
  title := "Long Verbs"
  page := 194
  members :=
    ["ache", "crave", "dangle", "fall", "hanker", "hope", "hunger", "itch", "long", "lust", "pine",
    "pray", "thirst", "wish", "yearn"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 1], .marginal, .all, none⟩]

/-- 33, Judgment Verbs. -/
def judgment : VerbClass where
  number := "33"
  title := "Judgment Verbs"
  page := 195
  members :=
    ["abuse", "acclaim", "applaud", "backbite", "bless", "calumniate", "castigate", "celebrate",
    "censure", "chasten", "chastise", "chide", "commend", "compensate", "compliment", "condemn",
    "congratulate", "criticize", "decry", "defame", "denigrate", "denounce", "deprecate",
    "deride", "disparage", "eulogize", "excuse", "extol", "fault", "felicitate", "fine",
    "forgive", "greet", "hail", "honor", "impeach", "insult", "lambaste", "laud", "malign",
    "mock", "pardon", "penalize", "persecute", "praise", "prosecute", "punish", "rebuke",
    "recompense", "remunerate", "repay", "reprimand", "reproach", "reprove", "revile", "reward",
    "ridicule", "salute", "scold", "scorn", "shame", "snub", "thank", "toast", "upbraid",
    "victimize", "vilify", "welcome"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 13, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 14], .acceptable, .some, none⟩,
    ⟨.property .processNominal, .acceptable, .some, none⟩]

/-- 34, Verbs of Assessment. -/
def assessment : VerbClass where
  number := "34"
  title := "Verbs of Assessment"
  page := 196
  members :=
    ["analyze", "assess", "audit", "evaluate", "review", "scrutinize", "study"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 13, 1], .acceptable, .all, none⟩,
    ⟨.alternation [2, 13, 2], .ungrammatical, .all, none⟩]

/-- 35.1, Hunt Verbs. -/
def hunt : VerbClass where
  number := "35.1"
  title := "Hunt Verbs"
  page := 197
  members :=
    ["dig", "feel", "fish", "hunt", "mine", "poach", "scrounge"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 1], .acceptable, .all, none⟩]

/-- 35.2, Search Verbs. -/
def search : VerbClass where
  number := "35.2"
  title := "Search Verbs"
  page := 198
  members :=
    ["advertise", "check", "comb", "dive", "drag", "dredge", "excavate", "patrol", "plumb", "probe",
    "prospect", "prowl", "quarry", "rake", "rifle", "scavenge", "scour", "scout", "search",
    "shop", "sift", "trawl", "troll", "watch"]
  doubtful := []
  properties :=
    []

/-- 35.3, Stalk Verbs. -/
def stalk : VerbClass where
  number := "35.3"
  title := "Stalk Verbs"
  page := 198
  members :=
    ["smell", "stalk", "taste", "track"]
  doubtful := []
  properties :=
    []

/-- 35.4, Investigate Verbs. -/
def investigate : VerbClass where
  number := "35.4"
  title := "Investigate Verbs"
  page := 198
  members :=
    ["canvass", "examine", "explore", "frisk", "inspect", "investigate", "observe", "quiz", "raid",
    "ransack", "riffle", "scan", "scrutinize", "survey", "tap"]
  doubtful := []
  properties :=
    []

/-- 35.5, Rummage Verbs. -/
def rummage : VerbClass where
  number := "35.5"
  title := "Rummage Verbs"
  page := 199
  members :=
    ["bore", "burrow", "delve", "forage", "fumble", "grope", "leaf", "listen", "look", "page",
    "paw", "poke", "rifle", "root", "rummage", "scrabble", "scratch", "snoop", "thumb",
    "tunnel"]
  doubtful := []
  properties :=
    []

/-- 35.6, Ferret Verbs. -/
def ferret : VerbClass where
  number := "35.6"
  title := "Ferret Verbs"
  page := 199
  members :=
    ["ferret", "nose", "seek", "tease"]
  doubtful := []
  properties :=
    []

/-- 36.1, Correspond Verbs. -/
def correspond : VerbClass where
  number := "36.1"
  title := "Correspond Verbs"
  page := 200
  members :=
    ["agree", "argue", "banter", "bargain", "bicker", "brawl", "clash", "coexist", "collaborate",
    "collide", "combat", "commiserate", "communicate", "compete", "concur", "confabulate",
    "conflict", "consort", "cooperate", "correspond", "dicker", "differ", "disagree", "dispute",
    "dissent", "duel", "elope", "feud", "flirt", "haggle", "hobnob", "jest", "joke", "joust",
    "mate", "mingle", "mix", "neck", "negotiate", "pair", "plot", "quarrel", "quibble",
    "rendezvous", "scuffle", "skirmish", "spar", "spat", "spoon", "squabble", "struggle",
    "tilt", "tussle", "vie", "war", "wrangle", "wrestle"]
  doubtful := []
  properties :=
    [⟨.property .collectiveNPSubject, .acceptable, .all, none⟩,
    ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [1, 2, 4], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩]

/-- 36.2, Marry Verbs. -/
def marry : VerbClass where
  number := "36.2"
  title := "Marry Verbs"
  page := 201
  members :=
    ["court", "cuddle", "date", "divorce", "embrace", "hug", "kiss", "marry", "nuzzle", "pass",
    "pet"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 4], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [1, 2, 4], .acceptable, .all, none⟩,
    ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩]

/-- 36.3, Meet Verbs. -/
def meet : VerbClass where
  number := "36.3"
  title := "Meet Verbs"
  page := 201
  members :=
    ["battle", "box", "consult", "debate", "fight", "meet", "play", "visit"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [1, 2, 4], .acceptable, .all, none⟩,
    ⟨.alternation [1, 4, 2], .acceptable, .all, none⟩]

/-- 37.1, Verbs of Transfer of a Message. -/
def transferOfMessage : VerbClass where
  number := "37.1"
  title := "Verbs of Transfer of a Message"
  page := 202
  members :=
    ["ask", "cite", "demonstrate", "dictate", "explain", "explicate", "narrate", "pose", "preach",
    "quote", "read", "recite", "relay", "show", "teach", "tell", "write"]
  doubtful := ["pose"]
  properties :=
    [⟨.alternation [2, 1], .acceptable, .most, none⟩]

/-- 37.2, Tell. -/
def tell : VerbClass where
  number := "37.2"
  title := "Tell"
  page := 203
  members :=
    ["tell"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .all, none⟩,
    ⟨.property (.sententialComplement (.required .object)), .acceptable, .all, none⟩,
    ⟨.property (.sententialComplement (.required .toPhrase)), .ungrammatical, .all, none⟩,
    ⟨.property (.sententialComplement .absent), .ungrammatical, .all, none⟩,
    ⟨.property .directSpeech, .acceptable, .all, none⟩,
    ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
    ⟨.alternation [5, 1], .acceptable, .all, none⟩,
    ⟨.property .impersonalPassive, .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩]

/-- 37.3, Verbs of Manner of Speaking. -/
def mannerOfSpeaking : VerbClass where
  number := "37.3"
  title := "Verbs of Manner of Speaking"
  page := 204
  members :=
    ["babble", "bark", "bawl", "bellow", "bleat", "boom", "bray", "burble", "cackle", "call",
    "carol", "chant", "chatter", "chirp", "cluck", "coo", "croak", "croon", "crow", "cry",
    "drawl", "drone", "gabble", "gibber", "groan", "growl", "grumble", "grunt", "hiss",
    "holler", "hoot", "howl", "jabber", "lilt", "lisp", "moan", "mumble", "murmur", "mutter",
    "purr", "rage", "rasp", "roar", "rumble", "scream", "screech", "shout", "shriek", "sing",
    "snap", "snarl", "snuffle", "splutter", "squall", "squawk", "squeak", "squeal", "stammer",
    "stutter", "thunder", "tisk", "trill", "trumpet", "twitter", "wail", "warble", "wheeze",
    "whimper", "whine", "whisper", "whistle", "whoop", "yammer", "yap", "yell", "yelp",
    "yodel"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.property (.sententialComplement (.optional .toPhrase)), .acceptable, .all, none⟩,
    ⟨.property .directSpeech, .acceptable, .all, none⟩,
    ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
    ⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 3], .acceptable, .all, none⟩,
    ⟨.alternation [7, 1], .marginal, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 37.4, Verbs of Instrument of Communication. -/
def instrumentOfCommunication : VerbClass where
  number := "37.4"
  title := "Verbs of Instrument of Communication"
  page := 206
  members :=
    ["cable", "e-mail", "fax", "modem", "netmail", "phone", "radio", "relay", "satellite",
    "semaphore", "sign", "signal", "telecast", "telegraph", "telephone", "telex", "wire",
    "wireless"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .all, none⟩,
    ⟨.property (.sententialComplement (.optional .object)), .acceptable, .all, none⟩,
    ⟨.property (.sententialComplement (.optional .toPhrase)), .acceptable, .all, none⟩,
    ⟨.property .directSpeech, .acceptable, .all, none⟩,
    ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 37.5, Talk Verbs. -/
def talk : VerbClass where
  number := "37.5"
  title := "Talk Verbs"
  page := 207
  members :=
    ["speak", "talk"]
  doubtful := []
  properties :=
    [⟨.property (.sententialComplement .unspecified), .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 5], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [1, 2, 4], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 37.6, Chitchat Verbs. -/
def chitchat : VerbClass where
  number := "37.6"
  title := "Chitchat Verbs"
  page := 208
  members :=
    ["argue", "chat", "chatter", "chitchat", "confer", "converse", "gab", "gossip", "rap",
    "schmooze", "yak"]
  doubtful := []
  properties :=
    [⟨.property (.sententialComplement .unspecified), .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 5, 4], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [2, 5, 5], .ungrammatical, .all, some "intransitive"⟩,
    ⟨.alternation [1, 2, 4], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 4, 2], .ungrammatical, .all, none⟩]

/-- 37.7, Say Verbs. -/
def say : VerbClass where
  number := "37.7"
  title := "Say Verbs"
  page := 209
  members :=
    ["announce", "articulate", "blab", "blurt", "claim", "confess", "confide", "convey", "declare",
    "mention", "note", "observe", "proclaim", "propose", "recount", "reiterate", "relate",
    "remark", "repeat", "report", "reveal", "say", "state", "suggest"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .ungrammatical, .all, none⟩]

/-- 37.8, Complain Verbs. -/
def complain : VerbClass where
  number := "37.8"
  title := "Complain Verbs"
  page := 210
  members :=
    ["boast", "brag", "complain", "crab", "gripe", "grouch", "grouse", "grumble", "kvetch",
    "object"]
  doubtful := []
  properties :=
    [⟨.property (.sententialComplement (.optional .toPhrase)), .acceptable, .all, none⟩,
    ⟨.property .directSpeech, .acceptable, .all, none⟩,
    ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩]

/-- 37.9, Advise Verbs. -/
def advise : VerbClass where
  number := "37.9"
  title := "Advise Verbs"
  page := 211
  members :=
    ["admonish", "advise", "alert", "caution", "counsel", "instruct", "warn"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 5], .acceptable, (.all ["alert"]), none⟩,
    ⟨.property (.sententialComplement (.optional .object)), .acceptable, .all, none⟩,
    ⟨.property .directSpeech, .acceptable, .all, none⟩,
    ⟨.property .parentheticalUse, .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .ungrammatical, .most, none⟩]

/-- 38, Verbs of Sounds Made by Animals. -/
def animalSound : VerbClass where
  number := "38"
  title := "Verbs of Sounds Made by Animals"
  page := 212
  members :=
    ["baa", "bark", "bay", "bellow", "blat", "bleat", "bray", "buzz", "cackle", "call", "caw",
    "chatter", "cheep", "chirp", "chirrup", "chitter", "cluck", "coo", "croak", "crow",
    "cuckoo", "drone", "gobble", "growl", "grunt", "hee-haw", "hiss", "honk", "hoot", "howl",
    "low", "meow", "mew", "moo", "neigh", "oink", "peep", "pipe", "purr", "quack", "roar",
    "scrawk", "scream", "screech", "sing", "snap", "snarl", "snort", "snuffle", "squawk",
    "squeak", "squeal", "stridulate", "trill", "tweet", "twitter", "wail", "warble", "whimper",
    "whinny", "whistle", "woof", "yap", "yell", "yelp", "yip", "yowl"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 3], .acceptable, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩]

/-- 39.1, Eat Verbs. -/
def eat : VerbClass where
  number := "39.1"
  title := "Eat Verbs"
  page := 213
  members :=
    ["drink", "eat"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .acceptable, .all, none⟩,
    ⟨.alternation [3, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 39.2, Chew Verbs. -/
def chew : VerbClass where
  number := "39.2"
  title := "Chew Verbs"
  page := 214
  members :=
    ["chew", "chomp", "crunch", "gnaw", "lick", "munch", "nibble", "peck", "pick", "sip", "slurp",
    "suck"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 39.3, Gobble Verbs. -/
def gobble : VerbClass where
  number := "39.3"
  title := "Gobble Verbs"
  page := 214
  members :=
    ["bolt", "gobble", "gulp", "guzzle", "quaff", "swallow", "swig", "wolf"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 39.4, Devour Verbs. -/
def devour : VerbClass where
  number := "39.4"
  title := "Devour Verbs"
  page := 215
  members :=
    ["consume", "devour", "imbibe", "ingest", "swill"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩]

/-- 39.5, Dine Verbs. -/
def dine : VerbClass where
  number := "39.5"
  title := "Dine Verbs"
  page := 215
  members :=
    ["banquet", "breakfast", "luncheon", "nosh", "picnic", "snack", "sup"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩]

/-- 39.6, Gorge Verbs. -/
def gorge : VerbClass where
  number := "39.6"
  title := "Gorge Verbs"
  page := 216
  members :=
    ["exist", "feed", "flourish", "gorge", "live", "prosper", "survive", "thrive"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩]

/-- 39.7, Verbs of Feeding. -/
def feed : VerbClass where
  number := "39.7"
  title := "Verbs of Feeding"
  page := 216
  members :=
    ["bottlefeed", "breastfeed", "feed", "forcefeed", "handfeed", "spoonfeed"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .acceptable, .all, none⟩]

/-- 40.1.1, Hiccup Verbs. -/
def hiccup : VerbClass where
  number := "40.1.1"
  title := "Hiccup Verbs"
  page := 217
  members :=
    ["belch", "blush", "burp", "flush", "hiccup", "pant", "sneeze", "sniffle", "snore", "snuffle",
    "swallow", "wheeze", "yawn"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 1], .marginal, .all, none⟩, ⟨.alternation [7, 5], .marginal, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 40.1.2, Breathe Verbs. -/
def breathe : VerbClass where
  number := "40.1.2"
  title := "Breathe Verbs"
  page := 218
  members :=
    ["bleed", "breathe", "cough", "cry", "dribble", "drool", "puke", "spit", "sweat", "vomit",
    "weep"]
  doubtful := ["weep"]
  properties :=
    [⟨.alternation [7, 1], .acceptable, .few, none⟩,
    ⟨.property .substanceObject, .acceptable, .most, none⟩,
    ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩]

/-- 40.1.3, Exhale Verbs. -/
def exhale : VerbClass where
  number := "40.1.3"
  title := "Exhale Verbs"
  page := 218
  members :=
    ["exhale", "inhale", "perspire"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩]

/-- 40.2, Verbs of Nonverbal Expression. -/
def nonverbalExpression : VerbClass where
  number := "40.2"
  title := "Verbs of Nonverbal Expression"
  page := 219
  members :=
    ["beam", "cackle", "chortle", "chuckle", "cough", "cry", "frown", "gape", "gasp", "gawk",
    "giggle", "glare", "glower", "goggle", "grimace", "grin", "groan", "growl", "guffaw",
    "howl", "jeer", "laugh", "moan", "pout", "scowl", "sigh", "simper", "smile", "smirk",
    "sneeze", "snicker", "sniff", "snigger", "snivel", "snore", "snort", "sob", "titter",
    "weep", "whistle", "yawn"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 1], .acceptable, .some, none⟩,
    ⟨.alternation [7, 3], .acceptable, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .most, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩]

/-- 40.3.1, Wink Verbs. -/
def wink : VerbClass where
  number := "40.3.1"
  title := "Wink Verbs"
  page := 220
  members :=
    ["blink", "clap", "nod", "point", "shrug", "squint", "wag", "wave", "wink"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 2], .acceptable, .all, none⟩,
    ⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 3], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 40.3.2, Crane Verbs. -/
def crane : VerbClass where
  number := "40.3.2"
  title := "Crane Verbs"
  page := 221
  members :=
    ["arch", "bare", "bat", "beat", "blow", "clench", "click", "close", "cock", "crane", "crook",
    "cross", "drum", "flap", "flash", "flex", "flick", "flutter", "fold", "gnash", "grind",
    "hang", "hunch", "kick", "knit", "open", "pucker", "purse", "raise", "roll", "rub", "shake",
    "show", "shuffle", "smack", "snap", "stamp", "stretch", "toss", "turn", "twiddle", "twitch",
    "wag", "waggle", "wiggle", "wring", "wrinkle"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 2], .acceptable, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 40.3.3, Curtsey Verbs. -/
def curtsey : VerbClass where
  number := "40.3.3"
  title := "Curtsey Verbs"
  page := 222
  members :=
    ["bob", "bow", "curtsey", "genuflect", "kneel", "salaam", "salute"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 3], .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 40.4, Snooze Verbs. -/
def snooze : VerbClass where
  number := "40.4"
  title := "Snooze Verbs"
  page := 222
  members :=
    ["catnap", "doze", "drowse", "nap", "sleep", "slumber", "snooze"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, (.all ["sleep"]), none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 40.5, Flinch Verbs. -/
def flinch : VerbClass where
  number := "40.5"
  title := "Flinch Verbs"
  page := 223
  members :=
    ["balk", "cower", "cringe", "flinch", "recoil", "shrink", "wince"]
  doubtful := ["balk"]
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 3], .ungrammatical, .all, none⟩]

/-- 40.6, Verbs of Body-Internal States of Existence. -/
def bodyInternalStateOfExistence : VerbClass where
  number := "40.6"
  title := "Verbs of Body-Internal States of Existence"
  page := 223
  members :=
    ["convulse", "cower", "quake", "quiver", "shake", "shiver", "shudder", "tremble", "writhe"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 40.7, Suffocate Verbs. -/
def suffocate : VerbClass where
  number := "40.7"
  title := "Suffocate Verbs"
  page := 224
  members :=
    ["asphyxiate", "choke", "drown", "stifle", "suffocate"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 1], .marginal, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .some, none⟩]

/-- 40.8.1, Pain Verbs. -/
def pain : VerbClass where
  number := "40.8.1"
  title := "Pain Verbs"
  page := 224
  members :=
    ["ache", "bother", "hurt", "itch", "pain"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 1], .ungrammatical, .all, none⟩]

/-- 40.8.2, Tingle Verbs. -/
def tingle : VerbClass where
  number := "40.8.2"
  title := "Tingle Verbs"
  page := 225
  members :=
    ["burn", "hum", "pound", "prickle", "pucker", "reel", "smart", "spin", "split", "sting", "swim",
    "throb", "tickle", "tingle"]
  doubtful := []
  properties :=
    [⟨.alternation [7, 1], .ungrammatical, .all, none⟩]

/-- 40.8.3, Hurt Verbs. -/
def hurt : VerbClass where
  number := "40.8.3"
  title := "Hurt Verbs"
  page := 225
  members :=
    ["bark", "bite", "break", "bruise", "bump", "burn", "chip", "cut", "fracture", "hurt", "injure",
    "nick", "prick", "pull", "rupture", "scald", "scratch", "skin", "split", "sprain", "strain",
    "stub", "turn", "twist"]
  doubtful := []
  properties :=
    []

/-- 40.8.4, Verbs of Change of Bodily State. -/
def changeOfBodilyState : VerbClass where
  number := "40.8.4"
  title := "Verbs of Change of Bodily State"
  page := 226
  members :=
    ["blanch", "faint", "sicken", "swoon"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩]

/-- 41.1.1, Dress Verbs. -/
def dress : VerbClass where
  number := "41.1.1"
  title := "Dress Verbs"
  page := 227
  members :=
    ["bathe", "change", "disrobe", "dress", "exercise", "preen", "primp", "shave", "shower",
    "strip", "undress", "wash"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 2, 3], .acceptable, .all, none⟩]

/-- 41.1.2, Groom Verbs. -/
def groom : VerbClass where
  number := "41.1.2"
  title := "Groom Verbs"
  page := 228
  members :=
    ["curry", "groom"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩]

/-- 41.2.1, Floss Verbs. -/
def floss : VerbClass where
  number := "41.2.1"
  title := "Floss Verbs"
  page := 228
  members :=
    ["brush", "floss", "shave", "wash"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 2, 2], .acceptable, .all, none⟩]

/-- 41.2.2, Braid Verbs. -/
def braid : VerbClass where
  number := "41.2.2"
  title := "Braid Verbs"
  page := 229
  members :=
    ["bob", "braid", "brush", "clip", "coldcream", "comb", "condition", "crimp", "crop", "curl",
    "cut", "dye", "file", "henna", "lather", "manicure", "part", "perm", "plait", "pluck",
    "powder", "rinse", "rouge", "set", "shampoo", "soap", "talc", "tease", "towel", "trim",
    "wave"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩]

/-- 41.3.1, Simple Verbs of Dressing. -/
def simpleDressing : VerbClass where
  number := "41.3.1"
  title := "Simple Verbs of Dressing"
  page := 229
  members :=
    ["doff", "don", "wear"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩]

/-- 41.3.2, Verbs of Dressing Well. -/
def dressingWell : VerbClass where
  number := "41.3.2"
  title := "Verbs of Dressing Well"
  page := 229
  members :=
    ["doll", "dress", "spruce", "tog"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 3], .acceptable, .all, none⟩]

/-- 41.3.3, Verbs of Being Dressed. -/
def beingDressed : VerbClass where
  number := "41.3.3"
  title := "Verbs of Being Dressed"
  page := 230
  members :=
    ["attire", "clad", "garb", "robe"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 2, 3], .ungrammatical, .all, none⟩]

/-- 42.1, Murder Verbs. -/
def murder : VerbClass where
  number := "42.1"
  title := "Murder Verbs"
  page := 230
  members :=
    ["assassinate", "butcher", "dispatch", "eliminate", "execute", "immolate", "kill", "liquidate",
    "massacre", "murder", "slaughter", "slay"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 3], .ungrammatical, (.all ["kill"]), none⟩,
    ⟨.alternation [7, 5], .ungrammatical, (.all ["kill"]), none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 42.2, Poison Verbs. -/
def poison : VerbClass where
  number := "42.2"
  title := "Poison Verbs"
  page := 232
  members :=
    ["asphyxiate", "crucify", "drown", "electrocute", "garrotte", "hang", "knife", "poison",
    "shoot", "smother", "stab", "strangle", "suffocate"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, (.all ["asphyxiate", "drown", "suffocate"]), none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩]

/-- 43.1, Verbs of Light Emission. -/
def lightEmission : VerbClass where
  number := "43.1"
  title := "Verbs of Light Emission"
  page := 233
  members :=
    ["beam", "blaze", "blink", "burn", "flame", "flare", "flash", "flicker", "glare", "gleam",
    "glimmer", "glint", "glisten", "glitter", "glow", "incandesce", "scintillate", "shimmer",
    "shine", "sparkle", "twinkle"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3, 4], .acceptable, .all, none⟩,
    ⟨.alternation [6, 2], .acceptable, .all, none⟩,
    ⟨.alternation [6, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
    ⟨.property .erNominal, .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 43.2, Verbs of Sound Emission. -/
def soundEmission : VerbClass where
  number := "43.2"
  title := "Verbs of Sound Emission"
  page := 234
  members :=
    ["babble", "bang", "beat", "beep", "bellow", "blare", "blast", "blat", "boom", "bubble",
    "burble", "burr", "buzz", "chatter", "chime", "chink", "chir", "chitter", "chug", "clack",
    "clang", "clank", "clap", "clash", "clatter", "click", "cling", "clink", "clomp", "clump",
    "clunk", "crack", "crackle", "crash", "creak", "crepitate", "crunch", "cry", "ding", "dong",
    "explode", "fizz", "fizzle", "groan", "growl", "gurgle", "hiss", "hoot", "howl", "hum",
    "jangle", "jingle", "knell", "knock", "lilt", "moan", "murmur", "patter", "peal", "ping",
    "pink", "pipe", "plink", "plonk", "plop", "plunk", "pop", "purr", "putter", "rap", "rasp",
    "rattle", "ring", "roar", "roll", "rumble", "rustle", "scream", "screech", "shriek",
    "shrill", "sing", "sizzle", "snap", "splash", "splutter", "sputter", "squawk", "squeak",
    "squeal", "squelch", "strike", "swish", "swoosh", "thrum", "thud", "thump", "thunder",
    "thunk", "tick", "ting", "tinkle", "toll", "toot", "tootle", "trill", "trumpet", "twang",
    "ululate", "vroom", "wail", "wheeze", "whine", "whir", "whish", "whistle", "whoosh",
    "whump", "zing"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3, 4], .acceptable, .most, none⟩,
    ⟨.alternation [6, 2], .acceptable, .some, none⟩,
    ⟨.alternation [6, 1], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩,
    ⟨.alternation [7, 8], .acceptable, .all, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
    ⟨.property .erNominal, .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 43.3, Verbs of Smell Emission. -/
def smellEmission : VerbClass where
  number := "43.3"
  title := "Verbs of Smell Emission"
  page := 236
  members :=
    ["reek", "smell", "stink"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 43.4, Verbs of Substance Emission. -/
def substanceEmission : VerbClass where
  number := "43.4"
  title := "Verbs of Substance Emission"
  page := 237
  members :=
    ["belch", "bleed", "bubble", "dribble", "drip", "drool", "emanate", "exude", "foam", "gush",
    "leak", "ooze", "pour", "puff", "radiate", "seep", "shed", "slop", "spew", "spill", "spout",
    "sprout", "spurt", "squirt", "steam", "stream", "sweat"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 3], .acceptable, .all, none⟩,
    ⟨.alternation [2, 3, 4], .acceptable, .some, none⟩,
    ⟨.alternation [6, 2], .acceptable, .some, none⟩,
    ⟨.alternation [6, 1], .acceptable, .some, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
    ⟨.property .erNominal, .acceptable, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 44, Destroy Verbs. -/
def destroy : VerbClass where
  number := "44"
  title := "Destroy Verbs"
  page := 239
  members :=
    ["annihilate", "blitz", "decimate", "demolish", "destroy", "devastate", "exterminate",
    "extirpate", "obliterate", "ravage", "raze", "ruin", "waste", "wreck"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 4, 1], .ungrammatical, .all, some "transitive"⟩,
    ⟨.alternation [2, 4, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [3, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .ungrammatical, .all, none⟩,
    ⟨.property .zeroRelatedNominal, .ungrammatical, .all, none⟩]

/-- 45.1, Break Verbs. -/
def break_ : VerbClass where
  number := "45.1"
  title := "Break Verbs"
  page := 241
  members :=
    ["break", "chip", "crack", "crash", "crush", "fracture", "rip", "shatter", "smash", "snap",
    "splinter", "split", "tear"]
  doubtful := []
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
    ⟨.property .zeroRelatedNominal, .acceptable, .all, none⟩]

/-- 45.2, Bend Verbs. -/
def bend : VerbClass where
  number := "45.2"
  title := "Bend Verbs"
  page := 242
  members :=
    ["bend", "crease", "crinkle", "crumple", "fold", "rumple", "wrinkle"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
    ⟨.alternation [3, 3], .acceptable, .all, none⟩,
    ⟨.alternation [2, 8], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 12], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .most, none⟩]

/-- 45.3, Cooking Verbs. -/
def cooking : VerbClass where
  number := "45.3"
  title := "Cooking Verbs"
  page := 243
  members :=
    ["bake", "barbecue", "blanch", "boil", "braise", "broil", "brown", "charbroil",
    "charcoal-broil", "coddle", "cook", "crisp", "deep-fry", "French fry", "fry", "grill",
    "hardboil", "heat", "microwave", "oven-fry", "oven-poach", "overcook", "pan-broil",
    "pan-fry", "parboil", "parch", "percolate", "perk", "plank", "poach", "pot-roast",
    "rissole", "roast", "sauté", "scald", "scallop", "shirr", "simmer", "softboil", "steam",
    "steam-bake", "stew", "stir-fry", "toast"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 1], .acceptable, .all, none⟩,
    ⟨.alternation [3, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.alternation [5, 3], .acceptable, .all, none⟩]

/-- 45.4, Other Alternating Verbs of Change of State. -/
def otherChangeOfState : VerbClass where
  number := "45.4"
  title := "Other Alternating Verbs of Change of State"
  page := 244
  members :=
    ["abate", "accelerate", "acetify", "acidify", "advance", "age", "agglomerate", "air",
    "alkalify", "alter", "ameliorate", "americanize", "atrophy", "attenuate", "awake", "awaken",
    "balance", "blacken", "blast", "blunt", "blur", "brighten", "broaden", "brown", "burn",
    "burst", "calcify", "capsize", "caramelize", "carbonify", "carbonize", "change", "char",
    "cheapen", "chill", "clean", "clear", "clog", "close", "coagulate", "coarsen", "collapse",
    "collect", "compress", "condense", "contract", "cool", "corrode", "crimson", "crisp",
    "crumble", "crystallize", "dampen", "darken", "de-escalate", "decelerate", "decentralize",
    "decompose", "decrease", "deepen", "deflate", "defrost", "degenerate", "degrade",
    "dehumidify", "demagnetize", "democratize", "depressurize", "desiccate", "destabilize",
    "deteriorate", "detonate", "dim", "diminish", "dirty", "disintegrate", "dissipate",
    "dissolve", "distend", "divide", "double", "drain", "dry", "dull", "ease", "empty",
    "emulsify", "energize", "enlarge", "equalize", "evaporate", "even", "expand", "explode",
    "fade", "fatten", "federate", "fill", "firm", "flatten", "flood", "fossilize", "fray",
    "freeze", "freshen", "frost", "fructify", "fuse", "gasify", "gelatinize", "gladden",
    "glutenize", "granulate", "gray", "green", "grow", "halt", "harden", "harmonize", "hasten",
    "heal", "heat", "heighten", "humidify", "hush", "hybridize", "ignite", "improve",
    "increase", "incubate", "inflate", "intensify", "iodize", "ionize", "kindle", "lengthen",
    "lessen", "level", "levitate", "light", "lighten", "lignify", "liquefy", "loop", "loose",
    "loosen", "macerate", "magnetize", "magnify", "mature", "mellow", "melt", "moisten",
    "muddy", "multiply", "narrow", "neaten", "neutralize", "nitrify", "open", "operate",
    "ossify", "overturn", "oxidize", "pale", "petrify", "polarize", "pop", "proliferate",
    "propagate", "pulverize", "purify", "purple", "putrefy", "quadruple", "quicken", "quiet",
    "quieten", "redden", "regularize", "rekindle", "reopen", "reproduce", "ripen", "roughen",
    "round", "rupture", "scorch", "sear", "sharpen", "short", "shortcircuit", "shorten",
    "shrink", "shrivel", "shut", "sicken", "silicify", "silver", "singe", "sink", "slack",
    "slacken", "slim", "slow", "smarten", "smooth", "soak", "sober", "soften", "solidify",
    "sour", "splay", "sprout", "stabilize", "steady", "steep", "steepen", "stiffen",
    "straighten", "stratify", "strengthen", "stretch", "submerge", "subside", "sweeten", "tame",
    "tan", "taper", "tauten", "tense", "thaw", "thicken", "thin", "tighten", "tilt", "tire",
    "topple", "toughen", "triple", "ulcerate", "unfold", "unionize", "vaporize", "vary",
    "vibrate", "vitrify", "volatilize", "waken", "warm", "warp", "weaken", "westernize",
    "whiten", "widen", "worsen", "yellow"]
  doubtful := []
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
    ⟨.alternation [5, 3], .acceptable, .all, none⟩]

/-- 45.5, Verbs of Entity-Specific Change of State. -/
def entitySpecificChangeOfState : VerbClass where
  number := "45.5"
  title := "Verbs of Entity-Specific Change of State"
  page := 246
  members :=
    ["blister", "bloom", "blossom", "burn", "corrode", "decay", "deteriorate", "erode", "ferment",
    "flower", "germinate", "molder", "molt", "rot", "rust", "sprout", "stagnate", "swell",
    "tarnish", "wilt", "wither"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 4], .acceptable, .some, none⟩]

/-- 45.6, Verbs of Calibratable Changes of State. -/
def calibratableChangeOfState : VerbClass where
  number := "45.6"
  title := "Verbs of Calibratable Changes of State"
  page := 247
  members :=
    ["appreciate", "balloon", "climb", "decline", "decrease", "depreciate", "differ", "diminish",
    "drop", "fall", "fluctuate", "gain", "grow", "increase", "jump", "mushroom", "plummet",
    "plunge", "rise", "rocket", "skyrocket", "soar", "surge", "tumble", "vary"]
  doubtful := ["mushroom"]
  properties :=
    [⟨.alternation [2, 13, 5], .acceptable, .all, some "intransitive"⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [6, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩]

/-- 46, Lodge Verbs. -/
def lodge : VerbClass where
  number := "46"
  title := "Lodge Verbs"
  page := 248
  members :=
    ["bivouac", "board", "camp", "dwell", "live", "lodge", "reside", "settle", "shelter", "stay",
    "stop"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [6, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
    ⟨.alternation [5, 3], .ungrammatical, .all, none⟩,
    ⟨.property .erNominal, .acceptable, .some, none⟩]

/-- 47.1, Exist Verbs. -/
def exist : VerbClass where
  number := "47.1"
  title := "Exist Verbs"
  page := 249
  members :=
    ["coexist", "correspond", "depend", "dwell", "endure", "exist", "extend", "flourish",
    "languish", "linger", "live", "loom", "lurk", "overspread", "persist", "predominate",
    "prevail", "prosper", "remain", "reside", "shelter", "stay", "survive", "thrive", "tower",
    "wait"]
  doubtful := ["correspond", "depend"]
  properties :=
    [⟨.alternation [6, 1], .acceptable, .all, none⟩, ⟨.alternation [6, 2], .acceptable, .all, none⟩,
    ⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩]

/-- 47.2, Verbs of Entity-Specific Modes of Being. -/
def entitySpecificModeOfBeing : VerbClass where
  number := "47.2"
  title := "Verbs of Entity-Specific Modes of Being"
  page := 250
  members :=
    ["billow", "bloom", "blossom", "blow", "breathe", "bristle", "bulge", "burn", "cascade",
    "corrode", "decay", "decompose", "effervesce", "erode", "ferment", "fester", "fizz", "flow",
    "flower", "foam", "froth", "germinate", "grow", "molt", "propagate", "rage", "ripple",
    "roil", "rot", "rust", "seethe", "smoke", "smolder", "spread", "sprout", "stagnate",
    "stream", "sweep", "tarnish", "trickle", "wilt", "wither"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .acceptable, .some, none⟩,
    ⟨.alternation [6, 2], .acceptable, .some, none⟩,
    ⟨.alternation [2, 3, 4], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .most, some "with a few exceptions"⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
    ⟨.property .erNominal, .ungrammatical, .all, none⟩]

/-- 47.3, Verbs of Modes of Being Involving Motion. -/
def modeOfBeingInvolvingMotion : VerbClass where
  number := "47.3"
  title := "Verbs of Modes of Being Involving Motion"
  page := 251
  members :=
    ["bob", "bow", "creep", "dance", "drift", "eddy", "flap", "float", "flutter", "hover", "jiggle",
    "joggle", "oscillate", "pulsate", "quake", "quiver", "revolve", "rock", "rotate", "shake",
    "stir", "sway", "swirl", "teeter", "throb", "totter", "tremble", "undulate", "vibrate",
    "waft", "wave", "waver", "wiggle", "wobble", "writhe"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [6, 1], .acceptable, .some, none⟩,
    ⟨.alternation [6, 2], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩]

/-- 47.4, Verbs of Sound Existence. -/
def soundExistence : VerbClass where
  number := "47.4"
  title := "Verbs of Sound Existence"
  page := 252
  members :=
    ["din", "echo", "resonate", "resound", "reverberate", "sound"]
  doubtful := ["din"]
  properties :=
    [⟨.alternation [2, 3, 4], .acceptable, .all, none⟩,
    ⟨.alternation [6, 1], .acceptable, .all, none⟩,
    ⟨.alternation [6, 2], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩,
    ⟨.property .erNominal, .ungrammatical, .all, none⟩]

/-- 47.5.1, Swarm Verbs. -/
def swarm : VerbClass where
  number := "47.5.1"
  title := "Swarm Verbs"
  page := 253
  members :=
    ["abound", "bustle", "crawl", "creep", "hop", "run", "swarm", "swim", "teem", "throng"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3, 4], .acceptable, .all, none⟩,
    ⟨.alternation [6, 2], .acceptable, .all, none⟩,
    ⟨.alternation [6, 1], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 47.5.2, Herd Verbs. -/
def herd : VerbClass where
  number := "47.5.2"
  title := "Herd Verbs"
  page := 254
  members :=
    ["accumulate", "aggregate", "amass", "assemble", "cluster", "collect", "congregate", "convene",
    "flock", "gather", "group", "herd", "huddle", "mass"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 47.5.3, Bulge Verbs. -/
def bulge : VerbClass where
  number := "47.5.3"
  title := "Bulge Verbs"
  page := 254
  members :=
    ["bristle", "bulge", "seethe"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 3], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 47.6, Verbs of Spatial Configuration. -/
def spatialConfiguration : VerbClass where
  number := "47.6"
  title := "Verbs of Spatial Configuration"
  page := 255
  members :=
    ["balance", "bend", "bow", "crouch", "dangle", "flop", "fly", "hang", "hover", "jut", "kneel",
    "lean", "lie", "loll", "loom", "lounge", "nestle", "open", "perch", "plop", "project",
    "protrude", "recline", "rest", "rise", "roost", "sag", "sit", "slope", "slouch", "slump",
    "sprawl", "squat", "stand", "stoop", "straddle", "swing", "tilt", "tower"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .acceptable, .all, none⟩, ⟨.alternation [6, 2], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩,
    ⟨.alternation [5, 4], .ungrammatical, .all, none⟩]

/-- 47.7, Meander Verbs. -/
def meander : VerbClass where
  number := "47.7"
  title := "Meander Verbs"
  page := 256
  members :=
    ["cascade", "climb", "crawl", "cut", "drop", "go", "meander", "plunge", "run", "straggle",
    "stretch", "sweep", "tumble", "turn", "twist", "wander", "weave", "wind"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 2], .acceptable, .all, none⟩,
    ⟨.alternation [6, 1], .acceptable, .all, none⟩]

/-- 47.8, Verbs of Contiguous Location. -/
def contiguousLocation : VerbClass where
  number := "47.8"
  title := "Verbs of Contiguous Location"
  page := 257
  members :=
    ["abut", "adjoin", "blanket", "border", "bound", "bracket", "bridge", "cap", "contain", "cover",
    "cross", "dominate", "edge", "encircle", "enclose", "fence", "fill", "flank", "follow",
    "frame", "head", "hit", "hug", "intersect", "line", "meet", "miss", "overhang", "precede",
    "rim", "ring", "skirt", "span", "straddle", "support", "surmount", "surround", "top",
    "touch", "underlie"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 3], .acceptable, .all, none⟩,
    ⟨.alternation [1, 2, 4], .acceptable, .some, none⟩]

/-- 48.1.1, Appear Verbs. -/
def appear : VerbClass where
  number := "48.1.1"
  title := "Appear Verbs"
  page := 258
  members :=
    ["appear", "arise", "awake", "awaken", "break", "burst", "come", "dawn", "derive", "develop",
    "emanate", "emerge", "erupt", "evolve", "exude", "flow", "form", "grow", "gush", "issue",
    "materialize", "open", "plop", "pop up", "result", "rise", "show up", "spill", "spread",
    "steal", "stem", "stream", "supervene", "surge", "turn up", "wax"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .acceptable, .most, none⟩,
    ⟨.alternation [6, 2], .acceptable, .most, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .many, none⟩,
    ⟨.alternation [5, 4], .acceptable, .all, none⟩]

/-- 48.1.2, Reflexive Verbs of Appearance. -/
def reflexiveAppearance : VerbClass where
  number := "48.1.2"
  title := "Reflexive Verbs of Appearance"
  page := 259
  members :=
    ["assert", "declare", "define", "express", "form", "intrude", "manifest", "offer", "pose",
    "present", "proffer", "recommend", "shape", "show", "suggest"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [6, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [4, 2], .acceptable, (.all ["intrude"]), none⟩]

/-- 48.2, Verbs of Disappearance. -/
def disappearance : VerbClass where
  number := "48.2"
  title := "Verbs of Disappearance"
  page := 260
  members :=
    ["die", "disappear", "expire", "lapse", "perish", "vanish"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .marginal, .all, none⟩, ⟨.alternation [6, 2], .marginal, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 4], .acceptable, .all, none⟩]

/-- 48.3, Verbs of Occurrence. -/
def occurrence : VerbClass where
  number := "48.3"
  title := "Verbs of Occurrence"
  page := 260
  members :=
    ["ensue", "eventuate", "happen", "occur", "recur", "transpire"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .acceptable, .all, none⟩, ⟨.alternation [6, 2], .acceptable, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 49, Verbs of Body-Internal Motion. -/
def bodyInternalMotion : VerbClass where
  number := "49"
  title := "Verbs of Body-Internal Motion"
  page := 261
  members :=
    ["buck", "fidget", "flap", "gyrate", "kick", "rock", "squirm", "sway", "teeter", "totter",
    "twitch", "waggle", "wiggle", "wobble", "wriggle"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.property .bodyPartObject, .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .some, none⟩,
    ⟨.alternation [7, 8], .acceptable, .all, none⟩]

/-- 50, Verbs of Assuming a Position. -/
def assumePosition : VerbClass where
  number := "50"
  title := "Verbs of Assuming a Position"
  page := 262
  members :=
    ["bend", "bow", "crouch", "flop", "hang", "kneel", "lean", "lie", "perch", "plop", "rise",
    "sit", "slouch", "slump", "sprawl", "squat", "stand", "stoop", "straddle"]
  doubtful := []
  properties :=
    [⟨.alternation [6, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [6, 2], .ungrammatical, .all, none⟩]

/-- 51.1, Verbs of Inherently Directed Motion. -/
def inherentlyDirectedMotion : VerbClass where
  number := "51.1"
  title := "Verbs of Inherently Directed Motion"
  page := 263
  members :=
    ["advance", "arrive", "ascend", "climb", "come", "cross", "depart", "descend", "enter",
    "escape", "exit", "fall", "flee", "go", "leave", "plunge", "recede", "return", "rise",
    "tumble"]
  doubtful := ["climb", "cross"]
  properties :=
    [⟨.alternation [1, 4, 1], .acceptable, .some, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩,
    ⟨.property .measurePhrase, .ungrammatical, .all, none⟩,
    ⟨.alternation [5, 4], .acceptable, .all, none⟩,
    ⟨.property .depictivePhrase, .acceptable, .all, none⟩,
    ⟨.alternation [7, 5], .ungrammatical, .all, none⟩]

/-- 51.2, Leave Verbs. -/
def leave : VerbClass where
  number := "51.2"
  title := "Leave Verbs"
  page := 264
  members :=
    ["abandon", "desert", "leave"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 3], .acceptable, .some, none⟩]

/-- 51.3.1, Roll Verbs. -/
def roll : VerbClass where
  number := "51.3.1"
  title := "Roll Verbs"
  page := 264
  members :=
    ["bounce", "coil", "drift", "drop", "float", "glide", "move", "revolve", "roll", "rotate",
    "slide", "spin", "swing", "turn", "twirl", "twist", "whirl", "wind"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 1], .acceptable, .most, none⟩,
    ⟨.alternation [1, 4, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.alternation [5, 3], .acceptable, .all, none⟩]

/-- 51.3.2, Run Verbs. -/
def run : VerbClass where
  number := "51.3.2"
  title := "Run Verbs"
  page := 265
  members :=
    ["amble", "backpack", "bolt", "bounce", "bound", "bowl", "canter", "carom", "cavort", "charge",
    "clamber", "climb", "clump", "coast", "crawl", "creep", "dart", "dash", "dodder", "drift",
    "file", "flit", "float", "fly", "frolic", "gallop", "gambol", "glide", "goosestep",
    "hasten", "hike", "hobble", "hop", "hurry", "hurtle", "inch", "jog", "journey", "jump",
    "leap", "limp", "lollop", "lope", "lumber", "lurch", "march", "meander", "mince", "mosey",
    "nip", "pad", "parade", "perambulate", "plod", "prance", "promenade", "prowl", "race",
    "ramble", "roam", "roll", "romp", "rove", "run", "rush", "sashay", "saunter", "scamper",
    "scoot", "scram", "scramble", "scud", "scurry", "scutter", "scuttle", "shamble", "shuffle",
    "sidle", "skedaddle", "skip", "skitter", "skulk", "sleepwalk", "slide", "slink", "slither",
    "slog", "slouch", "sneak", "somersault", "speed", "stagger", "stomp", "stray", "streak",
    "stride", "stroll", "strut", "stumble", "stump", "swagger", "sweep", "swim", "tack", "tear",
    "tiptoe", "toddle", "totter", "traipse", "tramp", "travel", "trek", "troop", "trot",
    "trudge", "trundle", "vault", "waddle", "wade", "walk", "wander", "whiz", "zigzag",
    "zoom"]
  doubtful := []
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
    ⟨.property .zeroRelatedNominal, .acceptable, .some, none⟩]

/-- 51.4.1, Verbs That Are Vehicle Names. -/
def vehicleName : VerbClass where
  number := "51.4.1"
  title := "Verbs That Are Vehicle Names"
  page := 267
  members :=
    ["balloon", "bicycle", "bike", "boat", "bobsled", "bus", "cab", "canoe", "chariot", "coach",
    "cycle", "dogsled", "ferry", "gondola", "helicopter", "jeep", "jet", "kayak", "moped",
    "motor", "motorbike", "motorcycle", "parachute", "punt", "raft", "rickshaw", "rocket",
    "skate", "skateboard", "ski", "sled", "sledge", "sleigh", "taxi", "toboggan", "tram",
    "trolley", "van", "yacht"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 2], .acceptable, .some, none⟩,
    ⟨.alternation [1, 4, 1], .acceptable, .some, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩]

/-- 51.4.2, Verbs That Are Not Vehicle Names. -/
def nonVehicleName : VerbClass where
  number := "51.4.2"
  title := "Verbs That Are Not Vehicle Names"
  page := 268
  members :=
    ["cruise", "drive", "fly", "oar", "paddle", "pedal", "ride", "row", "sail", "tack"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 2], .acceptable, .some, none⟩,
    ⟨.alternation [1, 4, 1], .acceptable, .some, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩]

/-- 51.5, Waltz Verbs. -/
def waltz : VerbClass where
  number := "51.5"
  title := "Waltz Verbs"
  page := 268
  members :=
    ["boogie", "bop", "cancan", "clog", "conga", "dance", "foxtrot", "jig", "jitterbug", "jive",
    "pirouette", "polka", "quickstep", "rumba", "samba", "shuffle", "squaredance", "tango",
    "tapdance", "waltz"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 2], .acceptable, .all, none⟩,
    ⟨.alternation [7, 5], .acceptable, .all, none⟩,
    ⟨.alternation [7, 1], .acceptable, .all, none⟩]

/-- 51.6, Chase Verbs. -/
def chase : VerbClass where
  number := "51.6"
  title := "Chase Verbs"
  page := 269
  members :=
    ["chase", "follow", "pursue", "shadow", "tail", "track", "trail"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 51.7, Accompany Verbs. -/
def accompany : VerbClass where
  number := "51.7"
  title := "Accompany Verbs"
  page := 270
  members :=
    ["accompany", "conduct", "escort", "guide", "lead", "shepherd"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 52, Avoid Verbs. -/
def avoid : VerbClass where
  number := "52"
  title := "Avoid Verbs"
  page := 270
  members :=
    ["avoid", "boycott", "dodge", "duck", "elude", "evade", "shun", "sidestep"]
  doubtful := ["boycott"]
  properties :=
    []

/-- 53.1, Verbs of Lingering. -/
def linger : VerbClass where
  number := "53.1"
  title := "Verbs of Lingering"
  page := 271
  members :=
    ["dally", "dawdle", "delay", "dither", "hesitate", "linger", "loiter", "tarry"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 53.2, Verbs of Rushing. -/
def rush : VerbClass where
  number := "53.2"
  title := "Verbs of Rushing"
  page := 271
  members :=
    ["hasten", "hurry", "rush"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 3], .acceptable, .all, none⟩]

/-- 54.1, Register Verbs. -/
def register : VerbClass where
  number := "54.1"
  title := "Register Verbs"
  page := 272
  members :=
    ["measure", "read", "register", "total", "weigh"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 54.2, Cost Verbs. -/
def cost : VerbClass where
  number := "54.2"
  title := "Cost Verbs"
  page := 272
  members :=
    ["carry", "cost", "last", "take"]
  doubtful := []
  properties :=
    [⟨.alternation [5, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 54.3, Fit Verbs. -/
def fit : VerbClass where
  number := "54.3"
  title := "Fit Verbs"
  page := 273
  members :=
    ["carry", "contain", "feed", "fit", "hold", "house", "seat", "serve", "sleep", "store", "take",
    "use"]
  doubtful := []
  properties :=
    []

/-- 54.4, Price Verbs. -/
def price : VerbClass where
  number := "54.4"
  title := "Price Verbs"
  page := 273
  members :=
    ["appraise", "assess", "estimate", "fix", "peg", "price", "rate", "value"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 54.5, Bill Verbs. -/
def bill : VerbClass where
  number := "54.5"
  title := "Bill Verbs"
  page := 274
  members :=
    ["bet", "bill", "charge", "fine", "mulct", "overcharge", "save", "spare", "tax", "tip",
    "undercharge", "wager"]
  doubtful := []
  properties :=
    [⟨.alternation [2, 1], .ungrammatical, .all, none⟩,
    ⟨.alternation [2, 14], .ungrammatical, .all, none⟩]

/-- 55.1, Begin Verbs. -/
def begin : VerbClass where
  number := "55.1"
  title := "Begin Verbs"
  page := 274
  members :=
    ["begin", "cease", "commence", "continue", "end", "finish", "halt", "keep", "proceed", "repeat",
    "resume", "start", "stop", "terminate"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2, 3], .acceptable, .some, none⟩]

/-- 55.2, Complete Verbs. -/
def complete : VerbClass where
  number := "55.2"
  title := "Complete Verbs"
  page := 275
  members :=
    ["complete", "discontinue", "initiate", "quit"]
  doubtful := []
  properties :=
    [⟨.alternation [1, 1, 2], .ungrammatical, .all, none⟩]

/-- 56, Weekend Verbs. -/
def weekend : VerbClass where
  number := "56"
  title := "Weekend Verbs"
  page := 275
  members :=
    ["summer", "vacation", "weekend", "winter"]
  doubtful := []
  properties :=
    []

/-- 57, Weather Verbs. -/
def weather : VerbClass where
  number := "57"
  title := "Weather Verbs"
  page := 276
  members :=
    ["blow", "clear", "drizzle", "fog", "freeze", "gust", "hail", "howl", "lightning", "mist",
    "mizzle", "pelt", "pour", "precipitate", "rain", "roar", "shower", "sleet", "snow", "spit",
    "spot", "sprinkle", "storm", "swelter", "teem", "thaw", "thunder"]
  doubtful := []
  properties :=
    []

end Data.VerbClasses.Levin1993.Entry

namespace ArgumentStructure.LevinClass

open Data.VerbClasses

/-- The class's page in the book. -/
def entry : LevinClass → VerbClass
  | .put => Levin1993.Entry.put
  | .putInSpatialConfiguration => Levin1993.Entry.putInSpatialConfiguration
  | .funnel => Levin1993.Entry.funnel
  | .putDirection => Levin1993.Entry.putDirection
  | .pour => Levin1993.Entry.pour
  | .coil => Levin1993.Entry.coil
  | .sprayLoad => Levin1993.Entry.sprayLoad
  | .fill => Levin1993.Entry.fill
  | .butter => Levin1993.Entry.butter
  | .pocket => Levin1993.Entry.pocket
  | .remove => Levin1993.Entry.remove
  | .banish => Levin1993.Entry.banish
  | .clear => Levin1993.Entry.clear
  | .wipeManner => Levin1993.Entry.wipeManner
  | .wipeInstrument => Levin1993.Entry.wipeInstrument
  | .steal => Levin1993.Entry.steal
  | .cheat => Levin1993.Entry.cheat
  | .pit => Levin1993.Entry.pit
  | .debone => Levin1993.Entry.debone
  | .mine => Levin1993.Entry.mine
  | .send => Levin1993.Entry.send
  | .slide => Levin1993.Entry.slide
  | .bringTake => Levin1993.Entry.bringTake
  | .carry => Levin1993.Entry.carry
  | .drive => Levin1993.Entry.drive
  | .pushPull => Levin1993.Entry.pushPull
  | .give => Levin1993.Entry.give
  | .contribute => Levin1993.Entry.contribute
  | .futureHaving => Levin1993.Entry.futureHaving
  | .fulfilling => Levin1993.Entry.fulfilling
  | .equip => Levin1993.Entry.equip
  | .get => Levin1993.Entry.get
  | .obtain => Levin1993.Entry.obtain
  | .exchange => Levin1993.Entry.exchange
  | .berry => Levin1993.Entry.berry
  | .learn => Levin1993.Entry.learn
  | .hold => Levin1993.Entry.hold
  | .keep => Levin1993.Entry.keep
  | .conceal => Levin1993.Entry.conceal
  | .throw => Levin1993.Entry.throw
  | .pelt => Levin1993.Entry.pelt
  | .hit => Levin1993.Entry.hit
  | .swat => Levin1993.Entry.swat
  | .spank => Levin1993.Entry.spank
  | .nonAgentiveImpact => Levin1993.Entry.nonAgentiveImpact
  | .poke => Levin1993.Entry.poke
  | .touch => Levin1993.Entry.touch
  | .cut => Levin1993.Entry.cut
  | .carve => Levin1993.Entry.carve
  | .mix => Levin1993.Entry.mix
  | .amalgamate => Levin1993.Entry.amalgamate
  | .shake => Levin1993.Entry.shake
  | .tape => Levin1993.Entry.tape
  | .cling => Levin1993.Entry.cling
  | .separate => Levin1993.Entry.separate
  | .split => Levin1993.Entry.split
  | .disassemble => Levin1993.Entry.disassemble
  | .differ => Levin1993.Entry.differ
  | .color => Levin1993.Entry.color
  | .imageImpression => Levin1993.Entry.imageImpression
  | .scribble => Levin1993.Entry.scribble
  | .illustrate => Levin1993.Entry.illustrate
  | .transcribe => Levin1993.Entry.transcribe
  | .build => Levin1993.Entry.build
  | .grow => Levin1993.Entry.grow
  | .prepare => Levin1993.Entry.prepare
  | .create => Levin1993.Entry.create
  | .knead => Levin1993.Entry.knead
  | .turn => Levin1993.Entry.turn
  | .performance => Levin1993.Entry.performance
  | .engender => Levin1993.Entry.engender
  | .calve => Levin1993.Entry.calve
  | .appoint => Levin1993.Entry.appoint
  | .characterize => Levin1993.Entry.characterize
  | .dub => Levin1993.Entry.dub
  | .declare => Levin1993.Entry.declare
  | .conjecture => Levin1993.Entry.conjecture
  | .masquerade => Levin1993.Entry.masquerade
  | .orphan => Levin1993.Entry.orphan
  | .captain => Levin1993.Entry.captain
  | .see => Levin1993.Entry.see
  | .sight => Levin1993.Entry.sight
  | .peer => Levin1993.Entry.peer
  | .stimulusSubjectPerception => Levin1993.Entry.stimulusSubjectPerception
  | .amuse => Levin1993.Entry.amuse
  | .admire => Levin1993.Entry.admire
  | .marvel => Levin1993.Entry.marvel
  | .appeal => Levin1993.Entry.appeal
  | .want => Levin1993.Entry.want
  | .long => Levin1993.Entry.long
  | .judgment => Levin1993.Entry.judgment
  | .assessment => Levin1993.Entry.assessment
  | .hunt => Levin1993.Entry.hunt
  | .search => Levin1993.Entry.search
  | .stalk => Levin1993.Entry.stalk
  | .investigate => Levin1993.Entry.investigate
  | .rummage => Levin1993.Entry.rummage
  | .ferret => Levin1993.Entry.ferret
  | .correspond => Levin1993.Entry.correspond
  | .marry => Levin1993.Entry.marry
  | .meet => Levin1993.Entry.meet
  | .transferOfMessage => Levin1993.Entry.transferOfMessage
  | .tell => Levin1993.Entry.tell
  | .mannerOfSpeaking => Levin1993.Entry.mannerOfSpeaking
  | .instrumentOfCommunication => Levin1993.Entry.instrumentOfCommunication
  | .talk => Levin1993.Entry.talk
  | .chitchat => Levin1993.Entry.chitchat
  | .say => Levin1993.Entry.say
  | .complain => Levin1993.Entry.complain
  | .advise => Levin1993.Entry.advise
  | .animalSound => Levin1993.Entry.animalSound
  | .eat => Levin1993.Entry.eat
  | .chew => Levin1993.Entry.chew
  | .gobble => Levin1993.Entry.gobble
  | .devour => Levin1993.Entry.devour
  | .dine => Levin1993.Entry.dine
  | .gorge => Levin1993.Entry.gorge
  | .feed => Levin1993.Entry.feed
  | .hiccup => Levin1993.Entry.hiccup
  | .breathe => Levin1993.Entry.breathe
  | .exhale => Levin1993.Entry.exhale
  | .nonverbalExpression => Levin1993.Entry.nonverbalExpression
  | .wink => Levin1993.Entry.wink
  | .crane => Levin1993.Entry.crane
  | .curtsey => Levin1993.Entry.curtsey
  | .snooze => Levin1993.Entry.snooze
  | .flinch => Levin1993.Entry.flinch
  | .bodyInternalStateOfExistence => Levin1993.Entry.bodyInternalStateOfExistence
  | .suffocate => Levin1993.Entry.suffocate
  | .pain => Levin1993.Entry.pain
  | .tingle => Levin1993.Entry.tingle
  | .hurt => Levin1993.Entry.hurt
  | .changeOfBodilyState => Levin1993.Entry.changeOfBodilyState
  | .dress => Levin1993.Entry.dress
  | .groom => Levin1993.Entry.groom
  | .floss => Levin1993.Entry.floss
  | .braid => Levin1993.Entry.braid
  | .simpleDressing => Levin1993.Entry.simpleDressing
  | .dressingWell => Levin1993.Entry.dressingWell
  | .beingDressed => Levin1993.Entry.beingDressed
  | .murder => Levin1993.Entry.murder
  | .poison => Levin1993.Entry.poison
  | .lightEmission => Levin1993.Entry.lightEmission
  | .soundEmission => Levin1993.Entry.soundEmission
  | .smellEmission => Levin1993.Entry.smellEmission
  | .substanceEmission => Levin1993.Entry.substanceEmission
  | .destroy => Levin1993.Entry.destroy
  | .break_ => Levin1993.Entry.break_
  | .bend => Levin1993.Entry.bend
  | .cooking => Levin1993.Entry.cooking
  | .otherChangeOfState => Levin1993.Entry.otherChangeOfState
  | .entitySpecificChangeOfState => Levin1993.Entry.entitySpecificChangeOfState
  | .calibratableChangeOfState => Levin1993.Entry.calibratableChangeOfState
  | .lodge => Levin1993.Entry.lodge
  | .exist => Levin1993.Entry.exist
  | .entitySpecificModeOfBeing => Levin1993.Entry.entitySpecificModeOfBeing
  | .modeOfBeingInvolvingMotion => Levin1993.Entry.modeOfBeingInvolvingMotion
  | .soundExistence => Levin1993.Entry.soundExistence
  | .swarm => Levin1993.Entry.swarm
  | .herd => Levin1993.Entry.herd
  | .bulge => Levin1993.Entry.bulge
  | .spatialConfiguration => Levin1993.Entry.spatialConfiguration
  | .meander => Levin1993.Entry.meander
  | .contiguousLocation => Levin1993.Entry.contiguousLocation
  | .appear => Levin1993.Entry.appear
  | .reflexiveAppearance => Levin1993.Entry.reflexiveAppearance
  | .disappearance => Levin1993.Entry.disappearance
  | .occurrence => Levin1993.Entry.occurrence
  | .bodyInternalMotion => Levin1993.Entry.bodyInternalMotion
  | .assumePosition => Levin1993.Entry.assumePosition
  | .inherentlyDirectedMotion => Levin1993.Entry.inherentlyDirectedMotion
  | .leave => Levin1993.Entry.leave
  | .roll => Levin1993.Entry.roll
  | .run => Levin1993.Entry.run
  | .vehicleName => Levin1993.Entry.vehicleName
  | .nonVehicleName => Levin1993.Entry.nonVehicleName
  | .waltz => Levin1993.Entry.waltz
  | .chase => Levin1993.Entry.chase
  | .accompany => Levin1993.Entry.accompany
  | .avoid => Levin1993.Entry.avoid
  | .linger => Levin1993.Entry.linger
  | .rush => Levin1993.Entry.rush
  | .register => Levin1993.Entry.register
  | .cost => Levin1993.Entry.cost
  | .fit => Levin1993.Entry.fit
  | .price => Levin1993.Entry.price
  | .bill => Levin1993.Entry.bill
  | .begin => Levin1993.Entry.begin
  | .complete => Levin1993.Entry.complete
  | .weekend => Levin1993.Entry.weekend
  | .weather => Levin1993.Entry.weather

end ArgumentStructure.LevinClass
