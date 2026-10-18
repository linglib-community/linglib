module

/-!
# Chuj Root Classes

Root lexicon for Chuj (Q'anjob'alan, Mayan): the four Mayanist root
classes and the root inventory of Coon's "Building verbs in Chuj:
Consequences for the nature of roots."

## Main declarations

* `Chuj.RootClass`: the four morphosyntactic root classes (√TV, √ITV,
  √POS, √NOM), identified by surface distribution.
* `Chuj.ChujRoot`: a root entry — form, gloss, and class label.
* `Chuj.allRoots` and the per-class lists `tvRoots`, `itvRoots`,
  `posRoots`, `nomRoots`, derived by filtering on the class label.

## Implementation notes

The entry carries only the distributional class label; the theoretical
coordinates (Coon's (3): semantic type, valency, transitive-Voice
licensing) are functions of the class, `RootClass.ty`, `RootClass.valency` and
`RootClass.LicensesTransitiveVoice`, in `Studies/Coon2019.lean`.

## References

* [coon-2019]
-/

@[expose] public section

namespace Chuj

/-- The four morphosyntactic root classes in Chuj, identified by
    surface distribution (which suffixes they combine with, whether
    they form bare transitive stems). Labels follow [coon-2019]. -/
inductive RootClass where
  /-- Transitive roots: form bare transitive stems. -/
  | tv
  /-- Intransitive roots: take null v in intransitive stems. -/
  | itv
  /-- Positional roots: require -w for verbalization. -/
  | pos
  /-- Nominal roots: require -w for verbalization. -/
  | nom
  deriving DecidableEq, Repr

/-- A Chuj root entry from [coon-2019]'s lexicon. -/
structure ChujRoot where
  /-- Chuj root form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- Morphosyntactic root class -/
  class' : RootClass
  deriving Repr, BEq, DecidableEq

/-! ### √TV roots (Table (5), p. 39) -/

def xik   : ChujRoot := ⟨"xik",   "chop", .tv⟩
def chonh : ChujRoot := ⟨"chonh", "sell", .tv⟩
def jax   : ChujRoot := ⟨"jax",   "grind", .tv⟩
def chel  : ChujRoot := ⟨"chel",  "hug", .tv⟩
def tek'  : ChujRoot := ⟨"tek'",  "kick", .tv⟩

/-! ### √TV roots from examples (not in Table (5)) -/

def mak'  : ChujRoot := ⟨"mak'",  "hit", .tv⟩    -- ex. (55b), p. 65
def il    : ChujRoot := ⟨"il",    "see", .tv⟩     -- ex. (10d), p. 41
def ch'ak : ChujRoot := ⟨"ch'ak", "fell", .tv⟩   -- ex. (63a), p. 68
def b'o'  : ChujRoot := ⟨"b'o'",  "make", .tv⟩   -- ex. (62), p. 68
def man   : ChujRoot := ⟨"man",   "buy", .tv⟩    -- ex. (59a), p. 67
def kal   : ChujRoot := ⟨"kal",   "stir", .tv⟩   -- ex. (29a), p. 52
def tzil  : ChujRoot := ⟨"tzil",  "tear", .tv⟩   -- ex. (35a), p. 54
def yam   : ChujRoot := ⟨"yam",   "catch", .tv⟩  -- ex. (60a), p. 67
def mak   : ChujRoot := ⟨"mak",   "close", .tv⟩  -- ex. (70a), p. 71

/-! ### √ITV roots (Table (5), p. 39) -/

def b'at  : ChujRoot := ⟨"b'at",  "go", .itv⟩
def way   : ChujRoot := ⟨"way",   "sleep", .itv⟩
def k'ey  : ChujRoot := ⟨"k'ey",  "ascend", .itv⟩
def jaw   : ChujRoot := ⟨"jaw",   "arrive", .itv⟩
def ok'   : ChujRoot := ⟨"ok'",   "cry", .itv⟩

/-! ### √ITV roots from examples (not in Table (5)) -/

def b'ey  : ChujRoot := ⟨"b'ey",  "walk", .itv⟩     -- ex. (7c), p. 40
def ul    : ChujRoot := ⟨"ul",    "dissolve", .itv⟩ -- ex. (48a), p. 61
def el    : ChujRoot := ⟨"el",    "leave", .itv⟩    -- ex. (57), p. 66

/-! ### √POS roots (Table (5), p. 39; Table (20), p. 47) -/

def chot  : ChujRoot := ⟨"chot",  "crouched", .pos⟩
def jenh  : ChujRoot := ⟨"jenh",  "outstretched", .pos⟩
def chek' : ChujRoot := ⟨"chek'", "leaning", .pos⟩
def lich' : ChujRoot := ⟨"lich'", "extended", .pos⟩
def b'ul  : ChujRoot := ⟨"b'ul",  "gathered", .pos⟩
def kot   : ChujRoot := ⟨"kot",   "on four legs", .pos⟩   -- Table (20)
def tel   : ChujRoot := ⟨"tel",   "lying down", .pos⟩     -- Table (20)
def chet  : ChujRoot := ⟨"chet",  "on two legs", .pos⟩    -- Table (20)

/-! ### √NOM roots (Table (5), p. 39; Table (17), p. 46) -/

def pat      : ChujRoot := ⟨"pat",      "house", .nom⟩
def k'atzitz : ChujRoot := ⟨"k'atzitz", "wood", .nom⟩
def ixim     : ChujRoot := ⟨"ixim",     "corn", .nom⟩
def winak    : ChujRoot := ⟨"winak",    "man", .nom⟩
def chanhal  : ChujRoot := ⟨"chanhal",  "dance", .nom⟩
def at'is    : ChujRoot := ⟨"at'is",    "sneeze", .nom⟩   -- Table (17)
def tz'ib'   : ChujRoot := ⟨"tz'ib'",   "writing", .nom⟩  -- Table (17)
def patan    : ChujRoot := ⟨"patan",    "cleared land", .nom⟩ -- Table (17)

/-! ### Root lists -/

/-- The full root inventory. -/
def allRoots : List ChujRoot :=
  [xik, chonh, jax, chel, tek', mak', il, ch'ak, b'o', man, kal, tzil, yam, mak,
   b'at, way, k'ey, jaw, ok', b'ey, ul, el,
   chot, jenh, chek', lich', b'ul, kot, tel, chet,
   pat, k'atzitz, ixim, winak, chanhal, at'is, tz'ib', patan]

/-- All √TV roots. -/
def tvRoots : List ChujRoot := allRoots.filter (·.class' == .tv)

/-- All √ITV roots. -/
def itvRoots : List ChujRoot := allRoots.filter (·.class' == .itv)

/-- All √POS roots. -/
def posRoots : List ChujRoot := allRoots.filter (·.class' == .pos)

/-- All √NOM roots. -/
def nomRoots : List ChujRoot := allRoots.filter (·.class' == .nom)

end Chuj
