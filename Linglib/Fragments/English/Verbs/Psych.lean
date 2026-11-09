module

public import Linglib.Fragments.English.Verbs.Attitude

/-!
# English psychological verbs

This file defines the English psychological and agent–patient verbs of Solstad and Bott's
study: the agent-experiencer verbs *enjoy*, *like*, *love*, *hate* and their kin, the
stimulus-experiencer verbs *frighten*, *amuse*, *fascinate* and the rest, and the agent-patient
verbs of contact and motion, *chase*, *hit*, *push*, *pull* and their kin.

## References

* [levin-1993]
* [levin-2026]
* [solstad-bott-2024]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Agent-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.2 (admire). Subject = experiencer, object = stimulus.
    NP1 (subject) IC bias. -/

/-- "enjoy" — AgExp verb (experiencer-subject) -/
def enjoy : Verb where
  morphs := [.root "enjoy"]
  levin := some Levin1993.Index.enjoy
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "like" — AgExp verb (experiencer-subject) -/
def like : Verb where
  morphs := [.root "like"]
  levin := some Levin1993.Index.like
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "love" — AgExp verb (experiencer-subject) -/
def love : Verb where
  morphs := [.root "love"]
  levin := some Levin1993.Index.love
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "hate" — AgExp verb (experiencer-subject) -/
def hate : Verb where
  morphs := [.root "hate"]
  levin := some Levin1993.Index.hate
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "admire" — AgExp verb (experiencer-subject) -/
def admire : Verb where
  morphs := [.root "admire"]
  levin := some Levin1993.Index.admire
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "envy" — AgExp verb (experiencer-subject).
    DOC-only ditransitive ("He envies me the car"). Implicit goal is
    definite (familiar). Implicit second obj is indefinite. -/
def envy : Verb where
  morphs := [.root "envy"]
  levin := some Levin1993.Index.envy
  valency := .ofFrames
    [ArgumentFrame.np,
     ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .state

/-- "respect" — AgExp verb (experiencer-subject) -/
def respect : Verb where
  morphs := [.root "respect"]
  levin := some Levin1993.Index.respect
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "value" — AgExp verb (experiencer-subject) -/
def value : Verb where
  morphs := [.root "value"]
  levin := some Levin1993.Index.value
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "fear" (NP complement) — Class I psych verb (B&R *temere*).
    "John fears snakes." Experiencer subject, stimulus object.
    Note: `fear` (attitude verb, clausal complement) is defined separately. -/
def fear_np : Verb where
  morphs := [.root "fear"]
  levin := some Levin1993.Index.fear
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "dread" (NP complement) — Class I psych verb.
    "John dreads exams." Note: `dread` (attitude, clausal) defined separately. -/
def dread_np : Verb where
  morphs := [.root "dread"]
  levin := some Levin1993.Index.dread
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-! ### Stimulus-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.1 (amuse). Subject = stimulus, object = experiencer.
    NP2 (object) IC bias. -/

/-- "frighten" — StimExp verb (stimulus subject). -/
def frighten : Verb where
  morphs := [.root "frighten"]
  levin := some Levin1993.Index.frighten
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "amuse" — StimExp verb (stimulus subject). -/
def amuse : Verb where
  morphs := [.root "amuse"]
  levin := some Levin1993.Index.amuse
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "fascinate" — StimExp verb (stimulus subject). -/
def fascinate : Verb where
  morphs := [.root "fascinate"]
  levin := some Levin1993.Index.fascinate
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "irritate" — StimExp verb (stimulus subject). -/
def irritate : Verb where
  morphs := [.root "irritate"]
  levin := some Levin1993.Index.irritate
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "annoy" — StimExp verb (stimulus subject). -/
def annoy : Verb where
  morphs := [.root "annoy"]
  levin := some Levin1993.Index.annoy
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "bore" — StimExp verb (stimulus subject). -/
def bore : Verb where
  morphs := [.root "bore"]
  levin := some Levin1993.Index.bore
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "charm" — StimExp verb (stimulus subject). -/
def charm : Verb where
  morphs := [.root "charm"]
  levin := some Levin1993.Index.charm
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "impress" — StimExp verb (stimulus subject). -/
def impress : Verb where
  morphs := [.root "impress"]
  levin := some Levin1993.Index.impress
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "concern" — stative Class II psych verb. -/
def concern : Verb where
  morphs := [.root "concern"]
  levin := some Levin1993.Index.concern
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "interest" — stative Class II psych verb. -/
def interest : Verb where
  morphs := [.root "interest"]
  levin := some Levin1993.Index.interest
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "surprise" — eventive Class II (Levin 31.1). "The news surprised John." -/
def surprise : Verb where
  morphs := [.root "surprise"]
  levin := some Levin1993.Index.surprise
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "scare" — eventive Class II (Levin 31.1). "The noise scared John." -/
def scare : Verb where
  morphs := [.root "scare"]
  levin := some Levin1993.Index.scare
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "delight" — eventive Class II (Levin 31.1). "The gift delighted Mary." -/
def delight : Verb where
  morphs := [.root "delight"]
  levin := some Levin1993.Index.delight
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "embarrass" — eventive Class II (Levin 31.1). "The remark embarrassed John." -/
def embarrass : Verb where
  morphs := [.root "embarrass"]
  levin := some Levin1993.Index.embarrass
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "upset" — eventive Class II (Levin 31.1). "The news upset Mary." -/
def upset_psych : Verb where
  morphs := [.root "upset"]
  levin := some Levin1993.Index.upset
  past := "upset"
  doubling := true
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "disgust" — eventive Class II (Levin 31.1). "The smell disgusted John." -/
def disgust : Verb where
  morphs := [.root "disgust"]
  levin := some Levin1993.Index.disgust
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "shock" — eventive Class II (Levin 31.1). "The revelation shocked everyone." -/
def shock : Verb where
  morphs := [.root "shock"]
  levin := some Levin1993.Index.shock
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "confuse" — eventive Class II (Levin 31.1). "The instructions confused John." -/
def confuse : Verb where
  morphs := [.root "confuse"]
  levin := some Levin1993.Index.confuse
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "disappoint" — eventive Class II (Levin 31.1). "The result disappointed Mary." -/
def disappoint : Verb where
  morphs := [.root "disappoint"]
  levin := some Levin1993.Index.disappoint
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "worry" (eventive) — Class II. "The noise worried John."
    Note: `worry` (attitude, clausal) defined separately. -/
def worry_eventive : Verb where
  morphs := [.root "worry"]
  levin := some Levin1993.Index.worry
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinExcluded := {LevinClass.marvel}

/-- "worry" (stative) — Class II. "The situation worries John." -/
def worry_stative : Verb where
  morphs := [.root "worry"]
  levin := some Levin1993.Index.worry
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinExcluded := {LevinClass.marvel}

/-- "please" — stative Class II. "The idea pleases John." Related to B&R Class III It.
    *piacere*. -/
def please_psych : Verb where
  morphs := [.root "please"]
  levin := some Levin1993.Index.please
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "trouble" — stative Class II. "The thought troubles John." -/
def trouble : Verb where
  morphs := [.root "trouble"]
  levin := some Levin1993.Index.trouble
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "puzzle" — stative Class II. "The problem puzzles John." -/
def puzzle : Verb where
  morphs := [.root "puzzle"]
  levin := some Levin1993.Index.puzzle
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-! ### Agent-patient verbs ([solstad-bott-2024]) -/

/-! Agent-patient verbs with full agentive subjects. NP1 IC bias (default).
    "kick" already defined above. -/

/-- "chase" — AgPat verb (Levin 51.6) -/
def chase : Verb where
  morphs := [.root "chase"]
  levin := some Levin1993.Index.chase
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative

/-- "hit" — AgPat verb (Levin 18.1) -/
def hit : Verb where
  morphs := [.root "hit"]
  levin := some Levin1993.Index.hit
  past := "hit"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .activity

/-- "push" — AgPat verb (Levin 12) -/
def push : Verb where
  morphs := [.root "push"]
  levin := some Levin1993.Index.push
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  incrementality := some .cumulative

/-- "pull" — AgPat verb (Levin 12) -/
def pull : Verb where
  morphs := [.root "pull"]
  levin := some Levin1993.Index.pull
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  incrementality := some .cumulative

/-- "shove" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def shove : Verb where
  morphs := [.root "shove"]
  levin := some Levin1993.Index.shove
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity

/-- "tug" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def tug : Verb where
  morphs := [.root "tug"]
  levin := some Levin1993.Index.tug
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity

/-- "yank" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def yank : Verb where
  morphs := [.root "yank"]
  levin := some Levin1993.Index.yank
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity

/-- "jerk" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def jerk : Verb where
  morphs := [.root "jerk"]
  levin := some Levin1993.Index.jerk
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity

/-- "wrench" — verb of exerting force for [levin-2026] (31); not among the
    members of Levin's §12. -/
def wrench : Verb where
  morphs := [.root "wrench"]
  levin := some Levin1993.Index.wrench
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity


/-- "fling" — Levin 17.1 Throw verbs; a verb of exerting force for
    [levin-2026] (31). Irregular past. -/
def fling : Verb where
  morphs := [.root "fling"]
  levin := some Levin1993.Index.fling
  past := "flung"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2])]
  vendlerClass := some .activity

/-- "slam" — Levin 17.1 Throw verbs; a hitting verb for [levin-2026] (32a).
    Irregular doubling. -/
def slam : Verb where
  morphs := [.root "slam"]
  levin := some Levin1993.Index.slam
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .activity

/-- "punch" — Levin 18.2 Swat verbs; a hitting verb for [levin-2026] (32a). -/
def punch : Verb where
  morphs := [.root "punch"]
  levin := some Levin1993.Index.punch
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1])]
  vendlerClass := some .activity

/-- "smack" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def smack : Verb where
  morphs := [.root "smack"]
  levin := some Levin1993.Index.smack
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3]),
     (ArgumentFrame.np, [3, 1])]
  vendlerClass := some .activity

/-- "thump" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def thump : Verb where
  morphs := [.root "thump"]
  levin := some Levin1993.Index.thump
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .activity

/-- "bang" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def bang : Verb where
  morphs := [.root "bang"]
  levin := some Levin1993.Index.bang
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .activity

/-- "thrash" — Levin 18.3 Spank verbs; a hitting verb for [levin-2026] (32a). -/
def thrash : Verb where
  morphs := [.root "thrash"]
  levin := some Levin1993.Index.thrash
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.on) (some .sup)]
  vendlerClass := some .activity

/-- "hammer" — Levin 18.1 Hit verbs. -/
def hammer : Verb where
  morphs := [.root "hammer"]
  levin := some Levin1993.Index.hammer
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .activity

/-- "scrape" — verb of surface contact, wiping (Levin 10.4,
    [levin-2026] (32b)). In intr-push-open, enters through
    surface-contact sense, not removing sense. -/
def scrape : Verb where
  morphs := [.root "scrape"]
  levin := some Levin1993.Index.scrape
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_spatialPP, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .activity

/-- "wipe" — Levin 10.4 Wipe verbs, manner subclass. -/
def wipe : Verb where
  morphs := [.root "wipe"]
  levin := some Levin1993.Index.wipe
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_spatialPP, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .activity

/-- "carry" — AgPat verb (Levin 11.4) -/
def carry : Verb where
  morphs := [.root "carry"]
  levin := some Levin1993.Index.carry
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .activity
  incrementality := some .cumulative

/-- "drag" — AgPat verb (Levin 11.4/12) -/
def drag : Verb where
  morphs := [.root "drag"]
  levin := some Levin1993.Index.drag
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .activity
  incrementality := some .cumulative

/-- "call" — AgPat verb (communication + agent-patient frame) -/
def call : Verb where
  morphs := [.root "call"]
  levin := some Levin1993.Index.call
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity

end English.Verbs
