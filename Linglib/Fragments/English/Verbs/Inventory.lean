module

public import Linglib.Fragments.English.Verbs.Aspectual
public import Linglib.Fragments.English.Verbs.Attitude
public import Linglib.Fragments.English.Verbs.Communication
public import Linglib.Fragments.English.Verbs.Causative
public import Linglib.Fragments.English.Verbs.ChangeOfState
public import Linglib.Fragments.English.Verbs.Psych
public import Linglib.Fragments.English.Verbs.Levin
public import Linglib.Fragments.English.Verbs.Ditransitive

/-!
# The English verb inventory

This file collects every English verb entry into one list, in the order of the class files, and
defines the two voices, the active and the periphrastic passive, the auxiliary *be* with the
past participle, the patient the subject and the agent demoted to an optional *by*-phrase.

## References

* [levin-1993]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree

/-! ### The inventory -/

/-- Every entry of the lexicon, in file order. -/
def verbs : List Verb :=
  [sleep, sneeze, run, arrive, come, eat, kick, aim, give, put,
   weigh, cover, measure, buy, meet, set_, clarify, sell,
   leave, see, know, regret, realize, discover, notice, stop,
   quit, start, begin_, continue_, keep, manage, fail, try_,
   persuade, promise, remember, forget, neglect, believe, think, doubt, want,
   intend, decide_, hope, pray, expect, wish, fear, dread,
   worry, seem, cause, make, let_, have_caus, get_caus, force,
   prevent, kill, break_, tear_, crack, dent, scratch, shatter,
   burn, destroy, melt, activate, affect, change, damage, eliminate,
   hurt, restore, trigger, bury, drop, lift, lock, shut,
   spread, stretch, switch, devour, drink, read, build, write,
   do_, sweep, sweep_instr, say, tell, claim, reveal, acknowledge, admit,
   announce, confess, inform, suggest, pretend, confirm, demonstrate, establish,
   prove, whisper, murmur, shout, cry, scream, mumble, mutter,
   shriek, yell, groan, grumble, hiss, sigh, whimper, snap,
   speak, talk, wonder, ask, investigate, depend_on, remember_rog, forget_rog,
   dare, bother, hesitate, venture, condescend, happen, enjoy, like,
   love, hate, admire, envy, respect, value, fear_np, dread_np,
   frighten, amuse, fascinate, irritate, annoy, bore, charm, impress,
   concern, interest, surprise, scare, delight, embarrass, upset_psych, disgust,
   shock, confuse, disappoint, worry_eventive, worry_stative, please_psych, trouble, puzzle,
   chase, hit, push, pull, shove, tug, yank, jerk,
   wrench, fling, slam, punch, smack, thump, bang, thrash,
   hammer, scrape, wipe, carry, drag, call, place, water,
   pour, spray, load, remove, clean, steal, send, drive,
   donate, obtain, trade, learn, hold, hide, throw, poke,
   touch, cut, chop, mix, separate, paint, draw, create,
   weave, grow, perform, appoint, hear, blame, evaluate, marry,
   bark, breathe, laugh, cough, hiccup, blink, knock, tap,
   flash, flinch, dress, drown, glow, buzz, rumble, bleed,
   freeze, heat, bend, boil, rust, increase, straighten, flatten,
   open_, lengthen, widen, cool, warm, exist, appear, fidget,
   wiggle, wriggle, sit, stand, walk, swim, fly, roll, float, avoid,
   linger, rush, rain, charge, cost, fine, tip, pay,
   strike_, forgive, spare, deny, permit, assign, begrudge, bet,
   serve, teach, feed, show_, award, forward_, grant, offer,
   reserve, pass, hand, mail, lend]

/-- Regular forms follow from the base, with the consonant doubled in *stopped* and *regretted*
and the suffix on the verb in *depends on*, and a listed form stands in the cell it is listed
for. -/
example :
    kick.realize .past = "kicked" ∧ stop.realize .past = "stopped" ∧
      regret.realize .presentParticiple = "regretting" ∧ carry.realize .thirdSg = "carries" ∧
      depend_on.realize .thirdSg = "depends on" ∧ wakeUp.realize .past = "woke up" ∧
      run.realize .past = "ran" ∧ run.realize .pastParticiple = "run" ∧
      run.realize .presentParticiple = "running" ∧ sleep.realize .pastParticiple = "slept" ∧
      have_caus.realize .thirdSg = "has" ∧ go.realize .thirdSg = "goes" := by
  decide

/-! ### Voice -/

/-- The passive, marked by the auxiliary *be* with the past participle,
`Verb.passiveParticiple`. -/
def passive : Voice := Voice.passive.marked [.free "be"]

/-- The active and the passive. -/
def voices : Finset Voice := {.active, passive}

end English.Verbs
