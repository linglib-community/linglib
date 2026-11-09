module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English ditransitive verbs

These are the ditransitive verbs of Bruening's study of implicit arguments, from *charge* and
*pay* to *hand* and *lend*. Their participants are the agent, the recipient and the theme,
numbered 0, 1 and 2, and a diathesis with an implicit argument is one of the verb's frames with
that argument left unexpressed (`ArgumentFrame.leaveImplicit`).

## References

* [bruening-2021]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Verbs without the prepositional frame -/

/-- "charge" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def charge : Verb where
  morphs := [.root "charge"]
  levin := some Levin1993.Index.charge
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment

/-- "cost" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def cost : Verb where
  morphs := [.root "cost"]
  levin := some Levin1993.Index.cost
  past := "cost"
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .state

/-- "fine" — the second object may be implicit, an indefinite; the first may not
(*They fined an astronomical amount*). -/
def fine : Verb where
  morphs := [.root "fine"]
  levin := some Levin1993.Index.fine
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 1 (some .indef)]
  vendlerClass := some .accomplishment

/-- "tip" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def tip : Verb where
  morphs := [.root "tip"]
  levin := some Levin1993.Index.tip
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment

/-- "strike" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def strike_ : Verb where
  morphs := [.root "strike"]
  levin := some Levin1993.Index.strike
  past := "struck"
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .achievement
  senseTag := .default

/-- "forgive" — either object may be implicit, each a definite. -/
def forgive : Verb where
  morphs := [.root "forgive"]
  levin := some Levin1993.Index.forgive
  past := "forgave"
  pastPart := "forgiven"
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .def),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment

/-- "spare" — the second object may be implicit, a definite; the first may not. -/
def spare : Verb where
  morphs := [.root "spare"]
  levin := some Levin1993.Index.spare
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 1 (some .def)]
  vendlerClass := some .accomplishment

/-- "deny" — the first object may be implicit, a definite; the second may not. -/
def deny : Verb where
  morphs := [.root "deny"]
  levin := some Levin1993.Index.deny
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment

/-- "permit" — the first object may be implicit, a definite; the second may not. -/
def permit : Verb where
  morphs := [.root "permit"]
  levin := none
  doubling := true
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment

/-- "begrudge" — neither object may be implicit. -/
def begrudge : Verb where
  morphs := [.root "begrudge"]
  levin := none
  valency := .ofFrame ArgumentFrame.np_np
  vendlerClass := some .state

/-- "bet" — neither object may be implicit. -/
def bet : Verb where
  morphs := [.root "bet"]
  levin := some Levin1993.Index.bet
  past := "bet"
  valency := .ofFrame ArgumentFrame.np_np
  vendlerClass := some .accomplishment

/-! ### Alternating verbs -/

/-- "pay" — the direct object may be implicit in the double object frame only, an indefinite;
the first object may be implicit, a definite. -/
def pay : Verb where
  morphs := [.root "pay"]
  levin := some Levin1993.Index.pay
  past := "paid"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2]),
     (ArgumentFrame.np_np.leaveImplicit 0 (some .def), [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "assign" — the goal may be implicit, a definite, as a first object or as a PP; the theme may
not. -/
def assign : Verb where
  morphs := [.root "assign"]
  levin := some Levin1993.Index.assign
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 0 (some .def), [0, 1, 2]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "serve" — the direct object may be implicit in the double object frame only, an indefinite;
the PP may be implicit, a definite. -/
def serve : Verb where
  morphs := [.root "serve"]
  levin := some Levin1993.Index.serve
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "teach" — the direct object may be implicit in the double object frame only, and the PP may
be implicit, each an indefinite. -/
def teach : Verb where
  morphs := [.root "teach"]
  levin := some Levin1993.Index.teach
  past := "taught"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .indef), [0, 2, 1])]
  vendlerClass := some .activity

/-- "feed" — the direct object may be implicit in the double object frame only, an
indefinite; the goal may not. -/
def feed : Verb where
  morphs := [.root "feed"]
  levin := some Levin1993.Index.feed
  past := "fed"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2])]
  vendlerClass := some .activity

/-- "show" — the direct object may be implicit in the double object frame only, a definite
(*Show me*); the goal may not. -/
def show_ : Verb where
  morphs := [.root "show"]
  levin := some Levin1993.Index.«show»
  pastPart := "shown"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .def), [0, 1, 2])]
  vendlerClass := some .accomplishment

/-- "award" — the PP may be implicit, a definite; the theme may not. -/
def award : Verb where
  morphs := [.root "award"]
  levin := some Levin1993.Index.award
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 2, 1]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "forward" — the PP may be implicit, a definite; the theme may not. -/
def forward_ : Verb where
  morphs := [.root "forward"]
  levin := some Levin1993.Index.forward
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 2, 1]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "grant" — the PP may be implicit, a definite; the theme may not. -/
def grant : Verb where
  morphs := [.root "grant"]
  levin := some Levin1993.Index.grant
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "offer" — the PP may be implicit, a definite; the theme may not. -/
def offer : Verb where
  morphs := [.root "offer"]
  levin := some Levin1993.Index.offer
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "reserve" — the PP may be implicit, a definite; the theme may not. -/
def reserve : Verb where
  morphs := [.root "reserve"]
  levin := some Levin1993.Index.reserve
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_) (some .ben), [0, 2, 1]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "pass" — the direct object may be implicit in the prepositional frame only, a definite
(*She wouldn't pass to me*); the PP may be implicit, an indefinite. Its theme is participant 1
and its goal participant 2. -/
def pass : Verb where
  morphs := [.root "pass"]
  levin := some Levin1993.Index.pass
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 0 (some .def),
       [0, 1, 2]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .indef), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "hand" — Levin 11.1 Send verbs; neither argument may be implicit. -/
def hand : Verb where
  morphs := [.root "hand"]
  levin := some Levin1993.Index.hand
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "mail" — transitive, ditransitive, or with a *to*-phrase (*Paul mailed a letter*). -/
def mail : Verb where
  morphs := [.root "mail"]
  levin := some Levin1993.Index.mail
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2])]

/-- "lend" — neither argument may be implicit. -/
def lend : Verb where
  morphs := [.root "lend"]
  levin := some Levin1993.Index.lend
  past := "lent"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 2, 1])]
  vendlerClass := some .accomplishment

end English.Verbs
