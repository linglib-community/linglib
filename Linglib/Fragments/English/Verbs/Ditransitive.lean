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

open ArgumentStructure Aspect Degree

/-! ### Verbs without the prepositional frame -/

/-- "charge" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def charge : Verb where
  morphs := [.root "charge"]
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .equip, .run}

/-- "cost" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def cost : Verb where
  morphs := [.root "cost"]
  past := "cost"
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .state
  levinClasses := {LevinClass.cost}

/-- "fine" — the second object may be implicit, an indefinite; the first may not
(*They fined an astronomical amount*). -/
def fine : Verb where
  morphs := [.root "fine"]
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 1 (some .indef)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .judgment}

/-- "tip" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def tip : Verb where
  morphs := [.root "tip"]
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .throw}

/-- "strike" — either object may be implicit, the second as an indefinite and the first as a
definite. -/
def strike_ : Verb where
  morphs := [.root "strike"]
  past := "struck"
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .indef),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .achievement
  senseTag := .default
  levinClasses := {LevinClass.amuse, .hit, .soundEmission}

/-- "forgive" — either object may be implicit, each a definite. -/
def forgive : Verb where
  morphs := [.root "forgive"]
  past := "forgave"
  pastPart := "forgiven"
  valency := .ofFrames
    [ArgumentFrame.np_np,
     ArgumentFrame.np_np.leaveImplicit 1 (some .def),
     ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.judgment}

/-- "spare" — the second object may be implicit, a definite; the first may not. -/
def spare : Verb where
  morphs := [.root "spare"]
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 1 (some .def)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill}

/-- "deny" — the first object may be implicit, a definite; the second may not. -/
def deny : Verb where
  morphs := [.root "deny"]
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture}

/-- "permit" — the first object may be implicit, a definite; the second may not. -/
def permit : Verb where
  morphs := [.root "permit"]
  doubling := true
  valency := .ofFrames [ArgumentFrame.np_np, ArgumentFrame.np_np.leaveImplicit 0 (some .def)]
  vendlerClass := some .accomplishment

/-- "begrudge" — neither object may be implicit. -/
def begrudge : Verb where
  morphs := [.root "begrudge"]
  valency := .ofFrame ArgumentFrame.np_np
  vendlerClass := some .state

/-- "bet" — neither object may be implicit. -/
def bet : Verb where
  morphs := [.root "bet"]
  past := "bet"
  valency := .ofFrame ArgumentFrame.np_np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill}

/-! ### Alternating verbs -/

/-- "pay" — the direct object may be implicit in the double object frame only, an indefinite;
the first object may be implicit, a definite. -/
def pay : Verb where
  morphs := [.root "pay"]
  past := "paid"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2]),
     (ArgumentFrame.np_np.leaveImplicit 0 (some .def), [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "assign" — the goal may be implicit, a definite, as a first object or as a PP; the theme may
not. -/
def assign : Verb where
  morphs := [.root "assign"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 0 (some .def), [0, 1, 2]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving}

/-- "serve" — the direct object may be implicit in the double object frame only, an indefinite;
the PP may be implicit, a definite. -/
def serve : Verb where
  morphs := [.root "serve"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.fit, .fulfilling, .give, .masquerade}

/-- "teach" — the direct object may be implicit in the double object frame only, and the PP may
be implicit, each an indefinite. -/
def teach : Verb where
  morphs := [.root "teach"]
  past := "taught"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .indef), [0, 2, 1])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.transferOfMessage}

/-- "feed" — the direct object may be implicit in the double object frame only, an
indefinite; the goal may not. -/
def feed : Verb where
  morphs := [.root "feed"]
  past := "fed"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 1, 2])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.feed, .fit, .give, .gorge}

/-- "show" — the direct object may be implicit in the double object frame only, a definite
(*Show me*); the goal may not. -/
def show_ : Verb where
  morphs := [.root "show"]
  pastPart := "shown"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .def), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .crane, .reflexiveAppearance, .transferOfMessage}

/-- "award" — the PP may be implicit, a definite; the theme may not. -/
def award : Verb where
  morphs := [.root "award"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving}

/-- "forward" — the PP may be implicit, a definite; the theme may not. -/
def forward_ : Verb where
  morphs := [.root "forward"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send}

/-- "grant" — the PP may be implicit, a definite; the theme may not. -/
def grant : Verb where
  morphs := [.root "grant"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .futureHaving}

/-- "offer" — the PP may be implicit, a definite; the theme may not. -/
def offer : Verb where
  morphs := [.root "offer"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.characterize, .futureHaving, .reflexiveAppearance}

/-- "reserve" — the PP may be implicit, a definite; the theme may not. -/
def reserve : Verb where
  morphs := [.root "reserve"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_), [0, 2, 1]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.get}

/-- "pass" — the direct object may be implicit in the prepositional frame only, a definite
(*She wouldn't pass to me*); the PP may be implicit, an indefinite. Its theme is participant 1
and its goal participant 2. -/
def pass : Verb where
  morphs := [.root "pass"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_)).leaveImplicit 0 (some .def), [0, 1, 2]),
     (ArgumentFrame.np_pp.leaveImplicit 1 (some .indef), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give, .marry, .send, .throw}

/-- "hand" — Levin 11.1 Send verbs; neither argument may be implicit. -/
def hand : Verb where
  morphs := [.root "hand"]
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send}

/-- "mail" — transitive, ditransitive, or with a *to*-phrase (*Paul mailed a letter*). -/
def mail : Verb where
  morphs := [.root "mail"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2])]
  levinClasses := {LevinClass.send}

/-- "lend" — neither argument may be implicit. -/
def lend : Verb where
  morphs := [.root "lend"]
  past := "lent"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

end English.Verbs
