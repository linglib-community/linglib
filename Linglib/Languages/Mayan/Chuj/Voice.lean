module

public import Linglib.Syntax.Voice.Basic

/-!
# Chuj voice

Chuj (Q'anjob'alan Mayan) forms five stems on a transitive root. Coon sets the transitive stem,
with a null suffix and a full noun phrase as its object, beside two antipassives, whose agent is
the sole argument: *-w*, the incorporation antipassive, whose object is a bare noun that takes no
preposition, as in *ixintek'wi pelota* 'I ball-kicked', and *-waj*, the absolutive antipassive,
whose patient is an oblique introduced by *t'a* or is left out, as in *ixintek'waj t'a nok'
pelota* 'I did kicking to the ball'. Her table of Chuj voice morphology sets the two
antipassives beside two passives, whose patient is the sole argument: *-j*, the agentless
passive, with no thematic agent, an *-uj*-phrase naming a cause of the event; and *-chaj*, the
passive, whose implicit agent may be expressed in an *-uj*-phrase and licenses agent-oriented
adverbs. Coon decomposes *-waj* and *-chaj* into *-w* and *-ch* and a suffix *-aj*; the
decomposition lives in her study.

## Main definitions

* `Chuj.transitive`, `incorporationAntipassive`, `absolutiveAntipassive`,
  `agentlessPassive`, `passive`: the five stems of a transitive root as voices
* `Chuj.voices`: the inventory

## Main results

* `Chuj.alternationTypes`: the two antipassives are antipassivizations, *-chaj* a
  passivization, and *-j* a decausativization

## Implementation notes

The absolutive antipassive leaves its patient implicit, as the passive leaves its agent; an
oblique may express either.

## References

* [coon-2019]
-/

@[expose] public section

namespace Chuj

/-- The transitive stem, with a null suffix: the active. -/
def transitive : Voice := Voice.active

/-- *-w*: the incorporation antipassive, the object a bare noun. -/
def incorporationAntipassive : Voice := (Voice.antipassive .incorporated).marked [.suff "w"]

/-- *-waj*: the absolutive antipassive, the patient implicit or an oblique. -/
def absolutiveAntipassive : Voice := (Voice.antipassive (.implicit none)).marked [.suff "waj"]

/-- *-j*: the agentless passive, with no agent in participant structure. -/
def agentlessPassive : Voice := Voice.anticausative.marked [.suff "j"]

/-- *-chaj*: the passive, the agent implicit or an oblique. -/
def passive : Voice := Voice.passive.marked [.suff "chaj"]

/-- The five stems of a transitive root. -/
def voices : Finset Voice :=
  {transitive, incorporationAntipassive, absolutiveAntipassive, agentlessPassive, passive}

/-- The antipassives *-w* and *-waj* are antipassivizations and *-chaj* a passivization; *-j*,
with no agent in participant structure, is a decausativization and not a passivization. -/
theorem alternationTypes :
    incorporationAntipassive.IsAntipassivization ∧ absolutiveAntipassive.IsAntipassivization ∧
      passive.IsPassivization ∧ agentlessPassive.IsDecausativization ∧
      ¬ agentlessPassive.IsPassivization := by
  decide

end Chuj
