module

public import Linglib.Syntax.Voice.Basic

/-!
# Chuj voice

Chuj (Q'anjob'alan Mayan) forms the stems of a transitive root with five suffixes, which
Coon tabulates: a null suffix for the transitive stem; *-w*, the incorporation antipassive,
whose object is a bare noun that takes no preposition, as in *ixintek'wi pelota* 'I
ball-kicked'; *-waj*, the absolutive antipassive, whose patient is an oblique introduced by
*t'a*, as in *ixintek'waj t'a nok' pelota* 'I did kicking to the ball'; *-j*, the agentless
passive, with no thematic agent, an *-u'uj*-phrase naming a cause of the event; and *-chaj*,
the passive, whose implicit agent may be expressed in an *-u'uj*-phrase and licenses
agent-oriented adverbs. Each stem is built from the root and its suffix, so the alternations
are read from the transitive construction. The decomposition of *-waj* and *-chaj* into *-w*
and *-ch* with a suffix *-aj* is Coon's analysis and lives in her study.

## Main definitions

* `Chuj.transitive`, `incorporationAntipassive`, `absolutiveAntipassive`,
  `agentlessPassive`, `passive` — the five stems of a transitive root as voices
* `Chuj.voices` — the inventory

## Main results

* `Chuj.agentFate` — the agent is kept by *-w* and *-waj*, demoted but present under
  *-chaj*, and absent under *-j*

## Implementation notes

The incorporated bare noun of a *-w* stem is entered as an implicit position, the frame
vocabulary having no expressed non-argument.

## References

* [coon-2019]
-/

@[expose] public section

namespace Chuj

/-- The transitive stem, with a null suffix: the active. -/
def transitive : Voice := Voice.active

/-- *-w*: the incorporation antipassive, the object a bare noun. -/
def incorporationAntipassive : Voice :=
  (Voice.of .np .objectDrop [some .external, some (.complement 0)]).marked [.suff "w"]

/-- *-waj*: the absolutive antipassive, the patient an oblique. -/
def absolutiveAntipassive : Voice := Voice.antipassive.marked [.suff "waj"]

/-- *-j*: the agentless passive, with no agent in participant structure. -/
def agentlessPassive : Voice := Voice.anticausative.marked [.suff "j"]

/-- *-chaj*: the passive, the agent implicit or an oblique. -/
def passive : Voice := Voice.passive.marked [.suff "chaj"]

/-- The five stems of a transitive root. -/
def voices : Finset Voice :=
  {transitive, incorporationAntipassive, absolutiveAntipassive, agentlessPassive, passive}

/-- The four intransitivizing suffixes differ in the fate of the agent: kept by *-w* and
*-waj*, demoted but present under *-chaj*, absent under *-j* ([coon-2019]). -/
theorem agentFate :
    incorporationAntipassive.fateOfRole .A = .maintained ∧
      absolutiveAntipassive.fateOfRole .A = .maintained ∧
      passive.fateOfRole .A = .denucleativized ∧
      agentlessPassive.fateOfRole .A = .suppressed := by
  decide

end Chuj
