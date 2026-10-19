module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Korean causative verbs

Korean has two causatives, which Sohn calls the long and the short form. The long form *-ge ha-*
'make do' denotes indirect causation and does not entail its effect: Song's *kiho-ka cini-ka wus-ke
ha-əss-ɨna cini-ka wus-ci=an-əss-ta* 'Keeho caused Jinee to smile, but she didn't smile' is not
contradictory. The short form suffixes *-i-*, *-hi-*, *-li-*, *-ki-* and their allomorphs to the
stem and denotes immediate causation, as in *jug-i-da* 'kill' from *jug-da* 'die', Sohn's
*koyangi-ka cwi-lul cwuk-i-ess-ta* 'a cat killed a rat'. The entries keep Song's Yale forms.

## Main definitions

* `Korean.verbs` — the causative verbs of the two constructions

## References

* [sohn-1994]
* [song-1996]
-/

@[expose] public section

namespace Korean

open ArgumentStructure

/-- *wus-ke ha-ta* 'cause to smile', the periphrastic causative. -/
def wus_ke_ha : Verb where
  morphs := [.root "wus", .suff "ke", .root "ha", .suff "ta"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]

/-- *ilk-ke ha-ta* 'cause to read', the periphrastic causative. -/
def ilk_ke_ha : Verb where
  morphs := [.root "ilk", .suff "ke", .root "ha", .suff "ta"]
  valency := .ofFrame ArgumentFrame.infinitival
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]

/-- *cwuk-i-ta* 'kill', the morphological causative of *cwuk-ta* 'die'. -/
def cwuk_i : Verb where
  morphs := [.root "cwuk", .suff "i", .suff "ta"]
  valency := .ofFrame ArgumentFrame.np

/-- The inventory. -/
def verbs : List Verb := [wus_ke_ha, ilk_ke_ha, cwuk_i]

end Korean
