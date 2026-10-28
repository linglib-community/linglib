module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Semantics.ArgumentStructure.RoleList

/-!
# Chuj verbs

The Chuj verbs of Alonso-Ovalle and Royer's examples, by root, with the proto-role entailments of
their subjects. *Man* 'buy', *yam* 'grab', *sik'* 'select' and *chi'* 'eat' are transitive and
*wa'* 'eat' and *chanhalw* 'dance' intransitive, each with an agent as its subject; *nib'*
'like', transitive with the derived transitive suffix *-ej* in *ix-s-nib'-ej* 'liked', has an
experiencer as its subject, sentient but not volitional.

## References

* [alonso-ovalle-royer-2024]
* [dowty-1991]
-/

@[expose] public section

namespace Chuj.Verbs

open ArgumentStructure

/-- *man* 'buy'. -/
def man : Verb where
  morphs := [.root "man"]
  valency := .ofFrame ArgumentFrame.np [some accomplishmentSubjectProfile, none]

/-- *yam* 'grab'. -/
def yam : Verb where
  morphs := [.root "yam"]
  valency := .ofFrame ArgumentFrame.np [some accomplishmentSubjectProfile, none]

/-- *sik'* 'select', passive *sik'-chaj*. -/
def sik' : Verb where
  morphs := [.root "sik'"]
  valency := .ofFrame ArgumentFrame.np [some accomplishmentSubjectProfile, none]

/-- *chi'* 'eat', transitive, as in *ix-chi'-an chi'b'ej* 'ate meat' with its subject focused. -/
def chi' : Verb where
  morphs := [.root "chi'"]
  valency := .ofFrame ArgumentFrame.np [some accomplishmentSubjectProfile, none]

/-- *chanhalw* 'dance', intransitive. -/
def chanhalw : Verb where
  morphs := [.root "chanhalw"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  voiceType := some .agentive

/-- *wa'* 'eat', intransitive. -/
def wa' : Verb where
  morphs := [.root "wa'"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  voiceType := some .agentive

/-- *nib'* 'like', with an experiencer as its subject. -/
def nib' : Verb where
  morphs := [.root "nib'"]
  valency := .ofFrame ArgumentFrame.np [some experiencerProfile, none]

/-- The verbs, for lookup by root. -/
def all : List Verb := [man, yam, sik', chi', chanhalw, wa', nib']

end Chuj.Verbs
