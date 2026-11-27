module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Sinhala verbs

A Colloquial Sinhala verb root occurs in a volitive stem, an involitive stem, or both. Involitive
stems have front root vowels and the thematic vowel *-e-* in the present tense, while volitive
stems take *-a-* or *-i-*. Subjects of volitives tend to be read as volitional, and involitives
always convey non-volitionality, unexpectedness to the speaker or ironic denial. A root that
requires volition, as *minimarannə* 'murder' does, has no involitive stem, and a psych verb such
as *ridennə* 'ache' has no volitive one. Some causative roots also have an intransitive
inchoative, which is always involitive, as *gilannə* 'drown' has *Nimal giluna* 'Nimal drowned'.

The entries are the roots whose anticausatives Beavers and Zubair analyze. An entry is cited by
its volitive infinitive, and its involitive diatheses carry the involitive infinitive as their
form: the transitive whose causer the postposition *atiŋ* marks, where the paper gives one, and
the intransitive inchoative with the patient as subject, where the root has one. *Marannə* 'kill'
has no involitive transitive, *\*Aruni atiŋ Nimal-wə mæruna*, and *kapannə* 'cut' no inchoative.

## Main definitions

* `Sinhala.HasInvolitive`: a verb has an involitive stem.

## Implementation notes

Forms are transliterated as printed in Beavers and Zubair, whose PDF text layer drops *ə*. They
give the involitives of *kapannə* 'cut' and *vinaashə-kərannə* 'destroy' only in the past,
*kæpuna* and *vinaashə-wuna*. The infinitives *kæpennə* and *vinaashə-wennə* follow their stem
formation, in which a compound's volitive *-kərə-* 'do' pairs with the involitive *-we-*. The
frames record no subject marking, so the *atiŋ* of an involitive transitive's causer is not
recorded.

## References

* [J. Beavers and C. Zubair, *Anticausatives in Sinhala: Involitivity and causer suppression*
  (2013)][beavers-zubair-2013]
-/

@[expose] public section

namespace Sinhala

/-- A verb has an involitive stem when one of its diatheses departs from the volitive citation
form. -/
def HasInvolitive (v : Verb) : Prop := ∃ d ∈ v.valency.diatheses, d.form.isSome

instance : DecidablePred HasInvolitive := fun v ↦
  inferInstanceAs (Decidable (∃ d ∈ v.valency.diatheses, _))

/-- *kadannə* 'break', whose involitive *kædennə* has a transitive, *Siri atiŋ piŋgaanəyə kæduna*
'Siri broke the plate (accidentally)' ((7a)), and an inchoative, *Eewa okkomə ibeemə kædenəwa*
'They all just break by themselves' ((28a)). -/
def kadann : Verb where
  morphs := [.root "kadannə"]
  valency := .of [(.np, [0, 1]), (.np, [0, 1]), (.intransitive, [1])]
    (forms := [none, some [.root "kædennə"], some [.root "kædennə"]])

/-- *gilannə* 'drown', whose involitive *gilennə* has a transitive, *Aruni atiŋ Nimal-wə giluna*
'Aruni drowned Nimal (accidentally)' ((2b)), and an inchoative, *Nimal giluna* 'Nimal drowned'
((3)). -/
def gilann : Verb where
  morphs := [.root "gilannə"]
  valency := .of [(.np, [0, 1]), (.np, [0, 1]), (.intransitive, [1])]
    (forms := [none, some [.root "gilennə"], some [.root "gilennə"]])

/-- *marannə* 'kill', whose involitive *mærennə* 'die' occurs only intransitively, *Nimal mæruna*
'Nimal died' ((17c)). -/
def marann : Verb where
  morphs := [.root "marannə"]
  valency := .of [(.np, [0, 1]), (.intransitive, [1])] (forms := [none, some [.root "mærennə"]])

/-- *minimarannə* 'murder' requires volition and so has neither an involitive stem nor an
inchoative. -/
def minimarann : Verb where
  morphs := [.root "minimarannə"]
  valency := .ofFrame .np

/-- *kapannə* 'cut', whose involitive has a transitive, *Joon atiŋ pan kæpuna* 'John cut the bread
(accidentally)' ((7c)), but no inchoative ((26)). -/
def kapann : Verb where
  morphs := [.root "kapannə"]
  valency := .ofFrames [.np, .np] (forms := [none, some [.root "kæpennə"]])

/-- *vinaashə-kərannə* 'destroy', whose involitive *vinaashə-wennə* has a transitive ((44)) and,
unlike English *destroy*, an inchoative (p. 40). -/
def vinaashKarann : Verb where
  morphs := [.root "vinaashə-kərannə"]
  valency := .of [(.np, [0, 1]), (.np, [0, 1]), (.intransitive, [1])]
    (forms := [none, some [.root "vinaashə-wennə"], some [.root "vinaashə-wennə"]])

/-- The verbs of this file. -/
def verbs : List Verb := [kadann, gilann, marann, minimarann, kapann, vinaashKarann]

end Sinhala
