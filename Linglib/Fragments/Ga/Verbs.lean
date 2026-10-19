/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Ga.Clause

/-!
# Gã complement-taking verbs

Allotey's Gã verbs that embed clauses are `Verb` entries whose frames are the clause frames of
`Fragments/Ga/Clause`, with the subject controlling the `ni`-clause, or the object an
object-control verb takes before it. Several verbs
alternate between frames: *kai* 'remember' takes the controlled `ni`-clause (ex 43) or a finite
`akɛ`-clause (ex 89a), *kɛɛ* 'say' takes `akɛ` (exx 47–49) or an object-controlled `ni`-clause (ex
117b). Complementizer selection is the paper's first non-finiteness diagnostic (§5.5.1, exx
104–108); the selection relation itself is `Verb.Takes` over `Ga.complementizers`.

## Implementation notes

An implication signature in Karttunen's sense (`Verb.implicative`) is recorded where it is textbook;
the paper uses implicativity for the contrast of ex 89, where the irrealis marker is absent exactly
under the implicatives, but does not classify the verbs itself. Vendler class stays unset, the
convention for clause-embedding verbs. Identifiers are ASCII (see `Fragments/Ga/Clause`); the IPA
orthography is in `form`.

## References

* [allotey-2021]
* [karttunen-1971]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2024]
-/

@[expose] public section

namespace Ga

/-- The reading of the controlled `ni`-frame carries the complement's sort in the classification
of [wurmbrand-lohninger-2023] where [wurmbrand-2024] classes the verb. -/
def niReading (size : Clause.Size) : Verb.Reading := { frame := niFrame, size := some size }

/-- The reading of a finite `akɛ`-frame is a proposition. -/
def akeReading : Verb.Reading := { frame := akeFrame, size := some .proposition }

/-! ### Subject control -/

/-- *tao* 'want' is a subject-control verb whose `ni` is optionally overt (ex 34: *Mi-i tao (ni)
ma na bo* 'I want to see you'), and its embedded 1SG is the irrealis portmanteau *má* (exx 88,
100). -/
def tao : Verb where
  morphs := [.root "tao"]
  valency := .ofFrame niFrame (controller := some 0)
  readings := [niReading .situation]

/-- *sumɔ* 'like' is a subject-control verb with no complementizer under negation (ex 3a: *Dida
sumɔ-ɔɔ e-na bo* 'Father is reluctant to see you') and with `ni` in the future (ex 92), and its
embedded pronoun cannot be obviative. -/
def sumo : Verb where
  morphs := [.root "sumɔ"]
  valency := .ofFrame niFrame (controller := some 0)

/-- *hiɛ-kã-nɔ* 'hope' (lit. 'face-place-upon') is a subject-control verb whose `ni` is obligatory
(ex 35: *Mi hiɛ-kã-nɔ ni ma ya skul gbi ko* 'I hope to go to school one day'). -/
def hiekano : Verb where
  morphs := [.root "hiɛ-kã-nɔ"]
  valency := .ofFrame niFrame (controller := some 0)

/-- *hiɛ-kpa-nɔ* 'forget' (lit. 'face-stop-upon') is a subject-control verb whose `ni` is
obligatory (exx 37–38: *O hiɛ-kpa-nɔ ni o kɔ aspaatere lɛ* 'You forgot to pick up the shoe'). It
is a negative implicative by the textbook classification, *forget to* entailing the complement
unrealized, and its `ni`-clause duly carries the irrealis marker (exx 102–103). -/
def hiekpano : Verb where
  morphs := [.root "hiɛ-kpa-nɔ"]
  valency := .ofFrame niFrame (controller := some 0)
  implicative := ⟨.some .negative, .some .positive⟩

/-- *mia-mi-hiɛ* 'try' (lit. 'squeeze-my-face') is a subject-control verb whose `ni` is obligatory
(exx 36, 60a: 'I tried to close the door'). -/
def miamihie : Verb where
  morphs := [.root "mia-mi-hiɛ"]
  valency := .ofFrame niFrame (controller := some 0)
  readings := [niReading .event]

/-- *kai* 'remember' is a positive implicative with subject control in the `ni`-frame (exx 42–43:
*Mi kai ni ma he wolo* 'I remembered to buy a book'). It alternates into a finite `akɛ`-frame
'remember that', whose realis past complement excludes the irrealis marker (ex 89a); under matrix
negation the `ni`-frame keeps it (ex 117a). -/
def kai : Verb where
  morphs := [.root "kai"]
  valency := .of [(niFrame, [0, 1]), (akeFrame, [0, 1])] (controllers := [some 0])
  readings := [akeReading]
  implicative := ⟨.some .positive, .some .negative⟩

/-- *nyɛ* 'manage' is a positive implicative with subject control, whose `ni` is optionally overt
(ex 39: 'The children managed to buy a home'). It is also attested with a bare realis past
complement that excludes the irrealis marker (ex 89b), a frame outside the three-way clause
typology. -/
def nye : Verb where
  morphs := [.root "nyɛ"]
  valency := .ofFrame niFrame (controller := some 0)
  implicative := ⟨.some .positive, .some .negative⟩

/-- *kplɛnɔ* 'agree' is a subject-control verb whose `ni`-frame requires the irrealis marker
(exx 52, 89c, 109, 122a). It alternates into `akɛ` with a subjunctive complement, 'agree that'
(ex 105: *Osa kplɛnɔ ni/akɛ Taki á-tsɛ́ Momo*). -/
def kpleno : Verb where
  morphs := [.root "kplɛnɔ"]
  valency := .of [(niFrame, [0, 1]), (akeFrame, [0, 1])] (controllers := [some 0])

/-- *kpaŋ* 'plan, decide' is a subject-control verb whose complement only `ni` introduces (ex 106),
with the irrealis marker obligatory (ex 89d). -/
def kpang : Verb where
  morphs := [.root "kpaŋ"]
  valency := .ofFrame niFrame (controller := some 0)
  readings := [niReading .situation]

/-- *kpã-gbɛ* 'expect' is a subject-control verb (ex 53: *Ajele kpã-gbɛ ni e-ye jweremɔ lɛ*
'Ajele expects to win the prize'), infelicitous when Ajele does not self-ascribe winning, which is
the *de se* diagnostic. -/
def kpagbe : Verb where
  morphs := [.root "kpã-gbɛ"]
  valency := .ofFrame niFrame (controller := some 0)
  readings := [niReading .situation]

/-- *dwɛŋ* 'think' takes a finite complement with a low-tone, freely referring subject
(exx 110–111: 'Aku thought s/he bought the book', under `akɛ` or a low-tone `ni`), and a controlled
`ni`-clause with the high-tone anaphoric subject (ex 112: 'Aku thought to buy a book'). -/
def dweng : Verb where
  morphs := [.root "dwɛŋ"]
  valency := .of [(akeFrame, [0, 1]), (niFrame, [0, 1])] (controllers := [none, some 0])
  readings := [akeReading]
  attitude := some (.doxastic .nonVeridical)

/-! ### Object control -/

/-- *wa* 'help' is an object-control verb (exx 44, 54: *Mi wa Ama ni e-ya skul* 'I helped Ama to
go to school'). Whether *help* is implicative has been contested since [karttunen-1971], so it is
left unclassified. -/
def wa : Verb where
  morphs := [.root "wa"]
  valency := .ofFrame niFrame.withObject (controller := some 1)

/-- *kenya* 'urge, encourage' is an object-control verb (exx 55, 60b). -/
def kenya : Verb where
  morphs := [.root "kenya"]
  valency := .ofFrame niFrame.withObject (controller := some 1)

/-- *dai* 'force' is an object-control verb (ex 56: 'I forced Kofi to go to school'), and affirmed
it implies its complement, as *force* does ([karttunen-1971]). -/
def dai : Verb where
  morphs := [.root "dai"]
  valency := .ofFrame niFrame.withObject (controller := some 1)
  implicative := ⟨.some .positive, ⊥⟩

/-- *laka* 'persuade, coax, deceive', its sense depending on context (fn 4), is an object-control
verb (exx 57–58). -/
def laka : Verb where
  morphs := [.root "laka"]
  valency := .ofFrame niFrame.withObject (controller := some 1)

/-- *bi* 'ask' is an object-control verb (ex 59: 'I asked Ayele to tell me a story'). -/
def bi : Verb where
  morphs := [.root "bi"]
  valency := .ofFrame niFrame.withObject (controller := some 1)

/-- *kɛɛ* 'say, tell' is the paper's utterance verb, taking a finite `akɛ`-clause (exx 47–49:
*Jojo kɛɛ akɛ …* 'Jojo said that …'), and an object-control verb in the `ni`-frame, 'tell someone
to' (ex 117b: *John é-kee-ee Mary ni é he noko-noko* 'John didn't tell Mary to buy anything'). -/
def kee : Verb where
  morphs := [.root "kɛɛ"]
  valency := .of [(akeFrame, [0, 1]), (niFrame.withObject, [0, 2, 1])]
    (controllers := [none, some 2])
  readings := [akeReading]
  speechActVerb := true

/-! ### Finite complements only -/

/-- *le* 'know' takes a finite `kɛji`-clause for if/whether complements (exx 104, 108: 'know if
they will be coming', 'know whether you or he bought the book'). -/
def le : Verb where
  morphs := [.root "le"]
  valency := .ofFrame kejiFrame
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- The clause-embedding verbs attested in the paper's examples. -/
def verbs : List Verb :=
  [tao, sumo, hiekano, hiekpano, miamihie, kai, nye, kpleno, kpang, kpagbe, dweng,
   wa, kenya, dai, laka, bi, kee, le]

end Ga
