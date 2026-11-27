module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Japanese particles

The clause-final particles of Japanese questions and their distribution over matrix, embedded
and quoted clauses: the question particle *ka*, obligatory in embedded questions and optional
in matrix ones, its informal counterpart *no*, the declarative complementizer *koto*, the
meta-question particle *kke*, which asks the addressee to remind the speaker of an answer and
occurs only in matrix questions and quotations, and the conjectural *darō*, which embeds
declaratives and questions alike. The colloquial polarity particles *un* 'yes' and *uun* 'no' are
`Japanese.PolarityParticles`. In Holmberg's truth-based system *un* confirms the negative
alternative of a negative question, *Kimi tukarete nai? — Un (tukarete nai)* 'Are you not
tired? — Yes (I'm not tired)'. The sentence-final *ze* and *wa* are `Japanese.Particles.ze` and
`Japanese.Particles.wa`.

## Main definitions

* `Japanese.Particles.ka`, `no_`, `koto`, `kke`, `daroo`: the clause-typing particles with their
  embedding distributions.
* `Japanese.Particles.ze`, `wa`: two sentence-final particles.
* `Japanese.PolarityParticles.un`, `uun`, `all`: the polarity particles.

## References

* [dayal-2025]
* [holmberg-2016]
* [ochs-1992]
* [roelofsen-uegaki-2021]
* [sauerland-yatsushiro-2017]
* [uegaki-roelofsen-2018]
-/

@[expose] public section

namespace Japanese.Particles

/-- *ka* — clause-typing Q-morpheme. Obligatory in subordinated
interrogatives, optional in matrix (can be dropped). Marks CP as +WH.
Licensed in quotation as well. -/
def ka : Clause.Marker where
  morphs := [.free "ka"]
  script := some "か"
  anchor := .clause {.final}
  distribution := fun (c, e) ↦ match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .obligatory
      | .quasiSubordinated => some .optional
      | .quotation => some .optional
      | .insubordinated => none
    | _ => none

/-- *no* — clause-typing particle for questions (informal). -/
def no_ : Clause.Marker where
  morphs := [.free "no"]
  script := some "の"
  anchor := .clause {.final}
  distribution := fun (c, e) ↦ match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .optional
      | .quasiSubordinated => some .optional
      | .quotation | .insubordinated => none
    | _ => none

/-- *koto* — complementizer for declarative clauses. Contrast with *ka*:
having *ka* in the embedded clause suffices for interrogative
interpretation, while *koto* marks a declarative ([dayal-2025]: (15)).
Subordinated clauses only. -/
def koto : Complementizer where
  morphs := [.free "koto"]
  script := some "こと"
  anchor := .clause {.final}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.declarative, .subordinated) => some .optional
    | (.declarative, .quasiSubordinated) => some .excluded
    | _ => none

/-- *kke* — meta question particle (MQP). Only in matrix questions and
quotations ([sauerland-yatsushiro-2017]). Has a "remind-me"
presupposition: speaker has forgotten Ans(Q) and believes the addressee
knows it. -/
def kke : Clause.Marker where
  morphs := [.free "kke"]
  script := some "っけ"
  anchor := .clause {.final}
  distribution := fun (c, e) ↦ match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .excluded
      | .quasiSubordinated => some .excluded
      | .quotation => some .optional
      | .insubordinated => none
    | _ => none

/-- *darō* だろう — conjectural/epistemic copula.
With declarative complement: "x thinks p" (⟦daroo⟧({p})(x) = INQ_x ⊆ {p}↓).
With interrogative complement: "x wonders Q" (⟦daroo⟧(Q)(x) = INQ_x ⊆ Q).
The dual reading arises from the absence of an ignorance component,
unlike wonder ([roelofsen-uegaki-2021], [uegaki-roelofsen-2018]).
Appears in matrix and quasi-subordinated contexts but not in subordinated
interrogatives (which use *ka*). -/
def daroo : Clause.Marker where
  morphs := [.free "darō"]
  script := some "だろう"
  anchor := .clause {.final}
  distribution := fun (c, e) ↦ match c with
    | .declarative | .polar =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .excluded
      | .quasiSubordinated => some .optional
      | .quotation | .insubordinated => none
    | _ => none

/-- *ze* ぜ, a sentence-final particle ([ochs-1992]). -/
def ze : Clause.Marker where
  morphs := [.free "ze"]
  script := some "ぜ"
  anchor := .clause {.final}

/-- *wa* わ, a sentence-final particle ([ochs-1992]), distinct from the topic marker *wa* は. -/
def wa : Clause.Marker where
  morphs := [.free "wa"]
  script := some "わ"
  anchor := .clause {.final}

end Japanese.Particles

namespace Japanese.PolarityParticles

/-- *un* 'yes'. -/
def un : Morphology.Morph := .free "un"

/-- *uun* 'no', as in *Kare-wa koohii-o noma nai no?* 'Does he not drink coffee?' — *Uun, nomu
yo* 'No, he drinks'. -/
def uun : Morphology.Morph := .free "uun"

/-- The colloquial polarity particles. -/
def all : List Morphology.Morph := [un, uun]

end Japanese.PolarityParticles
