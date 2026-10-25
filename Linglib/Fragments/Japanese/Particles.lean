module

public import Linglib.Syntax.Category.Particle.Basic

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
tired? — Yes (I'm not tired)'.

## Main definitions

* `Japanese.Particles.ka`, `no_`, `koto`, `kke`, `daroo`: the clause-typing particles with their
  embedding distributions.
* `Japanese.PolarityParticles.un`, `uun`, `all`: the polarity particles.

## References

* [dayal-2025]
* [holmberg-2016]
* [roelofsen-uegaki-2021]
* [sauerland-yatsushiro-2017]
* [uegaki-roelofsen-2018]
-/

@[expose] public section

namespace Japanese.Particles

/-- *ka* — clause-typing Q-morpheme. Obligatory in subordinated
interrogatives, optional in matrix (can be dropped). Marks CP as +WH.
Licensed in quotation as well. -/
def ka : Particle where
  form := "ka"
  script := some "か"
  position := some .clauseFinal
  distribution := fun c e ↦ match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .obligatory
      | .quasiSubordinated => some .optional
      | .quotation => some .optional
      | .insubordinated => none
    | _ => none

/-- *no* — clause-typing particle for questions (informal). -/
def no_ : Particle where
  form := "no"
  script := some "の"
  position := some .clauseFinal
  distribution := fun c e ↦ match c with
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
def koto : Particle where
  form := "koto"
  script := some "こと"
  position := some .clauseFinal
  distribution := fun c e ↦ match c, e with
    | .declarative, .matrix => some .excluded
    | .declarative, .subordinated => some .optional
    | .declarative, .quasiSubordinated => some .excluded
    | _, _ => none

/-- *kke* — meta question particle (MQP). Only in matrix questions and
quotations ([sauerland-yatsushiro-2017]). Has a "remind-me"
presupposition: speaker has forgotten Ans(Q) and believes the addressee
knows it. -/
def kke : Particle where
  form := "kke"
  script := some "っけ"
  position := some .clauseFinal
  distribution := fun c e ↦ match c with
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
def daroo : Particle where
  form := "darō"
  script := some "だろう"
  position := some .clauseFinal
  distribution := fun c e ↦ match c with
    | .declarative | .polar =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .excluded
      | .quasiSubordinated => some .optional
      | .quotation | .insubordinated => none
    | _ => none

end Japanese.Particles

namespace Japanese.PolarityParticles

/-- *un* 'yes'. -/
def un : Particle where
  form := "un"

/-- *uun* 'no', as in *Kare-wa koohii-o noma nai no?* 'Does he not drink coffee?' — *Uun, nomu
yo* 'No, he drinks'. -/
def uun : Particle where
  form := "uun"

/-- The colloquial polarity particles. -/
def all : List Particle := [un, uun]

end Japanese.PolarityParticles
