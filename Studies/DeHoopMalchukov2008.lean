module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Pragmatics.Bidirectional

/-!
# de Hoop and Malchukov (2008): Case-marking strategies

This file formalizes the two case-marking strategies of [de-hoop-malchukov-2008]: the
identifying function, (10), by which case encodes a property of the argument itself, and the
distinguishing function, (15), by which case tells the two arguments of a transitive clause
apart. Both are violable constraints evaluated against ECONOMY in the bidirectional Optimality
Theory of [blutner-2000], on the assumption that a morphologically unmarked case is the absence
of case, as in [aissen-2003]. Arguments are strong or weak by their discourse prominence, and
a strong subject is the typical, distinguishable one while a strong object is the atypical,
subject-like one, so DISTINGUISHABILITY targets the weak subject and the strong object where
IDENTIFY targets the strong argument in either position. The superoptimal pairs of the
tableaux follow: the strategies converge in differential object marking, both marking the
strong object as in Hindi, and diverge in differential subject marking, IDENTIFY marking the
volitional subject of Manipuri and DISTINGUISHABILITY the weak subject of Fore, which explains
the robustness of the one alternation and the variability of the other. In a symmetrical
alternation between two overt cases, Lezgian's ergative and oblique or Finnish's accusative
and partitive, DISTINGUISHABILITY is vacuously satisfied, so the alternation is necessarily due
to IDENTIFY. Section 4 replaces ECONOMY by PAIP, (42), which penalizes case on the primary
actant, the argument encoded like the intransitive subject, so that differential marking is
free of it on the object of a nominative-accusative and the subject of an ergative-absolutive
language, where differential object and subject marking are found, while the other two
alternations conflict with IDENTIFY and are resolved by voice, the passive making the object
and the antipassive the subject the unmarked argument.

## Implementation notes

A form is `Option C` over the language's overt cases, `none` the absence of case; the
asymmetrical games have one overt case, and the symmetrical game omits the caseless form
since the Case Filter outranks ECONOMY there. Superoptimality is the computable
`BidirectionalOT.superoptimal`, and each tableau is one `decide`.

## TODO

Tableau (41) for Aranda lists the ergative on the inanimate subject as a third superoptimal
pair, blocked under [blutner-2000]'s definition by the ergative on the first person, which
shares its form with a better profile; the paper keeps it by arguing that the one ergative
form cannot be ambiguous between a first person and an inanimate. `aranda` states what the
blocking relation gives, the first person marked and the intermediate types caseless.

## References

* [de-hoop-malchukov-2008]
* [blutner-2000]
* [aissen-2003]
-/

@[expose] public section

namespace DeHoopMalchukov2008

open BidirectionalOT OptimalityTheory

/-! ### Strength and position -/

/-- The strength of an argument, its discourse prominence: animate, definite and volitional
arguments are strong, *A* and *P*, and the others weak, *a* and *p*. -/
inductive Strength where
  | strong
  | weak
  deriving DecidableEq, Repr

/-- The other strength. -/
def Strength.opposite : Strength → Strength
  | .strong => .weak
  | .weak => .strong

/-- The two core positions of a transitive clause. -/
inductive Position where
  | subject
  | object
  deriving DecidableEq, Repr

/-- The argument DISTINGUISHABILITY must mark, the one confusable with its co-argument: the
weak subject, which lacks the agent's prominence, and the strong object, which has it. -/
def Position.confusable : Position → Strength
  | .subject => .weak
  | .object => .strong

/-! ### The constraints -/

section Constraints

variable {C M : Type*} [DecidableEq C] [DecidableEq M]

/-- IDENTIFY, (9): case `c` identifies the meaning `m`, so a pair violates it by having either
without the other. -/
def identify (c : C) (m : M) : Constraint (Option C × M) :=
  .binary λ p => ¬ (p.1 = some c ↔ p.2 = m)

/-- DISTINGUISHABILITY, (15), for the confusable meaning `m`: violated by leaving it
caseless. -/
def distinguish (m : M) : Constraint (Option C × M) := .binary λ p => p.1.isNone ∧ p.2 = m

/-- ECONOMY: violated by any morphological case. -/
def economy : Constraint (Option C × M) := .binary λ p => p.1.isSome

end Constraints

/-! ### Asymmetrical differential marking -/

/-- The asymmetrical game: one overt case against its absence, for either strength. -/
def asymmetrical : Finset (Option Unit × Strength) :=
  {(some (), .strong), (some (), .weak), (none, .strong), (none, .weak)}

/-- IDENTIFY over ECONOMY marks the strong argument in either position (Tableaux (18), (31) and
(39)). -/
theorem identify_marks_strong :
    superoptimal asymmetrical (profile [identify () .strong, economy]) =
      {(some (), .strong), (none, .weak)} := by
  decide

/-- DISTINGUISHABILITY over ECONOMY marks the confusable argument (Tableaux (21), (26), (32) and
(35)). -/
theorem distinguish_marks_confusable (pos : Position) :
    superoptimal asymmetrical (profile [distinguish pos.confusable, economy]) =
      {(some (), pos.confusable), (none, pos.confusable.opposite)} := by
  cases pos <;> decide

theorem converge_iff (pos : Position) :
    superoptimal asymmetrical (profile [identify () .strong, economy]) =
        superoptimal asymmetrical (profile [distinguish pos.confusable, economy]) ↔
      pos = .object := by
  cases pos <;> decide

/-! ### Symmetrical differential marking -/

/-- The two overt cases of a symmetrical alternation: the one identifying the strong
argument, Lezgian's ergative and Finnish's accusative, and the other, their oblique and
partitive. -/
inductive Overt where
  | identifying
  | other
  deriving DecidableEq, Repr

/-- The symmetrical game: both overt cases and no caseless form, the Case Filter outranking
ECONOMY. -/
def symmetrical : Finset (Option Overt × Strength) :=
  {(some .identifying, .strong), (some .identifying, .weak), (some .other, .strong),
    (some .other, .weak)}

/-- In a symmetrical system IDENTIFY pairs each overt case with a strength, as in Lezgian and
Finnish (Tableaux (24) and (29)). -/
theorem symmetrical_identify :
    superoptimal symmetrical (profile [identify .identifying .strong, economy]) =
      {(some .identifying, .strong), (some .other, .weak)} := by
  decide

theorem distinguish_symmetrical (m : Strength) : ∀ p ∈ symmetrical, distinguish m p = 0 := by
  cases m <;> decide

theorem symmetrical_distinguish (m : Strength) :
    superoptimal symmetrical (profile [distinguish m, economy]) = symmetrical := by
  cases m <;> decide

/-! ### Both strategies at once -/

/-- Aranda's subject types along the hierarchy (40): the first person pronoun, the
intermediate persons, humans and animates, and the inanimate noun. -/
inductive ArandaSubject where
  | firstPerson
  | intermediate
  | inanimate
  deriving DecidableEq, Repr

/-- The Aranda game: the ergative against its absence, for each subject type. -/
def arandaSubjects : Finset (Option Unit × ArandaSubject) :=
  {(some (), .firstPerson), (some (), .intermediate), (some (), .inanimate),
    (none, .firstPerson), (none, .intermediate), (none, .inanimate)}

/-- Tableau (41): with DISTINGUISHABILITY over IDENTIFY over ECONOMY, the first person takes
the ergative by IDENTIFY and the intermediate types stay caseless; the paper's ergative on the
inanimate is blocked by the first person's, see the module's TODO. -/
theorem aranda :
    superoptimal arandaSubjects
        (profile [distinguish .inanimate, identify () .firstPerson, economy]) =
      {(some (), .firstPerson), (none, .intermediate)} := by
  decide

/-! ### PAIP and the alignment of differential marking -/

/-- The alignment of a language's core cases. -/
inductive Alignment where
  | nominativeAccusative
  | ergativeAbsolutive
  deriving DecidableEq, Repr

/-- The primary actant, the argument of a transitive clause encoded like the intransitive
subject: the nominative subject or the absolutive object. -/
def Alignment.primaryActant : Alignment → Position
  | .nominativeAccusative => .subject
  | .ergativeAbsolutive => .object

section PAIP

variable {C M : Type*}

/-- PAIP, (42): avoid marking the unmarked argument, an overt case on the primary actant. -/
def paip (al : Alignment) : Constraint (Position × Option C × M) :=
  .binary λ p => p.1 = al.primaryActant ∧ p.2.1.isSome

theorem paip_eq_zero_iff (al : Alignment) (pos : Position) (c : C) (m : M) :
    paip al (pos, some c, m) = 0 ↔ pos ≠ al.primaryActant := by
  simp [paip]

end PAIP

end DeHoopMalchukov2008
