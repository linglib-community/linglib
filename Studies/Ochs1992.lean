module

public import Linglib.Pragmatics.SocialMeaning.IndexicalField
public import Mathlib.Data.Matrix.Mul

/-!
# Ochs (1992): Indexing Gender

This file formalizes the model of indirect indexicality in [ochs-1992]. Few features of
language index gender directly and exclusively; linguistic forms directly index stances,
acts, and activities, and these in turn help to constitute gender, so the relation of
language to gender is non-exclusive, constitutive, and mediated. The Japanese sentence-final
particles of [uyeno-1971] are the running example: *ze* directly indexes coarse intensity
and *wa* delicate intensity, and the affective dispositions so indexed are part of the
preferred images of men and women. The two steps are association fields, from form to stance
(`formStance`) and from stance to gender (`stanceGender`), and the indirect form–gender
association is their product (`composed`), an index of the second order in the sense of
[silverstein-2003]. *ze* indexes masculinity more than femininity and *wa* the reverse, through
the stances alone, and both particles carry a positive association with both genders, the
non-exclusivity that follows from every stance being available to both sexes.

## Implementation notes

The form-to-stance map is categorical, and the stance-to-gender strengths are two parameters,
the strength `a` with which a stance indexes the gender whose preferred image it belongs to
and the strength `b` with which it indexes the other, the chapter fixing only that both are
positive and that `a` exceeds `b`; the theorems assume no more. The third property of the
chapter, that the relation is temporally transcendent, is not represented.

## References

* [ochs-1992]
* [uyeno-1971]
* [silverstein-1976]
* [silverstein-2003]
* [eckert-2008]
* [west-zimmerman-1987]
-/

@[expose] public section

namespace Ochs1992

open SocialMeaning

/-- The two interactional stances of the chapter's example are coarse intensity, the rough
forceful style, and delicate intensity, the gentle refined one. -/
inductive Stance where
  | coarse
  | delicate
  deriving DecidableEq

instance : Fintype Stance := ⟨{.coarse, .delicate}, λ s => by cases s <;> simp⟩

/-- The poles of the social gender dimension ([west-zimmerman-1987]). -/
inductive GenderPole where
  | masculine
  | feminine
  deriving DecidableEq

/-- The two sentence-final particles, *ze*, coarse, and *wa*, delicate. -/
inductive SFP where
  | ze
  | wa
  deriving DecidableEq

variable {R : Type*} [Semiring R]

/-- The direct index has each particle index exactly one stance. -/
def formStance : AssociationField SFP Stance R := .of λ
  | .ze, .coarse => 1
  | .wa, .delicate => 1
  | _, _ => 0

/-- The constitutive relation makes coarse intensity part of the preferred image of men and
delicate intensity of women, each stance indexing its own gender with strength `a` and the
other with strength `b`, since both sexes use both. -/
def stanceGender (a b : R) : AssociationField Stance GenderPole R := .of λ
  | .coarse, .masculine => a
  | .coarse, .feminine => b
  | .delicate, .masculine => b
  | .delicate, .feminine => a

/-- The indirect index of gender by a particle composes the two maps through the stances. -/
def composed (a b : R) : AssociationField SFP GenderPole R := formStance * stanceGender a b

theorem composed_ze (a b : R) (g : GenderPole) :
    composed a b .ze g = stanceGender a b .coarse g := by
  simp [composed, Matrix.mul_apply, Finset.univ, Fintype.elems, Finset.sum_insert, formStance]

theorem composed_wa (a b : R) (g : GenderPole) :
    composed a b .wa g = stanceGender a b .delicate g := by
  simp [composed, Matrix.mul_apply, Finset.univ, Fintype.elems, Finset.sum_insert, formStance]

variable [Preorder R] {a b : R}

theorem ze_indexes_masculine (h : b < a) :
    composed a b .ze .feminine < composed a b .ze .masculine := by
  simpa [composed_ze, stanceGender] using h

theorem wa_indexes_feminine (h : b < a) :
    composed a b .wa .masculine < composed a b .wa .feminine := by
  simpa [composed_wa, stanceGender] using h

theorem indexes_all (hb : 0 < b) (h : b < a) (sfp : SFP) (g : GenderPole) :
    (composed a b).Indexes sfp g := by
  cases sfp <;> cases g <;>
    simp [AssociationField.Indexes, composed_ze, composed_wa, stanceGender] <;>
    first | exact hb | exact hb.trans h

theorem composed_ze_ne_wa (h : b < a) (g : GenderPole) :
    composed a b .ze g ≠ composed a b .wa g := by
  cases g <;> simp [composed_ze, composed_wa, stanceGender] <;> first | exact h.ne' | exact h.ne

end Ochs1992
