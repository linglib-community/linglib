module

public import Linglib.Morphology.DistributedMorphology.Locality
public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# Gender on the nominal categorizer

This file defines the gender features of the nominal categorizer n in Distributed Morphology. A
gender feature is a binary dimension such as [±FEM] with a sign, and it is interpretable for
natural gender and uninterpretable for arbitrary gender. A categorizing head may also bear the
selectional feature {D}, which licenses an inalienable possessor.

Agreement in gender is a probe relativized to gender, searching the heads of a nominal from the
top; when it finds none, Agree fails and the default gender is spelled out. When several n's are
stacked, Kramer's Highest Gender Hypothesis makes the gender of the highest n the agreeing
gender. Kramer derives it from cyclicity: each n is a cyclic head that sends the nPs below it to
spell-out, so the probe searches the last cycle of the word alone. A plain highest n then leaves
the default gender, where a probe searching every n would find the gender of a lower one, and a
diminutive that is not an n, bearing no gender, leaves the gender of the n below it.

## Main definitions

* `GenderValue`: a binary gender dimension with a sign.
* `GenderFeature`: a gender value with its interpretability.
* `Categorizer.Head`: a categorizer with its gender feature and {D}.
* `agreeingGender`: the gender a gender probe agrees in, or the default on failed Agree.

## Main results

* `agreeingGender_lastCycle`: the Highest Gender Hypothesis, the agreeing gender of a word being
  that of its highest cyclic head.
* `agreeingGender_lastCycle_plain`: a plain highest n gives the default, where a search of every
  n would not.

## References

* [kramer-2015]
* [adamson-2024]
* [myler-2016]
-/

@[expose] public section

namespace DistributedMorphology

open Minimalist

/-! ### Gender features -/

/-- A binary gender dimension. -/
inductive GenderDimension where
  /-- [±FEM], as in Amharic, Spanish and Maa. -/
  | fem
  /-- [±MASC], as in Jarawara. -/
  | masc
  /-- [±ANIM], as in Lealao Chinantec, Algonquian and Teop. -/
  | anim
  deriving DecidableEq, Repr, Fintype

/-- The sign of a binary feature. -/
inductive GenderValue.Pole where
  | pos
  | neg
  deriving DecidableEq, Repr, Fintype

/-- A valued gender feature is a dimension with a sign, as in [+FEM], [−FEM] and [+ANIM]. -/
structure GenderValue where
  /-- The dimension. -/
  dim : GenderDimension
  /-- The sign. -/
  pole : GenderValue.Pole
  deriving DecidableEq, Repr, Fintype

/-- A gender value together with its interpretability. -/
structure GenderFeature where
  /-- Whether the feature is legible at LF. -/
  interp : Interpretability
  /-- The value. -/
  val : GenderValue
  deriving DecidableEq, Repr

/-! ### Categorizing heads -/

/-- A categorizing head with its gender feature and the selectional feature {D}, a head of a
`ComplexHead`. -/
structure Categorizer.Head where
  /-- The categorizer n, v or a. -/
  categorizer : Categorizer
  /-- The gender feature, if any. -/
  gender : Option GenderFeature := none
  /-- The selectional feature {D}. -/
  selectsD : Bool := false
  deriving DecidableEq, Repr

namespace Categorizer.Head

/-- The n bearing the gender feature of interpretability `interp` and value `v`. -/
def gendered (interp : Interpretability) (v : GenderValue) : Categorizer.Head where
  categorizer := .n
  gender := some ⟨interp, v⟩

/-- The n with no gender feature. -/
def n_plain : Categorizer.Head where
  categorizer := .n

/-- The n bearing interpretable [+FEM], the natural feminine. -/
def n_iFem : Categorizer.Head := gendered .interpretable ⟨.fem, .pos⟩

/-- The n bearing interpretable [−FEM], the natural masculine. -/
def n_iMasc : Categorizer.Head := gendered .interpretable ⟨.fem, .neg⟩

/-- The n bearing uninterpretable [+FEM], the arbitrary feminine. -/
def n_uFem : Categorizer.Head := gendered .uninterpretable ⟨.fem, .pos⟩

/-- The n bearing uninterpretable [+ANIM], the nominalizer of Teop body-part roots. -/
def n_uAnim : Categorizer.Head := gendered .uninterpretable ⟨.anim, .pos⟩

end Categorizer.Head

/-! ### Agreement in gender -/

section HighestGender

open Minimalist

variable {R H G : Type*} (gender : H → Option G) (default : G)

/-- The probe for gender, relativized to the heads that bear one. -/
def genderProbe : Probe H := Probe.relativized fun h ↦ (gender h).isSome

/-- The gender a gender probe agrees in when it searches `goals`, nearest first, or `default`
when Agree fails. -/
def agreeingGender (goals : List H) : G :=
  (((genderProbe gender).search goals).bind gender).getD default

variable {gender default} {h h' : H} {hs : List H} {g : G}

@[simp] theorem agreeingGender_nil : agreeingGender gender default [] = default := rfl

theorem agreeingGender_cons_of_eq_some (hg : gender h = some g) :
    agreeingGender gender default (h :: hs) = g := by
  simp [agreeingGender, genderProbe, Probe.search, hg]

theorem agreeingGender_cons_of_eq_none (hh : gender h = none) :
    agreeingGender gender default (h :: hs) = agreeingGender gender default hs := by
  simp [agreeingGender, genderProbe, Probe.search, hh]

theorem agreeingGender_singleton : agreeingGender gender default [h] = (gender h).getD default := by
  cases hg : gender h <;> simp [agreeingGender, genderProbe, Probe.search, hg]

theorem agreeingGender_append_of_forall_eq_none {l l' : List H}
    (hl : ∀ a ∈ l, gender a = none) :
    agreeingGender gender default (l ++ l') = agreeingGender gender default l' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, agreeingGender_cons_of_eq_none (hl a (by simp))]
    exact ih fun b hb ↦ hl b (by simp [hb])

variable {cyclic : H → Prop} [DecidablePred cyclic]

theorem agreeingGender_lastCycle {r : R} {above : List H} (hc : cyclic h)
    (ha : ∀ a ∈ above, ¬ cyclic a ∧ gender a = none) :
    agreeingGender gender default ((⟨r, hs ++ h :: above⟩ : ComplexHead R H).lastCycle cyclic) =
      (gender h).getD default := by
  rw [ComplexHead.lastCycle_mk_append hc fun a ha' ↦ (ha a ha').1,
    agreeingGender_append_of_forall_eq_none fun a ha' ↦ (ha a (by simpa using ha')).2,
    agreeingGender_singleton]

theorem agreeingGender_lastCycle_plain {r : R} (hc : cyclic h) (hh : gender h = none)
    (hg : gender h' = some g) :
    agreeingGender gender default ((⟨r, hs ++ [h', h]⟩ : ComplexHead R H).lastCycle cyclic) =
        default ∧
      agreeingGender gender default (hs ++ [h', h]).reverse = g := by
  constructor
  · rw [show hs ++ [h', h] = (hs ++ [h']) ++ h :: [] by simp,
      agreeingGender_lastCycle (above := []) hc (by simp), hh]
    rfl
  · simp [agreeingGender_cons_of_eq_none hh, agreeingGender_cons_of_eq_some hg]

end HighestGender

end DistributedMorphology
