module

public import Linglib.Morphology.DistributedMorphology.Locality
public import Linglib.Syntax.Minimalist.Feature.Interpretability
public import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# Gender on the nominal categorizer

This file defines the gender features of the nominal categorizer n in Distributed Morphology. A
gender feature is a binary dimension such as [±FEM] with a sign, and it is interpretable for
natural gender and uninterpretable for arbitrary gender. A categorizing head may also bear the
selectional feature {D}, which licenses an inalienable possessor.

Agreement in gender is a probe relativized to gender, searching the heads of a nominal from the
top, and the gender it agrees in is that of the first head bearing one; when no head does, Agree
fails, and the probe is spelled out by whatever Vocabulary Item mentions no gender. When several
n's are stacked, Kramer's Highest Gender Hypothesis makes the gender of the highest n the agreeing
gender. Kramer derives it from cyclicity: each n is a cyclic head that sends the nPs below it to
spell-out, so the probe searches the last cycle of the word alone, where
[it finds the highest cyclic
head](##DistributedMorphology.agreeingGender_lastCycle_concat_of_cyclic) and
[sees through a noncyclic head bearing no
gender](##DistributedMorphology.agreeingGender_lastCycle_concat_of_not_cyclic). A probe searching
every head [finds whatever the cyclic probe
finds](##DistributedMorphology.agreeingGender_reverse_of_lastCycle), so the two
[differ only where the cyclic probe fails above a gendered
head](##DistributedMorphology.agreeingGender_lastCycle_ne_iff), as under a plain highest n.

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
structure Categorizer where
  /-- The category, n, v or a. -/
  cat : Minimalist.Cat
  /-- The gender feature, if any. -/
  gender : Option GenderFeature := none
  /-- The selectional feature {D}. -/
  selectsD : Bool := false
  deriving DecidableEq, Repr

namespace Categorizer

/-- The n bearing the gender feature of interpretability `interp` and value `v`. -/
def gendered (interp : Interpretability) (v : GenderValue) : Categorizer where
  cat := .n
  gender := some ⟨interp, v⟩

/-- The n with no gender feature. -/
def n_plain : Categorizer where
  cat := .n

/-- The n bearing interpretable [+FEM], the natural feminine. -/
def n_iFem : Categorizer := gendered .interpretable ⟨.fem, .pos⟩

/-- The n bearing interpretable [−FEM], the natural masculine. -/
def n_iMasc : Categorizer := gendered .interpretable ⟨.fem, .neg⟩

/-- The n bearing uninterpretable [+FEM], the arbitrary feminine. -/
def n_uFem : Categorizer := gendered .uninterpretable ⟨.fem, .pos⟩

/-- The n bearing uninterpretable [−FEM], the arbitrary masculine. -/
def n_uMasc : Categorizer := gendered .uninterpretable ⟨.fem, .neg⟩

/-- The n bearing uninterpretable [+ANIM], the nominalizer of Teop body-part roots. -/
def n_uAnim : Categorizer := gendered .uninterpretable ⟨.anim, .pos⟩

end Categorizer

/-! ### Agreement in gender -/

section HighestGender

open Minimalist ComplexHead

variable {R H G : Type*} (gender : H → Option G)

/-- The probe for gender, relativized to the heads that bear one. -/
def genderProbe : Probe H := Probe.relativized fun h ↦ (gender h).isSome

/-- The gender a gender probe agrees in when it searches `goals`, nearest first, which is `none`
when Agree fails. -/
def agreeingGender (goals : List H) : Option G :=
  ((genderProbe gender).search goals).bind gender

/-- The agreeing gender is the gender of the first goal that bears one. -/
@[simp]
theorem agreeingGender_eq_findSome? (goals : List H) :
    agreeingGender gender goals = goals.findSome? gender := by
  induction goals with
  | nil => rfl
  | cons a l ih =>
    cases hg : gender a <;>
      simp_all [agreeingGender, genderProbe, Probe.search]

variable {gender} {h : H} {hs : List H} {g : G} {cyclic : H → Prop} [DecidablePred cyclic] {r : R}
  {s : ComplexHead R H}

/-- The Highest Gender Hypothesis. A probe above a word whose highest head is cyclic agrees in the
gender of that head, whatever lies below it. -/
theorem agreeingGender_lastCycle_concat_of_cyclic (hc : cyclic h) :
    agreeingGender gender ((⟨r, hs ++ [h]⟩ : ComplexHead R H).lastCycle cyclic) = gender h := by
  simp [hc]

/-- A noncyclic head bearing no gender leaves the agreeing gender of the word it merges with. -/
theorem agreeingGender_lastCycle_concat_of_not_cyclic (hc : ¬ cyclic h) (hh : gender h = none) :
    agreeingGender gender ((⟨r, hs ++ [h]⟩ : ComplexHead R H).lastCycle cyclic) =
      agreeingGender gender ((⟨r, hs⟩ : ComplexHead R H).lastCycle cyclic) := by
  simp [hc, hh]

/-- A probe confined to the last cycle that finds a gender finds the one a probe searching every
head finds. -/
theorem agreeingGender_reverse_of_lastCycle
    (hg : agreeingGender gender (s.lastCycle cyclic) = some g) :
    agreeingGender gender s.heads.reverse = some g := by
  rw [agreeingGender_eq_findSome?] at hg ⊢
  exact (lastCycle_prefix s cyclic).findSome?_eq_some hg

/-- The probe confined to the last cycle and the probe searching every head differ exactly when
the first fails over a head that bears a gender. -/
theorem agreeingGender_lastCycle_ne_iff :
    agreeingGender gender (s.lastCycle cyclic) ≠ agreeingGender gender s.heads.reverse ↔
      agreeingGender gender (s.lastCycle cyclic) = none ∧
        ∃ a ∈ s.heads, (gender a).isSome := by
  cases hc : agreeingGender gender (s.lastCycle cyclic) with
  | none => simp [eq_comm (a := none), ← Option.isSome_iff_ne_none]
  | some g => simp [(agreeingGender_reverse_of_lastCycle hc).symm]

end HighestGender

end DistributedMorphology
