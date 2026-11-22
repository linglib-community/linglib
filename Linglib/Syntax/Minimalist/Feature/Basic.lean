module

public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Syntax.Feature.Bundle
public import Linglib.Syntax.Feature.Slot
public import Linglib.Syntax.Feature.Person.Features

/-!
# Features for Minimalist Agree

This file defines the feature dimensions that Agree checks and the feature bundles of lexical
items. A dimension is an agreement dimension (`Agreement.Dimension`), one of Harbour's person or
number features (`Person.Feature`, `Number.Feature`), or one of [±wh], [±tense], [Infl], [obl] and
the [E] of a head whose complement is elided. A dimension takes its values from the type that
already defines them; Harbour's features take values in `Bool`, and [E] is privative, with the
single value `()`. A feature bundle has a checking slot (`FeatureSlot`) at each dimension, over
the slot order of the dimension (`FeatureType.Slot`): the slot of the agreement bundle at an
agreement dimension, and the flat slot of the dimension's values elsewhere.

The agreement bundle of a checking bundle (`Agreement.Bundle`) keeps the slot at each agreement
dimension and drops the other dimensions; an agreement bundle is in turn a checking bundle that is
absent where it is unspecified. A checking bundle extends the checking bundle of an agreement
bundle exactly when its own agreement bundle extends that one
(`Minimalist.FeatureBundle.gc_ofAgreement_agreement`). The person slot holds a person
specification (`Syntax/Feature/Person/Specification.lean`), the participant sets the features
copied to the slot leave open, as a probe that has copied [participant] alone is specified for
a speech-act participant and no further ([deal-2024]).

A bundle records whether each feature is valued, not whether it is interpretable. Interpretability
depends on the host as well as on the dimension: agreement features are interpretable on nouns and
uninterpretable on verbs and adjectives ([chomsky-2000]). Keeping the two apart lets a study state
the Valuation/Interpretability Biconditional of [chomsky-2001] as a hypothesis
(`PesetskyTorrego2007.Biconditional`). Interpretability is defined in
`Feature/Interpretability.lean`.

## Main definitions

* `Minimalist.FeatureType`: the dimensions.
* `Minimalist.FeatureType.Value`, `Minimalist.FeatureType.Slot`: the values of a dimension and
  its slot order.
* `Minimalist.FeatureVal`: a dimension with a value.
* `Minimalist.FeatureBundle`: a checking slot at each dimension.
* `Minimalist.FeatureBundle.agreement`: the agreement bundle of a checking bundle.
* `Minimalist.FeatureBundle.ofAgreement`: an agreement bundle as a checking bundle.

## References

* [chomsky-2000]
* [chomsky-2001]
* [deal-2024]
* [adger-2003]
* [bjorkman-2011]
* [harbour-2014]
* [harbour-2016]
* [merchant-2001]
-/

@[expose] public section

namespace Minimalist

/-- The values of [Infl] ([bjorkman-2011]). The temporal or aspectual head that selects a verb
values its [Infl]: `perf` under Perf or Asp, `impf` under imperfective Asp. -/
inductive Infl where
  | perf
  | impf
  deriving Repr, DecidableEq

/-! ### Dimensions and values -/

/-- The feature dimensions that Agree checks. -/
inductive FeatureType where
  | agr (d : Agreement.Dimension)
  | personFeature (f : Person.Feature)
  | numberFeature (f : Number.Feature)
  | wh | tense | infl | oblique
  /-- [E], which leaves the complement of its head unpronounced ([merchant-2001]). -/
  | ellipsis
  deriving Repr, DecidableEq, Fintype

namespace FeatureType

/-- The agreement dimension of person. -/
@[match_pattern] abbrev person : FeatureType := agr .person
/-- The agreement dimension of number. -/
@[match_pattern] abbrev number : FeatureType := agr .number
/-- The agreement dimension of gender. -/
@[match_pattern] abbrev gender : FeatureType := agr .gender
/-- The agreement dimension of case. -/
@[match_pattern] abbrev case : FeatureType := agr .case
/-- Harbour's [±participant]. -/
@[match_pattern] abbrev participant : FeatureType := personFeature .participant
/-- Harbour's [±author]. -/
@[match_pattern] abbrev author : FeatureType := personFeature .speaker
/-- Harbour's [±atomic]. -/
@[match_pattern] abbrev atomic : FeatureType := numberFeature .atomic
/-- Harbour's [±minimal]. -/
@[match_pattern] abbrev minimal : FeatureType := numberFeature .minimal
/-- Harbour's [±additive]. -/
@[match_pattern] abbrev additive : FeatureType := numberFeature .additive

/-- The dimensions as a list, since `Finset.univ.toList` is noncomputable. -/
def all : List FeatureType :=
  [person, number, gender, case, agr .definiteness, participant, author, personFeature .addressee,
   atomic, minimal, additive, wh, tense, infl, oblique, ellipsis]

theorem mem_all (t : FeatureType) : t ∈ all := by
  revert t; decide

/-- The values of a dimension. -/
@[reducible] def Value : FeatureType → Type
  | agr d => d.Value
  | personFeature _ | numberFeature _ => Bool
  | infl => Infl
  | wh | tense | oblique => Bool
  | ellipsis => Unit

instance (t : FeatureType) : DecidableEq t.Value := by
  cases t with
  | agr d => cases d <;> exact inferInstance
  | _ => exact inferInstance

instance (t : FeatureType) : Repr t.Value := by
  cases t with
  | agr d => cases d <;> exact inferInstance
  | _ => exact inferInstance

/-- The slot order of a dimension: that of the agreement bundle at an agreement dimension, so a
person specification for person, and the flat slot of the dimension's values elsewhere. -/
abbrev Slot : FeatureType → Type
  | agr d => d.Slot
  | t => Flat t.Value

instance (t : FeatureType) : DecidableEq t.Slot := by
  cases t with
  | agr d => exact inferInstanceAs (DecidableEq d.Slot)
  | _ => exact inferInstanceAs (DecidableEq (Flat _))

instance (t : FeatureType) : PartialOrder t.Slot := by
  cases t with
  | agr d => exact inferInstanceAs (PartialOrder d.Slot)
  | _ => exact inferInstanceAs (PartialOrder (Flat _))

instance (t : FeatureType) : OrderBot t.Slot := by
  cases t with
  | agr d => exact inferInstanceAs (OrderBot d.Slot)
  | _ => exact inferInstanceAs (OrderBot (Flat _))

instance (t : FeatureType) (x y : t.Slot) : Decidable (Compat x y) := by
  cases t with
  | agr d => exact inferInstanceAs (Decidable (Compat (α := d.Slot) x y))
  | _ => exact inferInstanceAs (Decidable (Compat (α := Flat _) x y))

/-- A value of a dimension as a slot, a person value as the specification of what it covers. -/
def Slot.ofValue : (t : FeatureType) → t.Value → t.Slot
  | agr d, v => Agreement.Dimension.Slot.ofFlat d (v : Flat d.Value)
  | personFeature _, v | numberFeature _, v => (v : Flat Bool)
  | infl, v => (v : Flat Infl)
  | wh, v | tense, v | oblique, v => (v : Flat Bool)
  | ellipsis, v => (v : Flat Unit)

/-- The value a slot holds, if it holds one: the person a specification is that of. -/
def Slot.value? : (t : FeatureType) → t.Slot → Option t.Value
  | agr .person, x => Person.Specification.toPerson? x
  | agr .number, x => x
  | agr .gender, x => x
  | agr .case, x => x
  | agr .definiteness, x => x
  | personFeature _, x | numberFeature _, x => x
  | infl, x => x
  | wh, x | tense, x | oblique, x => x
  | ellipsis, x => x

/-- Unification in the slot order of a dimension, `⊤` where it fails. -/
def Slot.unify : (t : FeatureType) → t.Slot → t.Slot → WithTop t.Slot
  | agr d => Agreement.Dimension.Slot.unify d
  | personFeature _ | numberFeature _ => Flat.unify (α := Bool)
  | infl => Flat.unify (α := Infl)
  | wh | tense | oblique => Flat.unify (α := Bool)
  | ellipsis => Flat.unify (α := Unit)

theorem Slot.isLUB_unify (t : FeatureType) (a b : t.Slot) :
    IsLUB ({↑a, ↑b} : Set (WithTop t.Slot)) (Slot.unify t a b) := by
  cases t with
  | agr d => exact Agreement.Dimension.Slot.isLUB_unify d a b
  | _ => exact Flat.isLUB_unify a b

end FeatureType

/-- A dimension with a value, written `⟨.number, .singular⟩`. -/
abbrev FeatureVal := Σ t : FeatureType, t.Value

/-! ### Feature bundles -/

/-- A checking slot at each dimension, over the dimension's slot order. -/
abbrev FeatureBundle := (t : FeatureType) → FeatureSlot t.Slot

namespace FeatureBundle

/-- The bundle valued `v` at `t` and absent elsewhere. -/
def single (t : FeatureType) (v : t.Value) : FeatureBundle :=
  Function.update (⊥ : FeatureBundle) t ↑(FeatureType.Slot.ofValue t v)

@[simp] theorem single_self (t : FeatureType) (v : t.Value) :
    single t v t = ↑(FeatureType.Slot.ofValue t v) := by
  simp [single]

/-- The bundle with the slots in `l`, absent elsewhere. An earlier entry of `l` overrides a later
one at the same dimension. -/
def ofList (l : List (Σ t : FeatureType, FeatureSlot t.Slot)) : FeatureBundle :=
  l.foldr (fun p b ↦ Function.update b p.1 p.2) ⊥

@[simp] theorem ofList_nil : ofList [] = ⊥ := rfl

/-- The valued features of a bundle, in the order of `FeatureType.all`. -/
def valued (b : FeatureBundle) : List FeatureVal :=
  FeatureType.all.filterMap fun t ↦ (FeatureType.Slot.value? t ((b t).unbotD ⊥)).map (⟨t, ·⟩)

/-- The default bundle is absent everywhere. -/
instance : Inhabited FeatureBundle := ⟨⊥⟩

instance : DecidableEq FeatureBundle :=
  inferInstanceAs (DecidableEq ((t : FeatureType) → FeatureSlot t.Slot))

/-- A bundle is printed as its slots that are not absent. Structures with a bundle field rely on
this instance to derive `Repr`. -/
instance : Repr FeatureBundle where
  reprPrec fb _ :=
    repr <| FeatureType.all.filterMap fun t ↦
      if fb t = ⊥ then none
      else some (reprStr t, reprStr (FeatureType.Slot.value? t ((fb t).unbotD ⊥)))

/-! ### Agreement bundles -/

/-- The agreement bundle of a checking bundle, `⊥` at an agreement dimension that is absent or
unvalued. -/
def agreement (b : FeatureBundle) : Agreement.Bundle := fun d ↦ (b (.agr d)).unbotD ⊥

@[simp] theorem agreement_apply (b : FeatureBundle) (d : Agreement.Dimension) :
    b.agreement d = (b (.agr d)).unbotD ⊥ := rfl

/-- An agreement bundle as a checking bundle, absent wherever it is unspecified. -/
def ofAgreement (c : Agreement.Bundle) : FeatureBundle
  | .agr d => FeatureSlot.ofSlot (c d)
  | _ => ⊥

@[simp] theorem ofAgreement_agr (c : Agreement.Bundle) (d : Agreement.Dimension) :
    ofAgreement c (.agr d) = FeatureSlot.ofSlot (c d) := rfl

/-- A checking bundle extends that of an agreement bundle exactly when its agreement bundle
extends the agreement bundle. -/
theorem gc_ofAgreement_agreement : GaloisConnection ofAgreement agreement := fun c b ↦
  ⟨fun h d ↦ FeatureSlot.gc_ofSlot_unbotD.le_u (h (.agr d)), fun h t ↦ by
    cases t with
    | agr d => exact FeatureSlot.gc_ofSlot_unbotD.l_le (h d)
    | _ => exact bot_le⟩

/-- A checking bundle made from an agreement bundle has that agreement bundle. -/
@[simp] theorem agreement_ofAgreement (c : Agreement.Bundle) : (ofAgreement c).agreement = c :=
  funext fun d ↦ FeatureSlot.unbotD_ofSlot (c d)

/-- `ofAgreement` and `agreement` form a Galois coinsertion. -/
def gciOfAgreement : GaloisCoinsertion ofAgreement agreement :=
  gc_ofAgreement_agreement.toGaloisCoinsertion fun c ↦ (agreement_ofAgreement c).le

theorem monotone_agreement : Monotone agreement := gc_ofAgreement_agreement.monotone_u

theorem monotone_ofAgreement : Monotone ofAgreement := gc_ofAgreement_agreement.monotone_l

theorem agreement_update_agr (b : FeatureBundle) (d : Agreement.Dimension)
    (s : FeatureSlot (FeatureType.agr d).Slot) :
    agreement (Function.update b (.agr d) s) =
      Function.update b.agreement d (s.unbotD ⊥) := by
  funext d'
  rcases eq_or_ne d' d with rfl | hd
  · simp
  · have ht : FeatureType.agr d' ≠ .agr d := by simpa using hd
    simp [Function.update_of_ne, hd, ht]

end FeatureBundle

end Minimalist
