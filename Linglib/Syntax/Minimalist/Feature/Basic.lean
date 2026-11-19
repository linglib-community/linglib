module

public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Syntax.Feature.Bundle
public import Linglib.Syntax.Feature.Slot
public import Linglib.Syntax.Person.Features

/-!
# Features for Minimalist Agree

This file defines the feature dimensions that Agree checks and the feature bundles of lexical
items. A dimension is an agreement dimension (`Agreement.Dimension`), one of Harbour's person or
number features (`Person.Feature`, `Number.Feature`), or one of [±wh], [±tense], [Infl], [obl] and
the [E] of a head whose complement is elided. A dimension takes its values from the type that
already defines them; Harbour's features take values in `Bool`, and [E] is privative, with the
single value `()`. A feature bundle has a checking slot (`FeatureSlot`) at each dimension.

The agreement bundle of a checking bundle (`Agreement.Bundle`) keeps the value at each agreement
dimension and drops the other dimensions; an agreement bundle is in turn a checking bundle that is
absent where it is unspecified, and [has that agreement
bundle](##Minimalist.FeatureBundle.agreement_ofAgreement). The person of a checking slot is a
person specification (`Syntax/Person/Specification.lean`), the participant sets the features
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
* `Minimalist.FeatureType.Value`: the values of a dimension.
* `Minimalist.FeatureVal`: a dimension with a value.
* `Minimalist.FeatureBundle`: a checking slot at each dimension.
* `Minimalist.FeatureBundle.agreement`: the agreement bundle of a checking bundle.
* `Minimalist.FeatureBundle.ofAgreement`: an agreement bundle as a checking bundle.

## TODO

A checking slot compares two valued persons by equality, so a slot valued for the first person
does not extend to one valued for the inclusive, and the map from agreement bundles is not
monotone in the person dimension. Valuation of the person slot should be unification of
specifications.

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
  | agr .person => Person.Specification
  | agr .number => Number
  | agr .gender => UD.Gender
  | agr .case => Case
  | agr .definiteness => UD.Definite
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

end FeatureType

/-- A dimension with a value, written `⟨.person, .first⟩`. -/
abbrev FeatureVal := Σ t : FeatureType, t.Value

/-! ### Feature bundles -/

/-- A checking slot at each dimension. -/
abbrev FeatureBundle := (t : FeatureType) → FeatureSlot t.Value

namespace FeatureBundle

/-- The bundle valued `v` at `t` and absent elsewhere. -/
def single (t : FeatureType) (v : t.Value) : FeatureBundle :=
  Function.update (⊥ : FeatureBundle) t (.valued v)

@[simp] theorem single_self (t : FeatureType) (v : t.Value) :
    single t v t = .valued v := by
  simp [single]

/-- The bundle with the slots in `l`, absent elsewhere. An earlier entry of `l` overrides a later
one at the same dimension. -/
def ofList (l : List (Σ t : FeatureType, FeatureSlot t.Value)) : FeatureBundle :=
  l.foldr (fun p b ↦ Function.update b p.1 p.2) ⊥

@[simp] theorem ofList_nil : ofList [] = ⊥ := rfl

/-- The valued features of a bundle, in the order of `FeatureType.all`. -/
def valued (b : FeatureBundle) : List FeatureVal :=
  FeatureType.all.filterMap fun t ↦
    match b t with
    | .valued v => some ⟨t, v⟩
    | _ => none

/-- The default bundle is absent everywhere. -/
instance : Inhabited FeatureBundle := ⟨⊥⟩

instance : DecidableEq FeatureBundle :=
  inferInstanceAs (DecidableEq ((t : FeatureType) → FeatureSlot t.Value))

/-- A bundle is printed as its slots that are not absent. Structures with a bundle field rely on
this instance to derive `Repr`. -/
instance : Repr FeatureBundle where
  reprPrec fb _ :=
    repr <| FeatureType.all.filterMap fun t ↦
      if fb t = .absent then none else some (reprStr t, reprStr (fb t))

/-! ### Agreement bundles -/

/-- A value of a checking slot at an agreement dimension, or `⊥`, as the agreement slot: a person
specification is its own slot. -/
def slotOfFlat : (d : Agreement.Dimension) → Flat (FeatureType.agr d).Value → d.Slot
  | .person, x => x.recBotCoe ⊥ id
  | .number, x => x
  | .gender, x => x
  | .case, x => x
  | .definiteness, x => x

/-- An agreement slot as a value of a checking slot or `⊥`, the unspecified person being `⊥`. -/
def flatOfSlot : (d : Agreement.Dimension) → d.Slot → Flat (FeatureType.agr d).Value
  | .person, x => if x = ⊥ then ⊥ else (x : Flat Person.Specification)
  | .number, x => x
  | .gender, x => x
  | .case, x => x
  | .definiteness, x => x

@[simp] theorem slotOfFlat_flatOfSlot (d : Agreement.Dimension) (x : d.Slot) :
    slotOfFlat d (flatOfSlot d x) = x := by
  cases d
  · by_cases h : x = ⊥ <;> simp [slotOfFlat, flatOfSlot, h]
  all_goals rfl

theorem monotone_slotOfFlat (d : Agreement.Dimension) : Monotone (slotOfFlat d) := by
  cases d
  · intro x y h
    induction x using Flat.recBotCoe with
    | bot => exact bot_le
    | coe a => rw [Flat.coe_le_iff.1 h]
  all_goals exact monotone_id

/-- The agreement bundle of a checking bundle, `⊥` at an agreement dimension that is absent or
unvalued. -/
def agreement (b : FeatureBundle) : Agreement.Bundle := fun d ↦ slotOfFlat d (b (.agr d)).toFlat

@[simp] theorem agreement_apply (b : FeatureBundle) (d : Agreement.Dimension) :
    b.agreement d = slotOfFlat d (b (.agr d)).toFlat := rfl

/-- An agreement bundle as a checking bundle, absent wherever it is unspecified. -/
def ofAgreement (c : Agreement.Bundle) : FeatureBundle := fun t ↦
  match t with
  | .agr d => .ofFlat (flatOfSlot d (c d))
  | _ => ⊥

@[simp] theorem ofAgreement_agr (c : Agreement.Bundle) (d : Agreement.Dimension) :
    ofAgreement c (.agr d) = .ofFlat (flatOfSlot d (c d)) := rfl

/-- A checking bundle made from an agreement bundle has that agreement bundle. -/
@[simp] theorem agreement_ofAgreement (c : Agreement.Bundle) : (ofAgreement c).agreement = c :=
  funext fun d ↦ by simp [agreement, FeatureSlot.toFlat_ofFlat]

theorem monotone_agreement : Monotone agreement := fun _ _ h d ↦
  monotone_slotOfFlat d (FeatureSlot.gc_ofFlat_toFlat.monotone_u (h (.agr d)))

theorem agreement_update_agr (b : FeatureBundle) (d : Agreement.Dimension)
    (s : FeatureSlot (FeatureType.agr d).Value) :
    agreement (Function.update b (.agr d) s) =
      Function.update b.agreement d (slotOfFlat d s.toFlat) := by
  funext d'
  rcases eq_or_ne d' d with rfl | hd
  · simp
  · have ht : FeatureType.agr d' ≠ .agr d := by simpa using hd
    simp [Function.update_of_ne, hd, ht]

end FeatureBundle

end Minimalist
