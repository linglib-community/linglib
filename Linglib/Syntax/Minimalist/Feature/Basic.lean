module

public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Syntax.Agreement.Bundle
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
absent where it is unspecified. These two maps form a
[Galois coinsertion](##Minimalist.FeatureBundle.gciAgreement).

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

## References

* [chomsky-2000]
* [chomsky-2001]
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
@[match_pattern] abbrev author : FeatureType := personFeature .author
/-- Harbour's [±atomic]. -/
@[match_pattern] abbrev atomic : FeatureType := numberFeature .atomic
/-- Harbour's [±minimal]. -/
@[match_pattern] abbrev minimal : FeatureType := numberFeature .minimal

/-- The dimensions as a list, since `Finset.univ.toList` is noncomputable. -/
def all : List FeatureType :=
  [person, number, gender, case, agr .definiteness, participant, author, atomic, minimal,
   wh, tense, infl, oblique, ellipsis]

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
  | agr d => exact inferInstance
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

/-- The agreement bundle of a checking bundle, `⊥` at an agreement dimension that is absent or
unvalued. -/
def agreement (b : FeatureBundle) : Agreement.Bundle := fun d ↦ (b (.agr d)).toFlat

@[simp] theorem agreement_apply (b : FeatureBundle) (d : Agreement.Dimension) :
    b.agreement d = (b (.agr d)).toFlat := rfl

/-- An agreement bundle as a checking bundle, absent wherever it is unspecified. -/
def ofAgreement (c : Agreement.Bundle) : FeatureBundle := fun t ↦
  match t with
  | .agr d => .ofFlat (c d)
  | _ => ⊥

@[simp] theorem ofAgreement_agr (c : Agreement.Bundle) (d : Agreement.Dimension) :
    ofAgreement c (.agr d) = .ofFlat (c d) := rfl

@[simp] theorem agreement_ofAgreement (c : Agreement.Bundle) : (ofAgreement c).agreement = c :=
  funext fun d ↦ FeatureSlot.toFlat_ofFlat (c d)

theorem gc_ofAgreement_agreement : GaloisConnection ofAgreement agreement := by
  intro c b
  constructor
  · exact fun h d ↦ (FeatureSlot.gc_ofFlat_toFlat _ _).1 (h (.agr d))
  · intro h t
    cases t
    case agr d => exact (FeatureSlot.gc_ofFlat_toFlat _ _).2 (h d)
    all_goals exact bot_le

/-- `ofAgreement` and `agreement` form a Galois coinsertion. -/
def gciAgreement : GaloisCoinsertion ofAgreement agreement :=
  gc_ofAgreement_agreement.toGaloisCoinsertion fun c ↦ (agreement_ofAgreement c).le

theorem monotone_agreement : Monotone agreement := gc_ofAgreement_agreement.monotone_u

theorem monotone_ofAgreement : Monotone ofAgreement := gc_ofAgreement_agreement.monotone_l

theorem agreement_update_agr (b : FeatureBundle) (d : Agreement.Dimension)
    (s : FeatureSlot d.Value) :
    agreement (Function.update b (.agr d) s) = Function.update b.agreement d s.toFlat := by
  funext d'
  rcases eq_or_ne d' d with rfl | hd
  · simp
  · have ht : FeatureType.agr d' ≠ .agr d := by simpa using hd
    simp [Function.update_of_ne, hd, ht]

end FeatureBundle

end Minimalist
