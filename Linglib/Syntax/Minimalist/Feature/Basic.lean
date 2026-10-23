module

public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Minimalist.Feature.Slot
public import Linglib.Syntax.Person.Features

/-!
# Features for Minimalist Agree

A feature dimension is a kind of feature that Agree checks: an agreement dimension
(`Agreement.Dimension`), one of Harbour's person or number features (`Person.Feature`,
`Number.Feature`), or a Minimalist feature such as [±wh]. Each takes its values from the type
that already owns it, so the person dimension here is the person of an agreement bundle, and
Harbour's features are bivalent. A feature value is a dimension with a value in it, and two
values share a dimension when their first components agree. A feature bundle assigns each
dimension a three-state checking slot: absent, unvalued (a probe), or valued.

Interpretability is orthogonal to valuation. Chomsky's interpretable features contribute to LF
(the φ-features of a noun, categorial features), and uninterpretable ones must be checked and
deleted before it (the φ-features of T and v, the case of a noun); which a feature is depends on
its host as well as its dimension.

## Main definitions

* `Minimalist.FeatureType`, `Minimalist.FeatureType.ValueOf` — the dimensions and their values
* `Minimalist.FeatureVal` — a dimension with a value
* `Minimalist.FeatureBundle` — a checking slot at each dimension, with `ofList`, `toList` and
  `valued`
* `Minimalist.FeatureBundle.agreement`, `Minimalist.FeatureBundle.ofAgreement` — the agreement
  content of a checking bundle and the embedding of an agreement bundle, a Galois coinsertion
  (`FeatureBundle.gciAgreement`)
* `Minimalist.Interpretability` — ±interpretable

## References

* [chomsky-1995], [chomsky-2000], [chomsky-2001]
* [adger-2003]
* [bjorkman-2011] — the [Infl] feature
* [harbour-2014] — the number features
* [harbour-2016] — the person features
* [marcolli-chomsky-berwick-2025] — bundles as assignments
-/

@[expose] public section

namespace Minimalist


/-- The inflectional feature `[Infl]` ([bjorkman-2011]) is valued on the verb by the higher temporal
or aspectual head that selects it, `perf` for a participle under Perf/Asp and `impf` under
imperfective Asp. -/
inductive Infl where
  | perf
  | impf
  deriving Repr, DecidableEq

/-! ### Dimensions and values -/

/-- The feature dimensions Agree checks are the agreement dimensions, Harbour's person and number
features, and the Minimalist [±wh], [±tense], [Infl] and [obl]. -/
inductive FeatureType where
  | agr (d : Agreement.Dimension)
  | personFeature (f : Person.Feature)
  | numberFeature (f : Number.Feature)
  | wh | tense | infl | oblique
  deriving Repr, DecidableEq, Fintype

namespace FeatureType

/-- `person` is the agreement dimension of person. -/
@[match_pattern] abbrev person : FeatureType := agr .person
/-- `number` is the agreement dimension of number. -/
@[match_pattern] abbrev number : FeatureType := agr .number
/-- `gender` is the agreement dimension of gender. -/
@[match_pattern] abbrev gender : FeatureType := agr .gender
/-- `case` is the agreement dimension of case. -/
@[match_pattern] abbrev case : FeatureType := agr .case
/-- `participant` is Harbour's [±participant]. -/
@[match_pattern] abbrev participant : FeatureType := personFeature .participant
/-- `author` is Harbour's [±author]. -/
@[match_pattern] abbrev author : FeatureType := personFeature .author
/-- `atomic` is Harbour's [±atomic]. -/
@[match_pattern] abbrev atomic : FeatureType := numberFeature .atomic
/-- `minimal` is Harbour's [±minimal]. -/
@[match_pattern] abbrev minimal : FeatureType := numberFeature .minimal

/-- All feature dimensions, for computable enumeration (`Finset.univ.toList` is
noncomputable). -/
def all : List FeatureType :=
  [person, number, gender, case, agr .definiteness, participant, author, atomic, minimal,
   wh, tense, infl, oblique]

/-- Every dimension is listed in `all`. -/
theorem mem_all (t : FeatureType) : t ∈ all := by
  revert t; decide

/-- The value type of a dimension is that of the agreement dimension it is, [Infl]'s values, or
`Bool` for the bivalent features. -/
@[reducible] def ValueOf : FeatureType → Type
  | agr d => d.Value
  | personFeature _ | numberFeature _ => Bool
  | infl => Infl
  | wh | tense | oblique => Bool

instance (t : FeatureType) : DecidableEq t.ValueOf := by
  cases t with
  | agr d => exact inferInstance
  | _ => exact inferInstance

instance (t : FeatureType) : Repr t.ValueOf := by
  cases t with
  | agr d => cases d <;> exact inferInstance
  | _ => exact inferInstance

end FeatureType

/-- A feature value is a dimension with a value in it, written `⟨.person, .first⟩`. -/
abbrev FeatureVal := Σ t : FeatureType, t.ValueOf

/-! ### Feature bundles

A feature bundle is a total assignment from the dimensions to three-state checking slots
(`Minimalist.FeatureSlot`), absent, unvalued or valued, after [marcolli-chomsky-berwick-2025],
whose free-Merge core keeps the features of a syntactic object atomic, so the slots are an
Agree-layer structure decoupled from the `SyntacticObject` carrier. -/

/-- A feature bundle assigns each dimension a checking slot. -/
abbrev FeatureBundle := (t : FeatureType) → Minimalist.FeatureSlot t.ValueOf

namespace FeatureBundle

/-- The bundle has a valued feature of the given dimension. -/
def hasValuedFeature (a : FeatureBundle) (t : FeatureType) : Bool :=
  (a t).isValued

/-- The bundle has an unvalued (probe) feature of the given dimension. -/
def hasUnvaluedFeature (a : FeatureBundle) (t : FeatureType) : Bool :=
  (a t).isUnvalued

/-- The value at the given dimension, when valued. -/
def getValuedFeature (a : FeatureBundle) (t : FeatureType) : Option t.ValueOf :=
  (a t).value?

/-- The assignment specifying exactly one valued dimension, all others absent. -/
def single (t : FeatureType) (v : t.ValueOf) : FeatureBundle :=
  Function.update (⊥ : FeatureBundle) t (.valued v)

@[simp] theorem single_self (t : FeatureType) (v : t.ValueOf) :
    single t v t = .valued v := by
  simp [single]

/-- The bundle read off a list of slots, the list head winning on a repeated dimension. -/
def ofList (l : List (Σ t : FeatureType, Minimalist.FeatureSlot t.ValueOf)) : FeatureBundle :=
  l.foldr (fun p b ↦ Function.update b p.1 p.2) ⊥

@[simp] theorem ofList_nil : ofList [] = ⊥ := rfl

/-- The specified slots of a bundle, in `FeatureType.all` order. -/
def toList (b : FeatureBundle) : List (Σ t : FeatureType, Minimalist.FeatureSlot t.ValueOf) :=
  FeatureType.all.filterMap fun t ↦ if (b t).isSpecified then some ⟨t, b t⟩ else none

/-- The valued features of a bundle, in `FeatureType.all` order. -/
def valued (b : FeatureBundle) : List FeatureVal :=
  FeatureType.all.filterMap fun t ↦ (b t).value?.map (⟨t, ·⟩)

/-- The everywhere-`absent` bundle is the default. -/
instance : Inhabited FeatureBundle := ⟨⊥⟩

instance : DecidableEq FeatureBundle :=
  inferInstanceAs (DecidableEq ((t : FeatureType) → Minimalist.FeatureSlot t.ValueOf))

/-- A bundle is rendered by its specified (non-`absent`) dimensions. The function carrier has no
structural `Repr`, so containing structures that `deriving Repr` rely on this. -/
instance : Repr FeatureBundle where
  reprPrec fb _ :=
    repr <| FeatureType.all.filterMap fun t ↦
      if (fb t).isSpecified then some (reprStr t, reprStr (fb t)) else none

/-! ### The agreement restriction

`FeatureType.agr` embeds the agreement dimensions and `FeatureSlot.ofFlat` embeds the flat slot,
so a checking bundle restricts to its agreement content and an agreement bundle embeds as a
checking bundle, borne exactly on its specified dimensions: reindexing along the embedding
composed with the slot maps, a Galois coinsertion. -/

/-- The agreement content of a checking bundle: a valued agreement dimension keeps its value, an
unvalued or absent one is unspecified. -/
def agreement (b : FeatureBundle) : Agreement.Bundle := fun d ↦ (b (.agr d)).toFlat

@[simp] theorem agreement_apply (b : FeatureBundle) (d : Agreement.Dimension) :
    b.agreement d = (b (.agr d)).toFlat := rfl

/-- An agreement bundle as a checking bundle, borne and valued exactly on its specified agreement
dimensions and absent elsewhere. -/
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

/-- The checking layer sits over the agreement layer by a Galois coinsertion. -/
def gciAgreement : GaloisCoinsertion ofAgreement agreement :=
  gc_ofAgreement_agreement.toGaloisCoinsertion fun c ↦ (agreement_ofAgreement c).le

theorem monotone_agreement : Monotone agreement := gc_ofAgreement_agreement.monotone_u

theorem monotone_ofAgreement : Monotone ofAgreement := gc_ofAgreement_agreement.monotone_l

/-- Updating a checking bundle at an agreement dimension updates its agreement content there. -/
theorem agreement_update_agr (b : FeatureBundle) (d : Agreement.Dimension)
    (s : FeatureSlot d.Value) :
    agreement (Function.update b (.agr d) s) = Function.update b.agreement d s.toFlat := by
  funext d'
  rcases eq_or_ne d' d with rfl | hd
  · simp
  · have ht : FeatureType.agr d' ≠ .agr d := by simpa using hd
    simp [Function.update_of_ne, hd, ht]

end FeatureBundle

/-! ### Interpretability -/

/-- A feature is interpretable when it contributes to LF and uninterpretable when it must be
checked and deleted before LF ([chomsky-1995]). The distinction is orthogonal to valuation: the
φ-features of a noun are interpretable and valued, those of T and v uninterpretable and
unvalued. -/
inductive Interpretability where
  | interpretable
  | uninterpretable
  deriving Repr, DecidableEq

end Minimalist
