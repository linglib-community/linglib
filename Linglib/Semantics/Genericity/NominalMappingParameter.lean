module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# The Nominal Mapping Parameter

The Nominal Mapping Parameter of Chierchia sets what a language's nouns can denote: kinds, so
that they are arguments ([+arg]), or properties, so that they are predicates ([+pred]), or
either. A setting is the set of denotation types nouns take. The setting and the language's
determiners then decide which bare nominals can be arguments. A covert type shift is blocked when
a determiner lexicalizes it, the Blocking Principle. A [+arg, +pred] language with both articles
then admits exactly the bare nominals for which kind formation ∩ is defined, a [+arg, −pred]
language every bare nominal, and a [−arg, +pred] language none.

## Main definitions

* `NominalMapping`: a setting of the parameter, with the three attested settings `argOnly`,
  `argAndPred` and `predOnly`.
* `CovertShift`, `Determiner.Inventory.Blocks`: the covert type shifts and the Blocking
  Principle.
* `NominalMapping.LicensesBare`: the bare nominals a language admits as arguments.

## Main results

* `NominalMapping.argAndPred_licensesBare_iff`: with ι and ∃ blocked, a [+arg, +pred] language
  admits exactly the bare nominals ∩ is defined for.
* `NominalMapping.licensesBare_true_iff`: a language admits a bare nominal with a kind iff it is
  [+arg].

## Implementation notes

Whether ∩ is defined for a nominal is a proposition `down` that the consumer supplies, as for
`Determiner.Inventory.Available`. It depends on the nominal's denotation and not on its number
and countability alone, since a plural property anchored to particular entities has no kind.
`DirectedOn.iota_isGreatest_isSome` and `IsAntichain.iota_isGreatest_eq_none` decide it for
cumulative extensions and for extensions of two or more atoms.

## References

* [chierchia-1998]
* [dayal-2004]
* [jenks-2018]
* [moroney-2021]
-/

@[expose] public section

namespace Genericity

/-- A noun denotes a kind, of type e, or a property, of type ⟨e,t⟩. -/
inductive NominalDenotation where
  | kind
  | property
  deriving DecidableEq, Repr, Fintype

/-- A setting of the Nominal Mapping Parameter is the set of denotation types a language's nouns can
take. The language is [+arg] when `.kind` is in the setting and [+pred] when `.property` is; the
empty setting, [−arg, −pred], leaves nouns nothing to denote and is excluded by the paper. -/
def NominalMapping := Finset NominalDenotation

namespace NominalMapping

instance : Membership NominalDenotation NominalMapping :=
  inferInstanceAs (Membership NominalDenotation (Finset NominalDenotation))

instance : DecidableEq NominalMapping := inferInstanceAs (DecidableEq (Finset NominalDenotation))

instance (d : NominalDenotation) (m : NominalMapping) : Decidable (d ∈ m) :=
  Finset.decidableMem d m

/-- [+arg, −pred]: nouns denote kinds (Mandarin, Japanese). -/
def argOnly : NominalMapping := ({.kind} : Finset NominalDenotation)

/-- [+arg, +pred]: nouns denote kinds or properties (English, Germanic). -/
def argAndPred : NominalMapping := ({.kind, .property} : Finset NominalDenotation)

/-- [−arg, +pred]: nouns denote properties (Romance, Greek). -/
def predOnly : NominalMapping := ({.property} : Finset NominalDenotation)

@[simp] theorem mem_argOnly {d : NominalDenotation} : d ∈ argOnly ↔ d = .kind := by
  cases d <;> decide

@[simp] theorem mem_argAndPred {d : NominalDenotation} : d ∈ argAndPred := by cases d <;> decide

@[simp] theorem mem_predOnly {d : NominalDenotation} : d ∈ predOnly ↔ d = .property := by
  cases d <;> decide

/-- A nominal can denote a kind outright in a [+arg] language, and otherwise under an overt
determiner. -/
def CanDenoteKind (m : NominalMapping) (hasD : Prop) : Prop := .kind ∈ m ∨ hasD

instance (m : NominalMapping) (hasD : Prop) [Decidable hasD] :
    Decidable (m.CanDenoteKind hasD) := by
  unfold CanDenoteKind; infer_instance

/-- A nominal can denote a property in a [+pred] language. -/
def CanDenoteProperty (m : NominalMapping) : Prop := .property ∈ m

instance (m : NominalMapping) : Decidable m.CanDenoteProperty := by
  unfold CanDenoteProperty; infer_instance

end NominalMapping

/-! ### Covert type shifts -/

/-- The covert type shifts are kind formation ∩, the definite ι and the existential ∃ of
[chierchia-1998], and the anaphoric definite ι^x of [jenks-2018], which [moroney-2021] makes
covert. -/
inductive CovertShift where
  | down
  | iota
  | iotaAnaphoric
  | exists
  deriving DecidableEq, Repr, Fintype

end Genericity

/-! ### The Blocking Principle -/

namespace Determiner.Inventory

open Genericity (CovertShift)

/-- The Blocking Principle of [chierchia-1998]: a covert shift is blocked when a determiner of
the inventory lexicalizes it. A definite article is ι and an indefinite article ∃; a determiner
that obligatorily expones anaphoric definiteness is ι^x ([moroney-2021]); no determiner is ∩. -/
def Blocks (ds : Inventory) : CovertShift → Prop
  | .down => False
  | .iota => ∃ e ∈ ds, e.kind = .article .definite
  | .iotaAnaphoric => ds.Marks .familiarity
  | .exists => ∃ e ∈ ds, e.kind = .article .indefinite

instance (ds : Inventory) : DecidablePred ds.Blocks := fun τ ↦ by
  cases τ <;> unfold Blocks <;> infer_instance

theorem not_blocks_down (ds : Inventory) : ¬ ds.Blocks .down := nofun

theorem blocks_exists_iff (ds : Inventory) : ds.Blocks .exists ↔ ds.Realizes .indefinite :=
  Iff.rfl

theorem blocks_iotaAnaphoric_iff (ds : Inventory) :
    ds.Blocks .iotaAnaphoric ↔ ds.Realizes .anaphoric :=
  Iff.rfl

end Determiner.Inventory

namespace Genericity.NominalMapping

/-! ### Bare arguments -/

/-- A language with the setting `m` and the determiners `ds` admits as an argument a bare
nominal for which ∩ is defined just when `down` holds: it must be [+arg], and if it is also
[+pred], so that its nouns are predicates, ∩ must be defined for the nominal or ι or ∃ must be
unblocked. -/
def LicensesBare (m : NominalMapping) (ds : Determiner.Inventory) (down : Prop) : Prop :=
  .kind ∈ m ∧ (.property ∉ m ∨ down ∨ ¬ ds.Blocks .iota ∨ ¬ ds.Blocks .exists)

instance (m : NominalMapping) (ds : Determiner.Inventory) (down : Prop) [Decidable down] :
    Decidable (m.LicensesBare ds down) := by
  unfold LicensesBare; infer_instance

variable {m : NominalMapping} {ds : Determiner.Inventory} {down : Prop}

theorem argAndPred_licensesBare_iff (hι : ds.Blocks .iota) (hex : ds.Blocks .exists) :
    argAndPred.LicensesBare ds down ↔ down := by
  simp [LicensesBare, hι, hex]

theorem argAndPred_licensesBare_false_iff :
    argAndPred.LicensesBare ds False ↔ ¬ ds.Blocks .iota ∨ ¬ ds.Blocks .exists := by
  simp [LicensesBare]

theorem licensesBare_true_iff : m.LicensesBare ds True ↔ .kind ∈ m := by
  simp [LicensesBare]

end Genericity.NominalMapping
