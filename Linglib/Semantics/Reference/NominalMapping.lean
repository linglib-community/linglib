module

public import Linglib.Semantics.Reference.CovertShift

/-!
# The Nominal Mapping Parameter

The Nominal Mapping Parameter of Chierchia sets what a language's nouns can denote: kinds, so
that they are arguments ([+arg]), or properties, so that they are predicates ([+pred]), or
either. A setting is the set of denotation types nouns take. The setting and the covert type
shifts the language's determiners leave unblocked then decide which bare nominals can be
arguments (`NominalMapping.LicensesBare`): a [+arg, −pred] language admits every bare nominal, a
[−arg, +pred] language none, and a [+arg, +pred] language with ι and ∃ blocked exactly those for
which kind formation ∩ is defined (`NominalMapping.argAndPred_licensesBare_iff`).

## Implementation notes

Whether ∩ is defined for a nominal is a proposition `down` that the consumer supplies, as for
`Determiner.Inventory.Available`. `Kind.down_dom_of_supClosed` and
`IsAntichain.iota_isGreatest_eq_none` decide whether ∩ has a value for cumulative extensions and
for extensions of two or more atoms.

## References

* [chierchia-1998]
* [dayal-2004]
-/

@[expose] public section


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

/-! ### Bare arguments -/

/-- A language with the setting `m` and the determiners `ds` admits as an argument a bare
nominal of number `num` for which ∩ is defined just when `down` holds: it must be [+arg], and if it
is also [+pred], so that its nouns are predicates, ∩ must be defined for the nominal or ι or ∃ must
be unblocked for its number. -/
def LicensesBare (m : NominalMapping) (ds : Determiner.Inventory) (num : Number) (down : Prop) :
    Prop :=
  .kind ∈ m ∧ (.property ∉ m ∨ down ∨ ¬ ds.Blocks num .iota ∨ ¬ ds.Blocks num .exists)

instance (m : NominalMapping) (ds : Determiner.Inventory) (num : Number) (down : Prop)
    [Decidable down] : Decidable (m.LicensesBare ds num down) := by
  unfold LicensesBare; infer_instance

variable {m : NominalMapping} {ds : Determiner.Inventory} {num : Number} {down : Prop}

/-- With ι and ∃ blocked, a [+arg, +pred] language admits exactly the bare nominals ∩ is
defined for. -/
theorem argAndPred_licensesBare_iff (hι : ds.Blocks num .iota) (hex : ds.Blocks num .exists) :
    argAndPred.LicensesBare ds num down ↔ down := by
  simp [LicensesBare, hι, hex]

theorem argAndPred_licensesBare_false_iff :
    argAndPred.LicensesBare ds num False ↔ ¬ ds.Blocks num .iota ∨ ¬ ds.Blocks num .exists := by
  simp [LicensesBare]

/-- A language admits a bare nominal with a kind iff it is [+arg]. -/
theorem licensesBare_true_iff : m.LicensesBare ds num True ↔ .kind ∈ m := by
  simp [LicensesBare]

end NominalMapping
