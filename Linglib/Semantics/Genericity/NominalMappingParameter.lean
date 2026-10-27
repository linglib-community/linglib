module

public import Linglib.Semantics.Reference.Determiner

/-!
# The Nominal Mapping Parameter

The Nominal Mapping Parameter of Chierchia sets what a language's nouns can denote: kinds, so
that they are arguments ([+arg]), or properties, so that they are predicates ([+pred]), or
either. A setting is the set of denotation types nouns take. The setting and the language's
determiners then decide which bare nominals can be arguments. A covert type shift is blocked when
a determiner lexicalizes it, the Blocking Principle, and a determiner lexicalizes a shift when it
denotes what the shift denotes. An article lexicalizes the definite shifts of its strengths, and a
demonstrative, whose deictic presupposition can fail where the definite's does not, lexicalizes
none. A [+arg, +pred] language with both articles
then admits exactly the bare nominals for which kind formation ∩ is defined, a [+arg, −pred]
language every bare nominal, and a [−arg, +pred] language none.

## Main definitions

* `NominalMapping`: a setting of the parameter, with the three attested settings `argOnly`,
  `argAndPred` and `predOnly`.
* `CovertShift`, `Determiner.Entry.Lexicalizes`, `Determiner.Inventory.Blocks`: the covert type
  shifts, a determiner denoting one, and the Blocking Principle.
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

namespace Determiner.Entry

open Genericity (CovertShift)
open DefiniteDescription (Restrictor bare unique anaphoric)
open scoped Denotes

/-- A determiner lexicalizes a covert shift when it denotes what the shift denotes on every
restrictor in its domain, [dayal-2004]'s Blocking Principle. An article lexicalizes ι when one of
its readings is the bare definite on every model, and ι^x when one is the strong article at every
index. A demonstrative would have to equal the shift at every context of utterance and vicinity
relation, and a possessive at every possessor and possession relation, which their presuppositions
prevent (`not_lexicalizes_demonstrative`, `not_lexicalizes_possessive`). An indefinite article is
∃, and no determiner is ∩. -/
def Lexicalizes : Entry → CovertShift → Prop
  | .article a, .iota => ∀ (E W : Type) (R : Restrictor E W) (d : ℕ),
      (bare R).toNominal ∈ a.denotations R d
  | .article a, .iotaAnaphoric => ∀ (E W : Type) (R : Restrictor E W) (d : ℕ),
      (anaphoric R d).toNominal ∈ a.denotations R d
  | .article a, .exists => a.definiteness = .indefinite
  | .demonstrative dem, .iota => ∀ (E W P T : Type) [PartialOrder E]
      (c : Kaplan.Context W E P T) (χ : SetRel E E) (R : Restrictor E W) (d : ℕ),
      dem.denote R d c χ = (bare R).toNominal
  | .demonstrative dem, .iotaAnaphoric => ∀ (E W P T : Type) [PartialOrder E]
      (c : Kaplan.Context W E P T) (χ : SetRel E E) (R : Restrictor E W) (d : ℕ),
      dem.denote R d c χ = (anaphoric R d).toNominal
  | .possessive p, .iota => ∀ (E W : Type) (R : Restrictor E W) (possessor : Assignment E → W → E)
      (rel : Assignment E → W → E → E → Prop), p.denote R possessor rel = (bare R).toNominal
  | .possessive p, .iotaAnaphoric => ∀ (E W : Type) (R : Restrictor E W) (d : ℕ)
      (possessor : Assignment E → W → E) (rel : Assignment E → W → E → E → Prop),
      p.denote R possessor rel = (anaphoric R d).toNominal
  | _, _ => False

/-- The restrictor true of everything, with two satisfiers in `Bool`. -/
private abbrev top : Restrictor Bool Unit := fun _ _ _ ↦ True

/-- With two satisfiers the weak article is undefined and the strong one picks the indexed
entity. -/
private theorem unique_ne_anaphoric : (unique top).toNominal ≠ (anaphoric top 0).toNominal := by
  intro h
  have h' := congrFun (congrFun (congrArg Nominal.selector h) fun _ ↦ true) ()
  rw [DefiniteDescription.toNominal_selector, DefiniteDescription.toNominal_selector,
    DefiniteDescription.denote_unique_eq_none_of_ne top _ _ (x := true) (y := false) trivial
      trivial (by decide)] at h'
  exact Option.some_ne_none true
    (h'.trans ((DefiniteDescription.denote_anaphoric_eq_some_iff top 0 _ ()).2 ⟨trivial, rfl⟩)).symm

/-- A context of utterance on the one-element types. -/
private abbrev unitContext : Kaplan.Context Unit Unit Unit Unit := ⟨(), (), (), (), ()⟩

theorem lexicalizes_article_iota_iff (a : Article) :
    (article a).Lexicalizes .iota ↔ .uniqueness ∈ a.strengths := by
  refine ⟨fun h ↦ ?_, fun h _ _ R d ↦ ⟨_, ⟨_, h, rfl⟩, rfl⟩⟩
  obtain ⟨_, ⟨p, hp, rfl⟩, hk⟩ := h Bool Unit top 0
  cases p
  · exact hp
  · exact absurd hk.symm unique_ne_anaphoric

theorem lexicalizes_article_iotaAnaphoric_iff (a : Article) :
    (article a).Lexicalizes .iotaAnaphoric ↔ .familiarity ∈ a.strengths := by
  refine ⟨fun h ↦ ?_, fun h _ _ R d ↦ ⟨_, ⟨_, h, rfl⟩, rfl⟩⟩
  obtain ⟨_, ⟨p, hp, rfl⟩, hk⟩ := h Bool Unit top 0
  cases p
  · exact absurd hk unique_ne_anaphoric
  · exact hp

/-- A demonstrative lexicalizes no covert shift: where no referent has the indexed one in its
vicinity, its deictic presupposition fails and the definite's does not. -/
theorem not_lexicalizes_demonstrative (dem : DemonstrativeDeterminer) (τ : CovertShift) :
    ¬ (demonstrative dem).Lexicalizes τ := by
  have key : ∀ k : DefiniteDescription Unit Unit,
      dem.denote (fun _ _ _ ↦ True) 0 unitContext ⊥ ≠ k.toNominal := fun k h ↦ by
    have h' := congrFun (congrFun (congrArg Nominal.presup h) fun _ ↦ ()) ()
    simp [DemonstrativeDeterminer.denote, SetRel.image] at h'
  cases τ
  exacts [id, fun h ↦ key _ (h Unit Unit Unit Unit unitContext ⊥ _ 0),
    fun h ↦ key _ (h Unit Unit Unit Unit unitContext ⊥ _ 0), id]

/-- A possessive lexicalizes no covert shift: under the empty possession relation it is undefined
where the definite is not. -/
theorem not_lexicalizes_possessive (p : PossessiveDeterminer) (τ : CovertShift) :
    ¬ (possessive p).Lexicalizes τ := by
  have key : ∀ k : DefiniteDescription Unit Unit, (⟦k⟧ (fun _ ↦ ()) ()).isSome →
      p.denote (fun _ _ _ ↦ True) (fun _ _ ↦ ()) (fun _ _ _ _ ↦ False) ≠ k.toNominal :=
    fun k hk h ↦ by
      have h' := congrFun (congrFun (congrArg Nominal.selector h) fun _ ↦ ()) ()
      rw [PossessiveDeterminer.denote_selector, DefiniteDescription.toNominal_selector] at h'
      rw [← h', DefiniteDescription.denote_possessive_isSome_iff] at hk
      simp at hk
  cases τ
  · exact id
  · exact fun h ↦ key (bare fun _ _ _ ↦ True)
      ((DefiniteDescription.denote_isSome_iff _ _ _).2 ⟨(), trivial, fun _ _ ↦ rfl⟩)
      (h Unit Unit _ _ _)
  · exact fun h ↦ key (anaphoric (fun _ _ _ ↦ True) 0)
      ((DefiniteDescription.denote_anaphoric_isSome_iff _ _ _ _).2 trivial) (h Unit Unit _ 0 _ _)
  · exact id

theorem lexicalizes_iota_iff (e : Entry) : e.Lexicalizes .iota ↔ e.Marks .uniqueness := by
  cases e with
  | article a => exact lexicalizes_article_iota_iff a
  | demonstrative dem => exact iff_of_false (not_lexicalizes_demonstrative dem _) (by simp [Marks,
      strengths, uses])
  | quantifier _ => exact iff_of_false id (by simp [Marks, strengths, uses])
  | possessive p => exact iff_of_false (not_lexicalizes_possessive p _) (by simp [Marks, strengths,
      uses])

theorem lexicalizes_iotaAnaphoric_iff (e : Entry) :
    e.Lexicalizes .iotaAnaphoric ↔ e.Marks .familiarity := by
  cases e with
  | article a => exact lexicalizes_article_iotaAnaphoric_iff a
  | demonstrative dem => exact iff_of_false (not_lexicalizes_demonstrative dem _) (by simp [Marks,
      strengths, uses])
  | quantifier _ => exact iff_of_false id (by simp [Marks, strengths, uses])
  | possessive p => exact iff_of_false (not_lexicalizes_possessive p _) (by simp [Marks, strengths,
      uses])

theorem lexicalizes_exists_iff (e : Entry) :
    e.Lexicalizes .exists ↔ e.kind = .article .indefinite := by
  cases e <;> simp [Lexicalizes, kind]

theorem not_lexicalizes_down (e : Entry) : ¬ e.Lexicalizes .down := by
  cases e <;> exact id

instance (e : Entry) : DecidablePred e.Lexicalizes
  | .down => isFalse (not_lexicalizes_down e)
  | .iota => decidable_of_iff _ (lexicalizes_iota_iff e).symm
  | .iotaAnaphoric => decidable_of_iff _ (lexicalizes_iotaAnaphoric_iff e).symm
  | .exists => decidable_of_iff _ (lexicalizes_exists_iff e).symm

end Determiner.Entry

namespace Determiner.Inventory

open Genericity (CovertShift)

/-- The Blocking Principle of [chierchia-1998]: a covert shift is blocked when a determiner of
the inventory lexicalizes it. An article marking familiarity alone, as Akan *nó*, leaves ι to the
bare noun, and a demonstrative blocks nothing. -/
def Blocks (ds : Inventory) (τ : CovertShift) : Prop := ∃ e ∈ ds, e.Lexicalizes τ

instance (ds : Inventory) : DecidablePred ds.Blocks := fun _ ↦ by unfold Blocks; infer_instance

theorem not_blocks_down (ds : Inventory) : ¬ ds.Blocks .down :=
  fun ⟨e, _, h⟩ ↦ e.not_lexicalizes_down h

theorem blocks_exists_iff (ds : Inventory) : ds.Blocks .exists ↔ ds.Realizes .indefinite :=
  exists_congr fun e ↦ and_congr_right fun _ ↦ e.lexicalizes_exists_iff

theorem blocks_iota_iff (ds : Inventory) : ds.Blocks .iota ↔ ds.Realizes .unique :=
  exists_congr fun e ↦ and_congr_right fun _ ↦ e.lexicalizes_iota_iff

theorem blocks_iotaAnaphoric_iff (ds : Inventory) :
    ds.Blocks .iotaAnaphoric ↔ ds.Realizes .anaphoric :=
  exists_congr fun e ↦ and_congr_right fun _ ↦ e.lexicalizes_iotaAnaphoric_iff

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

/-- With ι and ∃ blocked, a [+arg, +pred] language admits exactly the bare nominals ∩ is
defined for. -/
theorem argAndPred_licensesBare_iff (hι : ds.Blocks .iota) (hex : ds.Blocks .exists) :
    argAndPred.LicensesBare ds down ↔ down := by
  simp [LicensesBare, hι, hex]

theorem argAndPred_licensesBare_false_iff :
    argAndPred.LicensesBare ds False ↔ ¬ ds.Blocks .iota ∨ ¬ ds.Blocks .exists := by
  simp [LicensesBare]

/-- A language admits a bare nominal with a kind iff it is [+arg]. -/
theorem licensesBare_true_iff : m.LicensesBare ds True ↔ .kind ∈ m := by
  simp [LicensesBare]

end Genericity.NominalMapping
