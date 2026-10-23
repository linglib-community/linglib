module

public import Linglib.Semantics.Genericity.NominalMappingParameter
public import Linglib.Semantics.Genericity.Normality
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Mereology
public import Linglib.Fragments.Mandarin.Nouns
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Japanese.Classifiers
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.Romance.French.Determiners
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.English.Determiners

/-!
# Chierchia (1998): Reference to kinds across languages

Chierchia's Nominal Mapping Parameter sets whether a language's nouns denote kinds, predicates,
or either: Chinese and Japanese are [+arg, −pred], the Romance languages [−arg, +pred], and
English [+arg, +pred]. In a [+arg, −pred] language every noun denotes a kind, so its extension is
mass and a numeral needs a classifier. A language's determiners decide which covert type shifts
it blocks, and with the parameter which bare nominals it admits as arguments. A bare plural
denotes its kind, whose instances meet the existential of derived kind predication in an
episodic sentence and the generic operator in a generic one. A kind sends each situation to a
partial individual, ∩ takes the largest member of a property's extension (`iota` of
`IsGreatest`) where the result is a kind, and ∪ takes the parts of a kind's value (`Set.Iic`).

## Main definitions

* `Chierchia1998.Language.nominalMapping`: the setting of the parameter in each sampled language.
* `Chierchia1998.dogsBark`, `Chierchia1998.computersRoute`: the generic logical forms (38b) and
  (39b).

## Main results

* `Chierchia1998.hasClassifiers_iff`: the classifier languages of the sample are the
  [+arg, −pred] ones.
* `Chierchia1998.argOnly_blocks_nothing`, `Chierchia1998.predOnly_blocks_iota`: blocking in the
  sampled languages.
* `Chierchia1998.iota_isGreatest_notMem_of_atom`,
  `Chierchia1998.not_forall_atom_iota_isGreatest`: ∩ is undefined for a singular property, and
  the concept of a sum-closed property with a plurality is not singular everywhere.
* `Chierchia1998.english_licensesBare_iff`, `Chierchia1998.english_not_licensesBare_singular`:
  English admits exactly the bare nominals for which ∩ is defined, and so no bare singular.
* `Chierchia1998.mem_computersRoute`: Diesing's generalization for (39b).
* `Chierchia1998.some_up_of_mem_dogsBark`: the generic reading of a bare plural entails its
  existential reading at a situation with a normal instance.

## Implementation notes

Each language's blocking is derived from its fragment's determiner inventory by
`Determiner.Inventory.Blocks`. The generic operator is the conditional over the normal cases of a
`Genericity.Normality`. The set `K` of kinds is a parameter, primitive as in the paper, and its
one stated property, that no kind has a singular instance in every situation, is a hypothesis.

## References

* [chierchia-1998]
-/

@[expose] public section

namespace Chierchia1998

open Genericity

/-- The sample covers five of the languages the paper discusses. -/
inductive Language where
  | mandarin | japanese | french | italian | english
  deriving DecidableEq, Fintype

namespace Language

/-- `nominalMapping l` is the setting of the Nominal Mapping Parameter in `l`. -/
def nominalMapping : Language → NominalMapping
  | mandarin | japanese => .argOnly
  | french | italian => .predOnly
  | english => .argAndPred

/-- `determiners l` is the determiner inventory of the fragment of `l`. -/
def determiners : Language → Determiner.Inventory
  | mandarin => Mandarin.Determiners.inventory
  | japanese => Japanese.Determiners.inventory
  | french => French.Determiners.inventory
  | italian => Italian.Determiners.inventory
  | english => English.Determiners.inventory

/-- The language has numeral classifiers, as its fragment records for Mandarin and Japanese; the
Romance languages and English have none. -/
def HasClassifiers : Language → Prop
  | mandarin => Mandarin.Classifiers.classifiers.Nonempty
  | japanese => Japanese.Classifiers.classifiers.Nonempty
  | french | italian | english => False

end Language

open Language

/-- A [+arg, −pred] language has a generalized classifier system, and a classifier language must
be [+arg, −pred]: the classifier languages of the sample are exactly the [+arg, −pred] ones. -/
theorem hasClassifiers_iff : ∀ l : Language, l.HasClassifiers ↔ l.nominalMapping = .argOnly
  | .mandarin =>
    iff_of_true ⟨Mandarin.Classifiers.ge, by simp [Mandarin.Classifiers.classifiers]⟩ rfl
  | .japanese =>
    iff_of_true ⟨Japanese.Classifiers.tsu, by simp [Japanese.Classifiers.classifiers]⟩ rfl
  | .french | .italian | .english => iff_of_false id (by decide)

/-! ### Kind formation, §2

∩ takes a property to the individual concept that picks out the largest member of its extension
at each situation, where that concept is a kind, (16), and is undefined otherwise. A kind cannot
have a singular instance in every situation (p. 351), so ∩ is undefined for a singular property,
which is true of atoms only. A plural is true of the pluralities of its singular, (10a), and a
mass noun comes out of the lexicon already pluralized, closed under sum (p. 347); where such an
extension is finite and has a plurality, its largest member is that plurality or above it, so its
concept passes the condition (pp. 351 and 357). -/

section KindFormation

open Mereology

variable {S E : Type*} {K : Set (S → Option E)} {P : S → Set E}

/-- ∩ is undefined for a singular property: its concept is singular in every situation, and no
kind is. -/
theorem iota_isGreatest_notMem_of_atom [PartialOrder E]
    (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, Atom d) (hP : ∀ s, ∀ x ∈ P s, Atom x) :
    (fun s ↦ iota (IsGreatest (P s))) ∉ K :=
  fun h ↦ hK _ h fun s _ hd ↦ hP s _ (iota_isGreatest_eq_some_iff.1 hd).1

/-- The concept of a property closed under sum is not singular in every situation once its
extension somewhere is finite and has a plurality. -/
theorem not_forall_atom_iota_isGreatest [SemilatticeSup E] {s : S} {x : E}
    (hfin : (P s).Finite) (hcum : SupClosed (P s)) (hx : x ∈ P s) (hx0 : ¬ IsBot x)
    (hxa : ¬ Atom x) : ¬ ∀ s, ∀ d ∈ iota (IsGreatest (P s)), Atom d := fun h ↦ by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1
    (hcum.directedOn.iota_isGreatest_isSome hfin ⟨x, hx⟩)
  have hma := h s m hm
  exact hxa (hma.eq ((iota_isGreatest_eq_some_iff.1 hm).2 hx) hx0 ▸ hma)

end KindFormation

/-! ### Bare arguments and type-shift blocking

The determiner inventory of each sampled language decides by the Blocking Principle which
covert shifts it blocks, and with the mapping which bare nominals it admits as arguments
(`NominalMapping.LicensesBare`), given whether ∩ is defined for the nominal. -/

/-- A [+arg, −pred] language has no articles and so blocks neither ι nor ∃, and ∩ is never
blocked: all three of Chierchia's shifts are available to Mandarin and Japanese bare nouns. -/
theorem argOnly_blocks_nothing :
    ∀ l : Language, l.nominalMapping = .argOnly →
      ¬ l.determiners.Blocks .iota ∧ ¬ l.determiners.Blocks .exists := by
  decide

theorem argOnly_licensesBare (down : Prop) :
    (nominalMapping .mandarin).LicensesBare (determiners .mandarin) down ∧
      (nominalMapping .japanese).LicensesBare (determiners .japanese) down := by
  simp [NominalMapping.LicensesBare, nominalMapping]

/-- The [−arg, +pred] languages of the sample have a definite article and so block ι. -/
theorem predOnly_blocks_iota :
    ∀ l : Language, l.nominalMapping = .predOnly → l.determiners.Blocks .iota := by
  decide

theorem predOnly_not_licensesBare (down : Prop) :
    ¬ (nominalMapping .french).LicensesBare (determiners .french) down ∧
      ¬ (nominalMapping .italian).LicensesBare (determiners .italian) down := by
  simp [NominalMapping.LicensesBare, nominalMapping]

/-- English, [+arg, +pred] with *the* and *a* blocking ι and ∃, admits exactly the bare nominals
kind formation is defined for. -/
theorem english_licensesBare_iff (down : Prop) :
    (nominalMapping .english).LicensesBare (determiners .english) down ↔ down :=
  NominalMapping.argAndPred_licensesBare_iff (by decide) (by decide)

open Mereology in
/-- English admits no bare singular count noun, (24b), since ∩ is undefined for it. -/
theorem english_not_licensesBare_singular {S E : Type*} [PartialOrder E]
    {K : Set (S → Option E)} {P : S → Set E} (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, Atom d)
    (hP : ∀ s, ∀ x ∈ P s, Atom x) :
    ¬ (nominalMapping .english).LicensesBare (determiners .english)
      ((fun s ↦ iota (IsGreatest (P s))) ∈ K) :=
  (english_licensesBare_iff _).not.2 (iota_isGreatest_notMem_of_atom hK hP)

/-! ### Bare plurals in generic and episodic sentences, §4.1 -/

section Generic

open Genericity

variable {S E : Type*} [PartialOrder E]

/-- *Dogs bark* (38b), `Gn x, s [∪∩dog(x) ∧ C(x, s)] [bark(x, s)]`, puts the instances of the
kind in the restriction of the generic operator, which binds them with the situations. -/
def dogsBark (N : Normality S (E × S)) (dog : S → Set E) (C : Set (E × S))
    (bark : E → S → Prop) : Set S :=
  N.gen ({p | p.1 ∈ (iota (IsGreatest (dog p.2))).elim ∅ Set.Iic} ∩ C) {p | bark p.1 p.2}

/-- In *Computers route modern planes* (39b), the object is fronted into the restriction of the
generic operator and the subject is reconstructed into its scope, where derived kind predication
reads it existentially. -/
def computersRoute (N : Normality S (E × S)) (computer plane : S → Set E) (C : Set (E × S))
    (route : E → E → S → Prop) : Set S :=
  N.gen ({p | p.1 ∈ (iota (IsGreatest (plane p.2))).elim ∅ Set.Iic} ∩ C)
    {p | Quantifier.GQ.some ((iota (IsGreatest (computer p.2))).elim (∅ : Set E) Set.Iic)
      (route · p.1 p.2)}

/-- In (39b) the fronted bare plural is universal over the normal cases, and the one in scope
existential over its kind's instances (p. 368). -/
theorem mem_computersRoute {N : Normality S (E × S)} {computer plane : S → Set E}
    {C : Set (E × S)} {route : E → E → S → Prop} {s : S} :
    s ∈ computersRoute N computer plane C route ↔
      ∀ p ∈ N.normal s ({p | p.1 ∈ (iota (IsGreatest (plane p.2))).elim ∅ Set.Iic} ∩ C),
        ∃ x ∈ (iota (IsGreatest (computer p.2))).elim ∅ Set.Iic, route x p.1 p.2 :=
  Iff.rfl

/-- The generic reading of a bare plural (38b) entails its episodic reading by derived kind
predication (31c) wherever the kind has a normal instance. -/
theorem some_up_of_mem_dogsBark {N : Normality S (E × S)} {dog : S → Set E} {C : Set (E × S)}
    {bark : E → S → Prop} {s s' : S} {x : E} (h : s ∈ dogsBark N dog C bark)
    (hx : (x, s') ∈ N.normal s ({p | p.1 ∈ (iota (IsGreatest (dog p.2))).elim ∅ Set.Iic} ∩ C)) :
    Quantifier.GQ.some ((iota (IsGreatest (dog s'))).elim (∅ : Set E) Set.Iic) (bark · s') :=
  ⟨x, (N.normal_subset s _ hx).1, h hx⟩

end Generic

end Chierchia1998
