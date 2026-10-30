module

public import Linglib.Semantics.Genericity.NominalMappingParameter
public import Linglib.Semantics.Genericity.Normality
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Mereology
public import Linglib.Fragments.Mandarin.Nouns
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Japanese.Nouns
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.Romance.French.Nouns
public import Linglib.Fragments.Romance.French.Determiners
public import Linglib.Fragments.Romance.Italian.Nouns
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Determiners

/-!
# Chierchia (1998): Reference to kinds across languages

Chierchia's Nominal Mapping Parameter sets whether a language's nouns denote kinds, predicates, or
either: Chinese and Japanese are [+arg, −pred], the Romance languages [−arg, +pred], and English
[+arg, +pred]. The languages of the sample whose fragments count nouns through classifiers are
[exactly the argument-only ones](##hasClassifiers_iff). A language's determiners decide which
covert type shifts it blocks, [none in an argument-only language](##argOnly_blocks_nothing), and
with the parameter which bare nominals it admits as arguments, in English
[a bare singular only where ∩ is defined for it](##english_licensesBare_singular_iff). ∩ and ∪
[undo each other](##down_up), and ∩ is [undefined for a singular property](##down_notMem_of_atom).
A generic bare plural [entails its episodic reading](##some_up_of_mem_dogsBark).

## Main definitions

* `Chierchia1998.Language.nominalMapping`: the setting of the parameter in each sampled language.
* `Chierchia1998.up`, `Chierchia1998.down`: ∪ and ∩, (15) and (16).
* `Chierchia1998.dogsBark`, `Chierchia1998.computersRoute`: the generic logical forms (38b) and
  (39b).

## Implementation notes

Each language's blocking is derived from its fragment's determiner inventory by
`Determiner.Inventory.Blocks`, and whether it has classifiers from its fragment's common nouns
(`Language.nouns`): a Mandarin or Japanese noun records the classifiers that count it, and an
English, French or Italian noun is a `ClassifiedNoun` over no classifiers. The generalized
classifier system of (20) has every noun counted through a classifier, while the fragments attest
classifiers rather than that: Mandarin counts the measure noun *tiān* bare
(`exists_isBareCount_mandarin`). The generic operator is the conditional over the normal cases
of a `Genericity.Normality`. The set `K` of kinds is a parameter, primitive as in the paper, and its
one stated property, that no kind has a singular instance in every situation, is a hypothesis.
∩ and ∪ are ι and its partial inverse Id applied at each situation (pp. 359–360), Id sending an
individual to its parts, `Set.Iic`; on a lower set taking the largest member is the partial
inverse of `Set.Iic` (`IsLowerSet.iota_isGreatest`). (17b) is stated for a property that is mass
at each situation, closed downward and under sum, and finite there; membership of ∩P in `K`
adds nothing to it.

## Errata

* (25e) prints Id(x) = λx[x ≤ y], binding the wrong variable; the text above footnote 14, which
  has ι undone via the part-of relation, and the footnote's Id(x) = λy[y = x] for a singularity
  give Id(x) = λy[y ≤ x].

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

/-- The type of the classifiers of the fragment of `l`, empty for a language without
classifiers. -/
abbrev ClassifierType : Language → Type
  | mandarin | japanese => Classifier
  | french | italian | english => Empty

/-- `nouns l` is the list of common nouns of the fragment of `l`. -/
def nouns : (l : Language) → List (ClassifiedNoun l.ClassifierType)
  | mandarin => Mandarin.Nouns.nouns.map (·.toClassifiedNoun)
  | japanese => Japanese.Nouns.nouns.map (·.toClassifiedNoun)
  | french => French.Nouns.nouns.map (·.toClassifiedNoun)
  | italian => Italian.Nouns.nouns.map (·.toClassifiedNoun)
  | english => English.Nouns.nouns.map (·.toClassifiedNoun)

/-- The language has classifiers: some common noun of its fragment is counted through one. -/
def HasClassifiers (l : Language) : Prop := ∃ n ∈ l.nouns, n.classifiers.Nonempty

end Language

open Chierchia1998.Language

/-- (20): the languages of the sample with classifiers are exactly the [+arg, −pred] ones. -/
theorem hasClassifiers_iff (l : Language) : l.HasClassifiers ↔ l.nominalMapping = .argOnly := by
  cases l
  · exact iff_of_true ⟨Mandarin.Nouns.ren.toClassifiedNoun,
      List.mem_map_of_mem (by simp [Mandarin.Nouns.nouns]), Mandarin.Classifiers.ge,
      by simp [Mandarin.Nouns.ren]⟩ rfl
  · exact iff_of_true ⟨Japanese.Nouns.inu.toClassifiedNoun,
      List.mem_map_of_mem (by simp [Japanese.Nouns.nouns]), Japanese.Classifiers.hiki,
      by simp [Japanese.Nouns.inu]⟩ rfl
  all_goals exact iff_of_false (fun ⟨_, _, c, _⟩ ↦ c.elim) (by decide)

theorem exists_isBareCount_mandarin : ∃ n ∈ Language.mandarin.nouns, n.IsBareCount :=
  ⟨Mandarin.Nouns.tian.toClassifiedNoun, List.mem_map_of_mem (by simp [Mandarin.Nouns.nouns]),
    by simp [Mandarin.Nouns.tian, ClassifiedNoun.IsBareCount]⟩

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

/-- ∪, (15): the instances of a kind at a situation are the parts of its value there. -/
def up [Preorder E] (k : S → Option E) (s : S) : Set E := (k s).elim ∅ Set.Iic

/-- The concept of the largest member of a property's extension at each situation, which is ∩
of (16) where it is a kind. -/
noncomputable def down [LE E] (P : S → Set E) (s : S) : Option E := iota (IsGreatest (P s))

/-- ∩∪d = d, and ∪∩P = P for mass P, (17a, b). -/
theorem down_up [PartialOrder E] (k : S → Option E) : down (up k) = k :=
  funext fun s ↦ iota_isGreatest_elim_Iic (k s)

theorem up_down [SemilatticeSup E] (hP : ∀ s, IsLowerSet (P s)) (hcum : ∀ s, SupClosed (P s))
    (hfin : ∀ s, (P s).Finite) : up (down P) = P :=
  funext fun s ↦ elim_Iic_iota_isGreatest (hP s) fun hne ↦
    iota_isGreatest_isSome_iff.1 ((hcum s).directedOn.iota_isGreatest_isSome (hfin s) hne)

/-- ∩ is undefined for a singular property: its concept is singular in every situation, and no
kind is. -/
theorem down_notMem_of_atom [PartialOrder E]
    (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, Atom d) (hP : ∀ s, ∀ x ∈ P s, Atom x) : down P ∉ K :=
  fun h ↦ hK _ h fun s _ hd ↦ hP s _ (iota_isGreatest_eq_some_iff.1 hd).1

/-- The concept of a property closed under sum is not singular in every situation once its
extension somewhere is finite and has a plurality. -/
theorem not_forall_atom_down [SemilatticeSup E] {s : S} {x : E}
    (hfin : (P s).Finite) (hcum : SupClosed (P s)) (hx : x ∈ P s) (hx0 : ¬ IsBot x)
    (hxa : ¬ Atom x) : ¬ ∀ s, ∀ d ∈ down P s, Atom d := fun h ↦ by
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
      ¬ l.determiners.Lexicalizes .iota ∧ ¬ l.determiners.Lexicalizes .exists := by
  decide

theorem argOnly_licensesBare (num : Number) (down : Prop) :
    (nominalMapping .mandarin).LicensesBare (determiners .mandarin) num down ∧
      (nominalMapping .japanese).LicensesBare (determiners .japanese) num down := by
  simp [NominalMapping.LicensesBare, nominalMapping]

/-- The [−arg, +pred] languages of the sample have a definite article and so block ι. -/
theorem predOnly_blocks_iota :
    ∀ l : Language, l.nominalMapping = .predOnly → l.determiners.Lexicalizes .iota := by
  decide

theorem predOnly_not_licensesBare (num : Number) (down : Prop) :
    ¬ (nominalMapping .french).LicensesBare (determiners .french) num down ∧
      ¬ (nominalMapping .italian).LicensesBare (determiners .italian) num down := by
  simp [NominalMapping.LicensesBare, nominalMapping]

/-- English, [+arg, +pred] with *the* blocking ι and *a* blocking ∃ for singulars, admits a bare
singular exactly where kind formation is defined for it. -/
theorem english_licensesBare_singular_iff (down : Prop) :
    (nominalMapping .english).LicensesBare (determiners .english) .singular down ↔ down :=
  NominalMapping.argAndPred_licensesBare_iff (by decide) (by decide)

/-- English admits every bare plural and mass noun, by ∃ where kind formation is undefined, since
*a* selects the singular. -/
theorem english_licensesBare_of_ne_singular {num : Number} (hnum : num ≠ .singular)
    (down : Prop) : (nominalMapping .english).LicensesBare (determiners .english) num down := by
  have key : ∀ n : Number, n ≠ .singular → ¬ (determiners .english).Blocks n .exists := by
    decide
  exact ⟨by decide, .inr (.inr (.inr (key num hnum)))⟩

open Mereology in
/-- English admits no bare singular count noun, (24b), since ∩ is undefined for it. -/
theorem english_not_licensesBare_singular {S E : Type*} [PartialOrder E]
    {K : Set (S → Option E)} {P : S → Set E} (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, Atom d)
    (hP : ∀ s, ∀ x ∈ P s, Atom x) :
    ¬ (nominalMapping .english).LicensesBare (determiners .english) .singular (down P ∈ K) :=
  (english_licensesBare_singular_iff _).not.2 (down_notMem_of_atom hK hP)

/-! ### Bare plurals in generic and episodic sentences, §4.1 -/

section Generic

open Genericity

variable {S E : Type*} [PartialOrder E]

/-- *Dogs bark* (38b), `Gn x, s [∪∩dog(x) ∧ C(x, s)] [bark(x, s)]`, puts the instances of the
kind in the restriction of the generic operator, which binds them with the situations. -/
def dogsBark (N : Normality S (E × S)) (dog : S → Set E) (C : Set (E × S))
    (bark : E → S → Prop) : Set S :=
  N.gen ({p | p.1 ∈ up (down dog) p.2} ∩ C) {p | bark p.1 p.2}

/-- In *Computers route modern planes* (39b), the object is fronted into the restriction of the
generic operator and the subject is reconstructed into its scope, where derived kind predication
reads it existentially. -/
def computersRoute (N : Normality S (E × S)) (computer plane : S → Set E) (C : Set (E × S))
    (route : E → E → S → Prop) : Set S :=
  N.gen ({p | p.1 ∈ up (down plane) p.2} ∩ C)
    {p | Quantifier.Det.some (up (down computer) p.2)
      (route · p.1 p.2)}

/-- In (39b) the fronted bare plural is universal over the normal cases, and the one in scope
existential over its kind's instances (p. 368). -/
theorem mem_computersRoute {N : Normality S (E × S)} {computer plane : S → Set E}
    {C : Set (E × S)} {route : E → E → S → Prop} {s : S} :
    s ∈ computersRoute N computer plane C route ↔
      ∀ p ∈ N.normal s ({p | p.1 ∈ up (down plane) p.2} ∩ C),
        ∃ x ∈ up (down computer) p.2, route x p.1 p.2 :=
  Iff.rfl

/-- The generic reading of a bare plural (38b) entails its episodic reading by derived kind
predication (31c) wherever the kind has a normal instance. -/
theorem some_up_of_mem_dogsBark {N : Normality S (E × S)} {dog : S → Set E} {C : Set (E × S)}
    {bark : E → S → Prop} {s s' : S} {x : E} (h : s ∈ dogsBark N dog C bark)
    (hx : (x, s') ∈ N.normal s ({p | p.1 ∈ up (down dog) p.2} ∩ C)) :
    Quantifier.Det.some (up (down dog) s') (bark · s') :=
  ⟨x, (N.normal_subset s _ hx).1, h hx⟩

end Generic

end Chierchia1998
