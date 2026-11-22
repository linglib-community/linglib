module

public import Linglib.Semantics.Genericity.MeaningPreservation
public import Linglib.Semantics.Genericity.Normality
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Reference.Kind
public import Linglib.Semantics.Plurality.Algebra
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
public import Linglib.Fragments.Slavic.Russian.Nouns
public import Linglib.Fragments.Slavic.Russian.Determiners
public import Linglib.Data.Examples.Chierchia1998
public import Linglib.Data.Examples.Languages
public import Studies.Carlson1977

/-!
# Chierchia (1998): Reference to kinds across languages

The Nominal Mapping Parameter of [chierchia-1998] sets whether the nouns of a language denote
kinds, so that they are arguments, properties, so that they are predicates, or either. A kind is
an individual concept whose value at a situation is the sum of its instances. The operator ∪,
`Kind.up`, takes that value to the set of its parts, and ∩, `Kind.down`, takes the extension of a
property to its largest member. The plural `PL t` of a set `t` of atoms is the set of individuals
outside `t` whose atoms are all in `t`.

Where nouns denote kinds, the extension of a noun is ∪ of its kind. That set is closed downward,
and in an atomic domain its plural is empty (`PL_up`), while the plural of the atoms is every
other individual (`mem_PL_isMin`). The sampled languages whose fragments count nouns through
classifiers are the ones whose nouns denote kinds (`hasClassifiers_iff`). Such a language admits
every bare nominal as an argument, and one whose nouns denote properties admits none unless it
has a null determiner, which a governing head licenses. A language with both settings admits a
bare nominal where ∩ is defined for it or where no determiner lexicalizes the definite or the
existential shift: with its two articles English admits a bare singular exactly where ∩ is
defined (`english_licensesBare_singular_iff`), which it is not for a singular property, and
Russian, with no article, admits every bare nominal (`russian_licensesBare`).
`Language.AdmitsBare` puts these together, and the judgments of the paper's examples with a bare
argument are the ones it gives (`bare_rows`), where ∩ is defined or not for the extension each
class of noun has in a model of two atoms (`down_extension_mem_kinds_iff`).

An English bare plural is shifted by ∩ where ∩ is defined for it and by ∃ otherwise
(`english_plural_shift_iff`). The first is the name of a kind and the second a quantifier, an
`Argument`. Raised over an operator, a kind leaves a trace that is a kind, so it has the reading
it has in place (`Argument.raise_kind`), while the quantifier has a second reading. A predicate
of objects holds of a kind iff the kind's value is in the predicate's upper closure
(`Argument.apply_kind_iff`).

Carlson's predication of a state of a kind is the existential over the instances of its concept
(`carlson_mem_image_iff`), so a state passes from a kind to any kind whose instances include its
own (`carlson_119`). A generic sentence with a bare plural (`dogsBark`, `computersRoute`) entails
the existential one wherever the kind has a normal instance (`some_up_of_mem_dogsBark`).

## Implementation notes

Each language's blocking is derived from its fragment's determiner inventory by
`Determiner.Inventory.Blocks`, and whether it has classifiers from its fragment's common nouns
(`Language.nouns`): a Mandarin or Japanese noun records the classifiers that count it, and a noun
of the other languages is a `ClassifiedNoun` over no classifiers. The paper has every noun of a
kind-denoting language counted through a classifier, while the fragments attest classifiers
rather than that: Mandarin counts the measure noun *tiān* bare (`exists_isBareCount_mandarin`).

`PL_up` takes the atomicity of the domain as two hypotheses, that every individual has an atom
as a part and that an individual is part of whatever its atoms are part of, since the
individuals have no null element; Link's nonempty sets of atoms meet both
(`PL_up_individual`).

The set `K` of kinds is a parameter, primitive as in the paper, and its property that no kind
has a singular instance in every situation is a hypothesis, read with the paper's "(when
defined)": no kind is singular in every situation where it has a value. The paper restricts
kinds further to concepts that identify classes of objects with a sufficiently regular function
or behavior, which is not formalized. A weaker condition, that no kind be necessarily
instantiated by one individual, would not exclude ∩ of a singular property with no instance in
some situation (the first `example` of the kind-formation section). The identity ∪∩P = P ∪ AT_P
for a plural P is stated with AT_P, "the set that generates P under PL", read as the atoms
beneath members of P (`up_down_PL`): read as the singular property itself, it fails at a
situation with exactly one instance, where the plural has no member.

`Language.AdmitsBare` licenses the null determiner under government alone, leaving out
licensing by focus, and under it chooses a shift as a language with both settings does. A
predicate of kinds needs ∩ where nouns can be predicates. A mass noun, and a noun of a language
without number, is given `Number.general`, which no article of the fragments selects. The
kinds of the model in which the examples are checked are all the concepts that the condition on
kinds allows, so there every plural and mass extension has a kind; the paper's plurals without
one, such as *parts of that machine*, are not among the rows.
`bare_rows` leaves out the Russian singular generic *sobaka obycnoe zyvotnoe*, which the paper
sets with the generic definite singular. The Italian example with a bare plural object is
entered as acceptable, as the paper's text describes it.

Carlson's instance relation is part-of in the model `lawn`, so a kind is an instance of itself.
The generic operator is the conditional over the normal cases of a `Genericity.Normality`.

## References

* [chierchia-1998]
* [carlson-1977]
-/

@[expose] public section

namespace Chierchia1998

open Genericity
open Examples (Example)

/-- The sample covers six of the languages the paper discusses. -/
inductive Language where
  | mandarin | japanese | french | italian | english | russian
  deriving DecidableEq, Fintype

namespace Language

/-- `nominalMapping l` is the setting of the Nominal Mapping Parameter in `l`. -/
def nominalMapping : Language → NominalMapping
  | mandarin | japanese => .argOnly
  | french | italian => .predOnly
  | english | russian => .argAndPred

/-- `determiners l` is the determiner inventory of the fragment of `l`. -/
def determiners : Language → Determiner.Inventory
  | mandarin => Mandarin.Determiners.inventory
  | japanese => Japanese.Determiners.inventory
  | french => French.Determiners.inventory
  | italian => Italian.Determiners.inventory
  | english => English.Determiners.inventory
  | russian => Russian.Determiners.inventory

/-- The type of the classifiers of the fragment of `l`, empty for a language without
classifiers. -/
abbrev ClassifierType : Language → Type
  | mandarin | japanese => Classifier
  | french | italian | english | russian => Empty

/-- `nouns l` is the list of common nouns of the fragment of `l`. -/
def nouns : (l : Language) → List (ClassifiedNoun l.ClassifierType)
  | mandarin => Mandarin.Nouns.nouns.map (·.toClassifiedNoun)
  | japanese => Japanese.Nouns.nouns.map (·.toClassifiedNoun)
  | french => French.Nouns.nouns.map (·.toClassifiedNoun)
  | italian => Italian.Nouns.nouns.map (·.toClassifiedNoun)
  | english => English.Nouns.nouns.map (·.toClassifiedNoun)
  | russian => Russian.Nouns.nouns.map (·.toClassifiedNoun)

/-- The Glottocode of each sampled language. -/
def glottocode : Language → Glottocode
  | mandarin => .mandarinChinese
  | japanese => .japanese
  | french => .french
  | italian => .italian
  | english => .english
  | russian => .russian

/-- The language has classifiers: some common noun of its fragment is counted through one. -/
def HasClassifiers (l : Language) : Prop := ∃ n ∈ l.nouns, n.classifiers.Nonempty

/-- Italian has a phonologically null determiner, and the other sampled languages none. -/
def HasNullD (l : Language) : Prop := l = italian

instance : DecidablePred HasNullD := fun _ ↦ inferInstanceAs (Decidable (_ = _))

end Language

open Chierchia1998.Language

/-- The languages of the sample with classifiers are exactly the [+arg, −pred] ones. -/
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

/-! ### Plurals and mass nouns

A singular count noun is true of atoms and its plural of the pluralities of those atoms. A mass
noun is true of atoms and pluralities alike, so it has no plural, and ∪ of a kind is such an
extension. -/

section Plural

open Mereology

variable {E : Type*} [PartialOrder E] {t : Set E} {x : E}

/-- (10a): the plural of a set of atoms holds of the individuals outside the set whose atoms
are all in it. -/
def PL (t : Set E) : Set E := {x | x ∉ t ∧ ∀ y ≤ x, IsMin y → y ∈ t}

theorem mem_PL : x ∈ PL t ↔ x ∉ t ∧ ∀ y ≤ x, IsMin y → y ∈ t := Iff.rfl

-- The plural of the atoms is everything else.
theorem mem_PL_isMin : x ∈ PL {y : E | IsMin y} ↔ ¬ IsMin x :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ _ hy ↦ hy⟩⟩

-- p. 347: the plural of a set is empty when the set holds whatever has its atoms in it.
theorem PL_eq_empty_iff : PL t = ∅ ↔ ∀ x, (∀ y ≤ x, IsMin y → y ∈ t) → x ∈ t :=
  Set.eq_empty_iff_forall_notMem.trans <| forall_congr' fun _ ↦ by
    simp only [mem_PL, not_and', not_not]

/-- The extension ∪ gives a kind has no plural in an atomic domain, so a language whose nouns
denote kinds has no plural marking. -/
theorem PL_up (hatom : ∀ x : E, ∃ y ≤ x, IsMin y)
    (hsum : ∀ x d : E, (∀ y ≤ x, IsMin y → y ≤ d) → x ≤ d) (k : Part E) :
    PL (Kind.up k) = ∅ := by
  refine PL_eq_empty_iff.2 fun x hx ↦ ?_
  obtain ⟨y, hyx, hy⟩ := hatom x
  obtain ⟨d, hd, -⟩ := hx y hyx hy
  exact ⟨d, hd, hsum x d fun z hz hzm ↦
    let ⟨_, hd', h⟩ := hx z hz hzm
    Part.mem_unique hd' hd ▸ h⟩

theorem PL_up_individual {α : Type*} (k : Part (Individual α)) : PL (Kind.up k) = ∅ :=
  PL_up
    (fun x ↦ let ⟨a, ha⟩ := x.2
      ⟨.atom a, Set.singleton_subset_iff.2 ha, Individual.isMin_atom a⟩)
    (fun _ _ h a ha ↦ Set.singleton_subset_iff.1 <|
      h (.atom a) (Set.singleton_subset_iff.2 ha) (Individual.isMin_atom a)) k

-- (17c), with AT_P the atoms beneath the pluralities.
theorem up_down_PL (ht : ∀ x ∈ t, IsMin x) (hdef : (PL t).Nonempty → (Kind.down (PL t)).Dom) :
    Kind.up (Kind.down (PL t)) = PL t ∪ {a | IsMin a ∧ ∃ x ∈ PL t, a ≤ x} :=
  Kind.up_down_of_forall_isMin ht (fun _ ↦ Iff.rfl) hdef

end Plural

/-! ### Kind formation

∩ takes a property to the individual concept that picks out the largest member of its extension
at each situation, where that concept is a kind, (16), and is undefined otherwise; ∪ takes a kind
to the parts of its value, (15). These are `Kind.down` and `Kind.up`. A kind cannot have a singular
instance in every situation where it has one (p. 351), so ∩ is undefined for a singular property,
which is true of atoms only (`Kind.down_comp_notMem_of_isMin`). -/

section KindFormation

open Mereology

/-- Were kinds to exclude only concepts instantiated by one individual in every situation, a
singular property with no instance in some situation could have a kind. -/
example :
    ∃ (P : Bool → Set Unit) (K : Set (Bool → Part Unit)),
      (∀ k ∈ K, ¬ ∀ s, ∃ d, d ∈ k s ∧ IsMin d) ∧ (∀ s, ∀ x ∈ P s, IsMin x) ∧
        Kind.down ∘ P ∈ K := by
  refine ⟨fun s ↦ if s then {()} else ∅, {fun s ↦ Kind.down (if s then {()} else ∅)}, ?_,
    fun _ _ _ _ _ ↦ le_rfl, Set.mem_singleton _⟩
  rintro k rfl h
  obtain ⟨d, hd, -⟩ := h false
  simp [Kind.down, iota_isGreatest_empty] at hd

/-- Read with AT_P the singular property itself, (17c) fails at a situation with exactly one
instance: in Link's model over two atoms, the plural of a property true of one atom alone has no
member, so ∩ has no value there and ∪∩ yields nothing, while the plural and its singular together
hold of the atom. -/
example : Kind.up (Kind.down (PL {Individual.atom true})) ≠
    PL {Individual.atom true} ∪ {.atom true} := by
  generalize hPdef : PL {Individual.atom true} = P
  have hP : ∀ x, x ∈ P ↔ x ≠ .atom true ∧ ∀ y ≤ x, IsMin y → y = .atom true :=
    fun _ ↦ hPdef ▸ Iff.rfl
  have hf : IsMin (Individual.atom false) := Individual.isMin_atom false
  have h0 : ∀ x, x ∉ P := fun x hx ↦ by
    obtain ⟨hne, hat⟩ := (hP x).1 hx
    by_cases hx0 : false ∈ x.1
    · exact absurd (hat (.atom false) (Set.singleton_subset_iff.2 hx0) hf)
        (by simp [Individual.atom])
    · have htrue : true ∈ x.1 := by
        obtain ⟨b, hb⟩ := x.2
        cases b
        exacts [absurd hb hx0, hb]
      refine hne (Subtype.ext (Set.ext fun a ↦ ?_))
      cases a <;> simp [Individual.atom, hx0, htrue]
  intro h
  have ht : Individual.atom true ∈ Kind.up (Kind.down P) := by
    rw [h]
    exact Or.inr rfl
  rw [Kind.up_of_not_dom fun hd ↦ (Kind.down_dom.1 hd).elim fun d hd ↦ h0 d hd.1] at ht
  exact ht

end KindFormation

/-! ### Carlson's realization relation

[carlson-1977] predicates a state of a kind as an existential over the stages that realize it,
and takes every stage of a kind to be a stage of one of its instances. When Carlson's instances of
a kind are the parts of its value, the instances of the concept, that existential is derived kind
predication (31c), and the inheritance of states from a kind to any kind containing its instances,
Carlson's (119), is the monotonicity of the existential in its restrictor. -/

section Carlson

open scoped SetRel

/-- Carlson's state predication on a kind is derived kind predication (31c) over its instances,
once his instances of the kind are the instances of its concept. -/
theorem carlson_mem_image_iff {S E Stage Place Time : Type*} [Preorder E]
    {M : Carlson1977.Model Stage E Place Time} {inst : SetRel E E} {k : E} {κ : S → Part E}
    {s : S} (hinst : ∀ x, x ~[inst] k ↔ x ∈ Kind.up (κ s)) (hk : M.RealizedByInstances inst k)
    (P : Set Stage) : k ∈ M.R.image P ↔ Quantifier.Det.some (Kind.up (κ s)) (M.R.image P) :=
  Set.ext (a := {x | x ~[inst] k}) hinst ▸ Carlson1977.Model.mem_image_iff hk P

/-- Two dogs, `0` and `1`, and a cat, `2`, each with one stage at its own place; an individual is
a set of animals, and a stage realizes each individual containing its animal. -/
def lawn : Carlson1977.Model (Fin 3) (Finset (Fin 3)) (Fin 3) Unit where
  R := {p | {p.1} ≤ p.2}
  place := id
  time := fun _ ↦ ()

theorem lawn_realizedByInstances (k : Finset (Fin 3)) :
    lawn.RealizedByInstances {p | p.1 ≤ p.2} k :=
  Carlson1977.Model.realizedByInstances_iff.2 fun t ↦
    ⟨fun ht ↦ ⟨{t}, show ({t} : Finset (Fin 3)) ≤ {t} from le_rfl, ht⟩,
      fun ⟨x, htx, hxk⟩ ↦ (show ({t} : Finset (Fin 3)) ≤ x from htx).trans hxk⟩

-- *Dogs are sitting on my lawn* gives *Mammals are sitting on my lawn*, Carlson's (119): a state
-- passes from a kind to any kind whose instances include its own.
theorem carlson_119 {S E Stage Place Time : Type*} [Preorder E]
    {M : Carlson1977.Model Stage E Place Time} {inst : SetRel E E} {k k' : E}
    {κ κ' : S → Part E} {s : S} (hinst : ∀ x, x ~[inst] k ↔ x ∈ Kind.up (κ s))
    (hinst' : ∀ x, x ~[inst] k' ↔ x ∈ Kind.up (κ' s)) (hk : M.RealizedByInstances inst k)
    (hk' : M.RealizedByInstances inst k') (hsub : Kind.up (κ s) ⊆ Kind.up (κ' s))
    {P : Set Stage} (hP : k ∈ M.R.image P) : k' ∈ M.R.image P :=
  (carlson_mem_image_iff hinst' hk' P).2 <|
    ((carlson_mem_image_iff hinst hk P).1 hP).mono (Set.inter_subset_inter_left _ hsub)

/-- On `lawn`, with the part-of relation as the instance relation, the dogs and the mammals meet
the conditions of (119). -/
example (P : Set (Fin 3)) (h : ({0, 1} : Finset (Fin 3)) ∈ lawn.R.image P) :
    (Finset.univ : Finset (Fin 3)) ∈ lawn.R.image P :=
  carlson_119 (M := lawn) (inst := {p | p.1 ≤ p.2}) (k := ({0, 1} : Finset (Fin 3)))
    (k' := Finset.univ) (κ := fun _ : Unit ↦ Part.some ({0, 1} : Finset (Fin 3)))
    (κ' := fun _ ↦ Part.some Finset.univ) (s := ())
    (fun _ ↦ by simp) (fun _ ↦ by simp)
    (lawn_realizedByInstances _) (lawn_realizedByInstances _) (fun x _ ↦ by simp) h

/-- States do not pass the other way: with the cat on the lawn, *Mammals are sitting on my lawn*
is true and *Dogs are sitting on my lawn* false. -/
example : (Finset.univ : Finset (Fin 3)) ∈ lawn.R.image {2} ∧
    ({0, 1} : Finset (Fin 3)) ∉ lawn.R.image {2} := by
  refine ⟨⟨2, rfl, Finset.subset_univ _⟩, ?_⟩
  rintro ⟨t, rfl, ht⟩
  have ht' : ({2} : Finset (Fin 3)) ⊆ {0, 1} := ht
  exact absurd (ht' (Finset.mem_singleton_self 2)) (by decide)

end Carlson

/-! ### Bare arguments and type-shift blocking

The determiner inventory of each sampled language decides by the Blocking Principle which
covert shifts it blocks, and with the mapping which bare nominals it admits as arguments
(`NominalMapping.LicensesBare`), given whether ∩ is defined for the nominal. -/

-- A [+arg, −pred] language of the sample has no articles and so blocks neither ι nor ∃.
theorem argOnly_blocks_nothing :
    ∀ l : Language, l.nominalMapping = .argOnly →
      ¬ l.determiners.Lexicalizes .iota ∧ ¬ l.determiners.Lexicalizes .exists := by
  decide

theorem argOnly_licensesBare (num : Number) (down : Prop) :
    (nominalMapping .mandarin).LicensesBare (determiners .mandarin) num down ∧
      (nominalMapping .japanese).LicensesBare (determiners .japanese) num down := by
  simp [NominalMapping.LicensesBare, nominalMapping]

-- The [−arg, +pred] languages of the sample have a definite article and so block ι.
theorem predOnly_blocks_iota :
    ∀ l : Language, l.nominalMapping = .predOnly → l.determiners.Lexicalizes .iota := by
  decide

theorem predOnly_not_licensesBare (num : Number) (down : Prop) :
    ¬ (nominalMapping .french).LicensesBare (determiners .french) num down ∧
      ¬ (nominalMapping .italian).LicensesBare (determiners .italian) num down := by
  simp [NominalMapping.LicensesBare, nominalMapping]

-- English, [+arg, +pred] with *the* blocking ι and *a* blocking ∃ for singulars, admits a bare
-- singular exactly where kind formation is defined for it.
theorem english_licensesBare_singular_iff (down : Prop) :
    (nominalMapping .english).LicensesBare (determiners .english) .singular down ↔ down :=
  NominalMapping.argAndPred_licensesBare_iff (by decide) (by decide)

-- English admits every bare plural and mass noun, by ∃ where kind formation is undefined, since
-- *a* selects the singular.
theorem english_licensesBare_of_ne_singular {num : Number} (hnum : num ≠ .singular)
    (down : Prop) : (nominalMapping .english).LicensesBare (determiners .english) num down := by
  have key : ∀ n : Number, n ≠ .singular → ¬ (determiners .english).Blocks n .exists := by
    decide
  exact ⟨by decide, .inr (.inr (.inr (key num hnum)))⟩

open Mereology in
-- (24b): English admits no bare singular count noun, since ∩ is undefined for it.
theorem english_not_licensesBare_singular {S E : Type*} [PartialOrder E]
    {K : Set (S → Part E)} {P : S → Set E} (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, IsMin d)
    (hP : ∀ s, ∀ x ∈ P s, IsMin x) :
    ¬ (nominalMapping .english).LicensesBare (determiners .english) .singular (Kind.down ∘ P ∈ K) :=
  (english_licensesBare_singular_iff _).not.2 (Kind.down_comp_notMem_of_isMin hK hP)

/-! ### The paper's examples

A bare nominal is an argument where the mapping and the determiners license it, or under a null
determiner that a governing head licenses, where a shift is chosen as in a language whose nouns
are of either type. A predicate of kinds needs the nominal to have a kind. -/

-- p. 361: a [+arg, +pred] language without articles admits every bare nominal.
theorem russian_licensesBare (num : Number) (down : Prop) :
    (nominalMapping .russian).LicensesBare (determiners .russian) num down :=
  ⟨by decide, .inr (.inr (.inl fun h ↦ absurd h.lexicalizes (by decide)))⟩

/-- `l.AdmitsBare num down governed kindLevel` holds when `l` admits as an argument a bare
nominal of number `num`, for which ∩ is defined just when `down` holds, in a governed position
or not, with a predicate of kinds or of objects. -/
def Language.AdmitsBare (l : Language) (num : Number) (down governed kindLevel : Prop) : Prop :=
  (l.nominalMapping.LicensesBare l.determiners num down ∨
    l.HasNullD ∧ governed ∧ NominalMapping.argAndPred.LicensesBare l.determiners num down) ∧
  (kindLevel → .property ∈ l.nominalMapping → down)

instance (l : Language) (num : Number) (down governed kindLevel : Prop) [Decidable down]
    [Decidable governed] [Decidable kindLevel] :
    Decidable (l.AdmitsBare num down governed kindLevel) := by
  unfold Language.AdmitsBare; infer_instance

/-- The number of a bare nominal, a mass noun or a noun without number being general. -/
def Examples.Bare.number : Examples.Bare → Number
  | .singular => .singular
  | .plural => .plural
  | .mass => .general

section Model

open Mereology

/-- The individuals of the model: two atoms and their sum. -/
abbrev Ind := {s : Finset Bool // s.Nonempty}

/-- The extension of a bare nominal at the one situation of the model: a singular count noun is
true of the atoms, its plural is `PL` of them, and a mass noun is true of every individual. -/
def Examples.Bare.extension : Examples.Bare → Unit → Set Ind
  | .singular, _ => {x | IsMin x}
  | .plural, _ => PL {x | IsMin x}
  | .mass, _ => Set.univ

/-- The kinds of the model are the concepts not singular wherever they have a value. -/
def kinds : Set (Unit → Part Ind) := {k | ¬ ∀ s, ∀ d ∈ k s, IsMin d}

-- ∩ is defined for the plural and the mass extension, and not for the singular one.
theorem down_extension_mem_kinds_iff (b : Examples.Bare) :
    Kind.down ∘ b.extension ∈ kinds ↔ b ≠ .singular := by
  cases b
  · exact iff_of_false (Kind.down_comp_notMem_of_isMin (fun _ h ↦ h) fun _ _ h ↦ h) (by simp)
  · have h : ∃ d : Ind, IsGreatest (PL {y : Ind | IsMin y}) d ∧ ¬ IsMin d := by
      simp only [IsGreatest, upperBounds, Set.mem_ofPred_eq, mem_PL_isMin]; decide
    obtain ⟨d, hd, hmin⟩ := h
    exact iff_of_true (fun h ↦ hmin (h () d (Kind.mem_down.2 hd))) (by decide)
  · have h : ∃ d : Ind, IsGreatest (Set.univ : Set Ind) d ∧ ¬ IsMin d := by
      simp only [IsGreatest, upperBounds, Set.mem_ofPred_eq, Set.mem_univ, true_and,
        forall_const]; decide
    obtain ⟨d, hd, hmin⟩ := h
    exact iff_of_true (fun h ↦ hmin (h () d (Kind.mem_down.2 hd))) (by decide)

instance (b : Examples.Bare) : Decidable (Kind.down ∘ b.extension ∈ kinds) :=
  decidable_of_iff _ (down_extension_mem_kinds_iff b).symm

end Model

/-- The examples with a bare argument are acceptable exactly where the language admits the
nominal, the Russian singular generic (27f) apart. -/
theorem bare_rows : ∀ x : Example, x ≠ .ex27f →
    ∀ b ∈ x.bare, ∀ p ∈ x.position, ∀ k ∈ x.predicate, ∃ l : Language,
      x.datum.language = l.glottocode ∧
        (l.AdmitsBare b.number (Kind.down ∘ b.extension ∈ kinds) (p = .governed) (k = .kind) ↔
          x.datum.judgment = .acceptable) := by
  decide

-- (23): Italian admits a bare plural where a head governs it and not as a subject.
example : Language.italian.AdmitsBare .plural True True False ∧
    ¬ Language.italian.AdmitsBare .plural True False False := by decide

-- An Italian bare singular count noun is out under government too, *un* blocking ∃.
example : ¬ Language.italian.AdmitsBare .singular False True False := by decide

/-! ### Bare plurals in generic and episodic sentences -/

section Generic

open Genericity

variable {S E : Type*} [PartialOrder E]

/-- *Dogs bark* (38b), `Gn x, s [∪∩dog(x) ∧ C(x, s)] [bark(x, s)]`, puts the instances of the
kind in the restriction of the generic operator, which binds them with the situations. -/
def dogsBark (N : S → Normality (E × S)) (dog : S → Set E) (C : Set (E × S))
    (bark : E → S → Prop) : Set S :=
  {s | (N s).gen ({p | p.1 ∈ Kind.up (Kind.down (dog p.2))} ∩ C) {p | bark p.1 p.2}}

/-- In *Computers route modern planes* (39b), the object is fronted into the restriction of the
generic operator and the subject is reconstructed into its scope, where derived kind predication
reads it existentially. -/
def computersRoute (N : S → Normality (E × S)) (computer plane : S → Set E)
    (C : Set (E × S)) (route : E → E → S → Prop) : Set S :=
  {s | (N s).gen ({p | p.1 ∈ Kind.up (Kind.down (plane p.2))} ∩ C)
    {p | Quantifier.Det.some (Kind.up (Kind.down (computer p.2))) {x | route x p.1 p.2}}}

-- In (39b) the fronted bare plural is universal over the normal cases, and the one in scope
-- existential over its kind's instances (p. 368).
theorem mem_computersRoute {N : S → Normality (E × S)} {computer plane : S → Set E}
    {C : Set (E × S)} {route : E → E → S → Prop} {s : S} :
    s ∈ computersRoute N computer plane C route ↔
      ∀ p ∈ (N s).normal ({p | p.1 ∈ Kind.up (Kind.down (plane p.2))} ∩ C),
        ∃ x ∈ Kind.up (Kind.down (computer p.2)), route x p.1 p.2 :=
  Iff.rfl

-- The generic reading of a bare plural (38b) entails its episodic reading by derived kind
-- predication (31c) wherever the kind has a normal instance.
theorem some_up_of_mem_dogsBark {N : S → Normality (E × S)} {dog : S → Set E} {C : Set (E × S)}
    {bark : E → S → Prop} {s s' : S} {x : E} (h : s ∈ dogsBark N dog C bark)
    (hx : (x, s') ∈ (N s).normal ({p | p.1 ∈ Kind.up (Kind.down (dog p.2))} ∩ C)) :
    Quantifier.Det.some (Kind.up (Kind.down (dog s'))) {x | bark x s'} :=
  ⟨x, ((N s).normal_subset _ hx).1, h hx⟩

end Generic

/-! ### Scope

A bare nominal that ∩ shifts is the name of a kind, and one that ∃ shifts is a quantifier. A
predicate of objects applies to a kind by derived kind predication, and an argument raised over
an operator leaves a trace of its own sort, so raising a kind changes nothing, while a
quantifier takes scope. -/

/-- Under Chierchia's ranking an English bare plural is shifted by ∩ where ∩ is defined for it
and by ∃ where it is not, *the* blocking ι and no article blocking ∃ for plurals. -/
theorem english_plural_shift_iff (down : Prop) (τ : CovertShift) :
    MaximalFor ((determiners .english).Available .plural down) (· = .down) τ ↔
      τ = .down ∧ down ∨ τ = .exists ∧ ¬ down := by
  have h1 : (determiners .english).Blocks .plural .iota := by decide
  have h2 : (determiners .english).Blocks .plural .iotaAnaphoric := by decide
  have h3 : ¬ (determiners .english).Blocks .plural .exists := by decide
  cases τ
  case iotaAnaphoric =>
    simp [CovertShift.maximalFor_eq_down_iff, Determiner.Inventory.Available, h2]
  all_goals simp [h1, h3]

section Scope

variable {E : Type*} [Preorder E]

/-- A nominal shifted to an argument is the value of a kind or a generalized quantifier. -/
inductive Argument (E : Type*) where
  | kind (k : Part E)
  | quantifier (𝒬 : Set E → Prop)

namespace Argument

/-- `a.apply V` combines the argument in place with a predicate of objects: a kind by derived
kind predication (31c), a quantifier by applying it. -/
def apply (V : Set E) : Argument E → Prop
  | kind k => Quantifier.Det.some (Kind.up k) V
  | quantifier 𝒬 => 𝒬 V

/-- `a.raise O V` scopes the argument over the operator `O`, abstracting over a trace of the
argument's sort: a kind for a kind (43b), an object for a quantifier. -/
def raise (O : Prop → Prop) (V : Set E) : Argument E → Prop
  | kind k => (fun x : Part E ↦ O ((kind x).apply V)) k
  | quantifier 𝒬 => 𝒬 {x | O (x ∈ V)}

-- (43a-d): raising a kind over an operator gives the reading it has in place.
theorem raise_kind (O : Prop → Prop) (V : Set E) (k : Part E) :
    (kind k).raise O V = O ((kind k).apply V) := rfl

-- (31c): a predicate of objects holds of a kind iff the kind's value is in its upper closure,
-- so it passes to any kind with more instances.
theorem apply_kind_iff (V : Set E) (k : Part E) :
    (kind k).apply V ↔ ∃ d ∈ k, d ∈ upperClosure V :=
  Kind.inter_up_nonempty_iff

-- (48): the argument ∃ makes of a property.
theorem raise_quantifier_some (O : Prop → Prop) (V P : Set E) :
    (quantifier (Quantifier.Det.some P)).raise O V ↔ ∃ x ∈ P, O (x ∈ V) :=
  Iff.rfl

end Argument

/-- (49d): under negation a nominal shifted by ∃ has a wide reading that its narrow reading
lacks, here with two objects of which one is seen. -/
example : (Argument.quantifier (Quantifier.Det.some (Set.univ : Set Bool))).raise Not {true} ∧
    ¬ ¬ (Argument.quantifier (Quantifier.Det.some (Set.univ : Set Bool))).apply {true} :=
  ⟨⟨false, trivial, by simp⟩, not_not.2 ⟨true, trivial, rfl⟩⟩

/-- (43e): the wide reading is none of a kind's, whose raised reading is false in the same
model though an instance is unseen. -/
example : ¬ (Argument.kind (Part.some true)).raise Not {true} ∧
    Quantifier.Det.some (Kind.up (Part.some true)) {x | x ∉ ({true} : Set Bool)} :=
  ⟨not_not.2 ⟨true, by simp, rfl⟩, ⟨false, by simp, by simp⟩⟩

end Scope

end Chierchia1998
