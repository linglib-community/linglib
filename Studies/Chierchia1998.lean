module

public import Linglib.Semantics.Genericity.NominalMappingParameter
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
public import Studies.Carlson1977

/-!
# Chierchia (1998): Reference to kinds across languages

Chierchia's Nominal Mapping Parameter sets whether a language's nouns denote kinds, predicates, or
either: Chinese and Japanese are [+arg, −pred], the Romance languages [−arg, +pred], and English
[+arg, +pred]. The languages of the sample whose fragments count nouns through classifiers are
[exactly the argument-only ones](##hasClassifiers_iff). A language's determiners decide which
covert type shifts it blocks, [none in an argument-only language](##argOnly_blocks_nothing), and
with the parameter which bare nominals it admits as arguments, in English
[a bare singular only where ∩ is defined for it](##english_licensesBare_singular_iff). ∩
[undoes ∪](##Kind.down_up), ∪ [undoes ∩ on a property closed downward](##Kind.up_down), and ∩ is
[undefined for a singular property](##Kind.down_notMem_of_atom). Carlson's state predication on a
kind [is derived kind predication over its instances](##carlson_mem_image_iff), so a state passes
from a kind to any kind whose instances include its own,
[Carlson's (119)](##carlson_119). A generic bare plural
[entails its episodic reading](##some_up_of_mem_dogsBark).

## Main definitions

* `Chierchia1998.Language.nominalMapping`: the setting of the parameter in each sampled language.
* `Chierchia1998.lawn`: a model of Carlson's stages with two dogs and a cat.
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
property that p. 351 uses, that no kind has a singular instance in every situation, is a hypothesis,
read with that page's "(when defined)": no kind is singular in every situation where it has a
value. The paper restricts kinds further, on p. 350, to concepts that identify classes of objects
with a sufficiently regular function or behavior, which is not formalized. A weaker condition,
that no kind be necessarily instantiated by one individual, would not exclude ∩ of a singular
property with no instance in some situation (the first `example` of the kind-formation section).
∩ and ∪ are `Kind.down` and `Kind.up`, ι and its partial inverse Id applied at each situation
(pp. 359–360), Id sending an individual to its parts, `Set.Iic`. (17b) is stated under its own
hypothesis, that ∩P is defined, read as ∩P having a value wherever P has instances, for a property
closed downward (`Kind.up_down`); over the paper's complete semilattice a property closed under
sum meets it whatever the size of its extension (`Kind.up_down_of_sSup_mem`). In (17c), AT_P,
"the set that generates P under PL", is read as the atoms beneath members of P
(`Kind.up_down_of_forall_atom`): read as the singular property itself, (17c) fails at a situation
with exactly one instance, where the plural has no member. Carlson's instance relation is
part-of in the model `lawn`, so a kind is an instance of itself.

## Errata

* (25e) prints Id(x) = λx[x ≤ y], binding the wrong variable; the text above footnote 14, which
  has ι undone via the part-of relation, and the footnote's Id(x) = λy[y = x] for a singularity
  give Id(x) = λy[y ≤ x].

## References

* [chierchia-1998]
* [carlson-1977]
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
at each situation, where that concept is a kind, (16), and is undefined otherwise; ∪ takes a kind
to the parts of its value, (15). These are `Kind.down` and `Kind.up`. A kind cannot have a singular
instance in every situation where it has one (p. 351), so ∩ is undefined for a singular property,
which is true of atoms only (`Kind.down_notMem_of_atom`). -/

section KindFormation

open Mereology

/-- Were kinds to exclude only concepts instantiated by one individual in every situation, a
singular property with no instance in some situation could have a kind. -/
example :
    ∃ (P : Bool → Set Bool) (K : Set (Bool → Option Bool)),
      (∀ k ∈ K, ¬ ∀ s, ∃ d, k s = some d ∧ Atom d) ∧ (∀ s, ∀ x ∈ P s, Atom x) ∧
        Kind.down P ∈ K := by
  refine ⟨fun s ↦ if s then {true} else ∅, {Kind.down fun s ↦ if s then {true} else ∅}, ?_, ?_,
    Set.mem_singleton _⟩
  · rintro k rfl h
    obtain ⟨d, hd, -⟩ := h false
    simp [Kind.down, iota_isGreatest_empty] at hd
  · rintro (_ | _) x hx
    · exact absurd hx (by simp)
    · obtain rfl : x = true := hx
      show ¬ IsBot true ∧ ∀ ⦃y⦄, ¬ IsBot y → y ≤ true → true ≤ y
      decide

/-- Read with AT_P the singular property itself, (17c) fails at a situation with exactly one
instance: in Link's model over two atoms, the plural of a property true of one atom alone has no
member, so ∩ has no value there and ∪∩ yields nothing, while the plural and its singular together
hold of the atom. -/
example {P : Unit → Set (Individual Bool)}
    (hP : ∀ x, x ∈ P () ↔ x ≠ .atom true ∧ ∀ y ≤ x, Atom y → y = .atom true) :
    Kind.up (Kind.down P) () ≠ P () ∪ {.atom true} := by
  have hf : Atom (Individual.atom false) := by
    refine ⟨fun h ↦ absurd (h (.atom true) (Set.mem_singleton false)) (by simp [Individual.atom]),
      fun y _ hyf ↦ ?_⟩
    obtain ⟨b, hb⟩ := y.2
    obtain rfl : b = false := hyf hb
    intro a ha
    rw [Set.mem_singleton_iff.1 ha]
    exact hb
  have h0 : ∀ x, x ∉ P () := fun x hx ↦ by
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
  have ht : Individual.atom true ∈ Kind.up (Kind.down P) () := by
    rw [h]
    exact Or.inr rfl
  rw [Kind.up_apply_of_eq_none (Kind.down_eq_none_iff.2 fun ⟨d, hd⟩ ↦ h0 d hd.1)] at ht
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
    {M : Carlson1977.Model Stage E Place Time} {inst : SetRel E E} {k : E} {κ : S → Option E}
    {s : S} (hinst : ∀ x, x ~[inst] k ↔ x ∈ Kind.up κ s) (h : M.R ○ inst ⊆ M.R)
    (hk : ∀ ⦃t⦄, t ~[M.R] k → t ~[M.R ○ inst] k) (P : Set Stage) :
    k ∈ M.R.image P ↔ Quantifier.Det.some (Kind.up κ s) (M.R.image P) :=
  (Carlson1977.Model.mem_image_iff h hk P).trans
    ⟨fun ⟨x, hx, hxk⟩ ↦ ⟨x, (hinst x).1 hxk, hx⟩, fun ⟨x, hxu, hx⟩ ↦ ⟨x, hx, (hinst x).2 hxu⟩⟩

/-- Two dogs, `0` and `1`, and a cat, `2`, each with one stage at its own place; an individual is
a set of animals, and a stage realizes each individual containing its animal. -/
def lawn : Carlson1977.Model (Fin 3) (Finset (Fin 3)) (Fin 3) Unit where
  R := {p | {p.1} ≤ p.2}
  place := id
  time := fun _ ↦ ()

theorem lawn_comp_subset : lawn.R ○ {p | p.1 ≤ p.2} ⊆ lawn.R := by
  rintro ⟨t, k⟩ ⟨x, htx, hxk⟩
  exact (show ({t} : Finset (Fin 3)) ≤ x from htx).trans hxk

/-- *Dogs are sitting on my lawn* gives *Mammals are sitting on my lawn* (119): when Carlson's
instances of two kinds are the instances of their concepts, a state passes from a kind to any kind
whose instances include its own, since the instance that derived kind predication finds for the
first is an instance of the second. -/
theorem carlson_119 {S E Stage Place Time : Type*} [Preorder E]
    {M : Carlson1977.Model Stage E Place Time} {inst : SetRel E E} {k k' : E}
    {κ κ' : S → Option E} {s : S} (hinst : ∀ x, x ~[inst] k ↔ x ∈ Kind.up κ s)
    (hinst' : ∀ x, x ~[inst] k' ↔ x ∈ Kind.up κ' s) (h : M.R ○ inst ⊆ M.R)
    (hk : ∀ ⦃t⦄, t ~[M.R] k → t ~[M.R ○ inst] k) (hsub : Kind.up κ s ⊆ Kind.up κ' s)
    {P : Set Stage} (hP : k ∈ M.R.image P) : k' ∈ M.R.image P := by
  obtain ⟨x, hx, t, ht, htx⟩ := (carlson_mem_image_iff hinst h hk P).1 hP
  exact ⟨t, ht, h ⟨x, htx, (hinst' x).2 (hsub hx)⟩⟩

/-- On `lawn`, with the part-of relation as the instance relation, the dogs and the mammals meet
the conditions of (119). -/
example (P : Set (Fin 3)) (h : ({0, 1} : Finset (Fin 3)) ∈ lawn.R.image P) :
    (Finset.univ : Finset (Fin 3)) ∈ lawn.R.image P :=
  carlson_119 (M := lawn) (inst := {p | p.1 ≤ p.2}) (k := ({0, 1} : Finset (Fin 3)))
    (k' := Finset.univ) (κ := fun _ : Unit ↦ some ({0, 1} : Finset (Fin 3)))
    (κ' := fun _ ↦ some Finset.univ) (s := ()) (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    lawn_comp_subset (fun _ ht ↦ ⟨_, ht, by simp⟩) (fun x _ ↦ Finset.subset_univ x) h

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
    ¬ (nominalMapping .english).LicensesBare (determiners .english) .singular (Kind.down P ∈ K) :=
  (english_licensesBare_singular_iff _).not.2 (Kind.down_notMem_of_atom hK hP)

/-! ### Bare plurals in generic and episodic sentences, §4.1 -/

section Generic

open Genericity

variable {S E : Type*} [PartialOrder E]

/-- *Dogs bark* (38b), `Gn x, s [∪∩dog(x) ∧ C(x, s)] [bark(x, s)]`, puts the instances of the
kind in the restriction of the generic operator, which binds them with the situations. -/
def dogsBark (N : Normality S (E × S)) (dog : S → Set E) (C : Set (E × S))
    (bark : E → S → Prop) : Set S :=
  N.gen ({p | p.1 ∈ Kind.up (Kind.down dog) p.2} ∩ C) {p | bark p.1 p.2}

/-- In *Computers route modern planes* (39b), the object is fronted into the restriction of the
generic operator and the subject is reconstructed into its scope, where derived kind predication
reads it existentially. -/
def computersRoute (N : Normality S (E × S)) (computer plane : S → Set E) (C : Set (E × S))
    (route : E → E → S → Prop) : Set S :=
  N.gen ({p | p.1 ∈ Kind.up (Kind.down plane) p.2} ∩ C)
    {p | Quantifier.Det.some (Kind.up (Kind.down computer) p.2)
      (route · p.1 p.2)}

/-- In (39b) the fronted bare plural is universal over the normal cases, and the one in scope
existential over its kind's instances (p. 368). -/
theorem mem_computersRoute {N : Normality S (E × S)} {computer plane : S → Set E}
    {C : Set (E × S)} {route : E → E → S → Prop} {s : S} :
    s ∈ computersRoute N computer plane C route ↔
      ∀ p ∈ N.normal s ({p | p.1 ∈ Kind.up (Kind.down plane) p.2} ∩ C),
        ∃ x ∈ Kind.up (Kind.down computer) p.2, route x p.1 p.2 :=
  Iff.rfl

/-- The generic reading of a bare plural (38b) entails its episodic reading by derived kind
predication (31c) wherever the kind has a normal instance. -/
theorem some_up_of_mem_dogsBark {N : Normality S (E × S)} {dog : S → Set E} {C : Set (E × S)}
    {bark : E → S → Prop} {s s' : S} {x : E} (h : s ∈ dogsBark N dog C bark)
    (hx : (x, s') ∈ N.normal s ({p | p.1 ∈ Kind.up (Kind.down dog) p.2} ∩ C)) :
    Quantifier.Det.some (Kind.up (Kind.down dog) s') (bark · s') :=
  ⟨x, (N.normal_subset s _ hx).1, h hx⟩

end Generic

end Chierchia1998
