module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Lattice.Fold
public import Linglib.Syntax.Feature.Person.Decomposition
public import Linglib.Syntax.Feature.Person.Partition
public import Linglib.Syntax.Feature.Person.Specification
public import Linglib.Semantics.Plurality.NumberFeatures
public import Studies.Harbour2014
public import Studies.Cysouw2003
public import Linglib.Semantics.Plurality.FeatureAction
public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Languages.Tamil.Pronouns
public import Linglib.Languages.English.Determiners
public import Linglib.Semantics.Reference.Determiner

/-!
# Harbour (2016): Impossible Persons

Harbour derives the person categories as the cells of a partition of the lattice of referents,
induced by two features, [±author] and [±participant], whose values act on lattices: the plus value
adds its lattice pairwise and the minus value subtracts its maximum. A language sets whether each
feature is present and, when both are, which composes first; composing [±author] outermost [yields
the quadripartition](##Examples.quad_cells_eq_participantSets) and [±participant] outermost [the
tripartition](##Examples.tri_card). These parameters [generate exactly five
partitions](##ofFeatures_mem_image_iff), those of the bivalent geometry he sets aside, while the
three-feature theories he rejects generate [every system in which a coordination's person is the
join of its conjuncts'](##Person.exists_bundle_eq_iff), seven in all, the hearer bipartition and
Zwicky's tripartition among them.
Without number the quadripartition is [Cysouw's only-inclusive pattern](##pattern_quad), and its
signs keep [the exclusive apart from the inclusive](##tamil_clusivity_distinguished).

## Implementation notes

One other suffices for the person partition, whose four cells are fixed by the presence of the
speaker and the hearer, so the ontology is `Fin 3` and the third-person group is not modeled;
every result is checked on this finite model. Lexical Complementarity applies once, after both
features, not cyclically (appendix B.1.2.3). The actions of the features (`act`) and Lexical
Complementarity (`lexComp`) come from `Semantics/Plurality/FeatureAction.lean`. The subsidiary
parameter of the tripartition, which value of [±author] represents the third person, changes no
partition and is not modeled. A setting's partition is compared with the three-feature systems on
participant sets, two participant sets being related when a cell holds a referent with each; every
cell is a union of the classes of referents with the same participants.

## References

* [harbour-2016]
* [harbour-2014]
* [cysouw-2003]
-/

@[expose] public section

namespace Harbour2016

open Finset
open Plurality.FeatureAction

/-! ### The partition construction (over `Plurality.FeatureAction`'s operators) -/

section Construction
variable {Ω : Type*} [DecidableEq Ω]

/-- Refining a cell `c` against its siblings applies Lexical Complementarity (31) and then
discards the empty set, which no person denotes (§4.4). -/
def refine (siblings : List (Finset (Finset Ω))) (c : Finset (Finset Ω)) :
    Finset (Finset Ω) :=
  (lexComp siblings.toFinset c).erase ∅

/-- The cells of a partition are the raw denotations of its sign assignments, each refined
against the whole family. -/
def cellsOf (raws : List (Finset (Finset Ω))) : Finset (Finset (Finset Ω)) :=
  (raws.map (refine raws)).toFinset

end Construction

/-- (29): a setting of the parameters of π, which features are present and, when both are, which
composes with π first. -/
structure Setting where
  /-- (29a): the author feature is present. -/
  author : Bool
  /-- (29b): the participant feature is present. -/
  participant : Bool
  /-- (29c): the author feature composes with π first, idle unless both features are present. -/
  authorFirst : Bool
  deriving DecidableEq, Fintype

section Construction
variable {Ω : Type*} [DecidableEq Ω]

/-- The raw cells of a setting over the author, participant and π lattices: the π lattice acted
on by each sign assignment of the features present, the feature that composes first acting
first. -/
def Setting.raws (σ : Setting) (au pt π : Finset (Finset Ω)) : List (Finset (Finset Ω)) :=
  match σ.author, σ.participant with
  | false, false => [π]
  | true, false => [true, false].map fun s ↦ act s au π
  | false, true => [true, false].map fun s ↦ act s pt π
  | true, true => [true, false].flatMap fun s ↦ [true, false].map fun t ↦
    if σ.authorFirst then act s pt (act t au π) else act s au (act t pt π)

/-- The partition a setting yields: its raw cells, each refined against the others. -/
def Setting.cells (σ : Setting) (au pt π : Finset (Finset Ω)) : Finset (Finset (Finset Ω)) :=
  cellsOf (σ.raws au pt π)

end Construction

/-! ### The three-element ontology `{i, u, o}` and the derived results

Harbour's abbreviation `i_o`/`iu_o`/`u_o`/`o_o` collapses the π-lattice into four
shape-classes; the minimal ontology realizing all four is `{i, u, o}`, taken here
as `Fin 3` with `i = 0`, `u = 1`, `o = 2`. A single `o` suffices for the *person*
partition (the four cells are fixed by `has i?`/`has u?`, not the others' count); the
3rd-person *group* `{o, o'}` is not modelled, and no result below depends on it. All
theorems are kernel-checked by `decide` on this finite model. -/

namespace Examples

abbrev Ω := Fin 3      -- 0 = speaker i, 1 = hearer u, 2 = other o

/-- The author lattice `ℒau` is the lattice of groups of the speaker. -/
def ℒau : Finset (Finset Ω) := Ioc ∅ {0}
/-- The participant lattice `ℒpt` is the lattice of groups of the speaker and the hearer. -/
def ℒpt : Finset (Finset Ω) := Ioc ∅ {0, 1}
/-- The π lattice has every nonempty set of referents as a group. -/
def ℒπ  : Finset (Finset Ω) := Ioc ∅ univ

-- p. 74
theorem lattice_chain : ℒau ⊆ ℒpt ∧ ℒpt ⊆ ℒπ :=
  ⟨Ioc_subset_Ioc_right (by decide), Ioc_subset_Ioc_right (subset_univ _)⟩

/-! #### Quadripartition — author composes outermost ([harbour-2016] §4.3.5) -/

/-- The raw quadripartition cell for the author sign `sa` and the participant sign `sp` applies
the participant value first and the author value outermost. -/
def quadRaw (sa sp : Bool) : Finset (Finset Ω) := act sa ℒau (act sp ℒpt ℒπ)

-- (65): before Lexical Complementarity, `+author +participant` holds the groups containing `i`
theorem quadRaw_true_true : quadRaw true true = containing {0} univ := by
  rw [quadRaw, act_true, act_true, ℒau, ℒpt, ℒπ, Ioc_sups_Ioc (subset_univ _),
    Ioc_sups_containing_of_subset (by decide) (subset_univ _)]

/-- The raw quadripartition cells are those of the setting with both features, the participant
feature composing first. -/
def quadRaws : List (Finset (Finset Ω)) := Setting.raws ⟨true, true, false⟩ ℒau ℒpt ℒπ

example :
    quadRaws = [quadRaw true true, quadRaw true false, quadRaw false true, quadRaw false false] :=
  rfl

/-- A quadripartition cell is a raw cell refined against the others. -/
def quadCell (sa sp : Bool) : Finset (Finset Ω) := refine quadRaws (quadRaw sa sp)

/-- The first person inclusive is the `+author +participant` cell. -/
def inclusive : Finset (Finset Ω) := quadCell true true
/-- The first person exclusive is the `+author −participant` cell. -/
def exclusive : Finset (Finset Ω) := quadCell true false
/-- The second person is the `−author +participant` cell. -/
def secondP : Finset (Finset Ω) := quadCell false true
/-- The third person is the `−author −participant` cell. -/
def thirdP : Finset (Finset Ω) := quadCell false false

/-! The inclusive and the exclusive come out as distinct, disjoint cells by construction. -/

theorem exclusive_excludes_addressee : ∀ s ∈ exclusive, (1 : Ω) ∉ s := by decide

theorem exclusive_includes_speaker : ∀ s ∈ exclusive, (0 : Ω) ∈ s := by decide

theorem inclusive_has_both : ∀ s ∈ inclusive, (0 : Ω) ∈ s ∧ (1 : Ω) ∈ s := by decide

theorem inclusive_ne_exclusive : inclusive ≠ exclusive := by decide

theorem quad_covers : inclusive ∪ exclusive ∪ secondP ∪ thirdP = ℒπ := by decide

theorem quad_disjoint :
    Disjoint inclusive exclusive ∧ Disjoint inclusive secondP ∧
    Disjoint inclusive thirdP ∧ Disjoint exclusive secondP ∧
    Disjoint exclusive thirdP ∧ Disjoint secondP thirdP := by decide

theorem quad_card : (cellsOf quadRaws).card = 4 := by decide

/-- The participants of a referent are the speaker if it contains `0` and the addressee if it
contains `1`. -/
def participants (s : Finset Ω) : Finset SpeechAct.Role :=
  {r | (match r with | .speaker => 0 | .addressee => 1 : Ω) ∈ s}

/-- The calculus generates the library's quadripartition, each of the four cells holding exactly
the referents whose participants the corresponding person value covers. -/
theorem quad_cells_eq_participantSets :
    ∀ s ∈ ℒπ,
      (s ∈ inclusive ↔ participants s ∈ Person.Specification.firstInclusive.sets) ∧
      (s ∈ exclusive ↔ participants s ∈ Person.Specification.firstExclusive.sets) ∧
      (s ∈ secondP ↔ participants s ∈ Person.second.participantSets) ∧
      (s ∈ thirdP ↔ participants s ∈ Person.third.participantSets) := by
  decide

/-! #### Standard tripartition — participant composes outermost ([harbour-2016] §4.3.4) -/

/-- The raw tripartition cell for the participant sign `sp` and the author sign `sa` applies the
author value first and the participant value outermost. -/
def triRaw (sp sa : Bool) : Finset (Finset Ω) := act sp ℒpt (act sa ℒau ℒπ)

/-- The raw tripartition cells are those of the setting with both features, the author feature
composing first. -/
def triRaws : List (Finset (Finset Ω)) := Setting.raws ⟨true, true, true⟩ ℒau ℒpt ℒπ

example :
    triRaws = [triRaw true true, triRaw true false, triRaw false true, triRaw false false] :=
  rfl

/-- With participant outermost the two `−participant` specifications coincide, so the
tripartition has three cells where the quadripartition has four, the noncommutativity of
feature composition (§4.2.3). -/
theorem tri_card : (cellsOf triRaws).card = 3 := by decide

theorem tri_ne_quad : cellsOf triRaws ≠ cellsOf quadRaws := by decide

/-! #### Every setting partitions the π lattice by participants -/

-- §4.3: each setting's cells partition the π lattice
theorem cells_partition (σ : Setting) :
    (σ.cells ℒau ℒpt ℒπ).sup id = ℒπ ∧ ∅ ∉ σ.cells ℒau ℒpt ℒπ ∧
      ∀ c ∈ σ.cells ℒau ℒpt ℒπ, ∀ d ∈ σ.cells ℒau ℒpt ℒπ, c ≠ d → Disjoint c d := by
  revert σ; decide +kernel

-- a cell holds a referent iff it holds every referent with its participants
theorem mem_cells_iff_of_participants_eq (σ : Setting) :
    ∀ c ∈ σ.cells ℒau ℒpt ℒπ, ∀ s ∈ ℒπ, ∀ t ∈ ℒπ, participants s = participants t →
      (s ∈ c ↔ t ∈ c) := by
  revert σ; decide +kernel

/-! #### No four-way singular person ([harbour-2016] Ch. 4) -/

/-- The singleton referents are `{i}`, `{u}` and `{o}`. -/
def singletons : Finset (Finset Ω) := {{0}, {1}, {2}}

theorem inclusive_has_no_singleton : inclusive ∩ singletons = ∅ := by decide

theorem inclusive_card_ge_two : ∀ s ∈ inclusive, 2 ≤ s.card := by decide

end Examples

/-! ### Three-feature theories (§8.2)

Theories with [±participant], [±author] and [±hearer] let a language activate any subset of the
three, and the active features identify the participant sets that agree on them. A set bears
[+participant] when it includes a participant, [+author] when it includes the speaker, and [+hearer]
when it includes the addressee (p. 10). Each feature is preserved by union, so in each system they
generate the person of a coordination is the join of its conjuncts' persons; conversely, the
participant sets lacking a feature are those below a single set, and every such system is generated
by the features it respects (`Person.exists_bundle_eq_iff`). The systems number seven
(`Person.Partition.card_image_ofFeatures`): the five of Table 4.1 and the two
Harbour names as these theories' overgeneration, the hearer bipartition and the tripartition Zwicky
problematized, which groups inclusive with second person (p. 190). The bivalent geometry (9), which
bars [±hearer] without [±author], generates exactly the five (p. 193); Harbour rejects it as one of
sixteen geometries with nothing to select it (p. 194). -/

open SpeechAct

open Person (Feature Features Bears bundle bundle_eq_bundle_iff Partition)

theorem bundle_hearer_eq_iff {s t : Finset Role} :
    bundle {.addressee} s = bundle {.addressee} t ↔ (.addressee ∈ s ↔ .addressee ∈ t) := by
  revert s t; decide

theorem bundle_hearer_participant_eq_iff {s t : Finset Role} :
    bundle {.addressee, .participant} s = bundle {.addressee, .participant} t ↔
      (s.Nonempty ↔ t.Nonempty) ∧ (.addressee ∈ s ↔ .addressee ∈ t) := by
  revert s t; decide

/-- Geometry (9) admits [±hearer] only with [±author]. -/
def Admissible (F : Features) : Prop := .addressee ∈ F → .speaker ∈ F

instance : DecidablePred Admissible := fun _ ↦ by unfold Admissible; infer_instance

theorem card_image_ofFeatures_admissible :
    ((univ.filter Admissible).image Partition.ofFeatures).card = 5 := by
  decide

theorem ofFeatures_not_admissible :
    ∀ F, ¬ Admissible F → Partition.ofFeatures F = .ofFeatures {.addressee} ∨
      Partition.ofFeatures F = .ofFeatures {.addressee, .participant} := by
  decide

/-! ### The parameter space and its yield

Read on participant sets, the partition a setting yields is one of the systems the three-feature
theories generate, and the settings yield exactly the systems of the bivalent geometry, so no
setting yields the hearer bipartition or Zwicky's tripartition. The account's five partitions
come from two features with no geometry: the order of composition supplies the fifth. -/

/-- The partition a setting yields on participant sets: two participant sets share a part when
the same cells hold a referent with each. -/
def Setting.partition (σ : Setting) : Partition :=
  .ofFun fun P ↦ (σ.cells Examples.ℒau Examples.ℒpt Examples.ℒπ).filter fun c ↦
    ∃ s ∈ c, Examples.participants s = P

-- Table 4.1: the monopartition, the author and participant bipartitions, the tripartition with
-- the author feature composing first, and the quadripartition with the participant feature first
theorem partition_setting (b : Bool) :
    (⟨false, false, b⟩ : Setting).partition = .ofFeatures ∅ ∧
      (⟨true, false, b⟩ : Setting).partition = .ofFeatures {.speaker} ∧
      (⟨false, true, b⟩ : Setting).partition = .ofFeatures {.participant} ∧
      (⟨true, true, true⟩ : Setting).partition = .ofFeatures {.participant, .speaker} ∧
      (⟨true, true, false⟩ : Setting).partition = .ofFeatures {.speaker, .addressee} := by
  revert b; decide

-- p. 193: the systems of the bivalent geometry
theorem image_partition_eq :
    univ.image Setting.partition = (univ.filter Admissible).image Partition.ofFeatures := by
  decide

/-- The parameters of π generate the system of a set of three features exactly when the set is
admissible in the bivalent geometry: two features, their order of composition and no geometry
yield all and only the partitions the geometry stipulates. -/
theorem ofFeatures_mem_image_iff (F : Features) :
    Partition.ofFeatures F ∈ univ.image Setting.partition ↔ Admissible F := by
  rw [image_partition_eq]; revert F; decide

-- Zwicky's tripartition, inclusive with second person, is no setting's yield
theorem ofFeatures_hearer_participant_not_mem :
    Partition.ofFeatures {.addressee, .participant} ∉ univ.image Setting.partition := by
  rw [ofFeatures_mem_image_iff]; decide

theorem card_image_partition_setting : (univ.image Setting.partition).card = 5 := by
  rw [image_partition_eq]; exact card_image_ofFeatures_admissible

/-! ### Spatial deixis (chapter 7)

Object, space and path deixis attest the same five partitions as person (§7.2.1), so the person
features generate them. English *this* and *these* denote things in the speaker's vicinity and
*that* and *those* things beyond, the author bipartition (p. 171). The spatial head χ carries a
person specification to the vicinity of the referents it denotes ((16), p. 180), so *this*
denotes the vicinity of the first person's referents. -/

-- p. 171
theorem english_demonstratives_author_bipartition :
    English.Determiners.that.deixis = English.Determiners.this.deixisᶜ ∧
      ∀ s t, bundle {.speaker} s = bundle {.speaker} t ↔
        (s ∈ English.Determiners.this.deixis ↔ t ∈ English.Determiners.this.deixis) := by
  refine ⟨rfl, fun s t ↦ ?_⟩
  rw [bundle_eq_bundle_iff]; revert s t; decide

-- (16), p. 180
theorem preimage_participants_this {W E P T : Type*} [PartialOrder E]
    (c : SpeechAct.Context W E P T) :
    c.participants ⁻¹' English.Determiners.this.deixis = Person.dom c (some .first) :=
  Set.ext fun _ ↦ (Person.participants_mem_participantSets_first c _).trans
    (Person.mem_dom_first c _).symm

namespace SpatialModel

open scoped SetRel

/-! A finite model of (16): the referents are the sets of two individuals under part-of, the
speaker is `{0}` and the addressee `{1}`, and every referent is in every vicinity. -/

/-- The context of utterance has speaker `{0}` and addressee `{1}`. -/
def ctx : SpeechAct.Context Unit (Finset (Fin 2)) Unit Unit := ⟨{0}, {1}, (), (), ()⟩

/-- Every referent is in every vicinity. -/
def near : SetRel (Finset (Fin 2)) (Finset (Fin 2)) := Set.univ

/-- The assignment sends every index to the empty referent. -/
def g₀ : ℕ → Finset (Fin 2) := fun _ ↦ ∅

/-- *this* with a trivial restrictor denotes the indexed referent, which is in its vicinity. -/
example : ∅ ∈ English.Determiners.this.denote (fun _ _ ↦ Set.univ) 0 (ctx.near near) g₀ () := by
  refine DemonstrativeDeterminer.mem_denote.2 ⟨?_, ?_⟩
  · rw [SpeechAct.Context.image_near]
    exact ⟨{0}, by simp [English.Determiners.this,
      Person.participants_mem_participantSets_first, ctx], trivial⟩
  · exact (mem_iota (s := {x : Finset (Fin 2) | True ∧ x = g₀ 0})).2
      ⟨⟨trivial, rfl⟩, fun _ hx ↦ hx.2⟩

/-- With no vicinities, even a demonstrative without a deictic contrast denotes nothing. -/
example (dem : DemonstrativeDeterminer) :
    ¬ (dem.denote (fun _ _ ↦ Set.univ) 0 (ctx.near ∅) g₀ ()).Dom := by
  rintro ⟨hv, -⟩
  rw [SpeechAct.Context.image_near] at hv
  obtain ⟨x, -, hx⟩ := hv
  exact hx

/-- When a referent lies both in the speaker's vicinity and in the addressee's, *this* and *that*
both hold of it, so the two cells' vicinities need not partition the space. -/
example : g₀ 0 ∈ (ctx.near near).image English.Determiners.this.deixis ∧
    g₀ 0 ∈ (ctx.near near).image English.Determiners.that.deixis := by
  simp only [SpeechAct.Context.image_near]
  refine ⟨⟨{0}, ?_, trivial⟩, ⟨{1}, ?_, trivial⟩⟩
  · simp [English.Determiners.this, Person.participants_mem_participantSets_first, ctx]
  · simp only [English.Determiners.that, Set.mem_preimage, Finset.mem_coe, Finset.mem_compl,
      Person.participants_mem_participantSets_first, ctx]
    decide

end SpatialModel

/-! ### Harbour's signs for the Cysouw categories (Table 4.3)

The membership bundles `Person.Category.toFeatures` give the three groups including the speaker
one bundle, `{participant, author}`. Harbour's signs distinguish them, a commitment of this theory
read off the quadripartition above: a category's sign is that of the cell holding its referent. A
sign is a bivalent valuation `Person.Feature → Bool` rather than a membership bundle
`Person.Features`: the exclusive's `+author −participant` is the combination the containment
filter rejects, and the filter, which holds of membership, does not hold of operations
(chapter 9). -/

open Person (Category)

/-- The referent of a category in the model: the speaker, the addressee and the other it
contains. Several others fall onto the one other, which the person partition does not
separate from it. -/
def referent (c : Category) : Finset Examples.Ω :=
  (if .speaker ∈ c.participants then {0} else ∅) ∪
    (if .addressee ∈ c.participants then {1} else ∅) ∪ (if c.otherCount = 0 then ∅ else {2})

/-- The values of Harbour's two features. They are signs of operations on the π lattice, not
properties of a referent's participants, so they are not indexed by `Person.Feature`. -/
structure Sign where
  /-- The value of [±author]. -/
  author : Bool
  /-- The value of [±participant]. -/
  participant : Bool
  deriving DecidableEq, Repr

/-- Harbour's sign for a Cysouw category in the quadripartition (Table 4.3) is the sign of the
cell holding its referent: `+author` in the inclusive and the exclusive cells, `+participant` in
the inclusive and the second-person cells. The exclusive, and with it the singular speaker, which
the quadripartition places in the exclusive cell (p. 96), is `+author −participant`, so it does
not collapse with the inclusive `+author +participant` as under `Category.toFeatures`. -/
def signOf (c : Category) : Sign where
  author := decide (referent c ∈ Examples.inclusive ∪ Examples.exclusive)
  participant := decide (referent c ∈ Examples.inclusive ∪ Examples.secondP)

theorem signOf_author (c : Category) : (signOf c).author = true ↔ c.IncludesSpeaker := by
  cases c <;> decide +kernel

/-- In the quadripartition a category is `+participant` exactly when it includes the addressee:
composed inside [±author], the participant feature tells the addressee's presence, not a
participant's. -/
theorem signOf_participant (c : Category) :
    (signOf c).participant = true ↔ c.IncludesAddressee := by
  cases c <;> decide +kernel

theorem signOf_speakerOthers_ne_speakerAddressee :
    signOf .speakerOthers ≠ signOf .speakerAddressee := by decide

/-! ### Cysouw's first person complex

Without number, a partition fixes which of the four categories including the speaker share a
form. The quadripartition gives the singular speaker the form of the exclusive and the two
inclusives a form of their own, Cysouw's only-inclusive pattern; every other setting gives all
four one form, his pattern without a 'we'. His other common patterns separate a 'we' from the
singular speaker, which person alone cannot do. -/

open Cysouw2003 (Clusivity)

/-- The pattern of the first person complex a setting yields without number: two of the four
categories including the speaker share a form when their referents lie in one cell. -/
abbrev Setting.pattern (σ : Setting) : Clusivity.Pattern :=
  Setoid.ker fun c ↦ (σ.cells Examples.ℒau Examples.ℒpt Examples.ℒπ).filter (referent c.1 ∈ ·)

-- p. 96: the numberless quadripartition is Cysouw's only-inclusive pattern
theorem pattern_quad :
    (⟨true, true, false⟩ : Setting).pattern = Clusivity.onlyInclusive.toPattern :=
  Setoid.ext fun c d ↦ by simp only [Setoid.ker_def]; revert c d; decide +kernel

theorem pattern_eq_noWe {σ : Setting} (h : σ ≠ ⟨true, true, false⟩) :
    σ.pattern = Clusivity.noWe.toPattern :=
  Setoid.ext fun c d ↦ by simp only [Setoid.ker_def]; revert σ c d; decide +kernel

/-! ### The Tamil clusivity contrast

A pronoun entry reaches Harbour's signs through the categories its person, number and clusivity
realize (`Pronoun.categories`). Tamil's first person plural forms *naam* (inclusive) and
*naan-ŋgæ* (exclusive) realize distinct signs, where the membership bundles give both categories
`{participant, author}`. -/

open Tamil.Pronouns (naam naanŋgæ)

/-- The signs a pronoun realizes are those of its categories, several where its φ-features
underdetermine the category. -/
def harbourSign (p : Pronoun) : Finset Sign := p.categories.image signOf

theorem naam_sign : harbourSign naam.toPronoun = {⟨true, true⟩} := by decide

theorem naanŋgæ_sign : harbourSign naanŋgæ.toPronoun = {⟨true, false⟩} := by decide

/-- Harbour's signs distinguish *naam* from *naan-ŋgæ* through the Pronoun API. -/
theorem tamil_clusivity_distinguished :
    harbourSign naam.toPronoun ≠ harbourSign naanŋgæ.toPronoun := by decide

theorem tamil_clusivity_collapsed_by_toFeatures :
    naam.toPronoun.categories.image (Category.toFeatures {.participant, .speaker}) =
      naanŋgæ.toPronoun.categories.image (Category.toFeatures {.participant, .speaker}) := by
  decide

theorem signOf_speakerOthers : signOf .speakerOthers = ⟨true, false⟩ := by decide +kernel

end Harbour2016
