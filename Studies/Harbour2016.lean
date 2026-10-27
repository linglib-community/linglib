module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Lattice.Fold
public import Linglib.Syntax.Person.Features
public import Linglib.Syntax.Person.System
public import Linglib.Semantics.Plurality.NumberFeatures
public import Studies.Harbour2014
public import Linglib.Semantics.Plurality.FeatureAction
public import Studies.Corbett2000
public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Fragments.Tamil.Pronouns
public import Linglib.Fragments.English.Determiners
public import Linglib.Semantics.Reference.Determiner

/-!
# Harbour (2016): Impossible Persons

Harbour derives the person categories as the cells of a partition of the lattice of referents,
induced by two features, [±author] and [±participant], whose values act on lattices rather than test
membership. The plus value of a feature adds its lattice pairwise (17), the minus value subtracts
the lattice's maximum (19), Lexical Complementarity confines a cell that properly contains a sibling
to the difference (31), and the host head discards the empty set. Over the ontology of speaker,
hearer and one other, composing [±author] outermost yields the quadripartition and composing
[±participant] outermost the tripartition. Harbour's signs for Cysouw's categories keep the
exclusive apart from the inclusive, and his number chapter is the calculus of his 2014 paper, which
generates the number systems Corbett attests. The same partitions organize the deixis of objects and
spaces, English *this* and *that* realizing the author bipartition. Against the three-feature
theories he rejects (§8.2), the systems their features generate are exactly the partitions on which
resolution is defined, seven of the fifteen, and the geometry that would select his five is one he
considers and sets aside.

## Implementation notes

One other suffices for the person partition, whose four cells are fixed by the presence of the
speaker and the hearer, so the ontology is `Fin 3` and the third-person group is not modeled;
every result is checked on this finite model. Lexical Complementarity applies once, after both
features, not cyclically (appendix B.1.2.3). Pairwise addition is mathlib's `⊻`; `ominus` and
`act` come from `Semantics/Plurality/FeatureAction.lean`.

## References

* [harbour-2016]
* [harbour-2014]
* [corbett-2000]
* [cysouw-2003]
-/

@[expose] public section

namespace Harbour2016

open Finset
open Plurality.FeatureAction

/-! ### The partition construction (over `Plurality.FeatureAction`'s operators) -/

section Construction
variable {Ω : Type*} [DecidableEq Ω]

/-- Refining a cell `c` against its siblings removes every sibling cell properly contained in
it, Lexical Complementarity (31), and then discards the empty set, which no person denotes
(§4.4). -/
def refine (siblings : List (Finset (Finset Ω))) (c : Finset (Finset Ω)) :
    Finset (Finset Ω) :=
  (siblings.foldl (fun acc d ↦ if d ⊂ c then acc \ d else acc) c).erase ∅

/-- The cells of a partition are the raw denotations of its sign assignments, each refined
against the whole family. -/
def cellsOf (raws : List (Finset (Finset Ω))) : Finset (Finset (Finset Ω)) :=
  (raws.map (refine raws)).toFinset

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

/-- The author lattice `ℒau` has the single group `{i}`. -/
def ℒau : Finset (Finset Ω) := {{0}}
/-- The participant lattice `ℒpt` has the groups `{i}`, `{u}` and `{i, u}`. -/
def ℒpt : Finset (Finset Ω) := {{0}, {1}, {0, 1}}
/-- The π lattice has every nonempty set of referents as a group. -/
def ℒπ  : Finset (Finset Ω) := Ioc ∅ univ

-- p. 74
theorem lattice_chain : ℒau ⊆ ℒpt ∧ ℒpt ⊆ ℒπ := by decide

/-! #### Quadripartition — author composes outermost ([harbour-2016] §4.3.5) -/

/-- The raw quadripartition cell for the author sign `sa` and the participant sign `sp` applies
the participant value first and the author value outermost. -/
def quadRaw (sa sp : Bool) : Finset (Finset Ω) := act sa ℒau (act sp ℒpt ℒπ)

/-- The raw quadripartition cells are those of the four sign assignments. -/
def quadRaws : List (Finset (Finset Ω)) :=
  [quadRaw true true, quadRaw true false, quadRaw false true, quadRaw false false]

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

/-- The four quadripartition cells cover the π-lattice. -/
theorem quad_covers : inclusive ∪ exclusive ∪ secondP ∪ thirdP = ℒπ := by decide

/-- The four quadripartition cells are pairwise disjoint. -/
theorem quad_disjoint :
    Disjoint inclusive exclusive ∧ Disjoint inclusive secondP ∧
    Disjoint inclusive thirdP ∧ Disjoint exclusive secondP ∧
    Disjoint exclusive thirdP ∧ Disjoint secondP thirdP := by decide

theorem quad_card : (cellsOf quadRaws).card = 4 := by decide

/-- The participants of a referent are the speaker if it contains `0` and the addressee if it
contains `1`. -/
def participants (s : Finset Ω) : Finset Discourse.Role :=
  {r | (match r with | .speaker => 0 | .addressee => 1 : Ω) ∈ s}

/-- The calculus generates the library's quadripartition, each of the four cells holding exactly
the referents whose participants the corresponding person value covers. -/
theorem quad_cells_eq_participantSets :
    ∀ s ∈ ℒπ,
      (s ∈ inclusive ↔ participants s ∈ Person.firstInclusive.participantSets) ∧
      (s ∈ exclusive ↔ participants s ∈ Person.firstExclusive.participantSets) ∧
      (s ∈ secondP ↔ participants s ∈ Person.second.participantSets) ∧
      (s ∈ thirdP ↔ participants s ∈ Person.third.participantSets) := by
  decide

/-! #### Standard tripartition — participant composes outermost ([harbour-2016] §4.3.4) -/

/-- The raw tripartition cell for the participant sign `sp` and the author sign `sa` applies the
author value first and the participant value outermost. -/
def triRaw (sp sa : Bool) : Finset (Finset Ω) := act sp ℒpt (act sa ℒau ℒπ)

/-- The raw tripartition cells are those of the four sign assignments. -/
def triRaws : List (Finset (Finset Ω)) :=
  [triRaw true true, triRaw true false, triRaw false true, triRaw false false]

/-- With participant outermost the two `−participant` specifications coincide, so the
tripartition has three cells where the quadripartition has four, the noncommutativity of
feature composition (§4.2.3). -/
theorem tri_card : (cellsOf triRaws).card = 3 := by decide

theorem tri_ne_quad : cellsOf triRaws ≠ cellsOf quadRaws := by decide

/-! #### The five partitions ([harbour-2016] Table 4.1) -/

/-- The monopartition has no feature active. -/
def monoP : Finset (Finset (Finset Ω)) := cellsOf [ℒπ]
/-- The author bipartition activates `±author` alone. -/
def authorBi : Finset (Finset (Finset Ω)) := cellsOf [act true ℒau ℒπ, act false ℒau ℒπ]
/-- The participant bipartition activates `±participant` alone. -/
def participantBi : Finset (Finset (Finset Ω)) := cellsOf [act true ℒpt ℒπ, act false ℒpt ℒπ]
/-- The tripartition is the set of its cells. -/
def triP : Finset (Finset (Finset Ω)) := cellsOf triRaws
/-- The quadripartition is the set of its cells. -/
def quadP : Finset (Finset (Finset Ω)) := cellsOf quadRaws

/-- The five parameter settings of Table 4.1, no feature, `±author`, `±participant`, and the two
composition orders of both, yield five distinct partitions. -/
theorem five_partitions : [monoP, authorBi, participantBi, triP, quadP].Nodup := by decide

/-! #### No four-way singular person ([harbour-2016] Ch. 4) -/

/-- The singleton referents are `{i}`, `{u}` and `{o}`. -/
def singletons : Finset (Finset Ω) := {{0}, {1}, {2}}

/-- The inclusive, the only cell distinguishing the quadripartition from the tripartition,
contains no singleton referent, so the singular realizes only three persons. -/
theorem inclusive_has_no_singleton : inclusive ∩ singletons = ∅ := by decide

theorem inclusive_card_ge_two : ∀ s ∈ inclusive, 2 ≤ s.card := by decide

end Examples

/-! ### Three-feature theories (§8.2)

Theories with [±participant], [±author] and [±hearer] let a language activate any subset of the
three, and the active features identify the participant sets that agree on them. A set bears
[+participant] when it includes a participant, [+author] when it includes the speaker, and
[+hearer] when it includes the addressee (p. 10). Each feature is preserved by union, so each
system they generate is a congruence for union; conversely, the participant sets lacking a
feature are those below a single set, and every partition on which resolution is defined is
generated by the features it respects (`exists_generated`). The systems number seven: the five of
Table 4.1 and the two Harbour names as these theories' overgeneration, the hearer bipartition and
the tripartition Zwicky problematized, which groups inclusive with second person (p. 190). The
bivalent geometry (9), which bars [±hearer] without [±author], generates exactly the five
(p. 193); Harbour rejects it as one of sixteen geometries with nothing to select it (p. 194). -/

open Discourse

/-- A feature of the three-feature theories. -/
inductive ThreeFeature where
  | participant
  | author
  | hearer
  deriving DecidableEq, Fintype

/-- A participant set bears [+participant] when it includes a participant, [+author] when it
includes the speaker, and [+hearer] when it includes the addressee. -/
def ThreeFeature.Holds : ThreeFeature → Finset Role → Prop
  | .participant, s => s.Nonempty
  | .author, s => .speaker ∈ s
  | .hearer, s => .addressee ∈ s

instance (f : ThreeFeature) : DecidablePred f.Holds := fun _ ↦ by
  cases f <;> unfold ThreeFeature.Holds <;> infer_instance

/-- The features of `F` a participant set bears; union of participant sets is union of
bundles. -/
def bundle (F : Finset ThreeFeature) : SupHom (Finset Role) (Finset ThreeFeature) where
  toFun s := F.filter (·.Holds s)
  map_sup' s t := by
    ext f
    cases f <;> simp [ThreeFeature.Holds, Finset.union_nonempty, and_or_left]

/-- The system a set of active features generates. -/
def generated (F : Finset ThreeFeature) : SupCon (Finset Role) := SupCon.ker (bundle F)

theorem generated_r_iff {F : Finset ThreeFeature} {s t : Finset Role} :
    (generated F).r s t ↔ ∀ f ∈ F, (f.Holds s ↔ f.Holds t) := by
  show bundle F s = bundle F t ↔ _
  simp only [bundle, SupHom.coe_mk, Finset.ext_iff, Finset.mem_filter]
  refine ⟨fun h f hf ↦ ?_, fun h f ↦ ?_⟩
  · simpa only [hf, true_and] using h f
  · by_cases hf : f ∈ F
    · simp only [hf, true_and, h f hf]
    · simp [hf]

private theorem subset_iff_or_exists (a : Finset Role) :
    a = univ ∨ ∃ f : ThreeFeature, ∀ s, s ⊆ a ↔ ¬ f.Holds s := by
  revert a; decide

/-- Every congruence for union is generated by the features it respects. -/
theorem exists_generated (c : SupCon (Finset Role)) :
    ∃ F, c.toSetoid = (generated F).toSetoid := by
  classical
  refine ⟨univ.filter fun f ↦ ∀ u v, c.r u v → (f.Holds u ↔ f.Holds v), Setoid.ext ?_⟩
  intro s t
  show c.r s t ↔ (generated _).r s t
  rw [generated_r_iff]
  refine ⟨fun hst f hf ↦ (Finset.mem_filter.mp hf).2 s t hst, fun h ↦ ?_⟩
  rw [c.r_iff_forall_le]
  intro a ha
  rcases subset_iff_or_exists a with rfl | ⟨f, hf⟩
  · simp
  · simp only [hf, not_iff_not] at ha ⊢
    exact h f (Finset.mem_filter.mpr ⟨mem_univ f, ha⟩)

theorem generated_participant_author :
    (generated {.participant, .author}).toSetoid = Person.tripartition.toSetoid := by
  refine Setoid.ext fun s t ↦ ?_
  show (generated _).r s t ↔ Person.tripartition.r s t
  rw [generated_r_iff, Person.tripartition_r_iff]
  revert s t; decide

theorem generated_hearer {s t : Finset Role} :
    (generated {.hearer}).r s t ↔ (.addressee ∈ s ↔ .addressee ∈ t) := by
  rw [generated_r_iff]; revert s t; decide

theorem generated_hearer_participant {s t : Finset Role} :
    (generated {.hearer, .participant}).r s t ↔
      (s.Nonempty ↔ t.Nonempty) ∧ (.addressee ∈ s ↔ .addressee ∈ t) := by
  rw [generated_r_iff]; revert s t; decide

/-- The graph of the system `F` generates, as a finset of pairs of participant sets. -/
def graph (F : Finset ThreeFeature) : Finset (Finset Role × Finset Role) :=
  univ.filter fun p ↦ bundle F p.1 = bundle F p.2

/-- The eight sets of active features generate seven systems. -/
theorem card_image_graph : (univ.image graph).card = 7 := by decide

/-- Geometry (9) admits [±hearer] only with [±author]. -/
def Admissible (F : Finset ThreeFeature) : Prop := .hearer ∈ F → .author ∈ F

instance : DecidablePred Admissible := fun _ ↦ by unfold Admissible; infer_instance

/-- The admissible feature sets generate five systems. -/
theorem card_image_graph_admissible : ((univ.filter Admissible).image graph).card = 5 := by
  decide

/-- The two systems only the inadmissible feature sets generate are the hearer bipartition and
Zwicky's tripartition. -/
theorem graph_not_admissible :
    ∀ F, ¬ Admissible F → graph F = graph {.hearer} ∨ graph F = graph {.hearer, .participant} := by
  decide

/-! ### Number (chapter 6): the attested systems of [corbett-2000] are generated -/

open Harbour2014 (Setting Convention)

/-- Winnebago has minimal and augmented, from `±minimal` alone ([harbour-2014] Table 3). -/
def winnebago : Number.System := { values := {.minimal, .augmented} }

/-- Mebengokre has minimal, paucal and plural, from `±additive` and `±minimal`
([harbour-2014] Table 3). -/
def mebengokre : Number.System :=
  { values := {.minimal, .paucal, .plural} }

/-- A setting generates a set of number values when every value is among its system's; a
language need not lexicalize every number its features afford. -/
def Generates (σ : Setting) (c : Convention) (values : Finset Number) : Prop :=
  ∀ v ∈ values, v ∈ σ.values c 0

instance (σ : Setting) (c : Convention) (values : Finset Number) :
    Decidable (Generates σ c values) :=
  inferInstanceAs (Decidable (∀ v ∈ values, v ∈ σ.values c 0))

-- The triples are finite, `Finset Number` among them, so `decide` would otherwise range over
-- every triple rather than the twelve listed.
attribute [local instance high] List.decidableBAll in
/-- Every attested number system of [corbett-2000], and each minimal–augmented system of
[harbour-2014] Table 3, is generated by some feature setting. -/
theorem attested_number_systems_derivable :
    ∀ p ∈ ([(⟨.inactive, .inactive, .inactive⟩, .none, Corbett2000.piraha.values),
        (⟨.active, .inactive, .inactive⟩, .none, Corbett2000.english.toSystem.values),
        (⟨.active, .inactive, .inactive⟩, .none, Corbett2000.russian.toSystem.values),
        (⟨.active, .inactive, .inactive⟩, .none, Corbett2000.japanese.toSystem.values),
        (⟨.active, .active, .inactive⟩, .none, Corbett2000.upperSorbian.toSystem.values),
        (⟨.active, .active, .inactive⟩, .none, Corbett2000.slovene.toSystem.values),
        (⟨.active, .inactive, .active⟩, .one .low, Corbett2000.bayso.toSystem.values),
        (⟨.active, .recursive, .inactive⟩, .none, Corbett2000.larike.toSystem.values),
        (⟨.active, .recursive, .active⟩, .one .low, Corbett2000.lihir.toSystem.values),
        (⟨.inactive, .active, .inactive⟩, .none, winnebago.values),
        (⟨.inactive, .recursive, .inactive⟩, .none, Corbett2000.rembarrnga.values),
        (⟨.inactive, .active, .active⟩, .one .low, mebengokre.values)] :
          List (Setting × Convention × Finset Number)),
      p.2.1.Fits p.1.additive ∧ Generates p.1 p.2.1 p.2.2 := by
  decide +kernel

/-! ### Spatial deixis (chapter 7)

Object, space and path deixis attest the same five partitions as person (§7.2.1), so the person
features generate them. English *this* and *these* denote things in the speaker's vicinity and
*that* and *those* things beyond, the author bipartition (p. 171). The spatial head χ carries a
person specification to the vicinity of the referents it denotes ((16), p. 180), so *this*
denotes the vicinity of the first person's referents. -/

/-- English *this* and *that* realize the author bipartition (p. 171). -/
theorem english_demonstratives_author_bipartition :
    English.Determiners.that.deixis = English.Determiners.this.deixisᶜ ∧
      ∀ s t, (generated {.author}).r s t ↔
        (s ∈ English.Determiners.this.deixis ↔ t ∈ English.Determiners.this.deixis) := by
  refine ⟨rfl, fun s t ↦ ?_⟩
  rw [generated_r_iff]; revert s t; decide

/-- *This* picks out the vicinity of the first person's referents, so [±author] defines the
speaker's space ((16), p. 180). -/
theorem preimage_participants_this {W E P T : Type*} [PartialOrder E]
    (c : Kaplan.Context W E P T) :
    c.participants ⁻¹' English.Determiners.this.deixis = Person.dom c (some .first) :=
  Set.ext fun _ ↦ Person.participants_mem_participantSets_first c _

namespace SpatialModel

open scoped SetRel

/-! A finite model of (16): the referents are the sets of two individuals under part-of, the
speaker is `{0}` and the addressee `{1}`, and every referent is in every vicinity. -/

/-- The context of utterance has speaker `{0}` and addressee `{1}`. -/
def ctx : Kaplan.Context Unit (Finset (Fin 2)) Unit Unit := ⟨{0}, {1}, (), (), ()⟩

/-- Every referent is in every vicinity. -/
def near : SetRel (Finset (Fin 2)) (Finset (Fin 2)) := Set.univ

/-- The assignment sends every index to the empty referent. -/
def g₀ : Assignment (Finset (Fin 2)) := fun _ ↦ ∅

/-- *this* resolved with a trivial restrictor is defined and its deictic presupposition holds. -/
example : (English.Determiners.this.denote (fun _ _ _ ↦ True) 0 ctx near).toTrivalent
    (fun _ _ ↦ True) g₀ () ≠ 0 := by
  rw [Ne, Nominal.toTrivalent_eq_zero_iff, not_imp]
  refine ⟨⟨{0}, ?_, trivial⟩, ?_⟩
  · simp [English.Determiners.this, Person.participants_mem_participantSets_first, ctx]
  · rw [← ne_eq, Option.ne_none_iff_exists']
    exact ⟨∅, (iota_eq_some_iff (P := fun x : Finset (Fin 2) ↦ True ∧ x = g₀ 0)).2
      ⟨⟨trivial, rfl⟩, fun _ hx ↦ hx.2⟩⟩

/-- With no vicinities, even a demonstrative without a deictic contrast presupposes falsely. -/
example (dem : DemonstrativeDeterminer) :
    ¬ (dem.denote (fun _ _ _ ↦ True) 0 ctx ∅).presup g₀ () := by
  rintro ⟨x, -, hx⟩; exact hx

/-- When a referent lies both in the speaker's vicinity and in the addressee's, *this* and *that*
both hold of it, so the two cells' vicinities need not partition the space. -/
example : (English.Determiners.this.denote (fun _ _ _ ↦ True) 0 ctx near).presup g₀ () ∧
    (English.Determiners.that.denote (fun _ _ _ ↦ True) 0 ctx near).presup g₀ () := by
  refine ⟨⟨{0}, ?_, trivial⟩, ⟨{1}, ?_, trivial⟩⟩
  · simp [English.Determiners.this, Person.participants_mem_participantSets_first, ctx]
  · simp only [English.Determiners.that, Set.mem_preimage, Finset.coe_compl, Set.mem_compl_iff,
      Finset.mem_coe, Person.participants_mem_participantSets_first, Person.mem_dom_first, ctx]
    decide

end SpatialModel

/-! ### Harbour's signs for the Cysouw categories (Table 4.3)

The membership bundles `Person.Category.toFeatures` give the three groups including the speaker
one bundle, `{participant, author}`. Harbour's signs distinguish them, a commitment of this theory
derived from the partition above. A sign is a bivalent valuation `Person.Feature → Bool` rather
than a membership bundle `Person.Features`: the exclusive's `+author −participant` is the
combination the containment filter rejects, and the filter, which holds of membership, does not
hold of operations (chapter 9). -/

open Person (Category)

/-- Harbour's sign for a Cysouw category (Table 4.3). The exclusive, and with it the singular
speaker, which the quadripartition places in the exclusive cell (p. 96), is
`+author −participant`, so it does not collapse with the inclusive `+author +participant` as
under `Category.toFeatures`. -/
def signOf : Category → Person.Feature → Bool
  | .speakerAddressee, _ | .speakerAddresseeOthers, _ => true     -- +author +participant
  | .speaker, f | .speakerOthers, f => f == .author                -- +author −participant
  | .addressee, f | .addresseeOthers, f => f == .participant       -- −author +participant
  | .other, _ | .others, _ => false                                -- −author −participant

theorem signOf_speakerOthers_ne_speakerAddressee :
    signOf .speakerOthers ≠ signOf .speakerAddressee := by decide

/-! ### The Tamil clusivity contrast

A pronoun entry reaches Harbour's signs through the categories its person, number and clusivity
realize (`Pronoun.categories`). Tamil's first person plural forms *naam* (inclusive) and
*naan-ŋgæ* (exclusive) realize distinct signs, where the membership bundles give both categories
`{participant, author}`. -/

open Tamil.Pronouns (naam naanŋgæ)

/-- The signs a pronoun realizes are those of its categories, several where its φ-features
underdetermine the category. -/
def harbourSign (p : Pronoun) : Finset (Person.Feature → Bool) := p.categories.image signOf

theorem naam_sign : harbourSign naam.toPronoun = {fun _ ↦ true} := by decide

theorem naanŋgæ_sign : harbourSign naanŋgæ.toPronoun = {(· == .author)} := by decide

/-- Harbour's signs distinguish *naam* from *naan-ŋgæ* through the Pronoun API. -/
theorem tamil_clusivity_distinguished :
    harbourSign naam.toPronoun ≠ harbourSign naanŋgæ.toPronoun := by decide

theorem tamil_clusivity_collapsed_by_toFeatures :
    naam.toPronoun.categories.image Category.toFeatures
      = naanŋgæ.toPronoun.categories.image Category.toFeatures := by decide

/-- The exclusive's sign is the [+author, −participant] combination the containment filter on
membership bundles rejects (`Person.wellFormed_iff_isIntent`), the author as a non-participant,
which the free combinatorics of chapter 9 generate and the calculus fills
(`Examples.exclusive_includes_speaker`). -/
theorem exclusive_sign_filtered :
    ¬ IsLowerSet (↑(Finset.univ.filter (signOf .speakerOthers ·)) : Set Person.Feature) := by
  decide

end Harbour2016
