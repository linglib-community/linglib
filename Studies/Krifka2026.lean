module

public import Linglib.Semantics.Reference.Kind
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Dynamic.Update
public import Linglib.Logic.Assignment
public import Linglib.Fragments.English.Nouns

/-!
# Krifka (2026): Anaphora for Concepts, Kinds, and Parts in Dynamic Interpretation

Krifka treats the head noun of a DP as introducing a discourse referent for a concept, a property
with the noun's count feature. The kind pronouns take that concept to a kind: *it* takes the
concept of a mass noun to its kind, and *they* the concept of a count noun to the kind of its plural
closure, so *a spider* is resumed by *them* and *mold* by *it*. Krifka takes the feature to be
formal, like grammatical gender, since *pollen* and *pollen grains* can describe the same stuff and
are still resumed by *it* and *them* respectively, (8) and (12) on pp. 605–606. Concept referents
are presupposed by the input assignment, as the referents of names are, so they survive negation,
which is a test, while an entity referent introduced under negation does not. After *John doesn't
own a dog*, the kind pronoun *them* is therefore interpretable and a partitive is not.

## Implementation notes

* Assignments are total functions into a heterogeneous value type with a value marking
  indices outside the domain; an anaphor's presupposition is a conjunct of its update, so a
  failed presupposition makes the update empty rather than undefined.
* Negation is the paper's VP negation, the substrate's `test (neg φ)`; the sentential negation
  with its condition that the negated existential extend the input differs only in ways
  irrelevant to projection. The concept referent's presupposition is a hypothesis of the
  projection theorems; the paper derives it from the head noun's partial lexical entry.
* Which concepts sponsor kinds (*dogs from the animal shelter* does not) is left to the
  lexicon, as in the paper.
* The count feature is read off the head noun's English entry: a count noun is one a numeral
  counts (`ClassifiedNoun.IsCount`).
* Individuals form any join semilattice, as in the paper (§3); the models are Link's nonempty
  sets of atoms, `Mereology.Individual`. A kind is a function from worlds to partial
  individuals, and σ is ι of `IsGreatest`, as in (13a), so *it* is ∩, `Kind.down`. The
  sufficient condition for σ is stated for finite extensions (`Kind.down_isSome_of_supClosed`),
  where the paper has closure under arbitrary sums, since Link's model has no empty sum.

## TODO

* *cattle*, *police* and *clothes* are resumed by *they* although no numeral counts them, so
  reading the feature off the counting record selects *it* for them. The paper does not discuss
  such nouns; they need the feature recorded apart from the counting record.

## References

* [krifka-2026]
* [chierchia-1998] — the down operator
* [link-1983] — the maximal element and the plural closure
* [hofmann-2025] — entity referents under negation, the neighbouring account
-/

@[expose] public section

namespace Krifka2026

open Mereology
open DynamicSemantics (Update Condition)
open DynamicSemantics.Update (test neg)
open SetRel

variable {World E : Type*}

/-! ### Kinds from concepts -/

section Kinds

variable [SemilatticeSup E]

/-- *they* (17b) denotes the kind of the plural closure (14) of a concept. -/
noncomputable def they (P : World → Set E) : World → Option E :=
  Kind.down fun w ↦ supClosure (P w)

/-- `pronoun noun` is the kind pronoun that the head noun selects (12): *they* for a count noun,
and for a mass noun *it*, which denotes the kind of the concept, ∩ as in (13b), (17a). -/
noncomputable def pronoun (noun : English.Nouns.Noun) : (World → Set E) → World → Option E :=
  if noun.IsCount then they else Kind.down

theorem pronoun_of_isCount {noun : English.Nouns.Noun} (h : noun.IsCount) :
    pronoun (World := World) (E := E) noun = they :=
  ite_eq_left h

theorem pronoun_of_not_isCount {noun : English.Nouns.Noun} (h : ¬ noun.IsCount) :
    pronoun (World := World) (E := E) noun = Kind.down :=
  ite_eq_right h

/-- *pollen* is resumed by *it* and *pollen grains* by *they*, though they can describe the same
stuff (8), (12). -/
theorem pronoun_pollen :
    pronoun (World := World) (E := E) English.Nouns.pollen = Kind.down ∧
      pronoun (World := World) (E := E) English.Nouns.pollenGrain = they :=
  ⟨pronoun_of_not_isCount (by decide), pronoun_of_isCount (by decide)⟩

/-- On a cumulative concept the plural closure changes nothing, so *they* and *it* denote the
same kind ((16), (18d)). -/
theorem they_eq_down_of_supClosed {P : World → Set E} (h : ∀ w, SupClosed (P w)) :
    they P = Kind.down P := by
  unfold they
  simp only [fun w ↦ (h w).supClosure_eq]

end Kinds

/-- The concept *spider* holds of the two atoms of a two-atom model. -/
def spider : Unit → Set (Individual Bool) :=
  fun _ ↦ {Individual.atom true, Individual.atom false}

/-- The kind of the singular count concept is undefined with two instances (15c). -/
theorem spider_no_kind : Kind.down spider () = none := by
  refine IsAntichain.iota_isGreatest_eq_none ?_ (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ rfl) fun h ↦ Bool.noConfusion (Set.singleton_eq_singleton_iff.1
      (congrArg Subtype.val h))
  rintro _ (rfl | rfl) _ (rfl | rfl) hne h
  exacts [hne rfl, Bool.noConfusion (h rfl), Bool.noConfusion (h rfl), hne rfl]

/-- The kind of the plural closure of *spider* is the sum of the two spiders (15b). -/
theorem spiders_kind : they spider () = some (Individual.atom true ⊔ Individual.atom false) := by
  refine iota_isGreatest_eq_some_iff.2
    ⟨supClosed_supClosure (subset_supClosure (Set.mem_insert _ _))
      (subset_supClosure (Set.mem_insert_of_mem _ rfl)), ?_⟩
  refine supClosure_min (t := Set.Iic (Individual.atom true ⊔ Individual.atom false)) ?_
    fun _ hx _ hy ↦ Set.mem_Iic.2 (sup_le (Set.mem_Iic.1 hx) (Set.mem_Iic.1 hy))
  rintro x (rfl | rfl)
  · exact (le_sup_left : Individual.atom true ≤ _)
  · exact (le_sup_right : Individual.atom false ≤ _)

/-! ### Concept discourse referents and anaphoric islands -/

/-- A discourse referent is anchored to an entity, a concept with the head noun that introduced
it, a kind, or an index (§4); `undef` marks an index outside the assignment's domain. -/
inductive DRefVal (World E : Type*)
  | entity (x : E)
  | concept (P : World → Set E) (noun : English.Nouns.Noun)
  | kind (k : World → Option E)
  | index (w : World)
  | undef

/-- A heterogeneous assignment sends each index to a discourse-referent value. -/
abbrev HAssign (World E : Type*) := Assignment (DRefVal World E)

/-- `entityIntro n body` introduces an entity referent at `n` existentially, as an indexed
determiner does (40c), and leaves its restriction to `body`. -/
def entityIntro (n : ℕ) (body : Update (HAssign World E)) : Update (HAssign World E) :=
  {(g, h) | ∃ x : E, Function.update g n (.entity x) ~[body] h}

theorem test_apply_eq {C : Condition (HAssign World E)} {g h : HAssign World E}
    (hTest : g ~[test C] h) (n : ℕ) : h n = g n :=
  congrFun hTest.1.symm n

-- (5a), (25), (45)
theorem concept_survives_test {n : ℕ} {P : World → Set E} {noun : English.Nouns.Noun}
    {C : Condition (HAssign World E)} {g h : HAssign World E}
    (hPresup : g n = .concept P noun) (hTest : g ~[test C] h) : h n = .concept P noun :=
  (test_apply_eq hTest n).trans hPresup

-- (5c)
theorem entity_trapped_by_test {n : ℕ} {C : Condition (HAssign World E)}
    {g h : HAssign World E} (hNovel : g n = .undef) (hTest : g ~[test C] h) : h n = .undef :=
  (test_apply_eq hTest n).trans hNovel

/-- Under negation the concept referent persists and the entity referent does not (45); the
asymmetry lies only in where the two referents are introduced. -/
theorem concept_entity_asymmetry {nC nE : ℕ} {P : World → Set E} {noun : English.Nouns.Noun}
    {φ : Update (HAssign World E)} {g h : HAssign World E}
    (hPresup : g nC = .concept P noun) (hNovel : g nE = .undef) (hNeg : g ~[test (neg φ)] h) :
    h nC = .concept P noun ∧ h nE = .undef :=
  ⟨concept_survives_test hPresup hNeg, entity_trapped_by_test hNovel hNeg⟩

/-! ### Concept, kind and partitive anaphors -/

section Anaphors

variable [SemilatticeSup E]

/-- The empty NP (46d) presupposes a concept referent at `n` and hands its property on. -/
def emptyNP (n : ℕ) (K : (World → Set E) → Update (HAssign World E)) :
    Update (HAssign World E) :=
  {(g, h) | ∃ P noun, g n = .concept P noun ∧ g ~[K P] h}

/-- The kind pronoun (48c) presupposes a concept referent at `n` introduced by a head noun it
agrees with and introduces the kind at `m`. -/
def kindPronoun (noun : English.Nouns.Noun) (n m : ℕ) : Update (HAssign World E) :=
  {(g, h) | ∃ P, g n = .concept P noun ∧ h = Function.update g m (.kind (pronoun noun P))}

/-- The partitive PP presupposes an entity referent at `n` and introduces a part of it at `m`.
-/
def partitive (n m : ℕ) : Update (HAssign World E) :=
  {(g, h) | ∃ x y, g n = .entity x ∧ y ≤ x ∧ h = Function.update g m (.entity y)}

/-- After a negated sentence, the kind pronoun and the empty NP can take the concept referent, but a
partitive cannot take the entity referent ((5a)–(5c)). -/
theorem anaphora_after_negation {nC nE m : ℕ} {P : World → Set E} {noun : English.Nouns.Noun}
    {φ : Update (HAssign World E)} {g h : HAssign World E}
    (hPresup : g nC = .concept P noun) (hNovel : g nE = .undef) (hNeg : g ~[test (neg φ)] h) :
    (∃ h', h ~[kindPronoun noun nC m] h') ∧ (∀ K, h ~[K P] h → h ~[emptyNP nC K] h) ∧
      ¬ ∃ h', h ~[partitive nE m] h' :=
  ⟨⟨_, P, concept_survives_test hPresup hNeg, rfl⟩,
    fun _ hK ↦ ⟨P, noun, concept_survives_test hPresup hNeg, hK⟩,
    fun ⟨_, _, _, hx, _⟩ ↦ by rw [entity_trapped_by_test hNovel hNeg] at hx; cases hx⟩

end Anaphors

/-! ### *John doesn't own a dog* -/

/-- The model has two entities, John and Mary. -/
inductive Ent
  | john
  | mary
  deriving DecidableEq

/-- The concept *dog* has no instances. -/
def dog : Unit → Set (Individual Ent) := fun _ ↦ ∅

/-- The input assignment of (44e) sends 1 to John and 2 to the concept of the count noun
*dog*. -/
def g₀ : HAssign Unit (Individual Ent)
  | 1 => .entity (Individual.atom .john)
  | 2 => .concept dog English.Nouns.dog
  | _ => .undef

/-- *own [a₃ [dog]₂]* (44c) introduces a referent at 3 that falls under the concept at 2. -/
def ownADog : Update (HAssign Unit (Individual Ent)) :=
  entityIntro 3 (test {g | ∃ P noun x, g 2 = .concept P noun ∧ g 3 = .entity x ∧ x ∈ P ()})

/-- *John₁ doesn't own [a₃ [dog]₂]* (44e) is the VP negation, the test of the negated update. -/
def doesntOwnADog : Update (HAssign Unit (Individual Ent)) := test (neg ownADog)

/-- The negated sentence holds in the model, there being no dogs, and returns the input. -/
theorem doesntOwnADog_g₀ : g₀ ~[doesntOwnADog] g₀ :=
  ⟨rfl, fun ⟨_, _, rfl, _, _, _, h₂, _, hy⟩ ↦ by
    rw [Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)] at h₂
    cases h₂; exact Set.notMem_empty _ hy⟩

/-- After it, *them₂,₄* introduces the kind of dogs at 4 (48), while *it₃* has no referent
(5c). -/
theorem them_after_doesntOwnADog {h : HAssign Unit (Individual Ent)}
    (hNeg : g₀ ~[doesntOwnADog] h) :
    h ~[kindPronoun English.Nouns.dog 2 4] Function.update h 4 (.kind (they dog)) ∧
      h 3 = .undef :=
  ⟨⟨dog, concept_survives_test rfl hNeg, by rw [pronoun_of_isCount (by decide)]⟩,
    entity_trapped_by_test rfl hNeg⟩

end Krifka2026
