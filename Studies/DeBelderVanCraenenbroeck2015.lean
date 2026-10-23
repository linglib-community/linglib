module

public import Linglib.Data.Examples.DeBelderVanCraenenbroeck2015
public import Linglib.Fragments.Dutch.Pronouns
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Logic.Relation

/-!
# De Belder and van Craenenbroeck (2015): How to Merge a Root

Merge is asymmetric and unary: it selects a single item from the resource and pairs it with the
object under construction, the selected item projecting. The first Merge of a derivation, Primary
Merge, finds no object yet and pairs its item with the null derivation, the empty set, which leaves
a radically empty terminal at the foot of the structure. That terminal is where a root is inserted
after syntax. It has no features, it projects nothing and so has no category, it is a position
rather than a kind of item, and it lies below all the functional material of its derivation. A
phrase with several roots is built from layered derivations: each is spelled out and readmitted to
the resource as an atom, opaque to later operations and unable to project, so that there is one
root for every derivational workspace.

Since the root position has no features, Vocabulary Insertion may put any item into it, functional
items included, and their features play no part in the syntax. Dutch uses wh-words, pronouns,
conjunctions, articles and particles as roots, the pronoun *ik* 'I' in a root position triggers
default third person agreement, and the conjunction *maar* 'but' used as a verb selects no clause.
Neither an early insertion model, in which only featureless items are roots, nor a late insertion
model that reserves root positions for items marked as roots derives these examples.

## Main statements

* `roots_eq_primaryMerges`: every object a derivation builds has one root for each Primary Merge,
  that is, for each derivational workspace.
* `derives_iff`: of the models that let only featureless items or any item realize a root
  position, inserting items before or after syntax, only the one that inserts any item after
  syntax derives the Dutch examples.

## Implementation notes

* An object's label is the bundle that projects in it. Following the refinement of (42), an item
  readmitted to the resource does not project, so its mother takes the label of its sister.
* An item is functional when it belongs to a closed class, as each example records. The person
  and number of *ik* are those of `Dutch.Pronouns.ik`; the wh-typing that *waarom* would bring to
  (2) is not modelled, and (10) and (11) carry the argument that an item in a root position has no
  syntactic effect.
* The early insertion model with featureless roots is Borer's exoskeletal model, and the late
  insertion model with root positions reserved for lexical items is that of a [Root] feature.

## References

* [de-belder-van-craenenbroeck-2015]
* [borer-2005]
* [halle-marantz-1993]
* [harley-noyer-1999]
-/

@[expose] public section

namespace DeBelderVanCraenenbroeck2015

universe u

/-! ### Unary Merge and the null derivation -/

section Merge

variable {F : Type u}

mutual
/-- An object of Unary Merge is the null derivation, or the ordered pair of an item selected from
the resource with the object under construction. -/
inductive Obj (F : Type u) where
  /-- The null derivation, the empty set Primary Merge pairs its item with. -/
  | null : Obj F
  /-- The ordered pair of a selected item with the object under construction. -/
  | pair : Item F → Obj F → Obj F

/-- An item of a resource is a bundle of grammatical features, or the output of an earlier
derivation readmitted to the resource as an atom. -/
inductive Item (F : Type u) where
  /-- A bundle of grammatical features. -/
  | bundle : Finset F → Item F
  /-- An earlier derivation readmitted as an atom. -/
  | atom : Obj F → Item F
end

/-- The object is the null derivation. -/
def Obj.IsNull : Obj F → Prop
  | .null => True
  | .pair _ _ => False

instance : ∀ o : Obj F, Decidable o.IsNull
  | .null => inferInstanceAs (Decidable True)
  | .pair _ _ => inferInstanceAs (Decidable False)

/-- The bundle that projects in an object. A selected bundle projects; a readmitted atom cannot,
and the null derivation, having no features, projects nothing. -/
def Obj.label : Obj F → Option (Finset F)
  | .null => none
  | .pair (.bundle f) _ => some f
  | .pair (.atom _) δ => δ.label

mutual
/-- The root positions of an object, its null derivations, those inside its atoms included. -/
def Obj.roots : Obj F → ℕ
  | .null => 1
  | .pair a δ => a.roots + δ.roots

/-- The root positions of an item. -/
def Item.roots : Item F → ℕ
  | .bundle _ => 0
  | .atom o => o.roots
end

mutual
/-- The Primary Merges of an object, the pairs whose object under construction is the null
derivation. -/
def Obj.primaryMerges : Obj F → ℕ
  | .null => 0
  | .pair a .null => a.primaryMerges + 1
  | .pair a (.pair b δ) => a.primaryMerges + (Obj.pair b δ).primaryMerges

/-- The Primary Merges of an item. -/
def Item.primaryMerges : Item F → ℕ
  | .bundle _ => 0
  | .atom o => o.primaryMerges
end

/-- A state of a derivation, its resource and the object under construction. -/
structure State (F : Type u) where
  resource : List (Item F)
  object : Obj F

/-- A step of a derivation. -/
inductive Step : State F → State F → Prop
  /-- Unary Merge selects an item from the resource and pairs it with the object under
  construction. -/
  | merge (R₁ R₂ : List (Item F)) (a : Item F) (δ : Obj F) :
      Step ⟨R₁ ++ a :: R₂, δ⟩ ⟨R₁ ++ R₂, .pair a δ⟩
  /-- The object is spelled out and readmitted to the resource as an atom, emptying the
  workspace for a new Primary Merge. -/
  | readmit (R : List (Item F)) (a : Item F) (δ : Obj F) :
      Step ⟨R, .pair a δ⟩ ⟨.atom (.pair a δ) :: R, .null⟩

/-- The state a derivation starts from, its resource of bundles and the null derivation. -/
def State.init (R : List (Finset F)) : State F := ⟨R.map .bundle, .null⟩

/-- The root positions of a state. -/
def State.roots (s : State F) : ℕ := s.object.roots + (s.resource.map Item.roots).sum

/-- The Primary Merges of a state. -/
def State.primaryMerges (s : State F) : ℕ :=
  s.object.primaryMerges + (s.resource.map Item.primaryMerges).sum

/-- A state has one root for each Primary Merge, and one more while its workspace is empty. -/
def State.Balanced (s : State F) : Prop :=
  s.roots = s.primaryMerges + if s.object.IsNull then 1 else 0

theorem State.balanced_init (R : List (Finset F)) : (State.init R).Balanced := by
  simp [State.init, State.Balanced, State.roots, State.primaryMerges, Obj.roots, Item.roots,
    Obj.primaryMerges, Item.primaryMerges, Obj.IsNull, Function.comp_def]

theorem Step.balanced {s t : State F} (h : Step s t) (hs : s.Balanced) : t.Balanced := by
  cases h with
  | merge R₁ R₂ a δ =>
    cases δ <;> simp_all [State.Balanced, State.roots, State.primaryMerges, Obj.roots,
      Obj.primaryMerges, Obj.IsNull] <;> omega
  | readmit R a δ =>
    simp_all [State.Balanced, State.roots, State.primaryMerges, Obj.roots, Item.roots,
      Obj.primaryMerges, Item.primaryMerges, Obj.IsNull]
    omega

theorem State.Balanced.of_reflTransGen {s t : State F} (h : Relation.ReflTransGen Step s t)
    (hs : s.Balanced) : t.Balanced := by
  induction h with
  | refl => exact hs
  | tail _ hst ih => exact hst.balanced ih

theorem roots_eq_primaryMerges {R : List (Finset F)} {o : Obj F}
    (h : Relation.ReflTransGen Step (State.init R) ⟨[], o⟩) (ho : ¬ o.IsNull) :
    o.roots = o.primaryMerges := by
  simpa [State.Balanced, State.roots, State.primaryMerges, ho] using
    State.Balanced.of_reflTransGen h (State.balanced_init R)

/-- The atoms of an object's own workspace, the derivations readmitted to it, opaque to the
operations of that workspace. -/
def Obj.atoms : Obj F → List (Obj F)
  | .null => []
  | .pair (.bundle _) δ => δ.atoms
  | .pair (.atom o) δ => o :: δ.atoms

/-- The bundles of an object's own workspace, open to its operations. -/
def Obj.bundles : Obj F → List (Finset F)
  | .null => []
  | .pair (.bundle f) δ => f :: δ.bundles
  | .pair (.atom _) δ => δ.bundles

end Merge

/-! ### The sample derivations -/

/-- The grammatical features of the sample derivations. -/
inductive Feature
  | v | f | definite | plural
  deriving DecidableEq, Repr

open Relation (ReflTransGen)

/-- *the books* of (18), the definite and plural features over the null derivation. -/
def theBooks : Obj Feature := .pair (.bundle {.definite}) (.pair (.bundle {.plural}) .null)

/-- The derivation (17)–(18) of *the books* from the resource of its definite and plural
features. -/
theorem derivation_theBooks :
    ReflTransGen Step (State.init [{.definite}, {.plural}]) ⟨[], theBooks⟩ :=
  .tail (.single (.merge [_] [] _ .null)) (.merge [] [] _ _)

theorem label_theBooks : theBooks.label = some {.definite} ∧ theBooks.roots = 1 := ⟨rfl, rfl⟩

/-- A definite DP, its feature over the null derivation. -/
def dp : Obj Feature := .pair (.bundle {.definite}) .null

/-- The v-V complex, v over the null derivation. -/
def vV : Obj Feature := .pair (.bundle {.v}) .null

/-- In *The child eats the cookie* of (41) the subject and the v-V complex, each spelled out in a
derivation of its own and readmitted as an atom, are merged over the direct object. -/
def theChildEatsTheCookie : Obj Feature := .pair (.atom dp) (.pair (.atom vV) dp)

/-- The derivation (33)–(41) builds and readmits the subject, then the v-V complex, and builds
the direct object last, merging the atoms over it. -/
theorem derivation_theChildEatsTheCookie :
    ReflTransGen Step (State.init [{.v}, {.definite}, {.definite}])
      ⟨[], theChildEatsTheCookie⟩ :=
  (ReflTransGen.single (.merge [_] [_] _ .null)).tail (.readmit _ _ _) |>.tail
    (.merge [_] [_] _ .null) |>.tail (.readmit _ _ _) |>.tail (.merge [_, _] [] _ .null) |>.tail
    (.merge [] [_] _ _) |>.tail (.merge [] [] _ _)

/-- In (41) the subject and the v-V complex are atoms, opaque to extraction, while the direct
object's feature is open to it, and the clause has three roots. -/
theorem atoms_theChildEatsTheCookie :
    theChildEatsTheCookie.atoms = [dp, vV] ∧ theChildEatsTheCookie.bundles = [{.definite}] ∧
      theChildEatsTheCookie.roots = 3 :=
  ⟨rfl, rfl, rfl⟩

/-- *eat the cookie* of (42), the direct object merged with F⁰ and the v-V complex over them. -/
def eatTheCookie : Obj Feature := .pair (.atom vV) (.pair (.bundle {.f}) dp)

theorem derivation_eatTheCookie :
    ReflTransGen Step (State.init [{.v}, {.f}, {.definite}]) ⟨[], eatTheCookie⟩ :=
  (ReflTransGen.single (.merge [] [_, _] _ .null)).tail (.readmit _ _ _) |>.tail
    (.merge [_, _] [] _ .null) |>.tail (.merge [_] [] _ _) |>.tail (.merge [] [] _ _)

/-- In (42) F⁰ labels the phrase, since the readmitted v-V complex cannot project. -/
theorem label_eatTheCookie : eatTheCookie.label = some {.f} := rfl

/-! ### Functional items in root positions -/

/-- The items in root positions belong to the open class or to the closed classes of the
functional items. -/
inductive ItemClass
  | lexical | wh | pronoun | conjunction | article | particle | adverb
  deriving DecidableEq, Repr

/-- Which items may realize a root position. -/
inductive Realizers
  /-- Only items without grammatical features, the lexical ones. -/
  | featureless
  /-- Any item. -/
  | any
  deriving DecidableEq, Repr

/-- When items are inserted. -/
inductive Insertion
  /-- Before syntax, their features visible to it. -/
  | early
  /-- After syntax. -/
  | late
  deriving DecidableEq, Repr

/-- A model of root insertion says which items may realize a root position and when items are
inserted. -/
structure Model where
  realizers : Realizers
  insertion : Insertion
  deriving DecidableEq, Repr

/-- Borer's exoskeletal model, in which items are inserted early and the featureless ones are
roots. -/
def Model.exoSkeletal : Model := ⟨.featureless, .early⟩

/-- Late insertion with a [Root] feature, which reserves root positions for lexical items. -/
def Model.rootFeature : Model := ⟨.featureless, .late⟩

/-- Late insertion into the empty position of Primary Merge, which any item may realize. -/
def Model.primaryMerge : Model := ⟨.any, .late⟩

/-- A model lets an item of a class realize a root position. -/
def Model.Realizes (M : Model) (c : ItemClass) : Prop :=
  M.realizers = .any ∨ c = .lexical

instance (M : Model) (c : ItemClass) : Decidable (M.Realizes c) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The person and number features. -/
inductive Phi
  | person (p : Person)
  | number (n : Number)
  deriving DecidableEq, Repr

/-- The person and number of a pronoun. -/
def phiOf (p : Pronoun) : List Phi := p.person.toList.map .person ++ p.number.toList.map .number

open DistributedMorphology (subsetPrinciple VocabularyItem)
open scoped DistributedMorphology

/-- The present forms of *zijn* 'be', third person singular *is* the Elsewhere form. -/
def zijn : Morphology.Exponence.RuleSet (VocabularyItem Phi String) :=
  [{.person .first, .number .singular} ⟷ "ben", {.person .second, .number .singular} ⟷ "bent",
    {.number .plural} ⟷ "zijn", ∅ ⟷ "is"]

/-- *ik* in a root position brings its own person and number to the syntax when it is inserted
early, and none when it is inserted late. -/
def Model.visiblePhi (M : Model) : List Phi :=
  match M.insertion with
  | .early => phiOf Dutch.Pronouns.ik.toPronoun
  | .late => []

/-- The copula agreeing with a subject whose root position *ik* realizes. -/
def Model.copula (M : Model) : Option String :=
  subsetPrinciple zijn (M.visiblePhi.toFinset : Finset Phi)

/-- An example tests whether an item may be in a root position, the agreement it triggers there,
or the complement it selects there. -/
inductive Construction
  | rootPosition | agreement | selection
  deriving DecidableEq, Repr

/-- A model predicts an item of a class acceptable in a construction, with the copula `form`. An
item of a functional class selects a clause only when its features are visible to syntax. -/
def Model.Accepts (M : Model) (c : ItemClass) (form : Option String) : Construction → Prop
  | .rootPosition => M.Realizes c
  | .agreement => M.Realizes c ∧ M.copula = form
  | .selection => M.Realizes c ∧ M.insertion = .early

instance (M : Model) (c : ItemClass) (form : Option String) :
    ∀ k, Decidable (M.Accepts c form k)
  | .rootPosition => inferInstanceAs (Decidable (M.Realizes c))
  | .agreement => inferInstanceAs (Decidable (_ ∧ _))
  | .selection => inferInstanceAs (Decidable (_ ∧ _))

/-- The classes as named in the rows. -/
def classTable : List (String × ItemClass) :=
  [("lexical", .lexical), ("wh", .wh), ("pronoun", .pronoun), ("conjunction", .conjunction),
    ("article", .article), ("particle", .particle), ("adverb", .adverb)]

/-- The constructions as named in the rows. -/
def constructionTable : List (String × Construction) :=
  [("rootPosition", .rootPosition), ("agreement", .agreement), ("selection", .selection)]

/-- The examples (2)–(11), each with its construction, the class of the item in the root
position, the copula of the agreement example, and the judgment. -/
def data : List (Construction × ItemClass × Option String × Judgment) :=
  Examples.all.filterMap fun d ↦ do
    pure (← d.parse? "construction" constructionTable, ← d.parse? "class" classTable,
      d.feature? "copula", d.judgment)

theorem data_length : data.length = Examples.all.length := by decide +kernel

/-- A model derives the examples when it accepts exactly the acceptable ones. -/
def Model.Derives (M : Model) : Prop :=
  ∀ r ∈ data, r.2.2.2 = .acceptable ↔ M.Accepts r.2.1 r.2.2.1 r.1

instance (M : Model) : Decidable M.Derives := inferInstanceAs (Decidable (∀ r ∈ data, _))

/-- **Roots are defined structurally, and inserted late.** Only the model that lets any item
realize a root position and inserts items after syntax derives the examples: the exoskeletal and
the [Root] feature models exclude the functional items of (2)–(9), and inserting them early would
give *ik* first person agreement in (10) and *maar* its clause in (11). -/
theorem derives_iff (M : Model) : M.Derives ↔ M = .primaryMerge := by
  obtain ⟨r, i⟩ := M
  cases r <;> cases i <;> decide +kernel

end DeBelderVanCraenenbroeck2015
