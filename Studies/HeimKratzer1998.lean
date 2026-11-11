module

public import Linglib.Syntax.Tree.QuantifierRaising
public import Linglib.Logic.Modal.Extensional
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.ModelTheory.Basic
public import Mathlib.Data.Fin.VecNotation
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.CallByValue
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Composition.PredicateAbstraction
public import Linglib.Semantics.Quantification.Polyadic
public import Linglib.Fragments.English.Determiners
public import Linglib.Data.Examples.HeimKratzer1998
public import Linglib.Semantics.Composition.Interpret

/-!
# Heim and Kratzer (1998): Semantics in Generative Grammar

Heim and Kratzer interpret a tree by a few general rules: Functional Application, Predicate
Modification, and Predicate Abstraction over a binder index. The rules are one grammar over the
book's types, with two families of denotations: those of Chapter 3, and from Chapter 4 the
partial functions that the Fregean article needs. [No two rules apply to the same
daughters](##HeimKratzer1998.length_derivs_le_one), the "pedantic" rules [agree with the plain
ones](##HeimKratzer1998.rel_realize) where no word is partial, a definite description may [have
a derivation and no value](##HeimKratzer1998.pmeanings_theStudent), and a determiner's
object-position entry [composes in situ](##HeimKratzer1998.derivs_inSitu). Quantifier Raising
(Chapter 7) gives *every person sees some person* [two logical forms with different
denotations](##HeimKratzer1998.meanings_surface_ne_inverse), and [changes nothing for a phrase
that denotes an individual](##HeimKratzer1998.realize_raise). For attitude reports
(Chapter 12) an extensional semantics [cannot tell two true complements
apart](##HeimKratzer1998.emeanings_agree), and Intensional Functional Application gives
*believes* [the proposition its complement
expresses](##HeimKratzer1998.imeanings_maryBelievesJanIsLoyal).

## Implementation notes

* The toy fragment's words stand in for the book's: *student who sleeps* for *house which is
  empty*, *every person sees some person* for "Some publisher offended every linguist".
* A partial function is a function into `Part`, at every function type
  (`Interpreter.Ty.cbv`), and a partial assignment a function from indices into `Part`. A tree's
  denotations are those of its derivations, so an uninterpretable tree has none and a
  presupposition failure has one that is undefined.
* The article is not a word of the plain rules, which have total denotations only.
* In Chapter 12 *is* is the identity on predicates, the book's emptiness of *is*, and (11d) is
  the falsity of (10) at the actual world, since the fragment has no negation.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

namespace HeimKratzer1998

open PhraseStructure
open PhraseStructure.Tree
open Quantifier Quantifier.Det
open Quantifier.Polyadic (iterate iterate_every_some_of_some_every)
open scoped Denotes

/-! ### Model

A small model with four entities (John, Mary, a pizza and a book) and a signature of four
constants and eight content relations, which `toyStructure` interprets as equalities on the
entities. The signature follows mathlib's concrete-language idiom
(`Mathlib/ModelTheory/Algebra/Ring/Basic.lean`), with arity-indexed symbol inductives, and the
structure is a closed term, so a claim about particular entities reduces by `rfl`. Binary
relations take the subject first in the structure and the object first as transitive-verb
denotations. -/

section ToyModel

open FirstOrder

/-- The entities of the toy model are John, Mary, a pizza and a book. -/
inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq, Fintype

/-- The function symbols of the toy signature are the constants naming entities. -/
inductive toyFunc : ℕ → Type
  | john : toyFunc 0
  | mary : toyFunc 0
  | pizza : toyFunc 0
  | book : toyFunc 0
  deriving DecidableEq

/-- The relation symbols of the toy signature are the content words at their arities. -/
inductive toyRel : ℕ → Type
  | sleep : toyRel 1
  | laugh : toyRel 1
  | student : toyRel 1
  | person : toyRel 1
  | pizza : toyRel 1
  | see : toyRel 2
  | eat : toyRel 2
  | read : toyRel 2
  deriving DecidableEq

/-- The toy signature has the toy constants as function symbols and the toy content words as
relation symbols. -/
def toyLang : Language :=
  { Functions := toyFunc
    Relations := toyRel }

/-- In the toy structure the names denote their entities, John sleeps, John and Mary laugh and
are the students and the persons, the pizza is the one pizza, John and Mary see each other, and
both eat the pizza and read the book. Binary relations take the subject first. -/
abbrev toyStructure : toyLang.Structure ToyEntity where
  funMap f _ :=
    match f with
    | .john => .john
    | .mary => .mary
    | .pizza => .pizza
    | .book => .book
  RelMap {n} r v :=
    match r, v with
    | .sleep, v => v 0 = .john
    | .laugh, v => v 0 = .john ∨ v 0 = .mary
    | .student, v => v 0 = .john ∨ v 0 = .mary
    | .person, v => v 0 = .john ∨ v 0 = .mary
    | .pizza, v => v 0 = .pizza
    | .see, v => v 0 = .john ∧ v 1 = .mary ∨ v 0 = .mary ∧ v 1 = .john
    | .eat, v => (v 0 = .john ∨ v 0 = .mary) ∧ v 1 = .pizza
    | .read, v => (v 0 = .john ∨ v 0 = .mary) ∧ v 1 = .book

namespace Toy

/-! The denotations of the content words, read off the structure. -/

def sleeps (x : ToyEntity) : Prop := toyStructure.RelMap toyRel.sleep ![x]
def student (x : ToyEntity) : Prop := toyStructure.RelMap toyRel.student ![x]
def person (x : ToyEntity) : Prop := toyStructure.RelMap toyRel.person ![x]
def sees (y x : ToyEntity) : Prop := toyStructure.RelMap toyRel.see ![x, y]

end Toy

end ToyModel

open Toy (student person)

/-! ### Words and their denotations

A word of the fragment is a symbol of the toy signature, a quantificational determiner of the
English fragment, or the definite article. The words other than the article have total
denotations, read off the toy structure, and a trace reads the assignment. -/

section Composition

open Interpreter ManySorted

/-- The words of the fragment. -/
inductive Word
  /-- A proper name. -/
  | name (c : toyFunc 0)
  /-- A noun or an intransitive verb. -/
  | pred (r : toyRel 1)
  /-- A transitive verb. -/
  | verb (r : toyRel 2)
  /-- A quantificational determiner. -/
  | det (w : QuantificationalDeterminer)
  /-- The definite article. -/
  | the
  deriving DecidableEq

/-- A proper name as a tree. -/
abbrev name (c : toyFunc 0) : Tree Unit Word := .leaf (.name c)
/-- A noun or an intransitive verb as a tree. -/
abbrev pred (r : toyRel 1) : Tree Unit Word := .leaf (.pred r)
/-- A transitive verb as a tree. -/
abbrev verb (r : toyRel 2) : Tree Unit Word := .leaf (.verb r)
/-- A quantificational determiner as a tree. -/
abbrev det (w : QuantificationalDeterminer) : Tree Unit Word := .leaf (.det w)

/-- The domains of the base sorts over the toy entities. -/
abbrev Dom : Base → Type := Base.Dom ToyEntity Unit

/-- The lexical items with total denotations, by type: names of type e, predicates of type
⟨e,t⟩, transitive verbs of type ⟨e,⟨e,t⟩⟩, determiners of type ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩, and traces,
of type e. -/
inductive Item : Ty Base → Type
  | name (c : toyFunc 0) : Item .e
  | pred (r : toyRel 1) : Item .et
  | verb (r : toyRel 2) : Item .eet
  | det (s : Det.Symbol) : Item .det
  | trace (n : ℕ) : Item .e

/-- The definite article, of type ⟨⟨e,t⟩,e⟩. -/
inductive Article : Ty Base → Type
  | the : Article (.et ⇒ .e)

/-- The readings a determiner may have. -/
def symbols : List Det.Symbol := [.every, .some, .no, .most, .few, .half, .both, .neither]

/-- The items a leaf may be: a determiner has the readings that its entry in the fragment
records, a trace is the item of its index, and the article is no total item. -/
def items : Word ⊕ ℕ → List (Σ a, Item a)
  | .inl (.name c) => [⟨_, .name c⟩]
  | .inl (.pred r) => [⟨_, .pred r⟩]
  | .inl (.verb r) => [⟨_, .verb r⟩]
  | .inl (.det w) => (symbols.filter (· ∈ w.readings)).map fun s ↦ ⟨_, .det s⟩
  | .inl .the => []
  | .inr n => [⟨_, .trace n⟩]

/-- The items a leaf may be, with the article. -/
def itemsThe : Word ⊕ ℕ → List (Σ a, Item a ⊕ Article a)
  | .inl .the => [⟨_, .inr .the⟩]
  | x => (items x).map fun ⟨a, i⟩ ↦ ⟨a, .inl i⟩

/-- The denotation of an item under a total assignment: a transitive verb takes its object
first, and a trace denotes what the assignment gives its index (the Traces and Pronouns Rule). -/
noncomputable def Item.val : {a : Ty Base} → Item a → (ℕ → ToyEntity) → a.Dom Dom
  | _, .name c => fun _ ↦ toyStructure.funMap c ![]
  | _, .pred r => fun _ x ↦ toyStructure.RelMap r ![x]
  | _, .verb r => fun _ y x ↦ toyStructure.RelMap r ![x, y]
  | _, .det s => fun _ ↦ s.denote ToyEntity
  | _, .trace n => fun g ↦ g n

/-- The denotation of an item under a partial assignment, a partial function at every function
type: a determiner is defined at partial predicates and reads where they are true, and a trace
has a denotation where the assignment is defined at its index. -/
def Item.pval : {a : Ty Base} → Item a → (ℕ → Part ToyEntity) → Part (a.cbv.Dom Dom)
  | _, .name c => fun _ ↦ .some (toyStructure.funMap c ![])
  | _, .pred r => fun _ ↦ .some fun x ↦ .some (toyStructure.RelMap r ![x])
  | _, .verb r => fun _ ↦ .some fun y ↦ .some fun x ↦ .some (toyStructure.RelMap r ![x, y])
  | _, .det s => fun _ ↦ .some fun f ↦ .some fun g ↦
      .some (s.denote ToyEntity {x | True ∈ f x} {x | True ∈ g x})
  | _, .trace n => fun g ↦ g n

/-- The Fregean definite article (5) of §4.4.1: defined at a predicate true of exactly one
individual, where it is that individual. -/
noncomputable def the : (.et ⇒ .e : Ty Base).cbv.Dom Dom :=
  fun f ↦ ⟨∃! x, True ∈ f x, fun h ↦ Classical.choose h⟩

theorem the_dom (f : ToyEntity → Part Prop) : (the f).Dom ↔ ∃! x, True ∈ f x := Iff.rfl

theorem the_eq_some {f : ToyEntity → Part Prop} {a : ToyEntity} (h : ∀ x, True ∈ f x ↔ x = a) :
    the f = .some a :=
  have hu : ∃! x, True ∈ f x := ⟨a, (h a).2 rfl, fun y hy ↦ (h y).1 hy⟩
  Part.eq_some_iff.2 ⟨hu, (h _).1 (Classical.choose_spec hu).1⟩

/-- At a total predicate true of one individual alone, the article is that individual. -/
theorem the_some {P : ToyEntity → Prop} {a : ToyEntity} (h : ∀ x, P x ↔ x = a) :
    the (fun x ↦ .some (P x)) = .some a :=
  the_eq_some fun x ↦ by simp [← h x]

/-- The denotation of an item or the article under a partial assignment. -/
noncomputable def pval : {a : Ty Base} → Item a ⊕ Article a → (ℕ → Part ToyEntity) →
    Part (a.cbv.Dom Dom)
  | _, .inl i => i.pval
  | _, .inr .the => fun _ ↦ .some the

/-! ### The book's rules

Functional Application, Predicate Modification and Predicate Abstraction are the rules of one
grammar over the book's types. Its values relative to an assignment are the denotations of rules
(11) to (16) of Chapter 5, and its values over partial functions those of the "pedantic" versions,
which are application, predicate modification and abstraction where every function is partial. -/

/-- The grammar of the book: Functional Application and Predicate Modification of sisters, and
Predicate Abstraction (16) of §5.3 over individuals. -/
abbrev grammar : ManySorted.Language (Ty Base) :=
  (application.sum predicateModification).withAbstraction fun _ ↦ .e

/-- A denotation relative to a total assignment. -/
abbrev Val (a : Ty Base) : Type := (ℕ → ToyEntity) → a.Dom Dom

/-- A denotation relative to a partial assignment: it may be undefined, and its functions are
partial. -/
abbrev PVal (a : Ty Base) : Type := (ℕ → Part ToyEntity) → Ty.PDom Dom a

/-- Total assignments: the abstract at an individual is the body at the assignment modified to
give it to the index. -/
def assignments : Assignments (ℕ → ToyEntity) (Ty.Dom Dom) fun _ ↦ .e :=
  .total Dom fun _ ↦ .e

/-- Partial assignments, (7) of §5.3.3: an abstract always has a denotation, a partial function
defined at the individuals at which the body has one, (7) of §5.4. -/
def partialAssignments : Assignments (ℕ → Part ToyEntity) (Ty.PDom Dom) fun _ ↦ .e :=
  .partial Dom fun _ ↦ .e

/-- The rules (13), (14) and (16) of Chapter 5: sisters combine at one assignment. -/
abbrev total : grammar.Structure Val := ManySorted.Language.withAbstraction.structure assignments

/-- The pedantic rules (13′) and (14′) of §5.2 and (7) and (9) of §5.4: a node has a denotation
where its daughters do and the function is defined at the argument, and a modified predicate is
defined where both predicates are. -/
abbrev pedantic : grammar.Structure PVal :=
  ManySorted.Language.withAbstraction.structure partialAssignments

/-- The interpreter of the book: an index admits abstraction over it, and sisters whichever of
application and predicate modification their types allow. -/
abbrev rules : Interpreter grammar ℕ :=
  (typeDriven (application.sum predicateModification)).withAbstraction fun _ ↦ .e

/-- The denotations of a tree relative to total assignments, for the words with total
denotations. -/
noncomputable def meanings (t : Tree Unit Word) : List (Σ a, Val a) :=
  t.values rules total Item.val items

/-- The denotations of a tree by the pedantic rules, relative to partial assignments. -/
noncomputable def pmeanings (t : Tree Unit Word) : List (Σ a, PVal a) :=
  t.values rules pedantic pval itemsThe

/-- The empty assignment. A tree's semantic value is its value under the empty assignment, (11)
of §5.3.3. -/
def emptyAssignment : ℕ → Part ToyEntity := fun _ ↦ .none

/-- "John sleeps" denotes, by Functional Application, what the model says. -/
theorem meanings_johnSleeps :
    meanings (.bin (name .john) (pred .sleep)) = [⟨.t, fun _ ↦ Toy.sleeps .john⟩] := rfl

/-- A predicate with two subjects is uninterpretable, as the book's *Ann laughed Jan* (§3.3):
no rule applies to a truth value and an individual, whatever the model. -/
theorem derivs_johnSleepsMary :
    Tree.Uninterpretable rules items (.bin (name .john) (.bin (pred .sleep) (name .mary))) :=
  ⟨by decide, rfl⟩

/-- The interpretation function is a function (§3.3): no two of the rules apply to the same
daughters, so a tree whose words are each at most one item has at most one derivation. -/
theorem length_derivs_le_one {W : Ty Base → Type} {lex : Word ⊕ ℕ → List (Σ a, W a)}
    (hl : ∀ x, (lex x).length ≤ 1) (t : Tree Unit Word) :
    (Tree.derivs rules lex t).length ≤ 1 := by
  rw [Tree.derivs_eq_values]
  exact Tree.length_values_le_one
    (fun n _ ↦ by
      cases n <;> simp [rules, Interpreter.withAbstraction, typeDriven,
        ManySorted.Language.LocallyFinite.symbols_sum])
    (fun l r ↦ by
      simpa [rules, Interpreter.withAbstraction, typeDriven] using
        length_binaryRules_application_sum_predicateModification_le_one l r) hl t

/-! ### Total and partial denotations

A total denotation and the partial one that is it are related, and every rule keeps them so: the
pedantic rules give a tree of words with total denotations a value wherever the assignment is
total, and it is the value of the plain rules. So the book states the plain rules and turns to
the pedantic ones where a word like the article is partial. -/

/-- A denotation relative to total assignments and the pedantic denotation that is it: under a
partial assignment that is a total one, defined, and the total denotation there. -/
def Rel (a : Ty Base) (v : Val a) (v' : PVal a) : Prop :=
  ∀ g g', (∀ i, g' i = .some (g i)) → Ty.PartRel a (v g) (v' g')

/-- The plain rules and the pedantic rules are logically related. -/
theorem isLogicalRel : total.IsLogicalRel pedantic Rel :=
  ManySorted.Language.withAbstraction.isLogicalRel isLogicalRel_partRel _
    (fun g g' n v v' hg ⟨y, hy, hyr⟩ i ↦ by
      cases hyr
      by_cases hi : i = n <;>
        simp [assignments, Assignments.total, partialAssignments, Assignments.partial,
          Function.update, hi, hg, hy])
    (fun _ _ h ↦ ⟨_, rfl, fun x x' hx ↦ h x (.some x') ⟨x', rfl, hx⟩⟩)

/-- Each word with a total denotation has the pedantic denotation that is it. -/
theorem rel_val : ∀ {a : Ty Base} (i : Item a), Rel a i.val i.pval
  | _, .name _ => fun _ _ _ ↦ ⟨_, rfl, rfl⟩
  | _, .pred _ => fun _ _ _ ↦ ⟨_, rfl, fun _ _ hx ↦ ⟨_, by cases hx; rfl, rfl⟩⟩
  | _, .verb _ => fun _ _ _ ↦ ⟨_, rfl, fun _ _ hy ↦ ⟨_, by cases hy; rfl, fun _ _ hx ↦
      ⟨_, by cases hx; rfl, rfl⟩⟩⟩
  | _, .det s => fun _ _ _ ↦ ⟨_, rfl, fun A f hf ↦ ⟨_, rfl, fun B f' hf' ↦ ⟨_, rfl, by
      have key {P : ToyEntity → Prop} {p : ToyEntity → Part Prop}
          (h : Ty.CbvRel (D := Dom) .et P p) : {x | True ∈ p x} = P := by
        ext x
        obtain ⟨y, hy, hyr⟩ := h x x rfl
        cases hyr
        simp [hy]
        rfl
      show _ = s.denote ToyEntity {x | True ∈ f x} {x | True ∈ f' x}
      rw [key hf, key hf']
      rfl⟩⟩⟩
  | _, .trace n => fun _ _ hg ↦ ⟨_, hg n, rfl⟩

/-- A derivation from words with total denotations has, by the pedantic rules under an
assignment that is total, a denotation, and it is the one the plain rules give. -/
theorem rel_realize {a : Ty Base} (d : grammar.Deriv Item a) :
    Rel a (d.realize total Item.val) (d.realize pedantic Item.pval) :=
  isLogicalRel.realize rel_val d

/-- No presupposition fails without a partial word: under a total assignment, a derivation from
words with total denotations has a pedantic denotation. -/
theorem dom_realize_pedantic {a : Ty Base} (d : grammar.Deriv Item a) (g : ℕ → ToyEntity) :
    (d.realize pedantic Item.pval fun i ↦ .some (g i)).Dom :=
  (rel_realize d g _ fun _ ↦ rfl).dom

/-! ### Definite descriptions

The article is defined at predicates true of exactly one individual (§4.4). In the toy model,
with two students and one pizza, *the pizza* denotes and *the student* has a derivation and no
value: a presupposition failure, a contingent matter. *The John* has no derivation, whatever the
model: it is uninterpretable (§4.4.4). -/

/-- *The pizza* has one derivation, by Functional Application. -/
theorem derivs_thePizza :
    Tree.derivs rules itemsThe (.bin (.leaf .the) (pred .pizza)) =
      [⟨.e, .binary (.inl (.inl .fa)) (.leaf (.inr .the)) (.leaf (.inl (.pred .pizza)))⟩] := rfl

/-- *The pizza* denotes the pizza, the toy model's unique one. -/
theorem pmeanings_thePizza :
    pmeanings (.bin (.leaf .the) (pred .pizza)) = [⟨.e, fun _ ↦ .some .pizza⟩] := by
  have h := the_some (P := fun x ↦ toyStructure.RelMap toyRel.pizza ![x]) (a := .pizza)
    fun _ ↦ Iff.rfl
  simp [pmeanings, Tree.values_eq_map_derivs, derivs_thePizza, pval, Item.pval, h]

/-- *The student* is a presupposition failure in the toy model, which has two students: it has
a derivation, and no value under any assignment. -/
theorem pmeanings_theStudent : ∃ v : PVal .e,
    pmeanings (.bin (.leaf .the) (pred .student)) = [⟨.e, v⟩] ∧ ∀ g, ¬ (v g).Dom := by
  refine ⟨_, rfl, fun g h ↦ ?_⟩
  have h' : ((Part.some the).bind fun f ↦
      (Part.some fun x ↦ Part.some (x = .john ∨ x = .mary)).bind f).Dom := h
  simp only [Part.bind_some] at h'
  obtain ⟨x, -, huniq⟩ := (the_dom _).1 h'
  have hj := huniq .john (by simp)
  have hm := huniq .mary (by simp)
  exact ToyEntity.noConfusion (hj.trans hm.symm)

/-- *The John*, the article with an individual, is uninterpretable: the types alone decide
it. -/
theorem derivs_theJohn :
    Tree.Uninterpretable rules itemsThe (.bin (.leaf .the) (name .john)) := ⟨by decide, rfl⟩

/-! ### Relative clauses

A relative clause gets no rule of its own: Predicate Abstraction over its trace makes it a
predicate (§5.2.3), which Predicate Modification intersects with the head noun. The vacuous
complementizer is a non-branching node. -/

/-- The subject relative `[CP who₁ [C̄ [S t₁ sleeps]]]`. -/
def tree_whoSleeps : Tree Unit Word :=
  .binder 1 (.node () (.bin (.tr 1) (pred .sleep) :: []))

/-- The noun phrase `[NP student [CP who₁ [C̄ [S t₁ sleeps]]]]`, standing in for the book's
*house which is empty*. -/
def tree_studentWhoSleeps : Tree Unit Word :=
  .bin (pred .student) tree_whoSleeps

/-- The open sentence `[S John [VP sees t₁]]`. -/
def tree_johnSeesT : Tree Unit Word :=
  .bin (name .john) (.bin (verb .see) (.tr 1))

/-- The object relative `[CP which₁ [C̄ [S John [VP sees t₁]]]]`, standing in for the book's
*which John abandoned t*. -/
def tree_whichJohnSees : Tree Unit Word :=
  .binder 1 (.node () (tree_johnSeesT :: []))

theorem meanings_whoSleeps :
    meanings tree_whoSleeps = [⟨.et, fun _ ↦ Toy.sleeps⟩] := rfl

/-- The relative clause modifies its head intersectively, restrictive relatives being "just
another kind of intersective modifier". -/
theorem meanings_studentWhoSleeps :
    meanings tree_studentWhoSleeps = [⟨.et, fun _ x ↦ Toy.student x ∧ Toy.sleeps x⟩] := rfl

/-- The open sentence denotes relative to an assignment, through its trace. -/
theorem meanings_johnSeesT :
    meanings tree_johnSeesT = [⟨.t, fun g ↦ Toy.sees (g 1) .john⟩] := rfl

/-- The one derivation of the object relative: Predicate Abstraction over the index, above
Functional Application of the verb to its trace and of the verb phrase to the subject. -/
theorem derivs_whichJohnSees :
    Tree.derivs rules items tree_whichJohnSees =
      [⟨.et, .unary (.inr (.index 1 .t)) (.binary (.inl (.inl .ba)) (.leaf (.name .john))
        (.binary (.inl (.inl .fa)) (.leaf (.verb .see)) (.leaf (.trace 1))))⟩] := rfl

/-- The object relative is assignment-independent, and denotes the individuals John sees. -/
theorem meanings_whichJohnSees :
    meanings tree_whichJohnSees = [⟨.et, fun _ x ↦ Toy.sees x .john⟩] := rfl

/-- By the pedantic rules the open sentence has no semantic value, its trace having none under
the empty assignment, and has one under an assignment defined at its index. -/
theorem pmeanings_johnSeesT : ∃ v : PVal .t,
    pmeanings tree_johnSeesT = [⟨.t, v⟩] ∧ ¬ (v emptyAssignment).Dom ∧
      ∀ (g : ℕ → Part ToyEntity) (x : ToyEntity), g 1 = .some x →
        v g = .some (Toy.sees x .john) := by
  refine ⟨fun g ↦ ((Part.some fun y ↦ Part.some fun x ↦ Part.some (Toy.sees y x)).bind
    fun k ↦ (g 1).bind k).bind fun h ↦ (Part.some ToyEntity.john).bind h, rfl, ?_, ?_⟩
  · simp [emptyAssignment]
  · intro g x hx
    simp [hx]

/-- *The student who sleeps* has one derivation: the article applies to the noun modified by
the abstract over the trace. -/
theorem derivs_theStudentWhoSleeps :
    Tree.derivs rules itemsThe (.bin (.leaf .the) tree_studentWhoSleeps) =
      [⟨.e, .binary (.inl (.inl .fa)) (.leaf (.inr .the))
        (.binary (.inl (.inr .pm)) (.leaf (.inl (.pred .student)))
          (.unary (.inr (.index 1 .t))
            (.binary (.inl (.inl .ba)) (.leaf (.inl (.trace 1))) (.leaf (.inl (.pred .sleep))))))⟩]
                :=
  rfl

/-- *The student who sleeps* denotes John, though *the student* is a presupposition failure. -/
theorem pmeanings_theStudentWhoSleeps :
    pmeanings (.bin (.leaf .the) tree_studentWhoSleeps) = [⟨.e, fun _ ↦ .some .john⟩] := by
  have h := the_some (a := .john)
    (P := fun x ↦ toyStructure.RelMap toyRel.student ![x] ∧ toyStructure.RelMap toyRel.sleep ![x])
    fun x ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨.inl h, h⟩⟩
  simp [pmeanings, Tree.values_eq_map_derivs, derivs_theStudentWhoSleeps, pval, Item.pval,
    partialAssignments, Assignments.partial, h]

/-- Under the bracketing `[[the student] [who₁ [t₁ sleeps]]]`, which §4.5 rejects, a sentence
with the definite as subject is uninterpretable. -/
theorem derivs_detNounModifier :
    Tree.Uninterpretable rules itemsThe
      (.bin (.bin (.bin (.leaf .the) (pred .student)) tree_whoSleeps)
      (pred .sleep)) :=
  ⟨by decide, rfl⟩

end Composition

/-! ### Quantifier scope

A quantifier in object position is of the wrong type for its verb, so the sentence as it is
pronounced has no denotation (§7.1). Quantifier Raising adjoins a phrase to its clause and
leaves a trace and a binder index (§7.3), so a raised quantifier takes the abstract over its
trace as its scope, and the two orders in which the quantifiers of *every person sees some
person* raise give its two scope readings (§7.5.1). A determiner is each reading its entry in
the fragment records, so a tree's denotations are those of every resolution of its words. -/

section QuantifierRaising

open Interpreter ManySorted

/-- *Every person*. -/
def everyPerson : Tree Unit Word := .bin (det English.Determiners.every) (pred .person)

/-- *Some person*. -/
def somePerson : Tree Unit Word := .bin (det English.Determiners.some_) (pred .person)

/-- *Every person sees some person* as it is pronounced. -/
def sentence : Tree Unit Word := .bin everyPerson (.bin (verb .see) somePerson)

/-- The object quantifier cannot combine with the verb where it stands: the sentence as
pronounced has no derivation. -/
theorem derivs_sentence : Tree.Uninterpretable rules items sentence := ⟨by decide, rfl⟩

/-- The surface-scope tree `[S [DP every person] [1 [S [DP some person] [2 [S t₁ [VP sees
t₂]]]]]]`, the object raised and then the subject over it. -/
def tree_surface : Tree Unit Word :=
  (sentence.raiseOf 2 somePerson).raiseOf 1 everyPerson

/-- The inverse-scope tree `[S [DP some person] [2 [S [DP every person] [1 [S t₁ [VP sees
t₂]]]]]]`, the subject raised and then the object over it. -/
def tree_inverse : Tree Unit Word :=
  (sentence.raiseOf 1 everyPerson).raiseOf 2 somePerson

theorem isLogicalForm_tree_surface : IsLogicalForm ⊥ sentence tree_surface :=
  ((IsLogicalForm.refl sentence).raiseOf rfl (passesNoIsland_bot _ _) 2).raiseOf rfl
    (passesNoIsland_bot _ _) 1

theorem isLogicalForm_tree_inverse : IsLogicalForm ⊥ sentence tree_inverse :=
  ((IsLogicalForm.refl sentence).raiseOf rfl (passesNoIsland_bot _ _) 1).raiseOf rfl
    (passesNoIsland_bot _ _) 2

/-- A name may raise as a quantifier does, and its trace has the name's own type, so raising
*John* in *John sleeps* changes nothing, as (3) of §8.1 has the truth conditions of *John
offended Mary*. -/
theorem meanings_raise_name :
    meanings ((.bin (name .john) (pred .sleep) : Tree Unit Word).raise 1 [0]) =
      meanings (.bin (name .john) (pred .sleep)) := rfl

/-- A derivation with the individual-denoting derivation `a` in place of the traces of the
index `n`. -/
def substTrace (n : ℕ) (a : grammar.Deriv Item .e) : {c : Ty Base} → Item c → grammar.Deriv Item c
  | _, .trace k => if k = n then a else ManySorted.Language.Deriv.leaf (.trace k)
  | _, .name c => ManySorted.Language.Deriv.leaf (.name c)
  | _, .pred r => ManySorted.Language.Deriv.leaf (.pred r)
  | _, .verb r => ManySorted.Language.Deriv.leaf (.verb r)
  | _, .det s => ManySorted.Language.Deriv.leaf (.det s)

/-- Raising an individual-denoting phrase is vacuous, in general: a derivation of type e
combined with the abstract over an index has the denotation of the abstract's body with the
derivation in place of the traces of that index, provided the body abstracts over no index that
is the raised one or that the phrase depends on. A quantifier takes scope because its trace is
not of its own type. -/
theorem realize_raise {b : Ty Base} (n : ℕ) (a : grammar.Deriv Item .e)
    (d : grammar.Deriv Item b)
    (hd : ∀ m ∈ ManySorted.Language.withAbstraction.binders d, m ≠ n ∧
      ∀ g u, a.realize total Item.val (Function.update g m u) = a.realize total Item.val g) :
    (ManySorted.Language.Deriv.binary (L := grammar) (.inl (.inl Application.ba)) a
        (.unary (.inr (.index n b)) d)).realize total Item.val =
      (d.bind (substTrace n a)).realize total Item.val :=
  ManySorted.Language.withAbstraction.realize_raise assignments Item.val (substTrace n a) n
    (.inl Application.ba) (fun _ _ ↦ rfl) a
    (fun w g ↦ by
      cases w with
      | trace k =>
        by_cases hk : k = n
        · subst hk
          simp [substTrace, Item.val, assignments, Assignments.total]
        · simp [substTrace, hk, Item.val, assignments, Assignments.total]
      | _ => rfl)
    (fun g m u v hm ↦
      show Function.update (Function.update g n v) m u = _ from
        Function.update_comm hm.symm v u g) d hd

/-- Raising needs a new index. In `[every person [1 [t₂ [sees t₁]]]]` the object trace is bound
by *every person*; raising `t₂` under that binder with the index 1 again captures the object
trace, and the quantifier's variable no longer occurs in its scope. -/
theorem meanings_raise_captures :
    meanings (.bin everyPerson (.binder 1 (.bin (.tr 2) (.bin (verb .see) (.tr 1))))) =
        [⟨.t, fun g ↦ every person fun x ↦ Toy.sees x (g 2)⟩] ∧
      meanings (.bin everyPerson (.binder 1
        ((.bin (.tr 2) (.bin (verb .see) (.tr 1)) : Tree Unit Word).raise 1 [0]))) =
        [⟨.t, fun g ↦ every person fun _ ↦ Toy.sees (g 2) (g 2)⟩] :=
  ⟨rfl, rfl⟩

/-- The surface-scope reading `∀ > ∃` puts `every` over `some`, with `x sees y`. -/
abbrev surfaceScopeProp : Prop :=
  iterate every Det.some person person fun x y ↦ Toy.sees y x

/-- The inverse-scope reading, `∃ > ∀`. -/
abbrev inverseScopeProp : Prop :=
  iterate Det.some every person person fun y x ↦ Toy.sees y x

theorem surface_scope_true : surfaceScopeProp := by
  rintro x (rfl | rfl)
  · exact ⟨.mary, .inr rfl, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨.john, .inl rfl, .inr ⟨rfl, rfl⟩⟩

theorem inverse_scope_false : ¬inverseScopeProp := by
  rintro ⟨y, (rfl | rfl), hall⟩
  · exact nomatch hall (Or.inl rfl)
  · exact nomatch hall (Or.inr rfl)

theorem inverse_entails_surface : inverseScopeProp → surfaceScopeProp :=
  iterate_every_some_of_some_every _ _ _

/-- The one derivation of the surface-scope tree: each quantifier applies, by Functional
Application, to the abstract over its own index. -/
theorem derivs_surface :
    Tree.derivs rules items tree_surface =
      [⟨.t, .binary (.inl (.inl .fa))
        (.binary (.inl (.inl .fa)) (.leaf (.det .every)) (.leaf (.pred .person)))
        (.unary (.inr (.index 1 .t)) (.binary (.inl (.inl .fa))
          (.binary (.inl (.inl .fa)) (.leaf (.det .some)) (.leaf (.pred .person)))
          (.unary (.inr (.index 2 .t)) (.binary (.inl (.inl .ba)) (.leaf (.trace 1))
            (.binary (.inl (.inl .fa)) (.leaf (.verb .see)) (.leaf (.trace 2)))))))⟩] := rfl

theorem meanings_surface : meanings tree_surface = [⟨.t, fun _ ↦ surfaceScopeProp⟩] := rfl

theorem meanings_inverse : meanings tree_inverse = [⟨.t, fun _ ↦ inverseScopeProp⟩] := rfl

/-- The two logical forms of the sentence have different denotations. -/
theorem meanings_surface_ne_inverse : meanings tree_surface ≠ meanings tree_inverse := by
  rw [meanings_surface, meanings_inverse]
  intro h
  have h' : (fun _ : ℕ → ToyEntity ↦ surfaceScopeProp) = fun _ ↦ inverseScopeProp := by
    simpa using h
  exact inverse_scope_false (congrFun h' (fun _ ↦ .john) ▸ surface_scope_true)

end QuantifierRaising

/-- `objectShift D` is the object-position entry of the determiner `D`, which the book's lexical
rule (§7.2.1) derives from the basic one. It takes an object-first two-place predicate and the
subject and quantifies over the object. -/
def objectShift {E : Type*} (D : Det E) : (E → Prop) → (E → E → Prop) → E → Prop :=
  fun P R x ↦ D P fun y ↦ R y x

@[simp] theorem objectShift_apply {E : Type*} (D : Det E) (P : E → Prop) (R : E → E → Prop)
    (x : E) : objectShift D P R x = D P fun y ↦ R y x := rfl


/-! ### Quantifiers in situ

In §7.2.1's alternative to movement a lexical rule gives each determiner an object-position
entry beside its basic one, and the flat tree composes by Functional Application alone, the
types choosing the entry at each position. -/

section InSitu

open Interpreter ManySorted

/-- The object-position entry of a determiner, of type ⟨⟨e,t⟩,⟨⟨e,⟨e,t⟩⟩,⟨e,t⟩⟩⟩. -/
inductive ObjectDet : Ty Base → Type
  | shift (s : Det.Symbol) : ObjectDet (.et ⇒ .eet ⇒ .et)

/-- The items a leaf may be under the lexical rule: a determiner is its basic entry or its
object-position entry. -/
def itemsFlex : Word ⊕ ℕ → List (Σ a, Item a ⊕ ObjectDet a)
  | .inl (.det w) => (symbols.filter (· ∈ w.readings)).flatMap fun s ↦
      [⟨_, .inl (.det s)⟩, ⟨_, .inr (.shift s)⟩]
  | x => (items x).map fun ⟨a, i⟩ ↦ ⟨a, .inl i⟩

/-- The denotation of an item or an object-position entry. -/
noncomputable def flexVal : {a : Ty Base} → Item a ⊕ ObjectDet a → Val a
  | _, .inl i => i.val
  | _, .inr (.shift s) => fun _ ↦ objectShift (s.denote ToyEntity)

/-- The book's in-situ tree on the toy fragment, `[S [DP every person] [VP sees [DP some
person]]]`, with no movement. -/
def tree_inSitu : Tree Unit Word :=
  .bin (.bin (det English.Determiners.every) (pred .person))
    (.bin (verb .see) (.bin (det English.Determiners.some_) (pred .person)))

/-- The flat tree has one derivation, by Functional Application alone: the subject determiner
is its basic entry and the object determiner its object-position entry. -/
theorem derivs_inSitu :
    Tree.derivs rules itemsFlex tree_inSitu =
      [⟨.t, .binary (.inl (.inl .fa))
        (.binary (.inl (.inl .fa)) (.leaf (.inl (.det .every))) (.leaf (.inl (.pred .person))))
        (.binary (.inl (.inl .ba)) (.leaf (.inl (.verb .see)))
          (.binary (.inl (.inl .fa)) (.leaf (.inr (.shift .some))) (.leaf (.inl (.pred
              .person)))))⟩] :=
  rfl

/-- The flat tree denotes the surface-scope reading. -/
theorem meanings_inSitu :
    tree_inSitu.values rules total flexVal itemsFlex =
      [⟨.t, fun _ ↦ surfaceScopeProp⟩] := rfl

/-- With the basic entries alone a quantifier in object position is uninterpretable (§7.1). -/
theorem derivs_basicObject :
    Tree.Uninterpretable rules items (.bin (name .john)
      (.bin (verb .see) (.bin (det English.Determiners.some_) (pred .person)))) :=
  ⟨by decide, rfl⟩

end InSitu

/-! ### Intensional semantics (Chapter 12)

Denotations are relative to a world as well as an assignment, predicates vary with the world,
and an attitude verb takes a proposition, of type ⟨s,t⟩. The rules are as before, with one more:
Intensional Functional Application, which gives a function of intensions the intension of its
sister. The fragment has no traces, and its denotations are relative to a world alone. -/

section Intensional

open Interpreter ManySorted ModalLogic SetRel

/-- Intensional Functional Application (9) of §12.3: a function of intensions applies to the
intension of its sister, in either order. -/
inductive IntensionalApplication : Ty Base → Ty Base → Ty Base → Type
  /-- The function on the left. -/
  | ifa {b c : Ty Base} : IntensionalApplication (.intens b ⇒ c) b c
  /-- The function on the right. -/
  | iba {b c : Ty Base} : IntensionalApplication b (.intens b ⇒ c) c

/-- The rule of Intensional Functional Application that applies to two types. -/
def IntensionalApplication.rules (l r : Ty Base) : List (Σ u, IntensionalApplication l r u) :=
  (match l with
    | .fn (.fn (.base .s) b) c => if h : b = r then [⟨c, h ▸ .ifa⟩] else []
    | _ => []) ++
  match r with
    | .fn (.fn (.base .s) b) c => if h : b = l then [⟨c, h ▸ .iba⟩] else []
    | _ => []

/-- Intensional Functional Application, as a language over the types. -/
@[reducible] def intensionalApplication : ManySorted.Language (Ty Base) :=
  .mk₂ (fun _ _ ↦ PEmpty) IntensionalApplication

instance : intensionalApplication.LocallyFinite :=
  .mk₂ (fun _ ↦ []) IntensionalApplication.rules nofun fun m ↦ by
    cases m <;> simp [IntensionalApplication.rules]

variable {E W : Type}

/-- A denotation relative to a world. -/
abbrev IVal (E W : Type) (a : Ty Base) : Type := W → a.Dom (Base.Dom E W)

/-- Functional Application relative to a world. -/
abbrev extensional : application.Structure (IVal E W) :=
  (inferInstance : application.Structure (Ty.Dom (Base.Dom E W))).pi W

/-- Functional Application and Intensional Functional Application relative to a world: the
first combines sisters at one world, and the second gives the function at a world the whole
intension of its sister. -/
@[instance_reducible] def intensional :
    (application.sum intensionalApplication).Structure (IVal E W) :=
  ((inferInstance : application.Structure (Ty.Dom (Base.Dom E W))).pi W).sum
    (.mk₂ nofun fun
      | .ifa, f, x => fun w ↦ f w x
      | .iba, x, f => fun w ↦ f w x)

/-- The words of the fragment. -/
inductive IWord
  | mary | jan | dick | is | loyal | deceitful | believes

/-- The lexical items by type: names, the copula, two predicates, and for *believes* an entry
that takes a proposition and, for the argument of §12.2, one that takes a truth value. -/
inductive IItem : Ty Base → Type
  | mary : IItem .e
  | jan : IItem .e
  | dick : IItem .e
  | is : IItem (.et ⇒ .et)
  | loyal : IItem .et
  | deceitful : IItem .et
  | believes : IItem (.intens .t ⇒ .e ⇒ .t)
  | believesExt : IItem (.t ⇒ .e ⇒ .t)

/-- The items of the words, *believes* taking a proposition. -/
def iitems : IWord ⊕ ℕ → List (Σ a, IItem a)
  | .inl .mary => [⟨_, .mary⟩]
  | .inl .jan => [⟨_, .jan⟩]
  | .inl .dick => [⟨_, .dick⟩]
  | .inl .is => [⟨_, .is⟩]
  | .inl .loyal => [⟨_, .loyal⟩]
  | .inl .deceitful => [⟨_, .deceitful⟩]
  | .inl .believes => [⟨_, .believes⟩]
  | .inr _ => []

/-- The items of the words in an extensional semantics, *believes* taking a truth value. -/
def iitemsExt : IWord ⊕ ℕ → List (Σ a, IItem a)
  | .inl .believes => [⟨_, .believesExt⟩]
  | x => iitems x

variable (loyal deceitful : W → E → Prop) (believes : E → SetRel W W) (mary jan dick : E)
  (believesExt : W → Prop → E → Prop)

/-- The denotations of the items (4), (5) and the entry for *believe* of §12.3: names are rigid,
*is* is empty, predicates vary with the world, and *believes* holds of a proposition and an
individual at a world where the proposition is true at every world compatible with what the
individual believes there. -/
def IItem.val : {a : Ty Base} → IItem a → IVal E W a
  | _, .mary => fun _ ↦ mary
  | _, .jan => fun _ ↦ jan
  | _, .dick => fun _ ↦ dick
  | _, .is => fun _ P ↦ P
  | _, .loyal => fun w x ↦ loyal w x
  | _, .deceitful => fun w x ↦ deceitful w x
  | _, .believes => fun w p x ↦ □[believes x] p w
  | _, .believesExt => fun w p x ↦ believesExt w p x

/-- *Jan is loyal*. -/
def janIsLoyal : Tree Unit IWord := .bin (.leaf .jan) (.bin (.leaf .is) (.leaf .loyal))

/-- *Dick is deceitful*. -/
def dickIsDeceitful : Tree Unit IWord := .bin (.leaf .dick) (.bin (.leaf .is) (.leaf .deceitful))

/-- *Mary believes Jan is loyal*. -/
def maryBelievesJanIsLoyal : Tree Unit IWord :=
  .bin (.leaf .mary) (.bin (.leaf .believes) janIsLoyal)

/-- *Mary believes Dick is deceitful*. -/
def maryBelievesDickIsDeceitful : Tree Unit IWord :=
  .bin (.leaf .mary) (.bin (.leaf .believes) dickIsDeceitful)

/-- The denotations of a tree by Functional Application and Intensional Functional
Application. -/
def imeanings (t : Tree Unit IWord) : List (Σ a, IVal E W a) :=
  t.values (typeDriven (application.sum intensionalApplication)) intensional
    (IItem.val loyal deceitful believes mary jan dick believesExt) iitems

/-- The denotations of a tree by Functional Application alone, in the extensional semantics
where *believes* takes a truth value. -/
def emeanings (t : Tree Unit IWord) : List (Σ a, IVal E W a) :=
  t.values (typeDriven application) extensional
    (IItem.val loyal deceitful believes mary jan dick believesExt) iitemsExt

theorem imeanings_janIsLoyal :
    imeanings loyal deceitful believes mary jan dick believesExt janIsLoyal =
      [⟨.t, fun w ↦ loyal w jan⟩] := rfl

/-- Functional Application cannot give *believes* its complement, a truth value where the verb
wants a proposition. -/
theorem derivs_maryBelievesJanIsLoyal_application :
    Tree.Uninterpretable (typeDriven application) iitems maryBelievesJanIsLoyal := ⟨by decide, rfl⟩

/-- The one derivation of the report: Intensional Functional Application of the verb to its
complement, and Functional Application elsewhere. -/
theorem derivs_maryBelievesJanIsLoyal :
    Tree.derivs (typeDriven (application.sum intensionalApplication)) iitems
        maryBelievesJanIsLoyal =
      [⟨.t, .binary (.inl .ba) (.leaf .mary) (.binary (.inr .ifa) (.leaf .believes)
        (.binary (.inl .ba) (.leaf .jan) (.binary (.inl .fa) (.leaf .is) (.leaf .loyal))))⟩] :=
  rfl

/-- (8) of §12.3 is true at a world iff Jan is loyal at every world compatible with what Mary
believes there. -/
theorem imeanings_maryBelievesJanIsLoyal :
    imeanings loyal deceitful believes mary jan dick believesExt maryBelievesJanIsLoyal =
      [⟨.t, fun w ↦ □[believes mary] (fun w' ↦ loyal w' jan) w⟩] := rfl

theorem imeanings_maryBelievesDickIsDeceitful :
    imeanings loyal deceitful believes mary jan dick believesExt maryBelievesDickIsDeceitful =
      [⟨.t, fun w ↦ □[believes mary] (fun w' ↦ deceitful w' dick) w⟩] := rfl

/-- The problem of §12.2: in an extensional semantics, whatever *believes* denotes, the two
reports have one truth value at a world where *Jan is loyal* and *Dick is deceitful* do. -/
theorem emeanings_agree {w : W} (h : loyal w jan ↔ deceitful w dick) : ∃ p q : W → Prop,
    emeanings loyal deceitful believes mary jan dick believesExt maryBelievesJanIsLoyal =
        [⟨.t, p⟩] ∧
      emeanings loyal deceitful believes mary jan dick believesExt maryBelievesDickIsDeceitful =
        [⟨.t, q⟩] ∧ (p w ↔ q w) :=
  ⟨_, _, rfl, rfl, by
    show believesExt w (loyal w jan) mary ↔ believesExt w (deceitful w dick) mary
    rw [propext h]⟩

/-- An attitude verb's complement is a nonextensional context at `w` exactly when the subject's
attitude at `w` leaves open a world other than `w`: only for a subject who rules out every other
world does the truth value of the complement fix the report. -/
theorem believes_isExtensionalAt_iff {x : E} {w : W} :
    IsExtensionalAt (fun p w' ↦ □[believes x] p w') w ↔ ∀ v, w ~[believes x] v → v = w :=
  isExtensionalAt_box_iff

/-- The two worlds of the model for (11). -/
inductive Ch12World | actual | other

/-- The individuals of the model for (11). -/
inductive Ch12Person | mary | jan | dick

/-- (11) of §12.3: Jan is loyal and Dick deceitful at the actual world, Mary believes that Jan is
loyal, and she does not believe that Dick is deceitful, since her beliefs leave open a world
where he is not. -/
theorem janIsLoyal_dickIsDeceitful_maryBelieves (b : Ch12World → Prop → Ch12Person → Prop) :
    let m := imeanings (W := Ch12World) (fun _ x ↦ x = .jan)
      (fun w x ↦ w = .actual ∧ x = .dick) (fun _ ↦ Set.univ) Ch12Person.mary .jan .dick b
    (∃ p, m janIsLoyal = [⟨.t, p⟩] ∧ p .actual) ∧
      (∃ p, m dickIsDeceitful = [⟨.t, p⟩] ∧ p .actual) ∧
      (∃ p, m maryBelievesJanIsLoyal = [⟨.t, p⟩] ∧ p .actual) ∧
      ∃ p, m maryBelievesDickIsDeceitful = [⟨.t, p⟩] ∧ ¬ p .actual :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, fun _ _ ↦ rfl⟩,
    ⟨_, rfl, fun h ↦ nomatch (h .other trivial).1⟩⟩

end Intensional

end HeimKratzer1998
