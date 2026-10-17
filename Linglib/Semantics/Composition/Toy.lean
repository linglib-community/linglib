module

public import Linglib.Semantics.Composition.Reduction
public import Linglib.Semantics.Composition.Term
public import Mathlib.Tactic.DeriveFintype

/-!
# A toy model for type-driven composition

`toyModel` is a small extensional model for exercising the composition engine, with four entities
(John, Mary, a pizza and a book), one world, and a signature of two constants and eight content
relations, which `toyStructure` interprets as equalities on the entities. The fragment is of
the kind Heim and Kratzer interpret in their textbook, with proper names, intransitive and
transitive verbs, and common nouns. The naming maps `toyNaming` send English word forms to
symbols, and the lexicon `toyLexicon` and the denotations `Toy.sleeps`, `Toy.sees`, … are read
off the model.

## Main definitions

* `ToyEntity`: the entity domain.
* `toyLang`, `toyStructure`: the signature and its interpretation.
* `toyModel`: the one-world composition model.
* `toyNaming`, `toyLexicon`: the naming maps and the lexicon they induce.
* `ToyConst`, `toyTerms`: four words as constants of the typed λ-calculus, for the translation of
  trees into terms.

## Implementation notes

The signature follows mathlib's concrete-language idiom
(`Mathlib/ModelTheory/Algebra/Ring/Basic.lean`), with arity-indexed symbol inductives and
per-symbol abbreviations in `Toy`. The structure is a closed term, so a claim about particular
entities reduces by `rfl` to an equality on `ToyEntity`. Binary relations take the subject first in
the structure and the object first as transitive-verb denotations, as `Model.pred₂ext` does.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

namespace HeimKratzer

open Montague

open FirstOrder

/-- The entities of the toy model are John, Mary, a pizza and a book. -/
inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq, Fintype

/-- The function symbols of the toy signature are the constants naming entities. -/
inductive toyFunc : ℕ → Type
  | john : toyFunc 0
  | mary : toyFunc 0
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

/-- The toy composition model is extensional, with the toy structure at its one world. -/
def toyModel : Model toyLang where
  E := ToyEntity
  W := Unit
  interp _ := toyStructure

namespace Toy

/-! The per-symbol abbreviations have the types `toyLang.Constants` and `toyLang.Relations n`, so
symbols elaborate without unfolding `toyLang`. -/

abbrev johnConst : toyLang.Constants := .john
abbrev maryConst : toyLang.Constants := .mary
abbrev sleepRel : toyLang.Relations 1 := .sleep
abbrev laughRel : toyLang.Relations 1 := .laugh
abbrev studentRel : toyLang.Relations 1 := .student
abbrev personRel : toyLang.Relations 1 := .person
abbrev pizzaRel : toyLang.Relations 1 := .pizza
abbrev seeRel : toyLang.Relations 2 := .see
abbrev eatRel : toyLang.Relations 2 := .eat
abbrev readRel : toyLang.Relations 2 := .read

/-! The denotations of the toy content words are read off the model at its one world. -/

def sleeps : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext sleepRel ()
def laughs : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext laughRel ()
def student : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext studentRel ()
def person : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext personRel ()
def pizza : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext pizzaRel ()
def sees : Ty.Domain ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext seeRel ()
def eats : Ty.Domain ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext eatRel ()
def reads : Ty.Domain ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext readRel ()

end Toy

open Toy in
/-- The toy naming maps send the toy word forms to the symbols of the toy signature. -/
def toyNaming : LexNaming toyLang where
  names
    | "John" => some johnConst
    | "Mary" => some maryConst
    | _ => none
  preds₁
    | "sleeps" => some sleepRel
    | "laughs" => some laughRel
    | "student" => some studentRel
    | "person" => some personRel
    | "pizza" => some pizzaRel
    | _ => none
  preds₂
    | "sees" => some seeRel
    | "eats" => some eatRel
    | "reads" => some readRel
    | _ => none

/-- The toy lexicon is the lexicon the toy naming maps induce over the toy model. -/
def toyLexicon : Lexicon ToyEntity Unit := toyModel.lexiconAt toyNaming ()

/-- The toy naming maps classify each word once. -/
theorem toyNaming_disjoint : toyNaming.Disjoint := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro s R h
      simp only [toyNaming] at h ⊢
      split at h <;> simp_all

/-- The default logical vocabulary is fresh for the toy naming maps. -/
theorem toyNaming_freshFor : FOWords.FreshFor {} toyNaming := by
  intro s hs
  fin_cases hs <;> exact ⟨rfl, rfl, rfl⟩

/-- "John sleeps" composes through `Tree.interp` over the toy lexicon to the model's fact. -/
example :
    Tree.interp toyLexicon (fun _ ↦ ToyEntity.john)
      (.node () [.terminal () "John", .terminal () "sleeps"] : PhraseStructure.Tree Unit String)
      = some ⟨.t, Toy.sleeps ToyEntity.john⟩ := rfl

/-! ### Translation into terms

Four words as constants: a quantifier-raised tree translates to its logical form, which the
interpretation of the constants evaluates to what `Tree.interp` computes. -/

/-- The constants of the four-word signature. -/
inductive ToyConst : Ty → Type
  | every : ToyConst Ty.det
  | student : ToyConst (.e ⇒ .t)
  | sleeps : ToyConst (.e ⇒ .t)
  | john : ToyConst .e

/-- The constants denote the determiner `every` and the toy model's facts. -/
noncomputable def ToyConst.interp : {ty : Ty} → ToyConst ty → Ty.Domain ToyEntity Unit ty
  | _, .every => Quantifier.GQ.every
  | _, .student => Toy.student
  | _, .sleeps => Toy.sleeps
  | _, .john => .john

/-- The four words translate to their constants. -/
def toyTerms : String → Option (Σ ty, Term ToyConst ty)
  | "every" => some ⟨_, .const .every⟩
  | "student" => some ⟨_, .const .student⟩
  | "sleeps" => some ⟨_, .const .sleeps⟩
  | "John" => some ⟨_, .const .john⟩
  | _ => none

/-- *Every student sleeps*, with the subject raised over the trace of index 1. -/
def everyStudentSleeps : PhraseStructure.Tree Unit String :=
  .node () [.node () [.terminal () "every", .terminal () "student"],
    .bind 1 () (.node () [.trace 1 (), .terminal () "sleeps"])]

/-- The logical form of *every student sleeps* is `every(student)(λ1. sleeps(x₁))`. -/
theorem translate_everyStudentSleeps : Tree.translate toyTerms everyStudentSleeps =
    some ⟨.t, .app (.app (.const .every) (.const .student))
      (.lam 1 (.app (.const .sleeps) (.var 1)))⟩ := rfl

/-- The logical form of the raised sentence is closed. -/
example : ((Tree.translate toyTerms everyStudentSleeps).map fun d ↦ d.2.freeVars) = some ∅ := by
  rw [translate_everyStudentSleeps]; decide

/-- *John John* translates to nothing, since no mode combines two individuals. -/
example : Tree.translate toyTerms
    (.node () [.terminal () "John", .terminal () "John"] : PhraseStructure.Tree Unit String) =
      none := rfl

/-- The engine interprets *every student sleeps* as its logical form says: every student
sleeps. -/
example (g : Assignment ToyEntity) :
    Tree.interp (fun w ↦ (toyTerms w).map (Tree.evalValue ToyConst.interp g)) g everyStudentSleeps =
      some ⟨.t, ∀ x, Toy.student x → Toy.sleeps x⟩ := by
  have hc : ∀ w d, toyTerms w = some d → d.2.Closed := by
    intro w d h
    simp only [toyTerms] at h
    split at h <;> cases h <;> rfl
  rw [Tree.interp_eq_map_translate ToyConst.interp hc g g, translate_everyStudentSleeps]
  rfl

end HeimKratzer
