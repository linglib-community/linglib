module

public import Linglib.Semantics.Composition.Reduction
public import Mathlib.Tactic.DeriveFintype

/-!
# A toy model for type-driven composition

`toyModel` is a small extensional model for exercising the composition engine, with four entities
(John, Mary, a pizza and a book), one world, and a signature of two constants and eight content
relations, which `toyStructure` interprets as equalities on the entities. The fragment is of
the kind Heim and Kratzer interpret in their textbook, with proper names, intransitive and
transitive verbs, and common nouns. The words `toyWords` translate English word forms to
symbols, and the lexicon `toyLexicon` and the denotations `Toy.sleeps`, `Toy.sees`, … are read
off the model; with the logical words, quantified trees translate to logical forms that read back
to first-order formulas.

## Main definitions

* `ToyEntity`: the entity domain.
* `toyLang`, `toyStructure`: the signature and its interpretation.
* `toyModel`: the one-world composition model.
* `toyWords`, `toyLexicon`: the content words and the lexicon they induce.
* `Toy.logicalWords`, `toyVocabulary`: the logical words, and all the toy words.

## Implementation notes

The signature follows mathlib's concrete-language idiom
(`Mathlib/ModelTheory/Algebra/Ring/Basic.lean`), with arity-indexed symbol inductives and
per-symbol abbreviations in `Toy`. The structure is a closed term, so a claim about particular
entities reduces by `rfl` to an equality on `ToyEntity`. Binary relations take the subject first in
the structure and the object first as transitive-verb denotations, as `Model.pred₂` does.

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

def sleeps : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ sleepRel ()
def laughs : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ laughRel ()
def student : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ studentRel ()
def person : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ personRel ()
def pizza : Ty.Domain ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ pizzaRel ()
def sees : Ty.Domain ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ seeRel ()
def eats : Ty.Domain ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ eatRel ()
def reads : Ty.Domain ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ readRel ()

end Toy

open Toy in
/-- The toy content words translate to the symbols of the toy signature. -/
def toyWords : String → Option (Σ ty, FirstOrderConstant toyLang ty)
  | "John" => some ⟨_, .name johnConst⟩
  | "Mary" => some ⟨_, .name maryConst⟩
  | "sleeps" => some ⟨_, .rel₁ sleepRel⟩
  | "laughs" => some ⟨_, .rel₁ laughRel⟩
  | "student" => some ⟨_, .rel₁ studentRel⟩
  | "person" => some ⟨_, .rel₁ personRel⟩
  | "pizza" => some ⟨_, .rel₁ pizzaRel⟩
  | "sees" => some ⟨_, .rel₂ seeRel⟩
  | "eats" => some ⟨_, .rel₂ eatRel⟩
  | "reads" => some ⟨_, .rel₂ readRel⟩
  | _ => none

/-- The toy lexicon is the lexicon the toy words induce over the toy model. -/
def toyLexicon : Lexicon ToyEntity Unit := toyModel.lexicon toyWords ()

/-- The toy lexicon has entries of the three first-order lexical types only. -/
theorem toyLexicon_fst {s : String} {d : Denotation ToyEntity Unit} (h : toyLexicon s = some d) :
    d.1 = .e ∨ d.1 = (.e ⇒ .t) ∨ d.1 = (.e ⇒ .e ⇒ .t) := by
  simp only [toyLexicon, Model.lexicon, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  unfold toyWords at hc
  split at hc <;> cases hc <;> simp

/-- "John sleeps" composes through `Tree.interp` over the toy lexicon to the model's fact. -/
example :
    Tree.interp toyLexicon (fun _ ↦ ToyEntity.john)
      (.node () [.terminal () "John", .terminal () "sleeps"] : PhraseStructure.Tree Unit String)
      = some ⟨.t, Toy.sleeps ToyEntity.john⟩ := rfl

/-! ### Logical forms and their readback

With the logical words, a quantifier-raised tree translates to its logical form, with the mode at
each node, and the logical form reads back to the first-order formula of its truth conditions. -/

/-- The English logical words translate to the logical first-order constants. -/
def Toy.logicalWords {L : FirstOrder.Language} : String → Option (Σ ty, FirstOrderConstant L ty)
  | "every" => some ⟨_, .every⟩
  | "some" => some ⟨_, .some⟩
  | "no" => some ⟨_, .no⟩
  | "not" => some ⟨_, .neg⟩
  | "and" => some ⟨_, .conj⟩
  | "or" => some ⟨_, .disj⟩
  | _ => none

/-- The toy vocabulary translates the toy content words and the logical words. -/
def toyVocabulary (s : String) : Option (Σ ty, FirstOrderConstant toyLang ty) :=
  toyWords s <|> Toy.logicalWords s

/-- *Every student sleeps*, with the subject raised over the trace of index 1. -/
def everyStudentSleeps : PhraseStructure.Tree Unit String :=
  .node () [.node () [.terminal () "every", .terminal () "student"],
    .bind 1 () (.node () [.trace 1 (), .terminal () "sleeps"])]

open Toy in
/-- In the logical form of *every student sleeps* the determiner applies forward to the noun and
to the abstraction over the trace, which the verb applies backward to. -/
theorem translate_everyStudentSleeps : Tree.translate toyVocabulary everyStudentSleeps =
    some ⟨.t, .comp .functionalLeft
      (.comp .functionalLeft (.const .every) (.const (.rel₁ studentRel)))
      (.lam 1 (.comp .functionalRight (.var 1) (.const (.rel₁ sleepRel))))⟩ :=
  rfl

open Toy FirstOrder.Language in
/-- The logical form of *every student sleeps* reads back to `∀ x, student x → sleeps x`. -/
example : ∃ u, Tree.translate toyVocabulary everyStudentSleeps = some ⟨.t, u⟩ ∧
    u.toFormula = ((studentRel.boundedFormula₁ (var (.inr 0))).imp
      (sleepRel.boundedFormula₁ (var (.inr 0)))).all :=
  ⟨_, rfl, rfl⟩

/-- *John John* translates to nothing, since no mode combines two individuals. -/
example : Tree.translate toyVocabulary
    (.node () [.terminal () "John", .terminal () "John"] : PhraseStructure.Tree Unit String) =
      none := rfl

/-- In *every student who sleeps laughs* the relative clause abstracts over its trace and
intersects with the noun by predicate modification. -/
def everyStudentWhoSleepsLaughs : PhraseStructure.Tree Unit String :=
  .node () [.node () [.terminal () "every",
      .node () [.terminal () "student",
        .bind 2 () (.node () [.trace 2 (), .terminal () "sleeps"])] ],
    .bind 1 () (.node () [.trace 1 (), .terminal () "laughs"])]

open Toy FirstOrder.Language in
/-- The relative clause reads back as a conjunct of the restrictor, in
`∀ x, student x ∧ sleeps x → laughs x`. -/
example : ∃ u, Tree.translate toyVocabulary everyStudentWhoSleepsLaughs = some ⟨.t, u⟩ ∧
    u.toFormula = ((studentRel.boundedFormula₁ (var (.inr 0)) ⊓
      sleepRel.boundedFormula₁ (var (.inr 0))).imp (laughRel.boundedFormula₁ (var (.inr 0)))).all :=
  ⟨_, rfl, rfl⟩

/-- *Every student who sleeps laughs* holds in the toy model, where the students are the ones
who laugh. -/
example (g : Assignment ToyEntity) :
    Tree.HoldsAt (toyModel.lexicon toyVocabulary ()) g everyStudentWhoSleepsLaughs := by
  rw [Tree.holdsAt_iff_eval toyModel () rfl]
  exact fun _ hx ↦ hx.1

end HeimKratzer
