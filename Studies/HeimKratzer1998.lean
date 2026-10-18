module

public import Linglib.Semantics.Composition.Tree
public import Linglib.Semantics.Composition.Assignment
public import Linglib.Semantics.Composition.FirstOrder
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Composition.Partial
public import Linglib.Semantics.Quantification.Polyadic
public import Linglib.Fragments.English.Determiners
public import Linglib.Data.Examples.HeimKratzer1998

/-!
# Heim and Kratzer (1998): Semantics in Generative Grammar

Heim and Kratzer interpret a tree by a few general rules: Functional Application, Predicate
Modification, Predicate Abstraction over a binder index, and, from Chapter 4, partial
denotations, with a Fregean definite article that may leave a node undefined. The library's
engines `Tree.interp` and `Tree.interpPartial` implement these rules. Here the book's rules are
transcribed as interpretation relations that the engines extend, and the engines are run on the
toy model for the book's definite descriptions (Chapter 4), relative clauses (Chapter 5) and
quantifier scope (Chapter 7).

## Main results

* `interp_of_denotes`, `Partial.interp_of_denotes`: where the book's rules assign a value, the
  engines compute it.
* `the_student_fails`, `the_pizza`, `the_john_uninterpretable`: presupposition failure and
  uninterpretability with the Fregean article (§4.4).
* `interp_studentWhoSleeps`, `the_student_who_sleeps`: a restrictive relative clause is an
  intersective modifier, so *the student who sleeps* is defined although *the student* is not
  (§5.1).
* `det_noun_modifier_uninterpretable`: the bracketing [[the noun] modifier] is uninterpretable
  (§4.5).
* `scope_ambiguity_computed`, `surfaceScopeProp_mem_readings_inSitu`: the two Quantifier Raising
  derivations of a doubly quantified sentence compute its two scope readings (§7.3), and the
  in-situ alternative of §7.2.1 derives the surface one.

## Implementation notes

The toy fragment's words stand in for the book's: *student who sleeps* for *house which is
empty*, *every person sees some person* for "Some publisher offended every linguist". With
`interpTy .t = Prop` the engines produce truth conditions as propositions.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

namespace HeimKratzer1998

open Montague
open scoped Assignment
open PhraseStructure
open PhraseStructure.Tree
open Quantifier Quantifier.GQ
open Quantifier.Polyadic (surfaceScope inverseScope iterate_every_some_of_some_every)
open English.Determiners (QuantityWord)
open scoped Semantics

/-! ### Model and lexicon

`toyModel` is a small extensional model with four entities (John, Mary, a pizza and a book), one
world, and a signature of two constants and eight content relations, which `toyStructure`
interprets as equalities on the entities. The fragment is of the kind the book interprets, with
proper names, intransitive and transitive verbs, and common nouns. The words `toyWords`
translate English word forms to symbols, and the lexicon `toyLexicon` and the denotations
`Toy.sleeps`, `Toy.sees`, … are read off the model. The signature follows mathlib's
concrete-language idiom (`Mathlib/ModelTheory/Algebra/Ring/Basic.lean`), with arity-indexed
symbol inductives and per-symbol abbreviations in `Toy`. The structure is a closed term, so a
claim about particular entities reduces by `rfl` to an equality on `ToyEntity`. Binary relations
take the subject first in the structure and the object first as transitive-verb denotations, as
`Model.pred₂` does. -/

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
def toyWords : String → Option ((ty : Ty) × FirstOrderConstant toyLang ty)
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
      (.bin (.leaf "John") (.leaf "sleeps") : Tree Unit String) =
        some ⟨.t, Toy.sleeps ToyEntity.john⟩ := rfl

end ToyModel

open Toy (student person)

/-- A reading as a composition terminal on the entity domain `E`, at the determiner type. -/
def toDenotation (d : Family.{0}) (E W : Type) [Fintype E] : Denotation E W := ⟨Ty.det, d E⟩

/-- The terminals of a set of readings on a domain. -/
def terminals (s : Set Family.{0}) (E W : Type) [Fintype E] : Set (Denotation E W) :=
  (toDenotation · E W) '' s

/-- `objectShift D` is the object-position entry of the determiner `D`, which the book's lexical
rule (§7.2.1) derives from the basic one. It takes an object-first two-place predicate and the
subject and quantifies over the object. -/
def objectShift {E : Type*} (D : GQ E) : (E → Prop) → (E → E → Prop) → E → Prop :=
  fun P R x ↦ D P fun y ↦ R y x

@[simp] theorem objectShift_apply {E : Type*} (D : GQ E) (P : E → Prop) (R : E → E → Prop)
    (x : E) : objectShift D P R x = D P fun y ↦ R y x := rfl

/-- The object-position entry of a terminal of the determiner type, the book's lexical rule
applied to a lexical item, and `none` at any other type. -/
def objectShift? {E W : Type} (d : Denotation E W) : Option (Denotation E W) :=
  if h : d.1 = Ty.det then
    Option.some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .e ⇒ .t) ⇒ .e ⇒ .t,
      objectShift (h ▸ d.2 : Ty.Domain E W Ty.det)⟩
  else none

/-- The object-position entries the lexical rule derives from a set of readings. -/
def objectShifts {E W : Type} (s : Set (Denotation E W)) : Set (Denotation E W) :=
  {d | ∃ d₁ ∈ s, objectShift? d₁ = some d}

/-- The study's stand on the quantifier words, the one reading each of *every* and *some* makes
available, as a terminal on the toy domain. -/
def quantifierReading : QuantityWord → Option (Denotation ToyEntity Unit)
  | .every => some (toDenotation Family.every ToyEntity Unit)
  | .some_ => some (toDenotation Family.some ToyEntity Unit)
  | _ => none

/-- Each chosen terminal is among the terminals of the word's available readings. -/
theorem quantifierReading_mem {w : QuantityWord} {d : Denotation ToyEntity Unit}
    (h : quantifierReading w = some d) : d ∈ terminals ⟦w⟧ ToyEntity Unit := by
  cases w <;> simp only [quantifierReading, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact Set.mem_image_of_mem _ (Set.mem_singleton _)

/-- The leaf interpretation reads the quantifier words through their readings and the toy
fragment's nouns and verbs through the toy lexicon. -/
def lex : QuantityWord ⊕ String → Option (Denotation ToyEntity Unit) :=
  Sum.elim quantifierReading toyLexicon

/-- The assignment `g₀` sends every index to John. -/
def g₀ : Assignment ToyEntity := fun _ ↦ .john

/-! ### The book's rules

The extensional rules of Chapters 3 to 5, one constructor per rule. The engine at `M = Id`
extends them. -/

section Reference

variable {C L E W : Type}

/-- The book's interpretation relation, relative to a leaf interpretation and an assignment. -/
inductive Denotes (lex : L → Option (Denotation E W)) :
    Assignment E → Tree C L → Denotation E W → Prop
  /-- By Terminal Nodes, a leaf denotes what the lexicon gives it. -/
  | tn {g : Assignment E} {c : C} {w : L} {d : Denotation E W} (h : lex w = some d) :
      Denotes lex g (.terminal c w) d
  /-- By Non-Branching Nodes, a node denotes what its only daughter does. -/
  | nn {g : Assignment E} {c : C} {t : Tree C L} {d : Denotation E W} (h : Denotes lex g t d) :
      Denotes lex g (.node c (t :: [])) d
  /-- By Functional Application, a node whose left daughter is the function denotes its value. -/
  | faLeft {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {σ τ : Ty} {f : Ty.Domain E W (σ ⇒ τ)}
      {a : Ty.Domain E W σ} (h₁ : Denotes lex g t₁ ⟨σ ⇒ τ, f⟩) (h₂ : Denotes lex g t₂ ⟨σ, a⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨τ, f a⟩
  /-- By Functional Application, a node whose right daughter is the function denotes its value. -/
  | faRight {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {σ τ : Ty} {a : Ty.Domain E W σ}
      {f : Ty.Domain E W (σ ⇒ τ)} (h₁ : Denotes lex g t₁ ⟨σ, a⟩)
      (h₂ : Denotes lex g t₂ ⟨σ ⇒ τ, f⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨τ, f a⟩
  /-- By Predicate Modification, two sister predicates conjoin. -/
  | pm {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {P Q : Ty.Domain E W (.e ⇒ .t)}
      (h₁ : Denotes lex g t₁ ⟨.e ⇒ .t, P⟩) (h₂ : Denotes lex g t₂ ⟨.e ⇒ .t, Q⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨.e ⇒ .t, fun x ↦ P x ∧ Q x⟩
  /-- By the Traces and Pronouns Rule, a trace denotes the value of its index. -/
  | trace {g : Assignment E} {n : ℕ} {c : C} : Denotes lex g (.trace n c) ⟨.e, g n⟩
  /-- By Predicate Abstraction, a binder abstracts over its index in the body. -/
  | pa {g : Assignment E} {n : ℕ} {c : C} {body : Tree C L} {τ : Ty} {F : E → Ty.Domain E W τ}
      (h : ∀ x, Denotes lex (g[n ↦ x]) body ⟨τ, F x⟩) : Denotes lex g (.bind n c body) ⟨.e ⇒ τ, F⟩

/-- Where the book assigns a denotation, the engine at `M = Id` computes it. -/
theorem interp_of_denotes {lex : L → Option (Denotation E W)} {g : Assignment E}
    {t : Tree C L} {d : Denotation E W} (h : Denotes lex g t d) : interp lex g t = some d := by
  induction h with
  | tn h => rw [interp_terminal]; exact h
  | nn _ ih => exact ih
  | faLeft _ _ ih₁ ih₂ =>
    rw [interp_node_binary, ih₁, ih₂, Option.bind_some, Option.bind_some, Mode.combine?_fn_left]
    rfl
  | faRight _ _ ih₁ ih₂ =>
    rw [interp_node_binary, ih₁, ih₂, Option.bind_some, Option.bind_some, Mode.combine?_fn_right]
    rfl
  | pm _ _ ih₁ ih₂ =>
    rw [interp_node_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
      Mode.combine?_predicateModification]
    rfl
  | trace => rfl
  | @pa g n c body τ F _ ih =>
    have hg := ih (g n)
    rw [Function.update_eq_self] at hg
    simp only [interp_bind, hg, Option.bind_some]
    show (some ⟨.e ⇒ τ, fun x ↦ valueAt τ (F (g n)) (interp lex (g[n ↦ x]) body)⟩ :
      Option (Denotation E W)) = _
    congr 2
    funext x
    simp [ih x, valueAt]

/-- The book's rules are deterministic. -/
theorem Denotes.unique {lex : L → Option (Denotation E W)} {g : Assignment E} {t : Tree C L}
    {d d' : Denotation E W} (h : Denotes lex g t d) (h' : Denotes lex g t d') : d = d' :=
  Option.some.inj ((interp_of_denotes h).symm.trans (interp_of_denotes h'))

end Reference

section FregeanArticle

variable {E W : Type} {S : Sorts}

/-- The Fregean definite article (§4.4) maps a predicate true of exactly one individual to that
individual and is undefined elsewhere. -/
noncomputable def the : Ty.PDomain E W ((.e ⇒ .t) ⇒ .e) S :=
  fun P ↦ ⟨∃! x, True ∈ P x, fun h ↦ Classical.choose h⟩

/-- The definite article is defined exactly on the predicates true of one individual. -/
theorem the_dom (P : E →. Prop) : (the (W := W) (S := S) P).Dom ↔ ∃! x, True ∈ P x := Iff.rfl

/-- A total predicate is true of an individual where it holds. -/
@[simp] theorem true_mem_lift (P : E → Prop) (x : E) : True ∈ PFun.lift P x ↔ P x := by
  simp [PFun.lift, Part.mem_some_iff]

/-- On a total predicate true of exactly one individual, the definite article picks it. -/
theorem the_lift_eq_some {P : E → Prop} {a : E} (h : ∀ x, P x ↔ x = a) :
    the (W := W) (S := S) (PFun.lift P) = Part.some a := by
  have hu : ∃! x, True ∈ PFun.lift P x := ⟨a, (true_mem_lift P a).mpr ((h a).mpr rfl),
    fun y hy ↦ (h y).mp ((true_mem_lift P y).mp hy)⟩
  exact Part.eq_some_iff.mpr ⟨hu, (h _).mp ((true_mem_lift P _).mp (Classical.choose_spec hu).1)⟩

end FregeanArticle

/-! ### Definite descriptions

The Fregean article `the` is defined on predicates true of exactly one individual
(§4.4). In the toy model, with two students and one pizza, *the student* is undefined and *the
pizza* is not. -/

section DefiniteArticle

/-- The toy lexicon for the partial engine, which pairs the definite article with the fragment's
nouns, *sleeps* and names lifted to partial denotations. -/
noncomputable def partialLex : String → Option (PDenotation ToyEntity Unit)
  | "the" => some ⟨(.e ⇒ .t) ⇒ .e, Part.some the⟩
  | "student" => some ⟨.e ⇒ .t, Part.some (PFun.lift student)⟩
  | "pizza" => some ⟨.e ⇒ .t, Part.some (PFun.lift Toy.pizza)⟩
  | "sleeps" => some ⟨.e ⇒ .t, Part.some (PFun.lift Toy.sleeps)⟩
  | "John" => some ⟨.e, Part.some .john⟩
  | _ => none

/-- *The student* is a presupposition failure in the toy model, which has two students. -/
theorem the_student_fails :
    PresupFailure partialLex g₀ (.bin (.leaf "the") (.leaf "student")) := by
  refine ⟨⟨.e, the (PFun.lift student)⟩, ?_, fun ⟨x, _, huniq⟩ ↦ ?_⟩
  · rw [interpPartial_node_binary, interpPartial_terminal, interpPartial_terminal]
    exact Mode.combine?_evalPartial_fn_left the (PFun.lift student)
  have hj := huniq .john ((true_mem_lift _ _).mpr (.inl rfl))
  have hm := huniq .mary ((true_mem_lift _ _).mpr (.inr rfl))
  exact ToyEntity.noConfusion (hj.trans hm.symm)

/-- *The pizza* denotes the pizza, the toy model's unique one. -/
theorem the_pizza : interpPartial partialLex g₀ (.bin (.leaf "the") (.leaf "pizza")) =
    some ⟨.e, Part.some .pizza⟩ := by
  rw [interpPartial_node_binary, interpPartial_terminal, interpPartial_terminal]
  refine (Mode.combine?_evalPartial_fn_left the (PFun.lift Toy.pizza)).trans ?_
  rw [the_lift_eq_some (P := Toy.pizza) (a := .pizza) fun _ ↦ Iff.rfl]

/-- *The John*, the article applied to an individual rather than a predicate, is
uninterpretable, and the types alone decide it (§4.4.4). -/
theorem the_john_uninterpretable :
    Uninterpretable partialLex g₀ (.bin (.leaf "the") (.leaf "John")) := rfl

end DefiniteArticle

/-! ### The book's partial rules

Chapter 4's revision of the rules for partial denotations, which the partial engine extends. -/

section PartialReference

namespace Partial

variable {C L E W : Type}

/-- The book's revised interpretation relation, relative to a leaf interpretation and an
assignment. -/
inductive Denotes (lex : L → Option (PDenotation E W)) :
    Assignment E → Tree C L → PDenotation E W → Prop
  /-- By Terminal Nodes, a leaf denotes what the lexicon gives it. -/
  | tn {g : Assignment E} {c : C} {w : L} {d : PDenotation E W} (h : lex w = some d) :
      Denotes lex g (.terminal c w) d
  /-- By Non-Branching Nodes, a node denotes what its only daughter does. -/
  | nn {g : Assignment E} {c : C} {t : Tree C L} {d : PDenotation E W}
      (h : Denotes lex g t d) : Denotes lex g (.node c (t :: [])) d
  /-- By Functional Application, a node whose left daughter is the function denotes its value,
  defined or not. -/
  | faLeft {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {σ τ : Ty}
      {f : Ty.PDomain E W (σ ⇒ τ)} {a : Ty.PDomain E W σ}
      (h₁ : Denotes lex g t₁ ⟨σ ⇒ τ, Part.some f⟩) (h₂ : Denotes lex g t₂ ⟨σ, Part.some a⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨τ, f a⟩
  /-- By Functional Application, a node whose right daughter is the function denotes its value. -/
  | faRight {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {σ τ : Ty} {a : Ty.PDomain E W σ}
      {f : Ty.PDomain E W (σ ⇒ τ)} (h₁ : Denotes lex g t₁ ⟨σ, Part.some a⟩)
      (h₂ : Denotes lex g t₂ ⟨σ ⇒ τ, Part.some f⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨τ, f a⟩
  /-- By Predicate Modification, two sister predicates conjoin where both are defined. -/
  | pm {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {P Q : Ty.PDomain E W (.e ⇒ .t)}
      (h₁ : Denotes lex g t₁ ⟨.e ⇒ .t, Part.some P⟩)
      (h₂ : Denotes lex g t₂ ⟨.e ⇒ .t, Part.some Q⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: []))
        ⟨.e ⇒ .t, Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b⟩
  /-- By the Traces and Pronouns Rule, a trace denotes the value of its index. -/
  | trace {g : Assignment E} {n : ℕ} {c : C} : Denotes lex g (.trace n c) ⟨.e, Part.some (g n)⟩
  /-- By Predicate Abstraction, a binder abstracts over its index in the body, the abstract
  defined at an individual where the body has a defined value under the modified assignment. -/
  | pa {g : Assignment E} {n : ℕ} {c : C} {body : Tree C L} {τ : Ty}
      {F : E → Part (Ty.PDomain E W τ)} (h : ∀ x, Denotes lex (g[n ↦ x]) body ⟨τ, F x⟩) :
      Denotes lex g (.bind n c body) ⟨.e ⇒ τ, Part.some F⟩

/-- Where the book's revised rules assign a value, the partial engine computes it. -/
theorem interp_of_denotes {lex : L → Option (PDenotation E W)} {g : Assignment E}
    {t : Tree C L} {d : PDenotation E W} (h : Denotes lex g t d) :
    interpPartial lex g t = some d := by
  induction h with
  | tn h => rw [interpPartial_terminal]; exact h
  | nn _ ih => exact ih
  | faLeft _ _ ih₁ ih₂ =>
    rw [interpPartial_node_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
      Mode.combine?_evalPartial_fn_left]
  | faRight _ _ ih₁ ih₂ =>
    rw [interpPartial_node_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
      Mode.combine?_evalPartial_fn_right]
  | pm _ _ ih₁ ih₂ =>
    rw [interpPartial_node_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
      Mode.combine?_evalPartial_predicateModification]
  | trace => rfl
  | @pa g n c body τ F _ ih =>
    have hg := ih (g n)
    rw [Function.update_eq_self] at hg
    rw [interpPartial_bind, hg, Option.map_some]
    congr 3
    funext x
    simp [ih x, valueAtPartial]

/-- The book's revised rules are deterministic. -/
theorem Denotes.unique {lex : L → Option (PDenotation E W)} {g : Assignment E} {t : Tree C L}
    {d d' : PDenotation E W} (h : Denotes lex g t d) (h' : Denotes lex g t d') : d = d' :=
  Option.some.inj ((interp_of_denotes h).symm.trans (interp_of_denotes h'))

/-- *The pizza* denotes the pizza by the book's own rules. -/
theorem denotes_the_pizza :
    Denotes partialLex g₀ (.bin (.leaf "the") (.leaf "pizza")) ⟨.e, Part.some .pizza⟩ := by
  have h : Denotes partialLex g₀ (.bin (.leaf "the") (.leaf "pizza"))
      ⟨.e, the (PFun.lift Toy.pizza)⟩ :=
    .faLeft (σ := .e ⇒ .t) (τ := .e) (f := the) (a := PFun.lift Toy.pizza)
      (.tn rfl) (.tn rfl)
  rwa [the_lift_eq_some (P := Toy.pizza) (a := .pizza) fun _ ↦ Iff.rfl] at h

/-- Whatever value the book's rules assign *the student* is undefined. -/
theorem denotes_the_student {v : Part ToyEntity}
    (h : Denotes partialLex g₀ (.bin (.leaf "the") (.leaf "student")) ⟨.e, v⟩) : ¬ v.Dom := by
  obtain ⟨d, hd, hdom⟩ := the_student_fails
  cases Option.some.inj ((interp_of_denotes h).symm.trans hd)
  exact hdom

/-- The toy lexicon lifted entrywise never fails, since its entries are first order. -/
theorem toyLexicon_toPartial_noFailure (g : Assignment ToyEntity) (t : Tree Unit String) :
    ¬ PresupFailure (fun w ↦ (toyLexicon w).map Denotation.toPartial) g t :=
  not_presupFailure_map_toPartial (fun _ _ h ↦ by
    rcases toyLexicon_fst h with h | h | h <;> rw [h] <;> repeat constructor) g t

end Partial

end PartialReference

/-! ### Relative clauses

A relative clause gets no rule of its own (p. 87): Predicate Abstraction over its trace makes it
a predicate, which Predicate Modification intersects with the head noun (p. 88). The vacuous
complementizer is a non-branching node, and the engine's abstraction is the indexed rule of
§5.3.4. -/

section RelativeClause

/-- The subject relative `[CP who₁ [C̄ [S t₁ sleeps]]]` (p. 101). -/
def tree_whoSleeps : Tree Unit String :=
  .binder 1 (.node () (.bin (.tr 1) (.leaf "sleeps") :: []))

/-- The noun phrase `[NP student [CP who₁ [C̄ [S t₁ sleeps]]]]`, standing in for the book's
*house which is empty* (p. 88). -/
def tree_studentWhoSleeps : Tree Unit String :=
  .bin (.leaf "student") tree_whoSleeps

/-- The open sentence `[S John [VP sees t₁]]`. -/
def tree_johnSeesT : Tree Unit String :=
  .bin (.leaf "John") (.bin (.leaf "sees") (.tr 1))

/-- The object relative `[CP which₁ [C̄ [S John [VP sees t₁]]]]`, standing in for the book's
*which John abandoned t* (p. 96). -/
def tree_whichJohnSees : Tree Unit String :=
  .binder 1 (.node () (tree_johnSeesT :: []))

/-- The subject relative denotes what *sleeps* denotes, at every assignment (p. 101). -/
theorem interp_whoSleeps (g : Assignment ToyEntity) :
    interp toyLexicon g tree_whoSleeps = some ⟨.e ⇒ .t, Toy.sleeps⟩ := rfl

/-- The relative clause modifies its head intersectively, restrictive relatives being "just
another kind of intersective modifier" (p. 88). -/
theorem interp_studentWhoSleeps (g : Assignment ToyEntity) :
    interp toyLexicon g tree_studentWhoSleeps =
      some ⟨.e ⇒ .t, (Modifier.intersective student Toy.sleeps : ToyEntity → Prop)⟩ := rfl

/-- The noun phrase is a derivation in the book's rules, Predicate Modification over the noun and
the Predicate Abstraction of the clause. -/
theorem denotes_studentWhoSleeps (g : Assignment ToyEntity) :
    Denotes toyLexicon g tree_studentWhoSleeps ⟨.e ⇒ .t, fun x ↦ student x ∧ Toy.sleeps x⟩ :=
  .pm (.tn rfl) <| .pa (τ := .t) fun x ↦ .nn <|
    .faRight (lex := toyLexicon) (σ := .e) (τ := .t) (a := x) (f := Toy.sleeps) .trace (.tn rfl)

/-- The open sentence has a value only relative to an assignment (definition (9), p. 94). -/
theorem interp_johnSeesT (g : Assignment ToyEntity) :
    interp toyLexicon g tree_johnSeesT = some ⟨.t, Toy.sees (g 1) .john⟩ := rfl

/-- The open sentence has no assignment-independent value, since John sees Mary but not
himself. -/
theorem interp_johnSeesT_ne :
    interp toyLexicon (g₀[1 ↦ .mary]) tree_johnSeesT ≠ interp toyLexicon g₀ tree_johnSeesT := by
  simp only [interp_johnSeesT, Function.update_self, ne_eq, Option.some.injEq, Sigma.mk.inj_iff,
    heq_eq_eq, true_and]
  intro h
  rcases cast h (.inl ⟨rfl, rfl⟩) with ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

/-- The object relative denotes the property of being seen by John at every assignment, the value
of none of its subtrees. -/
theorem interp_whichJohnSees (g : Assignment ToyEntity) :
    interp toyLexicon g tree_whichJohnSees = some ⟨.e ⇒ .t, fun x ↦ Toy.sees x .john⟩ := rfl

/-- The book's proof for *which John abandoned t* (pp. 96-98) is a derivation in its rules, by
Predicate Abstraction, the vacuous complementizer, Functional Application twice and the Traces
Rule. -/
theorem denotes_whichJohnSees (g : Assignment ToyEntity) :
    Denotes toyLexicon g tree_whichJohnSees ⟨.e ⇒ .t, fun x ↦ Toy.sees x .john⟩ :=
  .pa (τ := .t) fun x ↦ .nn <|
    .faRight (lex := toyLexicon) (σ := .e) (τ := .t) (a := .john) (f := Toy.sees x) (.tn rfl) <|
      .faLeft (lex := toyLexicon) (σ := .e) (τ := .e ⇒ .t) (f := Toy.sees) (a := x) (.tn rfl)
        .trace

/-- *The student who sleeps* denotes John by the book's revised rules, the article applying to the
noun phrase that the relative clause restricts. -/
theorem Partial.denotes_the_student_who_sleeps :
    Partial.Denotes partialLex g₀ (.bin (.leaf "the") tree_studentWhoSleeps)
      ⟨.e, Part.some .john⟩ := by
  have h : Partial.Denotes partialLex g₀ (.bin (.leaf "the") tree_studentWhoSleeps)
      ⟨.e, the fun x ↦
        (PFun.lift student x).bind fun a ↦ (PFun.lift Toy.sleeps x).map fun b ↦ a ∧ b⟩ :=
    .faLeft (σ := .e ⇒ .t) (τ := .e) (.tn rfl) <| .pm (.tn rfl) <| .pa (τ := .t) fun x ↦ .nn <|
      .faRight (lex := partialLex) (σ := .e) (τ := .t) (a := x) (f := PFun.lift Toy.sleeps)
        .trace (.tn rfl)
  have hP : (fun x ↦ (PFun.lift student x).bind fun a ↦ (PFun.lift Toy.sleeps x).map (a ∧ ·)) =
      PFun.lift fun x ↦ student x ∧ Toy.sleeps x := by
    funext x; simp [PFun.lift]
  rwa [hP, the_lift_eq_some (P := fun x ↦ student x ∧ Toy.sleeps x) (a := .john)
    fun _ ↦ ⟨And.right, fun h ↦ h ▸ ⟨.inl rfl, rfl⟩⟩] at h

/-- *The student who sleeps* denotes John, though *the student* is a presupposition failure
(`the_student_fails`), since the restrictive relative narrows the article's domain to one student,
where a nonrestrictive one would leave the article applying to *student* alone (p. 88). -/
theorem the_student_who_sleeps :
    interpPartial partialLex g₀ (.bin (.leaf "the") tree_studentWhoSleeps) =
      some ⟨.e, Part.some .john⟩ :=
  Partial.interp_of_denotes Partial.denotes_the_student_who_sleeps

/-- Under the bracketing `[[the student] [who₁ [t₁ sleeps]]]` that §4.5 rejects, the definite
denotes a truth value, so a sentence with it as subject is uninterpretable (p. 83). -/
theorem det_noun_modifier_uninterpretable :
    Uninterpretable partialLex g₀
      (.bin (.bin (.bin (.leaf "the") (.leaf "student")) tree_whoSleeps) (.leaf "sleeps")) :=
  rfl

end RelativeClause

/-! ### Quantifier scope

Quantifier Raising (§7.3) leaves a trace and a binder index, so a raised quantifier takes the
abstracted predicate as its scope. The two QR trees of "every person sees some person" compute
its two scope readings. -/

/-- The surface-scope tree `[S [DP every person] [1 [S [DP some person] [2 [S t₁ [VP sees t₂]]]]]]`
has the reading ∀x[person(x) → ∃y[person(y) ∧ sees(x,y)]]. -/
def tree_surface : Tree Unit (QuantityWord ⊕ String) :=
  .bin
    (.bin (.leaf (.inl .every)) (.leaf (.inr "person")))
    (.binder 1
      (.bin
        (.bin (.leaf (.inl .some_)) (.leaf (.inr "person")))
        (.binder 2
          (.bin (.tr 1) (.bin (.leaf (.inr "sees")) (.tr 2))))))

/-- The inverse-scope tree `[S [DP some person] [2 [S [DP every person] [1 [S t₁ [VP sees t₂]]]]]]`
has the reading ∃y[person(y) ∧ ∀x[person(x) → sees(x,y)]]. -/
def tree_inverse : Tree Unit (QuantityWord ⊕ String) :=
  .bin
    (.bin (.leaf (.inl .some_)) (.leaf (.inr "person")))
    (.binder 2
      (.bin
        (.bin (.leaf (.inl .every)) (.leaf (.inr "person")))
        (.binder 1
          (.bin (.tr 1) (.bin (.leaf (.inr "sees")) (.tr 2))))))

/-- The surface-scope reading `∀ > ∃` puts `every` over `some`, with `x sees y`. -/
abbrev surfaceScopeProp : Prop :=
  surfaceScope every GQ.some person person fun x y ↦ Toy.sees y x

/-- The inverse-scope reading, `∃ > ∀`. -/
abbrev inverseScopeProp : Prop :=
  inverseScope every GQ.some person person fun x y ↦ Toy.sees y x

/-- Surface scope is true in the toy model, where John and Mary see each other. -/
theorem surface_scope_true : surfaceScopeProp := by
  rintro x (rfl | rfl)
  · exact ⟨.mary, .inr rfl, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨.john, .inl rfl, .inr ⟨rfl, rfl⟩⟩

/-- Inverse scope is false in the toy model, where no one sees themselves. -/
theorem inverse_scope_false : ¬inverseScopeProp := by
  rintro ⟨y, (rfl | rfl), hall⟩
  · exact nomatch hall .john (.inl rfl)
  · exact nomatch hall .mary (.inr rfl)

/-- The inverse reading entails the surface one, so a model can separate them only in the
direction the toy model does. -/
theorem inverse_entails_surface : inverseScopeProp → surfaceScopeProp :=
  iterate_every_some_of_some_every _ _ _

/-- On the surface-scope tree the engine computes the surface reading. -/
theorem interp_computes_surface :
    interp lex g₀ tree_surface = some ⟨Ty.t, surfaceScopeProp⟩ := rfl

/-- On the inverse-scope tree the engine computes the inverse reading. -/
theorem interp_computes_inverse :
    interp lex g₀ tree_inverse = some ⟨Ty.t, inverseScopeProp⟩ := rfl

/-- The two QR derivations interpret to different meanings. -/
theorem scope_ambiguity_computed : interp lex g₀ tree_surface ≠ interp lex g₀ tree_inverse := by
  rw [interp_computes_surface, interp_computes_inverse]
  intro h
  have : surfaceScopeProp = inverseScopeProp := by injection h with h'; injection h'
  exact inverse_scope_false (this ▸ surface_scope_true)

/-- The surface-scope reading is a derivation in the book's rules, Functional Application around
two Predicate Abstractions with the quantifier words as terminals. -/
theorem denotes_surface : Denotes lex g₀ tree_surface ⟨Ty.t, surfaceScopeProp⟩ := by
  show Denotes lex g₀ tree_surface
    ⟨Ty.t, every person fun x ↦ GQ.some person fun y ↦ Toy.sees y x⟩
  refine .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := .t) (f := every person) ?_
    (.pa (τ := .t) fun x ↦ ?_)
  · exact .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := (.e ⇒ .t) ⇒ .t) (f := every)
      (a := person) (.tn rfl) (.tn rfl)
  · refine .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := .t) (f := GQ.some person) ?_
      (.pa (τ := .t) fun y ↦ ?_)
    · exact .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := (.e ⇒ .t) ⇒ .t) (f := GQ.some)
        (a := person) (.tn rfl) (.tn rfl)
    · exact .faRight (lex := lex) (σ := .e) (τ := .t) (a := x) (f := Toy.sees y) .trace
        (.faLeft (lex := lex) (σ := .e) (τ := .e ⇒ .t) (f := Toy.sees) (a := y)
          (.tn rfl) .trace)

/-! ### Readings of the ambiguous lexicon

`Tree.readings` composes the words' available readings, one resolution per occurrence; the
study's leaf interpretation is one such resolution. -/

section Readings

/-- The words' available readings, the quantifier words through the terminals of theirs and
the toy fragment's words through the toy lexicon. -/
def lexReadings : QuantityWord ⊕ String → Set (Denotation ToyEntity Unit) :=
  Sum.elim (fun w ↦ terminals ⟦w⟧ ToyEntity Unit) fun s ↦ {d | toyLexicon s = some d}

/-- The study's leaf interpretation chooses among the available readings. -/
theorem lex_mem_lexReadings (w : QuantityWord ⊕ String) (d : Denotation ToyEntity Unit)
    (h : lex w = some d) : d ∈ lexReadings w := by
  cases w with
  | inl w => exact quantifierReading_mem h
  | inr s => exact h

/-- The surface-scope reading is among the readings of the surface tree. -/
theorem surfaceScopeProp_mem_readings :
    ⟨Ty.t, surfaceScopeProp⟩ ∈ Tree.readings lexReadings g₀ tree_surface :=
  Tree.interp_mem_readings lex_mem_lexReadings interp_computes_surface

end Readings

/-! ### Quantifiers in situ

In §7.2.1's alternative to movement the book's lexical rule gives each determiner an
object-position entry (`objectShift?`), and the flat tree composes by Functional Application
alone. -/

section InSitu

/-- The words' readings closed under the lexical rule, each quantifier word making its
object-position entry available beside its basic one. -/
def lexFlex (w : QuantityWord ⊕ String) : Set (Denotation ToyEntity Unit) :=
  lexReadings w ∪ objectShifts (lexReadings w)

/-- A resolution of the quantifier words, the words in `object` taking their object-position
entry and the others their basic one. -/
def resolve (object : QuantityWord → Prop) [DecidablePred object] :
    QuantityWord ⊕ String → Option (Denotation ToyEntity Unit) :=
  Sum.elim (fun w ↦ if object w then (quantifierReading w).bind objectShift?
    else quantifierReading w) toyLexicon

/-- Every resolution chooses among the readings the lexical rule makes available. -/
theorem resolve_mem_lexFlex (object : QuantityWord → Prop) [DecidablePred object]
    (w : QuantityWord ⊕ String) (d : Denotation ToyEntity Unit) (h : resolve object w = some d) :
    d ∈ lexFlex w := by
  cases w with
  | inl w =>
    simp only [resolve, Sum.elim_inl] at h
    split_ifs at h with hw
    · obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      exact .inr ⟨d₁, quantifierReading_mem h₁, h⟩
    · exact .inl (quantifierReading_mem h)
  | inr s => exact .inl h

/-- The book's in-situ tree on the toy fragment, `[S [DP every person] [VP sees [DP some
person]]]`, with no movement. -/
def tree_inSitu : Tree Unit (QuantityWord ⊕ String) :=
  .bin (.bin (.leaf (.inl .every)) (.leaf (.inr "person")))
    (.bin (.leaf (.inr "sees")) (.bin (.leaf (.inl .some_)) (.leaf (.inr "person"))))

/-- Under the book's subscripts, the object-position entry for *some* alone, the in-situ tree
composes by Functional Application alone to the surface-scope reading. -/
theorem interp_computes_inSitu :
    interp (resolve (· = .some_)) g₀ tree_inSitu = some ⟨Ty.t, surfaceScopeProp⟩ := rfl

/-- The in-situ and QR derivations compute the same reading. -/
theorem inSitu_eq_surface :
    interp (resolve (· = .some_)) g₀ tree_inSitu = interp lex g₀ tree_surface :=
  interp_computes_inSitu.trans interp_computes_surface.symm

/-- The surface-scope reading is among the readings of the flat tree under the lexical rule. -/
theorem surfaceScopeProp_mem_readings_inSitu :
    ⟨Ty.t, surfaceScopeProp⟩ ∈ Tree.readings lexFlex g₀ tree_inSitu :=
  Tree.interp_mem_readings (resolve_mem_lexFlex _) interp_computes_inSitu

/-- An object-position entry in subject position leaves its mother uninterpretable, `[S [DP
some person] [VP sleeps]]` with *some* resolved to its object-position entry. -/
theorem object_entry_in_subject_uninterpretable :
    interp (resolve (· = .some_)) g₀
      (.bin (.bin (.leaf (.inl .some_)) (.leaf (.inr "person"))) (.leaf (.inr "sleeps"))) =
      none := rfl

/-- A basic entry in object position is the type mismatch of §7.1 the rule repairs, `[S John
[VP sees [DP some person]]]` with every word resolved to its basic entry. -/
theorem basic_entry_in_object_uninterpretable :
    interp (resolve fun _ ↦ False) g₀ (.bin (.leaf (.inr "John"))
      (.bin (.leaf (.inr "sees")) (.bin (.leaf (.inl .some_)) (.leaf (.inr "person"))))) =
      none := rfl

end InSitu

/-! ### Logical forms and their readback

With the logical words, a quantifier-raised tree translates to its logical form, with the mode at
each node, and the logical form reads back to the first-order formula of its truth conditions. -/

section LogicalForm

open FirstOrder

/-- The English logical words translate to the logical first-order constants. -/
def Toy.logicalWords {L : Language} : String → Option ((ty : Ty) × FirstOrderConstant L ty)
  | "every" => some ⟨_, .every⟩
  | "some" => some ⟨_, .some⟩
  | "no" => some ⟨_, .no⟩
  | "not" => some ⟨_, .neg⟩
  | "and" => some ⟨_, .conj⟩
  | "or" => some ⟨_, .disj⟩
  | _ => none

/-- The toy vocabulary translates the toy content words and the logical words. -/
def toyVocabulary (s : String) : Option ((ty : Ty) × FirstOrderConstant toyLang ty) :=
  toyWords s <|> Toy.logicalWords s

/-- *Every student sleeps*, with the subject raised over the trace of index 1. -/
def everyStudentSleeps : Tree Unit String :=
  .bin (.bin (.leaf "every") (.leaf "student")) (.binder 1 (.bin (.tr 1) (.leaf "sleeps")))

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
example : Tree.translate toyVocabulary (.bin (.leaf "John") (.leaf "John") : Tree Unit String) =
    none := rfl

/-- In *every student who sleeps laughs* the relative clause abstracts over its trace and
intersects with the noun by predicate modification. -/
def everyStudentWhoSleepsLaughs : Tree Unit String :=
  .bin (.bin (.leaf "every") (.bin (.leaf "student") (.binder 2 (.bin (.tr 2) (.leaf "sleeps")))))
    (.binder 1 (.bin (.tr 1) (.leaf "laughs")))

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

end LogicalForm

end HeimKratzer1998
