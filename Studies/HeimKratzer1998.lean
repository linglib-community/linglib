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
quantifier scope (Chapter 7). For attitude reports (Chapter 12) the words that vary with the world
read one, after Bumford and Charlow, and Intensional Functional Application, which feeds *believes*
the intension of its complement, is [application mapped over that
reader](##propositions_maryBelievesJanIsLoyal), so that *Mary believes Jan is loyal* and *Jan is
loyal*, *Dick is deceitful* can be true while *Mary believes Dick is deceitful* is false. Read at
one world, a complement of *believes* is its truth value, and the verb's complement is a
nonextensional context exactly when the subject's beliefs leave open another world.

## Implementation notes

The toy fragment's words stand in for the book's: *student who sleeps* for *house which is
empty*, *every person sees some person* for "Some publisher offended every linguist". The type
`t` denotes in `Prop` (`Montague.Ty.Domain`), so the engines produce truth conditions as
propositions. In Chapter 12 *is* is the identity on predicates, the book's emptiness of *is*, and
(11d) is the falsity of (10) at the actual world, since the fragment has no negation.

## References

* [heim-kratzer-1998]
* [bumford-charlow-2026]
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
open scoped Denotes

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
    rw [interp_phrase_binary, ih₁, ih₂, Option.bind_some, Option.bind_some, Mode.combine?_fn_left]
    rfl
  | faRight _ _ ih₁ ih₂ =>
    rw [interp_phrase_binary, ih₁, ih₂, Option.bind_some, Option.bind_some, Mode.combine?_fn_right]
    rfl
  | pm _ _ ih₁ ih₂ =>
    rw [interp_phrase_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
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

theorem the_dom (P : E →. Prop) : (the (W := W) (S := S) P).Dom ↔ ∃! x, True ∈ P x := Iff.rfl

@[simp] theorem true_mem_lift (P : E → Prop) (x : E) : True ∈ PFun.lift P x ↔ P x := by
  simp [PFun.lift, Part.mem_some_iff]

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
  · rw [interpPartial_phrase_binary, interpPartial_terminal, interpPartial_terminal]
    exact Mode.combine?_evalPartial_fn_left the (PFun.lift student)
  have hj := huniq .john ((true_mem_lift _ _).mpr (.inl rfl))
  have hm := huniq .mary ((true_mem_lift _ _).mpr (.inr rfl))
  exact ToyEntity.noConfusion (hj.trans hm.symm)

/-- *The pizza* denotes the pizza, the toy model's unique one. -/
theorem the_pizza : interpPartial partialLex g₀ (.bin (.leaf "the") (.leaf "pizza")) =
    some ⟨.e, Part.some .pizza⟩ := by
  rw [interpPartial_phrase_binary, interpPartial_terminal, interpPartial_terminal]
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
    rw [interpPartial_phrase_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
      Mode.combine?_evalPartial_fn_left]
  | faRight _ _ ih₁ ih₂ =>
    rw [interpPartial_phrase_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
      Mode.combine?_evalPartial_fn_right]
  | pm _ _ ih₁ ih₂ =>
    rw [interpPartial_phrase_binary, ih₁, ih₂, Option.bind_some, Option.bind_some,
      Mode.combine?_evalPartial_predicateModification]
  | trace => rfl
  | @pa g n c body τ F _ ih =>
    have hg := ih (g n)
    rw [Function.update_eq_self] at hg
    rw [interpPartial_bind, hg, Option.map_some]
    congr 3
    funext x
    simp [ih x, valueAtPartial]

theorem Denotes.unique {lex : L → Option (PDenotation E W)} {g : Assignment E} {t : Tree C L}
    {d d' : PDenotation E W} (h : Denotes lex g t d) (h' : Denotes lex g t d') : d = d' :=
  Option.some.inj ((interp_of_denotes h).symm.trans (interp_of_denotes h'))

theorem denotes_the_pizza :
    Denotes partialLex g₀ (.bin (.leaf "the") (.leaf "pizza")) ⟨.e, Part.some .pizza⟩ := by
  have h : Denotes partialLex g₀ (.bin (.leaf "the") (.leaf "pizza"))
      ⟨.e, the (PFun.lift Toy.pizza)⟩ :=
    .faLeft (σ := .e ⇒ .t) (τ := .e) (f := the) (a := PFun.lift Toy.pizza)
      (.tn rfl) (.tn rfl)
  rwa [the_lift_eq_some (P := Toy.pizza) (a := .pizza) fun _ ↦ Iff.rfl] at h

theorem denotes_the_student {v : Part ToyEntity}
    (h : Denotes partialLex g₀ (.bin (.leaf "the") (.leaf "student")) ⟨.e, v⟩) : ¬ v.Dom := by
  obtain ⟨d, hd, hdom⟩ := the_student_fails
  cases Option.some.inj ((interp_of_denotes h).symm.trans hd)
  exact hdom

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

-- p. 101
theorem interp_whoSleeps (g : Assignment ToyEntity) :
    interp toyLexicon g tree_whoSleeps = some ⟨.e ⇒ .t, Toy.sleeps⟩ := rfl

/-- The relative clause modifies its head intersectively, restrictive relatives being "just
another kind of intersective modifier" (p. 88). -/
theorem interp_studentWhoSleeps (g : Assignment ToyEntity) :
    interp toyLexicon g tree_studentWhoSleeps =
      some ⟨.e ⇒ .t, (Modifier.intersective student Toy.sleeps : ToyEntity → Prop)⟩ := rfl

theorem denotes_studentWhoSleeps (g : Assignment ToyEntity) :
    Denotes toyLexicon g tree_studentWhoSleeps ⟨.e ⇒ .t, fun x ↦ student x ∧ Toy.sleeps x⟩ :=
  .pm (.tn rfl) <| .pa (τ := .t) fun x ↦ .nn <|
    .faRight (lex := toyLexicon) (σ := .e) (τ := .t) (a := x) (f := Toy.sleeps) .trace (.tn rfl)

-- (9), p. 94
theorem interp_johnSeesT (g : Assignment ToyEntity) :
    interp toyLexicon g tree_johnSeesT = some ⟨.t, Toy.sees (g 1) .john⟩ := rfl

theorem interp_johnSeesT_ne :
    interp toyLexicon (g₀[1 ↦ .mary]) tree_johnSeesT ≠ interp toyLexicon g₀ tree_johnSeesT := by
  simp only [interp_johnSeesT, Function.update_self, ne_eq, Option.some.injEq, Sigma.mk.inj_iff,
    heq_eq_eq, true_and]
  intro h
  rcases cast h (.inl ⟨rfl, rfl⟩) with ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

theorem interp_whichJohnSees (g : Assignment ToyEntity) :
    interp toyLexicon g tree_whichJohnSees = some ⟨.e ⇒ .t, fun x ↦ Toy.sees x .john⟩ := rfl

-- pp. 96-98
theorem denotes_whichJohnSees (g : Assignment ToyEntity) :
    Denotes toyLexicon g tree_whichJohnSees ⟨.e ⇒ .t, fun x ↦ Toy.sees x .john⟩ :=
  .pa (τ := .t) fun x ↦ .nn <|
    .faRight (lex := toyLexicon) (σ := .e) (τ := .t) (a := .john) (f := Toy.sees x) (.tn rfl) <|
      .faLeft (lex := toyLexicon) (σ := .e) (τ := .e ⇒ .t) (f := Toy.sees) (a := x) (.tn rfl)
        .trace

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

/-- *The student who sleeps* denotes John, though *the student* is a presupposition failure (p. 88).
-/
theorem the_student_who_sleeps :
    interpPartial partialLex g₀ (.bin (.leaf "the") tree_studentWhoSleeps) =
      some ⟨.e, Part.some .john⟩ :=
  Partial.interp_of_denotes Partial.denotes_the_student_who_sleeps

/-- Under the bracketing `[[the student] [who₁ [t₁ sleeps]]]` that §4.5 rejects, a sentence with the
definite as subject is uninterpretable (p. 83). -/
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

theorem surface_scope_true : surfaceScopeProp := by
  rintro x (rfl | rfl)
  · exact ⟨.mary, .inr rfl, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨.john, .inl rfl, .inr ⟨rfl, rfl⟩⟩

theorem inverse_scope_false : ¬inverseScopeProp := by
  rintro ⟨y, (rfl | rfl), hall⟩
  · exact nomatch hall .john (.inl rfl)
  · exact nomatch hall .mary (.inr rfl)

theorem inverse_entails_surface : inverseScopeProp → surfaceScopeProp :=
  iterate_every_some_of_some_every _ _ _

theorem interp_computes_surface :
    interp lex g₀ tree_surface = some ⟨Ty.t, surfaceScopeProp⟩ := rfl

theorem interp_computes_inverse :
    interp lex g₀ tree_inverse = some ⟨Ty.t, inverseScopeProp⟩ := rfl

/-- The two QR derivations interpret to different meanings. -/
theorem scope_ambiguity_computed : interp lex g₀ tree_surface ≠ interp lex g₀ tree_inverse := by
  rw [interp_computes_surface, interp_computes_inverse]
  intro h
  have : surfaceScopeProp = inverseScopeProp := by injection h with h'; injection h'
  exact inverse_scope_false (this ▸ surface_scope_true)

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

theorem lex_mem_lexReadings (w : QuantityWord ⊕ String) (d : Denotation ToyEntity Unit)
    (h : lex w = some d) : d ∈ lexReadings w := by
  cases w with
  | inl w => exact quantifierReading_mem h
  | inr s => exact h

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

theorem interp_computes_inSitu :
    interp (resolve (· = .some_)) g₀ tree_inSitu = some ⟨Ty.t, surfaceScopeProp⟩ := rfl

theorem inSitu_eq_surface :
    interp (resolve (· = .some_)) g₀ tree_inSitu = interp lex g₀ tree_surface :=
  interp_computes_inSitu.trans interp_computes_surface.symm

/-- The surface-scope reading is among the readings of the flat tree under the lexical rule. -/
theorem surfaceScopeProp_mem_readings_inSitu :
    ⟨Ty.t, surfaceScopeProp⟩ ∈ Tree.readings lexFlex g₀ tree_inSitu :=
  Tree.interp_mem_readings (resolve_mem_lexFlex _) interp_computes_inSitu

theorem object_entry_in_subject_uninterpretable :
    interp (resolve (· = .some_)) g₀
      (.bin (.bin (.leaf (.inl .some_)) (.leaf (.inr "person"))) (.leaf (.inr "sleeps"))) =
      none := rfl

-- §7.1
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
theorem translate_everyStudentSleeps :
    Tree.translate individualIndices toyVocabulary everyStudentSleeps =
      some ⟨.t, .comp .functionalLeft
        (.comp .functionalLeft (.const .every) (.const (.rel₁ studentRel)))
        (.lam 1 (.comp .functionalRight (.var 1) (.const (.rel₁ sleepRel))))⟩ :=
  rfl

open Toy FirstOrder.Language in
/-- The logical form of *every student sleeps* reads back to `∀ x, student x → sleeps x`. -/
example : ∃ u, Tree.translate individualIndices toyVocabulary everyStudentSleeps = some ⟨.t, u⟩ ∧
    u.toFormula = ((studentRel.boundedFormula₁ (var (.inr 0))).imp
      (sleepRel.boundedFormula₁ (var (.inr 0)))).all :=
  ⟨_, rfl, rfl⟩

/-- *John John* translates to nothing, since no mode combines two individuals. -/
example : Tree.translate individualIndices toyVocabulary
    (.bin (.leaf "John") (.leaf "John") : Tree Unit String) = none := rfl

/-- In *every student who sleeps laughs* the relative clause abstracts over its trace and
intersects with the noun by predicate modification. -/
def everyStudentWhoSleepsLaughs : Tree Unit String :=
  .bin (.bin (.leaf "every") (.bin (.leaf "student") (.binder 2 (.bin (.tr 2) (.leaf "sleeps")))))
    (.binder 1 (.bin (.tr 1) (.leaf "laughs")))

open Toy FirstOrder.Language in
/-- The relative clause reads back as a conjunct of the restrictor, in
`∀ x, student x ∧ sleeps x → laughs x`. -/
example : ∃ u,
    Tree.translate individualIndices toyVocabulary everyStudentWhoSleepsLaughs = some ⟨.t, u⟩ ∧
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

/-! ### Intensional semantics (Chapter 12)

The interpretation function depends on a world as well as an assignment, predicates vary with
the world, and an attitude verb is necessity along what its subject believes, knows or hopes,
taking a proposition of type `⟨s,t⟩`. Typed as computations that read a world, the worldly words
compose by application mapped over that reader, and a report has several derivations, among them
the one Intensional Functional Application gives. -/

section Intensional

open ModalLogic SetRel

variable {E W : Type} (loyal deceitful : W → E → Prop) (believes : E → SetRel W W)
  (mary jan dick : E)

/-- The fragment's words, those that vary with the world typed as computations that read one
([bumford-charlow-2026]): names are individuals, *is* is empty, *loyal* and *deceitful* read a
world for a property, and *believes* reads one for necessity along what its subject believes, a
relation between a proposition, itself read off a world, and an individual. -/
def lexicon : String → Option (Σ ty, Ty.Domain E W ty)
  | "Mary" => some ⟨.e, mary⟩
  | "Jan" => some ⟨.e, jan⟩
  | "Dick" => some ⟨.e, dick⟩
  | "is" => some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t, fun P ↦ P⟩
  | "loyal" => some ⟨.comp (.reader .s) (.e ⇒ .t), fun w x ↦ loyal w x⟩
  | "deceitful" => some ⟨.comp (.reader .s) (.e ⇒ .t), fun w x ↦ deceitful w x⟩
  | "believes" => some ⟨.comp (.reader .s) (.comp (.reader .s) .t ⇒ .e ⇒ .t),
      fun w p x ↦ □[believes x] p w⟩
  | _ => none

/-- *Jan is loyal*. -/
def janIsLoyal : Tree Unit String := .bin (.leaf "Jan") (.bin (.leaf "is") (.leaf "loyal"))

/-- *Dick is deceitful*. -/
def dickIsDeceitful : Tree Unit String :=
  .bin (.leaf "Dick") (.bin (.leaf "is") (.leaf "deceitful"))

/-- *Mary believes Jan is loyal*. -/
def maryBelievesJanIsLoyal : Tree Unit String :=
  .bin (.leaf "Mary") (.bin (.leaf "believes") janIsLoyal)

/-- *Mary believes Dick is deceitful*. -/
def maryBelievesDickIsDeceitful : Tree Unit String :=
  .bin (.leaf "Mary") (.bin (.leaf "believes") dickIsDeceitful)

/-- The propositions that the derivations of a tree from `lexicon` denote. -/
def propositions (g : Assignment E) (t : Tree Unit String) : Set (Denotation E W) :=
  {d | d ∈ ((Tree.translations individualIndices (lexicon loyal deceitful believes mary jan dick)
    t).filter (·.1 = .comp (.reader .s) .t)).map fun d ↦ ⟨d.1, d.2.eval (fun c ↦ c) g⟩}

theorem propositions_janIsLoyal (g : Assignment E) :
    propositions loyal deceitful believes mary jan dick g janIsLoyal =
      {⟨.comp (.reader .s) .t, fun w ↦ loyal w jan⟩} := by
  ext d
  simp [propositions, Tree.translations, janIsLoyal, lexicon, Ty.modes, Ty.mode?,
    Mode.functionalLeft?, Mode.functionalRight?, Mode.predicateModification?,
    Mode.eventIdentification?, Eff.map, Mode.join?]

theorem propositions_dickIsDeceitful (g : Assignment E) :
    propositions loyal deceitful believes mary jan dick g dickIsDeceitful =
      {⟨.comp (.reader .s) .t, fun w ↦ deceitful w dick⟩} := by
  ext d
  simp [propositions, Tree.translations, dickIsDeceitful, lexicon, Ty.modes, Ty.mode?,
    Mode.functionalLeft?, Mode.functionalRight?, Mode.predicateModification?,
    Mode.eventIdentification?, Eff.map, Mode.join?]

/-- Intensional Functional Application is application mapped over the reader of worlds: the
derivations of *Mary believes Jan is loyal* denote two propositions, and the one mapping
application over the verb's reader is true at `w` iff Jan is loyal at every world compatible with
what Mary believes in `w` (8), p. 308. The others, by structured application or by joining a
layered derivation, give the verb the constant intension of the complement's truth value at `w`,
the report of an extensional semantics (p. 300). -/
theorem propositions_maryBelievesJanIsLoyal (g : Assignment E) :
    propositions loyal deceitful believes mary jan dick g maryBelievesJanIsLoyal =
      {⟨.comp (.reader .s) .t, fun w ↦ □[believes mary] (loyal · jan) w⟩,
       ⟨.comp (.reader .s) .t, fun w ↦ □[believes mary] (fun _ ↦ loyal w jan) w⟩} := by
  ext d
  simp [propositions, Tree.translations, maryBelievesJanIsLoyal, janIsLoyal, lexicon, Ty.modes,
    Ty.mode?, Mode.functionalLeft?, Mode.functionalRight?, Mode.predicateModification?,
    Mode.eventIdentification?, Eff.map, Eff.seq, Eff.pure, Mode.join?, Eff.join]
  tauto

theorem propositions_maryBelievesDickIsDeceitful (g : Assignment E) :
    propositions loyal deceitful believes mary jan dick g maryBelievesDickIsDeceitful =
      {⟨.comp (.reader .s) .t, fun w ↦ □[believes mary] (deceitful · dick) w⟩,
       ⟨.comp (.reader .s) .t, fun w ↦ □[believes mary] (fun _ ↦ deceitful w dick) w⟩} := by
  ext d
  simp [propositions, Tree.translations, maryBelievesDickIsDeceitful, dickIsDeceitful, lexicon,
    Ty.modes, Ty.mode?, Mode.functionalLeft?, Mode.functionalRight?, Mode.predicateModification?,
    Mode.eventIdentification?, Eff.map, Eff.seq, Eff.pure, Mode.join?, Eff.join]
  tauto

-- p. 300: the other derivations layer the two readers, and read at one world twice each is the
-- report about the constant intension of the complement's truth value there
theorem translations_maryBelievesJanIsLoyal_layered (g : Assignment E) :
    ((Tree.translations individualIndices (lexicon loyal deceitful believes mary jan dick)
      maryBelievesJanIsLoyal).filter (·.1 = .comp (.reader .s) (.comp (.reader .s) .t))).map
        (fun d ↦ (⟨d.1, d.2.eval (fun c ↦ c) g⟩ : Denotation E W)) =
      [⟨.comp (.reader .s) (.comp (.reader .s) .t),
        fun u v ↦ □[believes mary] (fun _ ↦ loyal u jan) v⟩,
       ⟨.comp (.reader .s) (.comp (.reader .s) .t),
        fun v u ↦ □[believes mary] (fun _ ↦ loyal u jan) v⟩,
       ⟨.comp (.reader .s) (.comp (.reader .s) .t),
        fun v u ↦ □[believes mary] (fun _ ↦ loyal u jan) v⟩] := by
  simp [Tree.translations, maryBelievesJanIsLoyal, janIsLoyal, lexicon, Ty.modes, Ty.mode?,
    Mode.functionalLeft?, Mode.functionalRight?, Mode.predicateModification?,
    Mode.eventIdentification?, Eff.map, Eff.pure, Mode.join?]

/-- The lexicon read at the world `w`: a word that reads a world gives its value there. -/
def lexiconAt (w : W) (s : String) : Option (Σ ty, Ty.Domain E W ty) :=
  (lexicon loyal deceitful believes mary jan dick s).map fun
    | ⟨.comp (.reader .s) ty, x⟩ => ⟨ty, x w⟩
    | d => d

-- p. 300: read at one world, a complement of *believes* is its truth value, and the one
-- derivation, by Unit Right, gives the verb the constant intension of that truth value, so two
-- true complements make the reports agree
theorem translations_lexiconAt_maryBelievesJanIsLoyal (w : W) (g : Assignment E) :
    (Tree.translations individualIndices (lexiconAt loyal deceitful believes mary jan dick w)
      maryBelievesJanIsLoyal).map (fun d ↦ (⟨d.1, d.2.eval (fun c ↦ c) g⟩ : Denotation E W)) =
      [⟨.t, □[believes mary] (fun _ ↦ loyal w jan) w⟩] := by
  simp [Tree.translations, maryBelievesJanIsLoyal, janIsLoyal, lexiconAt, lexicon, Ty.modes,
    Ty.mode?, Mode.functionalLeft?, Mode.functionalRight?, Mode.predicateModification?,
    Mode.eventIdentification?, Eff.pure, Mode.join?]

/-- An attitude verb's complement is a nonextensional context at `w` exactly when the subject's
attitude at `w` leaves open a world other than `w`, so the truth value of the complement fixes the
report only for a subject who rules out every other world (p. 300). -/
theorem believes_isExtensionalAt_iff {x : E} {w : W} :
    Montague.IsExtensionalAt (fun p w' ↦ □[believes x] p w') w ↔ ∀ v, w ~[believes x] v → v = w :=
  Montague.isExtensionalAt_box_iff

/-- The two worlds of the model for (11). -/
inductive Ch12World | actual | other

/-- The individuals of the model for (11). -/
inductive Ch12Person | mary | jan | dick

/-- (11), p. 309: Jan is loyal and Dick deceitful at the actual world, Mary believes that Jan is
loyal, and she does not believe that Dick is deceitful, since her beliefs leave open a world where
he is not. The report about the constant intension of the complement's truth value is true of
both, as p. 300 predicts of an extensional semantics. -/
theorem janIsLoyal_dickIsDeceitful_maryBelieves (g : Assignment Ch12Person) :
    let props := propositions (W := Ch12World) (fun _ x ↦ x = .jan)
      (fun w x ↦ w = .actual ∧ x = .dick) (fun _ ↦ Set.univ) .mary .jan .dick g
    let prop (p : Ch12World → Prop) : Denotation Ch12Person Ch12World :=
      ⟨.comp (.reader .s) .t, p⟩
    (∃ p, props janIsLoyal = {prop p} ∧ p .actual) ∧
      (∃ p, props dickIsDeceitful = {prop p} ∧ p .actual) ∧
      (∃ p q, props maryBelievesJanIsLoyal = {prop p, prop q} ∧ p .actual ∧ q .actual) ∧
      ∃ p q, props maryBelievesDickIsDeceitful = {prop p, prop q} ∧ ¬ p .actual ∧ q .actual :=
  ⟨⟨_, propositions_janIsLoyal .., rfl⟩, ⟨_, propositions_dickIsDeceitful .., rfl, rfl⟩,
    ⟨_, _, propositions_maryBelievesJanIsLoyal .., fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩,
    ⟨_, _, propositions_maryBelievesDickIsDeceitful .., (fun h ↦ nomatch (h .other trivial).1),
      fun _ _ ↦ ⟨rfl, rfl⟩⟩⟩

end Intensional

end HeimKratzer1998
