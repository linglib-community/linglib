module

public import Linglib.Data.Examples.Gutzmann2015
public import Linglib.Fragments.German.Particles
public import Linglib.Fragments.German.WordOrder

/-!
# Gutzmann (2015): Use-Conditional Meaning

This file formalizes the logic `L_TU` of [gutzmann-2015], chapter 4, and its two case studies,
sentence mood (chapter 5) and German modal particles (chapter 6). An expression of `L_TU` has
three dimensions, truth-conditional content, active use-conditional content, and the completed
use-conditional propositions; multidimensional application (4.46) applies functions in the first
two and merges the third, and use-conditional elimination (4.54) stores a completed second
dimension in the third, `Expr.app` and `Expr.elim`. The lexical extension rules (4.55), (4.56),
and (4.67) build three-dimensional entries from one-dimensional ones, giving a use-conditional
item an identity function as its truth-conditional dimension, `Expr.ofModifier`. The principle
of non-interaction (4.28) is then a theorem about every derivation, `Deriv.eval_t`: its
truth-conditional dimension is computed from the lexical items' first dimensions alone. Sentence
mood follows Truckenbrodt's decomposition into a deontic operator (5.85), present in every
matrix clause by the root rule (5.43), an epistemic modifier of it (5.91), present where a
[±wh] feature is visible at LF (5.41), and the hearer knowledge condition (5.99) of
v2-interrogatives; the German clause types compose as in (5.82), (5.93), and (5.100),
`ClauseType.mood`, so every clause's truth conditions are its content, its use conditions
are the deontic attitude, and a v2-interrogative differs from a vl-interrogative exactly by
hearer knowledge, the Cuban cigar scenario (5.36). Of the modal particles, *wohl* modifies the
epistemic operator (6.103), so its exclusion from imperatives and root *dass*-clauses is a type
mismatch: no derivation over their lexicon reaches the epistemic type, `Derivable`, and the
book's *wohl* examples are acceptable exactly where one does, `wohl_rows`; *ja* (6.122) and *denn*
(6.133) compose with any mood, and their use conditions in the excluded clause types, (6.129)
and (6.142), are ones the book argues no rational speaker holds. The book's examples are the
rows of `Data.Examples.Gutzmann2015`.

Truckenbrodt's five clause types are read off the library's clause cells, `ClauseType.ofCell`:
the finite verb moves to C in a root declarative or interrogative, while a *dass*-clause or a
deliberative *ob*- or wh-question used as a root utterance, Evans's insubordination, keeps it
last, and the imperative stands apart, (5.39). On the cells both classify, Truckenbrodt's verb
movement is the verb-second requirement of `German.verbSecond`, `verbInC_iff_required`; the
sentence types in which Durrell licenses *wohl* all have a clause type carrying the epistemic
modifier, `wohl_licensed_hasEpistemic`; and where Durrell excludes a modal particle from a cell
the book's row there is unacceptable, `excluded_rows`.

## Implementation notes

The type system (4.45) is taken at the propositional fragment: `t` is the type of propositions,
the book's `⟨s,t⟩`, and entities are omitted, so the typology of chapter 2 and the
expressive-modification examples of chapter 4 are not formalized. The deontic and epistemic
operators quantify over contextually suitable attitude predicates (5.84), (5.90), which a
`MoodModel` supplies together with the hearer knowledge, common knowledge, assumption, and
reason predicates the particles' lexical entries use. The rationality step that rules out *ja*
in interrogatives and *denn* outside v2-interrogatives (section 6.5.2) is not a theorem of the
logic, so their use conditions are derived and the restriction is left to the rows.

## References

* [gutzmann-2015]
* [potts-2005]
* [kaplan-1999]
* [durrell-2011]
* [evans-2007]
-/

@[expose] public section

namespace Gutzmann2015

open Clause (SentenceType EmbeddingContext)

/-- The German clause types of chapter 5, Truckenbrodt's, told apart by the position of the
finite verb and by the complementizer: root *dass*-clauses with the verb last, v2-declaratives,
v2-interrogatives with the finite verb in C, vl-interrogatives with the verb last, and
imperatives. -/
inductive ClauseType where
  | dassVL
  | v2Declarative
  | v2Interrogative
  | vlInterrogative
  | imperative
  deriving DecidableEq, Repr, Fintype

/-- The clause type of a cell. The finite verb moves to C in a root declarative or
interrogative, a *dass*-clause or an interrogative used as a root utterance keeps it last, and
the imperative stands apart. -/
def ClauseType.ofCell : SentenceType → EmbeddingContext → Option ClauseType
  | .declarative, .matrix => some .v2Declarative
  | .polar, .matrix | .alternative, .matrix | .constituent, .matrix => some .v2Interrogative
  | .imperative, .matrix => some .imperative
  | .declarative, .insubordinated => some .dassVL
  | .polar, .insubordinated | .alternative, .insubordinated | .constituent, .insubordinated =>
    some .vlInterrogative
  | _, _ => none

/-- The finite verb has moved to C, (5.39), in the v2 types and in the imperative. -/
def ClauseType.VerbInC : ClauseType → Prop
  | .v2Declarative | .v2Interrogative | .imperative => True
  | .dassVL | .vlInterrogative => False

instance : DecidablePred ClauseType.VerbInC
  | .v2Declarative | .v2Interrogative | .imperative => isTrue trivial
  | .dassVL | .vlInterrogative => isFalse id

/-- On the cells both classify, imperatives apart as in (5.39), Truckenbrodt's verb movement is
the verb-second requirement of the German fragment. -/
theorem verbInC_iff_required :
    ∀ t e, t ≠ .imperative → (t, e) ∈ German.verbSecond.recorded →
      ∀ ct ∈ ClauseType.ofCell t e, (ct.VerbInC ↔ (t, e) ∈ German.verbSecond.required) := by
  decide

/-- The cell a row records, a sentence type in a matrix or insubordinated context. -/
def cellOf (row : Datum) : Option (SentenceType × EmbeddingContext) :=
  (row.parse? "sentenceType" [("declarative", .declarative), ("polar", .polar),
    ("constituent", .constituent), ("imperative", .imperative)]).bind fun t ↦
    (row.parse? "embedding" [("matrix", .matrix), ("insubordinated", .insubordinated)]).map
      (t, ·)

/-- A clause type has the epistemic modifier of the deontic operator where a [±wh] feature is
visible at LF (5.41): in every clause type but root *dass*-clauses and imperatives. -/
def ClauseType.HasEpistemic : ClauseType → Prop
  | .dassVL | .imperative => False
  | _ => True

instance : DecidablePred ClauseType.HasEpistemic := fun ct ↦ by
  cases ct <;> unfold ClauseType.HasEpistemic <;> infer_instance

/-- Every sentence type in which Durrell licenses *wohl* has a clause type carrying the
epistemic modifier that *wohl* takes, (6.103). -/
theorem wohl_licensed_hasEpistemic :
    ∀ t e, (t, e) ∈ German.Particles.wohl.distribution.possible →
      ∀ ct ∈ ClauseType.ofCell t e, ct.HasEpistemic := by
  decide

universe u

/-! ### The logic `L_TU`, chapter 4 -/

/-- (4.45) at the propositional fragment: propositions, use-conditional propositions, and
function types. -/
inductive UCType
  | t
  | u
  | func (σ τ : UCType)
  deriving DecidableEq

namespace UCType

/-- (4.45b) and (4.45e): a type is use-conditional when it is `u` or a function into a
use-conditional type. -/
def IsUC : UCType → Prop
  | .u => True
  | .func _ τ => τ.IsUC
  | .t => False

instance decIsUC : DecidablePred IsUC
  | .u => isTrue trivial
  | .t => isFalse id
  | .func _ τ => decIsUC τ

/-- (4.66): the `n`-th level modifier type on `α`. -/
def modifier (α : UCType) : ℕ → UCType
  | 0 => α
  | n + 1 => func (modifier α n) (modifier α n)

@[simp] theorem modifier_zero (α : UCType) : modifier α 0 = α := rfl

@[simp] theorem modifier_succ (α : UCType) (n : ℕ) :
    modifier α (n + 1) = func (modifier α n) (modifier α n) := rfl

/-- The denotation of a type: propositions are sets of worlds, use-conditional propositions
sets of contexts. -/
def Denote (W C : Type u) : UCType → Type u
  | .t => W → Prop
  | .u => C → Prop
  | .func σ τ => Denote W C σ → Denote W C τ

end UCType

open UCType

variable {W C : Type u}

/-- A three-dimensional expression: a truth-conditional dimension of type `σ`, an active
use-conditional dimension of type `ρ`, and the completed use-conditional propositions. -/
structure Expr (W C : Type u) (σ ρ : UCType) where
  t : Denote W C σ
  s : Denote W C ρ
  u : C → Prop

namespace Expr

variable {σ τ ρ ν : UCType}

/-- (4.46): multidimensional application, application in the first two dimensions and merging
in the third. -/
def app (α : Expr W C (func σ τ) (func ρ ν)) (β : Expr W C σ ρ) : Expr W C τ ν :=
  ⟨α.t β.t, α.s β.s, λ c => α.u c ∧ β.u c⟩

/-- (4.54): unary use-conditional elimination. Once the active dimension is a use-conditional
proposition it is merged into the third, and the second becomes a copy of the first. -/
def elim (α : Expr W C σ .u) : Expr W C σ σ := ⟨α.t, α.t, λ c => α.u c ∧ α.s c⟩

/-- (4.55): a truth-conditional item is copied into the second dimension, with the neutral
third. -/
def ofTC (a : Denote W C σ) : Expr W C σ σ := ⟨a, a, λ _ => True⟩

/-- (4.56) and (4.67): an `n`-th level use-conditional modifier on `⟨σ, τ⟩` receives the
identity on the `n`-th level modifier type on `σ` as its truth-conditional dimension; at
`n = 0` this is the extension of a functional expletive use-conditional item. -/
def ofModifier (n : ℕ) (α : Denote W C (modifier (func σ τ) n)) :
    Expr W C (modifier σ (n + 1)) (modifier (func σ τ) n) :=
  ⟨λ x => x, α, λ _ => True⟩

end Expr

/-- A derivation in `L_TU`: lexical items composed by multidimensional application and
use-conditional elimination. -/
inductive Deriv (W C : Type u) : UCType → UCType → Type u
  | lex {σ ρ : UCType} : Expr W C σ ρ → Deriv W C σ ρ
  | app {σ τ ρ ν : UCType} : Deriv W C (func σ τ) (func ρ ν) → Deriv W C σ ρ → Deriv W C τ ν
  | elim {σ : UCType} : Deriv W C σ .u → Deriv W C σ σ

namespace Deriv

/-- The three-dimensional meaning of a derivation. -/
def eval : {σ ρ : UCType} → Deriv W C σ ρ → Expr W C σ ρ
  | _, _, .lex x => x
  | _, _, .app f a => f.eval.app a.eval
  | _, _, .elim d => d.eval.elim

/-- The truth-conditional dimension computed from the lexical items' first dimensions alone. -/
def truthShadow : {σ ρ : UCType} → Deriv W C σ ρ → Denote W C σ
  | _, _, .lex x => x.t
  | _, _, .app f a => f.truthShadow a.truthShadow
  | _, _, .elim d => d.truthShadow

/-- Every derivation's truth-conditional dimension depends only on its lexical items'
truth-conditional dimensions (4.28). -/
theorem eval_t {σ ρ : UCType} (d : Deriv W C σ ρ) : d.eval.t = d.truthShadow := by
  induction d with
  | lex x => rfl
  | app f a ihf iha => simp only [eval, Expr.app, truthShadow, ihf, iha]
  | elim d ih => simp only [eval, Expr.elim, truthShadow, ih]

end Deriv

/-! ### Sentence mood, chapter 5 -/

/-- The context-dependent attitudes the sentence mood operators and modal particles quantify
over: the world of the context, the deontic speaker predicates suitable for a proposition
(5.84), the epistemic predicates suitable at a world (5.90), whether the addressee knows
whether a proposition holds (5.99), the speaker's belief that it is common knowledge or
verifiable (6.122), the assumption operator of *wohl* (6.110), the common ground, and the
proposition that one proposition is the speaker's reason to ask another (6.133). -/
structure MoodModel (W C : Type u) where
  world : C → W
  deonticFor : C → (W → Prop) → Set ((W → Prop) → W → Prop)
  episFor : W → (W → Prop) → Set ((W → Prop) → W → Prop)
  knowsWhether : C → (W → Prop) → Prop
  commonKnowledge : C → (W → Prop) → Prop
  assume : (W → Prop) → W → Prop
  commonGround : C → Set (W → Prop)
  reasonToAsk : (W → Prop) → (W → Prop) → W → Prop

variable (M : MoodModel W C)

/-- (5.85): the deontic operator. Some contextually suitable deontic speaker predicate holds of
the proposition at the world of the context. -/
def deont : Denote W C (func .t .u) := λ p c => ∃ d ∈ M.deonticFor c p, d p (M.world c)

/-- (5.90): the epistemic predicate, some contextually suitable epistemic attitude toward the
proposition at a world. -/
def epis : Denote W C (func .t .t) := λ p w => ∃ e ∈ M.episFor w p, e p w

/-- (5.91): the epistemic sentence mood operator, a modifier feeding the epistemically embedded
proposition to a mood operator. -/
def E : Denote W C (modifier (func .t .u) 1) := λ D p => D (epis M p)

/-- (5.99): hearer knowledge, a functional expletive item. -/
def hknow : Denote W C (func .t .u) := λ p c => M.knowsWhether c p

/-- The propositional content as a lexical item, (4.55). -/
def prop (p : W → Prop) : Deriv W C .t .t := .lex (Expr.ofTC p)

/-- (5.82): the mood of a root dass-clause and of an imperative, the deontic operator alone. -/
def deonticOnly (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.lex (Expr.ofModifier 0 (deont M))) (prop p))

/-- (5.93): the mood of a v2-declarative and of a vl-interrogative: the epistemic modifier
applies to the deontic operator, which takes the content. -/
def deonticEpistemic (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.app (.lex (Expr.ofModifier 1 (E M))) (.lex (Expr.ofModifier 0 (deont M))))
    (prop p))

/-- (5.100): the mood of a v2-interrogative adds the free-floating hearer knowledge
condition. -/
def v2InterrogativeMood (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.app (.lex (Expr.ofModifier 1 (E M))) (.lex (Expr.ofModifier 0 (deont M))))
    (.elim (.app (.lex (Expr.ofModifier 0 (hknow M))) (prop p))))

/-- Chapter 5's compositions for the German clause types: dass-VL clauses and imperatives have
the deontic operator alone, since [−wh] on the meaningless *dass* is invisible at LF (5.41) and
imperatives carry no visible feature; declaratives and vl-interrogatives the epistemically
modified deontic operator; v2-interrogatives the hearer knowledge condition as well. -/
def ClauseType.mood : ClauseType → (W → Prop) → Deriv W C .t .t
  | .dassVL | .imperative => deonticOnly M
  | .v2Declarative | .vlInterrogative => deonticEpistemic M
  | .v2Interrogative => v2InterrogativeMood M

variable {M} {p : W → Prop} {c : C}

/-- (5.83a) and (5.94): the truth conditions of every clause type are its content. -/
theorem mood_t (ct : ClauseType) : (ct.mood M p).eval.t = p := by
  cases ct <;> rfl

/-- (5.83b): a root dass-clause or imperative is felicitous when the speaker holds a suitable
deontic attitude toward its content. -/
theorem deonticOnly_u : (deonticOnly M p).eval.u c ↔ deont M p c := by
  simp [deonticOnly, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC, prop]

/-- (5.95) and (5.96): a v2-declarative or vl-interrogative is felicitous when the speaker holds
a deontic attitude toward the epistemically embedded content. -/
theorem deonticEpistemic_u : (deonticEpistemic M p).eval.u c ↔ deont M (epis M p) c := by
  simp [deonticEpistemic, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC, prop, E]

/-- (5.100): a v2-interrogative adds that the addressee knows whether the content holds. -/
theorem v2InterrogativeMood_u :
    (v2InterrogativeMood M p).eval.u c ↔ M.knowsWhether c p ∧ deont M (epis M p) c := by
  simp [v2InterrogativeMood, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC, prop,
    E, hknow]

/-- (5.43), the root rule: the use conditions of every clause type include a deontic attitude
of the speaker. -/
theorem exists_deont_of_mood_u (ct : ClauseType) (h : (ct.mood M p).eval.u c) :
    ∃ q, deont M q c := by
  cases ct
  · exact ⟨p, deonticOnly_u.1 h⟩
  · exact ⟨_, deonticEpistemic_u.1 h⟩
  · exact ⟨_, (v2InterrogativeMood_u.1 h).2⟩
  · exact ⟨_, deonticEpistemic_u.1 h⟩
  · exact ⟨p, deonticOnly_u.1 h⟩

/-- (5.36), the Cuban cigar scenario: a v2-interrogative is felicitous exactly when the
vl-interrogative with the same content is and the addressee knows the answer. -/
theorem v2Interrogative_mood_u_iff :
    (ClauseType.v2Interrogative.mood M p).eval.u c ↔
      (ClauseType.vlInterrogative.mood M p).eval.u c ∧ M.knowsWhether c p := by
  simp only [ClauseType.mood, v2InterrogativeMood_u, deonticEpistemic_u]
  exact and_comm

/-! ### Modal particles, chapter 6 -/

variable (M)

/-- (6.122): *ja* flags its content as common knowledge or verifiable on the spot. -/
def jaEntry : Denote W C (func .t .u) := λ p c => M.commonKnowledge c p

/-- (6.103) and (6.110): *wohl* modifies the epistemic operator, embedding the content under
the speaker's or hearer's assumption. -/
def wohlEntry : Denote W C (modifier (func .t .u) 2) := λ E D p => E D (M.assume p)

/-- (6.131) and (6.133): *denn* modifies the hearer knowledge operator, adding that some
common ground proposition is known to be the speaker's reason for asking. -/
def dennEntry : Denote W C (modifier (func .t .u) 1) :=
  λ H p c => H p c ∧ ∃ q ∈ M.commonGround c, H (M.reasonToAsk q p) c

/-- (6.123): a declarative with *ja*, whose independent contribution is merged with the
mood. -/
def jaDeclarative (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.app (.lex (Expr.ofModifier 1 (E M))) (.lex (Expr.ofModifier 0 (deont M))))
    (.elim (.app (.lex (Expr.ofModifier 0 (jaEntry M))) (prop p))))

/-- (6.128): a v2-interrogative with *ja*. -/
def jaInterrogative (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.app (.lex (Expr.ofModifier 1 (E M))) (.lex (Expr.ofModifier 0 (deont M))))
    (.elim (.app (.lex (Expr.ofModifier 0 (hknow M)))
      (.elim (.app (.lex (Expr.ofModifier 0 (jaEntry M))) (prop p))))))

/-- (6.111) to (6.113): a declarative with *wohl*, which takes the epistemic modifier, then the
deontic operator, then the content. -/
def wohlDeclarative (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.app (.app (.lex (Expr.ofModifier 2 (wohlEntry M))) (.lex (Expr.ofModifier 1 (E M))))
    (.lex (Expr.ofModifier 0 (deont M)))) (prop p))

/-- (6.135): a v2-interrogative with *denn* modifying hearer knowledge. -/
def dennInterrogative (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.app (.lex (Expr.ofModifier 1 (E M))) (.lex (Expr.ofModifier 0 (deont M))))
    (.elim (.app (.app (.lex (Expr.ofModifier 1 (dennEntry M)))
      (.lex (Expr.ofModifier 0 (hknow M)))) (prop p))))

/-- (6.140): in an imperative *denn* can only modify the deontic operator. -/
def dennImperative (p : W → Prop) : Deriv W C .t .t :=
  .elim (.app (.app (.lex (Expr.ofModifier 1 (dennEntry M))) (.lex (Expr.ofModifier 0 (deont M))))
    (prop p))

variable {M}

/-- (6.125) to (6.127): a *ja*-declarative is felicitous when the speaker wants the hearer to
know its content and believes it common knowledge or verifiable. -/
theorem jaDeclarative_u :
    (jaDeclarative M p).eval.u c ↔ M.commonKnowledge c p ∧ deont M (epis M p) c := by
  simp [jaDeclarative, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC, prop, E,
    jaEntry]

/-- A *ja*-interrogative requires the speaker to want to know its content while believing it common
knowledge and known to the hearer (6.129). -/
theorem jaInterrogative_u :
    (jaInterrogative M p).eval.u c ↔
      (M.commonKnowledge c p ∧ M.knowsWhether c p) ∧ deont M (epis M p) c := by
  simp [jaInterrogative, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC, prop, E,
    jaEntry, hknow]

/-- (6.114) and (6.116): a *wohl*-declarative is true when its content is, and felicitous under
a deontic attitude toward the epistemically embedded assumption of the content. -/
theorem wohlDeclarative_u :
    (wohlDeclarative M p).eval.t = p ∧
      ((wohlDeclarative M p).eval.u c ↔ deont M (epis M (M.assume p)) c) :=
  ⟨rfl, by simp [wohlDeclarative, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC,
    prop, E, wohlEntry]⟩

/-- (6.136) and (6.137): a *denn*-interrogative adds that some common ground proposition is
known by the hearer to be the reason for asking. -/
theorem dennInterrogative_u :
    (dennInterrogative M p).eval.u c ↔
      (M.knowsWhether c p ∧ ∃ q ∈ M.commonGround c, M.knowsWhether c (M.reasonToAsk q p)) ∧
        deont M (epis M p) c := by
  simp [dennInterrogative, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC, prop,
    E, dennEntry, hknow]

/-- (6.142): a *denn*-imperative would require the speaker to want some proposition to be the
reason for asking whether its content holds. -/
theorem dennImperative_u :
    (dennImperative M p).eval.u c ↔
      deont M p c ∧ ∃ q ∈ M.commonGround c, deont M (M.reasonToAsk q p) c := by
  simp [dennImperative, Deriv.eval, Expr.app, Expr.elim, Expr.ofModifier, Expr.ofTC, prop,
    dennEntry]

/-! ### Selectional restrictions due to types, section 6.5.1 -/

/-- The active-dimension types derivable from a lexicon by multidimensional application and
use-conditional elimination, which returns a completed use-conditional proposition to the
propositional type. -/
inductive Derivable (L : Set UCType) : UCType → Prop
  | lex {σ : UCType} : σ ∈ L → Derivable L σ
  | app {σ τ : UCType} : Derivable L (func σ τ) → Derivable L σ → Derivable L τ
  | elim : Derivable L .u → Derivable L .t

/-- The active-dimension types of a clause type's mood items: the deontic operator, and the
epistemic modifier where a [±wh] feature is visible at LF; hearer knowledge has the deontic
operator's type. -/
def ClauseType.moodTypes : ClauseType → Set UCType
  | .dassVL | .imperative => {func .t .u}
  | .v2Declarative | .vlInterrogative | .v2Interrogative => {func .t .u, modifier (func .t .u) 1}

private theorem derivable_deonticOnly_subset {σ : UCType}
    (h : Derivable ({func .t .u} ∪ {modifier (func .t .u) 2, .t}) σ) :
    σ ∈ ({.t, .u, func .t .u, modifier (func .t .u) 2} : Set UCType) := by
  induction h with
  | lex hσ =>
    simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ ⊢
    rcases hσ with rfl | rfl | rfl <;> simp
  | app _ _ ihf iha =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, modifier_succ, modifier_zero] at ihf iha ⊢
    rcases ihf with h | h | h | h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · obtain ⟨rfl, rfl⟩ := UCType.func.inj h
      simp
    · obtain ⟨rfl, rfl⟩ := UCType.func.inj h
      simp at iha
  | elim _ _ => simp

/-- No derivation from a dass-clause or imperative with *wohl* and a proposition reaches the
epistemic modifier's type (6.108). -/
theorem not_derivable_deonticOnly :
    ¬ Derivable ({func .t .u} ∪ {modifier (func .t .u) 2, .t}) (modifier (func .t .u) 1) :=
  λ h => by simpa using derivable_deonticOnly_subset h

/-- The epistemic modifier's type is derivable from a clause type's mood items with *wohl* and a
proposition iff the clause type has the epistemic modifier (Section 6.5.1). -/
theorem derivable_wohl_iff (ct : ClauseType) :
    Derivable (ct.moodTypes ∪ {modifier (func .t .u) 2, .t}) (modifier (func .t .u) 1) ↔
      ct.HasEpistemic := by
  have hpos (L : Set UCType) (h₂ : modifier (func .t .u) 2 ∈ L) (h₁ : modifier (func .t .u) 1 ∈ L) :
      Derivable L (modifier (func .t .u) 1) :=
    .app (.lex h₂) (.lex h₁)
  cases ct
  · exact ⟨not_derivable_deonticOnly, False.elim⟩
  · exact ⟨fun _ ↦ trivial, fun _ ↦ hpos _ (by simp) (by simp [ClauseType.moodTypes])⟩
  · exact ⟨fun _ ↦ trivial, fun _ ↦ hpos _ (by simp) (by simp [ClauseType.moodTypes])⟩
  · exact ⟨fun _ ↦ trivial, fun _ ↦ hpos _ (by simp) (by simp [ClauseType.moodTypes])⟩
  · exact ⟨not_derivable_deonticOnly, False.elim⟩

theorem wohl_rows :
    ∀ row ∈ Examples.all, row.feature? "particle" = some "wohl" →
      ∀ c ∈ cellOf row, ∀ ct ∈ ClauseType.ofCell c.1 c.2,
        (row.judgment = .acceptable ↔
          Derivable (ct.moodTypes ∪ {modifier (func .t .u) 2, .t}) (modifier (func .t .u) 1)) := by
  simp only [derivable_wohl_iff]
  decide

theorem excluded_rows :
    ∀ row ∈ Examples.all, ∀ p ∈ German.Particles.modalParticles,
      row.feature? "particle" = some p.form → ∀ c ∈ cellOf row,
        p.distribution c.1 c.2 = some .excluded → row.judgment ≠ .acceptable := by
  decide

end Gutzmann2015
