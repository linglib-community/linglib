module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Krifka (2020): Layers of Assertive Clauses: Propositions, Judgements, Commitments, Acts

This file formalizes [krifka-2020]'s decomposition of an assertive clause into a proposition
(TP), a private judgement of it (JP), a public commitment to that judgement (ComP), and the act
that updates the common ground (ActP). A judgement phrase abstracts over the judge of a
judge-relative proposition (`Judgement`); the commitment phrase turns it into the proposition
that the judge is publicly responsible for its truth (`comP`); the assertive act performs a
performative update, which does not restrict the common ground but moves each of its indices
to a successor at which the speaker's commitment holds (`performative`), in contrast to the
informative update of [stalnaker-1978] (`informative`). Commitment closure, the pragmatic
step licensed once every index records a trustworthy speaker's commitment, then adds the
judgement itself (`assertClosed`), and judgement closure adds the proposition judged. On this
account a subjective epistemic adverb like *sicherlich* commits the speaker only to their own
certainty, a proposition easier to defend than the one communicated (`commits_certainly`), and
a reportative like *laut Eva* commits the speaker to Eva's commitment. The layers are ordered,
and clause-embedding predicates select a layer: *abhängen* a proposition, *glauben* and
*wissen* a judgement, *sagen* a commitment, so which modifiers a complement clause admits
follows from the layer selected (`Licensed`).

## Implementation notes

* The branching successor relation `i ⊶ i′[φ]` is a primitive with its one axiom, that `φ`
  holds at the successor; a model supplies it together with the commitment and certainty
  relations. Judgements and commitments share the type of functions from judges to
  propositions, the paper's sortal distinction being carried by the operators that build them.
* The closures are informative updates under their conditions, the trustworthiness and the
  absence of objection being left to the discourse.
* Commitment strength (§3.2) is not modelled: the paper argues it has no discrete values on a
  single dimension. The report readings under which *wissen* and *glauben* embed commitment
  modifiers are noted, not modelled.

## References

* [krifka-2020]
* [krifka-2015] — commitment spaces, the framework the layers refine
* [stalnaker-1978] — informative update
* [farkas-bruce-2010] — assertions that stick to the common ground even when rejected
-/

@[expose] public section

namespace Krifka2020

variable {Judge Index : Type*}

/-! ### Propositions, judgements, commitments, acts -/

/-- A judge-relative proposition, the meaning of a TP (19), or of a judgement phrase (20),
which makes the judge accessible. -/
abbrev Judgement (Judge Index : Type*) := Judge → Index → Prop

/-- The primitives of the semantics: public commitment `x ⊢ᵢ φ`, the certainty operator of
(42), and the branching successor `i ⊶ i′[φ]`, at which `φ` holds. -/
structure Model (Judge Index : Type*) where
  commits : Judge → Index → (Index → Prop) → Prop
  cert : Judge → Index → (Index → Prop) → Prop
  succ : Index → (Index → Prop) → Index → Prop
  succ_holds : ∀ i φ i', succ i φ i' → φ i'

variable (M : Model Judge Index)

/-- The commitment phrase (21): the judge is publicly responsible for the truth of the
judgement. -/
def comP (J : Judgement Judge Index) : Judgement Judge Index := λ j i => M.commits j i (J j)

/-- Informative update (22): restriction of the common ground. -/
def informative (c : Set Index) (φ : Index → Prop) : Set Index := {i ∈ c | φ i}

/-- Performative update (23): each index moves to a successor at which the proposition holds.
-/
def performative (c : Set Index) (φ : Index → Prop) : Set Index :=
  {i' | ∃ i ∈ c, M.succ i φ i'}

/-- The assertive act (24): the performative update with the commitment phrase applied to the
speaker. -/
def assert (s : Judge) (c : Set Index) (J : Judgement Judge Index) : Set Index :=
  performative M c (comP M J s)

/-- Commitment closure (25) after an assertion ((26), (27)): the judgement the speaker is
committed to is added to the common ground. -/
def assertClosed (s : Judge) (c : Set Index) (J : Judgement Judge Index) : Set Index :=
  informative (assert M s c J) (J s)

/-- A subjective epistemic adverb (42): the judge is certain of the judgement. -/
def certainly (J : Judgement Judge Index) : Judgement Judge Index := λ j i => M.cert j i (J j)

/-- A reportative evidential (53): another authority is committed to the judgement. -/
def according (x : Judge) (J : Judgement Judge Index) : Judgement Judge Index :=
  λ _ i => M.commits x i (J x)

/-- *Allegedly* (55): some authority is committed to the judgement. -/
def allegedly (J : Judgement Judge Index) : Judgement Judge Index :=
  λ _ i => ∃ x, M.commits x i (J x)

variable {M} {s : Judge} {c : Set Index} {J : Judgement Judge Index} {i : Index}

theorem informative_subset (c : Set Index) (φ : Index → Prop) : informative c φ ⊆ c :=
  λ _ h => h.1

theorem commits_of_mem_assert (h : i ∈ assert M s c J) : M.commits s i (J s) :=
  let ⟨_, _, h⟩ := h; M.succ_holds _ _ _ h

-- (27)
theorem mem_assertClosed_iff :
    i ∈ assertClosed M s c J ↔ (∃ i₀ ∈ c, M.succ i₀ (comP M J s) i) ∧ J s i :=
  Iff.rfl

theorem assertClosed_subset_assert : assertClosed M s c J ⊆ assert M s c J :=
  informative_subset _ _

/-! ### Judgement modifiers -/

/-- Asserting a hedged judgement (46) commits the speaker to their certainty, not to the
proposition. -/
theorem commits_certainly (h : i ∈ assert M s c (certainly M J)) :
    M.commits s i λ i => M.cert s i (J s) :=
  commits_of_mem_assert h

-- (44)
theorem cert_of_mem_assertClosed (h : i ∈ assertClosed M s c (certainly M J)) :
    M.cert s i (J s) :=
  h.2

-- (53)
theorem commits_according {x : Judge} (h : i ∈ assert M s c (according M x J)) :
    M.commits s i λ i => M.commits x i (J x) :=
  commits_of_mem_assert h

-- (91)
theorem according_certainly (x : Judge) :
    (according M x (certainly M J) = λ _ i => M.commits x i λ i => M.cert x i (J x)) ∧
      (certainly M (according M x J) = λ j i => M.cert j i λ i => M.commits x i (J x)) :=
  ⟨rfl, rfl⟩

/-! ### A model -/

/-- Indices as times, a commitment or a judgement being on record from the first step on,
and the successor the next step. -/
def steps : Model Unit ℕ where
  commits _ i _ := 0 < i
  cert _ i _ := 0 < i
  succ i φ i' := i' = i + 1 ∧ φ i'
  succ_holds _ _ _ h := h.2

/-- *Max snores loudly* from the first step on. -/
def snores : Judgement Unit ℕ := λ _ i => 0 < i

theorem assert_steps :
    assert steps () {0} snores = {1} ∧ assertClosed steps () {0} snores = {1} :=
  have h : assert steps () {0} snores = {1} := Set.ext λ i =>
    ⟨λ ⟨_, h0, h1, _⟩ => Set.mem_singleton_iff.2 (by have := Set.mem_singleton_iff.1 h0; omega),
      λ h => ⟨0, rfl, show i = 0 + 1 by have := Set.mem_singleton_iff.1 h; omega,
        show 0 < i by have := Set.mem_singleton_iff.1 h; omega⟩⟩
  ⟨h, Set.ext λ i => ⟨λ ⟨h1, _⟩ => h ▸ h1,
    λ h1 => ⟨h ▸ h1, show 0 < i by have := Set.mem_singleton_iff.1 h1; omega⟩⟩⟩

/-! ### Layers and embedding -/

/-- The layers of an assertive clause, in the order of (88). -/
inductive Layer
  | tp
  | jp
  | comP
  | actP
  deriving DecidableEq, Fintype, Repr

/-- The height of a layer. -/
def Layer.rank : Layer → ℕ
  | .tp => 0
  | .jp => 1
  | .comP => 2
  | .actP => 3

instance : LinearOrder Layer := LinearOrder.lift' Layer.rank (by decide)

/-- Modifiers of §3, with the layer they modify: subjective epistemics and evidentials the
judgement, affirmatives the commitment, *offen gesagt* the act. -/
inductive Modifier
  | sicherlich
  | wahrscheinlich
  | lautEva
  | echt
  | ungelogen
  | wirklich
  | ehrlich
  | offenGesagt
  deriving DecidableEq, Fintype, Repr

def Modifier.layer : Modifier → Layer
  | .sicherlich | .wahrscheinlich | .lautEva => .jp
  | .echt | .ungelogen | .wirklich | .ehrlich => .comP
  | .offenGesagt => .actP

/-- Clause-embedding predicates of §4.1 with the layer they select: a proposition (96), a
judgement (101), a commitment (111), or an act (112). -/
inductive Predicate
  | abhaengen
  | glauben
  | wissen
  | sagen
  | mitteilen
  deriving DecidableEq, Repr

def Predicate.selects : Predicate → Layer
  | .abhaengen => .tp
  | .glauben | .wissen => .jp
  | .sagen => .comP
  | .mitteilen => .actP

/-- A modifier occurs in a complement clause when the predicate selects its layer or a higher
one. -/
def Licensed (m : Modifier) (p : Predicate) : Prop := m.layer ≤ p.selects

instance (m : Modifier) (p : Predicate) : Decidable (Licensed m p) :=
  inferInstanceAs (Decidable (_ ≤ _))

-- (95), (100), (110)
theorem licensed_iff :
    (∀ m, ¬ Licensed m .abhaengen) ∧ (∀ m, Licensed m .glauben ↔ m.layer = .jp) ∧
      (∀ m, Licensed m .sagen ↔ m.layer ≠ .actP) := by
  decide

end Krifka2020
