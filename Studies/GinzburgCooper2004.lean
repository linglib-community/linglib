module

public import Linglib.Discourse.Gameboard.Basic
public import Linglib.Data.Examples.GinzburgCooper2004

/-!
# Ginzburg and Cooper (2004): Clarification, Ellipsis, and the Nature of Contextual Updates in Dialogue

This file formalizes the account of clarification ellipsis of [ginzburg-cooper-2004], on which a
sign carries the contextual parameters its sub-utterances introduce
(`LocutionaryProposition.parameters`, `LocutionaryProposition.constituents`), grounding an
utterance is finding an assignment for all of them (`Grounds`, `grounds_iff`), and an addressee
who cannot updates the context instead by a coercion operation on the sign: parameter focussing
raises the question `?i.p`, the content with the problematic parameter abstracted
(`parameterFocussing`), parameter identification the question what the speaker meant by the
sub-utterance (`parameterIdentification`), both making that sub-utterance salient
(`focusEstablishing_parameterFocussing`), and contextual existential generalization quantifies the
parameter away so that the weaker content can be grounded (`existentialGeneralization`,
`grounds_existentialGeneralization`). Since the operations read the constituents of the sign,
utterances with the same content have different clarification potentials
(`potential_ne_of_constituents`): the Hybrid Content Hypothesis, against the purely semantic
updates of dynamic semantics.

The utterance-processing protocol integrates a pending utterance whose parameters the
participant's assignment resolves and otherwise clarifies it (`IS.ground`, `IS.clarify`); after
"Did Bo leave?" the speaker's and the addressee's information states differ in MAX-QUD and
SAL-UTT (`Ex32.differ`), and the speaker comprehends the addressee's fragment by applying the
coercion to her own latest move (`IS.backtrack`, `backtrack_eq_clarify`). A fragment resolves
against the clarification context when it matches the salient sub-utterance in category
(`DeclFrag`); the clausal reading identifies its index with the parameter and so presupposes that
the participants share the sub-utterance's content, the constituent reading does not
(`rows_clausal`, `rows_constituent`), and a fragment of the wrong category has neither
(`rows_parallelism`).

## Implementation notes

* Signs are the substrate's `LocutionaryProposition`, whose constituents' denotations name the
  parameter each contributes; contents are opaque, so existential generalization takes the binder
  as an argument, and parameter labels and contents are written as the paper's strings. A
  contextual parameter is its label: the restrictions of (28) are not represented, grounding asks
  only for a value, and the parameters an assignment leaves unresolved are those contextual
  instantiation of its labels leaves.
* A coercion operation takes the problematic sub-utterance itself, whose denotation is the
  parameter; the clarification context it yields is the substrate's `InformationStructure`, with
  MAX-QUD as its question and SAL-UTT, a set of at most one sign, as its focus-establishing
  constituents.
* The information state keeps the components that (82) displays: LATEST-MOVE as a sign with its
  assignment, PENDING, MAX-QUD and SAL-UTT; the FACTS update (81) and the grounding conditions
  (80) are not modelled.
* The constituent reading is licensed by categorial parallelism alone, the reformulation without
  utterance anaphora of footnote 55, so that the non-identical fragments of (8) get it; the
  categories of (10) are distinguished by the case or verb form the contrasts turn on.

## References

* [ginzburg-cooper-2004]
* [ginzburg-sag-2000]
* [purver-ginzburg-2004]
* [ginzburg-2012]
-/

@[expose] public section

namespace GinzburgCooper2004

open Discourse

/-- The syntactic categories of the examples, distinguished by the case or verb form the
contrasts of (10) turn on. -/
inductive Category
  | s
  | n
  | np
  | npNom
  | npAcc
  | advP
  | vFin
  | vBse
  | vPrp
  | vPsp
  deriving DecidableEq, Repr

/-- The grammatical domain of the examples has orthographic forms and categories, with parameter
labels and sub-utterance denotations written as the paper's strings. -/
abbrev grammar : GrammaticalDomain :=
  { Form := String, Category := Category, Label := String, Denotation := String }

variable {V Cont : Type}

/-! ### Contextual parameters and grounding -/

/-- A contextual assignment gives values to parameter labels. -/
abbrev Assignment (V : Type) := List (String × V)

/-- `f` resolves the parameter labelled `i`. -/
def Assignment.Resolves (f : Assignment V) (i : String) : Prop := i ∈ f.map Prod.fst

instance (f : Assignment V) (i : String) : Decidable (f.Resolves i) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- `f` grounds `σ` when it resolves every contextual parameter of the sign. -/
def Grounds (f : Assignment V) (σ : LocutionaryProposition grammar Cont) : Prop :=
  ∀ i ∈ σ.parameters, f.Resolves i

instance (f : Assignment V) (σ : LocutionaryProposition grammar Cont) : Decidable (Grounds f σ) :=
  inferInstanceAs (Decidable (∀ i ∈ σ.parameters, _))

/-- The parameters of `σ` that `f` leaves unresolved, those that remain once contextual
instantiation witnesses every parameter `f` assigns. -/
def unresolved (f : Assignment V) (σ : LocutionaryProposition grammar Cont) : Finset String :=
  (σ.instantiate (f.map Prod.fst).toFinset).parameters

theorem grounds_iff (f : Assignment V) (σ : LocutionaryProposition grammar Cont) :
    Grounds f σ ↔ unresolved f σ = ∅ := by
  simp [Grounds, unresolved, Assignment.Resolves, Finset.subset_iff]

/-! ### Sign coercion -/

/-- The issues a clarification context makes maximal: the content posed, `?i.p` with the
problematic parameter abstracted from the content (focussing), and `?c.Mean(addr, u, c)`, what the
speaker meant by the sub-utterance `u` (identification). -/
inductive Issue (Cont : Type)
  | posed (p : Cont)
  | focus (i : String) (p : Cont)
  | meaning (u : SubUtterance grammar)
  deriving DecidableEq

/-- A clarification context is the partial specification a coercion operation yields, the
maximal question under discussion with the salient sub-utterance as its focus-establishing
constituent. -/
abbrev Clarification (Cont : Type) := InformationStructure grammar (Issue Cont)

/-- Parameter focussing makes `u` salient and MAX-QUD the content with its parameter abstracted,
`?i.p`, when `u` is a constituent of `σ` contributing one of its contextual parameters. -/
def parameterFocussing (σ : LocutionaryProposition grammar Cont) (u : SubUtterance grammar) :
    Option (Clarification Cont) :=
  if u ∈ σ.constituents ∧ u.denotation ∈ σ.parameters then
    some ⟨.focus u.denotation σ.content, {u}⟩
  else none

/-- Parameter identification makes `u` salient and MAX-QUD the question what the speaker meant by
it. -/
def parameterIdentification (σ : LocutionaryProposition grammar Cont) (u : SubUtterance grammar) :
    Option (Clarification Cont) :=
  if u ∈ σ.constituents ∧ u.denotation ∈ σ.parameters then some ⟨.meaning u, {u}⟩ else none

theorem focusEstablishing_parameterFocussing (σ : LocutionaryProposition grammar Cont)
    (u : SubUtterance grammar) :
    (parameterFocussing σ u).map (·.focusEstablishing) =
      (parameterIdentification σ u).map (·.focusEstablishing) := by
  unfold parameterFocussing parameterIdentification
  split_ifs <;> rfl

/-- Contextual existential generalization instantiates the parameter `i` and makes the content
`bind i p`, the content with `i` existentially bound with widest scope. -/
def existentialGeneralization (bind : String → Cont → Cont)
    (σ : LocutionaryProposition grammar Cont) (i : String) : LocutionaryProposition grammar Cont :=
  { σ.instantiate {i} with content := bind i σ.content }

theorem grounds_existentialGeneralization {bind : String → Cont → Cont}
    {σ : LocutionaryProposition grammar Cont} {i : String} {f : Assignment V}
    (h : ∀ c ∈ σ.parameters, c ≠ i → f.Resolves c) :
    Grounds f (existentialGeneralization bind σ i) := by
  intro c hc
  simp only [existentialGeneralization, LocutionaryProposition.parameters_instantiate,
    Finset.mem_sdiff, Finset.mem_singleton] at hc
  exact h c hc.1 hc.2

/-- The clarification potential of a sign: the clarification contexts its coercion operations make
available. -/
def potential (σ : LocutionaryProposition grammar Cont) : Set (Clarification Cont) :=
  {c | ∃ u, parameterFocussing σ u = some c ∨ parameterIdentification σ u = some c}

/-- The subjects of (19)–(20), "Jill" and "She", both contributing the parameter `j`. -/
def jill : SubUtterance grammar := ⟨"Jill", .np, "j"⟩

@[inherit_doc jill] def she : SubUtterance grammar := ⟨"She", .np, "j"⟩

/-- "`form` is the president" with content `p`, its subject contributing the parameter `j`. -/
def president (form : String) (subject : SubUtterance grammar) (p : Cont) :
    LocutionaryProposition grammar Cont :=
  { form, category := .s, content := p, parameters := {"j"}, constituents := {subject} }

/-- *Jill is the president* and *She is the president* differ in clarification potential despite
equal content, the Hybrid Content Hypothesis of (19)–(20). -/
theorem potential_ne_of_constituents (p : Cont) :
    potential (president "Jill is the president" jill p) ≠
      potential (president "She is the president" she p) := by
  intro h
  have hmem : (⟨.focus "j" p, {jill}⟩ : Clarification Cont) ∈
      potential (president "Jill is the president" jill p) :=
    ⟨jill, .inl (by simp [parameterFocussing, president, jill])⟩
  rw [h] at hmem
  obtain ⟨u, hu | hu⟩ := hmem <;>
    simp [parameterFocussing, parameterIdentification, president] at hu
  exact absurd (hu.1.1.symm.trans hu.2.2) (by decide)

/-! ### Integrating utterances in information states -/

/-- The components of a participant's information state that utterance processing reads and
writes: LATEST-MOVE as the sign with its assignment, the utterances PENDING, and the clarification
context MAX-QUD and SAL-UTT, a set of at most one sign (p. 327). -/
structure IS (V Cont : Type) where
  latestMove : Option (LocutionaryProposition grammar Cont × Assignment V) := none
  pending : List (LocutionaryProposition grammar Cont) := []
  maxQud : Option (Issue Cont) := none
  salUtt : Finset (SubUtterance grammar) := ∅
  deriving DecidableEq

/-- Protocol (84a): the maximal pending utterance, once `f` grounds it, becomes LATEST-MOVE and
its content the issue posed. -/
def IS.ground (s : IS V Cont) (f : Assignment V) : Option (IS V Cont) :=
  match s.pending with
  | σ :: rest =>
    if Grounds f σ then
      some { latestMove := some (σ, f), pending := rest, maxQud := some (.posed σ.content) }
    else none
  | [] => none

/-- A coercion operation is a partial map from signs and their sub-utterances to clarification
contexts. -/
abbrev Coercion (Cont : Type) :=
  LocutionaryProposition grammar Cont → SubUtterance grammar → Option (Clarification Cont)

/-- Protocol (84c): the maximal pending utterance stays pending, and MAX-QUD and SAL-UTT take the
values the coercion specifies for the sub-utterance `u`. -/
def IS.clarify (s : IS V Cont) (coe : Coercion Cont) (u : SubUtterance grammar) :
    Option (IS V Cont) :=
  match s.pending with
  | σ :: _ =>
    (coe σ u).map fun c ↦ { s with maxQud := some c.question, salUtt := c.focusEstablishing }
  | [] => none

/-- Protocol (84b): the coercion applied to the sign of LATEST-MOVE, by which the speaker of an
utterance comprehends a clarification of it. -/
def IS.backtrack (s : IS V Cont) (coe : Coercion Cont) (u : SubUtterance grammar) :
    Option (IS V Cont) :=
  s.latestMove.bind fun m ↦
    (coe m.1 u).map fun c ↦ { s with maxQud := some c.question, salUtt := c.focusEstablishing }

theorem backtrack_eq_clarify {s s' : IS V Cont} {σ : LocutionaryProposition grammar Cont}
    (coe : Coercion Cont) (u : SubUtterance grammar) (hs : s.latestMove.map Prod.fst = some σ)
    (hs' : s'.pending.head? = some σ) :
    (s.backtrack coe u).map (fun t ↦ (t.maxQud, t.salUtt)) =
      (s'.clarify coe u).map (fun t ↦ (t.maxQud, t.salUtt)) := by
  obtain ⟨⟨τ, f⟩, hm, hτ⟩ := Option.map_eq_some_iff.1 hs
  cases hτ
  obtain ⟨ρ, rest, hp⟩ : ∃ ρ rest, s'.pending = ρ :: rest := by
    cases h : s'.pending with
    | nil => simp [h] at hs'
    | cons ρ rest => exact ⟨ρ, rest, rfl⟩
  have hρ : ρ = τ := by simpa [hp] using hs'
  subst hρ
  simp only [IS.backtrack, IS.clarify, hm, hp, Option.bind_some]
  cases coe ρ u <;> rfl

/-! ### The running example, "Did Bo leave?" (32) -/

namespace Ex32

/-- The sub-utterances of (32), each with the parameter or relation it contributes. -/
def did : SubUtterance grammar := ⟨"Did", .vFin, "ask"⟩

def bo : SubUtterance grammar := ⟨"Bo", .np, "b"⟩

def leave : SubUtterance grammar := ⟨"leave", .vBse, "leave"⟩

def clause : SubUtterance grammar := ⟨"Did Bo leave", .s, "ask(i,j,?.leave(b,t))"⟩

/-- A's utterance: the root clause's parameters are the referent of "Bo", the time, the speaker,
the addressee and the utterance time (28), (32). -/
def σ : LocutionaryProposition grammar String :=
  { form := "did bo leave", category := .vFin, content := "ask(i,j,?.leave(b,t))",
    parameters := {"b", "t", "i", "j", "k"}, constituents := {did, bo, leave, clause} }

/-- A's assignment (82b). -/
def fA : Assignment String :=
  [("b", "B"), ("t", "T0"), ("i", "A"), ("j", "B"), ("k", "T1"), ("s", "S0")]

/-- B's assignment (82c), with no value for the referent of "Bo". -/
def fB : Assignment String := [("t", "T0"), ("i", "A"), ("j", "B"), ("k", "T1"), ("s", "S0")]

theorem grounds_fA : Grounds fA σ := by decide

theorem unresolved_fB : unresolved fB σ = {"b"} := by decide

-- (54)
theorem focussing_bo : parameterFocussing σ bo = some ⟨.focus "b" σ.content, {bo}⟩ := by decide

-- (60)
theorem identification_bo : parameterIdentification σ bo = some ⟨.meaning bo, {bo}⟩ := by decide

-- (78)
theorem grounds_fB_generalized (bind : String → String → String) :
    Grounds fB (existentialGeneralization bind σ "b") :=
  grounds_existentialGeneralization (by decide)

/-- The state after A's utterance, pending for both participants. -/
def initial : IS String String := { pending := [σ] }

-- (82b)
theorem speaker : initial.ground fA =
    some { latestMove := some (σ, fA), maxQud := some (.posed σ.content) } := by decide

theorem addressee_ground : initial.ground fB = none := by decide

-- (82c)
theorem addressee : initial.clarify parameterFocussing bo =
    some { pending := [σ], maxQud := some (.focus "b" σ.content), salUtt := {bo} } := by decide

theorem differ :
    (initial.ground fA).map (·.maxQud) ≠ (initial.clarify parameterFocussing bo).map (·.maxQud) ∧
    (initial.ground fA).map (·.salUtt) ≠
      (initial.clarify parameterFocussing bo).map (·.salUtt) := by
  decide

/-- Backtracking with the same coercion, A reaches B's clarification context and can read "Bo?"
as a clarification of her utterance (83). -/
theorem backtrack :
    ((initial.ground fA).bind (·.backtrack parameterFocussing bo)).map
        (fun s ↦ (s.maxQud, s.salUtt)) =
      (initial.clarify parameterFocussing bo).map (fun s ↦ (s.maxQud, s.salUtt)) := by
  decide

end Ex32

/-! ### Clarification ellipsis and its readings -/

/-- By decl-frag-cl (47), the fragment resolves against the clarification context when it matches
the salient sub-utterance in category. -/
def DeclFrag (c : Clarification Cont) (frag : SubUtterance grammar) : Prop :=
  ∃ u ∈ c.focusEstablishing, frag.category = u.category

instance (c : Clarification Cont) (frag : SubUtterance grammar) : Decidable (DeclFrag c frag) :=
  inferInstanceAs (Decidable (∃ u ∈ c.focusEstablishing, _))

/-- Whether the participants share (a belief about) the content of the sub-utterance. -/
inductive Access
  | shared
  | distinct
  deriving DecidableEq, Repr

/-- On the clausal reading the fragment resolves against a focussing context to the polar question
whether the speaker is asking about this value of the parameter (58), identifying the fragment's
index with the sub-utterance's, which presupposes shared content. -/
def Clausal (σ : LocutionaryProposition grammar Cont) (u frag : SubUtterance grammar)
    (a : Access) : Prop :=
  match parameterFocussing σ u with
  | some c => DeclFrag c frag ∧ a = .shared
  | none => False

/-- On the constituent reading the fragment resolves against an identification context to the
question what the speaker meant (68), presupposing nothing about the value. -/
def Constituent (σ : LocutionaryProposition grammar Cont) (u frag : SubUtterance grammar) :
    Prop :=
  match parameterIdentification σ u with
  | some c => DeclFrag c frag
  | none => False

instance (σ : LocutionaryProposition grammar Cont) (u frag : SubUtterance grammar) (a : Access) :
    Decidable (Clausal σ u frag a) := by
  unfold Clausal; split <;> infer_instance

instance (σ : LocutionaryProposition grammar Cont) (u frag : SubUtterance grammar) :
    Decidable (Constituent σ u frag) := by
  unfold Constituent; split <;> infer_instance

/-- A dialogue of §1.2: the sub-utterance clarified and the fragment, whether the participants
share the sub-utterance's content, the readings the paper judges available, and the acceptability
of the ellipsis. -/
structure Row where
  antecedent : SubUtterance grammar
  fragment : SubUtterance grammar
  access : Access
  clausal : Option Judgment
  constituent : Option Judgment
  judgment : Judgment
  deriving DecidableEq

/-- The category labels of the data file. -/
def categories : List (String × Category) :=
  [("AdvP", .advP), ("N", .n), ("NP", .np), ("NP[acc]", .npAcc), ("NP[nom]", .npNom),
    ("V[bse]", .vBse), ("V[fin]", .vFin), ("V[prp]", .vPrp), ("V[psp]", .vPsp)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let ant ← ex.feature? "antecedent"
  let antCat ← ex.parse? "antecedentCat" categories
  let frag ← ex.feature? "fragment"
  let fragCat ← ex.parse? "fragmentCat" categories
  let access ← ex.parse? "access" [("shared", .shared), ("distinct", .distinct)]
  pure ⟨⟨ant, antCat, "x"⟩, ⟨frag, fragCat, ""⟩, access, ex.readings.lookup "clausal",
    ex.readings.lookup "constituent", ex.judgment⟩

/-- The sign of the row's first turn, as far as the clarification reads it, has the antecedent as
its constituent contributing the parameter `x`. -/
def Row.sign (r : Row) : LocutionaryProposition grammar Unit :=
  { form := "", category := .s, content := (), parameters := {"x"}, constituents := {r.antecedent} }

/-- The nineteen dialogues of (4), (6), (8)–(13). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = 19 := by decide

theorem rows_clausal : ∀ r ∈ rows, r.clausal = none ∨
    (r.clausal = some .acceptable ↔ Clausal r.sign r.antecedent r.fragment r.access) := by
  decide

theorem rows_constituent : ∀ r ∈ rows, r.constituent = none ∨
    (r.constituent = some .acceptable ↔ Constituent r.sign r.antecedent r.fragment) := by
  decide

/-- Categorial parallelism (10): the ellipsis is acceptable exactly when some reading resolves
it. -/
theorem rows_parallelism : ∀ r ∈ rows, r.judgment = .acceptable ↔
    (Clausal r.sign r.antecedent r.fragment r.access ∨
      Constituent r.sign r.antecedent r.fragment) := by
  decide

end GinzburgCooper2004
