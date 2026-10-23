module

public import Linglib.Data.Examples.FarkasRoelofsen2017
public import Linglib.Discourse.Commitment.Basic
public import Linglib.Semantics.Questions.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Farkas and Roelofsen (2017): Division of Labor in Declaratives and Interrogatives

This file formalizes [farkas-roelofsen-2017]'s account of falling and rising declaratives,
polar interrogatives and tag interrogatives: their inquisitive semantics, the single basic
convention of use that replaces the Fregean force operators, and the special discourse effects
of the marked forms. A sentence form is a clause-type marker with an intonation, or a declarative
anchor with a tag (`Form`, §4.1); the markers are interpreted by the projection operators
of inquisitive semantics (31), (34), (36): `dec` is the non-inquisitive projection, the double
complement `Pᶜᶜ`, `int` the non-informative projection `Question.query` applied only to a
non-inquisitive argument, falling intonation is vacuous and rising intonation is `Question.query`
again. `Form.interpret` composes them as in (37)–(40): a falling declarative expresses
`!P` and every other form `?!P`, so that with a non-inquisitive radical the rising declarative,
the polar interrogatives and the tag interrogatives express one and the same inquisitive
proposition (`interpret_declarative_falling`, `interpret_marked`, `interpret_interrogative_ofSet`,
`isInquisitive_interpret_ofSet`; (41) and (43)). Among the forms for that content the polar
interrogatives are optimal and the rest marked (`Form.IsMarked`, (47)).

A discourse context is a stack of propositions, a commitment state, and for each participant the
possibilities she has signalled evidence for with a credence interval (the paper's (22) and §3.2;
`Context`, `Context.cs`, `Context.cg`, `Context.CommonlyDecided`). The basic convention of use
`Context.basic` puts the proposition on the table and commits the speaker to its informative
content (48); a falling declarative thereby commits her to the radical and the inquisitive
forms commit her to nothing (`cs_basic_declarative_falling`, `cs_basic_of_isInquisitive`; their
(49) and (50)). The special effects of the marked forms add the highlighted alternative to the
speaker's evidence with the credence interval of (52), (56) and (58), `[zero, low]` for the
rising declarative, `[moderate, high]` for the rising tag and `[high]` for the falling tag
(`Form.specialEffect`); `Context.utter` is the full conventional effect, and
`utter_eq_basic_of_not_isMarked` is the division of labor principle (21): the discourse
effects of the unmarked forms are the basic convention alone. §6 tests the account in
contexts that fix the speaker's evidence and credence; `Felicitous` renders the reasoning of that
section on a `Situation`, and `rows_felicitous` checks it against all sixty judgments of
(53)–(77).

## Implementation notes

* The felicity conditions of §6 are the paper's prose reasoning made explicit: a commitment to
  the radical needs high credence to be possible in the context; an inquisitive proposition on
  the table needs an addressee who is not neutral (61); an unmarked inquisitive form
  presents the speaker as neutral, which needs low credence to be possible (the paper's (63) against
  (65) and (67)); a marked form needs evidence for the highlighted alternative and a credence
  the context allows within the form's interval.
* The paper's `⟨?⟩` is a classical case split on inquisitiveness, so `Form.interpret` is
  noncomputable. Highlighting is the radical's own alternative, which the operators leave in
  place, so the forms take the radical's proposition `ofSet α` and `α` is the highlighted
  alternative by construction.
* The common ground is derived from the commitment sets as the paper derives it, not stored.

## References

* [farkas-roelofsen-2017]
* [farkas-bruce-2010]
* [ciardelli-groenendijk-roelofsen-2018]
* [roelofsen-farkas-2015]
* [gunlogson-2001]
* [malamud-stephenson-2015]
-/

@[expose] public section

namespace FarkasRoelofsen2017

open Commitment Question

/-! ### Sentence forms and their semantics -/

/-- Rising or falling intonation, the markers `open` and `closed` of (26b). -/
inductive Intonation
  | falling
  | rising
  deriving DecidableEq, Repr

/-- The six sentence forms of (3)–(8) are a declarative or interrogative clause with its
intonation, or a falling declarative anchor with a reverse-polarity tag carrying the
intonation. -/
inductive Form
  | declarative (i : Intonation)
  | interrogative (i : Intonation)
  | tag (i : Intonation)
  deriving DecidableEq, Repr

variable {W : Type*}

namespace Intonation

/-- `closed` intonation is vacuous and `open` intonation is the non-informative projection
(36). -/
def interpret : Intonation → Question W → Question W
  | .falling => id
  | .rising => Question.query

end Intonation

namespace Form

open scoped Classical in
/-- `dec` is `!`, `int` is `⟨?⟩`, which applies `?` only to a non-inquisitive argument, and a
tag applies `int` to the falling declarative anchor, as in (37)–(40). -/
noncomputable def interpret : Form → Question W → Question W
  | .declarative i, P => i.interpret Pᶜᶜ
  | .interrogative i, P => i.interpret (if P.IsInquisitive then P else P.query)
  | .tag i, P => i.interpret (if Pᶜᶜ.IsInquisitive then Pᶜᶜ else Pᶜᶜ.query)

/-- Polar interrogatives are the optimal forms for an inquisitive content, and rising
declaratives and tag interrogatives are marked (47). -/
def IsMarked : Form → Prop
  | .declarative .rising => True
  | .tag _ => True
  | _ => False

instance : DecidablePred IsMarked := λ f => by
  cases f with
  | declarative i => cases i <;> unfold IsMarked <;> infer_instance
  | interrogative i => unfold IsMarked; infer_instance
  | tag i => unfold IsMarked; infer_instance

end Form

/-- A falling declarative expresses the non-inquisitive projection of its radical (41a). -/
theorem interpret_declarative_falling (P : Question W) :
    (Form.declarative .falling).interpret P = Pᶜᶜ := rfl

/-- A rising declarative and a tag interrogative express `?!P`, as in (39) and (40). -/
theorem interpret_marked (P : Question W) (i : Intonation) :
    (Form.declarative .rising).interpret P = Pᶜᶜ.query ∧
      (Form.tag i).interpret P = Pᶜᶜ.query := by
  refine ⟨rfl, ?_⟩
  cases i <;> simp [Form.interpret, Intonation.interpret, not_isInquisitive_compl]

/-- A polar interrogative with a non-inquisitive radical expresses `?P`, whatever its
intonation (38). -/
theorem interpret_interrogative_ofSet (α : Set W) (i : Intonation) :
    (Form.interrogative i).interpret (ofSet α) = (ofSet α).query := by
  cases i <;> simp [Form.interpret, Intonation.interpret, not_isInquisitive_ofSet]

/-- Every form but the falling declarative expresses the same inquisitive proposition
`{α, ᾱ}` for a radical `α` (43). -/
theorem interpret_eq_query_ofSet (α : Set W) (f : Form) (h : f ≠ .declarative .falling) :
    f.interpret (ofSet α) = (ofSet α).query := by
  rcases f with i | i | i
  · cases i
    · exact absurd rfl h
    · simp [Form.interpret, Intonation.interpret]
  · exact interpret_interrogative_ofSet α i
  · rw [(interpret_marked (ofSet α) i).2, compl_compl_ofSet]

/-- Those forms raise a genuine issue unless the radical is a tautology or a
contradiction (41b). -/
theorem isInquisitive_interpret_ofSet {α : Set W} (h₁ : α ≠ Set.univ) (h₂ : α ≠ ∅) (f : Form)
    (h : f ≠ .declarative .falling) : (f.interpret (ofSet α)).IsInquisitive := by
  rw [interpret_eq_query_ofSet α f h]
  exact isInquisitive_query (by simpa using h₁) (by simpa using h₂)

/-! ### Credence and discourse contexts -/

/-- §3.2 distinguishes four credence levels, from `zero`, when the highlighted alternative is not
considered more likely than its complement, to `high`, when it is much more likely. -/
inductive CredenceLevel
  | zero
  | low
  | moderate
  | high
  deriving DecidableEq, Repr, Fintype

namespace CredenceLevel

def toNat : CredenceLevel → ℕ
  | .zero => 0
  | .low => 1
  | .moderate => 2
  | .high => 3

instance : LinearOrder CredenceLevel := LinearOrder.lift' toNat (by decide)

end CredenceLevel

/-- A discourse context (22), enriched in §3.2, records the propositions proposed so far, the
participants' commitments, and for each participant the possibilities they have signalled
evidence for, each with a credence interval. -/
structure Context (A W : Type*) where
  table : List (Question W)
  commitments : State A W
  evidence : A → Set (Set W × Set CredenceLevel)

namespace Context

variable {A : Type*} (K : Context A W) (x : A)

/-- `cs(x)` is the set of worlds compatible with everything `x` is committed to. -/
def cs : Set W := K.commitments.commitmentSet x

/-- The common ground, the smallest set every participant is committed to the actual world
lying in. -/
def cg : Set W := ⋃ x, K.cs x

/-- The participants have commonly decided on `P` when the common ground complies with it or
cannot comply with it. -/
def CommonlyDecided (P : Question W) : Prop := K.cg ∈ P ∨ ∀ s ∈ P, K.cg ∩ s = ∅

/-- The basic convention of use (48) puts the proposition on the table and its informative
content into the speaker's commitments. -/
def basic (φ : Question W) : Context A W :=
  ⟨φ :: K.table, insert (x, φ.info) K.commitments, K.evidence⟩

/-- A special effect enters the highlighted alternative into the speaker's evidence with a
credence interval. -/
def special [DecidableEq A] (α : Set W) (I : Set CredenceLevel) : Context A W :=
  { K with evidence := Function.update K.evidence x (insert (α, I) (K.evidence x)) }

end Context

/-- A marked form signals a credence interval for the highlighted alternative, as in (52), (56)
and (58). -/
def Form.specialEffect : Form → Option (CredenceLevel × CredenceLevel)
  | .declarative .rising => some (.zero, .low)
  | .tag .rising => some (.moderate, .high)
  | .tag .falling => some (.high, .high)
  | _ => none

namespace Context

variable {A : Type*} [DecidableEq A] (K : Context A W) (x : A)

/-- The conventional discourse effect of `x` uttering the form `f` with radical `α` is the basic
convention on the proposition the form expresses, followed by the form's special effect if it
has one. -/
noncomputable def utter (f : Form) (α : Set W) : Context A W :=
  match f.specialEffect with
  | none => K.basic x (f.interpret (ofSet α))
  | some I => (K.basic x (f.interpret (ofSet α))).special x α (Set.Icc I.1 I.2)

/-- By the division of labor principle (21a), an unmarked form's discourse effects are the
basic convention of use alone. -/
theorem utter_eq_basic_of_not_isMarked {f : Form} (h : ¬ f.IsMarked) (α : Set W) :
    K.utter x f α = K.basic x (f.interpret (ofSet α)) := by
  rcases f with i | i | i <;> cases i <;> simp_all [utter, Form.specialEffect, Form.IsMarked]

/-- A marked form's effects include the basic convention (21b). -/
theorem table_utter (f : Form) (α : Set W) :
    (K.utter x f α).table = f.interpret (ofSet α) :: K.table := by
  rcases f with i | i | i <;> cases i <;> rfl

theorem commitments_utter (f : Form) (α : Set W) :
    (K.utter x f α).commitments =
      insert (x, (f.interpret (ofSet α)).info) K.commitments := by
  rcases f with i | i | i <;> cases i <;> rfl

omit [DecidableEq A] in
/-- A falling declarative commits the speaker to the radical (49). -/
theorem cs_basic_declarative_falling (α : Set W) :
    (K.basic x ((Form.declarative .falling).interpret (ofSet α))).cs x = K.cs x ∩ α := by
  simp only [cs, basic, interpret_declarative_falling, compl_compl_ofSet, info_ofSet]
  rw [State.commitmentSet_insert_self, Set.inter_comm]

omit [DecidableEq A] in
/-- An inquisitive proposition commits the speaker only to the trivial possibility, as in (50)
and (51). -/
theorem cs_basic_of_isInquisitive {φ : Question W} (h : φ.info = Set.univ) :
    (K.basic x φ).cs x = K.cs x := by
  simp only [cs, basic, h]
  rw [State.commitmentSet_insert_self, Set.univ_inter]

/-- A marked form registers the highlighted alternative as evidenced with its credence
interval, as in (52), (56) and (58). -/
theorem mem_evidence_utter {f : Form} {I : CredenceLevel × CredenceLevel}
    (h : f.specialEffect = some I) (α : Set W) :
    (α, Set.Icc I.1 I.2) ∈ (K.utter x f α).evidence x := by
  simp [utter, h, special]

theorem evidence_utter_of_not_isMarked {f : Form} (h : ¬ f.IsMarked) (α : Set W) :
    (K.utter x f α).evidence = K.evidence := by
  rw [utter_eq_basic_of_not_isMarked K x h]
  rfl

end Context

/-! ### Testing the account (§6) -/

/-- A situation of §6 fixes whether the speaker has evidence for the highlighted alternative,
whether the addressee is neutral, and the range of credence the context makes reasonable. -/
structure Situation where
  evidence : Bool
  addresseeNeutral : Bool
  lo : CredenceLevel
  hi : CredenceLevel
  deriving DecidableEq, Repr

/-- A form is felicitous in a situation by the reasoning of §6: a commitment to the radical
needs high credence to be possible; an issue on the table needs an addressee who is not neutral;
the unmarked inquisitive form presents the speaker as neutral, which needs low credence to be
possible; a marked form needs evidence and a credence the context allows within its interval. -/
def Felicitous (f : Form) (s : Situation) : Prop :=
  match f.specialEffect with
  | some I => s.evidence ∧ ¬ s.addresseeNeutral ∧ ∃ c, s.lo ≤ c ∧ c ≤ s.hi ∧ I.1 ≤ c ∧ c ≤ I.2
  | none =>
    match f with
    | .declarative _ => s.lo ≤ .high ∧ .high ≤ s.hi
    | _ => ¬ s.addresseeNeutral ∧ s.lo ≤ .low

instance (f : Form) (s : Situation) : Decidable (Felicitous f s) := by
  rcases f with i | i | i <;> cases i <;> simp only [Felicitous, Form.specialEffect] <;>
    infer_instance

/-- A judgment of §6 records the form, the situation, and the paper's verdict. -/
structure Row where
  form : Form
  situation : Situation
  judgment : Judgment
  deriving DecidableEq, Repr

def formTable : List (String × Form) :=
  [("fallingDeclarative", .declarative .falling), ("risingDeclarative", .declarative .rising),
    ("fallingInterrogative", .interrogative .falling),
    ("risingInterrogative", .interrogative .rising), ("fallingTag", .tag .falling),
    ("risingTag", .tag .rising)]

def boolTable : List (String × Bool) := [("yes", true), ("no", false)]

def addresseeTable : List (String × Bool) := [("neutral", true), ("informed", false)]

def credenceTable : List (String × CredenceLevel) :=
  [("zero", .zero), ("low", .low), ("moderate", .moderate), ("high", .high)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let form ← ex.parse? "form" formTable
  let evidence ← ex.parse? "evidence" boolTable
  let addresseeNeutral ← ex.parse? "addressee" addresseeTable
  let lo ← ex.parse? "credenceMin" credenceTable
  let hi ← ex.parse? "credenceMax" credenceTable
  pure ⟨form, ⟨evidence, addresseeNeutral, lo, hi⟩, ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The account reproduces every judgment of §6. -/
theorem rows_felicitous :
    ∀ r ∈ rows, r.judgment = .acceptable ↔ Felicitous r.form r.situation := by
  decide

end FarkasRoelofsen2017
