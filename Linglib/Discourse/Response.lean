module

public import Linglib.Semantics.Polarity.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype

/-!
# Responses and their polarity features

A responding move reacts to a sentence that an assertion or a polar question has put on the
Table. Farkas and Bruce classify it by two polarity features, which Roelofsen and Farkas take
over: its relative polarity, [same] when it confirms that sentence and [reverse] when it reverses
it, and its absolute polarity, [+] or [−], the polarity of the sentence it asserts. A
`Discourse.Response` records the move it reacts to, the polarity of the sentence on the Table
and its own polarity, and its relative polarity is the quotient of the two. On a response
sharing the radical of the sentence on the Table this is Farkas and Bruce's definition of the
feature: the relative polarity takes the proposition on the Table to the one the response
asserts, so the response confirms that proposition iff it is [same] and reverses it iff it is
[reverse].

What a theory says a polarity particle marks is a set of responses. The typology of answering
systems asks which particle confirms the negative alternative of a negative polar question: the
affirmative one in a truth-based, or agree/disagree, system, and the negative one in a
polarity-based, or yes/no, system.

## Main definitions

* `Discourse.InitiatingMove`: an assertion or a polar question.
* `Discourse.Response`: a responding move, with `Response.relative` its relative polarity.
* `Discourse.Response.Feature`, `Discourse.Response.HasFeature`: the relative and absolute
  polarity features, and the features a response bears.
* `Discourse.Response.ConfirmsNegativeQuestion`: a set of responses includes the confirmation
  of a negative polar question, [same, −].

## Main results

* `Discourse.Response.eq_relative_iff_smul_eq`: under a free polarity action the relative
  polarity is the only polarity taking the antecedent's proposition to the response's.
* `Discourse.Response.polarity_smul_eq_antecedent_smul_iff`,
  `Discourse.Response.polarity_smul_eq_compl_iff`: a response asserts the proposition on the
  Table iff it is [same], and its complement iff it is [reverse].
* `Discourse.Response.exists_value_eq_and_hasFeature_iff`: a response bears a feature of a given
  value iff its relative or its absolute polarity has it.

## Implementation notes

Over a radical `p`, the propositions of a response and of its antecedent are two points of the
orbit `{p, pᶜ}`, on which the polarity group acts freely and transitively. The orbit is thus a
torsor and the relative polarity the quotient of the two points; `eq_relative_iff_smul_eq` states
this through freeness (`IsCancelSMul`) without building the torsor.

## References

* [farkas-bruce-2010]
* [roelofsen-farkas-2015]
* [sadock-zwicky-1985]
* [holmberg-2016]
-/

@[expose] public section

namespace Discourse

/-- A move that puts a sentence on the Table for a response to react to. -/
inductive InitiatingMove where
  /-- An assertion, a [reverse] response to which is a denial. -/
  | assertion
  /-- A polar question, a [reverse] response to which is a reverse answer. -/
  | polarQuestion
  deriving DecidableEq, Repr, Fintype

/-- A responding move, given by the move it reacts to, the polarity of the sentence radical on
the Table, and the polarity of the sentence it asserts. -/
structure Response where
  /-- The move responded to. -/
  reactsTo : InitiatingMove
  /-- The polarity of the sentence on the Table. -/
  antecedent : Polarity
  /-- The polarity of the response, its absolute polarity. -/
  polarity : Polarity
  deriving DecidableEq, Repr, Fintype

namespace Response

/-- The relative polarity of a response, positive ([same]) when it shares the polarity of the
sentence on the Table and negative ([reverse]) when it reverses it. -/
def relative (x : Response) : Polarity := x.polarity / x.antecedent

@[simp] theorem relative_mk (m : InitiatingMove) (a p : Polarity) :
    (⟨m, a, p⟩ : Response).relative = p / a := rfl

variable {x : Response}

theorem relative_eq_positive_iff : x.relative = .positive ↔ x.polarity = x.antecedent :=
  div_eq_one

theorem relative_eq_negative_iff : x.relative = .negative ↔ x.polarity ≠ x.antecedent := by
  rw [Ne, ← relative_eq_positive_iff]
  cases x.relative <;> decide

/-! ### The propositions of a response -/

section Smul

variable {X : Type*} [MulAction Polarity X] {r : Polarity}

/-- The relative polarity of a response takes the antecedent's proposition to the response's. -/
@[simp] theorem relative_smul_antecedent_smul (x : Response) (a : X) :
    x.relative • x.antecedent • a = x.polarity • a := by
  rw [smul_smul, relative, div_mul_cancel]

/-- Under a free action, the relative polarity of a response is the only polarity taking the
antecedent's proposition to the response's. -/
theorem eq_relative_iff_smul_eq [IsCancelSMul Polarity X] (a : X) :
    r = x.relative ↔ r • x.antecedent • a = x.polarity • a := by
  rw [← x.relative_smul_antecedent_smul a]
  exact ⟨fun h ↦ h ▸ rfl, IsCancelSMul.right_cancel _ _ _⟩

/-- Under a free action, a response asserts the proposition on the Table iff it is [same]. -/
theorem polarity_smul_eq_antecedent_smul_iff [IsCancelSMul Polarity X] (a : X) :
    x.polarity • a = x.antecedent • a ↔ x.relative = .positive := by
  rw [eq_comm, eq_comm (b := Polarity.positive), eq_relative_iff_smul_eq a,
    Polarity.positive_smul]

/-- A response asserts the complement of the proposition on the Table iff it is [reverse]. -/
theorem polarity_smul_eq_compl_iff {W : Type*} [Nonempty W] (p : Set W) :
    x.polarity • p = (x.antecedent • p)ᶜ ↔ x.relative = .negative := by
  rw [eq_comm, eq_comm (b := Polarity.negative), eq_relative_iff_smul_eq p,
    Polarity.negative_smul_set]

end Smul

/-! ### Polarity features -/

/-- A polarity feature is relative, [same] when positive and [reverse] when negative, or
absolute, [+] or [−]. -/
inductive Feature where
  /-- The relative polarity feature, [same] or [reverse]. -/
  | relative (r : Polarity)
  /-- The absolute polarity feature, [+] or [−]. -/
  | absolute (s : Polarity)
  deriving DecidableEq, Repr, Fintype

/-- The polarity of a feature, positive for [same] and [+] and negative for [reverse] and
[−]. -/
def Feature.value : Feature → Polarity
  | .relative r => r
  | .absolute s => s

/-- A response bears the relative feature of its relative polarity and the absolute feature of
its polarity. -/
def HasFeature (x : Response) : Feature → Prop
  | .relative r => x.relative = r
  | .absolute s => x.polarity = s

@[simp] theorem hasFeature_relative {r : Polarity} :
    x.HasFeature (.relative r) ↔ x.relative = r := Iff.rfl

@[simp] theorem hasFeature_absolute {s : Polarity} :
    x.HasFeature (.absolute s) ↔ x.polarity = s := Iff.rfl

instance (x : Response) : DecidablePred x.HasFeature
  | .relative _ => inferInstanceAs (Decidable (_ = _))
  | .absolute _ => inferInstanceAs (Decidable (_ = _))

/-- A response bears a feature of value `v` iff its relative or its absolute polarity is `v`. -/
theorem exists_value_eq_and_hasFeature_iff {v : Polarity} :
    (∃ f : Feature, f.value = v ∧ x.HasFeature f) ↔ x.relative = v ∨ x.polarity = v := by
  constructor
  · rintro ⟨_ | _, rfl, h⟩
    exacts [Or.inl h, Or.inr h]
  · rintro (h | h)
    exacts [⟨.relative v, rfl, h⟩, ⟨.absolute v, rfl, h⟩]

/-! ### Answering systems -/

/-- The confirmation of the negative alternative of a negative polar question, [same, −]. -/
def negativeQuestionConfirmation : Response := ⟨.polarQuestion, .negative, .negative⟩

/-- The responses `S` include the confirmation of the negative alternative of a negative polar
question. -/
def ConfirmsNegativeQuestion (S : Set Response) : Prop := negativeQuestionConfirmation ∈ S

instance (S : Set Response) [DecidablePred (· ∈ S)] : Decidable (ConfirmsNegativeQuestion S) :=
  inferInstanceAs (Decidable (negativeQuestionConfirmation ∈ S))

end Response

end Discourse
