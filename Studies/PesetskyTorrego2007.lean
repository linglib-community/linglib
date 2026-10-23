module

public import Linglib.Core.Order.Flat
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Pesetsky and Torrego (2007): The syntax of valuation and the interpretability of features

Agree shares features: an unvalued probe feature is replaced by the goal's, so that one feature
has instances at both locations (5). Agree between two unvalued features is therefore not vacuous,
since a later Agree that values one instance values them all (7)–(8). Valuation and
interpretability are independent (9): Tns bears interpretable unvalued T and the finite verb
uninterpretable valued T (10), and every feature must be valued and interpreted at one of its
instances, Radical Interpretability (15). Structural case is an uninterpretable instance of T. In
a finite clause the finite verb values the subject's case through Tns (17); in a raising
infinitive, whose verb's T is unvalued, the subject's case is valued only once it raises into a
finite clause, which values the infinitival Tns as well (18). Defectivity is the absence of a
value.

## Implementation notes

* A state names the feature each location bears by the location that first bore it, so that two
  locations share a feature when the map identifies them, and stores each feature's value in
  `Flat`, `⊥` while unvalued. Interpretability belongs to locations, one per instance.
* Agree applies when the probe's feature is unvalued, and replaces every instance of it. In its
  assignment version (2) the probe's feature takes the goal's value and no link remains.

## TODO

* Wh-typing (13)–(14), sentential subjects (section 5), and the deletion of uninterpretable
  instances.

## References

* [pesetsky-torrego-2007]
* [chomsky-2001]
-/

@[expose] public section

namespace PesetskyTorrego2007

/-! ### Feature sharing -/

/-- A state of feature sharing over the locations `L`: the feature each location bears, named by
the location that first bore it, and the value of each feature. -/
structure State (L V : Type*) where
  /-- The feature a location bears. -/
  feature : L → L
  /-- The value of a feature, `⊥` while unvalued. -/
  value : L → Flat V

namespace State

variable {L V : Type*}

/-- The lexicon's state: each location bears a feature of its own, with its lexical value. -/
def lexical (v : L → Flat V) : State L V := ⟨id, v⟩

variable (s : State L V)

/-- The value at a location, that of the feature it bears. -/
def valueAt (x : L) : Flat V := s.value (s.feature x)

/-- Two locations share a feature when they bear the same one. -/
def Shares : Setoid L := Setoid.ker s.feature

variable [DecidableEq L] [DecidableEq V]

instance : DecidableRel s.Shares := fun _ _ ↦ decidable_of_iff _ Setoid.ker_def.symm

/-- Agree, feature sharing version (5): the unvalued feature at `α` is replaced, at every one of
its instances, by the feature at `β`. -/
def agree (α β : L) : Option (State L V) :=
  if s.valueAt α = ⊥ then
    some ⟨fun x ↦ if s.feature x = s.feature α then s.feature β else s.feature x, s.value⟩
  else none

/-- Agree, assignment version (2): the unvalued feature at `α` takes the value of the feature at
`β`, and no link between them remains. -/
def assign (α β : L) : Option (State L V) :=
  if s.valueAt α = ⊥ then some ⟨s.feature, Function.update s.value (s.feature α) (s.valueAt β)⟩
  else none

variable {s} {α β : L} {s' : State L V}

theorem shares_of_agree (h : s.agree α β = some s') : s'.Shares α β := by
  unfold agree at h
  split at h
  · cases h; simp [Setoid.ker_def]
  · cases h

theorem Shares.agree {x y : L} (hxy : s.Shares x y) (h : s.agree α β = some s') :
    s'.Shares x y := by
  unfold State.agree at h
  split at h
  · cases h
    simp only [Setoid.ker_def] at hxy ⊢
    simp [hxy]
  · cases h

theorem valueAt_agree {x : L} (hx : s.Shares x α) (h : s.agree α β = some s') :
    s'.valueAt x = s.valueAt β := by
  unfold agree at h
  split at h
  · cases h
    simp only [Setoid.ker_def] at hx
    simp [valueAt, hx]
  · cases h

end State

variable {L V : Type*} [Fintype L] [DecidableEq L] (interp : L → Prop) [DecidablePred interp]

/-- Radical Interpretability (15): every feature is valued and has an interpretable instance. -/
def RadicallyInterpretable (s : State L V) : Prop :=
  ∀ x, s.valueAt x ≠ ⊥ ∧ ∃ y, s.Shares x y ∧ interp y

instance [DecidableEq V] (s : State L V) : Decidable (RadicallyInterpretable interp s) := by
  unfold RadicallyInterpretable; infer_instance

/-- The Valuation/Interpretability Biconditional (3) of [chomsky-2001]: a feature is
uninterpretable exactly when it is unvalued. -/
def Biconditional (v : L → Flat V) : Prop := ∀ x, ¬ interp x ↔ v x = ⊥

instance [DecidableEq V] (v : L → Flat V) : Decidable (Biconditional interp v) := by
  unfold Biconditional; infer_instance

/-! ### Agree between unvalued features (7)–(8) -/

/-- The tense values. -/
inductive Tense
  | past | present
  deriving DecidableEq, Repr

/-- Three locations of one feature. -/
inductive Three
  | α | β | γ
  deriving DecidableEq, Repr, Fintype

/-- `α` and `β` unvalued, `γ` valued. -/
def three : State Three Tense := .lexical fun | .α => ⊥ | .β => ⊥ | .γ => ↑Tense.past

/-- (7)–(8): Agree between the unvalued `α` and `β`, then between `β` and the valued `γ`, values
`α` under feature sharing; under assignment the first step is vacuous and `α` stays unvalued. -/
theorem ex7_8 :
    ((three.agree .α .β).bind (·.agree .β .γ)).map (·.valueAt .α) = some ↑Tense.past ∧
      ((three.assign .α .β).bind (·.assign .β .γ)).map (·.valueAt .α) = some ⊥ := by
  decide

/-! ### Tense and nominative case in a finite clause (10), (17) -/

/-- The locations of T in a finite clause. -/
inductive Finite
  | tns | subject | verb
  deriving DecidableEq, Repr, Fintype

/-- Only T on Tns is interpretable; the subject's T is its case. -/
def Finite.Interp : Finite → Prop
  | .tns => True
  | _ => False

instance : DecidablePred Finite.Interp := fun x ↦ by
  cases x <;> unfold Finite.Interp <;> infer_instance

/-- iT[ ] on Tns, uT[ ] on the subject, uT past on the finite verb. -/
def finite : State Finite Tense := .lexical fun | .verb => ↑Tense.past | _ => ⊥

/-- (17): T on Tns probes the subject, valuing nothing, and then the finite verb, which values T
on Tns and the subject's case at once. -/
def finiteClause : Option (State Finite Tense) :=
  (finite.agree .tns .subject).bind (·.agree .tns .verb)

/-- (10): the lexicon of a finite clause has interpretable unvalued and uninterpretable valued T,
which the Biconditional (3) disallows. -/
theorem ex10 : ¬ Biconditional Finite.Interp finite.value := by decide

/-- (17): the first Agree leaves the subject's case unvalued, the second values it, and the result
is radically interpretable, as the lexicon is not. -/
theorem ex17 : (finite.agree .tns .subject).map (·.valueAt .subject) = some ⊥ ∧
    finiteClause.map (·.valueAt .subject) = some ↑Tense.past ∧
    (∀ s ∈ finiteClause, RadicallyInterpretable Finite.Interp s) ∧
    ¬ RadicallyInterpretable Finite.Interp finite := by
  decide

/-! ### Raising (16), (18) -/

/-- The locations of T in a raising construction: the infinitival clause and the finite clause
the subject raises into. -/
inductive Raising
  | infTns | subject | infVerb | tns | verb
  deriving DecidableEq, Repr, Fintype

/-- T is interpretable on the two Tns heads. -/
def Raising.Interp : Raising → Prop
  | .infTns | .tns => True
  | _ => False

instance : DecidablePred Raising.Interp := fun x ↦ by
  cases x <;> unfold Raising.Interp <;> infer_instance

/-- The infinitival verb's T is unvalued, the finite verb's past. -/
def raising : State Raising Tense := .lexical fun | .verb => ↑Tense.past | _ => ⊥

/-- (18): infinitival Tns probes the subject and then the infinitival verb, valuing nothing. -/
def infinitive : Option (State Raising Tense) :=
  (raising.agree .infTns .subject).bind (·.agree .infTns .infVerb)

/-- (16): the subject raises, and finite Tns probes it and then the finite verb. -/
def raised : Option (State Raising Tense) :=
  infinitive.bind (·.agree .tns .subject) |>.bind (·.agree .tns .verb)

/-- (16), (18): within the infinitive the subject's case stays unvalued, so the infinitive alone is
not radically interpretable; once the subject raises, the finite verb values its case and the
infinitival Tns, whose tense the finite clause thus determines. -/
theorem ex16_ex18 : infinitive.map (·.valueAt .subject) = some ⊥ ∧
    (∀ s ∈ infinitive, ¬ RadicallyInterpretable Raising.Interp s) ∧
    raised.map (·.valueAt .subject) = some ↑Tense.past ∧
    raised.map (·.valueAt .infTns) = some ↑Tense.past ∧
    ∀ s ∈ raised, RadicallyInterpretable Raising.Interp s := by
  decide

end PesetskyTorrego2007
