module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Reference.Definite
public import Linglib.Semantics.Tense.Quantificational

/-!
# Pronominal tense

Read pronominally, after Partee, a tense refers to a time as a pronoun refers to an individual.
It denotes the value of a temporal variable and presupposes that this time stands to the
evaluation time, the value of a second variable, in a relation, as a pronoun presupposes that
its referent has its φ-features. `Tense.pronoun R k j` is this denotation, a definite over times
(`Definite`) as the denotation of a personal pronoun is a definite over individuals. The past
and the present are the pronouns of the relations of their cells (`Tense.toSetRel`), the zero
tense of Kratzer, a variable with no presupposition, is the pronoun of the unconstrained cell
`⊤`, and a tense whose reference time is an interval is the pronoun of the relation of an Allen
cell (`Allen.toSetRel`).
One denotation serves the deictic, the anaphoric and the bound use, binding being abstraction
over the assignment (`Λ[n]`), and a free evaluation index is by convention
the utterance time. Bound by an existential quantifier, a pronominal tense is the
quantificational tense of its cell.

## Main definitions

* `Tense.pronoun`: the pronominal tense of a relation between times, with a referential and an
  evaluation index.

## Main statements

* `Tense.exists_pronoun_iff_diamond`: the existential closure of a pronominal tense is the
  quantificational tense of its relation at the evaluation time.

## References

* [partee-1973]
* [heim-1994-comments]
* [kratzer-1998]
* [sharvit-2014]
-/

@[expose] public section

namespace Tense

open ModalLogic
open scoped Assignment
open scoped SetRel

variable {W T : Type*} {R : SetRel T T} {C : Finset Ordering} {k j : ℕ} {g : ℕ → T} {w : W}

/-- The pronominal tense with relation `R`, referential index `k` and evaluation index `j` denotes
the time of `k` where the time of `j` stands in `R` to it, and nothing elsewhere. -/
def pronoun (R : SetRel T T) (k j : ℕ) : Definite (ℕ → T) W T :=
  fun g _ ↦ ⟨g j ~[R] g k, fun _ ↦ g k⟩

@[simp] theorem pronoun_dom : (pronoun (W := W) R k j g w).Dom ↔ g j ~[R] g k := Iff.rfl

@[simp] theorem mem_pronoun {t : T} :
    t ∈ pronoun (W := W) R k j g w ↔ g j ~[R] g k ∧ g k = t :=
  ⟨fun ⟨h, ht⟩ ↦ ⟨h, ht⟩, fun ⟨h, ht⟩ ↦ ⟨h, ht⟩⟩

/-- A pronominal tense with its referential index bound by an existential quantifier is the
quantificational tense of its relation at the evaluation time. -/
theorem exists_pronoun_iff_diamond (hkj : k ≠ j) (P : T → Prop) :
    (∃ t, Λ[k] (fun g ↦ ∃ s ∈ pronoun (W := W) R k j g w, P s) g t) ↔ ◇[R] P (g j) := by
  simp [Diamond, Function.update_of_ne hkj.symm]

instance [Decidable (g j ~[R] g k)] : Decidable (pronoun (W := W) R k j g w).Dom :=
  inferInstanceAs (Decidable (g j ~[R] g k))

@[simp] theorem pronoun_dom_const [LinearOrder T] (t₀ : T) :
    (pronoun (W := W) (toSetRel C) k j (Function.const ℕ t₀) w).Dom ↔ .eq ∈ C := by
  simp

end Tense
