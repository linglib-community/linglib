module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Reference.Nominal
public import Linglib.Semantics.Tense.Quantificational

/-!
# Pronominal tense

Read pronominally, after Partee, a tense refers to a time as a pronoun refers to an individual.
It denotes the value of a temporal variable and presupposes that this time stands to the
evaluation time, the value of a second variable, in a position of its cell, as a pronoun
presupposes that its referent has its φ-features. `Tense.pronoun C k j` is this denotation, a
nominal over times (`Nominal`) as the denotation of a personal pronoun is a nominal
over individuals. The past and the present are the pronouns of their cells, and the zero tense
of Kratzer, a variable with no presupposition, is the pronoun of the unconstrained cell `⊤`.
One denotation serves the deictic, the anaphoric and the bound use, binding being abstraction
over the assignment (`Λ[n]`), and a free evaluation index is by convention
the utterance time. Bound by an existential quantifier, a pronominal tense is the
quantificational tense of its cell.

## Main definitions

* `Tense.pronoun`: the pronominal tense of a cell, with a referential and an evaluation index.

## Main statements

* `Tense.exists_pronoun_iff_diamond`: the existential closure of a pronominal tense is the
  quantificational tense of its cell at the evaluation time.

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

variable {W T : Type*} {C : Finset Ordering} {k j : ℕ} {g : ℕ → T} {w : W}

section LT

variable [LT T]

/-- The pronominal tense with cell `C`, referential index `k` and evaluation index `j` denotes
the time of `k` where it stands to the time of `j` in a position of `C`, and nothing
elsewhere. -/
def pronoun (C : Finset Ordering) (k j : ℕ) : Nominal (ℕ → T) W T :=
  fun g _ ↦ ⟨g j ~[toSetRel C] g k, fun _ ↦ g k⟩

@[simp] theorem pronoun_dom : (pronoun (W := W) C k j g w).Dom ↔ g j ~[toSetRel C] g k := Iff.rfl

@[simp] theorem mem_pronoun {t : T} :
    t ∈ pronoun (W := W) C k j g w ↔ g j ~[toSetRel C] g k ∧ g k = t :=
  ⟨fun ⟨h, ht⟩ ↦ ⟨h, ht⟩, fun ⟨h, ht⟩ ↦ ⟨h, ht⟩⟩

/-- A pronominal tense with its referential index bound by an existential quantifier is the
quantificational tense of its cell at the evaluation time. -/
theorem exists_pronoun_iff_diamond (hkj : k ≠ j) (P : T → Prop) :
    (∃ t, Λ[k] (fun g ↦ ∃ s ∈ pronoun (W := W) C k j g w, P s) g t) ↔
      ◇[toSetRel C] P (g j) := by
  simp [Diamond, Function.update_of_ne hkj.symm]

end LT

section LinearOrder

variable [LinearOrder T]

instance : Decidable (pronoun (W := W) C k j g w).Dom :=
  inferInstanceAs (Decidable (g j ~[toSetRel C] g k))

@[simp] theorem pronoun_dom_const (t₀ : T) :
    (pronoun (W := W) C k j (Function.const ℕ t₀) w).Dom ↔ .eq ∈ C := by
  simp

end LinearOrder

end Tense
