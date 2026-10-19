module

public import Studies.Heinamaki1974
public import Linglib.Semantics.Aspect.Defs

/-!
# Karttunen (1974): Until

Karttunen argues that English has two *until*s. Durative *until* modifies a durative sentence and
marks the minimum length of its interval: some run-time of `A` reaches a time of `B`. Punctual
*until* is a negative polarity item whose logical form is that of *before*, *A not until T* being
the negation of Anscombe's quantificational *before* (33). What distinguishes it from *before* is
a pragmatic presupposition of lateness, *A before T or A when T* (34), with Heinämäki's *when*.
Since the logical form holds of a clause that never happens, the commitment to *A when T* follows
from assertion and presupposition by disjunctive syllogism (36), which is why *Nancy didn't get
married until she died* (23) commits the speaker to a marriage at her death.

## Main statements

* `notUntil_iff`, `not_notUntil_iff`: `T` holds or has held at every time of `A`, and the denial
  is *A before T*.
* `notUntil_empty`: the logical form holds of a clause that never happens.
* `notUntil_when`: assertion and presupposition together yield *A when T*.
* `notUntil_iff_when_of_presupposition`: for point events the two logical forms coincide given
  the presupposition, as with Finnish *vasta* and German *erst* (38)–(39).

## References

* [karttunen-1974]
* [anscombe-1964]
* [heinamaki-1974]
-/

@[expose] public section

namespace Karttunen1974

open Tense Anscombe1964 Heinamaki1974

variable {T : Type*} [LinearOrder T] (A B : Set (NonemptyInterval T))

/-- Durative *A until B* holds when some run-time of `A` reaches a time of `B`. -/
def until_ : Prop := ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- Punctual *A not until B*, (33), is *A not before B*. -/
def notUntil : Prop := ¬ Tense.beforeEver A B

/-- The presupposition of lateness, (34), is *A before B or A when B*. -/
def presupposition : Prop := Tense.beforeEver A B ∨ when_ A B

theorem until_veridical_complement : until_ A B → ∃ t, t ∈ timeTrace B :=
  fun ⟨t, _, ht⟩ ↦ ⟨t, ht⟩

/-- Every time of `A` is one at which `B` holds or has held. -/
theorem notUntil_iff : notUntil A B ↔ timeTrace A ⊆ upperClosure (timeTrace B) := by
  rw [notUntil, beforeEver_iff_not_subset_upperClosure, not_not]

/-- Denying *A not until B* is asserting *A before B*, (30)–(31). -/
theorem not_notUntil_iff : ¬ notUntil A B ↔ Tense.beforeEver A B := not_not

/-- The logical form holds of a clause that never happens. -/
theorem notUntil_empty : notUntil (∅ : Set (NonemptyInterval T)) B :=
  fun ⟨_, ⟨_, hi, _⟩, _⟩ ↦ hi

/-- By disjunctive syllogism, (36), assertion and presupposition together yield *A when B*. -/
theorem notUntil_when (h : notUntil A B) (hp : presupposition A B) : when_ A B :=
  hp.resolve_left h

/-- For point events under the presupposition, *A not until B* and *A when B* — the logical
forms of Finnish *ennenkuin* and *vasta*, (39) — say the same. -/
theorem notUntil_iff_when_of_presupposition (a b : T)
    (hp : presupposition {NonemptyInterval.pure a} {NonemptyInterval.pure b}) :
    notUntil {NonemptyInterval.pure a} {NonemptyInterval.pure b} ↔
      when_ {NonemptyInterval.pure a} {NonemptyInterval.pure b} := by
  simp only [notUntil, Tense.beforeEver, when_, presupposition, mem_timeTrace_pure,
    exists_eq_left, forall_eq] at hp ⊢
  exact ⟨hp.resolve_left, fun h ↦ by subst h; exact lt_irrefl _⟩

/-! ### The durative selectional restriction -/

open Aspect

/-- Durative *until* selects a durative, atelic main clause — the classes with the
subinterval property. -/
def SatisfiesDurativeRestriction (c : VendlerClass) : Prop :=
  c.telicity = .atelic ∧ c.duration = .durative

instance : DecidablePred SatisfiesDurativeRestriction := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

theorem satisfiesDurativeRestriction_iff (c : VendlerClass) :
    SatisfiesDurativeRestriction c ↔ c = .state ∨ c = .activity := by
  cases c <;> decide

end Karttunen1974
