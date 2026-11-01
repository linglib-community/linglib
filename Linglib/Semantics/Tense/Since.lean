module

public import Linglib.Semantics.Presupposition.Strawson

/-!
# Temporal *since*

This file defines Iatridou's temporal *since*, in the form von Fintel gives it: *it has been five
years since p* presupposes that `p` held at the time five years before the evaluation time and
asserts that it has not held since. It is [Strawson
anti-additive](##Tense.isStrawsonAntiAdditive_since) in `p`, but [not classically downward
entailing](##Tense.not_antitone_posSupport_since), since its presupposition can fail at a
stronger argument, and [not Strawson upward entailing](##Tense.not_isStrawsonUE_since).

## References

* [von-fintel-1999]
-/

@[expose] public section

namespace Tense

open Presupposition Trivalent

section Since

variable {T : Type*} [LinearOrder T] (ago : T → T)

open Classical in
/-- *It has been five years since p* presupposes that `p` held at the time `ago t` five years
before the evaluation time `t` and asserts that it has not held since ([von-fintel-1999], after
Iatridou). -/
noncomputable def since (p : Set T) : T → SignType :=
  {t | ago t ∈ p}.indicator fun t ↦ SignType.ofProp (Disjoint (Set.Ioc (ago t) t) p)

theorem isStrawsonAntiAdditive_since : IsStrawsonAntiAdditive (since ago) :=
  .of_isAntiAdditive (a := fun p t ↦ Disjoint (Set.Ioc (ago t) t) p)
    (fun _ _ ↦ funext fun _ ↦ propext Set.disjoint_union_right)
    fun p t h ↦ by by_cases ht : ago t ∈ p <;> simp_all [since]

theorem isStrawsonDE_since : IsStrawsonDE (since ago) :=
  (isStrawsonAntiAdditive_since ago).isStrawsonDE

theorem not_antitone_posSupport_since :
    ¬ Antitone fun p : Set ℤ ↦ posSupport (since (· - 5) p) :=
  not_antitone_posSupport (p := ∅) (q := {-5}) (w := 0) (Set.empty_subset _)
    (by simp [since, Set.disjoint_singleton_right]) (by simp [since])

/-- *It's been five years since I saw an eagle* does not Strawson-entail *it's been five years
since I saw a bird*, defined and false when a sparrow was seen since. -/
theorem not_isStrawsonUE_since : ¬ IsStrawsonUE (since (T := ℤ) (· - 5)) :=
  not_isStrawsonUE (p := {-5}) (q := .univ) (w := 0) (Set.subset_univ _)
    (by simp [since, Set.disjoint_singleton_right])
    (by simpa [since] using Set.nonempty_iff_ne_empty.1 ⟨0, by simp⟩)

end Since

end Tense
