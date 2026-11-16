module

public import Linglib.Semantics.Exhaustification.InnocentExclusion

/-!
# Exhaustifying a disjunction with a conjunctive disjunct

Among the worlds of `(a ∧ b) ∨ c`, those verifying a minimal set of the atoms `a`, `b`, `c` are
[the worlds of `(a ∧ b ∧ ¬c) ∨ (c ∧ ¬a ∧ ¬b)`](##Exhaustification.exhMW_inter_union), each
disjunct exclusive of the material of the other: the strongly exhaustive reading, under which the
second premise `a` of the illusory inference from disjunction leaves only worlds of `b`. This is
the example *either Mary came, or both Peter and Sue did* of [spector-2016], whose shortcut is to
compute innocent exclusion from the minimal worlds over the atoms: it yields the reading [against
the closure of the atoms under conjunction and
disjunction](##Exhaustification.exhIE_latticeClosure_inter_union), and against [any part of that
closure containing the atoms, `a ∧ c` and `b ∧ c`](##Exhaustification.exhIE_inter_union).

## References

* [spector-2016]
* [spector-2007]
* [sable-meyer-mascarenhas-2022]
* [bade-picat-chung-mascarenhas-2022]
-/

@[expose] public section

namespace Exhaustification

open Set

variable {W : Type*} {ALT : Set (Set W)} {a b c : Set W}

theorem exhMW_inter_union (hc : (c \ (a ∪ b)).Nonempty) :
    exhMW {a, b, c} ((a ∩ b) ∪ c) = ((a ∩ b) \ c) ∪ (c \ (a ∪ b)) := by
  obtain ⟨y, hyc, hyab⟩ := hc
  ext u
  simp only [mem_exhMW, MinimalFor, Set.subset_def, Preorder.mem_satisfied, mem_insert_iff,
    mem_singleton_iff, and_imp, forall_eq_or_imp, forall_eq, true_or, or_true, true_and,
    mem_union, mem_inter_iff, mem_sdiff] at hyab ⊢
  refine ⟨fun ⟨hu, hmin⟩ ↦ ?_, fun hu ↦ ⟨by tauto, fun v hv ↦ by tauto⟩⟩
  have hy := hmin (j := y) (.inr hyc)
  tauto

/-- Innocent exclusion strengthens `(a ∧ b) ∨ c` to `(a ∧ b ∧ ¬c) ∨ (c ∧ ¬a ∧ ¬b)` against any
alternatives built from `a`, `b`, `c` by conjunction and disjunction that include the three and the
conjunctions `a ∧ c` and `b ∧ c`. -/
theorem exhIE_inter_union (h₁ : {a, b, c, a ∩ c, b ∩ c} ⊆ ALT)
    (h₂ : ALT ⊆ latticeClosure {a, b, c}) (hc : (c \ (a ∪ b)).Nonempty) :
    exhIE ALT ((a ∩ b) ∪ c) = ((a ∩ b) \ c) ∪ (c \ (a ∪ b)) := by
  have hMW : exhMW ALT ((a ∩ b) ∪ c) = ((a ∩ b) \ c) ∪ (c \ (a ∪ b)) := by
    rw [exhMW_eq_of_subset_latticeClosure (fun q hq ↦ h₁ (by grind)) h₂, exhMW_inter_union hc]
  rw [(exhIE_eq_exhMW_iff ALT _).2 fun u hu hmin ↦ ?_, hMW]
  rw [hMW] at hmin ⊢
  by_cases hac : u ∈ a ∩ c
  · exact ⟨a ∩ c, h₁ (by simp), hac, by grind⟩
  · exact ⟨b ∩ c, h₁ (by simp), by grind, by grind⟩

theorem exhIE_latticeClosure_inter_union (hc : (c \ (a ∪ b)).Nonempty) :
    exhIE (latticeClosure {a, b, c}) ((a ∩ b) ∪ c) = ((a ∩ b) \ c) ∪ (c \ (a ∪ b)) := by
  rw [exhIE_latticeClosure _ _ (by simp), exhMW_inter_union hc]

end Exhaustification
