/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Order.Argmax
public import Linglib.Core.Order.PiLex
public import Mathlib.Algebra.Order.Group.PiLex

/-!
# Violation profiles

The marks of a candidate under constraints in rank order form its *violation profile*
([riggle-2009b]), and
profiles are compared lexicographically: strict domination is mathlib's lexicographic order on
`Fin n → ℕ`, position `0` the most dominant constraint. A profile along a list of constraints is
`ViolationProfile.ofList`, and the harmony order it induces on candidates is the order
bidirectional optimality theory evaluates over, well-founded on any candidate set.

## References

* [prince-smolensky-1993]
* [blutner-2000]
* [riggle-2009b]
-/

@[expose] public section

namespace OptimalityTheory

/-- A fixed-length violation profile, the violation vector `Fin n → ℕ` under its lexicographic
order. -/
abbrev ViolationProfile (n : ℕ) := Lex (Fin n → ℕ)

namespace ViolationProfile

variable {C : Type*} {n : ℕ}

/-- The violation profile of a candidate under constraints in rank order, position `0` most
dominant. -/
abbrev of (cs : ConstraintSet C (Fin n)) (c : C) : ViolationProfile n := toLex (cs.marks c)

/-- The violation profile of a candidate under a list of constraints in rank order. -/
def ofList (ranking : List (Constraint C)) : C → ViolationProfile ranking.length := of ranking.get

theorem of_lt_iff {cs : ConstraintSet C (Fin (n + 1))} {d e : C} :
    of cs d < of cs e ↔
      cs 0 d < cs 0 e ∨ cs 0 d = cs 0 e ∧ of (Fin.tail cs) d < of (Fin.tail cs) e :=
  Pi.toLex_lt_toLex_iff_succ _ _

/-- A candidate is minimal under ranked constraints iff it is minimal under the lower constraints
among the candidates doing best on the top constraint. -/
theorem minimalFor_of_iff {P : C → Prop} {cs : ConstraintSet C (Fin (n + 1))} {c : C} :
    MinimalFor P (of cs) c ↔ MinimalFor (MinimalFor P (cs 0)) (of (Fin.tail cs)) c := by
  simp only [minimalFor_iff_forall_lt, of_lt_iff]
  refine ⟨fun ⟨hc, hmin⟩ ↦ ⟨⟨hc, fun d hd ↦ hmin (.inl hd)⟩, fun d hd ⟨hdR, hdF⟩ ↦ ?_⟩,
    fun ⟨⟨hc, hF⟩, hmin⟩ ↦ ⟨hc, fun d hd hdR ↦ ?_⟩⟩
  · have heq : cs 0 d = cs 0 c :=
      (not_lt.1 fun h ↦ hdF h hc).antisymm (not_lt.1 fun h ↦ hmin (.inl h) hdR)
    exact hmin (.inr ⟨heq, hd⟩) hdR
  · rcases hd with hd | ⟨heq, hd⟩
    · exact hF hd hdR
    · exact hmin hd ⟨hdR, fun e he ↦ hF (heq ▸ he)⟩

theorem ofList_cons_lt_iff {F : Constraint C} {Fs : List (Constraint C)} {d e : C} :
    ofList (F :: Fs) d < ofList (F :: Fs) e ↔
      F d < F e ∨ F d = F e ∧ ofList Fs d < ofList Fs e :=
  of_lt_iff

theorem not_ofList_nil_lt {d e : C} : ¬ ofList [] d < ofList [] e := fun ⟨i, _⟩ ↦ i.elim0

theorem minimalFor_ofList_nil {P : C → Prop} {c : C} : MinimalFor P (ofList []) c ↔ P c :=
  ⟨(·.1), fun h ↦ minimalFor_iff_forall_lt.2 ⟨h, fun _ hd ↦ absurd hd not_ofList_nil_lt⟩⟩

theorem minimalFor_ofList_cons {P : C → Prop} {F : Constraint C} {Fs : List (Constraint C)}
    {c : C} : MinimalFor P (ofList (F :: Fs)) c ↔ MinimalFor (MinimalFor P F) (ofList Fs) c :=
  minimalFor_of_iff

/-- The profile is strictly monotone in a candidate order when every constraint is monotone and
some constraint separates each strict pair. -/
theorem strictMono_ofList [Preorder C] {ranking : List (Constraint C)}
    (hmono : ∀ c ∈ ranking, Monotone c) (hsep : ∀ ⦃p q⦄, p < q → ∃ c ∈ ranking, c p < c q) :
    StrictMono (ofList ranking) := fun p q hpq ↦ by
  refine Pi.toLex_strictMono (Pi.lt_def.2 ⟨fun i ↦ hmono _ (List.get_mem ..) hpq.le, ?_⟩)
  obtain ⟨c, hc, hlt⟩ := hsep hpq
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hc
  exact ⟨i, hlt⟩

end ViolationProfile

end OptimalityTheory
