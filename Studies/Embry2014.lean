/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Part.Extensions
public import Linglib.Semantics.Conditionals.Basic
public import Studies.Fine2012

/-!
# Embry (2014): A Difficulty for Fine's Exact Semantics for Counterfactuals

On the truth clause of [fine-2012] a counterfactual is true when every outcome of every exact
verifier of its antecedent contains a verifier of its consequent. An atomic statement such as
*it snowed* is determinable: each determinate snowfall verifies it. So where I ski after eight
inches and not after a hundred feet, *if it had snowed, I would have gone skiing* is false on
that clause, because of the outcome of the hundred-foot verifier (`not_would_snowed`), although
it is true of the eight-inch verifier taken alone (`would_eightInches`).

Bringing in closeness between worlds to set the hundred-foot verifier aside costs one of the
rules that the argument of [fine-2012] against the possible-worlds semantics relies on. Where
the antecedent-worlds approach the base world without a closest one, the conditional of
[lewis-1973b] does not satisfy Infinitary Conjunction (`infinitary_conjunction_fails`), and
Fine's alternative, on which the consequent must hold in the closest and in the stranded
antecedent-worlds, does not satisfy Disjunction (`disjunction_fails`).

## Implementation notes

The states of the snowfall model are partial assignments to two variables, the snowfall and
whether I ski, and an outcome of a snowfall adds the skiing it leads to. The paper states the
two counterexamples of its dilemma for the clauses that add exact verification to closeness;
they are stated here for the conditionals between propositions, on which those clauses rest.
In them the antecedent-worlds are indexed by the natural numbers, a larger index being closer,
and the base world is the single point of evaluation.

## References

* [embry-2014]
* [fine-2012]
* [lewis-1973b]
-/

@[expose] public section

namespace Embry2014

open Conditional Fine2012
open scoped IsBoundedComplete

/-! ### A determinable antecedent -/

/-- How much it snowed. -/
inductive Depth | none | eightInches | hundredFeet
  deriving DecidableEq

/-- The snowfall and whether I ski. -/
inductive V | snow | ski
  deriving DecidableEq

/-- The snowfall is a depth and skiing is yes or no. -/
abbrev Val : V → Type
  | .snow => Depth
  | .ski => Bool

/-- A state settles the snowfall, the skiing, both or neither. -/
abbrev St := ∀ v, Part (Val v)

/-- The state of its having snowed to the depth `d`. -/
def snowedTo (d : Depth) : St := Function.update ⊥ V.snow (Part.some d)

/-- The state of my skiing or not. -/
def skiing (b : Bool) : St := Function.update ⊥ V.ski (Part.some b)

/-- The outcome of a snowfall adds the skiing it leads to: I ski after eight inches only. -/
def outcome (_ : Unit) (t u : St) : Prop :=
  ∃ d, t = snowedTo d ∧
    u = Function.update (snowedTo d) V.ski (Part.some (decide (d = .eightInches)))

/-- *It snowed*, verified by each positive snowfall. -/
def snowed : SetSemiring (Fused St) :=
  SetSemiring.ofSet {st (snowedTo .eightInches)} + SetSemiring.ofSet {st (snowedTo .hundredFeet)}

/-- *I went skiing*. -/
def skis : SetSemiring (Fused St) := SetSemiring.ofSet {st (skiing true)}

theorem st_injective : Function.Injective (st : St → Fused St) :=
  fun _ _ h ↦ WithTop.coe_injective h

theorem snowedTo_injective : Function.Injective snowedTo := fun d e h ↦ by
  have := congrFun h V.snow
  simpa [snowedTo] using this

/-- An outcome of the snowfall `d` contains my skiing exactly when `d` is eight inches. -/
theorem inexact_skis_iff {d : Depth} {u : St} (hu : outcome () (snowedTo d) u) :
    Inexact skis u ↔ d = .eightInches := by
  obtain ⟨e, he, rfl⟩ := hu
  obtain rfl := snowedTo_injective he
  constructor
  · rintro ⟨c, hc, hcu⟩
    obtain rfl : c = skiing true := st_injective hc
    have := hcu V.ski true (by simp [skiing])
    simpa using this
  · rintro rfl
    refine ⟨skiing true, rfl, fun v ↦ ?_⟩
    cases v <;> simp [skiing, snowedTo]

-- true of the eight-inch verifier
theorem would_eightInches :
    () ∈ would outcome (SetSemiring.ofSet {st (snowedTo .eightInches)}) skis := by
  rintro a rfl t ht u hu
  obtain rfl := st_injective ht
  exact (inexact_skis_iff hu).mpr rfl

-- (3b)
theorem not_would_hundredFeet :
    () ∉ would outcome (SetSemiring.ofSet {st (snowedTo .hundredFeet)}) skis := fun h ↦
  absurd ((inexact_skis_iff ⟨_, rfl, rfl⟩).mp (h rfl _ rfl _ ⟨_, rfl, rfl⟩)) (by decide)

/-- (3a) is false on the truth clause of exact semantics: the outcome of the hundred-foot
verifier contains no skiing. -/
theorem not_would_snowed : () ∉ would outcome snowed skis := fun h ↦
  not_would_hundredFeet ((Set.ext_iff.mp would_add ()).mp h).2

/-! ### The dilemma for a repair by closeness -/

/-- The antecedent worlds, indexed by the naturals, a larger index being closer to the base
world. The base world is not among them. -/
abbrev closer (_ : Unit) : Preorder ℕ := Preorder.lift (OrderDual.toDual : ℕ → ℕᵒᵈ)

theorem closer_le {a b : ℕ} : (closer ()).le a b ↔ b ≤ a := Iff.rfl

instance (i : Unit) : Std.Total (closer i).le := ⟨fun a b ↦ le_total b a⟩

/-- Infinitary Conjunction fails for the conditional of [lewis-1973b]: from the supposition that
Linus is longer than an inch it follows, for each bound, that he is not longer than it, and it
does not follow that he is not longer than any of them. -/
theorem infinitary_conjunction_fails :
    (∀ n, () ∈ variablyStrictImp (fun _ ↦ Set.univ) closer Set.univ {m | n ≤ m}) ∧
      () ∉ variablyStrictImp (fun _ ↦ Set.univ) closer Set.univ (⋂ n, {m | n ≤ m}) := by
  refine ⟨fun n ↦ mem_variablyStrictImp_iff_exists.mpr
    (.inr ⟨n, ⟨trivial, trivial⟩, fun w _ hw ↦ hw⟩), fun h ↦ ?_⟩
  rcases mem_variablyStrictImp_iff_exists.mp h with h | ⟨v, -, hv⟩
  · exact Set.eq_empty_iff_forall_notMem.mp h 0 ⟨trivial, trivial⟩
  · have := Set.mem_iInter.mp (hv v ⟨trivial, trivial⟩ (closer_le.mpr le_rfl)) (v + 1)
    exact absurd this (by simp)

/-- Fine's alternative: the consequent is true in all of the closest antecedent-worlds and in
all of the stranded ones, those with no closest antecedent-world at least as close. -/
def strandedImp {I W : Type*} (ord : I → Preorder W) (p q : Set W) : Set I :=
  {i | (ord i).minimals p ⊆ q ∧
    ∀ x ∈ p, (¬ ∃ m ∈ (ord i).minimals p, (ord i).le m x) → x ∈ q}

private theorem minimals_eq_empty {p : Set ℕ} (h : ∀ a ∈ p, a + 1 ∈ p) :
    (closer ()).minimals p = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun a ha ↦
    absurd ((Preorder.mem_minimals_iff.mp ha).2 (h a (Preorder.mem_minimals_iff.mp ha).1)
      (closer_le.mpr (Nat.le_succ a))) (by simp [closer_le])

/-- Disjunction fails for Fine's alternative. -/
theorem disjunction_fails :
    () ∈ strandedImp closer {0, 1} {m | 1 ≤ m} ∧
      () ∈ strandedImp closer {m | 1 ≤ m} {m | 1 ≤ m} ∧
      () ∉ strandedImp closer ({0, 1} ∪ {m | 1 ≤ m}) {m | 1 ≤ m} := by
  have h1 : (1 : ℕ) ∈ (closer ()).minimals {0, 1} := by
    refine Preorder.mem_minimals_iff.mpr ⟨.inr rfl, fun b hb _ ↦ closer_le.mpr ?_⟩
    rcases hb with rfl | rfl <;> simp
  refine ⟨⟨fun a ha ↦ ?_, fun x hx hs ↦ ?_⟩, ⟨fun a ha ↦ (Preorder.mem_minimals_iff.mp ha).1,
    fun x hx _ ↦ hx⟩, fun h ↦ ?_⟩
  · obtain ⟨ha₁, ha₂⟩ := Preorder.mem_minimals_iff.mp ha
    rcases ha₁ with rfl | rfl
    · exact absurd (closer_le.mp (ha₂ (b := 1) (.inr rfl) (closer_le.mpr (Nat.zero_le 1))))
        (by simp)
    · exact Nat.le_refl 1
  · refine (hs ⟨1, h1, closer_le.mpr ?_⟩).elim
    rcases hx with rfl | rfl <;> simp
  · have h0 : (closer ()).minimals ({0, 1} ∪ {m : ℕ | 1 ≤ m}) = ∅ :=
      minimals_eq_empty fun a _ ↦ .inr (Nat.succ_le_succ (Nat.zero_le a))
    exact absurd (h.2 0 (.inl (.inl rfl)) (by rw [h0]; rintro ⟨m, hm, -⟩; exact hm)) (by simp)

end Embry2014
