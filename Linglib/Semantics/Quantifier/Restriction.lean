module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.SymmDiff
public import Linglib.Semantics.Quantifier.Defs

/-!
# The restriction of a quantifier

A quantifier lives on a set when only the part of its argument inside that set matters. Its
restriction is the intersection of the sets it lives on, the individuals whose presence in the
argument can make a difference; on a finite universe the quantifier lives on its restriction, so
that the sets it lives on are exactly the supersets of the restriction. The restriction divides
into a positive restriction, the individuals whose addition can make the quantifier apply, and a
negative restriction, those whose removal can. On a finite universe a quantifier is monotone
exactly when its negative restriction is empty, and antitone exactly when its positive one is.
The complement and the inner negation of a quantifier have its restriction, with the positive and
the negative restriction exchanged. Flipping the scope within a set `N`, which takes `Q` to
`fun B ↦ Q (N ∆ B)`, keeps the restriction and exchanges the other two on `N`; inner negation
is the flip by the whole universe.

## Main results

* `Quantifier.livesOn_restriction`: on a finite universe a quantifier lives on its restriction.
* `Quantifier.negativeRestriction_eq_empty_iff`: on a finite universe a quantifier is monotone if
  and only if its negative restriction is empty.
* `Quantifier.positiveRestriction_symmDiff`: the positive restriction of `fun B ↦ Q (N ∆ B)` is
  `Q.positiveRestriction \ N ∪ Q.negativeRestriction ∩ N`.

## References

* [barwise-cooper-1981]
* [fagen-2026]
-/

@[expose] public section

namespace Quantifier

open Set

variable {α : Type*} {Q : Quantifier α} {A : Set α} {x : α}

/-! ### The restriction -/

variable (Q) in
/-- The restriction of a quantifier is the intersection of the sets it lives on. -/
def restriction : Set α := ⋂₀ {A | Q.LivesOn A}

theorem LivesOn.restriction_subset (h : Q.LivesOn A) : Q.restriction ⊆ A :=
  sInter_subset_of_mem h

theorem Det.Conservative.restriction_subset {d : Det α} (h : d.Conservative) (A : Set α) :
    (d A).restriction ⊆ A :=
  (h.livesOn A).restriction_subset

theorem notMem_restriction_iff : x ∉ Q.restriction ↔ Q.LivesOn {x}ᶜ := by
  simp only [restriction, mem_sInter, mem_ofPred_eq, not_forall, exists_prop]
  exact ⟨fun ⟨S, hS, hx⟩ ↦ hS.mono (subset_compl_singleton_iff.2 hx),
    fun h ↦ ⟨_, h, fun h' ↦ h' (mem_singleton x)⟩⟩

theorem mem_restriction_iff : x ∈ Q.restriction ↔ ∃ S, ¬ (Q S ↔ Q (S \ {x})) := by
  rw [← not_iff_not, notMem_restriction_iff, not_exists]
  simp only [not_not, LivesOn, ← sdiff_eq_compl_inter]

variable (Q) in
/-- On a finite universe a quantifier lives on its restriction. -/
theorem livesOn_restriction [Finite α] : Q.LivesOn Q.restriction := by
  classical
  have key : ∀ F : Finset α, (∀ x ∈ F, Q.LivesOn {x}ᶜ) → Q.LivesOn (↑F)ᶜ := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; simpa using Q.livesOn_univ
    | insert a F _ ih =>
      intro h
      rw [Finset.coe_insert, insert_eq, compl_union]
      exact (h a (Finset.mem_insert_self a F)).inter
        (ih fun x hx ↦ h x (Finset.mem_insert_of_mem hx))
  simpa using key (Q.restriction)ᶜ.toFinite.toFinset
    fun x hx ↦ notMem_restriction_iff.1 (by simpa using hx)

theorem livesOn_iff_restriction_subset [Finite α] : Q.LivesOn A ↔ Q.restriction ⊆ A :=
  ⟨LivesOn.restriction_subset, (Q.livesOn_restriction).mono⟩

/-! ### Positive and negative restrictions -/

variable (Q) in
/-- The positive restriction of a quantifier holds the individuals whose addition turns a set the
quantifier does not apply to into one it applies to. -/
def positiveRestriction : Set α := {x | ∃ S, ¬ Q S ∧ Q (insert x S)}

variable (Q) in
/-- The negative restriction of a quantifier holds the individuals whose removal turns a set the
quantifier does not apply to into one it applies to. -/
def negativeRestriction : Set α := {x | ∃ S, ¬ Q S ∧ Q (S \ {x})}

theorem mem_positiveRestriction_iff :
    x ∈ Q.positiveRestriction ↔ ∃ S, Q S ∧ ¬ Q (S \ {x}) := by
  constructor
  · rintro ⟨S, hS, hxS⟩
    have hx : x ∉ S := fun h ↦ hS (by rwa [insert_eq_of_mem h] at hxS)
    refine ⟨insert x S, hxS, ?_⟩
    rwa [insert_sdiff_of_mem _ (mem_singleton x), sdiff_singleton_eq_self hx]
  · rintro ⟨S, hS, hSx⟩
    have hx : x ∈ S := by_contra fun h ↦ hSx (by rwa [sdiff_singleton_eq_self h])
    refine ⟨S \ {x}, hSx, ?_⟩
    rwa [insert_sdiff_singleton, insert_eq_of_mem hx]

theorem mem_negativeRestriction_iff :
    x ∈ Q.negativeRestriction ↔ ∃ S, Q S ∧ ¬ Q (insert x S) := by
  constructor
  · rintro ⟨S, hS, hSx⟩
    have hx : x ∈ S := by_contra fun h ↦ hS (by rwa [sdiff_singleton_eq_self h] at hSx)
    refine ⟨S \ {x}, hSx, ?_⟩
    rwa [insert_sdiff_singleton, insert_eq_of_mem hx]
  · rintro ⟨S, hS, hxS⟩
    have hx : x ∉ S := fun h ↦ hxS (by rwa [insert_eq_of_mem h])
    refine ⟨insert x S, hxS, ?_⟩
    rwa [insert_sdiff_of_mem _ (mem_singleton x), sdiff_singleton_eq_self hx]

variable (Q) in
/-- The positive and negative restrictions of a quantifier make up its restriction, on any
universe. -/
theorem positiveRestriction_union_negativeRestriction :
    Q.positiveRestriction ∪ Q.negativeRestriction = Q.restriction := by
  ext x
  rw [mem_union, mem_positiveRestriction_iff, mem_restriction_iff, negativeRestriction,
    mem_ofPred_eq, ← exists_or]
  exact exists_congr fun S ↦ by tauto

theorem positiveRestriction_subset_restriction : Q.positiveRestriction ⊆ Q.restriction :=
  Q.positiveRestriction_union_negativeRestriction ▸ subset_union_left

theorem negativeRestriction_subset_restriction : Q.negativeRestriction ⊆ Q.restriction :=
  Q.positiveRestriction_union_negativeRestriction ▸ subset_union_right

/-! ### Negation

A quantifier and its complement live on the same sets, and so do a quantifier and its inner
negation. Each negation exchanges the positive and the negative restriction, so the dual has the
same two restrictions as the quantifier. -/

theorem livesOn_compl_iff : Qᶜ.LivesOn A ↔ Q.LivesOn A :=
  forall_congr' fun _ ↦ not_iff_not

@[simp] theorem restriction_compl : Qᶜ.restriction = Q.restriction := by
  simp only [restriction, livesOn_compl_iff]

@[simp] theorem positiveRestriction_compl : Qᶜ.positiveRestriction = Q.negativeRestriction := by
  ext x
  constructor
  · rintro ⟨S, hS, hx⟩
    have hQS : Q S := not_not.1 hS
    have hxS : x ∉ S := fun h ↦ hx (by rw [insert_eq_of_mem h]; exact hQS)
    have e : insert x S \ {x} = S := by ext y; by_cases hy : y = x <;> simp [hy, hxS]
    exact ⟨insert x S, hx, by rw [e]; exact hQS⟩
  · rintro ⟨S, hS, hx⟩
    refine ⟨S \ {x}, not_not.2 hx, fun h ↦ hS ?_⟩
    by_cases hxS : x ∈ S
    · have e : insert x (S \ {x}) = S := by ext y; by_cases hy : y = x <;> simp [hy, hxS]
      rwa [e] at h
    · have e : S \ {x} = S := by ext y; by_cases hy : y = x <;> simp [hy, hxS]
      rw [e] at hx
      exact (hS hx).elim

@[simp] theorem negativeRestriction_compl : Qᶜ.negativeRestriction = Q.positiveRestriction := by
  rw [← positiveRestriction_compl, compl_compl]

/-! ### Flips

Flipping the scope of a quantifier within a set `N` gives the quantifier `fun B ↦ Q (N ∆ B)`. It
lives on the same sets as `Q`, and its positive and negative restrictions are those of `Q` with
the two exchanged on `N`. Inner negation is the flip by the whole universe. -/

section Flip

open symmDiff

variable (N : Set α)

private theorem symmDiff_insert_of_notMem (hx : x ∉ N) (S : Set α) :
    N ∆ insert x S = insert x (N ∆ S) := by
  ext y
  simp only [mem_symmDiff, mem_insert_iff]
  by_cases hy : y = x
  · subst hy; tauto
  · tauto

private theorem symmDiff_insert_of_mem (hx : x ∈ N) (S : Set α) :
    N ∆ insert x S = (N ∆ S) \ {x} := by
  ext y
  simp only [mem_symmDiff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
  by_cases hy : y = x
  · subst hy; tauto
  · tauto

theorem livesOn_symmDiff_iff : LivesOn (fun B ↦ Q (N ∆ B)) A ↔ Q.LivesOn A := by
  have key (Q : Quantifier α) (h : Q.LivesOn A) : LivesOn (fun B ↦ Q (N ∆ B)) A := fun B ↦ by
    change Q (N ∆ B) ↔ Q (N ∆ (A ∩ B))
    rw [h (N ∆ B), h (N ∆ (A ∩ B))]
    congr! 1
    ext y; simp only [mem_inter_iff, mem_symmDiff]; tauto
  refine ⟨fun h ↦ ?_, key Q⟩
  have := key _ h
  simpa only [symmDiff_symmDiff_cancel_left] using this

@[simp] theorem restriction_symmDiff : restriction (fun B ↦ Q (N ∆ B)) = Q.restriction := by
  simp only [restriction, livesOn_symmDiff_iff]

/-- Flipping the scope within `N` exchanges the positive and the negative restriction on `N`. -/
theorem positiveRestriction_symmDiff :
    positiveRestriction (fun B ↦ Q (N ∆ B)) =
      Q.positiveRestriction \ N ∪ Q.negativeRestriction ∩ N := by
  ext x
  by_cases hx : x ∈ N
  · simp only [positiveRestriction, negativeRestriction, mem_union, mem_sdiff, mem_inter_iff,
      mem_ofPred_eq, hx, not_true_eq_false, and_false, and_true, false_or,
      symmDiff_insert_of_mem N hx]
    exact ⟨fun ⟨S, h⟩ ↦ ⟨N ∆ S, h⟩, fun ⟨S, h⟩ ↦ ⟨N ∆ S, by rwa [symmDiff_symmDiff_cancel_left]⟩⟩
  · simp only [positiveRestriction, negativeRestriction, mem_union, mem_sdiff, mem_inter_iff,
      mem_ofPred_eq, hx, not_false_eq_true, and_true, and_false, or_false,
      symmDiff_insert_of_notMem N hx]
    exact ⟨fun ⟨S, h⟩ ↦ ⟨N ∆ S, h⟩, fun ⟨S, h⟩ ↦ ⟨N ∆ S, by rwa [symmDiff_symmDiff_cancel_left]⟩⟩

theorem negativeRestriction_symmDiff :
    negativeRestriction (fun B ↦ Q (N ∆ B)) =
      Q.negativeRestriction \ N ∪ Q.positiveRestriction ∩ N := by
  have h := positiveRestriction_symmDiff (Q := Qᶜ) N
  rw [positiveRestriction_compl, negativeRestriction_compl] at h
  rw [← h, ← positiveRestriction_compl]; rfl

theorem innerNeg_eq_symmDiff_univ : Q.innerNeg = fun B ↦ Q (univ ∆ B) := funext fun B ↦ by
  rw [innerNeg_apply, ← top_eq_univ, top_symmDiff, hnot_eq_compl]

end Flip

@[simp] theorem positiveRestriction_innerNeg :
    Q.innerNeg.positiveRestriction = Q.negativeRestriction := by
  rw [innerNeg_eq_symmDiff_univ, positiveRestriction_symmDiff, sdiff_univ, empty_union,
    inter_univ]

@[simp] theorem negativeRestriction_innerNeg :
    Q.innerNeg.negativeRestriction = Q.positiveRestriction := by
  rw [← positiveRestriction_innerNeg, innerNeg_innerNeg]

theorem positiveRestriction_dual : Q.dual.positiveRestriction = Q.positiveRestriction := by
  rw [dual, positiveRestriction_compl, negativeRestriction_innerNeg]

theorem negativeRestriction_dual : Q.dual.negativeRestriction = Q.negativeRestriction := by
  rw [dual, negativeRestriction_compl, positiveRestriction_innerNeg]

theorem positiveRestriction_subset_sUnion : Q.positiveRestriction ⊆ ⋃₀ {S | Q S} := fun x hx ↦
  let ⟨S, hS, hSx⟩ := mem_positiveRestriction_iff.1 hx
  mem_sUnion.2 ⟨S, hS, by_contra fun h ↦ hSx (by rwa [sdiff_singleton_eq_self h])⟩

/-- The members of a minimal set of a quantifier are in its positive restriction. -/
theorem subset_positiveRestriction_of_minimal {S : Set α} (h : Minimal Q S) :
    S ⊆ Q.positiveRestriction := fun x hx ↦
  mem_positiveRestriction_iff.2 ⟨S, h.prop, fun h' ↦ (h.2 h' sdiff_subset hx).2 (mem_singleton x)⟩

theorem negativeRestriction_eq_empty_of_monotone (hQ : Monotone Q) :
    Q.negativeRestriction = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, hS, h⟩ ↦ hS (hQ sdiff_subset h)

theorem positiveRestriction_eq_empty_of_antitone (hQ : Antitone Q) :
    Q.positiveRestriction = ∅ :=
  eq_empty_of_forall_notMem fun x ⟨S, hS, h⟩ ↦ hS (hQ (subset_insert x S) h)

/-- On a finite universe a quantifier is monotone exactly when its negative restriction is
empty. -/
theorem negativeRestriction_eq_empty_iff [Finite α] :
    Q.negativeRestriction = ∅ ↔ Monotone Q := by
  classical
  refine ⟨fun h A B hAB hA ↦ ?_, negativeRestriction_eq_empty_of_monotone⟩
  have step : ∀ x S, Q S → Q (insert x S) := fun x S hS ↦ not_not.1 fun hn ↦
    (eq_empty_iff_forall_notMem.1 h x) (mem_negativeRestriction_iff.2 ⟨S, hS, hn⟩)
  have key : ∀ F : Finset α, Q (A ∪ ↑F) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hA
    | insert a F _ ih => rw [Finset.coe_insert, union_insert]; exact step a _ ih
  have := key (B \ A).toFinite.toFinset
  rwa [Finite.coe_toFinset, union_sdiff_cancel hAB] at this

/-- On a finite universe a quantifier is antitone exactly when its positive restriction is
empty. -/
theorem positiveRestriction_eq_empty_iff [Finite α] :
    Q.positiveRestriction = ∅ ↔ Antitone Q := by
  classical
  refine ⟨fun h A B hAB hB ↦ ?_, positiveRestriction_eq_empty_of_antitone⟩
  have step : ∀ x S, Q S → Q (S \ {x}) := fun x S hS ↦ not_not.1 fun hn ↦
    (eq_empty_iff_forall_notMem.1 h x) (mem_positiveRestriction_iff.2 ⟨S, hS, hn⟩)
  have key : ∀ F : Finset α, Q (B \ ↑F) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hB
    | insert a F _ ih =>
      rw [Finset.coe_insert, insert_eq, union_comm, ← sdiff_sdiff]; exact step a _ ih
  have := key (B \ A).toFinite.toFinset
  rwa [Finite.coe_toFinset, sdiff_sdiff_cancel_left hAB] at this

end Quantifier
