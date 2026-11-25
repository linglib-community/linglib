module

public import Linglib.Semantics.Quantifier.Basic

/-!
# Permutation invariance

A quantifier or a determiner denotation is quantity invariant when no permutation of the universe
changes it, so that it cannot tell the individuals of the universe apart. This is Mostowski's
condition on a quantifier, on a single universe.

We prove that quantity invariance is preserved by the Boolean operations, by inner negation and
by the dual, and that *every*, *some* and *no* are quantity invariant. Among the conservative,
quantity-invariant determiner denotations, van Benthem characterizes *some* and *no* by their
properties as relations between sets.

## Main results

* `Quantifier.Det.Conservative.iff_inter_nonempty`: *some* is the only conservative,
  quantity-invariant determiner denotation that is symmetric and quasi-reflexive and holds of a
  singleton but not everywhere.
* `Quantifier.Det.Conservative.iff_disjoint`: *no* is the only conservative, quantity-invariant
  determiner denotation that is symmetric and quasi-universal and fails of a singleton but holds
  somewhere.
* `Quantifier.exists_det_apply_eq_iff_livesOn`: the quantifiers `d A` of the conservative,
  quantity-invariant determiner denotations are the quantifiers that live on a set and that the
  permutations fixing that set leave unchanged.

## References

* [mostowski-1957]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*}

/-- A quantifier is quantity invariant when no permutation of the universe changes it,
`Q (σ ⁻¹' B) ↔ Q B`: [mostowski-1957]'s invariance condition on a quantifier limited to a universe,
of which `Det.QuantityInvariant` is the counterpart for determiner denotations. -/
def QuantityInvariant (Q : Quantifier α) : Prop :=
  ∀ (σ : Equiv.Perm α) (B : Set α), Q (σ ⁻¹' B) ↔ Q B

section QuantityInvariant

variable {Q Q' : Quantifier α}

theorem QuantityInvariant.compl (h : Q.QuantityInvariant) : Qᶜ.QuantityInvariant :=
  fun σ B ↦ not_congr (h σ B)

theorem QuantityInvariant.inf (h : Q.QuantityInvariant) (h' : Q'.QuantityInvariant) :
    (Q ⊓ Q').QuantityInvariant :=
  fun σ B ↦ and_congr (h σ B) (h' σ B)

theorem QuantityInvariant.sup (h : Q.QuantityInvariant) (h' : Q'.QuantityInvariant) :
    (Q ⊔ Q').QuantityInvariant :=
  fun σ B ↦ or_congr (h σ B) (h' σ B)

end QuantityInvariant

namespace Det

variable {d d' : Det α} {A B : Set α}

/-- A determiner denotation is quantity invariant when no permutation of the universe changes it,
`d (σ ⁻¹' A) (σ ⁻¹' B) ↔ d A B`, the requirement of [mostowski-1957] that a quantifier not
distinguish the elements of the universe. -/
def QuantityInvariant (d : Det α) : Prop :=
  ∀ (σ : Equiv.Perm α) (A B : Set α), d (σ ⁻¹' A) (σ ⁻¹' B) ↔ d A B

theorem QuantityInvariant.compl (h : d.QuantityInvariant) : dᶜ.QuantityInvariant :=
  fun σ A B ↦ not_congr (h σ A B)

theorem QuantityInvariant.innerNeg (h : d.QuantityInvariant) : d.innerNeg.QuantityInvariant :=
  fun σ A B ↦ h σ A Bᶜ

theorem QuantityInvariant.dual (h : d.QuantityInvariant) : d.dual.QuantityInvariant :=
  h.innerNeg.compl

theorem QuantityInvariant.inf (h : d.QuantityInvariant) (h' : d'.QuantityInvariant) :
    (d ⊓ d').QuantityInvariant :=
  fun σ A B ↦ and_congr (h σ A B) (h' σ A B)

theorem QuantityInvariant.sup (h : d.QuantityInvariant) (h' : d'.QuantityInvariant) :
    (d ⊔ d').QuantityInvariant :=
  fun σ A B ↦ or_congr (h σ A B) (h' σ A B)

/-- The section of a quantity-invariant determiner denotation at the universe is quantity
invariant. -/
theorem QuantityInvariant.apply_univ (h : d.QuantityInvariant) : (d .univ).QuantityInvariant :=
  fun σ B ↦ by simpa using h σ .univ B

/-! ### The logical determiners -/

theorem quantityInvariant_every : (every : Det α).QuantityInvariant :=
  fun σ _ _ ↦ σ.surjective.preimage_subset_preimage_iff

theorem quantityInvariant_some : (Det.some : Det α).QuantityInvariant :=
  fun σ A B ↦ σ.surjective.nonempty_preimage (s := A ∩ B)

theorem quantityInvariant_no : (no : Det α).QuantityInvariant := quantityInvariant_every.innerNeg

/-! ### Relational characterizations -/

private theorem preimage_swap_singleton [DecidableEq α] (x a : α) :
    Equiv.swap x a ⁻¹' {a} = {x} := by
  ext y; simp [Equiv.swap_apply_eq_iff]

/-- *Some* is the only symmetric quasi-reflexive conservative determiner denotation that is
permutation invariant and holds of a singleton but not everywhere ([van-benthem-1984],
Theorem 3.3.2). -/
theorem Conservative.iff_inter_nonempty (h : d.Conservative) [Std.Symm d]
    (hQ : d.QuasiReflexive) (hI : d.QuantityInvariant) (hx : ∃ x, d {x} {x})
    (hA : ∃ A, ¬ d A A) : d A B ↔ (A ∩ B).Nonempty := by
  classical
  have up {C D : Set α} (hCD : C ⊆ D) (hC : d C C) : d D D :=
    hQ D C ((h.symm_iff_intersective.1 inferInstance D C C C
      (by rw [Set.inter_eq_right.2 hCD, Set.inter_self])).2 hC)
  rw [h.iff_inter_inter]
  refine ⟨fun hd ↦ Set.nonempty_iff_ne_empty.2 fun he ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · obtain ⟨A₀, hA₀⟩ := hA
    exact hA₀ (up (Set.empty_subset A₀) (he ▸ hd))
  · obtain ⟨x, hx⟩ := hx
    have hs : d {a} {a} := by
      rw [← hI (Equiv.swap x a) {a} {a}, preimage_swap_singleton]; exact hx
    exact up (Set.singleton_subset_iff.2 ha) hs

/-- *No* is the only symmetric quasi-universal conservative determiner denotation that is
permutation invariant and fails of a singleton but holds somewhere ([van-benthem-1984],
Corollary 3.3.3). -/
theorem Conservative.iff_disjoint (h : d.Conservative) [Std.Symm d]
    (hQ : d.QuasiUniversal) (hI : d.QuantityInvariant) (hx : ∃ x, ¬ d {x} {x})
    (hA : ∃ A, d A A) : d A B ↔ Disjoint A B := by
  classical
  have down {C D : Set α} (hCD : C ⊆ D) (hD : d D D) : d C C := by
    have := Std.Symm.symm _ _ (hQ D C hD)
    rwa [h, Set.inter_eq_left.2 hCD] at this
  rw [h.iff_inter_inter, Set.disjoint_iff_inter_eq_empty]
  refine ⟨fun hd ↦ Set.eq_empty_iff_forall_notMem.2 fun a ha ↦ ?_, fun he ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hx
    have ha' : d {a} {a} := down (Set.singleton_subset_iff.2 ha) hd
    rw [← hI (Equiv.swap x a) {a} {a}, preimage_swap_singleton] at ha'
    exact hx ha'
  · obtain ⟨A₀, hA₀⟩ := hA
    exact he ▸ down (Set.empty_subset A₀) hA₀

end Det

open Set in
/-- The quantifiers `d A` that a conservative, quantity-invariant determiner denotation gives at a
restrictor, [peters-westerstahl-2006]'s freezings of it, are the quantifiers that live on a set and
that the permutations fixing that set leave unchanged. -/
theorem exists_det_apply_eq_iff_livesOn {Q : Quantifier α} :
    (∃ d : Det α, d.Conservative ∧ d.QuantityInvariant ∧ ∃ A, d A = Q) ↔
      ∃ A, Q.LivesOn A ∧ ∀ σ : Equiv.Perm α, σ ⁻¹' A = A → ∀ B, Q (σ ⁻¹' B) ↔ Q B := by
  refine ⟨fun ⟨d, hC, hQ, A, hdQ⟩ ↦ hdQ ▸ ⟨A, hC.livesOn A, fun σ hσ B ↦ by
    simpa [hσ] using hQ σ A B⟩, fun ⟨J, hJ, hinv⟩ ↦ ?_⟩
  -- `d A B` when a permutation carries `J` onto `A` and `Q` holds of the part of `A ∩ B` it
  -- carries there
  let d : Det α := fun A B ↦ ∃ τ : Equiv.Perm α, τ ⁻¹' A = J ∧ Q (τ ⁻¹' (A ∩ B))
  have key : ∀ (σ : Equiv.Perm α) A B, d A B → d (σ ⁻¹' A) (σ ⁻¹' B) := by
    rintro σ A B ⟨τ, hτ, hB⟩
    refine ⟨τ.trans σ.symm, ?_, ?_⟩
    · rw [← hτ]; ext x; simp
    · have : ⇑(τ.trans σ.symm) ⁻¹' (σ ⁻¹' A ∩ σ ⁻¹' B) = τ ⁻¹' (A ∩ B) := by ext x; simp
      rwa [this]
  have e : ∀ (σ : Equiv.Perm α) X, ⇑σ.symm ⁻¹' (σ ⁻¹' X) = X := fun σ X ↦ by ext; simp
  refine ⟨d, fun A B ↦ ?_, fun σ A B ↦ ⟨fun h ↦ ?_, key σ A B⟩, J, funext fun B ↦ propext ?_⟩
  · simp only [d, ← inter_assoc, inter_self]
  · simpa only [e] using key σ.symm _ _ h
  · exact ⟨fun ⟨τ, hτ, hB⟩ ↦ (hJ B).2 ((hinv τ hτ _).1 hB),
      fun hB ↦ ⟨Equiv.refl α, rfl, (hJ B).1 hB⟩⟩

end Quantifier
