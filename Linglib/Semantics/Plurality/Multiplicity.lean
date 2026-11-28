module

public import Linglib.Semantics.Plurality.Cardinality
public import Linglib.Semantics.Exhaustification.InnocentExclusion

/-!
# The multiplicity inference

An existential sentence about a noun phrase is evaluated at the number of its witnesses, a natural
number. Its inclusive reading `Number.inclusive` holds where there is a witness, and the exclusive
reading `Number.exclusive s v` of a number value `v` holds where the witnesses have a cardinality
the system `s` gives `v`. The exclusive readings of a system's values are disjoint and cover the
inclusive reading.

On the implicature account the sentence has the inclusive reading whatever its number, and
competes with the exclusive readings of the determinate values of its system. Exhaustified against
them, it has the exclusive reading of the plural, `Number.exhIE_inclusive`: more than one witness
in a system with a singular, more than two in a system with a singular and a dual.

## References

* [spector-2007b]
* [zweig-2009]
* [fox-2007]
-/

@[expose] public section

namespace Number

open Exhaustification

variable (s : Finset Number) {v w : Number} {n : ℕ}

/-- The inclusive reading holds where there is a witness. -/
def inclusive : Set ℕ := Set.range ((↑) : ℕ+ → ℕ)

@[simp] theorem mem_inclusive : n ∈ inclusive ↔ 1 ≤ n :=
  ⟨fun ⟨p, hp⟩ ↦ hp ▸ p.pos, fun h ↦ ⟨⟨n, h⟩, rfl⟩⟩

/-- The exclusive reading of a number value holds where the witnesses have a cardinality the
system gives that value. -/
def exclusive (v : Number) : Set ℕ := (↑) '' (ofCard s ⁻¹' {v})

variable {s}

theorem mem_exclusive_iff : n ∈ exclusive s v ↔ ∃ p : ℕ+, ofCard s p = v ∧ (p : ℕ) = n := Iff.rfl

@[simp] theorem coe_mem_exclusive_iff {p : ℕ+} : (p : ℕ) ∈ exclusive s v ↔ ofCard s p = v :=
  PNat.coe_injective.mem_set_image

variable (s) in
theorem exclusive_subset_inclusive (v : Number) : exclusive s v ⊆ inclusive :=
  Set.image_subset_range _ _

/-- The exclusive reading of the plural holds of the cardinalities to which no value of the system
is fixed. -/
theorem mem_exclusive_plural_iff :
    n ∈ exclusive s .plural ↔ 1 ≤ n ∧ ∀ v ∈ s, ∀ m ∈ v.exactCard, (m : ℕ) ≠ n := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.pos, fun v hv m hm h ↦ ofCard_eq_plural_iff_forall.1 hp v hv (PNat.eq h ▸ hm)⟩
  · rintro ⟨h1, h⟩
    exact ⟨⟨n, h1⟩, ofCard_eq_plural_iff_forall.2 fun v hv hc ↦ h v hv _ hc rfl, rfl⟩

theorem disjoint_exclusive (h : v ≠ w) : Disjoint (exclusive s v) (exclusive s w) :=
  Set.disjoint_image_of_injective PNat.coe_injective <|
    Set.disjoint_iff.2 fun _ ⟨hv, hw⟩ ↦ h (hv.symm.trans hw)

variable (s) in
theorem iUnion_exclusive : ⋃ v, exclusive s v = inclusive := by
  simp only [exclusive, ← Set.image_iUnion, ← Set.preimage_iUnion, Set.iUnion_of_singleton,
    Set.preimage_univ, Set.image_univ, inclusive]

variable (s) in
/-- The alternatives of the inclusive reading in a system are itself and the exclusive readings
of the system's determinate values. -/
def exclusiveAlternatives : Set (Set ℕ) :=
  insert inclusive (exclusive s '' {v | v ∈ s ∧ v.IsDeterminate})

variable (s) in
/-- Plain exhaustification of the inclusive reading against the exclusive readings of a system's
determinate values gives the exclusive reading of the plural. -/
theorem exh_inclusive :
    exh (exclusiveAlternatives s) inclusive = exclusive s .plural := by
  unfold exclusiveAlternatives
  ext n
  constructor
  · rintro ⟨⟨p, rfl⟩, h⟩
    by_contra hp
    rw [coe_mem_exclusive_iff, ofCard_eq_plural_iff, not_not] at hp
    have h4 : ((4 : ℕ+) : ℕ) ∈ exclusive s (ofCard s p) :=
      h _ (.inr ⟨_, ⟨((ofCard_eq_iff hp).1 rfl).1, hp⟩, rfl⟩) (coe_mem_exclusive_iff.2 rfl)
        ⟨4, rfl⟩
    rw [coe_mem_exclusive_iff, ofCard_of_three_lt (by decide)] at h4
    exact ofCard_eq_plural_iff.1 h4.symm hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, rfl⟩, ?_⟩
    rintro _ (rfl | ⟨v, ⟨-, hv⟩, rfl⟩) hq
    · exact subset_rfl
    · rw [coe_mem_exclusive_iff] at hq
      exact absurd (hq ▸ hv) (ofCard_eq_plural_iff.1 hp)

variable (s) in
/-- Exhaustified against the exclusive readings of the determinate values of its system, the
inclusive reading is the exclusive reading of the plural. -/
theorem exhIE_inclusive :
    exhᴵᴱ (exclusiveAlternatives s) inclusive = exclusive s .plural := by
  have h : (exh (exclusiveAlternatives s) inclusive).Nonempty := by
    rw [exh_inclusive]
    exact ⟨4, 4, ofCard_of_three_lt (by decide), rfl⟩
  rw [exhIE_eq_exh_of_nonempty _ _ h, exh_inclusive]

end Number
