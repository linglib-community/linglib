module

public import Linglib.Semantics.Quantification.Individual
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Predicative content

`BE`, Montague's translation of *be* recast by Partee as a type shift, takes a quantifier to the
individuals whose singleton it contains. It is a complete homomorphism, [the only one taking each
individual to its singleton](##Quantifier.BE_unique), and the existential determiner `Det.some`,
Partee's `A`, is a section of it, [the only conservative, symmetric, monotone
one](##Quantifier.eq_some_of_leftInverse); on the monotone quantifiers the two form a Galois
coinsertion. On an intersective determiner `BE` [asks of an individual only about the
restrictor there](##Quantifier.Det.Intersective.mem_BE). *Be the `A`* [holds of the only
`A`](##Quantifier.mem_BE_the), as *be every `A`* does once there is an `A`, and read at each index
it is [a role that no set represents](##Quantifier.BE_the_not_mem_range_const).

## Implementation notes

Fact 2 of [partee-1987], the uniqueness of `BE`, is stated for complete homomorphisms: on an
infinite domain a Boolean homomorphism can agree with `BE` on the individuals and differ
elsewhere (`Studies/Partee1987.lean`).

## References

* [partee-1987]
-/

@[expose] public section

namespace Quantifier

open Quantifier.Det

variable {E : Type*}

/-! ### `BE` and its sections -/

/-- `BE Q` is the predicative content of the quantifier `Q`, `BE(Q) = {x | Q {x}}`, which
preserves arbitrary meets and joins. -/
def BE : CompleteLatticeHom (Quantifier E) (Set E) where
  toFun Q := {x | Q {x}}
  map_sInf' _ := Set.ext fun _ ↦ by simp
  map_sSup' _ := Set.ext fun _ ↦ by simp

@[simp] theorem mem_BE (Q : Quantifier E) (x : E) : x ∈ BE Q ↔ Q {x} := .rfl

@[simp] theorem BE_individual (j : E) : BE (individual j) = {j} :=
  Set.ext fun _ ↦ eq_comm

/-- `BE ∘ A` is the identity: *be a man* is *man*. -/
@[simp] theorem BE_some (A : Set E) : BE (Det.some A) = A :=
  Set.ext fun _ ↦ Set.inter_singleton_nonempty

theorem some_injective : Function.Injective (Det.some : Det E) :=
  Function.LeftInverse.injective BE_some

theorem some_BE_eq_self_iff {Q : Quantifier E} : Det.some (BE Q) = Q ↔ ∃ A, Det.some A = Q :=
  ⟨fun h ↦ ⟨_, h⟩, fun ⟨A, h⟩ ↦ h ▸ congrArg Det.some (BE_some A)⟩

/-- `BE` is the only complete homomorphism taking each individual to its singleton, Fact 2 of
[partee-1987]. -/
theorem BE_unique {f : CompleteLatticeHom (Quantifier E) (Set E)}
    (h : ∀ a, f (individual a) = {a}) : f = BE :=
  completeLatticeHom_ext fun a ↦ (h a).trans (BE_individual a).symm

/-- `A` is the natural inverse of `BE` ([partee-1987], §3.3): among conservative determiners it is
the only symmetric, upward monotone one that `BE` undoes. *Exactly one* is a symmetric section of
`BE` that is not monotone. -/
theorem eq_some_of_leftInverse [Nonempty E] {D : Det E} (hc : D.Conservative) [Std.Symm D]
    (hm : D.ScopeMonotone) (h : Function.LeftInverse BE D) : D = Det.some := by
  ext A B
  change _ ↔ (A ∩ B).Nonempty
  rw [hc.iff_inter_inter]
  refine ⟨fun hAB ↦ Set.nonempty_iff_ne_empty.2 fun he ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty E›
    have : x ∈ BE (D ∅) := hm ∅ (Set.empty_subset {x}) (he ▸ hAB)
    rwa [h ∅] at this
  · exact hm _ (Set.singleton_subset_iff.2 hx) ((h (A ∩ B)).symm ▸ hx : x ∈ BE (D (A ∩ B)))

/-- `BE` of an intersective determiner, which looks only at `A ∩ B`, asks of an entity `x` only
about `A ∩ {x}`. For one that is also quantity invariant, as the weak determiners are, the
predicative reading is the noun, its complement or a constant. -/
theorem Det.Intersective.mem_BE {D : Det E} (hD : D.Intersective) {A : Set E} {x : E} :
    x ∈ BE (D A) ↔ D (A ∩ {x}) (A ∩ {x}) :=
  hD _ _ _ _ (Set.inter_self _).symm

theorem iota_BE_individual (a : E) : iota (BE (individual a)) = Part.some a := by
  rw [BE_individual, iota_singleton]

/-! ### The definite article -/

/-- *Be the `A`* holds of `x` when `x` is the only `A` ([partee-1987], §3.2). -/
theorem mem_BE_the {A : Set E} {x : E} : x ∈ BE (the A) ↔ A = {x} :=
  ⟨fun ⟨_, hz, hzx⟩ ↦ Set.ext fun z ↦ (hz z).trans (by rw [hzx]; rfl),
    fun h ↦ ⟨x, fun z ↦ h ▸ Iff.rfl, rfl⟩⟩

/-- On a restrictor with at most one member, *be the `A`* is `A`, as in *John is (the)
president* ([partee-1987], §3.2). -/
theorem BE_the_of_subsingleton {A : Set E} (hA : A.Subsingleton) : BE (the A) = A :=
  Set.ext fun _ ↦ mem_BE_the.trans ⟨fun h ↦ h ▸ rfl, hA.eq_singleton_of_mem⟩

/-- On a nonempty restrictor, *be every `A`* is *be the `A`* ([partee-1987], §3.3). -/
theorem BE_every_of_nonempty {A : Set E} (hA : A.Nonempty) : BE (every A) = BE (the A) :=
  Set.ext fun _ ↦ hA.subset_singleton_iff.trans mem_BE_the.symm

/-- The predicative definite read at each index is the role of being the only `P` there, which
no set read at every index represents once the referent changes: *the owner of this land* as a
predicate depends on who owns it where ([partee-1987], fn. 16). -/
theorem BE_the_not_mem_range_const {W : Type*} {P : W → Set E} {w₀ w₁ : W} {a b : E}
    (h₀ : P w₀ = {a}) (h₁ : P w₁ = {b}) (hab : a ≠ b) :
    (fun w ↦ BE (the (P w))) ∉ Set.range (Function.const W) := by
  rintro ⟨B, hB⟩
  have h₀' := congrFun hB w₀
  have h₁' := congrFun hB w₁
  simp only [Function.const_apply, h₀, h₁,
    BE_the_of_subsingleton Set.subsingleton_singleton] at h₀' h₁'
  exact hab (Set.singleton_injective (h₀'.symm.trans h₁'))

/-! ### The Galois coinsertion on monotone quantifiers -/

theorem individual_le_iff {Q : Quantifier E} (hQ : Monotone Q) {x : E} :
    individual x ≤ Q ↔ x ∈ BE Q :=
  ⟨fun h ↦ h _ rfl, fun h _ hB ↦ hQ (Set.singleton_subset_iff.2 hB) h⟩

theorem some_le_iff {Q : Quantifier E} (hQ : Monotone Q) {A : Set E} :
    Det.some A ≤ Q ↔ A ⊆ BE Q := by
  simp only [some_eq_iSup_individual, iSup₂_le_iff, individual_le_iff hQ]
  rfl

/-- On the monotone quantifiers `Det.some` and `BE` form a Galois coinsertion. -/
def gciSomeBE :
    GaloisCoinsertion (fun A ↦ (⟨Det.some A, monotone_some A⟩ : Set E →o Prop)) fun Q ↦ BE Q :=
  GaloisConnection.toGaloisCoinsertion (fun _ Q ↦ some_le_iff Q.monotone) fun A ↦ (BE_some A).le

end Quantifier
