module

public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Individuals

The individual of an entity, `Quantifier.individual a`, is the quantifier of the sets it belongs
to, Montague's lift. The individuals [generate the quantifiers](##Quantifier.completeLatticeHom_ext)
under complete Boolean operations and are [those commuting with negation and arbitrary
conjunction](##Quantifier.exists_eq_individual_iff), Keenan and Faltz's proper-noun denotations.
Partee's type shifts are built on them. `lower` is the partial inverse of the lift, and *the king*
[lowers to `iota` of its noun](##Quantifier.lower_the), as *a man* does. Predicative `BE` is [the
only complete homomorphism](##Quantifier.BE_unique) taking each individual to its singleton, and
`Det.some`, Partee's `A`, is [its only conservative, symmetric, monotone
section](##Quantifier.eq_some_of_leftInverse).

## Implementation notes

Fact 2 of [partee-1987], the uniqueness of `BE`, is stated for complete homomorphisms: on an
infinite domain a Boolean homomorphism can agree with `BE` on the individuals and differ
elsewhere (`Studies/Partee1987.lean`).

## References

* [keenan-faltz-1985]
* [partee-1987]
-/

@[expose] public section

namespace Quantifier

open Quantifier.Det

variable {E : Type*}

/-! ### Individuals -/

theorem sInter_individual (a : E) : ⋂₀ {B | individual a B} = {a} :=
  Set.ext fun _ ↦ ⟨fun h ↦ h {a} rfl, fun h _ hs ↦ h ▸ hs⟩

@[simp] theorem individual_compl (a : E) (B : Set E) : individual a Bᶜ ↔ ¬ individual a B :=
  .rfl

@[simp] theorem individual_sInter (a : E) (S : Set (Set E)) :
    individual a (⋂₀ S) ↔ ∀ B ∈ S, individual a B :=
  .rfl

/-! ### Generation by the individuals

*Every*, *some* and *no* at a restrictor are the meet, the join and the meet of the complements
of the individuals of the restrictor, and every quantifier is a join of meets of individuals and
their complements. -/

theorem every_eq_iInf_individual (A : Set E) : every A = ⨅ x ∈ A, individual x :=
  funext fun _ ↦ by simp [every, individual, Set.subset_def]

theorem some_eq_iSup_individual (A : Set E) : Det.some A = ⨆ x ∈ A, individual x :=
  funext fun _ ↦ by simp [Det.some, individual, Set.Nonempty]

theorem no_eq_iInf_compl_individual (A : Set E) : no A = ⨅ x ∈ A, (individual x)ᶜ :=
  funext fun _ ↦ by simp [no, individual, Set.subset_def]

theorem every_inf_no_compl_apply {A B : Set E} : (every A ⊓ no Aᶜ) B ↔ B = A :=
  ⟨fun ⟨h₁, h₂⟩ ↦ Set.Subset.antisymm (Set.compl_subset_compl.1 h₂) h₁,
    fun h ↦ h ▸ ⟨subset_rfl, subset_rfl⟩⟩

theorem eq_iSup_every_inf_no (Q : Quantifier E) : Q = ⨆ (A) (_ : Q A), every A ⊓ no Aᶜ :=
  funext fun _ ↦ by
    simp only [iSup_apply, iSup_Prop_eq, every_inf_no_compl_apply, exists_prop, exists_eq_right']

/-- Complete homomorphisms out of `Quantifier E` that agree on the individuals are equal, the
individuals being complete generators. -/
theorem completeLatticeHom_ext {β : Type*} [CompleteBooleanAlgebra β]
    {f g : CompleteLatticeHom (Quantifier E) β} (h : ∀ x, f (individual x) = g (individual x)) :
    f = g := by
  ext Q
  rw [eq_iSup_every_inf_no Q]
  simp only [map_iSup, map_inf, every_eq_iInf_individual, no_eq_iInf_compl_individual, map_iInf,
    map_compl', h]

/-! ### Predicative content and existential closure -/

/-- `BE Q` is the predicative content of the quantifier `Q`, `BE(Q) = {x | Q {x}}`, which
preserves arbitrary meets and joins. -/
def BE : CompleteLatticeHom (Quantifier E) (Set E) where
  toFun Q := {x | Q {x}}
  map_sInf' _ := Set.ext fun _ ↦ by simp
  map_sSup' _ := Set.ext fun _ ↦ by simp

@[simp] theorem mem_BE (Q : Quantifier E) (x : E) : x ∈ BE Q ↔ Q {x} := .rfl

@[simp] theorem BE_individual (j : E) : BE (individual j) = {j} :=
  Set.ext fun _ ↦ eq_comm

@[simp] theorem some_singleton (j : E) : Det.some {j} = individual j :=
  funext fun _ ↦ propext Set.singleton_inter_nonempty

/-- `BE ∘ A` is the identity: *be a man* is *man*. -/
@[simp] theorem BE_some (A : Set E) : BE (Det.some A) = A :=
  Set.ext fun _ ↦ Set.inter_singleton_nonempty

theorem some_injective : Function.Injective (Det.some : Det E) :=
  Function.LeftInverse.injective BE_some

theorem some_eq_individual_iff {N : Set E} {a : E} : Det.some N = individual a ↔ N = {a} := by
  rw [← some_singleton, some_injective.eq_iff]

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

/-! ### Lowering

`lower` takes a principal ultrafilter to the entity generating it. A definite description has an
entity reading where `iota` of its restrictor is defined; an indefinite or a universal has one only
on a singleton restrictor, which `iota` again detects. -/

/-- `lower Q` is the entity whose individual is `Q`, defined when `Q` is a principal ultrafilter. -/
noncomputable def lower : Quantifier E → Option E := Function.partialInv individual

theorem lower_isPartialInv : Function.IsPartialInv individual (lower (E := E)) :=
  individual_injective.isPartialInv

theorem lower_eq_some_iff {Q : Quantifier E} {a : E} : lower Q = some a ↔ individual a = Q :=
  lower_isPartialInv a Q

@[simp] theorem lower_individual (a : E) : lower (individual a) = some a :=
  Function.partialInv_left individual_injective a

@[simp] theorem lower_bot : lower (⊥ : Quantifier E) = none :=
  Option.eq_none_iff_forall_ne_some.2 fun a h ↦
    (congrFun (lower_eq_some_iff.1 h) Set.univ).mp (Set.mem_univ a)

theorem iota_BE_individual (a : E) : iota (BE (individual a)) = some a := by
  rw [BE_individual, iota_singleton]

theorem every_injective : Function.Injective (every : Det E) := fun A B h ↦
  subset_antisymm ((congrFun h B).mpr subset_rfl) ((congrFun h A).mp subset_rfl)

private theorem lower_eq_iota_of {f : Det E}
    (hf : ∀ {A : Set E} {a : E}, f A = individual a ↔ A = {a}) (A : Set E) :
    lower (f A) = iota A :=
  Option.ext fun _ ↦ lower_eq_some_iff.trans <| eq_comm.trans <| hf.trans <|
    Set.eq_singleton_iff_unique_mem.trans (iota_eq_some_iff _).symm

/-- An indefinite has an entity reading by `lower` only where the definite does. -/
theorem lower_some (A : Set E) : lower (Det.some A) = iota A :=
  lower_eq_iota_of some_eq_individual_iff A

theorem lower_every (A : Set E) : lower (every A) = iota A :=
  lower_eq_iota_of (fun {_ _} ↦ by rw [individual_eq_every, every_injective.eq_iff]) A

/-! ### The definite article -/

/-- *The `A`* is the lift of `iota A` where `iota A` is defined, and the empty quantifier
elsewhere. -/
theorem the_eq_elim (A : Set E) : the A = (iota A).elim ⊥ individual :=
  funext fun _ ↦ propext <| the_iff_exists_mem_iota.trans <| by
    cases iota A <;> simp [individual]

@[simp] theorem lower_the (A : Set E) : lower (the A) = iota A := by
  rw [the_eq_elim]; cases iota A <;> simp

/-- *Be the `A`* holds of `x` when `x` is the only `A`. -/
theorem mem_BE_the {A : Set E} {x : E} : x ∈ BE (the A) ↔ A = {x} :=
  ⟨fun ⟨_, hz, hzx⟩ ↦ Set.ext fun z ↦ (hz z).trans (by rw [hzx]; rfl),
    fun h ↦ ⟨x, fun z ↦ h ▸ Iff.rfl, rfl⟩⟩

/-- On a restrictor with at most one member, *be the `A`* is `A`, as in *John is (the)
president* ([partee-1987], §3.2). -/
theorem BE_the_of_subsingleton {A : Set E} (hA : A.Subsingleton) : BE (the A) = A :=
  Set.ext fun _ ↦ mem_BE_the.trans ⟨fun h ↦ h ▸ rfl, hA.eq_singleton_of_mem⟩

/-- On a nonempty restrictor, *be every `A`* is *be the `A`*. -/
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

/-! ### Individuals as complete homomorphisms

Keenan and Faltz define a proper-noun denotation as a set of properties satisfying the Meets,
Joins and Complements Conditions and prove that these are exactly the individuals generated by
atoms; the Joins Condition follows from the other two. Read as scope, the Complements Condition
says that the quantifier commutes with negation and the Meets Condition that it commutes with
universal quantification, so the scopeless quantifiers are the Montagovian individuals. -/

/-- The quantifiers that commute with negation and with arbitrary intersection are the
Montagovian individuals, [keenan-faltz-1985]'s Theorem 9 for the algebra `Set E`. -/
theorem exists_eq_individual_iff {Q : Quantifier E} :
    (∃ a, Q = individual a) ↔
      (∀ B, Q Bᶜ ↔ ¬ Q B) ∧ ∀ S : Set (Set E), Q (⋂₀ S) ↔ ∀ B ∈ S, Q B := by
  refine ⟨?_, fun ⟨hc, hs⟩ ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨individual_compl a, individual_sInter a⟩
  have hC : Q (⋂₀ {B | Q B}) := (hs _).2 fun _ h ↦ h
  obtain ⟨a, ha⟩ : (⋂₀ {B | Q B}).Nonempty := by
    by_contra! h
    rw [h, ← Set.compl_univ, ← Set.sInter_empty, hc, hs ∅] at hC
    exact hC fun _ h ↦ h.elim
  refine ⟨a, funext fun B ↦ propext ⟨fun h ↦ ha B h, fun h ↦ by_contra fun hB ↦ ?_⟩⟩
  exact ha _ ((hc B).2 hB) h

end Quantifier
