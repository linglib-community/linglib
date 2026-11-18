module

public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Individuals

The individual of an entity, `Quantifier.individual a`, is the quantifier of the sets it belongs
to, Montague's lift. The individuals [generate the quantifiers](##Quantifier.completeLatticeHom_ext)
under complete Boolean operations and are [those commuting with negation and arbitrary
conjunction](##Quantifier.exists_eq_individual_iff), Keenan and Faltz's proper-noun denotations.
An existential is an individual [exactly when its restrictor is a
singleton](##Quantifier.some_eq_individual_iff). Partee's `lower` is the partial inverse of the
lift, so *the king* [lowers to `iota` of its noun](##Quantifier.lower_the), and *a man* and
*every man* do only where there is one man. Predicative content is in
`Quantification/Predicative.lean`.

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

/-! ### Existential closure of a singleton -/

@[simp] theorem some_singleton (j : E) : Det.some {j} = individual j :=
  funext fun _ ↦ propext Set.singleton_inter_nonempty

theorem some_eq_individual_iff {N : Set E} {a : E} : Det.some N = individual a ↔ N = {a} := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ some_singleton a⟩
  have hsub : N ⊆ {a} := fun x hx ↦ by_contra fun hxa ↦ ((congrFun h {a}ᶜ).mp ⟨x, hx, hxa⟩) rfl
  have hne : N.Nonempty := by simpa [Det.some] using (congrFun h Set.univ).mpr (Set.mem_univ a)
  exact hne.subset_singleton_iff.1 hsub

/-! ### Lowering

`lower` takes a principal ultrafilter to the entity generating it. A definite description has an
entity reading where `iota` of its restrictor is defined; an indefinite or a universal has one only
on a singleton restrictor, which `iota` again detects. -/

/-- `lower Q` is the entity whose individual is `Q`, defined when `Q` is a principal ultrafilter. -/
noncomputable def lower (Q : Quantifier E) : Part E := ⟨∃ a, individual a = Q, fun h ↦ h.choose⟩

/-- `lower` is the partial inverse of `individual`. -/
@[simp] theorem mem_lower {Q : Quantifier E} {a : E} : a ∈ lower Q ↔ individual a = Q :=
  ⟨fun ⟨h, ha⟩ ↦ ha ▸ h.choose_spec, fun h ↦
    have hu : ∃ a, individual a = Q := ⟨a, h⟩
    ⟨hu, individual_injective (hu.choose_spec.trans h.symm)⟩⟩

@[simp] theorem lower_individual (a : E) : lower (individual a) = Part.some a :=
  Part.eq_some_iff.2 (mem_lower.2 rfl)

@[simp] theorem lower_bot : lower (⊥ : Quantifier E) = Part.none :=
  Part.eq_none_iff.2 fun a h ↦ (congrFun (mem_lower.1 h) Set.univ).mp (Set.mem_univ a)

private theorem lower_eq_iota_of {f : Det E}
    (hf : ∀ {A : Set E} {a : E}, f A = individual a ↔ A = {a}) (A : Set E) :
    lower (f A) = iota A :=
  Part.ext fun _ ↦ mem_lower.trans <| eq_comm.trans <| hf.trans mem_iota_iff_eq_singleton.symm

/-- An indefinite has an entity reading by `lower` only where the definite does
([partee-1987], §3.4.1). -/
theorem lower_some (A : Set E) : lower (Det.some A) = iota A :=
  lower_eq_iota_of some_eq_individual_iff A

theorem lower_every (A : Set E) : lower (every A) = iota A :=
  lower_eq_iota_of (fun {_ _} ↦ by rw [individual_eq_every, every_injective.eq_iff]) A

@[simp] theorem lower_the (A : Set E) : lower (the A) = iota A := by
  by_cases h : (iota A).Dom
  · obtain ⟨a, ha⟩ := Part.dom_iff_mem.1 h
    rw [the_eq_individual ha, lower_individual, Part.eq_some_iff.2 ha]
  · rw [the_eq_bot h, lower_bot, Part.eq_none_iff'.2 h]

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
