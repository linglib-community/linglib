module

public import Linglib.Semantics.Questions.Basic
public import Linglib.Semantics.Polarity.Basic

/-!
# Polar questions

The polar question `polar p` is the join `ofSet p ⊔ ofSet pᶜ` of the declaratives of `p` and of
its complement, Hamblin's yes/no question as an inquisitive content and Punčochář's
`?α := α ⩒ ¬α`. It is the non-informative projection of the declarative (`query_ofSet`), and a
nontrivial polar question has the alternatives `p` and `pᶜ` (`alt_polar_of_nontrivial`).

## References

* [ciardelli-groenendijk-roelofsen-2018]
* [hamblin-1973b]
* [puncochar-2019]
-/

@[expose] public section

namespace Question

variable {W : Type*}

/-! ### Polar question via inquisitive disjunction -/

/-- The **polar interrogative** content of a proposition `p`, defined
    via [puncochar-2019]'s `?α := α ⩒ ¬α`. Alternatives are `p`
    and `pᶜ`; non-informative (`info = univ`); inquisitive iff `p` is
    non-trivial. -/
def polar (p : Set W) : Question W :=
  ofSet p ⊔ ofSet pᶜ

@[simp] theorem polar_compl (p : Set W) : polar pᶜ = polar p := by
  rw [polar, polar, compl_compl, sup_comm]

theorem polar_eq_sup (p : Set W) :
    polar p = ofSet p ⊔ ofSet pᶜ := rfl

theorem polar_eq_iSup_orbit (p : Set W) :
    polar p = ⨆ q ∈ MulAction.orbit Polarity p, ofSet q := by
  rw [polar_eq_sup, Polarity.orbit_eq_pair_compl, iSup_insert, iSup_singleton]

@[simp] theorem polar_smul (s : Polarity) (p : Set W) : polar (s • p) = polar p := by
  rw [polar_eq_iSup_orbit, polar_eq_iSup_orbit, MulAction.orbit_smul]

theorem query_ofSet (p : Set W) : (ofSet p).query = polar p := by
  rw [query, info_ofSet, polar_eq_sup]

@[simp] theorem mem_polar {p σ : Set W} : σ ∈ polar p ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  rw [polar_eq_sup]; simp only [mem_sup, mem_ofSet]

theorem isNormal_polar (p : Set W) : (polar p).IsNormal :=
  (isNormal_ofSet p).sup (isNormal_ofSet pᶜ)

@[simp] theorem info_polar (p : Set W) : (polar p).info = Set.univ := by
  rw [polar_eq_sup, info_sup, info_ofSet, info_ofSet,
      Set.union_compl_self]

theorem not_isInformative_polar (p : Set W) :
    ¬ (polar p).IsInformative :=
  fun h => h (info_polar p)

theorem isInquisitive_polar_iff (p : Set W) :
    (polar p).IsInquisitive ↔ p ≠ ∅ ∧ p ≠ Set.univ := by
  show (polar p).info ∉ polar p ↔ _
  rw [info_polar]
  simp only [mem_polar, Set.univ_subset_iff, Set.compl_univ_iff, not_or]
  tauto

/-! ### `alt`-characterization of `polar` -/

theorem coe_polar (p : Set W) : (polar p : Set (Set W)) = lowerClosure {p, pᶜ} := by
  ext q
  simp [mem_polar]

theorem alt_polar_of_nontrivial {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    alt (polar p) = {p, pᶜ} :=
  alt_eq_of_coe_eq_lowerClosure
    (Set.pairwise_pair.mpr fun _ ↦ ⟨fun h ↦ hne (le_compl_self.mp h),
      fun h ↦ hnu (compl_le_self.mp h)⟩) (coe_polar p)

theorem alt_polar_eq_orbit {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    alt (polar p) = MulAction.orbit Polarity p := by
  rw [alt_polar_of_nontrivial hne hnu, Polarity.orbit_eq_pair_compl]

/-! ### Polar degenerate-case identities -/

theorem polar_empty : (polar (∅ : Set W)) = ⊤ := by
  rw [polar_eq_sup, Set.compl_empty, ofSet_univ, sup_top_eq]

theorem polar_univ : (polar (Set.univ : Set W)) = ⊤ := by
  rw [polar_eq_sup, ofSet_univ, top_sup_eq]

/-! ### `alt`-characterization of `polar` (full) -/

theorem alt_polar_iff (p : Set W) (q : Set W) :
    q ∈ alt (polar p) ↔
      ((p = ∅ ∨ p = Set.univ) ∧ q = Set.univ) ∨
      (p ≠ ∅ ∧ p ≠ Set.univ ∧ (q = p ∨ q = pᶜ)) := by
  by_cases he : p = ∅
  · subst he
    rw [polar_empty, alt_top]
    simp
  · by_cases hu : p = Set.univ
    · subst hu
      rw [polar_univ, alt_top]
      simp
    · rw [alt_polar_of_nontrivial he hu]
      simp [he, hu]

theorem mem_alt_polar_of_nontrivial {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) (q : Set W) :
    q ∈ alt (polar p) ↔ q = p ∨ q = pᶜ := by
  rw [alt_polar_of_nontrivial hne hnu]; simp

/-! ### Inf of two polar questions classified by a partition

When two polar questions `polar p ⊓ polar q` are answered together,
the joint resolution carves the world space into the four "corners"
`p ∩ q`, `p ∩ qᶜ`, `pᶜ ∩ q`, `pᶜ ∩ qᶜ`. Every state resolving both
polars lies in some corner. A wh-question whose cells contain these
corners therefore satisfies `polar p ⊓ polar q ≤ which D P`. -/

theorem mem_polar_inf_polar_iff {p q σ : Set W} :
    σ ∈ polar p ⊓ polar q ↔
      σ ⊆ p ∩ q ∨ σ ⊆ p ∩ qᶜ ∨ σ ⊆ pᶜ ∩ q ∨ σ ⊆ pᶜ ∩ qᶜ := by
  simp only [mem_inf, mem_polar, Set.subset_inter_iff]
  tauto

end Question
