module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Data.Examples.Wang2023

/-!
# Wang (2023): Honorifics without [HON]

Across Wang's survey the values recruited for honorific pronouns are plural number, third
person and indefiniteness, never singular, first or second person, or definites (Table 1, (28)).
These are the semantically unmarked values, the ones carrying the weakest presupposition (54)–(56).
Recruitment follows from the Taboo of Directness (57), which in respect contexts demands the
weakest presupposition, ranked above Heim's Maximize Presupposition! (59), which demands the
strongest: [the weakest form alone survives](##sToD_top). Number systems with a dual (80) also need
a weak taboo that avoids only the strongest presupposition (82), and the four attested patterns of
honorific nonsingulars are the rankings of (83), [plural only](##stod_mp_wtod), [dual
only](##wtod_mp_stod), and [both, non-escalating](##wtod_alone), the escalating system combining the
first two by politeness.

## Implementation notes

The maxims compare presuppositions, so they count the competitors a form's presupposition is
strictly stronger or weaker than; on the chain of (80) these counts are the violations of a ranked
tableau. The dual's presupposition (80b) is lexical: `presup .dual` bounds a plurality by two
atoms, where [`Number.dom` leaves the dual unrestricted](##presup_dual_ne_dom), having no
`[−atomic]` to build it on, Martí's objection to inclusive-only plurals. The singular is printed as
`|x| = 1` in (54b) and as `|x| ≤ 1` in (80c); `presup` keeps (54b).

## TODO

* MP! (59) chooses the strongest presupposition compatible with what is assumed, a condition at the
  context, stated by `Presupposition.minimalFor_preimage_Ici_iff`, while `mp` counts competitors.
  The two agree when every stronger form is compatible.

## References

* [wang-r-2023]
* [heim-1991]
* [harbour-2016]
* [sauerland-2003]
-/

@[expose] public section

namespace Wang2023

open OptimalityTheory

/-! ### The recruited values are the least specified cells (§4.1) -/

-- (55)
theorem third_eq_bot : Person.toFeatures .third = ⊥ := Person.toFeatures_third

/-! ### The Taboo of Directness and Maximize Presupposition! (§4.2, §5) -/

section Maxims

variable {C E : Type*} (s : Finset C) (p : C → Set E)

open Classical in
/-- The Taboo of Directness (57), strong in (82a), asks in respect contexts for the form with the
weakest presupposition; it counts the competitors weaker than a form. -/
noncomputable def sToD : Constraint C := fun c ↦ (s.filter fun d ↦ p c ⊂ p d).card

open Classical in
/-- Maximize Presupposition! (59) asks for the form with the strongest presupposition; it counts
the competitors stronger than a form. -/
noncomputable def mp : Constraint C := fun c ↦ (s.filter fun d ↦ p d ⊂ p c).card

open Classical in
/-- The weak Taboo of Directness (82b) avoids the form with the strongest presupposition. -/
noncomputable def wToD : Constraint C := fun c ↦ if ∀ d ∈ s, p c ⊆ p d then 1 else 0

variable {s p} {a b c : C}

theorem sToD_lt (hb : b ∈ s) (h : p a ⊂ p b) : sToD s p b < sToD s p a := by
  classical
  refine Finset.card_lt_card ⟨fun d hd ↦ ?_, fun hsub ↦ ?_⟩
  · obtain ⟨hds, hbd⟩ := Finset.mem_filter.1 hd
    exact Finset.mem_filter.2 ⟨hds, h.trans hbd⟩
  · exact (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hb, h⟩))).2.ne rfl

theorem mp_lt (ha : a ∈ s) (h : p a ⊂ p b) : mp s p a < mp s p b := by
  classical
  refine Finset.card_lt_card ⟨fun d hd ↦ ?_, fun hsub ↦ ?_⟩
  · obtain ⟨hds, hda⟩ := Finset.mem_filter.1 hd
    exact Finset.mem_filter.2 ⟨hds, hda.trans h⟩
  · exact (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨ha, h⟩))).2.ne rfl

theorem optimal_ofList_singleton (Fs : List (Constraint C)) :
    (Tableau.ofList {c} Fs).optimal = {c} :=
  Finset.Subset.antisymm Tableau.optimal_subset <| Finset.singleton_subset_iff.2 <| by
    obtain ⟨d, hd⟩ := Tableau.optimal_nonempty (t := Tableau.ofList {c} Fs)
      (Finset.singleton_nonempty c)
    exact Finset.mem_singleton.1 (Tableau.optimal_subset hd) ▸ hd

/-- The strong taboo on top of any ranking selects the weakest form alone from a candidate set that
contains it: the emergence of the semantically unmarked. -/
theorem sToD_top [DecidableEq C] (hc : c ∈ s) (h : ∀ d ∈ s, d ≠ c → p d ⊂ p c)
    (Fs : List (Constraint C)) :
    (Tableau.ofList s (sToD s p :: Fs)).optimal = {c} := by
  rw [Tableau.optimal_ofList_cons, Finset.argmin_eq_singleton_iff.2
    ⟨hc, fun d hd hne ↦ sToD_lt hc (h d hd hne)⟩, optimal_ofList_singleton]

theorem mp_top [DecidableEq C] (hc : c ∈ s) (h : ∀ d ∈ s, d ≠ c → p c ⊂ p d)
    (Fs : List (Constraint C)) :
    (Tableau.ofList s (mp s p :: Fs)).optimal = {c} := by
  rw [Tableau.optimal_ofList_cons, Finset.argmin_eq_singleton_iff.2
    ⟨hc, fun d hd hne ↦ mp_lt hc (h d hd hne)⟩, optimal_ofList_singleton]

-- (28): under the strong taboo a form with a weaker competitor is never recruited
theorem notMem_optimal_of_sToD_top (hb : b ∈ s) (h : p a ⊂ p b) (Fs : List (Constraint C)) :
    a ∉ (Tableau.ofList s (sToD s p :: Fs)).optimal := fun ha ↦ by
  rw [Tableau.optimal_ofList_cons] at ha
  exact absurd (Finset.mem_argmin.1 (Tableau.optimal_subset ha)).2 fun hle ↦
    (sToD_lt hb h).not_ge (hle b hb)

section Chain

variable [DecidableEq C] (hab : p a ⊂ p b) (hbc : p b ⊂ p c)

include hab hbc

-- the weak taboo leaves all but the strongest form of a chain
theorem argmin_wToD :
    ({a, b, c} : Finset C).argmin (wToD {a, b, c} p) = {b, c} := by
  have hA : wToD {a, b, c} p a = 1 := ite_eq_left <| by
    simpa [Finset.forall_mem_insert] using ⟨hab.subset, (hab.trans hbc).subset⟩
  have hB : wToD {a, b, c} p b = 0 := ite_eq_right fun h ↦ hab.not_subset (h a (by simp))
  have hC : wToD {a, b, c} p c = 0 :=
    ite_eq_right fun h ↦ (hab.trans hbc).not_subset (h a (by simp))
  ext d
  simp only [Finset.mem_argmin, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hd⟩
    · have := hd b (by simp)
      omega
    · exact .inl rfl
    · exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨by simp, fun e _ ↦ hB ▸ Nat.zero_le _⟩
    · exact ⟨by simp, fun e _ ↦ hC ▸ Nat.zero_le _⟩

-- over a chain the weak taboo above MP! selects the middle form
theorem wToD_mp (Fs : List (Constraint C)) :
    (Tableau.ofList {a, b, c} (wToD {a, b, c} p :: mp {a, b, c} p :: Fs)).optimal = {b} := by
  have hmin : ({b, c} : Finset C).argmin (mp {a, b, c} p) = {b} := by
    refine Finset.argmin_eq_singleton_iff.2 ⟨by simp, fun d hd hne ↦ ?_⟩
    rcases Finset.mem_insert.1 hd with h | h
    · exact absurd h hne
    · obtain rfl := Finset.mem_singleton.1 h
      exact mp_lt (by simp) hbc
  rw [Tableau.optimal_ofList_cons, argmin_wToD hab hbc, Tableau.optimal_ofList_cons, hmin,
    optimal_ofList_singleton]

theorem wToD_alone :
    (Tableau.ofList {a, b, c} [wToD {a, b, c} p]).optimal = {b, c} := by
  rw [Tableau.optimal_ofList_cons, argmin_wToD hab hbc, Tableau.optimal_ofList_nil]

end Chain

end Maxims

/-! ### Articulated number systems (§5) -/

section Number

variable {E : Type*} [CompleteLattice E] {a b y : E}

/-- The presuppositions (54), (80): the singular of an atom, the dual of at most two atoms, and
nothing of the plural. -/
def presup : Number → Set E
  | .dual => {x | ∃ a b, IsAtom a ∧ IsAtom b ∧ x ≤ a ⊔ b}
  | n => Number.dom (some n)

/-- The singular, dual and plural of an articulated number system (80). -/
def number : Finset Number := {.singular, .dual, .plural}

theorem presup_plural : presup (E := E) .plural = Set.univ := Number.dom_plural

-- (80)
theorem presup_singular_ssubset_dual (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    presup (E := E) .singular ⊂ presup .dual := by
  refine ⟨fun x hx ↦ ?_, fun h ↦ ?_⟩
  · have hxA := Mereology.atom_iff_isAtom.1 ((Number.mem_dom_singular x).1 hx)
    exact ⟨x, x, hxA, hxA, le_sup_left⟩
  · exact Mereology.not_atom_sup_of_ne (Mereology.atom_iff_isAtom.2 ha)
      (Mereology.atom_iff_isAtom.2 hb) hab
      ((Number.mem_dom_singular _).1 (h ⟨a, b, ha, hb, le_rfl⟩))

-- (80)
theorem presup_dual_ssubset_plural (hy : y ∉ presup (E := E) .dual) :
    presup (E := E) .dual ⊂ presup .plural := by
  rw [presup_plural]
  exact ⟨Set.subset_univ _, fun h ↦ hy (h (Set.mem_univ y))⟩

-- (80b) is lexical: the features' positive values leave the dual unrestricted
theorem presup_dual_ne_dom (hy : y ∉ presup (E := E) .dual) :
    presup (E := E) .dual ≠ Number.dom (some .dual) := fun h ↦
  hy (h.trans Number.dom_dual ▸ Set.mem_univ y)

-- the bound is not vacuous: three individuals exceed it
example : (Set.univ : Set (Fin 3)) ∉ presup (E := Set (Fin 3)) .dual := by
  rintro ⟨a, b, ha, hb, h⟩
  obtain ⟨i, rfl⟩ := Set.isAtom_iff.1 ha
  obtain ⟨j, rfl⟩ := Set.isAtom_iff.1 hb
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j :=
    (by decide : ∀ i j : Fin 3, ∃ k, k ≠ i ∧ k ≠ j) i j
  exact (h (Set.mem_univ k)).elim hki hkj

variable (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hy : y ∉ presup (E := E) .dual)

include ha hb hab hy

/-- Strong taboo » MP! » weak taboo recruits the plural only, as in Slovenian (83b). -/
theorem stod_mp_wtod :
    (Tableau.ofList number [sToD number (presup (E := E)), mp number (presup (E := E)),
      wToD number (presup (E := E))]).optimal = {.plural} := by
  refine sToD_top (by decide) ?_ _
  intro d hd hne
  obtain rfl | rfl | rfl := by simpa [number] using hd
  · exact (presup_singular_ssubset_dual ha hb hab).trans (presup_dual_ssubset_plural hy)
  · exact presup_dual_ssubset_plural hy
  · exact absurd rfl hne

/-- Weak taboo » MP! » strong taboo recruits the dual only, as in Mwotlap and Kharia (83a). -/
theorem wtod_mp_stod :
    (Tableau.ofList number [wToD number (presup (E := E)), mp number (presup (E := E)),
      sToD number (presup (E := E))]).optimal = {.dual} :=
  wToD_mp (presup_singular_ssubset_dual ha hb hab) (presup_dual_ssubset_plural hy) _

/-- The weak taboo alone leaves dual and plural, the non-escalating system of Imere (83d). -/
theorem wtod_alone :
    (Tableau.ofList number [wToD number (presup (E := E))]).optimal = {.dual, .plural} :=
  wToD_alone (presup_singular_ssubset_dual ha hb hab) (presup_dual_ssubset_plural hy)

-- with MP! on top the strongest form wins, the absence of honorification
theorem mp_stod_wtod :
    (Tableau.ofList number [mp number (presup (E := E)), sToD number (presup (E := E)),
      wToD number (presup (E := E))]).optimal = {.singular} := by
  refine mp_top (by decide) ?_ _
  intro d hd hne
  obtain rfl | rfl | rfl := by simpa [number] using hd
  · exact absurd rfl hne
  · exact presup_singular_ssubset_dual ha hb hab
  · exact (presup_singular_ssubset_dual ha hb hab).trans (presup_dual_ssubset_plural hy)

-- (28): no ranking with the strong taboo on top recruits the singular
theorem singular_notMem_optimal_of_sToD_top (Fs : List (Constraint Number)) :
    Number.singular ∉ (Tableau.ofList number (sToD number (presup (E := E)) :: Fs)).optimal :=
  notMem_optimal_of_sToD_top (b := .plural) (by decide)
    ((presup_singular_ssubset_dual ha hb hab).trans (presup_dual_ssubset_plural hy)) Fs

end Number

end Wang2023
