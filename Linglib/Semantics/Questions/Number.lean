module

public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Order.Atoms
public import Linglib.Semantics.Presupposition.Strengthening
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Semantics.Questions.HamblinSet

/-!
# Number in Hamblin sets

This file defines the Hamblin sets of *wh* phrases over a lattice of pluralities. A situation is
identified with the plurality the nucleus holds of, so the member for `x` is `Set.Ici x`, and a
phrase of number `n` ranges over the non-null individuals in Sauerland's domain of `n`, the atoms
for a singular phrase and all of them otherwise. Dayal's presupposition on such a Hamblin set
[holds exactly in the situations of the domain](##Question.isExhaustivelyResolvable_whHamblin_iff).
Under competition in number a plural phrase is then [felicitous exactly in the situations that are
neither null nor atomic](##Question.whFelicitous_plural).

## References

* [dayal-1996]
* [dayal-2016]
* [sauerland-2003]
* [heim-1991]
-/

@[expose] public section

namespace Question

open Set Presupposition

variable {E : Type*} [CompleteLattice E]

/-- The individuals a *wh* phrase of number `n` ranges over, the non-null ones in the domain of
`n`: the atoms for singular *which N*, and all of them for plural *which N* and for *who* and
*what*, which carry no number. -/
def whDomain (n : Option Number) : Set E := {x ∈ Number.dom n | x ≠ ⊥}

theorem mem_whDomain_singular {x : E} : x ∈ whDomain (some .singular) ↔ IsAtom x := by
  rw [whDomain, mem_sep_iff, Number.mem_dom_singular, Mereology.atom_iff_isAtom]
  exact ⟨And.left, fun h ↦ ⟨h, h.ne_bot⟩⟩

theorem whDomain_of_ne_singular {n : Option Number} (h : n ≠ some .singular) :
    whDomain n = {x : E | x ≠ ⊥} := by
  simp [whDomain, Number.dom_eq_univ_of_ne_singular h]

theorem mem_whDomain_plural {x : E} : x ∈ whDomain (some .plural) ↔ x ≠ ⊥ := by
  rw [whDomain_of_ne_singular (by simp)]
  rfl

theorem mem_whDomain_of_isAtom (n : Option Number) {a : E} (ha : IsAtom a) : a ∈ whDomain n := by
  by_cases h : n = some .singular
  · exact h ▸ mem_whDomain_singular.2 ha
  · rw [whDomain_of_ne_singular h]
    exact ha.ne_bot

/-- The Hamblin set of a *wh* phrase of number `n`: the member for `x` is `Ici x`, the situations
in which the nucleus holds of `x`. -/
def whHamblin (n : Option Number) : Set (Set E) := Ici '' whDomain n

/-- The situations in which a *wh* question is felicitous: its existential presupposition holds
and that of no competitor with a stronger one does. -/
def whFelicitous (n : Option Number) : Set E :=
  strengthen Number.alts (fun m ↦ presupposition (whHamblin m)) n

variable [IsAtomistic E]

theorem sSup_whDomain_le (n : Option Number) (w : E) : sSup {x ∈ whDomain n | x ≤ w} = w :=
  le_antisymm (sSup_le fun _ hx ↦ hx.2) <| (sSup_atoms_le_eq w).ge.trans <|
    sSup_le_sSup fun _ ⟨ha, haw⟩ ↦ ⟨mem_whDomain_of_isAtom n ha, haw⟩

theorem weakAnswer_whHamblin (n : Option Number) (w : E) : weakAnswer (whHamblin n) w = Ici w := by
  rw [whHamblin, weakAnswer, trueAnswers_image, sInter_image, ← Ici_sSup]
  exact congrArg Ici (sSup_whDomain_le n w)

/-- Ans-D is defined on the Hamblin set of a *wh* phrase exactly in the situations its domain
contains. -/
theorem isExhaustivelyResolvable_whHamblin_iff (n : Option Number) (w : E) :
    IsExhaustivelyResolvable (whHamblin n) w ↔ w ∈ whDomain n := by
  rw [isExhaustivelyResolvable_iff, weakAnswer_whHamblin, whHamblin, Ici_injective.mem_set_image]

theorem presupposition_whHamblin (n : Option Number) :
    presupposition (whHamblin n) = whDomain (E := E) n :=
  Set.ext (isExhaustivelyResolvable_whHamblin_iff n)

theorem whFelicitous_eq_strengthen_whDomain (n : Option Number) :
    whFelicitous (E := E) n = strengthen Number.alts whDomain n := by
  simp only [whFelicitous, presupposition_whHamblin]

theorem whFelicitous_none : whFelicitous (E := E) none = {w | w ≠ ⊥} := by
  rw [whFelicitous_eq_strengthen_whDomain, strengthen_eq_self, whDomain_of_ne_singular (by simp)]
  rintro _ h -
  exact h

theorem whFelicitous_singular : whFelicitous (E := E) (some .singular) = {w | IsAtom w} := by
  rw [whFelicitous_eq_strengthen_whDomain, strengthen_eq_self]
  · exact Set.ext fun _ ↦ mem_whDomain_singular
  · rintro _ (h | h) hss <;> rw [h] at hss
    · exact hss.ne rfl
    · exact hss.not_subset fun x hx ↦ mem_whDomain_of_isAtom _ (mem_whDomain_singular.1 hx)

theorem whFelicitous_of_ne_singular {a b : E} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    {m : Number} (hm : m ≠ .singular) : whFelicitous (some m) = {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  have hne : ∀ {m : Number}, m ≠ .singular → whDomain (some m) = {x : E | x ≠ ⊥} :=
    fun hm ↦ whDomain_of_ne_singular (by simpa using hm)
  have hss : whDomain (some .singular) ⊂ whDomain (E := E) (some m) := by
    refine ⟨fun x hx ↦ mem_whDomain_of_isAtom _ (mem_whDomain_singular.1 hx), fun h ↦ ?_⟩
    have hab' : a ⊔ b ∈ whDomain (some m) := by
      rw [hne hm]
      exact fun h0 ↦ ha.ne_bot (le_bot_iff.1 (h0 ▸ le_sup_left))
    exact Mereology.not_atom_sup_of_ne (Mereology.atom_iff_isAtom.2 ha)
      (Mereology.atom_iff_isAtom.2 hb) hab
      (Mereology.atom_iff_isAtom.2 (mem_whDomain_singular.1 (h hab')))
  rw [whFelicitous_eq_strengthen_whDomain,
    strengthen_eq_sdiff (alts := Number.alts) (ψ := some .singular) (mem_insert _ _) hss, hne hm]
  · exact Set.ext fun _ ↦ and_congr_right fun _ ↦ not_congr mem_whDomain_singular
  · rintro χ (rfl | rfl) hχ
    · exact subset_rfl
    · exact (hχ.ne ((hne (m := .plural) (by decide)).trans (hne hm).symm)).elim

/-- With two atoms, the plural question is felicitous exactly in the situations that are neither
null nor atomic. -/
theorem whFelicitous_plural {a b : E} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    whFelicitous (some .plural) = {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} :=
  whFelicitous_of_ne_singular (E := E) ha hb hab (m := .plural) (by decide)

theorem notMem_whFelicitous_bot (n : Option Number) : (⊥ : E) ∉ whFelicitous n := by
  rw [whFelicitous_eq_strengthen_whDomain]
  exact fun h ↦ (strengthen_subset _ _ _ h).2 rfl

end Question
