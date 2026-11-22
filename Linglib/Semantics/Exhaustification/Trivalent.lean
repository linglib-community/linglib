module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Logic.Trivalent.Quantifier

/-!
# Trivalent exhaustification

For a negation `neg` of three-valued truth, we define the exhaustification `exhWith neg alts p` of
a trivalent prejacent `p` against trivalent alternatives `alts`. An alternative is excluded when
it is innocently excludable in Fox's sense, a set of propositions being consistent when some world
makes the prejacent and the negation of each of them true, and the exhaustification is the Weak
Kleene conjunction of the prejacent with the negations of the excluded alternatives
(`exhWith_apply_eq_meetWeak`).

Spector and Sudo's two operators are its two instances. `exh1` negates weakly, an alternative
that is not true counting as denied, so it is undefined exactly where its prejacent is
(`exh1_eq_undefined_iff`) and is true where classical innocent exclusion on the truth conditions
is (`posExt_exh1`). `exh2` negates strongly, so an alternative is excluded only if it can be false
where the prejacent is true, and the operator inherits the presuppositions of the alternatives it
excludes (`exh2_eq_undefined_iff`). Exhaustification that excludes nothing returns its prejacent
(`exhWith_eq_self`).

## References

* [spector-sudo-2017]
* [fox-2007]
-/

@[expose] public section

namespace Exhaustification.Trivalent

open Exhaustification

variable {W ι : Type*} [Fintype W] [Fintype ι] (neg : Trivalent → Trivalent)
  (alts : ι → W → Trivalent) (p : W → Trivalent)

/-- An alternative is excluded when it is innocently excludable given the prejacent, a set of
alternatives being consistently excluded when some world makes the prejacent and the negation of
each of them true. -/
def Excluded (i : ι) : Prop :=
  IsInnocentlyExcludable (Set.range fun j ↦ {w | neg (alts j w) ≠ .true}) (Trivalent.posExt p)
    {w | neg (alts i w) ≠ .true}

instance (i : ι) : Decidable (Excluded neg alts p i) :=
  inferInstanceAs (Decidable (IsInnocentlyExcludable
    (Set.range fun j ↦ {w | neg (alts j w) ≠ .true}) (Trivalent.posExt p)
    ((fun j ↦ {w | neg (alts j w) ≠ .true}) i)))

/-- Exhaustification with the negation `neg` is undefined where the prejacent or the negation of
some excluded alternative is, true where the prejacent and the negation of every excluded
alternative are true, and false otherwise. -/
def exhWith (w : W) : Trivalent :=
  if p w = .undefined ∨ ∃ i, Excluded neg alts p i ∧ neg (alts i w) = .undefined then .undefined
  else if p w = .true ∧ ∀ i, Excluded neg alts p i → neg (alts i w) = .true then .true else .false

/-- Weak-negation exhaustification denies an alternative where it is not true. -/
abbrev exh1 : W → Trivalent := exhWith (fun a ↦ (Trivalent.ofProp (a = .true))ᶜ) alts p

/-- Strong-negation exhaustification denies an alternative where it is false. -/
abbrev exh2 : W → Trivalent := exhWith (·ᶜ) alts p

variable {neg alts p} {w : W}

theorem exhWith_eq_undefined_iff :
    exhWith neg alts p w = .undefined ↔
      p w = .undefined ∨ ∃ i, Excluded neg alts p i ∧ neg (alts i w) = .undefined := by
  unfold exhWith; split_ifs <;> simp_all

theorem exhWith_eq_true_iff :
    exhWith neg alts p w = .true ↔
      p w = .true ∧ ∀ i, Excluded neg alts p i → neg (alts i w) = .true := by
  unfold exhWith
  split_ifs with h₁ h₂
  · refine iff_of_false (by decide) fun ⟨hp, ha⟩ ↦ ?_
    rcases h₁ with h | ⟨i, hi, hu⟩
    · exact absurd (hp.symm.trans h) (by decide)
    · exact absurd ((ha i hi).symm.trans hu) (by decide)
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by decide) h₂

/-- Exhaustification is the Weak Kleene conjunction of the prejacent with the negations of the
excluded alternatives. -/
theorem exhWith_apply_eq_meetWeak :
    exhWith neg alts p w = Trivalent.meetWeak (p w)
      (Trivalent.forallWeak fun i : {i // Excluded neg alts p i} ↦ neg (alts i w)) :=
  Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff
    (by simp [exhWith_eq_undefined_iff]) (by simp [exhWith_eq_true_iff])

/-- Exhaustification that excludes no alternative returns its prejacent. -/
theorem exhWith_eq_self (h : ∀ i, ¬ Excluded neg alts p i) : exhWith neg alts p = p :=
  funext fun _ ↦ Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff
    (by simp [exhWith_eq_undefined_iff, h]) (by simp [exhWith_eq_true_iff, h])

omit [Fintype W] [Fintype ι] in
/-- If the prejacent and the negations of all the alternatives are true together somewhere, every
alternative is excluded. -/
theorem Excluded.of_exists (h : ∃ w, p w = .true ∧ ∀ j, neg (alts j w) = .true) (i : ι) :
    Excluded neg alts p i :=
  let ⟨w, hp, hw⟩ := h
  IsInnocentlyExcludable.of_full_exclusion_consistent (Set.mem_range_self i)
    ⟨w, hp, by rintro _ ⟨j, rfl⟩; exact fun hn ↦ hn (hw j)⟩

omit [Fintype W] in
/-- An alternative whose negation is true nowhere that a satisfiable prejacent is true is not
excluded. -/
theorem not_excluded_of_forall {i : ι} (hp : ∃ w, p w = .true)
    (h : ∀ w, p w = .true → neg (alts i w) ≠ .true) : ¬ Excluded neg alts p i :=
  not_isInnocentlyExcludable_of_phi_subset (φ := Trivalent.posExt p) (Set.finite_range _) hp h

/-! ### Weak negation -/

omit [Fintype W] in
private theorem setOf_weakNeg_ne_true (a : W → Trivalent) :
    {w | (Trivalent.ofProp (a w = .true))ᶜ ≠ .true} = Trivalent.posExt a := by
  ext w; simp

theorem exh1_eq_undefined_iff : exh1 alts p w = .undefined ↔ p w = .undefined := by
  simp [exhWith_eq_undefined_iff]

/-- Weak-negation exhaustification is true where classical innocent exclusion on the truth
conditions is. -/
theorem posExt_exh1 :
    Trivalent.posExt (exh1 alts p) =
      exhIE (Set.range fun j ↦ Trivalent.posExt (alts j)) (Trivalent.posExt p) := by
  ext w
  simp only [Trivalent.mem_posExt, exhWith_eq_true_iff, mem_exhIE_iff, Excluded,
    setOf_weakNeg_ne_true]
  refine and_congr_right fun _ ↦ ⟨fun h a ha ↦ ?_, fun h i hi ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := ha.1
    simpa using h i ha
  · simpa using h _ hi

/-! ### Strong negation -/

theorem exh2_eq_undefined_iff :
    exh2 alts p w = .undefined ↔
      p w = .undefined ∨ ∃ i, Excluded (·ᶜ) alts p i ∧ alts i w = .undefined := by
  simp [exhWith_eq_undefined_iff]

theorem exh2_eq_true_iff :
    exh2 alts p w = .true ↔ p w = .true ∧ ∀ i, Excluded (·ᶜ) alts p i → alts i w = .false := by
  simp [exhWith_eq_true_iff]

end Exhaustification.Trivalent
