/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Proposition

/-!
# Trivalent quantifiers

The trivalent quantifiers come in families that share one truth rule and differ in where
undefinedness projects: `forallWith D p` and `existsWith D p` are the quantifiers over the
instances `p` that are defined exactly where `D` holds. The Weak Kleene quantifiers `forallWeak`
and `existsWeak` are undefined as soon as any instance is, the Strong Kleene quantifiers
`forallStrong` and `existsStrong` are the indexed `⊓` and `⊔`, and Haug's quantifiers
`forallHaug` and `existsHaug` are undefined only when every instance is. Restricted to a pair of
instances, each family is its binary connective (`forallWeak_pair`, `forallStrong_pair`,
`forallHaug_pair`).

Each family is the quantifier of a theory of how a presupposition projects from the scope of a
quantifier. Over the domain's subtype, the Weak Kleene quantifiers project universally, as
Chemla's experiments support, Haug's existentially, as Mayr and Sauerland argue for a semantic
projection that pragmatics then strengthens, and the Strong Kleene existential of Kleene and Fox
is defined exactly where some instance is true or every instance is false; Spector and Sudo
delimit when each reading surfaces.

A trivalent quantifier extends a classical one when it agrees with it on classical predicates
(`IsExtensionOf`), and is regular when it is monotone for the knowledge order (`IsRegular`).

## Implementation notes

The Strong Kleene quantifiers are explicit definitions rather than `⨅` and `⨆`, because a
`CompleteLinearOrder` instance on `Trivalent` would carry a second `LinearOrder` parent that
instance search prefers, making every later `⊓` noncomputable.

## References

* [haug-2014]
* [coppock-beaver-2015]
* [cooper-2023]
* [chemla-2009a]
* [mayr-sauerland-2015]
* [spector-sudo-2017]
* [fox-2013]
* [george-2014]
* [kleene-1952]
-/

@[expose] public section

namespace Trivalent

open Bilattice

variable {W : Type*}

/-! ### Quantifiers

Like the binary connectives, the trivalent quantifiers come in rival families that share one
truth rule and differ only in where undefinedness projects, which `forallWith` and
`existsWith` make definitional: a family is fixed by its definedness condition. The Weak
Kleene quantifiers are undefined as soon as any instance is; the Strong Kleene quantifiers
are defined whenever the instances settle the value, the indexed `⊓` and `⊔`; and the
quantifiers of [haug-2014], adopted by [coppock-beaver-2015] and [cooper-2023], are undefined
only when every instance is, so that a quantified presupposition projects existentially.
Restricted to a pair of instances the families are the binary connectives — Weak Kleene
`meetWeak`, Strong Kleene `⊓`, and, for Haug's quantifier, Belnap's skip-undefined
`meetBelnap` (`forallHaug_pair`). Middle Kleene reads its operands left to right, so no
quantifier restricts to it on a pair of instances. Peters-Kleene deployment, which derives Middle
Kleene from the classical connectives, takes a quantifier's instances as a single argument, and
so gives the Strong Kleene quantifiers ([george-2014] §4.1). -/

open Classical in
/-- `forallWith D p` is the universal quantifier undefined unless `D` holds, and otherwise false
exactly when some instance is. All the families share this truth rule
(`forallWith_eq_forallWith_of_defined`). -/
noncomputable def forallWith {ι : Sort*} (D : Prop) (p : ι → Trivalent) : Trivalent :=
  if D then if ∃ i, p i = .false then .false else .true else .undefined

/-- `existsWith D p` is the existential quantifier of the family whose definedness condition
is `D`, the dual of `forallWith`. -/
noncomputable def existsWith {ι : Sort*} (D : Prop) (p : ι → Trivalent) : Trivalent :=
  (forallWith D fun i ↦ (p i)ᶜ)ᶜ

section WithFamilies

variable {ι : Sort*} {D D' : Prop} {p : ι → Trivalent}

theorem forallWith_eq_undefined_iff : forallWith D p = .undefined ↔ ¬D := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_false_iff : forallWith D p = .false ↔ D ∧ ∃ i, p i = .false := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_true_iff : forallWith D p = .true ↔ D ∧ ∀ i, p i ≠ .false := by
  unfold forallWith; split_ifs <;> simp_all

theorem existsWith_eq_undefined_iff : existsWith D p = .undefined ↔ ¬D := by
  simp [existsWith, forallWith_eq_undefined_iff]

theorem existsWith_eq_true_iff : existsWith D p = .true ↔ D ∧ ∃ i, p i = .true := by
  simp [existsWith, forallWith_eq_false_iff]

theorem existsWith_eq_false_iff : existsWith D p = .false ↔ D ∧ ∀ i, p i ≠ .true := by
  simp [existsWith, forallWith_eq_true_iff]

theorem forallWith_eq_forallWith_of_defined (hD : D) (hD' : D') :
    forallWith D p = forallWith D' p := by
  unfold forallWith
  rw [ite_eq_left hD, ite_eq_left hD']

theorem forallWith_congr (h : D ↔ D') : forallWith D p = forallWith D' p :=
  eq_of_eq_undefined_iff_of_eq_true_iff
    (by rw [forallWith_eq_undefined_iff, forallWith_eq_undefined_iff, h])
    (by rw [forallWith_eq_true_iff, forallWith_eq_true_iff, h])

theorem existsWith_congr (h : D ↔ D') : existsWith D p = existsWith D' p :=
  congrArg compl (forallWith_congr h)

end WithFamilies

/-- The Weak Kleene universal quantifier is undefined when any instance is, and otherwise
classical. -/
noncomputable def forallWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  forallWith (∀ i, p i ≠ .undefined) p

/-- The Weak Kleene existential quantifier is the dual of `forallWeak`. -/
noncomputable def existsWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  existsWith (∀ i, p i ≠ .undefined) p

section WeakQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallWeak_eq_undefined_iff :
    forallWeak p = .undefined ↔ ∃ i, p i = .undefined := by
  rw [forallWeak, forallWith_eq_undefined_iff, not_forall]
  simp

@[simp] theorem forallWeak_eq_true_iff : forallWeak p = .true ↔ ∀ i, p i = .true := by
  rw [forallWeak, forallWith_eq_true_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · exact absurd h (hf i)
    · exact absurd h (hd i)
    · rfl
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallWeak_eq_false_iff :
    forallWeak p = .false ↔ (∀ i, p i ≠ .undefined) ∧ ∃ i, p i = .false := by
  rw [forallWeak, forallWith_eq_false_iff]

@[simp] theorem existsWeak_eq_undefined_iff :
    existsWeak p = .undefined ↔ ∃ i, p i = .undefined := by
  rw [existsWeak, existsWith_eq_undefined_iff, not_forall]
  simp

@[simp] theorem existsWeak_eq_true_iff :
    existsWeak p = .true ↔ (∀ i, p i ≠ .undefined) ∧ ∃ i, p i = .true := by
  rw [existsWeak, existsWith_eq_true_iff]

@[simp] theorem existsWeak_eq_false_iff : existsWeak p = .false ↔ ∀ i, p i = .false := by
  rw [existsWeak, existsWith_eq_false_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · rfl
    · exact absurd h (hd i)
    · exact absurd h (hf i)
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

end WeakQuantifiers

/-- The Strong Kleene universal quantifier is the indexed `⊓`, false when any instance is, true
when all are, and undefined otherwise. -/
noncomputable def forallStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  forallWith ((∃ i, p i = .false) ∨ ∀ i, p i = .true) p

/-- The Strong Kleene existential quantifier is the dual of `forallStrong`, the indexed
`⊔`. -/
noncomputable def existsStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  existsWith ((∃ i, p i = .true) ∨ ∀ i, p i = .false) p

section StrongQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallStrong_eq_false_iff : forallStrong p = .false ↔ ∃ i, p i = .false := by
  rw [forallStrong, forallWith_eq_false_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem forallStrong_eq_true_iff : forallStrong p = .true ↔ ∀ i, p i = .true := by
  rw [forallStrong, forallWith_eq_true_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallStrong_eq_undefined_iff :
    forallStrong p = .undefined ↔ (∀ i, p i ≠ .false) ∧ ∃ i, p i = .undefined := by
  rw [forallStrong, forallWith_eq_undefined_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

theorem forallStrong_ne_undefined_iff :
    forallStrong p ≠ .undefined ↔ (∃ i, p i = .false) ∨ ∀ i, p i ≠ .undefined := by
  rw [ne_eq, forallStrong_eq_undefined_iff, not_and_or, not_forall_not, not_exists]

@[simp] theorem existsStrong_eq_true_iff : existsStrong p = .true ↔ ∃ i, p i = .true := by
  rw [existsStrong, existsWith_eq_true_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem existsStrong_eq_false_iff : existsStrong p = .false ↔ ∀ i, p i = .false := by
  rw [existsStrong, existsWith_eq_false_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem existsStrong_eq_undefined_iff :
    existsStrong p = .undefined ↔ (∀ i, p i ≠ .true) ∧ ∃ i, p i = .undefined := by
  rw [existsStrong, existsWith_eq_undefined_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

theorem existsStrong_ne_undefined_iff :
    existsStrong p ≠ .undefined ↔ (∃ i, p i = .true) ∨ ∀ i, p i ≠ .undefined := by
  rw [ne_eq, existsStrong_eq_undefined_iff, not_and_or, not_forall_not, not_exists]

/-- The Strong Kleene quantifiers are dual under Kleene's negation. -/
theorem compl_forallStrong : (forallStrong p)ᶜ = existsStrong fun i ↦ (p i)ᶜ :=
  eq_of_eq_true_iff_of_eq_false_iff (by simp) (by simp)

end StrongQuantifiers

/-- Haug's universal quantifier skips undefined instances — undefined only when every
instance is, false when some instance is, and true otherwise. -/
noncomputable def forallHaug (p : W → Trivalent) : Trivalent :=
  forallWith (∃ w, p w ≠ .undefined) p

/-- The dual of `forallHaug`. -/
noncomputable def existsHaug (p : W → Trivalent) : Trivalent :=
  existsWith (∃ w, p w ≠ .undefined) p

section HaugQuantifiers

variable {p : W → Trivalent}

@[simp] theorem forallHaug_eq_undefined_iff :
    forallHaug p = .undefined ↔ ∀ w, p w = .undefined := by
  rw [forallHaug, forallWith_eq_undefined_iff, not_exists]
  simp

@[simp] theorem forallHaug_eq_false_iff : forallHaug p = .false ↔ ∃ w, p w = .false := by
  rw [forallHaug, forallWith_eq_false_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem forallHaug_eq_true_iff :
    forallHaug p = .true ↔ (∃ w, p w ≠ .undefined) ∧ ∀ w, p w ≠ .false := by
  rw [forallHaug, forallWith_eq_true_iff]

@[simp] theorem existsHaug_eq_undefined_iff :
    existsHaug p = .undefined ↔ ∀ w, p w = .undefined := by
  rw [existsHaug, existsWith_eq_undefined_iff, not_exists]
  simp

@[simp] theorem existsHaug_eq_true_iff : existsHaug p = .true ↔ ∃ w, p w = .true := by
  rw [existsHaug, existsWith_eq_true_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem existsHaug_eq_false_iff :
    existsHaug p = .false ↔ (∃ w, p w ≠ .undefined) ∧ ∀ w, p w ≠ .true := by
  rw [existsHaug, existsWith_eq_false_iff]

end HaugQuantifiers

/-! ### Each family restricted to a pair is its binary connective

One lemma carries the correspondence: the gap-policy quantifier at a pair of instances is
the gap-policy connective at the matching policy (`forallWith_pair`), and each family's
pair lemma instantiates it. -/

section Pairs

variable (a b : Trivalent)

theorem forallWith_pair {D : Prop} [Decidable D] :
    forallWith D (fun i : Bool => bif i then a else b) = meetWith D a b := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · rw [forallWith_eq_undefined_iff, meetWith_eq_undefined_iff]
  · rw [forallWith_eq_true_iff, meetWith_eq_true_iff, Bool.forall_bool]
    exact and_congr_right fun _ => and_comm

theorem existsWith_pair {D : Prop} [Decidable D] :
    existsWith D (fun i : Bool => bif i then a else b) = joinWith D a b := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · rw [existsWith_eq_undefined_iff, joinWith_eq_undefined_iff]
  · rw [existsWith_eq_true_iff, joinWith_eq_true_iff, Bool.exists_bool]
    exact and_congr_right fun _ => or_comm

theorem forallWeak_pair : forallWeak (fun i : Bool => bif i then a else b) = meetWeak a b :=
  (forallWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((forallWith_pair a b).trans (meetWeak_eq_meetWith a b).symm)

theorem existsWeak_pair : existsWeak (fun i : Bool => bif i then a else b) = joinWeak a b :=
  (existsWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((existsWith_pair a b).trans (joinWeak_eq_joinWith a b).symm)

theorem forallStrong_pair :
    forallStrong (fun i : Bool => bif i then a else b) = a ⊓ b :=
  (forallWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((forallWith_pair a b).trans (inf_eq_meetWith a b).symm)

theorem existsStrong_pair :
    existsStrong (fun i : Bool => bif i then a else b) = a ⊔ b :=
  (existsWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((existsWith_pair a b).trans (sup_eq_joinWith a b).symm)

theorem forallHaug_pair :
    forallHaug (fun i : Bool => bif i then a else b) = meetBelnap a b :=
  (forallWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((forallWith_pair a b).trans (meetBelnap_eq_meetWith a b).symm)

theorem existsHaug_pair :
    existsHaug (fun i : Bool => bif i then a else b) = joinBelnap a b :=
  (existsWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((existsWith_pair a b).trans (joinBelnap_eq_joinWith a b).symm)

end Pairs

theorem existsHaug_presuppose_ne_false (p : W → Trivalent) :
    existsHaug (fun w => (p w ⊔ .undefined)) ≠ .false := by
  simp

/-- Quantifier Projection ([coppock-beaver-2015]'s appendix) lets a presupposition under the
existential project as an existentially quantified presupposition, over bivalent `φ` and
`ψ`. -/
theorem existsHaug_meetWeak_presuppose {φ ψ : W → Trivalent} (hφ : IsBivalent φ)
    (hψ : IsBivalent ψ) :
    existsHaug (fun w => meetWeak (φ w ⊔ .undefined) (ψ w)) =
      meetWeak (existsHaug fun w => (φ w ⊔ .undefined))
        (existsHaug fun w => meetWeak (φ w) (ψ w)) := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · simp only [existsHaug_eq_undefined_iff, meetWeak_eq_undefined_iff,
      sup_undefined_eq_undefined_iff, hφ.ne_undefined,
      hψ.ne_undefined, or_false]
    exact ⟨Or.inl, fun h => h.elim id fun h w => (h w).elim⟩
  · simp only [existsHaug_eq_true_iff, meetWeak_eq_true_iff, sup_undefined_eq_true_iff]
    exact ⟨fun ⟨w, h⟩ => ⟨⟨w, h.1⟩, w, h⟩, fun h => h.2⟩

/-! ### Regular extensions of a quantifier -/

section Regular

variable {U : Type*}

open Classical in
/-- A trivalent quantifier is an extension of `Q` when it has the value of `Q` at every classical
predicate. -/
def IsExtensionOf (Q : Set U → Prop) (T : (U → Trivalent) → Trivalent) : Prop :=
  ∀ R : Set U, T (fun u ↦ ofProp (u ∈ R)) = ofProp (Q R)

/-- A trivalent quantifier is regular when more information about its argument gives more
information about its value ([kleene-1952]). -/
def IsRegular (T : (U → Trivalent) → Trivalent) : Prop :=
  ∀ ⦃A A' : U → Trivalent⦄, (∀ u, A u ≤ₖ A' u) → T A ≤ₖ T A'

end Regular

end Trivalent
