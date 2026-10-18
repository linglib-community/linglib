/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Tactic.DeriveFintype

/-!
# Strict CV: proper government and the Empty Category Principle

In Strict CV the skeleton is a strict sequence of CV units, so the nuclei of a domain form a
sequence. A nucleus may stay silent only when its silence is licensed: by proper government from
a following nucleus, by enclosure in a domain of infrasegmental government, or at the end of the
domain where the language allows an empty final nucleus. This is the Empty Category Principle.
Government is discharged from right to left by lateral actors: pronounced nuclei and, where the
language allows it, an empty final nucleus. A realization is the set of nuclei that are
pronounced. The standard realization pronounces an empty nucleus exactly when nothing licenses
its silence, and it exists and is unique.

## Main definitions

* `StrictCV.FinalNucleus`: whether a final nucleus may be empty, and whether it then acts.
* `StrictCV.Profile`: the nuclei with melody, those required on independent grounds, and those
  flanked by consonants that may contract infrasegmental government.
* `StrictCV.Acts`, `StrictCV.Enclosed`, `StrictCV.ProperlyGoverned`,
  `StrictCV.SilenceLicensed`: lateral actors and the ways a silence is licensed.
* `StrictCV.SatisfiesECP`, `StrictCV.IsStandard`, `StrictCV.standard`.

## Main results

* `StrictCV.isStandard_standard`, `StrictCV.IsStandard.eq`: the standard realization exists and
  is unique.
* `StrictCV.IsStandard.satisfiesECP`: it satisfies the Empty Category Principle.

## Implementation notes

The lateral actors are the pronounced nuclei, an epenthetic one included, as in Scheer's
"only phonetically expressed Nuclei can govern and license"; Cavirani's alternative grants
actorship to unpronounced nuclei with melody and is not built. An empty final nucleus either
acts, governing and licensing, or does not, a single parameter, as Scheer and Ziková conclude.
Government passes over a nucleus enclosed in a domain of infrasegmental government and binds the
first nucleus whose silence is not licensed otherwise. Whether two consonants may contract
infrasegmental government is a fact about their melody, supplied by the profile; that the
governing consonant must be licensed by its own nucleus is built in. The distribution of
government and licensing over onsets, which the two versions of the Coda Mirror state
differently, is not modelled: proper government of nuclei is the same in both. A nucleus can be
required on independent grounds, as a guttural needs a pronounced licensor or an initial empty CV
unit needs a pronounced first nucleus to govern it.

## References

* [lowenstamm-1996]
* [kaye-lowenstamm-vergnaud-1990]
* [charette-1991]
* [scheer-2004]
* [scheer-zikova-2010]
* [cavirani-2022]
-/

@[expose] public section

namespace StrictCV

/-- How a language treats the final nucleus of a domain ([scheer-zikova-2010] §5). -/
structure FinalNucleus where
  /-- A final nucleus may stay empty. -/
  empty : Bool
  /-- An empty final nucleus is a lateral actor, governing and licensing. -/
  acts : Bool
  deriving DecidableEq, Repr, Fintype

/-- What the lateral computation reads off a domain with `n` nuclei. -/
structure Profile (n : ℕ) where
  /-- The nuclei with melody. -/
  full : Finset (Fin n)
  /-- The nuclei that must be pronounced on independent grounds. -/
  forced : Finset (Fin n) := ∅
  /-- The nuclei flanked by a consonant and a following one that may govern it
  ([scheer-2004] (49a)). -/
  cluster : Finset (Fin n) := ∅
  deriving DecidableEq

variable {n : ℕ} (p : FinalNucleus) (w : Profile n) (R : Finset (Fin n))

/-- Nucleus `j` is the last of the domain. -/
def IsLast (j : Fin n) : Prop := j.val + 1 = n

instance (j : Fin n) : Decidable (IsLast j) := inferInstanceAs (Decidable (_ = _))

/-- The lateral actors of a realization `R` are its pronounced nuclei, and an empty final nucleus
where final nuclei act. -/
def Acts (j : Fin n) : Prop := j ∈ R ∨ (IsLast j ∧ p.acts = true)

instance (j : Fin n) : Decidable (Acts p R j) := inferInstanceAs (Decidable (_ ∨ _))

/-- Nucleus `j` is enclosed in a domain of infrasegmental government when it is empty, its flanking
consonants may contract government, and the governing consonant is licensed by its own nucleus,
which acts ([scheer-2004] (49), (50)). -/
def Enclosed (j : Fin n) : Prop :=
  j ∉ w.full ∧ j ∈ w.cluster ∧ ∃ k : Fin n, k.val = j.val + 1 ∧ Acts p R k

instance (j : Fin n) : Decidable (Enclosed p w R j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _, _))

/-- Nucleus `j` is properly governed when it is empty, not enclosed, and the first following
nucleus that is not enclosed acts: government binds the first nucleus whose silence is not
licensed otherwise ([scheer-2004] §75). -/
def ProperlyGoverned (j : Fin n) : Prop :=
  j ∉ w.full ∧ ¬ Enclosed p w R j ∧
    ∃ k, j < k ∧ Acts p R k ∧ ∀ i, j < i → i < k → Enclosed p w R i

instance (j : Fin n) : Decidable (ProperlyGoverned p w R j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _, _ ∧ _ ∧ ∀ _, _))

/-- The silence of nucleus `j` is licensed when it is properly governed, enclosed, or final where
final nuclei may be empty ([scheer-2004] (53)). -/
def SilenceLicensed (j : Fin n) : Prop :=
  ProperlyGoverned p w R j ∨ Enclosed p w R j ∨ (IsLast j ∧ p.empty = true)

instance (j : Fin n) : Decidable (SilenceLicensed p w R j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The Empty Category Principle requires melody to be pronounced and the silence of every silent
nucleus to be licensed. -/
def SatisfiesECP : Prop := w.full ⊆ R ∧ ∀ j, j ∉ R → SilenceLicensed p w R j

instance : Decidable (SatisfiesECP p w R) := inferInstanceAs (Decidable (_ ∧ ∀ _, _))

/-- The standard realization pronounces the nuclei with melody, the required ones, and exactly the
nuclei whose silence is not licensed. -/
def IsStandard : Prop := ∀ j, j ∈ R ↔ j ∈ w.full ∨ j ∈ w.forced ∨ ¬ SilenceLicensed p w R j

instance : Decidable (IsStandard p w R) := inferInstanceAs (Decidable (∀ _, _))

/-! ### Locality

Whether the silence of a nucleus is licensed depends only on the nuclei after it, since lateral
relations are discharged from right to left. -/

section Locality

variable {p w} {R R' : Finset (Fin n)} {j : Fin n}

theorem acts_congr {k : Fin n} (h : k ∈ R ↔ k ∈ R') : Acts p R k ↔ Acts p R' k := by
  simp only [Acts, h]

theorem enclosed_congr (h : ∀ i, j < i → (i ∈ R ↔ i ∈ R')) :
    Enclosed p w R j ↔ Enclosed p w R' j :=
  and_congr_right' <| and_congr_right' <| exists_congr fun k ↦ and_congr_right fun hk ↦
    acts_congr (h k (Fin.lt_def.2 (by omega)))

theorem properlyGoverned_congr (h : ∀ i, j < i → (i ∈ R ↔ i ∈ R')) :
    ProperlyGoverned p w R j ↔ ProperlyGoverned p w R' j := by
  unfold ProperlyGoverned
  rw [enclosed_congr h]
  exact and_congr_right' <| and_congr_right' <| exists_congr fun k ↦ and_congr_right fun hk ↦
    and_congr (acts_congr (h k hk)) <| forall_congr' fun i ↦ forall_congr' fun hi ↦
      forall_congr' fun _ ↦ enclosed_congr fun i' hi' ↦ h i' (hi.trans hi')

theorem silenceLicensed_congr (h : ∀ i, j < i → (i ∈ R ↔ i ∈ R')) :
    SilenceLicensed p w R j ↔ SilenceLicensed p w R' j := by
  unfold SilenceLicensed
  rw [properlyGoverned_congr h, enclosed_congr h]

end Locality

/-! ### The standard realization -/

section Standard

variable {p w R}

theorem IsStandard.satisfiesECP (h : IsStandard p w R) : SatisfiesECP p w R :=
  ⟨fun j hj ↦ (h j).2 (.inl hj), fun j hj ↦ by_contra fun hs ↦ hj ((h j).2 (.inr (.inr hs)))⟩

theorem IsStandard.forced_subset (h : IsStandard p w R) : w.forced ⊆ R :=
  fun j hj ↦ (h j).2 (.inr (.inl hj))

/-- The standard realization is unique. -/
theorem IsStandard.eq {R' : Finset (Fin n)} (h : IsStandard p w R) (h' : IsStandard p w R') :
    R = R' := by
  ext j
  induction j using WellFoundedGT.induction with
  | ind j ih => rw [h, h', silenceLicensed_congr ih]

variable (p w)

/-- The standard realization among the last `d` nuclei, built from the right. -/
def standardFrom : ℕ → Finset (Fin n)
  | 0 => ∅
  | d + 1 =>
    if h : d < n then
      let j : Fin n := ⟨n - 1 - d, by omega⟩
      if j ∈ w.full ∨ j ∈ w.forced ∨ ¬ SilenceLicensed p w (standardFrom d) j then
        insert j (standardFrom d)
      else standardFrom d
    else standardFrom d

/-- The standard realization. -/
def standard : Finset (Fin n) := standardFrom p w n

variable {p w} {i : Fin n} {d : ℕ}

theorem le_of_mem_standardFrom : ∀ {d : ℕ}, i ∈ standardFrom p w d → n - d ≤ i.val
  | 0, h => absurd h (Finset.notMem_empty _)
  | d + 1, h => by
    simp only [standardFrom] at h
    split_ifs at h with hd
    · rcases Finset.mem_insert.1 h with rfl | h
      · simp only; omega
      · have := le_of_mem_standardFrom h; omega
    · have := le_of_mem_standardFrom h; omega
    · have := le_of_mem_standardFrom h; omega

theorem mem_standardFrom_succ_iff (hi : n - d ≤ i.val) :
    i ∈ standardFrom p w (d + 1) ↔ i ∈ standardFrom p w d := by
  simp only [standardFrom]
  split_ifs with hd
  · rw [Finset.mem_insert, or_iff_right fun h ↦ by rw [h] at hi; simp only at hi; omega]
  · rfl
  · rfl

theorem mem_standardFrom_iff_of_le {e : ℕ} (hde : d ≤ e) (hi : n - d ≤ i.val) :
    i ∈ standardFrom p w e ↔ i ∈ standardFrom p w d := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e hde ih => rw [mem_standardFrom_succ_iff (by omega), ih]

variable (p w)

/-- The standard realization exists. -/
theorem isStandard_standard : IsStandard p w (standard p w) := by
  intro j
  have hd : n - 1 - j.val < n := by omega
  have hj : (⟨n - 1 - (n - 1 - j.val), by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
  have hagree : ∀ i, j < i → (i ∈ standard p w ↔ i ∈ standardFrom p w (n - 1 - j.val)) :=
    fun i hi ↦ mem_standardFrom_iff_of_le (by omega) (by have := Fin.lt_def.1 hi; omega)
  rw [silenceLicensed_congr hagree, standard,
    mem_standardFrom_iff_of_le (d := n - 1 - j.val + 1) (by omega) (by omega)]
  simp only [standardFrom, hd, dite_true, hj]
  split_ifs with hc
  · simp only [Finset.mem_insert_self, hc]
  · simp only [hc, iff_false]
    exact fun h ↦ absurd (le_of_mem_standardFrom h) (by omega)

theorem existsUnique_isStandard : ∃! R, IsStandard p w R :=
  ⟨standard p w, isStandard_standard p w, fun _ h ↦ h.eq (isStandard_standard p w)⟩

end Standard

end StrictCV
