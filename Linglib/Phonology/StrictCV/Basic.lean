/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Nat.Even
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
* `StrictCV.Profile.drop`: the profile of the last nuclei of a domain.

## Main results

* `StrictCV.isStandard_standard`, `StrictCV.IsStandard.eq`: the standard realization exists and
  is unique.
* `StrictCV.IsStandard.satisfiesECP`: it satisfies the Empty Category Principle.
* `StrictCV.silenceLicensed_iff_acts`: a nucleus is governed by the next one, when that one acts.
* `StrictCV.mem_standard_iff_even`, `StrictCV.mem_standard_iff_even_of_final`: in a run of nuclei
  without melody every other one is pronounced, counting from the right, which is Havlík's Law.
* `StrictCV.dropRealization_standard`: the realization of the last nuclei of a domain is computed
  from them alone.

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
  /-- The nuclei without melody, not even floating, flanked by a consonant and a following one that
  may govern it ([scheer-2004] (49a)). -/
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
which only a pronounced nucleus can do ([scheer-2004] (49), (50)). -/
def Enclosed (j : Fin n) : Prop :=
  j ∉ w.full ∧ j ∈ w.cluster ∧ ∃ k : Fin n, k.val = j.val + 1 ∧ k ∈ R

instance (j : Fin n) : Decidable (Enclosed w R j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _, _))

/-- Nucleus `j` is properly governed when it is empty, not enclosed, and the first following
nucleus that is not enclosed acts: government binds the first nucleus whose silence is not
licensed otherwise ([scheer-2004] §75). -/
def ProperlyGoverned (j : Fin n) : Prop :=
  j ∉ w.full ∧ ¬ Enclosed w R j ∧
    ∃ k, j < k ∧ Acts p R k ∧ ∀ i, j < i → i < k → Enclosed w R i

instance (j : Fin n) : Decidable (ProperlyGoverned p w R j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _, _ ∧ _ ∧ ∀ _, _))

/-- The silence of nucleus `j` is licensed when it is properly governed, enclosed, or final where
final nuclei may be empty ([scheer-2004] (53)). -/
def SilenceLicensed (j : Fin n) : Prop :=
  ProperlyGoverned p w R j ∨ Enclosed w R j ∨ (IsLast j ∧ p.empty = true)

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
    Enclosed w R j ↔ Enclosed w R' j :=
  and_congr_right' <| and_congr_right' <| exists_congr fun k ↦ and_congr_right fun hk ↦
    h k (Fin.lt_def.2 (by omega))

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

variable {p w}

theorem mem_standard_iff {j : Fin n} :
    j ∈ standard p w ↔ j ∈ w.full ∨ j ∈ w.forced ∨ ¬ SilenceLicensed p w (standard p w) j :=
  isStandard_standard p w j

end Standard

/-! ### Government from the following nucleus -/

section Successor

variable {p w R} {x y : Fin n}

/-- A nucleus without melody, followed by a nucleus that no domain of infrasegmental government
encloses, has its silence licensed exactly when that nucleus acts: government comes from the
following nucleus, and only one nucleus is governed by it ([scheer-2004] §23). -/
theorem silenceLicensed_iff_acts (hy : y.val = x.val + 1) (hf : x ∉ w.full)
    (hx : ¬ Enclosed w R x) (hye : ¬ Enclosed w R y) :
    SilenceLicensed p w R x ↔ Acts p R y := by
  have hxy : x < y := Fin.lt_def.2 (by omega)
  constructor
  · rintro (⟨-, -, k, hxk, hk, hbet⟩ | h | ⟨hl, -⟩)
    · obtain rfl | hyk := eq_or_lt_of_le (show y ≤ k from Fin.le_def.2 (by
        have := Fin.lt_def.1 hxk; omega))
      · exact hk
      · exact absurd (hbet y hxy hyk) hye
    · exact absurd h hx
    · have := y.isLt; unfold IsLast at hl; omega
  · intro h
    refine .inl ⟨hf, hx, y, hxy, h, fun i hi hiy ↦ ?_⟩
    have := Fin.lt_def.1 hi; have := Fin.lt_def.1 hiy; omega

end Successor

/-! ### Locality over a final stretch

Lateral relations run from right to left, so the realization of the last nuclei of a domain is
computed from those nuclei alone. -/

section Drop

variable {k m : ℕ}

/-- The profile of the last `m` nuclei of a domain of `k + m`. -/
def Profile.drop (k : ℕ) (w : Profile (k + m)) : Profile m where
  full := Finset.univ.filter fun j ↦ Fin.natAdd k j ∈ w.full
  forced := Finset.univ.filter fun j ↦ Fin.natAdd k j ∈ w.forced
  cluster := Finset.univ.filter fun j ↦ Fin.natAdd k j ∈ w.cluster

/-- The nuclei of a realization among the last `m`, renumbered from the first of them. -/
def dropRealization (k : ℕ) (R : Finset (Fin (k + m))) : Finset (Fin m) :=
  Finset.univ.filter fun j ↦ Fin.natAdd k j ∈ R

variable {p : FinalNucleus} {w : Profile (k + m)} {R : Finset (Fin (k + m))} {j : Fin m}

@[simp] theorem mem_dropRealization : j ∈ dropRealization k R ↔ Fin.natAdd k j ∈ R := by
  simp [dropRealization]

private theorem exists_natAdd_eq {i : Fin (k + m)} (h : k ≤ i.val) :
    ∃ i' : Fin m, Fin.natAdd k i' = i :=
  ⟨⟨i.val - k, by omega⟩, Fin.ext (by simp; omega)⟩

theorem acts_natAdd {j : Fin m} :
    Acts p R (Fin.natAdd k j) ↔ Acts p (dropRealization k R) j := by
  simp only [Acts, IsLast, Fin.val_natAdd, mem_dropRealization]
  exact or_congr_right (and_congr_left' (by omega))

theorem enclosed_natAdd :
    Enclosed w R (Fin.natAdd k j) ↔ Enclosed (w.drop k) (dropRealization k R) j := by
  simp only [Enclosed, Profile.drop, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_dropRealization, Fin.val_natAdd]
  refine and_congr_right' <| and_congr_right' ⟨fun ⟨i, hi, hR⟩ ↦ ?_, fun ⟨i, hi, hR⟩ ↦ ?_⟩
  · obtain ⟨i', rfl⟩ := exists_natAdd_eq (i := i) (by omega)
    exact ⟨i', by simp at hi; omega, hR⟩
  · exact ⟨_, by simp; omega, hR⟩

theorem properlyGoverned_natAdd :
    ProperlyGoverned p w R (Fin.natAdd k j) ↔
      ProperlyGoverned p (w.drop k) (dropRealization k R) j := by
  unfold ProperlyGoverned
  rw [enclosed_natAdd]
  simp only [Profile.drop, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right' <| and_congr_right'
    ⟨fun ⟨i, hji, hi, hbet⟩ ↦ ?_, fun ⟨i, hji, hi, hbet⟩ ↦ ?_⟩
  · obtain ⟨i', rfl⟩ := exists_natAdd_eq (i := i) (by have := Fin.lt_def.1 hji; simp at this; omega)
    refine ⟨i', (Fin.natAdd_lt_natAdd_iff k).1 hji, acts_natAdd.1 hi, fun l hjl hli ↦ ?_⟩
    exact enclosed_natAdd.1 (hbet _ ((Fin.natAdd_lt_natAdd_iff k).2 hjl)
      ((Fin.natAdd_lt_natAdd_iff k).2 hli))
  · refine ⟨Fin.natAdd k i, (Fin.natAdd_lt_natAdd_iff k).2 hji, acts_natAdd.2 hi,
      fun l hjl hli ↦ ?_⟩
    obtain ⟨l', rfl⟩ := exists_natAdd_eq (i := l) (by have := Fin.lt_def.1 hjl; simp at this; omega)
    exact enclosed_natAdd.2 (hbet l' ((Fin.natAdd_lt_natAdd_iff k).1 hjl)
      ((Fin.natAdd_lt_natAdd_iff k).1 hli))

theorem silenceLicensed_natAdd :
    SilenceLicensed p w R (Fin.natAdd k j) ↔
      SilenceLicensed p (w.drop k) (dropRealization k R) j := by
  unfold SilenceLicensed
  rw [properlyGoverned_natAdd, enclosed_natAdd]
  simp only [IsLast, Fin.val_natAdd]
  exact or_congr_right (or_congr_right (and_congr_left' (by omega)))

variable (p w)

/-- The realization of the last `m` nuclei of a domain is the standard realization of their own
profile, whatever precedes them. -/
theorem dropRealization_standard : dropRealization k (standard p w) = standard p (w.drop k) := by
  refine IsStandard.eq (fun j ↦ ?_) (isStandard_standard p (w.drop k))
  rw [mem_dropRealization, mem_standard_iff, silenceLicensed_natAdd]
  simp [Profile.drop]

end Drop

/-! ### Havlík's Law

In a run of nuclei without melody, pronunciation alternates from the right: every other nucleus
is pronounced, counting from the right edge of the run. -/

section Havlik

variable {p w} {a b x : Fin n}

private theorem even_sub_iff {a x : ℕ} (h : x < a) : Even (a - x) ↔ ¬ Even (a - (x + 1)) := by
  rw [show a - x = a - (x + 1) + 1 by omega, Nat.even_add_one]

/-- In a run of nuclei without melody, required by nothing and in no cluster, that ends before a
nucleus with melody, a nucleus of the run is pronounced iff its distance to that nucleus is even:
every other yer survives, counting from the right edge of the sequence ([scheer-2004] (304)). -/
theorem mem_standard_iff_even (ha : a ∈ w.full)
    (hrun : ∀ y, b ≤ y → y < a → y ∉ w.full ∧ y ∉ w.forced ∧ y ∉ w.cluster)
    (hbx : b ≤ x) (hxa : x < a) : x ∈ standard p w ↔ Even (a.val - x.val) := by
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    obtain ⟨hf, hfo, hc⟩ := hrun x hbx hxa
    have hlt := Fin.lt_def.1 hxa
    let y : Fin n := ⟨x.val + 1, by have := a.isLt; omega⟩
    have hxy : x < y := Fin.lt_def.2 (by simp [y])
    have hsl := silenceLicensed_iff_acts (p := p) (R := standard p w) (y := y) rfl hf
      (fun h ↦ hc h.2.1)
    rw [mem_standard_iff]
    simp only [hf, hfo, false_or]
    by_cases hya : y = a
    · rw [hsl (fun h ↦ h.1 (hya ▸ ha)), hya, even_sub_iff hlt, show a.val - (x.val + 1) = 0 by
        rw [← hya]; simp [y]]
      simp only [Even.zero, not_true_eq_false, iff_false, not_not]
      exact .inl ((isStandard_standard p w a).2 (.inl ha))
    · have hya' : y < a := lt_of_le_of_ne (Fin.le_def.2 (by simp [y]; omega)) hya
      obtain ⟨-, -, hyc⟩ := hrun y (hbx.trans hxy.le) hya'
      rw [hsl (fun h ↦ hyc h.2.1), even_sub_iff hlt]
      have hyl : ¬ IsLast y := by unfold IsLast; have := a.isLt; have := Fin.lt_def.1 hya'; omega
      simp only [Acts, hyl, false_and, or_false]
      rw [ih y hxy (hbx.trans hxy.le) hya']

/-- In a run of nuclei without melody, required by nothing and in no cluster, that reaches the end
of a domain whose final nucleus may be empty and does not act, a nucleus of the run is pronounced
iff its distance to the end is even ([scheer-2004] (304)). -/
theorem mem_standard_iff_even_of_final (hp : p.empty = true) (hp' : p.acts = false)
    (hrun : ∀ y, b ≤ y → y ∉ w.full ∧ y ∉ w.forced ∧ y ∉ w.cluster) (hbx : b ≤ x) :
    x ∈ standard p w ↔ Even (n - x.val) := by
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    obtain ⟨hf, hfo, hc⟩ := hrun x hbx
    rw [mem_standard_iff]
    simp only [hf, hfo, false_or]
    by_cases hl : IsLast x
    · unfold IsLast at hl
      rw [show n - x.val = 1 by omega]
      simp only [Nat.not_even_one, iff_false, not_not]
      exact .inr (.inr ⟨hl, hp⟩)
    · have hx1 : x.val + 1 < n := by unfold IsLast at hl; have := x.isLt; omega
      let y : Fin n := ⟨x.val + 1, hx1⟩
      have hxy : x < y := Fin.lt_def.2 (by simp [y])
      obtain ⟨-, -, hyc⟩ := hrun y (hbx.trans hxy.le)
      rw [silenceLicensed_iff_acts (y := y) rfl hf (fun h ↦ hc h.2.1) (fun h ↦ hyc h.2.1),
        even_sub_iff (show x.val < n from x.isLt)]
      simp only [Acts, hp', Bool.false_eq_true, and_false, or_false]
      rw [ih y hxy (hbx.trans hxy.le)]

end Havlik

end StrictCV
