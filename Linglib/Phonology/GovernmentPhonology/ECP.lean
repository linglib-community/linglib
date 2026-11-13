/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.GovernmentPhonology.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Basic

/-!
# The Empty Category Principle

A nucleus may stay unexpressed when it is governed, when it is enclosed in a domain of
infrasegmental government, or when it is final in a language whose final nuclei may be empty.
Since a governed nucleus governs nothing, of two successive unexpressed nuclei
[one is enclosed](##GovernmentPhonology.SatisfiesECP.enclosed_or_enclosed). Where alternation
with zero is obligatory, the realization of a domain is fixed from the right, each nucleus
unexpressed exactly when its silence is licensed, and the principle
[holds of it](##GovernmentPhonology.satisfiesECP_obligatory). In a word of alternating vowels
the outcome depends on whether such a vowel, once expressed, is strong enough to govern another:
where it is, [every other one](##GovernmentPhonology.expressed_obligatory_iff_even) is
expressed, counting from the end, and where it is not,
[all but the last](##GovernmentPhonology.expressed_obligatory_iff_succ_lt) are.

## Implementation notes

The realization takes the set of nuclei that are required to be expressed on grounds the
lateral relations do not give. Alternation is optional in some languages, and the realization
here is the obligatory one.

## References

* [kaye-lowenstamm-vergnaud-1990]
* [scheer-2004]
* [scheer-cyran-2018]
-/

@[expose] public section

namespace GovernmentPhonology

variable (A : Actorship) (l : List Nucleus) {i : ℕ}

/-- The Empty Category Principle ([scheer-2004] (53)): associated melody is expressed, and a
nucleus is unexpressed only if it is governed, enclosed in a domain of infrasegmental
government, or final where final nuclei may be empty. -/
structure SatisfiesECP : Prop where
  /-- Associated melody is expressed. -/
  expressed_of_associated : ∀ x ∈ l, x.melody = .associated → x.expressed = true
  /-- The silence of an unexpressed nucleus is licensed. -/
  licensed : ∀ i, (∃ x ∈ l[i]?, x.expressed = false) →
    Governed A l i ∨ Enclosed A l i ∨ i + 1 = l.length ∧ A.finalEmpty = true

variable {A l}

theorem satisfiesECP_nil : SatisfiesECP A [] :=
  ⟨by simp, by simp⟩

/-- A stretch satisfies the Empty Category Principle when its first nucleus does and the rest
of the stretch does. -/
theorem satisfiesECP_cons {x : Nucleus} {r : List Nucleus} : SatisfiesECP A (x :: r) ↔
    (x.melody = .associated → x.expressed = true) ∧ (x.expressed = false →
      GovernedHead A (x :: r) ∨ EnclosedHead A (x :: r) ∨ r = [] ∧ A.finalEmpty = true) ∧
      SatisfiesECP A r := by
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h1 x List.mem_cons_self, fun hx ↦ ?_,
    fun y hy ↦ h1 y (List.mem_cons_of_mem _ hy), fun i hi ↦ ?_⟩, fun ⟨h1, h2, h3, h4⟩ ↦
    ⟨fun y hy ↦ (List.mem_cons.1 hy).elim (· ▸ h1) (h3 y), fun i hi ↦ ?_⟩⟩
  · simpa [Governed, Enclosed] using h2 0 ⟨x, rfl, hx⟩
  · simpa [Governed, Enclosed] using h2 (i + 1) hi
  · rcases i with _ | i
    · simpa [Governed, Enclosed] using h2 (by simpa using hi)
    · simpa [Governed, Enclosed] using h4 i hi

variable (A) in
instance instDecidablePredSatisfiesECP : DecidablePred (SatisfiesECP A)
  | [] => isTrue satisfiesECP_nil
  | _ :: r =>
    have := instDecidablePredSatisfiesECP r
    decidable_of_iff _ satisfiesECP_cons.symm

/-- Of two successive unexpressed nuclei before the last, one is enclosed. -/
theorem SatisfiesECP.enclosed_or_enclosed (h : SatisfiesECP A l) {x y : Nucleus}
    (hx : l[i]? = some x) (hy : l[i + 1]? = some y) (hxe : x.expressed = false)
    (hye : y.expressed = false) (hl : i + 2 < l.length) :
    Enclosed A l i ∨ Enclosed A l (i + 1) := by
  rcases h.licensed i ⟨x, hx, hxe⟩ with h1 | h1 | h1
  · rcases h.licensed (i + 1) ⟨y, hy, hye⟩ with h2 | h2 | h2
    · exact absurd h2 (governed_iff.1 h1).2.1
    · exact .inr h2
    · omega
  · exact .inl h1
  · omega

/-! ### The obligatory realization -/

variable (A) in
/-- The obligatory realization of a stretch whose first nucleus is nucleus `i` of its domain:
from the right, a nucleus is left unexpressed exactly when its silence is licensed, unless it
has associated melody or is one of `R`, the nuclei required to be expressed. -/
def obligatoryFrom (R : Finset ℕ) : ℕ → List Nucleus → List Nucleus
  | _, [] => []
  | i, x :: r =>
    let r' := obligatoryFrom R (i + 1) r
    let silent : Nucleus := { x with expressed := false }
    if x.melody ≠ .associated ∧ i ∉ R ∧ (GovernedHead A (silent :: r') ∨
        EnclosedHead A (silent :: r') ∨ r = [] ∧ A.finalEmpty = true) then
      silent :: r'
    else { x with expressed := true } :: r'

variable (A) in
/-- The obligatory realization of a domain, in which every nucleus that may be unexpressed is,
except those of `R`. -/
def obligatory (R : Finset ℕ) (l : List Nucleus) : List Nucleus := obligatoryFrom A R 0 l

variable {R : Finset ℕ} {k : ℕ} {x : Nucleus} {r : List Nucleus}

theorem obligatoryFrom_cons : obligatoryFrom A R i (x :: r) =
    if x.melody ≠ .associated ∧ i ∉ R ∧
      (GovernedHead A ({ x with expressed := false } :: obligatoryFrom A R (i + 1) r) ∨
        EnclosedHead A ({ x with expressed := false } :: obligatoryFrom A R (i + 1) r) ∨
        r = [] ∧ A.finalEmpty = true)
    then { x with expressed := false } :: obligatoryFrom A R (i + 1) r
    else { x with expressed := true } :: obligatoryFrom A R (i + 1) r :=
  rfl

@[simp] theorem length_obligatoryFrom : (obligatoryFrom A R i l).length = l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons x r ih => rw [obligatoryFrom_cons]; split_ifs <;> simp [ih]

@[simp] theorem length_obligatory : (obligatory A R l).length = l.length :=
  length_obligatoryFrom

theorem map_obligatoryFrom : (obligatoryFrom A R i l).map ({ · with expressed := false }) =
    l.map ({ · with expressed := false }) := by
  induction l generalizing i with
  | nil => rfl
  | cons x r ih => rw [obligatoryFrom_cons]; split_ifs <;> simp [ih]

/-- The obligatory realization changes only which nuclei are expressed. -/
theorem map_obligatory : (obligatory A R l).map ({ · with expressed := false }) =
    l.map ({ · with expressed := false }) :=
  map_obligatoryFrom

/-- The realization of the last nuclei of a stretch is computed from them alone. -/
theorem drop_obligatoryFrom :
    (obligatoryFrom A R i l).drop k = obligatoryFrom A R (i + k) (l.drop k) := by
  induction l generalizing i k with
  | nil => simp [obligatoryFrom]
  | cons x r ih =>
    rcases k with _ | k
    · rfl
    · rw [obligatoryFrom_cons]
      split_ifs <;> simp [ih, Nat.add_assoc, Nat.add_comm 1 k]

theorem satisfiesECP_obligatoryFrom : SatisfiesECP A (obligatoryFrom A R i l) := by
  induction l generalizing i with
  | nil => exact satisfiesECP_nil
  | cons x r ih =>
    rw [obligatoryFrom_cons]
    split_ifs with hc
    · refine satisfiesECP_cons.2 ⟨fun h ↦ absurd h hc.1, fun _ ↦ hc.2.2.imp_right (.imp_right ?_),
        ih⟩
      exact .imp_left fun h ↦ by rw [h]; rfl
    · exact satisfiesECP_cons.2 ⟨fun _ ↦ rfl, fun h ↦ by simp at h, ih⟩

theorem satisfiesECP_obligatory : SatisfiesECP A (obligatory A R l) :=
  satisfiesECP_obligatoryFrom

private theorem ite_cons_eq_cons_iff {c : Prop} [Decidable c] {o : List Nucleus} :
    (if c then { x with expressed := false } :: o else { x with expressed := true } :: o) =
      x :: r ↔ (x.expressed = true ↔ ¬ c) ∧ o = r := by
  obtain ⟨m, e, cl⟩ := x
  split_ifs with hc <;> cases e <;> simp [hc]

/-- A stretch is its own obligatory realization exactly when each nucleus is expressed just in
case it has associated melody, is required to be expressed, or would not have its silence
licensed. -/
theorem obligatoryFrom_eq_self_iff : obligatoryFrom A R k l = l ↔
    ∀ i x, l[i]? = some x → (x.expressed = true ↔ x.melody = .associated ∨ i + k ∈ R ∨
      ¬ (Governed A (l.set i { x with expressed := false }) i ∨
        Enclosed A (l.set i { x with expressed := false }) i ∨
        i + 1 = l.length ∧ A.finalEmpty = true)) := by
  induction l generalizing k with
  | nil => simp [obligatoryFrom]
  | cons x r ih =>
    rw [obligatoryFrom_cons, ite_cons_eq_cons_iff, ← Nat.and_forall_add_one]
    refine (and_congr_left fun hr ↦ ?_).trans (and_congr_right' (ih.trans ?_))
    · rw [hr]
      simp [Governed, Enclosed, or_iff_not_imp_left]
    · simp [Governed, Enclosed, Nat.add_right_comm _ 1 k, Nat.add_assoc _ k 1]

/-- A domain is its own obligatory realization exactly when each nucleus is expressed just in
case it has associated melody, is required to be expressed, or would not have its silence
licensed. -/
theorem obligatory_eq_self_iff : obligatory A R l = l ↔
    ∀ i x, l[i]? = some x → (x.expressed = true ↔ x.melody = .associated ∨ i ∈ R ∨
      ¬ (Governed A (l.set i { x with expressed := false }) i ∨
        Enclosed A (l.set i { x with expressed := false }) i ∨
        i + 1 = l.length ∧ A.finalEmpty = true)) :=
  obligatoryFrom_eq_self_iff

/-! ### Words of alternating vowels -/

variable (A) in
/-- An unexpressed final alternating vowel is too weak to govern another. -/
def FinalFloatingInert : Prop := ∀ x : Nucleus, x.melody = .floating → x.expressed = false →
  A.strength x true < (Melody.floating : WithBot Melody)

private theorem melody_eq_floating_of_mem_obligatoryFrom (hl : ∀ x ∈ l, x.melody = .floating) :
    ∀ y ∈ obligatoryFrom A R i l, y.melody = .floating := by
  induction l generalizing i with
  | nil => simp [obligatoryFrom]
  | cons x r ih =>
    have := ih (i := i + 1) fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)
    rw [obligatoryFrom_cons]
    split_ifs <;> simpa [hl x List.mem_cons_self] using this

private theorem not_enclosedHead_of_floating (hx : x.melody = .floating) :
    ¬ EnclosedHead A ({ x with expressed := false } :: r) := by
  cases r <;> simp [EnclosedHead, hx]

/-- The realization of a word of alternating vowels with one more vowel before it: the new
vowel is unexpressed when it is the last or the next one governs it. -/
private theorem obligatoryFrom_cons_of_floating (hx : x.melody = .floating)
    (he : A.finalEmpty = true) : obligatoryFrom A ∅ i (x :: r) =
      if r = [] ∨ GovernedHead A ({ x with expressed := false } :: obligatoryFrom A ∅ (i + 1) r)
      then { x with expressed := false } :: obligatoryFrom A ∅ (i + 1) r
      else { x with expressed := true } :: obligatoryFrom A ∅ (i + 1) r := by
  have hm : x.melody ≠ .associated := by simp [hx]
  rw [obligatoryFrom_cons]
  exact if_congr (by simp [hm, he, not_enclosedHead_of_floating hx, or_comm]) rfl rfl

private theorem head_obligatoryFrom_of_le (hf : FinalFloatingInert A)
    (hs : ∀ x : Nucleus, x.melody = .floating → x.expressed = true →
      (Melody.floating : WithBot Melody) ≤ A.strength x false)
    (he : A.finalEmpty = true) (hl : ∀ x ∈ l, x.melody = .floating) :
    (∀ y ∈ (obligatoryFrom A ∅ k l).head?, (y.expressed = true ↔ Even l.length)) ∧
      (GovernedHead A (obligatoryFrom A ∅ k l) ↔ ¬ Even l.length ∧ l.length ≠ 1) := by
  induction l generalizing k with
  | nil => simp [obligatoryFrom, GovernedHead]
  | cons x r ih =>
    have hr : ∀ y ∈ r, y.melody = .floating := fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)
    have hx : x.melody = .floating := hl x List.mem_cons_self
    obtain ⟨ib, ic⟩ := ih (k := k + 1) hr
    have ia := melody_eq_floating_of_mem_obligatoryFrom (A := A) (R := ∅) (i := k + 1) hr
    have hlen := length_obligatoryFrom (A := A) (R := ∅) (i := k + 1) (l := r)
    have hG : GovernedHead A ({ x with expressed := false } :: obligatoryFrom A ∅ (k + 1) r) ↔
        Even r.length ∧ r.length ≠ 0 := by
      rw [governedHead_cons]
      simp only [not_enclosedHead_of_floating hx, not_false_eq_true, true_and]
      generalize obligatoryFrom A ∅ (k + 1) r = o at ia ib ic hlen
      rcases o with _ | ⟨y, o⟩
      · simp [← hlen]
      · have hy := ia y List.mem_cons_self
        have hye := ib y rfl
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq, exists_eq_left',
          List.tail_cons, hx, ic]
        rcases o with _ | ⟨z, o⟩
        · have h1 : r.length = 1 := hlen.symm
          have := hf y hy (by simpa [h1] using hye)
          simp [h1, not_le.2 this]
        · have h2 : r.length = o.length + 2 := hlen.symm
          by_cases hev : Even r.length
          · exact ⟨fun _ ↦ ⟨hev, by omega⟩, fun _ ↦ ⟨fun h ↦ h.1 hev, hs y hy (hye.2 hev)⟩⟩
          · exact ⟨fun h ↦ absurd ⟨hev, by omega⟩ h.1, fun h ↦ absurd h.1 hev⟩
    have hc : r = [] ∨ GovernedHead A ({ x with expressed := false } ::
        obligatoryFrom A ∅ (k + 1) r) ↔ Even r.length := by
      rw [hG]
      rcases r with _ | ⟨z, r⟩ <;> simp
    rw [obligatoryFrom_cons_of_floating hx he]
    by_cases hev : Even r.length
    · rw [ite_eq_left (hc.2 hev), hG]
      simp [Nat.even_add_one, hev]
    · rw [ite_eq_right (mt hc.1 hev), governedHead_cons]
      simp [Nat.even_add_one, hev]

private theorem head_obligatoryFrom_of_lt (hf : FinalFloatingInert A)
    (hs : ∀ x : Nucleus, x.melody = .floating → x.expressed = true →
      A.strength x false < (Melody.floating : WithBot Melody))
    (he : A.finalEmpty = true) (hl : ∀ x ∈ l, x.melody = .floating) :
    (∀ y ∈ (obligatoryFrom A ∅ k l).head?, (y.expressed = true ↔ 2 ≤ l.length)) ∧
      ¬ GovernedHead A (obligatoryFrom A ∅ k l) := by
  induction l generalizing k with
  | nil => simp [obligatoryFrom, GovernedHead]
  | cons x r ih =>
    have hr : ∀ y ∈ r, y.melody = .floating := fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)
    have hx : x.melody = .floating := hl x List.mem_cons_self
    obtain ⟨ib, -⟩ := ih (k := k + 1) hr
    have ia := melody_eq_floating_of_mem_obligatoryFrom (A := A) (R := ∅) (i := k + 1) hr
    have hlen := length_obligatoryFrom (A := A) (R := ∅) (i := k + 1) (l := r)
    have hG : ¬ GovernedHead A ({ x with expressed := false } ::
        obligatoryFrom A ∅ (k + 1) r) := by
      rw [governedHead_cons]
      generalize obligatoryFrom A ∅ (k + 1) r = o at ia ib hlen
      rcases o with _ | ⟨y, o⟩
      · simp
      · have hy := ia y List.mem_cons_self
        have hye := ib y rfl
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq, exists_eq_left',
          List.tail_cons, hx]
        rintro ⟨-, -, -, hle⟩
        rcases o with _ | ⟨z, o⟩
        · have h1 : r.length = 1 := hlen.symm
          exact absurd hle (not_le.2 (hf y hy (by simpa [h1] using hye)))
        · have h2 : r.length = o.length + 2 := hlen.symm
          exact absurd hle (not_le.2 (hs y hy (hye.2 (by omega))))
    rw [obligatoryFrom_cons_of_floating hx he]
    by_cases hnil : r = []
    · rw [ite_eq_left (.inl hnil)]
      exact ⟨by simp [hnil], hG⟩
    · rw [ite_eq_right (not_or.2 ⟨hnil, hG⟩), governedHead_cons]
      have := List.length_pos_iff.2 hnil
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq',
        List.length_cons, true_iff, Bool.true_eq_false, false_and, not_false_eq_true, and_true]
      omega

private theorem expressed_getElem?_obligatory_iff {p : Prop}
    (h : ∀ y ∈ (obligatoryFrom A R (0 + i) (l.drop i)).head?, (y.expressed = true ↔ p)) :
    (∃ x ∈ (obligatory A R l)[i]?, x.expressed = true) ↔ i < l.length ∧ p := by
  rw [← drop_obligatoryFrom, List.head?_drop] at h
  rcases Nat.lt_or_ge i l.length with hi | hi
  · have hi' : i < (obligatory A R l).length := length_obligatory.trans_gt hi
    rw [obligatory, List.getElem?_eq_getElem hi'] at *
    simpa [hi] using h
  · simp [hi.not_gt]

/-- Havlík's Law ([scheer-2004] (304)): where an expressed alternating vowel governs another, a
word of alternating vowels expresses those at an even distance from its end, the last standing
at distance one. -/
theorem expressed_obligatory_iff_even (hl : ∀ x ∈ l, x.melody = .floating)
    (he : A.finalEmpty = true) (hf : FinalFloatingInert A)
    (hs : ∀ x : Nucleus, x.melody = .floating → x.expressed = true →
      (Melody.floating : WithBot Melody) ≤ A.strength x false) :
    (∃ x ∈ (obligatory A ∅ l)[i]?, x.expressed = true) ↔ i < l.length ∧ Even (l.length - i) :=
  expressed_getElem?_obligatory_iff <| List.length_drop ▸
    (head_obligatoryFrom_of_le hf hs he fun x hx ↦ hl x (List.mem_of_mem_drop hx)).1

/-- Lower: where an expressed alternating vowel does not govern another, a word of alternating
vowels expresses all but the last. -/
theorem expressed_obligatory_iff_succ_lt (hl : ∀ x ∈ l, x.melody = .floating)
    (he : A.finalEmpty = true) (hf : FinalFloatingInert A)
    (hs : ∀ x : Nucleus, x.melody = .floating → x.expressed = true →
      A.strength x false < (Melody.floating : WithBot Melody)) :
    (∃ x ∈ (obligatory A ∅ l)[i]?, x.expressed = true) ↔ i + 1 < l.length := by
  rw [expressed_getElem?_obligatory_iff
    (head_obligatoryFrom_of_lt hf hs he fun x hx ↦ hl x (List.mem_of_mem_drop hx)).1,
    List.length_drop]
  omega

end GovernmentPhonology
