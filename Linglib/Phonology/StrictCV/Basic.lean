/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

/-!
# Strict CV: proper government and the Empty Category Principle

In Strict CV the skeleton is a strict sequence of CV units, so the nuclei of a domain form a
sequence. A nucleus has associated melody, floating melody, or none, and only associated melody
must be pronounced. Any other nucleus may stay silent only when its silence is licensed: by
proper government from the nuclei after it, by enclosure in a domain of infrasegmental
government, or at the end of the domain where the language allows an empty final nucleus. This
is the Empty Category Principle. Government is discharged from right to left by lateral actors:
pronounced nuclei and, where the language allows it, an empty final nucleus. A realized stretch
pairs each nucleus with whether it is pronounced, and the lateral relations of a nucleus are
read off the stretch after it. The standard realization, computed from the right, pronounces a
nucleus exactly when it has associated melody, is required, or nothing licenses its silence.

## Main definitions

* `StrictCV.Melody`, `StrictCV.Nucleus`: the melody of a nucleus, whether it is required, and
  whether its flanking consonants may contract infrasegmental government.
* `StrictCV.FinalNucleus`: whether a final nucleus may be empty, and whether it then acts.
* `StrictCV.Acts`, `StrictCV.Enclosed`, `StrictCV.Governs`, `StrictCV.ProperlyGoverned`,
  `StrictCV.SilenceLicensed`: lateral actors and the ways a silence is licensed.
* `StrictCV.SatisfiesECP`, `StrictCV.standard`.

## Main results

* `StrictCV.satisfiesECP_standard`: the standard realization satisfies the Empty Category
  Principle.
* `StrictCV.standard_drop`: the realization of the last nuclei of a domain is computed from them
  alone.
* `StrictCV.standard_append_of_floating`: in a run of floating melodies every other one is
  pronounced, counting from the right, which is Havlík's Law.

## Implementation notes

The lateral actors are the pronounced nuclei, an epenthetic one included, as in Scheer's
"only phonetically expressed Nuclei can govern and license"; Cavirani's alternative grants
actorship to unpronounced nuclei with melody and is not built. An empty final nucleus either
acts, governing and licensing, or does not, a single parameter, as Scheer and Ziková conclude.
Government passes over a nucleus enclosed in a domain of infrasegmental government and binds the
first nucleus whose silence is not licensed otherwise. Only a nucleus without melody is enclosed:
a vowel that alternates with zero, a "hidden" zero, breaks up the cluster around it. Whether two
consonants may contract infrasegmental government is a fact about their melody, supplied with
the nucleus between them; that the governing consonant must be licensed by its own nucleus is
built in. The distribution of government and licensing over onsets, which the two versions of
the Coda Mirror state differently, is not modelled: proper government of nuclei is the same in
both. A nucleus can be required on independent grounds, as a guttural needs a pronounced
licensor or an initial empty CV unit needs a pronounced first nucleus to govern it.

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

/-- The melody of a nucleus ([scheer-2004] (73)). A full vowel has associated melody, a vowel
that alternates with zero has floating melody, and the nucleus inside a branching onset or a
coda-onset cluster has none. -/
inductive Melody
  /-- No melody. -/
  | empty
  /-- Floating melody, which associates unless the nucleus is governed. -/
  | floating
  /-- Associated melody. -/
  | associated
  deriving DecidableEq, Repr

/-- A nucleus as the lateral computation reads it. -/
structure Nucleus where
  /-- The melody of the nucleus. -/
  melody : Melody
  /-- The nucleus must be pronounced on independent grounds. -/
  forced : Bool := false
  /-- The consonants flanking the nucleus may contract infrasegmental government, the following
  one governing the preceding one ([scheer-2004] (49a)). -/
  cluster : Bool := false
  deriving DecidableEq, Repr

/-- How a language treats the final nucleus of a domain ([scheer-zikova-2010] §5). -/
structure FinalNucleus where
  /-- A final nucleus may stay empty. -/
  empty : Bool
  /-- An empty final nucleus is a lateral actor, governing and licensing. -/
  acts : Bool
  deriving DecidableEq, Repr, Fintype

variable (p : FinalNucleus)

/-- The first nucleus of a realized stretch is a lateral actor when it is pronounced, or when it
is an empty final nucleus where final nuclei act. -/
def Acts : List (Nucleus × Bool) → Prop
  | [] => False
  | (_, b) :: r => b = true ∨ (r = [] ∧ p.acts = true)

instance : DecidablePred (Acts p)
  | [] => isFalse fun h ↦ h
  | (_, _) :: _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A nucleus before a realized stretch is enclosed in a domain of infrasegmental government
when it has no melody, its flanking consonants may contract government, and the governing
consonant is licensed by its own nucleus, which only a pronounced nucleus can do
([scheer-2004] (49), (50)). -/
def Enclosed (x : Nucleus) : List (Nucleus × Bool) → Prop
  | [] => False
  | (_, b) :: _ => x.melody = .empty ∧ x.cluster = true ∧ b = true

instance (x : Nucleus) : DecidablePred (Enclosed x)
  | [] => isFalse fun h ↦ h
  | (_, _) :: _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A realized stretch governs the nucleus before it when government reaches a lateral actor,
passing over enclosed nuclei only ([scheer-2004] §75). -/
def Governs : List (Nucleus × Bool) → Prop
  | [] => False
  | (y, b) :: r => Acts p ((y, b) :: r) ∨ (Enclosed y r ∧ Governs r)

instance instDecidablePredGoverns : DecidablePred (Governs p)
  | [] => isFalse fun h ↦ h
  | (_, _) :: r =>
    have := instDecidablePredGoverns r
    inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- A nucleus before a realized stretch is properly governed when it has no associated melody,
is not enclosed, and the stretch governs it. -/
def ProperlyGoverned (x : Nucleus) (r : List (Nucleus × Bool)) : Prop :=
  x.melody ≠ .associated ∧ ¬ Enclosed x r ∧ Governs p r

instance (x : Nucleus) : DecidablePred (ProperlyGoverned p x) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The silence of a nucleus before a realized stretch is licensed when it is properly governed,
enclosed, or final where final nuclei may be empty ([scheer-2004] (53)). -/
def SilenceLicensed (x : Nucleus) (r : List (Nucleus × Bool)) : Prop :=
  ProperlyGoverned p x r ∨ Enclosed x r ∨ (r = [] ∧ p.empty = true)

instance (x : Nucleus) : DecidablePred (SilenceLicensed p x) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- A realized stretch satisfies the Empty Category Principle when associated melody is
pronounced and the silence of every silent nucleus is licensed by the nuclei after it. -/
def SatisfiesECP : List (Nucleus × Bool) → Prop
  | [] => True
  | (x, b) :: r =>
    (x.melody = .associated → b = true) ∧ (b = true ∨ SilenceLicensed p x r) ∧ SatisfiesECP r

instance instDecidablePredSatisfiesECP : DecidablePred (SatisfiesECP p)
  | [] => isTrue trivial
  | (_, _) :: r =>
    have := instDecidablePredSatisfiesECP r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The standard realization, computed from the right: a nucleus is pronounced when it has
associated melody, is required, or the nuclei after it do not license its silence. -/
def standard (l : List Nucleus) : List (Nucleus × Bool) :=
  l.foldr (fun x r ↦
    (x, decide (x.melody = .associated ∨ x.forced = true ∨ ¬ SilenceLicensed p x r)) :: r) []

variable {p} {x y : Nucleus} {b : Bool} {r : List (Nucleus × Bool)}

/-! ### The standard realization -/

section Standard

@[simp] theorem standard_nil : standard p [] = [] := rfl

theorem standard_cons (x : Nucleus) (l : List Nucleus) :
    standard p (x :: l) = (x, decide (x.melody = .associated ∨ x.forced = true ∨
      ¬ SilenceLicensed p x (standard p l))) :: standard p l := rfl

@[simp] theorem map_fst_standard (l : List Nucleus) : (standard p l).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [standard_cons, List.map_cons, ih]

@[simp] theorem length_standard (l : List Nucleus) : (standard p l).length = l.length := by
  rw [← List.length_map (f := Prod.fst), map_fst_standard]

/-- The realization of the last nuclei of a domain is computed from them alone, since lateral
relations are discharged from right to left. -/
theorem standard_drop (k : ℕ) (l : List Nucleus) :
    standard p (l.drop k) = (standard p l).drop k := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    cases k with
    | zero => rfl
    | succ k => rw [List.drop_succ_cons, ih, standard_cons, List.drop_succ_cons]

variable (p) in
/-- The standard realization satisfies the Empty Category Principle. -/
theorem satisfiesECP_standard (l : List Nucleus) : SatisfiesECP p (standard p l) := by
  induction l with
  | nil => trivial
  | cons x l ih =>
    rw [standard_cons]
    refine ⟨fun h ↦ decide_eq_true (.inl h), ?_, ih⟩
    by_cases h : SilenceLicensed p x (standard p l)
    · exact .inr h
    · exact .inl (decide_eq_true (.inr (.inr h)))

end Standard

/-! ### Government from the following nucleus -/

section Successor

theorem Enclosed.melody_eq_empty : Enclosed x r → x.melody = .empty := by
  cases r with
  | nil => exact False.elim
  | cons y r => exact fun h ↦ h.1

theorem Enclosed.cluster_eq_true : Enclosed x r → x.cluster = true := by
  cases r with
  | nil => exact False.elim
  | cons y r => exact fun h ↦ h.2.1

/-- A stretch whose first nucleus is not enclosed governs the nucleus before it exactly when that
first nucleus acts: government comes from the following nucleus ([scheer-2004] §23). -/
theorem governs_cons_iff (h : ¬ Enclosed y r) :
    Governs p ((y, b) :: r) ↔ Acts p ((y, b) :: r) := by
  simp only [Governs, h, false_and, or_false]

/-- The silence of a floating melody is licensed exactly when the nuclei after it govern it or it
ends a domain whose final nucleus may be empty. -/
theorem silenceLicensed_of_floating (hx : x.melody = .floating) :
    SilenceLicensed p x r ↔ Governs p r ∨ (r = [] ∧ p.empty = true) := by
  have he : ¬ Enclosed x r := fun h ↦ by rw [h.melody_eq_empty] at hx; cases hx
  simp only [SilenceLicensed, ProperlyGoverned, hx, he, ne_eq, reduceCtorEq, not_false_eq_true,
    true_and, false_or]

end Successor

/-! ### Havlík's Law

In a run of floating melodies, pronunciation alternates from the right: every other one is
pronounced, counting from the right edge of the run. -/

section Havlik

variable {xs ys : List Nucleus}

/-- In a run of floating melodies, required by nothing, before nuclei that govern it or at the end
of a domain whose final nucleus may be empty and does not act, a nucleus of the run is pronounced
iff its distance to the end of the run is even: every other yer survives, counting from the
right edge of the sequence ([scheer-2004] (304)). -/
theorem standard_append_of_floating (hxs : ∀ x ∈ xs, x.melody = .floating ∧ x.forced = false)
    (hys : Governs p (standard p ys) ∨ ys = [] ∧ p.empty = true ∧ p.acts = false) :
    standard p (xs ++ ys) =
      xs.mapIdx (fun i x ↦ (x, decide (Even (xs.length - i)))) ++ standard p ys := by
  have hfin : ys = [] → p.empty = true ∧ p.acts = false := fun h ↦ by
    subst h
    exact hys.resolve_left id |>.2
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, hfx⟩ := hxs x List.mem_cons_self
    rw [List.cons_append, standard_cons, ih fun y hy ↦ hxs y (List.mem_cons_of_mem _ hy),
      List.mapIdx_cons, List.cons_append, List.length_cons]
    refine congrArg₂ List.cons (Prod.ext rfl ?_) (by simp only [Nat.add_sub_add_right])
    dsimp only
    rw [decide_eq_decide, silenceLicensed_of_floating hx, hx, hfx, Nat.sub_zero, Nat.even_add_one]
    simp only [reduceCtorEq, Bool.false_eq_true, false_or]
    refine not_congr ?_
    rcases xs with _ | ⟨y, xs⟩
    · simp only [List.mapIdx_nil, List.nil_append, List.length_nil, Even.zero, iff_true]
      rcases hys with h | ⟨rfl, h, -⟩
      exacts [.inl h, .inr ⟨rfl, h⟩]
    · obtain ⟨hy, -⟩ := hxs y (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [List.mapIdx_cons, List.cons_append,
        governs_cons_iff fun h ↦ by rw [h.melody_eq_empty] at hy; cases hy]
      simp only [Acts, Nat.sub_zero, decide_eq_true_eq, reduceCtorEq, false_and, or_false]
      refine or_iff_left fun ⟨h, ha⟩ ↦ ?_
      have hys' : ys = [] := by simpa using congrArg List.length (List.append_eq_nil_iff.1 h).2
      simp [(hfin hys').2] at ha

end Havlik

end StrictCV
