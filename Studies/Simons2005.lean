module

public import Linglib.Semantics.Modality.MinimalCovering
public import Studies.KratzerShimoyama2002

/-!
# Simons (2005): Dividing things up: the semantics of *or* and the modal/*or* interaction

[simons-2005] takes an *or* coordination to denote the set of its disjuncts' denotations and to
divide up a set of worlds by them: the set is super covered, each disjunct meeting it and the
disjuncts together covering it. On its non-disjunctive reading *Jane must sing or dance* is true
when the singing and the dancing worlds super cover the accessible worlds, and *Jane may sing or
dance* when they super cover some of them, which holds exactly when
[each disjunct is possible](##Simons2005.mem_may_iff). The modals are thus Kratzer and Shimoyama's
with their distribution requirement
[built into the truth conditions](##Simons2005.mem_may_iff_kann_and_distribution). Unembedded,
*φ or ψ* is true at a world of a set the disjuncts super cover, which is
[classical disjunction of consistent disjuncts](##Simons2005.mem_orCoordination_iff), and the
pragmatic Genuineness constraint, that the set lie among the speaker's epistemic possibilities,
[reduces the disjunctive reading of *might φ or might ψ*](##Simons2005.mem_may_of_genuine) to its
free-choice reading, which is why epistemic *or* sentences seem to lack the disjunctive reading
([zimmermann-2000]).

Disjuncts are expected to be alternatives to one another, which three enhanced super covers make
precise: Non-Containment, No Total Overlap, and Alternativeness, under which each disjunct
contains a world of the set that no other disjunct contains. A disjunct that entails another
within the worlds the set is drawn from
[violates Alternativeness on every such set](##Simons2005.not_alternativeness_of_inter_subset),
whether the entailment is logical, comes from the speaker's beliefs under Genuineness, or comes
from the modal's domain (§6.2).

## Implementation notes

* Propositions are sets of worlds and the accessible worlds are `R w`. The propositions of
  [kratzer-shimoyama-2002] are predicates on worlds and their accessibility a relation, reached
  through `SetRel.ofSuccessors R`. The appendix adapts the truth conditions to Kratzer's semantics
  by replacing the accessible worlds with the g-closest worlds, which is a choice of `R`.
* The No Total Overlap constraint (107) is mathlib's `IsAntichain (· ⊆ ·)` on the disjuncts.
* The unification of fn. 10 applied to a single proposition makes `MUST[φ]` require the accessible
  worlds to be nonempty ([`mem_must_singleton_iff`](##Simons2005.mem_must_singleton_iff)), which
  (14) does not.

## Errata

* p. 308: Alternativeness entails Non-Containment only when the disjuncts denote at least two
  propositions. A single proposition, the argument fn. 10 allows a modal, or the denotation of an
  *or* coordination of synonymous disjuncts, satisfies Alternativeness on a set inside it while
  violating Non-Containment there (`alternativeness_singleton`).

## TODO

* The syntax of §§3–4, ATB movement of the modal and the Rule of Independent Composition (51),
  and the disjunctive readings of narrow *or* sentences (§5.2).
* The truth conditions without the Limit Assumption (§8.3).
* The judgments (98)–(104) as `Data/Examples` rows paired with models of their entailments.

## References

* [simons-2005]
* [kratzer-shimoyama-2002]
* [zimmermann-2000]
-/

@[expose] public section

namespace Simons2005

open MinimalCovering ModalLogic

variable {W : Type*}

/-! ### Non-disjunctive readings (§2) -/

/-- `MAY[φ or ψ]`, (12): the disjuncts super cover some set of accessible worlds. -/
def may (R : W → Set W) (C : Set (Set W)) : Set W := {w | ∃ S ⊆ R w, IsSuperCover C S}

/-- `MUST[φ or ψ]`, (16): the disjuncts super cover the accessible worlds. -/
def must (R : W → Set W) (C : Set (Set W)) : Set W := {w | IsSuperCover C (R w)}

variable {R : W → Set W} {C : Set (Set W)} {w : W}

-- (13)
theorem mem_may_iff : w ∈ may R C ↔ C.Nonempty ∧ ∀ c ∈ C, (c ∩ R w).Nonempty :=
  exists_isSuperCover_iff

-- (9), (10)
theorem may_singleton (p : Set W) : may R {p} = {w | (p ∩ R w).Nonempty} := by
  ext w
  simp [mem_may_iff]

theorem mem_must_singleton_iff {p : Set W} : w ∈ must R {p} ↔ (R w).Nonempty ∧ R w ⊆ p := by
  simp only [must, IsSuperCover, Set.mem_ofPred_eq, Set.singleton_nonempty, Set.mem_singleton_iff,
    forall_eq, Set.sUnion_singleton, true_and]
  exact ⟨fun ⟨h, hp⟩ ↦ ⟨h.mono Set.inter_subset_right, hp⟩,
    fun ⟨h, hp⟩ ↦ ⟨(Set.inter_eq_right.2 hp).symm ▸ h, hp⟩⟩

-- p. 272
theorem must_subset_may : must R C ⊆ may R C :=
  fun _ h ↦ ⟨_, subset_rfl, h⟩

/-- `MAY` is the possibility of [kratzer-shimoyama-2002] together with their distribution
requirement, that each alternative be possible (p. 278). -/
theorem mem_may_iff_kann_and_distribution :
    w ∈ may R C ↔ C.Nonempty ∧ (∀ q ∈ KratzerShimoyama2002.kann (.ofSuccessors R) C, q w) ∧
      KratzerShimoyama2002.distribution (.ofSuccessors R) C w := by
  simp only [mem_may_iff, KratzerShimoyama2002.kann, KratzerShimoyama2002.distribution,
    Set.mem_singleton_iff, forall_eq, Diamond, SetRel.mem_ofSuccessors]
  refine ⟨fun ⟨⟨c, hc⟩, h⟩ ↦ ⟨⟨c, hc⟩, ?_, fun c hc ↦ ?_⟩,
    fun ⟨hC, _, h⟩ ↦ ⟨hC, fun c hc ↦ ?_⟩⟩
  · obtain ⟨v, hvc, hvR⟩ := h c hc
    exact ⟨v, hvR, c, hc, hvc⟩
  · obtain ⟨v, hvc, hvR⟩ := h c hc
    exact ⟨v, hvR, hvc⟩
  · obtain ⟨v, hvR, hvc⟩ := h c hc
    exact ⟨v, hvc, hvR⟩

-- p. 278
theorem mem_must_iff_muss_and_distribution :
    w ∈ must R C ↔ C.Nonempty ∧ (∀ q ∈ KratzerShimoyama2002.muss (.ofSuccessors R) C, q w) ∧
      KratzerShimoyama2002.distribution (.ofSuccessors R) C w := by
  simp only [must, IsSuperCover, Set.mem_ofPred_eq, KratzerShimoyama2002.muss,
    KratzerShimoyama2002.distribution, Set.mem_singleton_iff, forall_eq, Box, Diamond,
    SetRel.mem_ofSuccessors]
  refine and_congr_right fun _ ↦ and_comm.trans (and_congr (forall_congr' fun v ↦ ?_)
    (forall₂_congr fun c _ ↦ ?_))
  · exact ⟨fun h hv ↦ h hv, fun h hv ↦ h hv⟩
  · exact ⟨fun ⟨v, hvc, hvR⟩ ↦ ⟨v, hvR, hvc⟩, fun ⟨v, hvR, hvc⟩ ↦ ⟨v, hvc, hvR⟩⟩

/-! ### Jane's permissions and obligations (§2)

The worlds record whether Jane sings and whether she dances. -/

namespace Jane

/-- Jane sings. -/
def sing : Set (Bool × Bool) := {w | w.1 = true}

/-- Jane dances. -/
def dance : Set (Bool × Bool) := {w | w.2 = true}

/-- Every course of action is permitted. -/
def anything : Bool × Bool → Set (Bool × Bool) := fun _ ↦ Set.univ

/-- Jane must either sing without dancing or dance without singing. -/
def exactlyOne : Bool × Bool → Set (Bool × Bool) := fun _ ↦ {(true, false), (false, true)}

-- p. 277
theorem may_not_must :
    (false, false) ∈ may anything {sing, dance} ∧ (false, false) ∉ must anything {sing, dance} := by
  refine ⟨mem_may_iff.2 ⟨⟨sing, .inl rfl⟩, ?_⟩, fun h ↦ ?_⟩
  · rintro c (rfl | rfl)
    · exact ⟨(true, false), rfl, trivial⟩
    · exact ⟨(false, true), rfl, trivial⟩
  · obtain ⟨c, hc, hv⟩ := h.subset_sUnion (Set.mem_univ (false, false))
    rcases hc with rfl | rfl <;> exact Bool.noConfusion hv

-- p. 272
theorem must_not_obligatory :
    (true, true) ∈ must exactlyOne {sing, dance} ∧
      ¬ exactlyOne (true, true) ⊆ sing ∧ ¬ exactlyOne (true, true) ⊆ dance := by
  refine ⟨⟨⟨sing, .inl rfl⟩, ?_, ?_⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro c (rfl | rfl)
    · exact ⟨(true, false), rfl, .inl rfl⟩
    · exact ⟨(false, true), rfl, .inr rfl⟩
  · rintro v (rfl | rfl)
    · exact ⟨sing, .inl rfl, rfl⟩
    · exact ⟨dance, .inr rfl, rfl⟩
  · exact Bool.noConfusion (h (.inr rfl) : (false, true) ∈ sing)
  · exact Bool.noConfusion (h (.inl rfl) : (true, false) ∈ dance)

end Jane

/-! ### Disjunctive readings (§5) -/

/-- An unembedded *or* coordination, (62): it is true at `w` when `w` lies in a set its disjuncts
super cover. -/
def orCoordination (C : Set (Set W)) : Set W := {w | ∃ S, w ∈ S ∧ IsSuperCover C S}

/-- An unembedded *or* coordination is classical disjunction of consistent disjuncts: true where
some disjunct is, provided that none is contradictory. -/
theorem mem_orCoordination_iff : w ∈ orCoordination C ↔ w ∈ ⋃₀ C ∧ ∀ c ∈ C, c.Nonempty := by
  refine ⟨fun ⟨S, hwS, h⟩ ↦ ⟨h.subset_sUnion hwS, fun c hc ↦ (h.2.1 c hc).mono
    Set.inter_subset_left⟩, fun ⟨hw, h⟩ ↦ ⟨⋃₀ C, hw, ?_, fun c hc ↦ ?_, subset_rfl⟩⟩
  · obtain ⟨c, hc, -⟩ := hw
    exact ⟨c, hc⟩
  · obtain ⟨v, hv⟩ := h c hc
    exact ⟨v, hv, c, hc, hv⟩

-- fn. 33
theorem orCoordination_eq_empty (h : ∅ ∈ C) : orCoordination C = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hw ↦
    (mem_orCoordination_iff.1 hw).2 ∅ h |>.ne_empty rfl

/-- If what is possibly possible is possible, the disjunctive reading of *might φ or might ψ* under
the Genuineness constraint, (96), is its non-disjunctive reading: `φ` and `ψ` are both possible,
(97). -/
theorem mem_may_of_genuine {φ ψ : Set W} (htrans : ∀ v ∈ R w, R v ⊆ R w)
    (h : ∃ S, w ∈ S ∧ IsSuperCover {may R {φ}, may R {ψ}} S ∧ S ⊆ R w) :
    w ∈ may R {φ, ψ} := by
  obtain ⟨S, -, ⟨-, hS, -⟩, hSR⟩ := h
  refine mem_may_iff.2 ⟨⟨φ, .inl rfl⟩, ?_⟩
  rintro c (rfl | rfl)
  · obtain ⟨v, hv, hvS⟩ := hS _ (.inl rfl)
    rw [may_singleton] at hv
    exact hv.mono (Set.inter_subset_inter_right _ (htrans v (hSR hvS)))
  · obtain ⟨v, hv, hvS⟩ := hS _ (.inr rfl)
    rw [may_singleton] at hv
    exact hv.mono (Set.inter_subset_inter_right _ (htrans v (hSR hvS)))

-- p. 302
theorem not_may_of_genuine_other :
    ∃ (R Rₐ : Fin 4 → Set (Fin 4)) (φ ψ : Set (Fin 4)),
      (∃ S, 0 ∈ S ∧ IsSuperCover {may Rₐ {φ}, may Rₐ {ψ}} S ∧ S ⊆ R 0) ∧
        0 ∉ may Rₐ {φ, ψ} := by
  refine ⟨fun _ ↦ {0, 1}, fun v ↦ if v = 0 then {2} else {3}, {2}, {3},
    ⟨{0, 1}, .inl rfl, ⟨⟨_, .inl rfl⟩, ?_, ?_⟩, subset_rfl⟩, fun h ↦ ?_⟩
  · rintro c (rfl | rfl)
    · exact ⟨0, by simp [may_singleton], .inl rfl⟩
    · exact ⟨1, by simp [may_singleton], .inr rfl⟩
  · rintro v (rfl | rfl)
    · exact ⟨_, .inl rfl, by simp [may_singleton]⟩
    · exact ⟨_, .inr rfl, by simp [may_singleton]⟩
  · obtain ⟨v, hv3, hv⟩ := (mem_may_iff.1 h).2 {3} (.inr rfl)
    simp_all

/-! ### Alternativeness (§6) -/

/-- The Non-Containment constraint of (106): the set lies within no disjunct. -/
def NonContainment (C : Set (Set W)) (S : Set W) : Prop := ∀ X ∈ C, ¬ S ⊆ X

/-- The Alternativeness constraint of (109): each disjunct contains a world of the set that no
other disjunct contains. -/
def Alternativeness (C : Set (Set W)) (S : Set W) : Prop :=
  ∀ X ∈ C, ∃ x ∈ X ∩ S, ∀ Y ∈ C, Y ≠ X → x ∉ Y

variable {S E A B : Set W}

-- p. 308
theorem Alternativeness.isAntichain (h : Alternativeness C S) : IsAntichain (· ⊆ ·) C :=
  fun X hX Y hY hXY hsub ↦
    let ⟨_, ⟨hxX, _⟩, hx⟩ := h X hX
    hx Y hY (Ne.symm hXY) (hsub hxX)

-- p. 308
theorem Alternativeness.nonContainment (h : Alternativeness C S) (hC : C.Nontrivial) :
    NonContainment C S := fun X hX hSX ↦
  let ⟨Y, hY, hYX⟩ := hC.exists_ne X
  let ⟨_, ⟨_, hyS⟩, hy⟩ := h Y hY
  hy X hX (Ne.symm hYX) (hSX hyS)

-- p. 308
theorem alternativeness_singleton (hS : S.Nonempty) (hSA : S ⊆ A) :
    Alternativeness {A} S ∧ ¬ NonContainment {A} S := by
  obtain ⟨v, hv⟩ := hS
  exact ⟨fun X hX ↦ ⟨v, ⟨hX ▸ hSA hv, hv⟩, fun Y hY hYX ↦ absurd (hY.trans hX.symm) hYX⟩,
    fun h ↦ h A rfl hSA⟩

/-- A disjunct that entails another within `E` leaves no set within `E` that the two super cover
satisfying Non-Containment: the logical entailments (98)–(100) with `E` everything, Figure 1 and
(105), the epistemic entailments (102)–(104) with `E` the speaker's epistemic possibilities under
Genuineness, (108), and the modal-internal violations of §6.2 with `E` the accessible worlds. -/
theorem not_nonContainment_of_inter_subset (hAB : A ∩ E ⊆ B) (hSE : S ⊆ E)
    (h : IsSuperCover {A, B} S) : ¬ NonContainment {A, B} S := fun hNC ↦
  hNC B (.inr rfl) fun _ hv ↦ ((isSuperCover_pair_iff.1 h).2.2 hv).elim
    (fun hvA ↦ hAB ⟨hvA, hSE hv⟩) id

/-- A disjunct that entails another within `E` has no world of a set within `E` to itself, so no
such set satisfies Alternativeness: the epistemic entailment with a third disjunct, (103), which
meets the other constraints. -/
theorem not_alternativeness_of_inter_subset (hA : A ∈ C) (hB : B ∈ C) (hAB : A ≠ B)
    (hE : A ∩ E ⊆ B) (hSE : S ⊆ E) : ¬ Alternativeness C S := fun h ↦
  let ⟨_, ⟨hxA, hxS⟩, hx⟩ := h A hA
  hx B hB hAB.symm (hE ⟨hxA, hSE hxS⟩)

-- (98)–(100), (107)
theorem not_isAntichain_of_subset (hAB : A ⊆ B) (hne : A ≠ B) : ¬ IsAntichain (· ⊆ ·) {A, B} :=
  fun h ↦ h (.inl rfl) (.inr rfl) hne hAB

/-! #### Henry (103)

Henry may be a graduate student, chronically stressed, or upset that the Steelers lost, and the
speaker believes all graduate students are chronically stressed. The worlds number the
combinations the speaker leaves open. -/

namespace Henry

/-- Henry is a graduate student. -/
def student : Set (Fin 4) := {0, 3}

/-- Henry is chronically stressed. -/
def stressed : Set (Fin 4) := {0, 1}

/-- Henry is upset that the Steelers lost. -/
def upset : Set (Fin 4) := {2}

/-- The speaker's epistemic possibilities: Henry is no unstressed graduate student. -/
def epistemic : Set (Fin 4) := {0, 1, 2}

-- (103)
theorem epistemic_entailment_plus :
    IsSuperCover {student, stressed, upset} epistemic ∧ 0 ∈ epistemic ∧
      IsAntichain (· ⊆ ·) {student, stressed, upset} ∧
      NonContainment {student, stressed, upset} epistemic ∧
      ∀ S ⊆ epistemic, ¬ Alternativeness {student, stressed, upset} S := by
  refine ⟨⟨⟨_, .inl rfl⟩, ?_, ?_⟩, .inl rfl, ?_, ?_, fun S hS ↦
    not_alternativeness_of_inter_subset (.inl rfl) (.inr (.inl rfl)) ?_ ?_ hS⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨⟨0, by simp [student, epistemic]⟩, ⟨0, by simp [stressed, epistemic]⟩,
      ⟨2, by simp [upset, epistemic]⟩⟩
  · intro v hv
    simp only [epistemic, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨student, .inl rfl, by simp [student]⟩
    · exact ⟨stressed, .inr (.inl rfl), by simp [stressed]⟩
    · exact ⟨upset, .inr (.inr rfl), by simp [upset]⟩
  · rintro X (rfl | rfl | rfl) Y (rfl | rfl | rfl) hXY h
    · exact hXY rfl
    · exact absurd (h (show (3 : Fin 4) ∈ student by simp [student])) (by simp [stressed])
    · exact absurd (h (show (0 : Fin 4) ∈ student by simp [student])) (by simp [upset])
    · exact absurd (h (show (1 : Fin 4) ∈ stressed by simp [stressed])) (by simp [student])
    · exact hXY rfl
    · exact absurd (h (show (0 : Fin 4) ∈ stressed by simp [stressed])) (by simp [upset])
    · exact absurd (h (show (2 : Fin 4) ∈ upset by simp [upset])) (by simp [student])
    · exact absurd (h (show (2 : Fin 4) ∈ upset by simp [upset])) (by simp [stressed])
    · exact hXY rfl
  · rintro X (rfl | rfl | rfl) h
    · simpa [student, epistemic] using h (show (1 : Fin 4) ∈ epistemic by simp [epistemic])
    · simpa [stressed, epistemic] using h (show (2 : Fin 4) ∈ epistemic by simp [epistemic])
    · simpa [upset, epistemic] using h (show (0 : Fin 4) ∈ epistemic by simp [epistemic])
  · exact fun h ↦ absurd (h ▸ (show (3 : Fin 4) ∈ student by simp [student])) (by simp [stressed])
  · intro v ⟨hv, hvE⟩
    simp only [student, epistemic, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hvE
    rcases hv with rfl | rfl
    · simp [stressed]
    · simp at hvE

end Henry

end Simons2005
