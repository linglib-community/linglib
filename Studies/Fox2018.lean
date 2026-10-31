module

public import Linglib.Semantics.Questions.Closure
public import Linglib.Semantics.Exhaustification.InnocentInclusion
public import Studies.Fox2007
public import Studies.FoxHackl2006
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Linglib.Data.Examples.Fox2018
public import Linglib.Data.Examples.Readers

/-!
# Fox (2018): Partition by Exhaustification

Fox derives Dayal's maximality presupposition from a matching condition between a question's
Hamblin set and the partition it induces on the context set. Each member is exhaustified pointwise:
Cell Identification asks that every cell be a member's exhaustification and Non-Vacuity that every
member's exhaustification be a cell, together [that pointwise exhaustification partition the context
set](##qpm_iff_partitionsBy). With the exhaustification (11), which holds where a member is the
strongest true one, [Cell Identification is Dayal's presupposition](##cellIdentification_exh_iff),
while Non-Vacuity [fails on a question with the disjunction of two independent
members](##not_nonVacuity_exh_of_union), the negative island of higher-order questions. With
exhaustification as cell identification (32), a question closed under conjunction and its
disjunctive counterpart identify the same cells by different members, and [the answer operator
(35) returns several answers for the latter](##not_subsingleton_ans_supClosure_range): mention-some.
[The judgments of the degree and higher-order questions](##rows_predicted) follow from whether
their denotations are admissible.

## Implementation notes

* Questions are Hamblin sets `Set (Set W)` rather than `Question` lower sets, since the paper's sets
  are not antichains. The three-location model is a family of atoms `a : ι → Set W` with every set
  of atoms true at some world (`Rich`); the closures of the atoms under conjunction and under
  disjunction, `infClosure (range a)` and `supClosure (range a)`, are the paper's two denotations
  (21)''a and (21)''b.
* The exhaustification (32) is Fox's simplification of [bar-lev-fox-2017]'s operator,
  `Exhaustification.cell`, which agrees with theirs wherever it is consistent (fn. 33).
* The answer operator `ans` quantifies over the cell identifiers instead of taking the unique one
  as (35) does, so it is defined without the presupposition.
* In the data model degrees are rationals, a world of a modal question is its modal base
  (`modalBase`), and the higher-order denotations range over the type shift of fn. 48 (`shift`) on
  three books (`Book`), one French book standing for the French books of (47b). Sections 5–7 on
  the distribution of mention-some are not formalized.

## Errata

* Section 1.3.2 repeats the title of Section 1.3.1, "Inferences of admissible questions", though it
  presents the evidence from acceptability, the negative islands.
* Footnote 24 prints an unresolved cross-reference, "(Error! Bookmark not defined.)".
* The type shift of fn. 48 admits an empty set of parts `A'`, which yields the contradictory
  quantifier that fn. 25 says the rule eliminates; requiring `A'` nonempty would. `shift` follows
  the print, and the contradictory quantifier changes no prediction here.

## References

* [fox-2018]
* [dayal-1996]
* [spector-2008]
* [bar-lev-fox-2017]
* [fox-hackl-2006]
* [heim-1994]
-/

@[expose] public section

namespace Fox2018

open Question Exhaustification Set
open scoped SetRel

variable {W : Type*}

/-! ### Question Partition Matching -/

section Matching

variable (Exh : Set W → Set W) (H : Set (Set W)) (A : Set W)

/-- The contextual partition restricts the strong answers to the context set. -/
def contextualPartition : Set (Set W) := {C | ∃ w ∈ A, C = strongAnswer H w ∩ A}

/-- Cell Identification holds when every cell of the contextual partition is the
exhaustification of some member. -/
def CellIdentification : Prop := ∀ C ∈ contextualPartition H A, ∃ p ∈ H, Exh p ∩ A = C

/-- Non-Vacuity holds when every member exhaustifies to a cell of the contextual partition. -/
def NonVacuity : Prop := ∀ p ∈ H, ∃ C ∈ contextualPartition H A, Exh p ∩ A = C

/-- Question Partition Matching. -/
def QPM : Prop := CellIdentification Exh H A ∧ NonVacuity Exh H A

/-- The pointwise exhaustifications partition the context set. -/
def PartitionsBy : Prop :=
  (∀ p ∈ H, (Exh p ∩ A).Nonempty) ∧
    (∀ p ∈ H, ∀ q ∈ H, Exh p ∩ A = Exh q ∩ A ∨ Disjoint (Exh p ∩ A) (Exh q ∩ A)) ∧
    ∀ w ∈ A, ∃ p ∈ H, w ∈ Exh p

/-- An exhaustifier identifies cells when each of its non-empty values is a strong answer. -/
def IsCellValued : Prop := ∀ p ∈ H, ∀ w ∈ Exh p, Exh p = strongAnswer H w

variable {Exh H A}

theorem mem_contextualPartition {C : Set W} :
    C ∈ contextualPartition H A ↔ ∃ w ∈ A, C = strongAnswer H w ∩ A := Iff.rfl

/-- For an exhaustifier whose values are cells, Question Partition Matching (20) is the demand that
pointwise exhaustification partition the context set, Schwarzschild's restatement (38). -/
theorem qpm_iff_partitionsBy (h : IsCellValued Exh H) : QPM Exh H A ↔ PartitionsBy Exh H A := by
  constructor
  · rintro ⟨hCI, hNV⟩
    refine ⟨fun p hp ↦ ?_, fun p hp q hq ↦ ?_, fun w hw ↦ ?_⟩
    · obtain ⟨_, ⟨w, hw, rfl⟩, hpw⟩ := hNV p hp
      exact ⟨w, by rw [hpw]; exact ⟨self_mem_strongAnswer H w, hw⟩⟩
    · obtain ⟨_, ⟨w, hw, rfl⟩, hpw⟩ := hNV p hp
      obtain ⟨_, ⟨v, hv, rfl⟩, hqv⟩ := hNV q hq
      rw [hpw, hqv]
      rcases strongAnswer_eq_or_disjoint H w v with heq | hdisj
      · exact Or.inl (by rw [heq])
      · exact Or.inr (Disjoint.mono inter_subset_left inter_subset_left hdisj)
    · obtain ⟨p, hp, hpw⟩ := hCI _ ⟨w, hw, rfl⟩
      have : w ∈ Exh p ∩ A := by rw [hpw]; exact ⟨self_mem_strongAnswer H w, hw⟩
      exact ⟨p, hp, this.1⟩
  · rintro ⟨hne, -, hcov⟩
    refine ⟨?_, fun p hp ↦ ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨p, hp, hwp⟩ := hcov w hw
      exact ⟨p, hp, by rw [h p hp w hwp]⟩
    · obtain ⟨w, hwp, hwA⟩ := hne p hp
      exact ⟨_, ⟨w, hwA, rfl⟩, by rw [h p hp w hwp]⟩

end Matching

/-! ### Dayal's presupposition -/

section Dayal

variable {H : Set (Set W)} {A : Set W}

theorem isCellValued_exh : IsCellValued (exh H) H :=
  fun _ hp w hw ↦ exh_eq_strongAnswer H w ((mem_exh_iff_isStrongestTrueAnswer hp).1 hw)

/-- With the exhaustification (11), Cell Identification (19) is Dayal's presupposition at every
world of the context set ((12) and its converse). -/
theorem cellIdentification_exh_iff :
    CellIdentification (exh H) H A ↔ ∀ w ∈ A, IsExhaustivelyResolvable H w := by
  rw [forall_isExhaustivelyResolvable_iff_exh_inter]
  exact ⟨fun h w hw ↦ h _ ⟨w, hw, rfl⟩, fun h _ ⟨w, hw, hC⟩ ↦ hC ▸ h w hw⟩

theorem nonVacuity_exh_iff :
    NonVacuity (exh H) H A ↔ ∀ p ∈ H, ∃ w ∈ A, IsStrongestTrueAnswer H w p := by
  constructor
  · intro h p hp
    obtain ⟨_, ⟨w, hw, rfl⟩, hpw⟩ := h p hp
    have : w ∈ exh H p ∩ A := by rw [hpw]; exact ⟨self_mem_strongAnswer H w, hw⟩
    exact ⟨w, hw, (mem_exh_iff_isStrongestTrueAnswer hp).1 this.1⟩
  · intro h p hp
    obtain ⟨w, hw, hwp⟩ := h p hp
    exact ⟨_, ⟨w, hw, rfl⟩, by rw [exh_eq_strongAnswer H w hwp]⟩

theorem isExhaustivelyResolvable_range_iff_existsUnique {ι : Type*} {a : ι → Set W}
    (ha : ∀ i j, a i ⊆ a j → i = j) (w : W) :
    IsExhaustivelyResolvable (range a) w ↔ ∃! i, w ∈ a i := by
  rw [isExhaustivelyResolvable_range_iff]
  exact exists_congr fun i ↦ and_congr_right fun _ ↦
    ⟨fun h j hj ↦ (ha _ _ (h j hj)).symm, fun h j hj ↦ by rw [h j hj]⟩

theorem isExhaustivelyResolvable_infClosure_range {ι : Type*} [Fintype ι] {a : ι → Set W} {w : W}
    (hw : ∃ i, w ∈ a i) : IsExhaustivelyResolvable (infClosure (range a)) w := by
  classical
  obtain ⟨i, hi⟩ := hw
  let T : Finset ι := Finset.univ.filter (fun i ↦ w ∈ a i)
  have hT : ∀ i, i ∈ T ↔ w ∈ a i := fun i ↦ by simp [T]
  refine ⟨(⋂ i ∈ T, a i), ⟨mem_infClosure_range.2 ⟨T, ⟨i, (hT i).2 hi⟩, rfl⟩,
    mem_iInter₂.2 fun i hi ↦ (hT i).1 hi⟩, ?_⟩
  rintro _ ⟨hq, hwS⟩ v hv
  obtain ⟨S, -, rfl⟩ := mem_infClosure_range.1 hq
  exact mem_iInter₂.2 fun j hj ↦ mem_iInter₂.1 hv j ((hT j).2 (mem_iInter₂.1 hwS j hj))

/-! ### Negative islands -/

/-- A question containing the disjunction of two members neither of which entails the other fails
Non-Vacuity, the negative island of higher-order questions ((26)', (28)). -/
theorem not_nonVacuity_exh_of_union {q₁ q₂ : Set W} (h₁ : q₁ ∈ H) (h₂ : q₂ ∈ H)
    (hu : q₁ ∪ q₂ ∈ H) (h₁₂ : ¬ q₁ ⊆ q₂) (h₂₁ : ¬ q₂ ⊆ q₁) : ¬ NonVacuity (exh H) H A := by
  rw [nonVacuity_exh_iff]
  intro h
  obtain ⟨w, -, hw⟩ := h _ hu
  exact not_dominated_of_isStrongestTrueAnswer hw (dominated_union h₁ h₂ h₁₂ h₂₁)

theorem isStrongestTrueAnswer_box {W' : Type*} {R : SetRel W' W} {p : Set W} (hp : p ∈ H)
    {x : W'} (hx : ∀ v, x ~[R] v ↔ v ∈ p) : IsStrongestTrueAnswer (box H R) x (R.core p) := by
  refine ⟨⟨⟨p, hp, rfl⟩, fun v hv ↦ (hx v).1 hv⟩, ?_⟩
  rintro _ ⟨⟨q, -, rfl⟩, hxq⟩ y hy v hyv
  exact hxq ((hx v).2 (hy hyv))

theorem nonVacuity_box {W' : Type*} {R : SetRel W' W} {A : Set W'}
    (h : ∀ p ∈ H, ∃ x ∈ A, ∀ v, x ~[R] v ↔ v ∈ p) :
    NonVacuity (exh (box H R)) (box H R) A := by
  rw [nonVacuity_exh_iff]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨x, hx, hxp⟩ := h p hp
  exact ⟨x, hx, isStrongestTrueAnswer_box hp hxp⟩

end Dayal

/-! ### Exhaustivity as cell identification -/

section Cell

variable {H : Set (Set W)}

theorem cell_eq_strongAnswer {p : Set W} (hp : p ∈ H) {w : W} (hw : w ∈ cell H p) :
    cell H p = strongAnswer H w := by
  ext v
  rw [mem_strongAnswer]
  constructor
  · intro hv q hq
    by_cases hIE : IsInnocentlyExcludable H p q
    · exact ⟨fun hwq ↦ (hw.2.1 q hIE hwq).elim, fun hvq ↦ (hv.2.1 q hIE hvq).elim⟩
    · exact ⟨fun _ ↦ hv.2.2 q ⟨hq, hIE⟩, fun _ ↦ hw.2.2 q ⟨hq, hIE⟩⟩
  · intro hv
    exact ⟨(hv p hp).1 hw.1, fun q hIE hvq ↦ hw.2.1 q hIE ((hv q hIE.1).2 hvq),
      fun r hr ↦ (hv r hr.1).1 (hw.2.2 r hr)⟩

theorem isCellValued_cell : IsCellValued (cell H) H := fun _ hp _ hw ↦ cell_eq_strongAnswer hp hw

theorem qpm_cell_iff_partitionsBy {A : Set W} : QPM (cell H) H A ↔ PartitionsBy (cell H) H A :=
  qpm_iff_partitionsBy isCellValued_cell

theorem cell_diamond {w s n e : Set W} (h : Fox2007.IsDiamond w s n e) :
    cell {w, s, n, e} w = (s ∩ n) \ e := by
  rw [cell_eq_of_iff _ _ fun q hq ↦ h.isInnocentlyExcludable_iff hq]
  have hne : ∀ q ∈ ({w, s, n} : Set (Set W)), q ≠ e := by
    obtain ⟨rfl, hs, hn, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    rintro q (rfl | rfl | rfl) hqe
    · exact ha.2 (hn (hqe ▸ Or.inl ha.1))
    · exact ha.2 (hn (hqe ▸ ha.1))
    · exact hb.2 (hs (hqe ▸ hb.1))
  ext x
  constructor
  · rintro ⟨-, hx⟩
    exact ⟨⟨(hx s (by simp)).2 (hne s (by simp)), (hx n (by simp)).2 (hne n (by simp))⟩,
      fun hxe ↦ (hx e (by simp)).1 hxe rfl⟩
  · rintro ⟨⟨hxs, hxn⟩, hxe⟩
    refine ⟨h.union ▸ Or.inl hxs, fun q hq ↦ ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    obtain h1 | h1 | h1 | h1 := hq <;> subst q
    · exact iff_of_true (h.union ▸ Or.inl hxs) (hne _ (by simp))
    · exact iff_of_true hxs (hne _ (by simp))
    · exact iff_of_true hxn (hne _ (by simp))
    · exact iff_of_false hxe fun h' ↦ h' rfl

theorem cell_eq_exhIter_two {w s n e : Set W} (h : Fox2007.IsDiamond w s n e)
    (hne : ((s ∩ n) \ e).Nonempty) : cell {w, s, n, e} w = Fox2007.exhIter {w, s, n, e} 2 w := by
  rw [cell_diamond h, h.exhIter_two_eq hne]

end Cell

/-! ### Mention-some and mention-all -/

section Closures

variable {ι : Type*} {a : ι → Set W}

-- The atoms true at a world, the criteria it satisfies.
set_option hygiene false in
local notation "atoms " w:max => Preorder.satisfied (fun v i ↦ v ∈ a i) Set.univ w

/-- Every set of atoms is the set true at some world. -/
def Rich (a : ι → Set W) : Prop :=
  ∀ T : Finset ι, ∃ w, Preorder.satisfied (fun v i ↦ v ∈ a i) Set.univ w = ↑T

/-- The worlds at which exactly the atoms of `T` are true form a cell of the logical partition of
either closure. -/
def atomCell (a : ι → Set W) (T : Finset ι) : Set W :=
  {v | Preorder.satisfied (fun v i ↦ v ∈ a i) Set.univ v = ↑T}

theorem mem_atomCell {T : Finset ι} {v : W} : v ∈ atomCell a T ↔ atoms v = ↑T := Iff.rfl

theorem strongAnswer_infClosure_range_eq {T : Finset ι} {w : W} (hw : atoms w = ↑T) :
    strongAnswer (infClosure (range a)) w = atomCell a T := by
  ext v
  rw [strongAnswer_eq_cell, partition_infClosure_range, Setoid.mem_cell, Setoid.ker_def, hw,
    mem_atomCell]

theorem strongAnswer_supClosure_range_eq {T : Finset ι} {w : W} (hw : atoms w = ↑T) :
    strongAnswer (supClosure (range a)) w = atomCell a T := by
  ext v
  rw [strongAnswer_eq_cell, partition_supClosure_range, Setoid.mem_cell, Setoid.ker_def, hw,
    mem_atomCell]

theorem leALT_infClosure_range_iff {u v : W} :
    (u ≤[infClosure (range a)] v) ↔ atoms u ⊆ atoms v := by
  constructor
  · intro h i hi
    exact mem_satisfied_iff.2 (h _ (subset_infClosure (mem_range_self i)) (mem_satisfied_iff.1 hi))
  · rintro h _ hq hu
    obtain ⟨S, -, rfl⟩ := mem_infClosure_range.1 hq
    exact mem_biInter_iff_subset.2 ((mem_biInter_iff_subset.1 hu).trans h)

theorem leALT_supClosure_range_iff {u v : W} :
    (u ≤[supClosure (range a)] v) ↔ atoms u ⊆ atoms v := by
  constructor
  · intro h i hi
    exact mem_satisfied_iff.2 (h _ (subset_supClosure (mem_range_self i)) (mem_satisfied_iff.1 hi))
  · rintro h _ hq hu
    obtain ⟨S, -, rfl⟩ := mem_supClosure_range.1 hq
    obtain ⟨i, hi, hui⟩ := mem_iUnion₂.1 hu
    exact mem_biUnion hi (mem_satisfied_iff.1 (h (mem_satisfied_iff.2 hui)))

variable (hrich : Rich a)
include hrich

theorem biInter_subset_biInter_iff {S T : Finset ι} :
    (⋂ i ∈ T, a i) ⊆ (⋂ i ∈ S, a i) ↔ S ⊆ T := by
  constructor
  · intro h i hi
    obtain ⟨w, hw⟩ := hrich T
    have := mem_biInter_iff_subset.1 (h (mem_biInter_iff_subset.2 (by rw [hw])))
      (Finset.mem_coe.2 hi)
    rw [hw] at this
    exact Finset.mem_coe.1 this
  · exact fun h _ hv ↦ mem_iInter₂.2 fun i hi ↦ mem_iInter₂.1 hv i (h hi)

theorem biUnion_subset_biUnion_iff {S T : Finset ι} : (⋃ i ∈ S, a i) ⊆ (⋃ i ∈ T, a i) ↔ S ⊆ T := by
  constructor
  · intro h i hi
    obtain ⟨w, hw⟩ := hrich ({i} : Finset ι)
    have hwi : w ∈ a i := by
      refine mem_satisfied_iff.1 ?_
      rw [hw]
      exact Finset.mem_coe.2 (Finset.mem_singleton_self i)
    obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.1 (h (mem_biUnion hi hwi))
    have : j ∈ atoms w := mem_satisfied_iff.2 hwj
    rw [hw, Finset.coe_singleton, mem_singleton_iff] at this
    exact this ▸ hj
  · rintro h _ hv
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 hv
    exact mem_biUnion (h hi) hvi

theorem isInnocentlyExcludable_conj_iff [Fintype ι] {S T : Finset ι} (hS : S.Nonempty) :
    IsInnocentlyExcludable (infClosure (range a)) (⋂ i ∈ T, a i) (⋂ i ∈ S, a i) ↔ ¬ S ⊆ T := by
  obtain ⟨w₀, hw₀⟩ := hrich T
  have hw₀T : w₀ ∈ (⋂ i ∈ T, a i) := mem_biInter_iff_subset.2 (by rw [hw₀])
  constructor
  · exact fun hIE hST ↦ not_isInnocentlyExcludable_of_phi_subset (finite_range a).infClosure
      ⟨w₀, hw₀T⟩
      ((biInter_subset_biInter_iff hrich).2 hST) hIE
  · intro hST
    refine .of_forall_subset_or_notMem (mem_infClosure_range.2 ⟨_, hS, rfl⟩) hw₀T ?_ ?_
    · rw [mem_biInter_iff_subset, hw₀]
      exact fun h ↦ hST (Finset.coe_subset.1 h)
    · rintro _ hq
      obtain ⟨U, -, rfl⟩ := mem_infClosure_range.1 hq
      by_cases hUT : U ⊆ T
      · exact Or.inl ((biInter_subset_biInter_iff hrich).2 hUT)
      · right
        rw [mem_biInter_iff_subset, hw₀]
        exact fun h ↦ hUT (Finset.coe_subset.1 h)

theorem mem_exhMW_supClosure_range_iff {T : Finset ι} {u : W} :
    u ∈ exhMW (supClosure (range a)) (⋃ i ∈ T, a i) ↔ ∃ i ∈ T, atoms u = ↑({i} : Finset ι) := by
  have hsing : ∀ {i : ι} {v : W}, atoms v = ↑({i} : Finset ι) → v ∈ a i := fun {i v} hv ↦ by
    refine mem_satisfied_iff.1 ?_
    rw [hv]
    exact Finset.mem_coe.2 (Finset.mem_singleton_self i)
  constructor
  · rintro ⟨hu, hmin⟩
    obtain ⟨i, hi, hui⟩ := mem_iUnion₂.1 hu
    obtain ⟨v, hv⟩ := hrich ({i} : Finset ι)
    have hvu : v ≤[supClosure (range a)] u := leALT_supClosure_range_iff.2 (by
      rw [hv, Finset.coe_singleton]
      exact singleton_subset_iff.2 (mem_satisfied_iff.2 hui))
    have huv : u ≤[supClosure (range a)] v :=
      by_contra fun h ↦ hmin ⟨v, mem_biUnion hi (hsing hv), hvu, h⟩
    refine ⟨i, hi, subset_antisymm ?_ ?_⟩
    · rw [← hv]
      exact leALT_supClosure_range_iff.1 huv
    · rw [Finset.coe_singleton]
      exact singleton_subset_iff.2 (mem_satisfied_iff.2 hui)
  · rintro ⟨i, hi, hu⟩
    refine ⟨mem_biUnion hi (hsing hu), ?_⟩
    rintro ⟨v, hv, hvu, hnuv⟩
    obtain ⟨j, -, hvj⟩ := mem_iUnion₂.1 hv
    have hj : j ∈ atoms v := mem_satisfied_iff.2 hvj
    have hji : j ∈ atoms u := leALT_supClosure_range_iff.1 hvu hj
    rw [hu, Finset.coe_singleton, mem_singleton_iff] at hji
    subst hji
    refine hnuv (leALT_supClosure_range_iff.2 ?_)
    rw [hu, Finset.coe_singleton]
    exact singleton_subset_iff.2 hj

theorem isInnocentlyExcludable_disj_iff {S T : Finset ι} (hS : S.Nonempty) :
    IsInnocentlyExcludable (supClosure (range a)) (⋃ i ∈ T, a i) (⋃ i ∈ S, a i) ↔ Disjoint S T := by
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (mem_supClosure_range.2 ⟨_, hS, rfl⟩),
    Finset.disjoint_left]
  constructor
  · intro h i hiS hiT
    obtain ⟨v, hv⟩ := hrich ({i} : Finset ι)
    refine h ((mem_exhMW_supClosure_range_iff hrich).2 ⟨i, hiT, hv⟩) (mem_biUnion hiS ?_)
    refine mem_satisfied_iff.1 ?_
    rw [hv]
    exact Finset.mem_coe.2 (Finset.mem_singleton_self i)
  · intro h u hu huS
    obtain ⟨i, hiT, hui⟩ := (mem_exhMW_supClosure_range_iff hrich).1 hu
    obtain ⟨j, hjS, huj⟩ := mem_iUnion₂.1 huS
    have : j ∈ atoms u := mem_satisfied_iff.2 huj
    rw [hui, Finset.coe_singleton, mem_singleton_iff] at this
    exact h hjS (this ▸ hiT)

theorem cell_biInter [Fintype ι] (T : Finset ι) :
    cell (infClosure (range a)) (⋂ i ∈ T, a i) = atomCell a T := by
  rw [infClosure_range_eq_image, cell_image_eq (P := fun S ↦ ¬ S ⊆ T) _ fun S hS ↦ by
    rw [← infClosure_range_eq_image]; exact isInnocentlyExcludable_conj_iff hrich hS]
  ext x
  simp only [mem_ofPred_eq, mem_biInter_iff_subset, not_not, mem_atomCell]
  constructor
  · rintro ⟨-, h⟩
    ext i
    have := h {i} ⟨i, Finset.mem_singleton_self i⟩
    rw [Finset.coe_singleton, singleton_subset_iff, Finset.singleton_subset_iff] at this
    exact this.trans Finset.mem_coe.symm
  · intro hx
    exact ⟨by rw [hx], fun S _ ↦ by rw [hx, Finset.coe_subset]⟩

theorem cell_biUnion {T : Finset ι} (hT : T.Nonempty) :
    cell (supClosure (range a)) (⋃ i ∈ T, a i) = atomCell a T := by
  rw [supClosure_range_eq_image, cell_image_eq (P := fun S ↦ Disjoint S T) _ fun S hS ↦ by
    rw [← supClosure_range_eq_image]; exact isInnocentlyExcludable_disj_iff hrich hS]
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop, Finset.not_disjoint_iff, mem_atomCell]
  constructor
  · rintro ⟨-, h⟩
    ext i
    have := h {i} ⟨i, Finset.mem_singleton_self i⟩
    simp only [Finset.mem_singleton, exists_eq_left] at this
    exact mem_satisfied_iff.trans (this.trans Finset.mem_coe.symm)
  · intro hx
    obtain ⟨i, hi⟩ := hT
    have hmem : ∀ j, x ∈ a j ↔ j ∈ T := fun j ↦ by
      rw [← mem_satisfied_iff, hx, Finset.mem_coe]
    refine ⟨⟨i, hi, (hmem i).2 hi⟩, fun S _ ↦ ?_⟩
    simp only [hmem]

/-- The revised answer operator returns the true members entailing the cell identifier. -/
def ans (Exh : Set W → Set W) (H : Set (Set W)) (w : W) : Set (Set W) :=
  {q ∈ H | w ∈ q ∧ ∀ p ∈ H, w ∈ Exh p → q ⊆ p}

theorem ans_infClosure_range [Fintype ι] {T : Finset ι} (hT : T.Nonempty) {w : W}
    (hw : atoms w = ↑T) :
    ans (cell (infClosure (range a))) (infClosure (range a)) w = {(⋂ i ∈ T, a i)} := by
  ext q
  rw [mem_singleton_iff]
  constructor
  · rintro ⟨hq, hwS, h⟩
    obtain ⟨S, -, rfl⟩ := mem_infClosure_range.1 hq
    have h1 : S ⊆ T := by
      have := mem_biInter_iff_subset.1 hwS
      rw [hw] at this
      exact Finset.coe_subset.1 this
    have h2 : T ⊆ S := (biInter_subset_biInter_iff hrich).1
      (h _ (mem_infClosure_range.2 ⟨_, hT, rfl⟩) (by rw [cell_biInter hrich T]; exact hw))
    rw [Finset.Subset.antisymm h1 h2]
  · rintro rfl
    refine ⟨mem_infClosure_range.2 ⟨_, hT, rfl⟩, mem_biInter_iff_subset.2 (by rw [hw]), ?_⟩
    rintro _ hq hwU
    obtain ⟨U, hU, rfl⟩ := mem_infClosure_range.1 hq
    rw [cell_biInter hrich U] at hwU
    have hwU' : atoms w = ↑U := hwU
    rw [hw, Finset.coe_inj] at hwU'
    subst hwU'
    exact subset_rfl

theorem ans_supClosure_range {T : Finset ι} (hT : T.Nonempty) {w : W} (hw : atoms w = ↑T) :
    ans (cell (supClosure (range a))) (supClosure (range a)) w =
      (fun S ↦ ⋃ i ∈ S, a i) '' {S | S.Nonempty ∧ S ⊆ T} := by
  ext q
  constructor
  · rintro ⟨hq, -, h⟩
    obtain ⟨S, hS, rfl⟩ := mem_supClosure_range.1 hq
    exact ⟨S, ⟨hS, (biUnion_subset_biUnion_iff hrich).1
      (h _ (mem_supClosure_range.2 ⟨_, hT, rfl⟩) (by rw [cell_biUnion hrich hT]; exact hw))⟩, rfl⟩
  · rintro ⟨S, ⟨⟨i, hi⟩, hST⟩, rfl⟩
    refine ⟨mem_supClosure_range.2 ⟨_, ⟨i, hi⟩, rfl⟩, mem_biUnion hi ?_, ?_⟩
    · refine mem_satisfied_iff.1 ?_
      rw [hw]
      exact Finset.mem_coe.2 (hST hi)
    · rintro _ hq hwU
      obtain ⟨U, hU, rfl⟩ := mem_supClosure_range.1 hq
      rw [cell_biUnion hrich hU] at hwU
      have hwU' : atoms w = ↑U := hwU
      rw [hw, Finset.coe_inj] at hwU'
      subst hwU'
      exact (biUnion_subset_biUnion_iff hrich).2 hST

/-- On the disjunctive denotation (21)''b the answer operator (35) returns more than one answer at a
world where two atoms are true: mention-some. -/
theorem not_subsingleton_ans_supClosure_range {T : Finset ι} (hT : 1 < T.card) {w : W}
    (hw : atoms w = ↑T) :
    ¬ (ans (cell (supClosure (range a))) (supClosure (range a)) w).Subsingleton := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hT
  rw [ans_supClosure_range hrich ⟨i, hi⟩ hw]
  intro h
  have := h ⟨{i}, ⟨⟨i, Finset.mem_singleton_self i⟩, Finset.singleton_subset_iff.2 hi⟩, rfl⟩
    ⟨T, ⟨⟨i, hi⟩, subset_rfl⟩, rfl⟩
  have := (biUnion_subset_biUnion_iff hrich).1 this.ge
  exact hij (Finset.mem_singleton.1 (this hj)).symm

end Closures

/-! ### Admissible questions and the data

A question is admissible when some context set meets Question Partition Matching. Under a necessity
modal every question is (fn. 26), under negation one that contains the disjunction of two
independent members is not, and on a dense scale the negative degree question is not. The
higher-order question of Spector's fragments quantifies over Fox's type shift of the restrictor
(fn. 48), which on single books yields no disjunction. -/

section Data

/-- A question is admissible when some nonempty context set meets Question Partition Matching. -/
def Admissible {W : Type*} (H : Set (Set W)) : Prop := ∃ A : Set W, A.Nonempty ∧ QPM (exh H) H A

/-- A world seen through its modal base: the possibilities the base allows. -/
abbrev modalBase (S : Type*) : SetRel (Set S) S := {p | p.2 ∈ p.1}

-- fn. 26, (27), (29): under a necessity modal a question is admissible, on the modal bases that
-- are its members
theorem admissible_box {S : Type*} {H : Set (Set S)} (hH : H.Nonempty) :
    Admissible (box H (modalBase S)) :=
  ⟨H, hH, cellIdentification_exh_iff.2 fun _ hx ↦ ⟨_, isStrongestTrueAnswer_box hx fun _ ↦ .rfl⟩,
    nonVacuity_box fun p hp ↦ ⟨p, hp, fun _ ↦ .rfl⟩⟩

-- (26), (28): a question with the disjunction of two independent members is inadmissible
theorem not_admissible_of_union {W : Type*} {H : Set (Set W)} {q₁ q₂ : Set W} (h₁ : q₁ ∈ H)
    (h₂ : q₂ ∈ H) (hu : q₁ ∪ q₂ ∈ H) (h₁₂ : ¬ q₁ ⊆ q₂) (h₂₁ : ¬ q₂ ⊆ q₁) : ¬ Admissible H :=
  fun ⟨_, _, _, hNV⟩ ↦ not_nonVacuity_exh_of_union h₁ h₂ hu h₁₂ h₂₁ hNV

variable {D : Type*} [LinearOrder D]

theorem isStrongestTrueAnswer_Ici (w : D) : IsStrongestTrueAnswer (range Ici) w (Ici w) := by
  refine ⟨⟨⟨w, rfl⟩, self_mem_Ici⟩, ?_⟩
  rintro _ ⟨⟨d, rfl⟩, hw⟩
  exact Ici_subset_Ici.2 hw

-- (16a), (17a), (18a)
theorem admissible_Ici [Nonempty D] : Admissible (range Ici : Set (Set D)) :=
  ⟨univ, univ_nonempty, cellIdentification_exh_iff.2 fun w _ ↦ ⟨_, isStrongestTrueAnswer_Ici w⟩,
    nonVacuity_exh_iff.2 fun _ ⟨d, hd⟩ ↦ ⟨d, mem_univ d, hd ▸ isStrongestTrueAnswer_Ici d⟩⟩

-- (16b), (17b), (18b): on a dense scale the negative degree question is inadmissible
theorem not_admissible_Iio [DenselyOrdered D] : ¬ Admissible (range Iio : Set (Set D)) :=
  fun ⟨_, ⟨w, hw⟩, hCI, _⟩ ↦ FoxHackl2006.negation_not_isExhaustivelyResolvable id
    Function.surjective_id w (cellIdentification_exh_iff.1 hCI w hw)

variable {ι : Type*}

/-- Fox's type shift `S` (fn. 48): the quantifiers true of a property when some member of a set
`A'` of parts of a plurality in the restrictor `A` has it. A plurality is a nonempty set of books,
and a quantifier is the set of reading situations, the sets of books read, at which it holds of
*we read*. -/
def shift (A : Set (Set ι)) : Set (Set (Set ι)) :=
  {Q | ∃ x ∈ A, ∃ A' ⊆ {x' | x'.Nonempty ∧ x' ⊆ x}, Q = {s | ∃ X ∈ A', X ⊆ s}}

/-- The restrictor of a singular *wh*-phrase, *which book*: the single books. -/
def singulars : Set (Set ι) := range singleton

/-- The restrictor of a plural or number-neutral *wh*-phrase, *which books* or *what*: the
pluralities. -/
def pluralities : Set (Set ι) := {x | x.Nonempty}

theorem lift_mem_shift {X : Set ι} (hX : X.Nonempty) : {s | X ⊆ s} ∈ shift pluralities :=
  ⟨X, hX, {X}, singleton_subset_iff.2 ⟨hX, subset_rfl⟩, by ext; simp⟩

theorem disjunction_mem_shift {X Y : Set ι} (hX : X.Nonempty) (hY : Y.Nonempty) :
    {s | X ⊆ s ∨ Y ⊆ s} ∈ shift pluralities :=
  ⟨X ∪ Y, hX.mono subset_union_left, {X, Y},
    insert_subset_iff.2 ⟨⟨hX, subset_union_left⟩, singleton_subset_iff.2 ⟨hY, subset_union_right⟩⟩,
    by ext; simp⟩

-- fn. 48: from single books the shift yields only the contradiction and the books' lifts
theorem eq_empty_or_lift_of_mem_shift_singulars {Q : Set (Set ι)} (h : Q ∈ shift singulars) :
    Q = ∅ ∨ ∃ b, Q = {s | b ∈ s} := by
  obtain ⟨_, ⟨b, rfl⟩, A', hA', rfl⟩ := h
  have : A' ⊆ {{b}} := fun x hx ↦ (Nonempty.subset_singleton_iff (hA' hx).1).1 (hA' hx).2
  rcases subset_singleton_iff_eq.1 this with rfl | rfl
  · left; ext; simp
  · right; exact ⟨b, by ext; simp⟩

-- (48): a singular *wh*-phrase has no disjunction of two books in its type shift
theorem disjunction_notMem_shift_singulars {b₁ b₂ : ι} (h : b₁ ≠ b₂) :
    {s | {b₁} ⊆ s ∨ {b₂} ⊆ s} ∉ shift singulars := fun hQ ↦ by
  have h₁ : ({b₁} : Set ι) ∈ {s : Set ι | {b₁} ⊆ s ∨ {b₂} ⊆ s} := by simp
  have h₂ : ({b₂} : Set ι) ∈ {s : Set ι | {b₁} ⊆ s ∨ {b₂} ⊆ s} := by simp
  rcases eq_empty_or_lift_of_mem_shift_singulars hQ with hQ | ⟨b, hQ⟩
  · rw [hQ] at h₁
    exact h₁
  · rw [hQ] at h₁ h₂
    simp only [mem_ofPred_eq, mem_singleton_iff] at h₁ h₂
    exact h (h₁.symm.trans h₂)

-- (26), (26)', (28): under negation the higher-order question is inadmissible
theorem not_admissible_compl_shift {b₁ b₂ : ι} (h : b₁ ≠ b₂) :
    ¬ Admissible (compl '' shift pluralities : Set (Set (Set ι))) := by
  refine not_admissible_of_union (q₁ := {s | {b₁} ⊆ s}ᶜ) (q₂ := {s | {b₂} ⊆ s}ᶜ)
    (mem_image_of_mem _ (lift_mem_shift (singleton_nonempty b₁)))
    (mem_image_of_mem _ (lift_mem_shift (singleton_nonempty b₂))) ?_ ?_ ?_
  · rw [← compl_inter]
    refine ⟨_, lift_mem_shift (insert_nonempty b₁ {b₂}), ?_⟩
    ext s
    simp [insert_subset_iff]
  · exact fun h' ↦ h' (show ({b₂} : Set ι) ∈ {s | {b₁} ⊆ s}ᶜ by simpa using h)
      (show ({b₂} : Set ι) ∈ {s | {b₂} ⊆ s} by simp)
  · exact fun h' ↦ h' (show ({b₁} : Set ι) ∈ {s | {b₂} ⊆ s}ᶜ by simpa using h.symm)
      (show ({b₁} : Set ι) ∈ {s | {b₁} ⊆ s} by simp)

/-- The books of the examples: *War and Peace* and *Brothers Karamazov*, the Russian books of
(47b), and a French book standing for its French books. -/
inductive Book where
  | warAndPeace
  | brothersKaramazov
  | french
  deriving DecidableEq

/-- *War and Peace or Brothers Karamazov*. -/
def warAndPeaceOrBrothersKaramazov : Set (Set Book) :=
  {s | {.warAndPeace} ⊆ s ∨ {.brothersKaramazov} ⊆ s}

/-- *The Russian books or the French books* (47b). -/
def russianOrFrench : Set (Set Book) :=
  {s | {.warAndPeace, .brothersKaramazov} ⊆ s ∨ {.french} ⊆ s}

/-- The judgments of the data are the model's predictions. The degree question is admissible
plain and under a necessity modal and inadmissible under negation on a dense scale (16), and a
fragment's narrow-scope reading is available exactly when its quantifier is in the restrictor's
type shift and the higher-order question is admissible ((24), (26), (27), (47), (48)). -/
theorem rows_predicted :
    (Admissible (range Ici : Set (Set ℚ)) ↔ Examples.ex16a.judgment.band = .accepted) ∧
    (Admissible (range Iio : Set (Set ℚ)) ↔ Examples.ex16b.judgment.band = .accepted) ∧
    (Admissible (box (range Iio : Set (Set ℚ)) (modalBase ℚ)) ↔
      Examples.ex16c.judgment.band = .accepted) ∧
    (warAndPeaceOrBrothersKaramazov ∈ shift pluralities ∧
        Admissible (box (shift pluralities) (modalBase (Set Book))) ↔
      (Examples.ex24.readings.lookup "required > or").map Judgment.band ≠ some .rejected) ∧
    (warAndPeaceOrBrothersKaramazov ∈ shift pluralities ∧
        Admissible (compl '' shift pluralities : Set (Set (Set Book))) ↔
      (Examples.ex26.readings.lookup "not > or").map Judgment.band ≠ some .rejected) ∧
    (warAndPeaceOrBrothersKaramazov ∈ shift pluralities ∧
        Admissible (box (compl '' shift pluralities) (modalBase (Set Book))) ↔
      (Examples.ex27.readings.lookup "not > or").map Judgment.band ≠ some .rejected) ∧
    (warAndPeaceOrBrothersKaramazov ∈ shift pluralities ∧
        Admissible (box (shift pluralities) (modalBase (Set Book))) ↔
      (Examples.ex47a.readings.lookup "required > or").map Judgment.band ≠ some .rejected) ∧
    (russianOrFrench ∈ shift pluralities ∧
        Admissible (box (shift pluralities) (modalBase (Set Book))) ↔
      (Examples.ex47b.readings.lookup "required > or").map Judgment.band ≠ some .rejected) ∧
    (warAndPeaceOrBrothersKaramazov ∈ shift singulars ∧
        Admissible (box (shift singulars) (modalBase (Set Book))) ↔
      (Examples.ex48.readings.lookup "required > or").map Judgment.band ≠ some .rejected) := by
  have hwb : warAndPeaceOrBrothersKaramazov ∈ shift pluralities :=
    disjunction_mem_shift (singleton_nonempty _) (singleton_nonempty _)
  have hbox := admissible_box ⟨_, hwb⟩
  refine ⟨iff_of_true admissible_Ici (by decide), iff_of_false not_admissible_Iio (by decide),
    iff_of_true (admissible_box (range_nonempty _)) (by decide),
    iff_of_true ⟨hwb, hbox⟩ (by decide),
    iff_of_false (fun h ↦ not_admissible_compl_shift (b₁ := Book.warAndPeace)
      (b₂ := .brothersKaramazov) (by decide) h.2) (by decide),
    iff_of_true ⟨hwb, admissible_box ⟨_, mem_image_of_mem _ hwb⟩⟩ (by decide),
    iff_of_true ⟨hwb, hbox⟩ (by decide),
    iff_of_true ⟨disjunction_mem_shift (insert_nonempty _ _) (singleton_nonempty _), hbox⟩
      (by decide),
    iff_of_false (fun h ↦ disjunction_notMem_shift_singulars (b₁ := Book.warAndPeace)
      (b₂ := .brothersKaramazov) (by decide) h.1) (by decide)⟩

end Data

end Fox2018
