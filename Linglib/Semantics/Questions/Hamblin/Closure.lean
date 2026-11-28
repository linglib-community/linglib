module

public import Linglib.Semantics.Questions.Hamblin.StrongestAnswer
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Core.Order.SupClosed

/-!
# Hamblin sets closed under conjunction or disjunction

A wh-question has one atomic answer `a i` for each individual `i`. Accounts differ on which further
propositions belong to its Hamblin set.

* On the account of [dayal-1996], the set is closed under conjunction: it is
  `infClosure (Set.range a)`.
* On the account of [spector-2008] and [fox-2018], it is closed under disjunction: it is
  `supClosure (Set.range a)`.

Both closures raise the same partition question as the atoms themselves.

We also define `hamblin P D`, which contains both the conjunctions and the disjunctions. Its
strongest true answer is the conjunction of its true members. See
`Question.isStrongestTrueAnswer_hamblin`.

## References

* [dayal-1996]
* [spector-2008]
* [fox-2007]
* [fox-2018]
-/

public section

namespace Question

variable {W ι : Type*} {a : ι → Set W}

@[simp] theorem mem_satisfied_iff {w : W} {i : ι} :
    i ∈ {i | w ∈ a i} ↔ w ∈ a i :=
  Iff.rfl

theorem mem_biInter_iff_subset {S : Finset ι} {w : W} :
    w ∈ ⋂ i ∈ S, a i ↔ ↑S ⊆ {i | w ∈ a i} :=
  Set.mem_iInter₂.trans ⟨fun h _ hi ↦ h _ hi, fun h _ hi ↦ h hi⟩

theorem ofProps_infClosure_range :
    Setoid.ofProps (infClosure (Set.range a)) =
      Setoid.ker fun v ↦ {i | v ∈ a i} := by
  ext v w
  rw [Setoid.ofProps_iff, Setoid.ker_def]
  constructor
  · intro h
    ext i
    simpa only [Set.mem_ofPred_eq, Set.mem_univ, true_and] using
      h _ (subset_infClosure (Set.mem_range_self i))
  · intro h q hq
    obtain ⟨S, -, rfl⟩ := Set.mem_infClosure_range.1 hq
    rw [mem_biInter_iff_subset, mem_biInter_iff_subset, h]

theorem ofProps_supClosure_range :
    Setoid.ofProps (supClosure (Set.range a)) =
      Setoid.ker fun v ↦ {i | v ∈ a i} := by
  ext v w
  rw [Setoid.ofProps_iff, Setoid.ker_def]
  constructor
  · intro h
    ext i
    simpa only [Set.mem_ofPred_eq, Set.mem_univ, true_and] using
      h _ (subset_supClosure (Set.mem_range_self i))
  · intro h q hq
    obtain ⟨S, -, rfl⟩ := Set.mem_supClosure_range.1 hq
    simp only [Set.ext_iff, Set.mem_ofPred_eq] at h
    simp only [Set.mem_iUnion, exists_prop, h]

theorem ofProps_infClosure_range_eq_supClosure_range :
    Setoid.ofProps (infClosure (Set.range a)) = Setoid.ofProps (supClosure (Set.range a)) :=
  ofProps_infClosure_range.trans ofProps_supClosure_range.symm

/-- The conjunction of the members true at a world is the strongest true member of the closure
of a finite family under conjunction. -/
theorem isStrongestTrueAnswer_infClosure_image {s : Set ι} {w : W} (hs : s.Finite)
    (h : ∃ i ∈ s, w ∈ a i) :
    IsStrongestTrueAnswer (infClosure (a '' s)) w (⋂ i ∈ {i ∈ s | w ∈ a i}, a i) := by
  obtain ⟨i, his, hi⟩ := h
  have hT : {i ∈ s | w ∈ a i}.Finite := hs.subset (Set.sep_subset _ _)
  refine ⟨⟨Set.mem_infClosure_image.2 ⟨hT.toFinset, ⟨i, by simp [his, hi]⟩,
    by simp +contextual [Set.subset_def], by simp⟩, by simp +contextual⟩, ?_⟩
  rintro _ ⟨hq, hw⟩
  obtain ⟨t, -, hts, rfl⟩ := Set.mem_infClosure_image.1 hq
  exact Set.subset_iInter₂ fun j hj ↦
    Set.biInter_subset_of_mem (s := {i ∈ s | w ∈ a i}) ⟨hts hj, Set.mem_iInter₂.1 hw j hj⟩

theorem presupposition_infClosure_image {s : Set ι} (hs : s.Finite) :
    presupposition (infClosure (a '' s)) = ⋃ i ∈ s, a i := by
  refine Set.ext fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ⟨_, isStrongestTrueAnswer_infClosure_image hs
    (by simpa using h)⟩⟩
  obtain ⟨_, hq, hw⟩ := h.exists_mem
  obtain ⟨t, ⟨i, hi⟩, hts, rfl⟩ := Set.mem_infClosure_image.1 hq
  exact Set.mem_biUnion (hts hi) (Set.mem_iInter₂.1 hw i hi)

/-! ### Conjunctions and disjunctions together -/

section Hamblin

variable (P : ι → Set W) (D : Set ι)

/-- The Hamblin set of an interrogative with nucleus `P` over the domain `D`, ranging over
conjunctions and disjunctions of individuals: the conjunctions and the disjunctions of `P` over the
nonempty finite subsets of `D`. -/
@[expose] def hamblin : Set (Set W) := infClosure (P '' D) ∪ supClosure (P '' D)

variable {P D} {q : Set W} {w : W}

theorem mem_hamblin : q ∈ hamblin P D ↔
    ∃ X : Finset ι, X.Nonempty ∧ ↑X ⊆ D ∧ (⋂ x ∈ X, P x = q ∨ ⋃ x ∈ X, P x = q) := by
  simp only [hamblin, Set.mem_union, Set.mem_infClosure_image, Set.mem_supClosure_image,
    ← exists_or, ← and_or_left]

theorem hamblin_mono {D' : Set ι} (h : D' ⊆ D) : hamblin P D' ⊆ hamblin P D :=
  Set.union_subset_union (infClosure_mono (Set.image_mono h)) (supClosure_mono (Set.image_mono h))

@[simp] theorem hamblin_singleton (x : ι) : hamblin P {x} = {P x} := by simp [hamblin]

@[simp] theorem hamblin_empty : hamblin P ∅ = ∅ := by simp [hamblin]

theorem subset_biUnion_of_mem_hamblin (hq : q ∈ hamblin P D) : q ⊆ ⋃ x ∈ D, P x := by
  obtain ⟨X, ⟨x, hx⟩, hXD, rfl | rfl⟩ := mem_hamblin.1 hq
  · exact (Set.biInter_subset_of_mem hx).trans (Set.subset_biUnion_of_mem (hXD hx))
  · exact Set.biUnion_subset_biUnion_left hXD

theorem isStrongestTrueAnswer_hamblin (hD : D.Finite) (h : ∃ x ∈ D, w ∈ P x) :
    IsStrongestTrueAnswer (hamblin P D) w (⋂ x ∈ {x ∈ D | w ∈ P x}, P x) := by
  have hs := isStrongestTrueAnswer_infClosure_image hD h
  refine ⟨⟨.inl hs.1.1, hs.1.2⟩, ?_⟩
  rintro q ⟨hq | hq, hw⟩
  · exact hs.2 ⟨hq, hw⟩
  · obtain ⟨t, -, hts, rfl⟩ := Set.mem_supClosure_image.1 hq
    obtain ⟨x, hx, hwx⟩ := Set.mem_iUnion₂.1 hw
    exact (hs.2 ⟨subset_infClosure (Set.mem_image_of_mem _ (hts hx)), hwx⟩).trans
      (Set.subset_biUnion_of_mem hx)

/-- An interrogative over conjunctions and disjunctions presupposes only that some member of its
domain makes the nucleus true: the conjunction over all such members is the strongest true answer,
however many there are. -/
theorem presupposition_hamblin (hD : D.Finite) : presupposition (hamblin P D) = ⋃ x ∈ D, P x :=
  Set.ext fun _ ↦ ⟨fun h ↦ let ⟨_, hq, hw⟩ := h.exists_mem; subset_biUnion_of_mem_hamblin hq hw,
    fun h ↦ ⟨_, isStrongestTrueAnswer_hamblin hD (by simpa using h)⟩⟩

end Hamblin

/-! ### Distributive nuclei -/

section Distributive

open Set

variable {E : Type*} {D s T : Set E} {a b : E}

section Preorder

variable [Preorder E]

/-- The disjunction of the elements of a finite `T` is the strongest member of a Hamblin set
supported on a state `s` when `T` lies in the domain and in `s` and everything in `s` lies above
some element of `T`. -/
theorem isLeast_supported_hamblin (hT : T.Finite) (hne : T.Nonempty) (hTD : T ⊆ D) (hTs : T ⊆ s)
    (hs : s ⊆ ⋃ t ∈ T, Ici t) : IsLeast (supported (hamblin Ici D) s) (⋃ t ∈ T, Ici t) := by
  refine ⟨⟨.inr (Set.mem_supClosure_image.2 ⟨hT.toFinset, by simpa using hne, by simpa using hTD,
    by simp⟩), hs⟩, ?_⟩
  rintro q ⟨hq, hsq⟩
  obtain ⟨X, -, -, rfl | rfl⟩ := mem_hamblin.1 hq
  · exact iUnion₂_subset fun t ht ↦ subset_iInter₂ fun x hx ↦
      Ici_subset_Ici.2 (mem_iInter₂.1 (hsq (hTs ht)) x hx)
  · refine iUnion₂_subset fun t ht ↦ ?_
    obtain ⟨x, hx, hxt⟩ := mem_iUnion₂.1 (hsq (hTs ht))
    exact (Ici_subset_Ici.2 hxt).trans (subset_biUnion_of_mem hx)

theorem isLeast_supported_hamblin_pair (haD : a ∈ D) (hbD : b ∈ D) (has : a ∈ s) (hbs : b ∈ s)
    (hs : s ⊆ Ici a ∪ Ici b) : IsLeast (supported (hamblin Ici D) s) (Ici a ∪ Ici b) := by
  simpa using isLeast_supported_hamblin (T := {a, b}) (toFinite _) ⟨a, .inl rfl⟩
    (pair_subset haD hbD) (pair_subset has hbs) (by simpa using hs)

theorem presupposition_image_Ici (hD : IsUpperSet D) : presupposition (Ici '' D) = D := by
  refine Set.ext fun w ↦ ⟨fun h ↦ ?_, fun hw ↦ ⟨Ici w, ⟨⟨w, hw, rfl⟩, self_mem_Ici⟩, ?_⟩⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩, hxw⟩ := h.exists_mem
    exact hD hxw hx
  · rintro _ ⟨⟨x, -, rfl⟩, hxw⟩
    exact Ici_subset_Ici.2 hxw

theorem presupposition_hamblin_Ici (hfin : D.Finite) (hD : IsUpperSet D) :
    presupposition (hamblin Ici D) = D := by
  rw [presupposition_hamblin hfin]
  exact Set.ext fun w ↦ ⟨fun h ↦ let ⟨_, hx, hxw⟩ := mem_iUnion₂.1 h; hD hxw hx,
    fun hw ↦ mem_biUnion hw self_mem_Ici⟩

end Preorder

/-- Over individuals, a state with two disjoint elements supports no member: there is no one
individual below both. -/
theorem not_hasStrongestAnswerOn_image_Ici [PartialOrder E] [OrderBot E] (hD : ⊥ ∉ D)
    (hab : Disjoint a b) (has : a ∈ s) (hbs : b ∈ s) :
    ¬ HasStrongestAnswerOn (Ici '' D) s := by
  rintro ⟨_, ⟨⟨x, hx, rfl⟩, hxs⟩, -⟩
  exact hD (le_bot_iff.1 (hab (hxs has) (hxs hbs)) ▸ hx)

end Distributive

end Question
