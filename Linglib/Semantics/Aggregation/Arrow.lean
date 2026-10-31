module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Linarith
public import Linglib.Semantics.Aggregation.Basic

/-!
# Arrow's theorem

This file proves Arrow's theorem. With three or more alternatives, a rule on profiles of values
that is ordinally invariant, outputs weak orderings, respects weak Pareto and is independent of
irrelevant alternatives has a dictator, an individual whose strict rankings are the strict overall
rankings. Ordinal invariance makes the values carry no more than each individual's ranking, which
recovers Arrow's setting. The proof is by field expansion and group contraction: the whole
population is decisive, an almost decisive group is decisive for every pair, and a decisive group
with two or more members has a decisive proper subgroup.

## Main statements

* `Aggregation.exists_isDictator`: a rule meeting Arrow's conditions has a dictator.
* `Aggregation.arrow`: no rule meets all of Arrow's conditions.

## References

* [arrow-1950]
* [sen-1970]
-/

@[expose] public section

namespace Aggregation

variable {ι α K : Type*}

/-! ### Arrow's theorem -/

section Arrow

variable [LinearOrder K] {a : Rule ι α K}

/-- A group `G` is decisive when the rule ranks `x` strictly above `y` whenever every individual in
`G` does. -/
def Decisive (a : Rule ι α K) (G : Finset ι) : Prop :=
  ∀ v x y, (∀ i ∈ G, v y i < v x i) → AsymmRel (a v) x y

/-- A group `G` is decisive for the pair `x, y` when the rule ranks `x` strictly above `y` whenever
every individual in `G` does. -/
def DecisiveOn (a : Rule ι α K) (G : Finset ι) (x y : α) : Prop :=
  ∀ v, (∀ i ∈ G, v y i < v x i) → AsymmRel (a v) x y

/-- A group `G` is almost decisive for the pair `x, y` when it prevails if every individual outside
`G` ranks `y` strictly above `x`. -/
def AlmostDecisiveOn (a : Rule ι α K) (G : Finset ι) (x y : α) : Prop :=
  ∀ v, (∀ i ∈ G, v y i < v x i) → (∀ i ∉ G, v x i < v y i) → AsymmRel (a v) x y

theorem DecisiveOn.almost {G : Finset ι} {x y : α} (h : DecisiveOn a G x y) :
    AlmostDecisiveOn a G x y :=
  fun v hG _ ↦ h v hG

theorem decisive_of_decisiveOn {G : Finset ι} (hne : G.Nonempty)
    (h : ∀ x y, x ≠ y → DecisiveOn a G x y) : Decisive a G := by
  intro v x y hv
  rcases eq_or_ne x y with rfl | hxy
  · obtain ⟨i, hi⟩ := hne
    exact absurd (hv i hi) (lt_irrefl _)
  · exact h x y hxy v hv

variable [Field K] [IsStrictOrderedRing K]

theorem iff_of_pattern (hO : Invariant ordinal a) (hI : Independent a)
    {v w : Profile ι α K} {x y : α}
    (h : ∀ i, (v x i < v y i ↔ w x i < w y i) ∧ (v y i < v x i ↔ w y i < w x i)) :
    a v x y ↔ a w x y := by
  let f : Profile ι α K → ι → K → K := fun u i t ↦
    if u x i = u y i then t - u x i else (t - u x i) / |u y i - u x i|
  have hf : ∀ u, f u ∈ ordinal := fun u ↦ by
    intro i s t hst
    dsimp only [f]
    split_ifs with h
    · exact sub_lt_sub_right hst _
    · exact div_lt_div_of_pos_right (sub_lt_sub_right hst _)
        (abs_pos.2 (sub_ne_zero.2 (Ne.symm h)))
  have hx : ∀ u : Profile ι α K, Profile.transform (f u) u x = 0 := fun u ↦ funext fun i ↦ by
    simp only [Profile.transform, f]
    split_ifs <;> simp
  have hy : ∀ u : Profile ι α K, Profile.transform (f u) u y =
      fun i ↦ if u x i < u y i then 1 else if u y i < u x i then -1 else 0 := fun u ↦
    funext fun i ↦ by
      simp only [Profile.transform, f]
      rcases lt_trichotomy (u x i) (u y i) with hlt | heq | hgt
      · rw [ite_eq_right hlt.ne, ite_eq_left hlt, abs_of_pos (sub_pos.2 hlt),
          div_self (sub_pos.2 hlt).ne']
      · simp [heq]
      · rw [ite_eq_right hgt.ne', ite_eq_right (lt_asymm hgt), ite_eq_left hgt,
          abs_of_neg (sub_neg.2 hgt), div_neg, div_self (sub_neg.2 hgt).ne]
  have hyw : Profile.transform (f v) v y = Profile.transform (f w) w y := by
    rw [hy, hy]
    funext i
    simp only [(h i).1, (h i).2]
  calc a v x y ↔ a (v.transform (f v)) x y := by rw [hO (f v) (hf v) v]
    _ ↔ a (w.transform (f w)) x y := hI _ _ x y (by rw [hx, hx]) hyw
    _ ↔ a w x y := by rw [hO (f w) (hf w) w]

theorem decisiveOn_of_almost (hW : WeakOrderValued a) (hP : WeakPareto a) (hI : Independent a)
    {G : Finset ι} {x y : α} (hxy : x ≠ y) (h : AlmostDecisiveOn a G x y) {z : α}
    (hzy : z ≠ y) : DecisiveOn a G x z := by
  intro v hv
  classical
  let v' : Profile ι α K := fun w i ↦
    if w = y then (if i ∈ G then (v x i + v z i) / 2 else max (v x i) (v z i) + 1) else v w i
  have hx : v' x = v x := funext fun i ↦ by simp [v', hxy]
  have hz : v' z = v z := funext fun i ↦ by simp [v', hzy]
  have hG : ∀ i ∈ G, v' y i < v' x i := fun i hi ↦ by
    simp only [v', ite_true, ite_eq_right hxy, ite_eq_left hi]
    linarith [hv i hi]
  have hG' : ∀ i ∉ G, v' x i < v' y i := fun i hi ↦ by
    simp only [v', ite_true, ite_eq_right hxy, ite_eq_right hi]
    linarith [le_max_left (v x i) (v z i)]
  have hyz : ∀ i, v' z i < v' y i := fun i ↦ by
    by_cases hi : i ∈ G
    · simp only [v', ite_true, ite_eq_right hzy, ite_eq_left hi]
      linarith [hv i hi]
    · simp only [v', ite_true, ite_eq_right hzy, ite_eq_right hi]
      linarith [le_max_right (v x i) (v z i)]
  have := hW.1 v'
  have h₃ : AsymmRel (a v') x z := (h v' hG hG').trans_le (hP v' y z hyz).1
  exact ⟨(hI v' v x z hx hz).1 h₃.1, fun hzx' ↦ h₃.2 ((hI v' v z x hz hx).2 hzx')⟩

theorem decisiveOn_of_almost' (hW : WeakOrderValued a) (hP : WeakPareto a) (hI : Independent a)
    {G : Finset ι} {x y : α} (hxy : x ≠ y) (h : AlmostDecisiveOn a G x y) {z : α}
    (hzx : z ≠ x) : DecisiveOn a G z y := by
  intro v hv
  classical
  let v' : Profile ι α K := fun w i ↦
    if w = x then (if i ∈ G then (v z i + v y i) / 2 else min (v z i) (v y i) - 1) else v w i
  have hz : v' z = v z := funext fun i ↦ by simp [v', hzx]
  have hy : v' y = v y := funext fun i ↦ by simp [v', hxy.symm]
  have hzx' : ∀ i, v' x i < v' z i := fun i ↦ by
    by_cases hi : i ∈ G
    · simp only [v', ite_true, ite_eq_right hzx, ite_eq_left hi]
      linarith [hv i hi]
    · simp only [v', ite_true, ite_eq_right hzx, ite_eq_right hi]
      linarith [min_le_left (v z i) (v y i)]
  have hG : ∀ i ∈ G, v' y i < v' x i := fun i hi ↦ by
    simp only [v', ite_true, ite_eq_right hxy.symm, ite_eq_left hi]
    linarith [hv i hi]
  have hG' : ∀ i ∉ G, v' x i < v' y i := fun i hi ↦ by
    simp only [v', ite_true, ite_eq_right hxy.symm, ite_eq_right hi]
    linarith [min_le_right (v z i) (v y i)]
  have := hW.1 v'
  have h₃ : AsymmRel (a v') z y := (hP v' z x hzx').trans_le (h v' hG hG').1
  exact ⟨(hI v' v z y hz hy).1 h₃.1, fun hyz ↦ h₃.2 ((hI v' v y z hy hz).2 hyz)⟩

variable [Fintype α]

theorem decisiveOn_of_almost_of_ne (hW : WeakOrderValued a) (hP : WeakPareto a)
    (hI : Independent a) (h₃ : 3 ≤ Fintype.card α) {G : Finset ι} {x y : α} (hxy : x ≠ y)
    (h : AlmostDecisiveOn a G x y) {u w : α} (huw : u ≠ w) : DecisiveOn a G u w := by
  have A : ∀ p q, p ≠ q → AlmostDecisiveOn a G p q → ∀ r, r ≠ p → r ≠ q →
      DecisiveOn a G p r ∧ DecisiveOn a G r q :=
    fun p q hpq hpq' r hrp hrq ↦
      ⟨decisiveOn_of_almost hW hP hI hpq hpq' hrq, decisiveOn_of_almost' hW hP hI hpq hpq' hrp⟩
  obtain ⟨z, hzx, hzy⟩ : ∃ z, z ≠ x ∧ z ≠ y := by
    by_contra hz
    push Not at hz
    classical
    have hsub : (Finset.univ : Finset α) ⊆ {x, y} := fun z _ ↦ by
      rcases eq_or_ne z x with rfl | hzx
      · simp
      · simp [hz z hzx]
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    simp only [Finset.card_univ, Finset.card_singleton] at this
    omega
  have hxz : DecisiveOn a G x z := (A x y hxy h z hzx hzy).1
  have hzy' : DecisiveOn a G z y := (A x y hxy h z hzx hzy).2
  have hxy' : DecisiveOn a G x y := (A x z hzx.symm hxz.almost y hxy.symm hzy.symm).1
  have hyz : DecisiveOn a G y z := (A x z hzx.symm hxz.almost y hxy.symm hzy.symm).2
  have hzx' : DecisiveOn a G z x := (A z y hzy hzy'.almost x hzx.symm hxy).1
  have key : ∀ u, ∃ q, q ≠ u ∧ DecisiveOn a G u q := fun u ↦ by
    rcases eq_or_ne u x with rfl | hux
    · exact ⟨y, hxy.symm, hxy'⟩
    rcases eq_or_ne u y with rfl | huy
    · exact ⟨z, hzy, hyz⟩
    rcases eq_or_ne u z with rfl | huz
    · exact ⟨x, hzx.symm, hzx'⟩
    · exact ⟨y, huy.symm, (A x y hxy h u hux huy).2⟩
  obtain ⟨q, hqu, hq⟩ := key u
  rcases eq_or_ne w q with rfl | hwq
  · exact hq
  · exact (A u q hqu.symm hq.almost w huw.symm hwq).1

theorem exists_decisive_ssubset (hO : Invariant ordinal a) (hW : WeakOrderValued a)
    (hP : WeakPareto a) (hI : Independent a) (h₃ : 3 ≤ Fintype.card α) {G : Finset ι}
    (hG : Decisive a G) (h₂ : 2 ≤ G.card) : ∃ G' ⊂ G, Decisive a G' := by
  classical
  obtain ⟨i, hi⟩ : G.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := (Fintype.two_lt_card_iff (α := α)).1 (by omega)
  let v : Profile ι α K := fun w j ↦
    if j = i then (if w = x then 2 else if w = y then 1 else 0)
    else if j ∈ G then (if w = y then 2 else if w = z then 1 else 0)
    else (if w = z then 2 else if w = x then 1 else 0)
  have hv : ∀ j, (v x j < v z j ↔ j ≠ i) ∧ (v z j < v x j ↔ j = i) ∧
      (v y j < v x j ↔ j ∉ G ∨ j = i) ∧ (v x j < v y j ↔ j ∈ G ∧ j ≠ i) := fun j ↦ by
    by_cases hji : j = i
    · subst hji
      simp [v, hxy.symm, hxz.symm, hyz.symm, hi]
    · by_cases hj : j ∈ G <;> simp [v, hji, hj, hxy, hxz, hyz, hxy.symm, hyz.symm]
  have hyz' : AsymmRel (a v) y z := hG v y z fun j hj ↦ by
    by_cases hji : j = i
    · subst hji; simp [v, hxz.symm, hxy.symm, hyz.symm]
    · simp [v, hji, hj, hyz.symm]
  have := hW.1 v
  by_cases hxz' : AsymmRel (a v) x z
  · refine ⟨{i}, Finset.ssubset_iff_subset_ne.2 ⟨Finset.singleton_subset_iff.2 hi, ?_⟩, ?_⟩
    · rintro rfl
      simp at h₂
    · refine decisive_of_decisiveOn ⟨i, Finset.mem_singleton_self i⟩ fun p q hpq ↦
        decisiveOn_of_almost_of_ne hW hP hI h₃ hxz ?_ hpq
      intro u hu hu'
      have hpat : ∀ j, (u x j < u z j ↔ v x j < v z j) ∧ (u z j < u x j ↔ v z j < v x j) := by
        intro j
        rw [(hv j).1, (hv j).2.1]
        rcases eq_or_ne j i with rfl | hji
        · have := hu j (Finset.mem_singleton_self j)
          exact ⟨⟨fun h ↦ absurd h (lt_asymm this), fun h ↦ absurd rfl h⟩,
            ⟨fun _ ↦ rfl, fun _ ↦ this⟩⟩
        · have := hu' j (by simpa using hji)
          exact ⟨⟨fun _ ↦ hji, fun _ ↦ this⟩,
            ⟨fun h ↦ absurd h (lt_asymm this), fun h ↦ absurd h hji⟩⟩
      exact ⟨(iff_of_pattern hO hI hpat).2 hxz'.1,
        fun h' ↦ hxz'.2 ((iff_of_pattern hO hI fun j ↦ ⟨(hpat j).2, (hpat j).1⟩).1 h')⟩
  · have hzx : a v z x := by
      by_contra hzx
      exact hxz' ⟨((hW.2 v).total x z).resolve_right hzx, hzx⟩
    have hyx : AsymmRel (a v) y x := hyz'.trans_le hzx
    refine ⟨G.erase i, Finset.erase_ssubset hi, ?_⟩
    have hne : (G.erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hi]; omega
    refine decisive_of_decisiveOn hne fun p q hpq ↦
      decisiveOn_of_almost_of_ne hW hP hI h₃ hxy.symm ?_ hpq
    intro u hu hu'
    have hpat : ∀ j, (u y j < u x j ↔ v y j < v x j) ∧ (u x j < u y j ↔ v x j < v y j) := by
      intro j
      rw [(hv j).2.2.1, (hv j).2.2.2]
      by_cases hj : j ∈ G.erase i
      · have := hu j hj
        rw [Finset.mem_erase] at hj
        exact ⟨⟨fun h ↦ absurd h (lt_asymm this),
            fun h ↦ absurd (h.resolve_right hj.1) (fun h' ↦ h' hj.2)⟩,
          ⟨fun _ ↦ ⟨hj.2, hj.1⟩, fun _ ↦ this⟩⟩
      · have := hu' j hj
        rw [Finset.mem_erase, not_and_or, not_not] at hj
        exact ⟨⟨fun _ ↦ hj.symm, fun _ ↦ this⟩,
          ⟨fun h ↦ absurd h (lt_asymm this),
            fun h ↦ absurd h (fun h' ↦ hj.elim (fun e ↦ h'.2 e) (fun e ↦ e h'.1))⟩⟩
    exact ⟨(iff_of_pattern hO hI hpat).2 hyx.1,
      fun h' ↦ hyx.2 ((iff_of_pattern hO hI fun j ↦ ⟨(hpat j).2, (hpat j).1⟩).1 h')⟩

variable [Fintype ι]

/-- Arrow's theorem says that with three or more alternatives a rule that is ordinally invariant,
outputs weak orderings, respects weak Pareto and is independent has a dictator. -/
theorem exists_isDictator (hO : Invariant ordinal a) (hW : WeakOrderValued a)
    (hP : WeakPareto a) (hI : Independent a) (h₃ : 3 ≤ Fintype.card α) :
    ∃ i, IsDictator a i := by
  classical
  obtain ⟨x⟩ := Fintype.card_pos_iff.1 (show 0 < Fintype.card α by omega)
  have huniv : Decisive a Finset.univ := fun v p q h ↦ hP v p q fun i ↦ h i (Finset.mem_univ i)
  obtain ⟨G, hG, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset ι)).filter (Decisive a)) Finset.card ⟨_, by simpa using huniv⟩
  rw [Finset.mem_filter] at hG
  have hne : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have := hG.2 (fun _ _ ↦ 0) x x (by simp)
    exact this.2 this.1
  have hcard : G.card = 1 := by
    by_contra h
    obtain ⟨G', hG', hdec⟩ := exists_decisive_ssubset hO hW hP hI h₃ hG.2
      (by have := hne.card_pos; omega)
    have := hmin G' (by simpa using hdec)
    exact absurd (Finset.card_lt_card hG') (not_lt.2 this)
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hcard
  exact ⟨i, fun v p q h ↦ hG.2 v p q fun j hj ↦ (Finset.mem_singleton.1 hj) ▸ h⟩

/-- Arrow's theorem is an impossibility, since no rule meets all of Arrow's conditions. -/
theorem arrow (h₃ : 3 ≤ Fintype.card α) (a : Rule ι α K) :
    ¬ (Invariant ordinal a ∧ WeakOrderValued a ∧ WeakPareto a ∧ Independent a ∧
      NonDictatorial a) :=
  fun ⟨hO, hW, hP, hI, hD⟩ ↦ let ⟨i, hi⟩ := exists_isDictator hO hW hP hI h₃; hD i hi

end Arrow

end Aggregation
