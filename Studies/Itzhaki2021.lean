module

public import Linglib.Core.Algebra.Order.Archimedean.Class
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Semantics.Degree.Comparison
public import Mathlib.Algebra.Order.Ring.StandardPart
public import Mathlib.Analysis.Real.Hyperreal

/-!
# Itzhaki (2021): Qualitative versus Quantitative Representation: A Non-Standard Analysis of the Sorites Paradox

Itzhaki traces the Sorites paradox to the conflation of two maps from individuals to degrees. A
quantitative map sends a pile to its number of grains and a person to their height, in an
Archimedean scale; a qualitative map sends piles and changes into the hyperreals. A heap gets an
infinite qualitative size, so that adding or removing a grain never crosses between heaps and
non-heaps, and a change of one millimetre gets an infinitesimal qualitative magnitude, so that the
standard part of a height ignores it. The premises of each Sorites are then jointly satisfiable
under the qualitative map and inconsistent under the quantitative one, and the conclusion of the
argument follows from its premises only when the inverse of the size map is total.

A soritical argument is one schema, `Sorites`: a base case, tolerance along a step relation, and
a counterexample. The classic and the reverse paradox of the heap are its instances along steps of
one grain, read through either size map.

## Main statements

* `Itzhaki2021.Sorites.conclusion`, `Itzhaki2021.Sorites.false_of_total`: the conclusion of a
  Sorites follows from its premises when the inverse of the size map is total, and the premises are
  then inconsistent.
* `Itzhaki2021.sorites_not_heap`, `Itzhaki2021.sorites_heap`: under the qualitative size, the
  classic and the reverse paradox of the heap hold for any heap predicate with a heap and a
  non-heap, while under the quantitative size of the model they are inconsistent
  (`Itzhaki2021.Model55.not_sorites_size`).
* `Itzhaki2021.induction_premise`, `Itzhaki2021.conclusion_tall`,
  `Itzhaki2021.not_forall_sub_natCast_ge`: with an infinitesimal unit of change the premises of the
  tall paradox hold, and with the quantitative unit its conclusion fails.
* `Itzhaki2021.instIsTransInfinitelyLess`, `Itzhaki2021.merged_iff`,
  `Itzhaki2021.not_merged_qualSize`: being infinitely less is transitive, and the merged paradox
  of the small heap is satisfiable exactly when the qualitative sizes of its two heaps are
  infinitely apart, which the qualitative size of the heap paradox never makes them.

## Implementation notes

* The finite and the infinitesimal hyperreals are mathlib's subgroups of archimedean classes at
  least and above that of `1`, and the standard part is mathlib's `stdPart`.
* Whether the size of a heap is known is a parameter of the qualitative size; no result depends on
  it.
* The pluralities of the heap model are their sizes, as the paper reduces them (fn. 23), and the
  individuals of the tall model their heights in millimetres.
* As printed, (9d) claims that an infinite number times a nonzero finite one is infinite, which
  `ω * ε = 1` refutes (`not_forall_mk_mul_neg`), and (80) is unsatisfiable under the qualitative
  size (36) (`not_merged_qualSize`).

## References

* [itzhaki-2021]
* [kennedy-2007]
* [link-1983]
* [williamson-1994]
-/

@[expose] public section

namespace Itzhaki2021

open ArchimedeanClass Hyperreal Relation

/-! ### Finite, infinitesimal and infinite hyperreals -/

/-- The infinitesimal hyperreals, those of archimedean class above that of `1` (7b). -/
noncomputable abbrev infinitesimals : AddSubgroup ℝ* := ballAddSubgroup 0

/-- The finite hyperreals, those of archimedean class at least that of `1` (7a). -/
noncomputable abbrev finites : AddSubgroup ℝ* := closedBallAddSubgroup 0

theorem mem_infinitesimals {a : ℝ*} : a ∈ infinitesimals ↔ 0 < mk a :=
  mem_ballAddSubgroup_iff (by simp)

theorem mem_finites {a : ℝ*} : a ∈ finites ↔ 0 ≤ mk a := mem_closedBallAddSubgroup_iff

/-- `a` is indistinguishable from `b` when their difference is infinitesimal (10). -/
def InfinitesimallyClose (a b : ℝ*) : Prop := a - b ∈ infinitesimals

/-- `a` and `b` are finitely close when their difference is finite (74). -/
def FinitelyClose (a b : ℝ*) : Prop := a - b ∈ finites

/-- `a` is infinitely less than `b` when it is less and not finitely close (78). -/
def InfinitelyLess (a b : ℝ*) : Prop := a < b ∧ ¬ FinitelyClose a b

/-- Being indistinguishable is an equivalence relation (11). -/
instance : IsEquiv ℝ* InfinitesimallyClose where
  refl _ := by simp [InfinitesimallyClose]
  symm _ _ h := by simpa [InfinitesimallyClose] using infinitesimals.neg_mem h
  trans _ _ _ h₁ h₂ := by simpa [InfinitesimallyClose] using infinitesimals.add_mem h₁ h₂

theorem FinitelyClose.refl (a : ℝ*) : FinitelyClose a a := by simp [FinitelyClose]

@[grind →]
theorem FinitelyClose.symm {a b : ℝ*} (h : FinitelyClose a b) : FinitelyClose b a := by
  have := finites.neg_mem h
  rwa [neg_sub] at this

theorem FinitelyClose.trans {a b c : ℝ*} (h₁ : FinitelyClose a b) (h₂ : FinitelyClose b c) :
    FinitelyClose a c := by
  have := finites.add_mem h₁ h₂
  rwa [sub_add_sub_cancel] at this

/-- Being finitely close is an equivalence relation (fn. 31). -/
instance : IsEquiv ℝ* FinitelyClose where
  refl := FinitelyClose.refl
  symm _ _ := FinitelyClose.symm
  trans _ _ _ := FinitelyClose.trans

/-- Distinct reals are distinguishable (14), so a taller person's height is never
indistinguishable from a shorter one's (67). -/
theorem not_infinitesimallyClose_coe {r s : ℝ} (h : r ≠ s) :
    ¬ InfinitesimallyClose (r : ℝ*) s := by
  rw [InfinitesimallyClose, mem_infinitesimals, ← coe_sub, archimedeanClassMk_coe (sub_ne_zero.2 h)]
  exact lt_irrefl 0

/-- The standard part of a real minus an infinitesimal is the real (22). -/
theorem stdPart_sub_infinitesimal (r : ℝ) {e : ℝ*} (he : e ∈ infinitesimals) :
    stdPart ((r : ℝ*) - e) = r := by
  rw [stdPart_sub_eq_left (mem_infinitesimals.1 he), stdPart_coe]

/-- An infinite number times a nonzero finite one need not be infinite, against (9d) as
printed. -/
theorem not_forall_mk_mul_neg :
    ¬ ∀ H a : ℝ*, mk H < 0 → a ≠ 0 → 0 ≤ mk a → mk (H * a) < 0 := fun h ↦ by
  have := h ω ε archimedeanClassMk_omega_neg epsilon_ne_zero archimedeanClassMk_epsilon_pos.le
  rw [mul_comm, epsilon_mul_omega] at this
  simp at this

/-- Every finite number is a difference of two infinite ones (§2.2.2). -/
theorem exists_sub_of_mk_nonneg {a : ℝ*} (ha : 0 ≤ mk a) :
    ∃ G H : ℝ*, mk G < 0 ∧ mk H < 0 ∧ a = G - H :=
  ⟨a + ω, ω, by
    rw [add_comm, mk_add_eq_mk_left (archimedeanClassMk_omega_neg.trans_le ha)]
    exact archimedeanClassMk_omega_neg, archimedeanClassMk_omega_neg, by ring⟩

/-- Adding a natural number keeps a number finite (38a). -/
theorem mk_add_natCast_nonneg {a : ℝ*} (ha : 0 ≤ mk a) (n : ℕ) : 0 ≤ mk (a + n) :=
  (le_min ha (mk_natCast_nonneg n)).trans (min_le_mk_add a n)

/-- Subtracting a natural number keeps a number infinite (38b). -/
theorem mk_sub_natCast_neg {a : ℝ*} (ha : mk a < 0) (n : ℕ) : mk (a - n) < 0 := by
  rw [sub_eq_add_neg, mk_add_eq_mk_left (by rw [mk_neg]; exact ha.trans_le (mk_natCast_nonneg n))]
  exact ha

/-! ### The soritical argument -/

/-- A soritical argument has a base case `a` with `P`, tolerance of `P` along `R`, and a
counterexample `b` without `P`, premises I, II and IV of (1) and (2). -/
structure Sorites {α : Type*} (P : α → Prop) (R : α → α → Prop) (a b : α) : Prop where
  base : P a
  tolerance : ∀ ⦃x y⦄, P x → R x y → P y
  counter : ¬ P b

variable {α : Type*} {P : α → Prop} {R : α → α → Prop} {a b : α}

theorem Sorites.not_reflTransGen (h : Sorites P R a b) : ¬ ReflTransGen R a b := fun hab ↦
  let ⟨_, _, hcd, hc, hd, _⟩ := hab.exists_boundary (S := {x | P x}) h.base h.counter
  hd (h.tolerance hc hcd)

theorem Sorites.of_reflTransGen (h : Sorites P R a b) {y : α} (hy : ReflTransGen R a y) : P y :=
  by_contra fun hn ↦ (Sorites.mk h.base h.tolerance hn).not_reflTransGen hy

/-- `y` is one step `d` above `x` along the size map `s`. -/
def Step (s : α → ℝ*) (d : ℝ*) (x y : α) : Prop := s y = s x + d

variable {s : α → ℝ*} {d : ℝ*}

/-- The conclusion of a Sorites (52.III) follows from its premises when every intermediate value
is the size of some individual, the totality of the inverse of the size map (44)–(46). -/
theorem Sorites.conclusion (h : Sorites P (Step s d) a b) (hs : Function.Injective s) :
    ∀ n : ℕ, (∀ m < n, ∃ x, s x = s a + m * d) → ∀ y, s y = s a + n * d → P y := by
  intro n
  induction n with
  | zero => intro _ y hy; rw [Nat.cast_zero, zero_mul, add_zero] at hy; exact hs hy ▸ h.base
  | succ n ih =>
    intro htot y hy
    obtain ⟨x, hx⟩ := htot n (Nat.lt_succ_self n)
    refine h.tolerance (ih (fun m hm ↦ htot m (hm.trans (Nat.lt_succ_self n))) x hx) ?_
    unfold Step
    rw [hy, hx]
    push_cast
    ring

/-- When the inverse of the size map is total and `b` is reached arithmetically from `a`, the
premises of a Sorites are inconsistent. -/
theorem Sorites.false_of_total (h : Sorites P (Step s d) a b) (hs : Function.Injective s)
    (n : ℕ) (htot : ∀ m < n, ∃ x, s x = s a + m * d) (hb : s b = s a + n * d) : False :=
  h.counter (h.conclusion hs n htot b hb)

/-! ### Collective nouns -/

section Heap

variable {De : Type*} (heap known : De → Prop) [DecidablePred heap] [DecidablePred known]
  (size : De → ℕ) (H : ℝ*)

/-- The qualitative size (36) maps a heap of known size to `H` plus its size, a heap of unknown
size to `H`, and anything else to its size. -/
noncomputable def qualSize (x : De) : ℝ* :=
  if heap x then (if known x then H + size x else H) else size x

variable {heap known size H} {x y : De}

theorem qualSize_of_not_heap (hx : ¬ heap x) : qualSize heap known size H x = size x := by
  simp [qualSize, hx]

/-- What is not a heap has finite qualitative size (37a). -/
theorem mk_qualSize_nonneg (hx : ¬ heap x) : 0 ≤ mk (qualSize heap known size H x) := by
  rw [qualSize_of_not_heap hx]
  exact mk_natCast_nonneg _

/-- A heap has infinite qualitative size when `H` is infinite (37b). -/
theorem mk_qualSize_neg (hH : mk H < 0) (hx : heap x) :
    mk (qualSize heap known size H x) < 0 := by
  unfold qualSize
  split_ifs
  · exact (mk_add_eq_mk_left (hH.trans_le (mk_natCast_nonneg _))).symm ▸ hH
  · exact hH

/-- A heap's qualitative size exceeds every natural number when `H` is positive and infinite
(37b). -/
theorem natCast_lt_qualSize (hH : mk H < 0) (hpos : 0 < H) (hx : heap x) (n : ℕ) :
    (n : ℝ*) < qualSize heap known size H x := by
  have hn : (n : ℝ*) < H := by
    have := (mk_lt_mk.1 (hH.trans_eq mk_one.symm)) n
    rwa [abs_one, nsmul_one, abs_of_pos hpos] at this
  unfold qualSize
  split_ifs
  · exact hn.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · exact hn

theorem finitelyClose_qualSize (hx : heap x) (hy : heap y) :
    FinitelyClose (qualSize heap known size H x) (qualSize heap known size H y) := by
  have hn (n : ℕ) : (n : ℝ*) ∈ finites := mem_finites.2 (mk_natCast_nonneg n)
  unfold FinitelyClose qualSize
  split_ifs <;> simp only [add_sub_add_left_eq_sub, add_sub_cancel_left, sub_add_cancel_left,
    sub_self, finites.zero_mem, finites.sub_mem (hn _) (hn _), finites.neg_mem (hn _), hn]

/-- Under the qualitative size, a non-heap and a heap make the classic paradox of the heap
consistent (52), since adding a grain to a non-heap never yields a heap (38a). -/
theorem sorites_not_heap (hH : mk H < 0) {g₁ g : De} (h₁ : ¬ heap g₁) (hg : heap g) :
    Sorites (¬ heap ·) (Step (qualSize heap known size H) 1) g₁ g where
  base := h₁
  tolerance x y hx hxy hy := by
    have := mk_qualSize_neg (known := known) (size := size) hH hy
    rw [hxy, ← Nat.cast_one] at this
    exact (this.trans_le (mk_add_natCast_nonneg (mk_qualSize_nonneg hx) 1)).false
  counter := not_not.2 hg

/-- Under the qualitative size, the reverse paradox of the heap is consistent too (54), since
removing a grain from a heap never yields a non-heap (38b). -/
theorem sorites_heap (hH : mk H < 0) {g₁ g : De} (h₁ : ¬ heap g₁) (hg : heap g) :
    Sorites heap (Step (qualSize heap known size H) (-1)) g g₁ where
  base := hg
  tolerance x y hx hxy := by
    by_contra hy
    have := mk_qualSize_nonneg (known := known) (size := size) (H := H) hy
    rw [hxy, ← sub_eq_add_neg, ← Nat.cast_one] at this
    exact (mk_sub_natCast_neg (mk_qualSize_neg hH hx) 1).not_ge this
  counter := h₁

/-- The size of a heap is nobody's qualitative size (47a). -/
theorem natCast_size_notMem_range (hH : mk H < 0) (hs : Function.Injective size)
    (hx : heap x) : (size x : ℝ*) ∉ Set.range (qualSize heap known size H) := fun ⟨y, hy⟩ ↦ by
  by_cases hy' : heap y
  · exact ((mk_qualSize_neg (known := known) (size := size) hH hy').trans_le
      (hy ▸ mk_natCast_nonneg _)).false
  · rw [qualSize_of_not_heap hy', Nat.cast_inj] at hy
    exact hy' (hs hy ▸ hx)

/-- `H` plus the size of a non-heap is nobody's qualitative size (47b). -/
theorem add_natCast_size_notMem_range (hH : mk H < 0) (hs : Function.Injective size)
    (hx : ¬ heap x) (hpos : 0 < size x) :
    H + size x ∉ Set.range (qualSize heap known size H) := fun ⟨y, hy⟩ ↦ by
  by_cases hy' : heap y
  · unfold qualSize at hy
    simp only [hy', ite_true] at hy
    split_ifs at hy
    · exact hx (hs (Nat.cast_injective (add_left_cancel hy)) ▸ hy')
    · exact hpos.ne' (Nat.cast_eq_zero.1 (add_eq_left.1 hy.symm))
  · rw [qualSize_of_not_heap hy'] at hy
    have := mk_natCast_nonneg (S := ℝ*) (size y)
    rw [hy, mk_add_eq_mk_left (hH.trans_le (mk_natCast_nonneg _))] at this
    exact this.not_gt hH

end Heap

/-! ### The model of the heap -/

namespace Model55

/-- The pluralities of `1` to `10,000` grains, one of each size. -/
abbrev De := Set.Icc (1 : ℕ) 10000

/-- Only the plurality of `10,000` grains is a heap. -/
def heap (x : De) : Prop := x.1 = 10000

instance : DecidablePred heap := fun x ↦ inferInstanceAs (Decidable (x.1 = 10000))

/-- One grain. -/
def g₁ : De := ⟨1, by simp⟩

/-- `10,000` grains. -/
def g₁₀₀₀₀ : De := ⟨10000, by simp⟩

/-- The qualitative size of the model, every size known and `H = ω`. -/
noncomputable abbrev qs : De → ℝ* := qualSize heap (fun _ ↦ True) Subtype.val ω

example : qs g₁ = 1 ∧ qs g₁₀₀₀₀ = ω + 10000 := by
  simp [qs, qualSize, heap, g₁, g₁₀₀₀₀]

/-- The classic paradox of the heap holds of the qualitative size (52). -/
theorem sorites_qs : Sorites (¬ heap ·) (Step qs 1) g₁ g₁₀₀₀₀ :=
  sorites_not_heap archimedeanClassMk_omega_neg (by simp [heap, g₁]) rfl

/-- The reverse paradox holds of the qualitative size (54). -/
theorem sorites_qs_reverse : Sorites heap (Step qs (-1)) g₁₀₀₀₀ g₁ :=
  sorites_heap archimedeanClassMk_omega_neg (by simp [heap, g₁]) rfl

/-- Under the quantitative size, the premises of the classic paradox are inconsistent. -/
theorem not_sorites_size : ¬ Sorites (¬ heap ·) (Step (fun x : De ↦ (x.1 : ℝ*)) 1) g₁ g₁₀₀₀₀ :=
  fun h ↦ h.false_of_total (fun _ _ e ↦ Subtype.ext (by simpa using e)) 9999
    (fun m hm ↦ ⟨⟨m + 1, by simp, by omega⟩, by simp [g₁]; ring⟩) (by simp [g₁₀₀₀₀, g₁]; norm_num)

/-- The quantitative size of a heap is nobody's qualitative size (49a). -/
example : ¬ ∃ y, qs y = qs g₁ + 9999 := fun ⟨y, hy⟩ ↦
  natCast_size_notMem_range (heap := heap) (known := fun _ ↦ True) (size := Subtype.val)
    (H := ω) (x := g₁₀₀₀₀) archimedeanClassMk_omega_neg Subtype.val_injective rfl
    ⟨y, hy.trans (by simp [qs, qualSize, heap, g₁, g₁₀₀₀₀]; norm_num)⟩

end Model55

/-! ### Gradable adjectives -/

/-- The qualitative magnitude (62) of a change `r` is an infinitesimal `e` when `r` is below the
smallest contextually relevant unit `U`, and `r` otherwise. -/
noncomputable def qualUnit (U : ℝ) (e : ℝ*) (r : ℝ) : ℝ* := if r < U then e else r

/-- A positive unit of change whose every multiple stays below a real bound is infinitesimal
(61). -/
theorem mem_infinitesimals_of_forall_mul_le {u : ℝ*} {c : ℝ} (hu : 0 < u)
    (h : ∀ n : ℕ, (n : ℝ*) * u ≤ c) : u ∈ infinitesimals := by
  rw [mem_infinitesimals, ← mk_one, mk_lt_mk]
  intro n
  by_contra hn
  rw [not_lt, abs_one, abs_of_pos hu, nsmul_eq_mul] at hn
  obtain ⟨m, hm⟩ := exists_nat_gt c
  have h2 : (m : ℝ*) ≤ (n * m : ℕ) * u := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ*) m]
  have h3 : ((c : ℝ) : ℝ*) < (m : ℝ*) := by
    rw [show (m : ℝ*) = ((m : ℝ) : ℝ*) by norm_cast]
    exact coe_lt_coe.2 hm
  exact (h3.trans_le h2).not_ge (h (n * m))

variable {E : Type*} {tall : E → ℝ} {S U : ℝ} {e : ℝ*}

/-- With a millimetre below the relevant unit, the induction premise (63) holds, since the
standard part of the height of anyone tall, less the qualitative millimetre, still meets the
standard. -/
theorem induction_premise (he : e ∈ infinitesimals) (hU : 1 < U) {x : E}
    (hx : x ∈ tall ⁻¹' Set.Ici S) :
    S ≤ stdPart ((tall x : ℝ*) - qualUnit U e 1) := by
  rw [show qualUnit U e 1 = e by simp [qualUnit, hU], stdPart_sub_infinitesimal _ he]
  exact hx

/-- With a millimetre below the relevant unit, the conclusion (70.III) holds, since any number
of qualitative millimetres below two metres is still tall. -/
theorem conclusion_tall (he : e ∈ infinitesimals) (hU : 1 < U) (hS : S ≤ 2000) (n : ℕ) :
    S ≤ stdPart ((2000 : ℝ*) - n * qualUnit U e 1) := by
  have hne : (n : ℝ*) * e ∈ infinitesimals := by
    rw [← nsmul_eq_mul]
    exact infinitesimals.nsmul_mem he n
  rw [show qualUnit U e 1 = e by simp [qualUnit, hU],
    show (2000 : ℝ*) = ((2000 : ℝ) : ℝ*) by norm_num, stdPart_sub_infinitesimal _ hne]
  exact hS

/-- With the quantitative unit, the conclusion of the tall paradox fails for any standard above
one metre (66). -/
theorem not_forall_sub_natCast_ge (hU : U ≤ 1) (hS : 1000 < S) :
    ¬ ∀ n : ℕ, S ≤ stdPart ((2000 : ℝ*) - n * qualUnit U e 1) := fun h ↦ by
  have := h 1000
  norm_num [qualUnit, not_lt.2 hU, stdPart_ofNat] at this
  linarith

/-- In the model (71), heights run in millimetres, the standard is `1800` and the smallest
relevant unit `2`; two metres is tall, one metre is not, and the induction premise and the
conclusion hold. -/
example : (2000 : ℕ) ∈ (fun i : ℕ ↦ (i : ℝ)) ⁻¹' Set.Ici 1800 ∧
    (1000 : ℕ) ∉ (fun i : ℕ ↦ (i : ℝ)) ⁻¹' Set.Ici 1800 ∧
    (∀ x ∈ (fun i : ℕ ↦ (i : ℝ)) ⁻¹' Set.Ici 1800,
      1800 ≤ stdPart (((x : ℝ) : ℝ*) - qualUnit 2 ε 1)) ∧
    ∀ n : ℕ, 1800 ≤ stdPart ((2000 : ℝ*) - n * qualUnit 2 ε 1) := by
  have he : ε ∈ infinitesimals := mem_infinitesimals.2 archimedeanClassMk_epsilon_pos
  refine ⟨by norm_num, by norm_num, fun x hx ↦ induction_premise he (by norm_num) hx,
    conclusion_tall he (by norm_num) (by norm_num)⟩

/-! ### The merged paradox -/

/-- `a` is at most `b` up to a finite difference when they are finitely close or `a` is
infinitely less (79). -/
def LeUpToFinite (a b : ℝ*) : Prop := FinitelyClose a b ∨ InfinitelyLess a b

/-- Being infinitely less is transitive (78). -/
instance instIsTransInfinitelyLess : IsTrans ℝ* InfinitelyLess where
  trans a b c hab hbc := by
    refine ⟨hab.1.trans hbc.1, fun hac ↦ hab.2 ?_⟩
    have hca : c - a ∈ finites := by simpa using finites.neg_mem hac
    have hba : b - a ∈ finites := (ordConnected_closedBallAddSubgroup 0).out finites.zero_mem hca
      ⟨sub_nonneg.2 hab.1.le, sub_le_sub_right hbc.1.le a⟩
    exact FinitelyClose.symm hba

theorem InfinitelyLess.of_finitelyClose {a b c : ℝ*} (hab : FinitelyClose a b)
    (hbc : InfinitelyLess b c) : InfinitelyLess a c := by
  refine ⟨lt_of_not_ge fun hca ↦ hbc.2 ?_, fun hac ↦ hbc.2 (hab.symm.trans hac)⟩
  have : c - b ∈ finites := (ordConnected_closedBallAddSubgroup 0).out finites.zero_mem hab
    ⟨(sub_pos.2 hbc.1).le, by linarith⟩
  exact FinitelyClose.symm this

theorem leUpToFinite_iff_not_infinitelyLess {a b : ℝ*} :
    LeUpToFinite a b ↔ ¬ InfinitelyLess b a := by
  unfold LeUpToFinite InfinitelyLess
  grind [FinitelyClose.refl]

theorem LeUpToFinite.add_one {a S : ℝ*} (h : LeUpToFinite a S) : LeUpToFinite (a + 1) S := by
  have h1 : (1 : ℝ*) ∈ finites := mem_finites.2 (by simp)
  rcases h with h | ⟨hlt, hn⟩
  · refine .inl ?_
    have := finites.add_mem h h1
    rwa [sub_add_eq_add_sub] at this
  · by_cases hf : FinitelyClose (a + 1) S
    · exact .inl hf
    refine .inr ⟨lt_of_not_ge fun hle ↦ hn ?_, hf⟩
    have : S - a ∈ finites := (ordConnected_closedBallAddSubgroup 0).out finites.zero_mem h1
      ⟨(sub_pos.2 hlt).le, by linarith⟩
    simpa [FinitelyClose] using finites.neg_mem this

/-- Of two heaps whose qualitative sizes are ordered, the larger is either finitely close or
infinitely larger, never both (81). -/
theorem finitelyClose_or_infinitelyLess {a b : ℝ*} (h : a < b) :
    FinitelyClose a b ∨ InfinitelyLess a b :=
  (em _).imp_right (⟨h, ·⟩)

/-- The merged paradox (80) has a standard of size making it consistent exactly when the
qualitative sizes of its small heap and its large heap are infinitely apart. -/
theorem merged_iff {De : Type*} {s : De → ℝ*} {g₅₀ g : De} :
    (∃ S, Sorites (fun x ↦ LeUpToFinite (s x) S) (Step s 1) g₅₀ g) ↔
      InfinitelyLess (s g₅₀) (s g) := by
  constructor
  · rintro ⟨S, hb, -, hc⟩
    rw [leUpToFinite_iff_not_infinitelyLess, not_not] at hc
    exact hb.elim (fun h ↦ InfinitelyLess.of_finitelyClose h hc) fun h ↦ IsTrans.trans _ _ _ h hc
  · intro h
    refine ⟨s g₅₀, .inl (.refl _), fun x y hx hxy ↦ hxy ▸ hx.add_one, ?_⟩
    rw [leUpToFinite_iff_not_infinitelyLess, not_not]
    exact h

/-- Under the qualitative size (36), the merged paradox (80) is unsatisfiable, since two heaps are
never infinitely apart. -/
theorem not_merged_qualSize {De : Type*} {heap known : De → Prop} [DecidablePred heap]
    [DecidablePred known] {size : De → ℕ} {H : ℝ*} {g₅₀ g : De} (h₅₀ : heap g₅₀) (hg : heap g) :
    ¬ ∃ S, Sorites (fun x ↦ LeUpToFinite (qualSize heap known size H x) S)
      (Step (qualSize heap known size H) 1) g₅₀ g := by
  rw [merged_iff]
  exact fun h ↦ h.2 (finitelyClose_qualSize h₅₀ hg)

end Itzhaki2021
