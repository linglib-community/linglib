module

public import Linglib.Semantics.Degree.Marginality.Hyperreal
public import Linglib.Semantics.Degree.Sorites
public import Mathlib.Algebra.Order.Ring.StandardPart
public import Mathlib.Analysis.Real.Hyperreal

/-!
# Itzhaki (2021): Qualitative versus Quantitative Representation: A Non-Standard Analysis of the Sorites Paradox

Individuals are mapped to degrees in two ways. A quantitative map sends a pile to its number of
grains and a person to their height, in an archimedean scale. A qualitative map takes values in
the hyperreals: the qualitative size of a heap is its number of grains plus an infinite number
`H`, and the qualitative magnitude of a change `r` below the smallest relevant unit is `ε * r`
for an infinitesimal `ε`.

The premises of the paradox of the heap hold under the qualitative size, because adding a grain
keeps a size finite and removing one keeps it infinite. The premises of the paradox for *tall*
hold on the hyperreal degrees for the predicate of having standard part at least the standard,
because subtracting an infinitesimal leaves the standard part unchanged. In both cases the unit of
change is negligible against the distance between the base case and the counterexample, and a
monotone predicate satisfies the premises exactly then. Under the quantitative map the
intermediate values are all degrees of some individual, a chain of steps leads from the base case
to the counterexample, and the premises are inconsistent.

When a gradable adjective modifies a collective noun, as in *small heap*, sizes are compared up
to a finite difference. The premises then hold for some standard exactly when the two heaps are
infinitely far apart.

## Implementation notes

* Being indistinguishable and being finitely close are at most marginal difference in
  `Hyperreal.infinitesimalScale` and `Hyperreal.finiteScale`, and being infinitely less is largely
  smaller than in the latter. The preorder of the merged paradox is the order of the blocks of
  `Hyperreal.finiteScale`. The standard part is mathlib's `ArchimedeanClass.stdPart`.
* Whether the size of a heap is known is a parameter of the qualitative size; no result depends on
  it.
* The pluralities of the heap model are their sizes, one of each size, and the individuals of the
  tall model their heights in millimetres.
* The paradox for *tall* is stated on the hyperreal degrees and not on individuals, since no
  individual's height is another's less an infinitesimal. Its tolerance premise at the height of
  an individual is the induction premise of the paper.
* Closure of the infinite numbers under multiplication is stated for a finite factor that is not
  infinitesimal.
* The merged paradox is stated for an arbitrary size map. Under the qualitative size with a single
  `H` any two heaps are finitely close, and the comparison of two heaps takes them to have
  qualitative sizes `H` and `G`.

## References

* [itzhaki-2021]
* [kennedy-2007]
* [link-1983]
* [williamson-1994]
-/

@[expose] public section

namespace Itzhaki2021

open ArchimedeanClass Hyperreal Relation MarginalScale

/-! ### Finite, infinitesimal and infinite hyperreals -/

-- (9d): an infinite number plus a finite one is infinite
theorem mk_add_neg {H a : ℝ*} (hH : mk H < 0) (ha : 0 ≤ mk a) : mk (H + a) < 0 :=
  (mk_add_eq_mk_left (hH.trans_le ha)).symm ▸ hH

-- (9d): an infinite number times a finite one that is not infinitesimal is infinite
example {H a : ℝ*} (hH : mk H < 0) (ha : mk a = 0) : mk (H * a) < 0 := by
  rwa [mk_mul, ha, add_zero]

-- §2.2.2: every finite number is a difference of two infinite ones
theorem exists_sub_of_mk_nonneg {a : ℝ*} (ha : 0 ≤ mk a) :
    ∃ G H : ℝ*, mk G < 0 ∧ mk H < 0 ∧ a = G - H :=
  ⟨ω + a, ω, mk_add_neg archimedeanClassMk_omega_neg ha, archimedeanClassMk_omega_neg, by ring⟩

-- (14), (67): distinct reals are distinguishable
theorem not_atMostMarginal_coe {r s : ℝ} (h : r ≠ s) :
    ¬ infinitesimalScale.AtMostMarginal (r : ℝ*) s := by
  rw [infinitesimalScale_atMostMarginal_iff, ← coe_sub,
    archimedeanClassMk_coe (sub_ne_zero.2 h.symm)]
  exact lt_irrefl 0

-- (22)
theorem stdPart_coe_sub (r : ℝ) {e : ℝ*} (he : 0 < mk e) : stdPart ((r : ℝ*) - e) = r := by
  rw [stdPart_sub_eq_left he, stdPart_coe]

/-! ### Collective nouns -/

section Heap

variable {De : Type*} (heap known : De → Prop) [DecidablePred heap] [DecidablePred known]
  (size : De → ℕ) (H : ℝ*)

/-- The qualitative size (36) maps a heap of known size to `H` plus its size, a heap of unknown
size to `H`, and anything else to its size. -/
noncomputable def qualSize (x : De) : ℝ* :=
  if heap x then (if known x then H + size x else H) else size x

variable {heap known size H} {x y a b : De}

theorem qualSize_of_not_heap (hx : ¬ heap x) : qualSize heap known size H x = size x := by
  simp [qualSize, hx]

-- (37a)
theorem mk_qualSize_nonneg (hx : ¬ heap x) : 0 ≤ mk (qualSize heap known size H x) := by
  rw [qualSize_of_not_heap hx]
  exact mk_natCast_nonneg _

-- (37b)
theorem mk_qualSize_neg (hH : mk H < 0) (hx : heap x) :
    mk (qualSize heap known size H x) < 0 := by
  unfold qualSize
  split_ifs
  exacts [mk_add_neg hH (mk_natCast_nonneg _), hH]

-- (37b)
theorem natCast_lt_qualSize (hH : mk H < 0) (hpos : 0 < H) (hx : heap x) (n : ℕ) :
    (n : ℝ*) < qualSize heap known size H x := by
  have hn : (n : ℝ*) < H := by
    have := (mk_lt_mk.1 (hH.trans_eq mk_one.symm)) n
    rwa [abs_one, nsmul_one, abs_of_pos hpos] at this
  unfold qualSize
  split_ifs
  exacts [hn.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg _)), hn]

-- (76): two heaps are finitely close in qualitative size
theorem atMostMarginal_qualSize (hx : heap x) (hy : heap y) :
    finiteScale.AtMostMarginal (qualSize heap known size H x) (qualSize heap known size H y) := by
  have hn (m n : ℕ) : 0 ≤ mk ((m : ℝ*) - n) :=
    (le_min (mk_natCast_nonneg m) (mk_natCast_nonneg n)).trans (min_le_mk_sub ..)
  rw [finiteScale_atMostMarginal_iff]
  unfold qualSize
  split_ifs
  · simpa using hn _ _
  · simpa using mk_natCast_nonneg (S := ℝ*) _
  · simpa using mk_natCast_nonneg (S := ℝ*) _
  · simp

/-- Under the qualitative size the premises of the paradox of the heap (52) hold, since adding a
grain to a non-heap never yields a heap (38a). -/
theorem sorites_not_heap (hH : mk H < 0) (ha : ¬ heap a) (hb : heap b) :
    Sorites (¬ heap ·)
      (fun x y ↦ qualSize heap known size H y = qualSize heap known size H x + 1) a b where
  base := ha
  tolerance x y hx hxy hy := by
    have := mk_qualSize_neg (known := known) (size := size) hH hy
    rw [hxy] at this
    exact (this.trans_le ((le_min (mk_qualSize_nonneg hx) (by simp)).trans
      (min_le_mk_add ..))).false
  counter := not_not_intro hb

-- (54): the reverse paradox is the contrapositive argument
theorem sorites_heap (hH : mk H < 0) (ha : ¬ heap a) (hb : heap b) :
    Sorites heap
      (fun x y ↦ qualSize heap known size H y = qualSize heap known size H x - 1) b a :=
  have h := (sorites_not_heap (known := known) (size := size) hH ha hb).swap
  ⟨hb, fun _ _ hx hxy ↦ not_not.1 (h.tolerance (not_not_intro hx) (eq_sub_iff_add_eq.1 hxy).symm),
    ha⟩

-- (47a): the quantitative size of a heap is nobody's qualitative size
theorem natCast_size_notMem_range (hH : mk H < 0) (hs : Function.Injective size)
    (hx : heap x) : (size x : ℝ*) ∉ Set.range (qualSize heap known size H) := fun ⟨y, hy⟩ ↦ by
  by_cases hy' : heap y
  · exact ((mk_qualSize_neg (known := known) (size := size) hH hy').trans_le
      (hy ▸ mk_natCast_nonneg _)).false
  · rw [qualSize_of_not_heap hy', Nat.cast_inj] at hy
    exact hy' (hs hy ▸ hx)

-- (47b)
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
    exact (mk_add_neg hH (mk_natCast_nonneg _)).not_ge (hy ▸ mk_natCast_nonneg (S := ℝ*) (size y))

end Heap

/-- When the size map is injective and every intermediate size is the size of something, so that
its inverse is total on them (44)–(46), the premises of a Sorites along steps of `d` are
inconsistent. -/
theorem not_sorites_of_forall_exists {α : Type*} {P : α → Prop} {s : α → ℝ*} {d : ℝ*} {a b : α}
    (hs : Function.Injective s) {n : ℕ} (h : ∀ m < n, ∃ x, s x = s a + m • d)
    (hb : s b = s a + n • d) : ¬ Sorites P (fun x y ↦ s y = s x + d) a b :=
  fun hP ↦ hP.not_reflTransGen (reflTransGen_of_forall_exists_eq_add hs h hb)

-- (81b): along steps of one grain a downward closed predicate of sizes satisfies the premises
-- from `a` to `b` exactly when `a` is infinitely less than `b`
theorem exists_isLowerSet_sorites_iff_largelyLT {a b : ℝ*} :
    (∃ P : ℝ* → Prop, IsLowerSet {x | P x} ∧ Sorites P (fun x y ↦ y = x + 1) a b) ↔
      finiteScale.LargelyLT a b := by
  rw [exists_isLowerSet_sorites_add_iff zero_lt_one, finiteScale_largelyLT_iff, mk_one]

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

-- (52)
theorem sorites_qs : Sorites (¬ heap ·) (fun x y ↦ qs y = qs x + 1) g₁ g₁₀₀₀₀ :=
  sorites_not_heap archimedeanClassMk_omega_neg (by simp [heap, g₁]) rfl

-- (54)
theorem sorites_qs_reverse : Sorites heap (fun x y ↦ qs y = qs x - 1) g₁₀₀₀₀ g₁ :=
  sorites_heap archimedeanClassMk_omega_neg (by simp [heap, g₁]) rfl

-- under the quantitative size the premises of the classic paradox are inconsistent
theorem not_sorites_size :
    ¬ Sorites (¬ heap ·) (fun x y : De ↦ (y.1 : ℝ*) = x.1 + 1) g₁ g₁₀₀₀₀ :=
  not_sorites_of_forall_exists (s := fun x : De ↦ (x.1 : ℝ*))
    (fun _ _ e ↦ Subtype.ext (by simpa using e)) (n := 9999)
    (fun m hm ↦ ⟨⟨m + 1, by simp, by omega⟩, by simp [g₁]; ring⟩) (by simp [g₁₀₀₀₀, g₁]; norm_num)

-- (49a)
example : ¬ ∃ y, qs y = qs g₁ + 9999 := fun ⟨y, hy⟩ ↦
  natCast_size_notMem_range (heap := heap) (known := fun _ ↦ True) (size := Subtype.val)
    (H := ω) (x := g₁₀₀₀₀) archimedeanClassMk_omega_neg Subtype.val_injective rfl
    ⟨y, hy.trans (by simp [qs, qualSize, heap, g₁, g₁₀₀₀₀]; norm_num)⟩

end Model55

/-! ### Gradable adjectives -/

/-- The qualitative magnitude (62) of a change `r` is `e * r` for an infinitesimal `e` when `r`
is below the smallest contextually relevant unit `U`, and `r` otherwise. -/
noncomputable def qualUnit (U : ℝ) (e : ℝ*) (r : ℝ) : ℝ* := if r < U then e * r else r

variable {S U : ℝ} {e : ℝ*}

theorem qualUnit_one_of_lt (hU : 1 < U) : qualUnit U e 1 = e := by simp [qualUnit, hU]

theorem qualUnit_one_of_le (hU : U ≤ 1) : qualUnit U e 1 = 1 := by simp [qualUnit, hU.not_gt]

-- (62): the qualitative magnitude of a change below the relevant unit is infinitesimal
theorem mk_qualUnit_pos (he : 0 < mk e) {r : ℝ} (hr : r < U) : 0 < mk (qualUnit U e r) := by
  simp only [qualUnit, hr, ↓reduceIte, mk_mul]
  exact add_pos_of_pos_of_nonneg he (mk_map_nonneg_of_archimedean coeRingHom r)

/-- With a millimetre below the relevant unit, the premises of the paradox for *tall* (70) hold of
the degrees whose standard part is at least the standard: two metres is tall, one metre is not,
and a qualitative millimetre less leaves the standard part unchanged (64). -/
theorem sorites_tall (he : 0 < mk e) (hU : 1 < U) (h₁ : 1000 < S) (h₂ : S ≤ 2000) :
    Sorites (fun x : ℝ* ↦ S ≤ stdPart x) (fun x y ↦ y = x - qualUnit U e 1) 2000 1000 where
  base := by simpa using h₂
  tolerance x y hx hxy := by rwa [hxy, qualUnit_one_of_lt hU, stdPart_sub_eq_left he]
  counter := by simpa using h₁

private theorem reflTransGen_sub {u a : ℝ*} (n : ℕ) :
    ReflTransGen (fun x y : ℝ* ↦ y = x - u) a (a - n * u) := by
  have := reflTransGen_add_iff (d := -u) (a := a).2 ⟨n, rfl⟩
  simpa [sub_eq_add_neg] using this

-- (70.III)
theorem conclusion_tall (he : 0 < mk e) (hU : 1 < U) (h₁ : 1000 < S) (h₂ : S ≤ 2000) (n : ℕ) :
    S ≤ stdPart ((2000 : ℝ*) - n * qualUnit U e 1) :=
  (sorites_tall he hU h₁ h₂).of_reflTransGen (reflTransGen_sub n)

-- (66): with the quantitative unit the premises are inconsistent, whatever the predicate
theorem not_sorites_tall {P : ℝ* → Prop} (hU : U ≤ 1) :
    ¬ Sorites P (fun x y ↦ y = x - qualUnit U e 1) 2000 1000 := fun h ↦
  h.not_reflTransGen <| by
    have := reflTransGen_sub (u := qualUnit U e 1) (a := 2000) 1000
    rw [qualUnit_one_of_le hU] at this ⊢
    norm_num at this
    exact this

/-- An upward closed predicate of degrees satisfies the premises of the paradox for *tall* along
steps of `u` exactly when `u` is infinitesimal (61). -/
theorem exists_isUpperSet_sorites_tall_iff {u : ℝ*} (hu : 0 < u) :
    (∃ P : ℝ* → Prop, IsUpperSet {x | P x} ∧ Sorites P (fun x y ↦ y = x - u) 2000 1000) ↔
      0 < mk u := by
  rw [exists_isUpperSet_sorites_sub_iff hu]
  norm_num

-- (71): heights in millimetres, the standard `1800` and the smallest relevant unit `2`
example : Sorites (fun x : ℝ* ↦ (1800 : ℝ) ≤ stdPart x) (fun x y ↦ y = x - qualUnit 2 ε 1)
    2000 1000 :=
  sorites_tall archimedeanClassMk_epsilon_pos (by norm_num) (by norm_num) (by norm_num)

/-! ### The merged paradox -/

/-- The premises of the merged paradox (80) hold for some standard exactly when the size of the
small heap is infinitely less than that of the large one. A size is at most the standard up to a
finite difference (79) when its block in the scale of finite differences is at most that of the
standard. -/
theorem merged_iff {De : Type*} {s : De → ℝ*} {g₅₀ g : De} :
    (∃ S, Sorites (fun x ↦ finiteScale.toBlock (s x) ≤ finiteScale.toBlock S)
      (fun x y ↦ s y = s x + 1) g₅₀ g) ↔ finiteScale.LargelyLT (s g₅₀) (s g) :=
  ⟨fun ⟨_, h⟩ ↦ toBlock_lt_toBlock.1 (h.base.trans_lt (not_le.1 h.counter)),
    fun h ↦ ⟨s g₅₀, (sorites_toBlock_le le_rfl h).comap s fun x y hxy ↦
      finiteScale_atMostMarginal_iff.2 (by simp [hxy])⟩⟩

-- (81): of two sizes, the smaller is finitely close to the larger or infinitely less
example {a b : ℝ*} (h : a < b) : finiteScale.MarginallyLT a b ∨ finiteScale.LargelyLT a b :=
  marginallyLT_or_largelyLT_of_lt h

end Itzhaki2021
