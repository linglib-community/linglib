module

public import Linglib.Semantics.Dynamic.RegisterStructure
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Quantification.Defs
public import Mathlib.Order.SupClosed
public import Mathlib.Data.Fin.VecNotation

/-!
# Plural CDRT

Compositional DRT over plural information states ([van-den-berg-1996], [brasoveanu-2007],
[brasoveanu-2010]). An information state is a set of CDRT states, a matrix whose rows are
assignments and whose columns are drefs: a dref stores the set of its values in the rows, and the
rows store the dependencies between the values of different drefs. A dref takes the dummy value ★
in the rows where it has none; here its register holds a `Flat E` and ★ is `⊥`.

Every CDRT update lifts to plural states cumulatively: the lift is the relation lifting
`Set.LiftRel` of the update, which is the cumulation `**` of [beck-sauerland-2000], each input row
having a successor among the output rows and each output row a predecessor among the input rows.
This is how dref introduction `[u]` lifts to plural states, and the lift is a functor. Atomic
conditions hold distributively of the rows where their drefs have values. Structured inclusion
selects a subset of a dref's values by discarding rows, so the subset keeps exactly the
superset's dependencies. A dref's values are the defined part of the image of its register, and
on plural partial assignments they are `PluralAssign.value`, its cells the operator `restrict`.
Singular number says the values are a singleton, [spector-2026]'s `atomic(x)`.

Quantification is decomposed into maximization, which stores in a dref every individual that
satisfies an update, distributivity, which updates the cell of each value of a dref separately,
and a static determiner relating the values of two drefs.

## Main definitions

* `PCDRT.value`, `PCDRT.cell`, `PCDRT.nonDummy`, `PCDRT.dep`, `PCDRT.tuples`: a dref's values,
  the rows where it holds a given value or ★, the rows where it has one, and the values that two
  or more drefs take together in a row.
* `PCDRT.intro`: dref introduction `[u]`.
* `PCDRT.atom`, `PCDRT.sing`, `PCDRT.det`: distributive predication, singular number, and a static
  determiner over the values of two drefs.
* `PCDRT.structSub`, `PCDRT.structSubAll`: structured inclusion.
* `PCDRT.max`, `PCDRT.maxSub`, `PCDRT.dist`, `PCDRT.distrib`: maximization and distributivity.
* `PCDRT.copy`: a dref copying another's value in every row.
* `PCDRT.Preserves`: an update leaves the values of some drefs in place row for row.

## Main results

* `PCDRT.dom_dep`, `PCDRT.cod_dep`: where every row valuing one dref values the other, the
  dependency's domain and codomain are the two drefs' values.
* `PCDRT.dep_subset_of_structSub`, `PCDRT.dep_eq_of_structSubAll`: a structured subset keeps
  only, and with the full condition all, of the superset's dependencies.
* `PCDRT.distrib_test`, `PCDRT.distrib_test_atom_self`: distributivity over a test tests every
  cell, and over a dref's own atomic condition it is redundant.
* `PCDRT.nonDummy_subset_of_mem_max`, `PCDRT.mem_max_test_atom_self_iff`: maximization of a
  union-closed condition stores every individual that satisfies it, with every input row.
* `PCDRT.mem_maxSub_test_copy`: a structured subset that copies its superset row for row is
  maximal when it passes the test.

## References

* [M. H. van den Berg, *Some aspects of the internal structure of discourse: the dynamics of
  nominal anaphora* (1996)][van-den-berg-1996]
* [A. Brasoveanu, *Structured nominal and modal reference* (2007)][brasoveanu-2007]
* [A. Brasoveanu, *Decomposing modal quantification* (2010)][brasoveanu-2010]
* [S. Beck and U. Sauerland, *Cumulation is needed: A reply to Winter (2000)*
  (2000)][beck-sauerland-2000]
* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
* [B. Spector, *Trivalence and transparency: A non-dynamic approach to anaphora*
  (2026)][spector-2026]
-/

@[expose] public section

namespace PCDRT

open DynamicSemantics DynamicSemantics.Update SetRel RegisterStructure

variable {R S E ι : Type*} [RegisterStructure R S (Flat E)] {u u' v : R} {w : ι → R}
  {I J K : Set S} {D D' : Update (Set S)} {C : Condition (Set S)} {x : E}

/-! ### Values, rows and cells -/

/-- The values of `u` in `I`, `uI` ([brasoveanu-2010] (16), (38)); ★ is not a value. -/
def value (u : R) (I : Set S) : Set E := {x | ∃ i ∈ I, val u i = ↑x}

/-- The rows of `I` where `u` holds `e`, `I_{u=e}` ((71)); at `e = ★` the rows where `u` has no
value. -/
def cell (u : R) (e : Flat E) (I : Set S) : Set S := {i ∈ I | val u i = e}

/-- The rows of `I` where `u` has a value, the non-dummy substate `I_{u≠★}` ((29)). -/
def nonDummy (u : R) (I : Set S) : Set S := {i ∈ I | val u i ≠ ⊥}

/-- The dependency between `u` and `v` that `I` stores is the set of pairs of their values in a
row. -/
def dep (u v : R) (I : Set S) : SetRel E E :=
  {p | ∃ i ∈ I, val u i = ↑p.1 ∧ val v i = ↑p.2}

/-- The tuples of values that the drefs `w` take together in a row of `I`; a row where some `wₖ`
is ★ contributes none, so these are read off the substate `I_{u₁≠★,…,uₙ≠★}` ((33)). -/
def tuples (w : ι → R) (I : Set S) : Set (ι → E) := {y | ∃ i ∈ I, ∀ k, val (w k) i = ↑(y k)}

@[simp] theorem mem_value : x ∈ value u I ↔ ∃ i ∈ I, val u i = ↑x := Iff.rfl

@[simp] theorem mem_cell {e : Flat E} {i : S} : i ∈ cell u e I ↔ i ∈ I ∧ val u i = e := Iff.rfl

@[simp] theorem mem_nonDummy {i : S} : i ∈ nonDummy u I ↔ i ∈ I ∧ val u i ≠ ⊥ := Iff.rfl

@[simp] theorem mem_tuples {y : ι → E} : y ∈ tuples w I ↔ ∃ i ∈ I, ∀ k, val (w k) i = ↑(y k) :=
  Iff.rfl

theorem value_eq_preimage_image (u : R) (I : Set S) :
    value u I = (↑) ⁻¹' (val u '' I) :=
  rfl

theorem cell_coe_eq_empty (h : x ∉ value u I) : cell u x I = ∅ :=
  Set.eq_empty_of_forall_notMem fun i hi ↦ h ⟨i, hi⟩

theorem eq_of_forall_cell_eq (h : ∀ e, cell u e I = cell u e J) : I = J :=
  Set.ext fun i ↦ by simpa using Set.ext_iff.1 (h (val u i)) i

theorem cell_bot_union_biUnion_cell (u : R) (I : Set S) :
    cell u ⊥ I ∪ ⋃ x ∈ value u I, cell u x I = I := by
  ext i
  simp only [Set.mem_union, mem_cell, Set.mem_iUnion, mem_value, exists_prop]
  refine ⟨by rintro (⟨hi, -⟩ | ⟨x, -, hi, -⟩) <;> exact hi, fun hi ↦ ?_⟩
  rcases eq_or_ne (val u i) ⊥ with h | h
  · exact .inl ⟨hi, h⟩
  · obtain ⟨x, hx⟩ := Flat.ne_bot_iff_exists.1 h
    exact .inr ⟨x, ⟨i, hi, hx⟩, hi, hx⟩

theorem value_cell_subset (u : R) (x : E) (I : Set S) : value u (cell u x I) ⊆ {x} :=
  fun _ ⟨_, hi, hy⟩ ↦ Flat.coe_inj.1 (hy.symm.trans hi.2)

theorem value_cell (h : x ∈ value u I) : value u (cell u x I) = {x} :=
  (value_cell_subset u x I).antisymm (by simpa using h)

@[simp] theorem value_nonDummy : value u (nonDummy u I) = value u I :=
  Set.ext fun _ ↦ ⟨fun ⟨i, hi, h⟩ ↦ ⟨i, hi.1, h⟩,
    fun ⟨i, hi, h⟩ ↦ ⟨i, ⟨hi, h ▸ Flat.coe_ne_bot⟩, h⟩⟩

@[simp] theorem cell_coe_nonDummy : cell u x (nonDummy u I) = cell u x I :=
  Set.ext fun _ ↦ ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2 ▸ Flat.coe_ne_bot⟩, h.2⟩⟩

theorem value_singleton_of_eq {i : S} (h : val u i = ↑x) : value u {i} = {x} := by
  ext y
  simp [h, eq_comm]

theorem dep_singleton_of_eq {i : S} {x y : E} (hu : val u i = ↑x) (hv : val v i = ↑y) :
    dep u v {i} = {(x, y)} := by
  ext ⟨a, b⟩
  simp [dep, hu, hv, eq_comm]

theorem fst_mem_value_of_mem_dep {p : E × E} (h : p ∈ dep u v I) : p.1 ∈ value u I :=
  let ⟨i, hi, hu, _⟩ := h; ⟨i, hi, hu⟩

theorem snd_mem_value_of_mem_dep {p : E × E} (h : p ∈ dep u v I) : p.2 ∈ value v I :=
  let ⟨i, hi, _, hv⟩ := h; ⟨i, hi, hv⟩

theorem value_mono (h : I ⊆ J) : value u I ⊆ value u J :=
  fun _ ⟨i, hi, hx⟩ ↦ ⟨i, h hi, hx⟩

theorem dep_mono (h : I ⊆ J) : dep u v I ⊆ dep u v J :=
  fun _ ⟨i, hi, hu, hv⟩ ↦ ⟨i, h hi, hu, hv⟩

theorem nonDummy_mono (h : I ⊆ J) : nonDummy u I ⊆ nonDummy u J :=
  fun _ hi ↦ ⟨h hi.1, hi.2⟩

@[simp] theorem tuples_union (w : ι → R) (I J : Set S) :
    tuples w (I ∪ J) = tuples w I ∪ tuples w J := by
  ext
  simp [or_and_right, exists_or]

theorem tuples_singleton_of_eq {i : S} {y : ι → E} (h : ∀ k, val (w k) i = ↑(y k)) :
    tuples w {i} = {y} := by
  ext z; simp [h, funext_iff, eq_comm]

theorem tuples_singleton_of_eq_bot {i : S} (k : ι) (h : val (w k) i = ⊥) :
    tuples w {i} = (∅ : Set (ι → E)) :=
  Set.eq_empty_of_forall_notMem fun _ hy ↦ by simp_all

theorem tuples_vec1 (u : R) (I : Set S) : tuples ![u] I = (fun x ↦ ![x]) '' value u I := by
  ext y; simp [funext_iff]

theorem tuples_vec2 (u v : R) (I : Set S) :
    tuples ![u, v] I = (fun p ↦ ![p.1, p.2]) '' dep u v I := by
  ext y; simp [funext_iff, Fin.forall_fin_two, dep]

/-- Where every row valuing `u` also values `v`, the values of `u` are the domain of the
dependency between them. -/
theorem dom_dep (h : ∀ i ∈ I, val u i ≠ ⊥ → val v i ≠ ⊥) :
    (dep u v I).dom = value u I := by
  refine Set.ext fun x ↦ ⟨fun ⟨y, hp⟩ ↦ fst_mem_value_of_mem_dep hp, fun ⟨i, hi, hx⟩ ↦ ?_⟩
  obtain ⟨y, hy⟩ := Flat.ne_bot_iff_exists.1 (h i hi (hx ▸ Flat.coe_ne_bot))
  exact ⟨y, i, hi, hx, hy⟩

/-- Where every row valuing `v` also values `u`, the values of `v` are the codomain of the
dependency between them. -/
theorem cod_dep (h : ∀ i ∈ I, val v i ≠ ⊥ → val u i ≠ ⊥) :
    (dep u v I).cod = value v I := by
  refine Set.ext fun y ↦ ⟨fun ⟨x, hp⟩ ↦ snd_mem_value_of_mem_dep hp, fun ⟨i, hi, hy⟩ ↦ ?_⟩
  obtain ⟨x, hx⟩ := Flat.ne_bot_iff_exists.1 (h i hi (hy ▸ Flat.coe_ne_bot))
  exact ⟨x, i, hi, hx, hy⟩

theorem cell_eq_restrict {Var D : Type*} [DecidableEq Var] (G : PluralAssign Var D) (x : Var)
    (a : D) : cell x ↑a G = G.restrict x a :=
  rfl

theorem value_eq_pluralAssign_value {Var D : Type*} [DecidableEq Var] (G : PluralAssign Var D)
    (x : Var) : value x G = G.value x :=
  rfl

/-! ### Dref introduction and conditions -/

/-- Dref introduction `[u]` ([brasoveanu-2010] (18)): the cumulative lift of CDRT's random
assignment. -/
def intro (u : R) : Update (Set S) := cumul (randomAssign u)

theorem singleton_mem_intro (i : S) (u : R) (e : Flat E) :
    {i} ~[intro u] {extend i u e} :=
  ⟨fun _ hi ↦ ⟨_, rfl, e, by rw [hi]⟩, fun _ hj ↦ ⟨i, rfl, e, by rw [hj]⟩⟩

/-- The atomic condition `P{u₁, …, uₙ}` ((30), (32), (34)) holds when some row values every `wₖ`
and the values in every such row satisfy `P`. -/
def atom (P : (ι → E) → Prop) (w : ι → R) : Condition (Set S) :=
  {I | (tuples w I).Nonempty ∧ ∀ y ∈ tuples w I, P y}

@[simp] theorem mem_atom {P : (ι → E) → Prop} :
    I ∈ atom P w ↔ (tuples w I).Nonempty ∧ ∀ y ∈ tuples w I, P y :=
  Iff.rfl

theorem supClosed_atom (P : (ι → E) → Prop) (w : ι → R) : SupClosed (atom P w : Set (Set S)) :=
  fun _ ⟨hI, hP⟩ _ ⟨_, hQ⟩ ↦ ⟨by simpa using Or.inl hI,
    by simpa using fun y h ↦ h.elim (hP y) (hQ y)⟩

theorem singleton_mem_atom_iff {P : (ι → E) → Prop} {i : S} {y : ι → E}
    (h : ∀ k, val (w k) i = ↑(y k)) : {i} ∈ atom P w ↔ P y := by
  simp [tuples_singleton_of_eq h]

theorem mem_atom_vec1 {P : (Fin 1 → E) → Prop} :
    I ∈ atom P ![u] ↔ (value u I).Nonempty ∧ ∀ x ∈ value u I, P ![x] := by
  simp only [mem_atom, tuples_vec1, Set.image_nonempty, Set.forall_mem_image]

theorem mem_atom_vec2 {P : (Fin 2 → E) → Prop} :
    I ∈ atom P ![u, v] ↔ (dep u v I).Nonempty ∧ ∀ p ∈ dep u v I, P ![p.1, p.2] := by
  simp only [mem_atom, tuples_vec2, Set.image_nonempty, Set.forall_mem_image]

/-- Singular number `sing(u)` ((39)) holds when `u` has exactly one value. -/
def sing (u : R) : Condition (Set S) := {I | ∃ x, value u I = {x}}

theorem mem_sing_iff {Var D : Type*} [DecidableEq Var] {G : PluralAssign Var D} {x : Var} :
    G ∈ sing x ↔ ∃ d, G.value x = {d} :=
  Iff.rfl

/-- The determiner condition `DET{u, u'}` ((76)): the static determiner `q` relates the values of
`u` and `u'`. -/
def det (q : Quantifier.GQ E) (u u' : R) : Condition (Set S) :=
  {I | q (· ∈ value u I) (· ∈ value u' I)}

@[simp] theorem mem_det {q : Quantifier.GQ E} :
    I ∈ det q u u' ↔ q (· ∈ value u I) (· ∈ value u' I) :=
  Iff.rfl

/-! ### Structured inclusion -/

/-- Structured inclusion `u' ⋐ u` ((66)) holds when in every row `u'` has `u`'s value or ★. -/
def structSub (u' u : R) : Condition (Set S) :=
  {I | ∀ i ∈ I, val u' i = val u i ∨ val u' i = ⊥}

/-- Full structured inclusion `u' ⊑ u` ((68)) is structured inclusion that also keeps every row
in which `u` has one of `u'`'s values. -/
def structSubAll (u' u : R) : Condition (Set S) :=
  {I | I ∈ structSub u' u ∧ ∀ i ∈ I, ∀ x ∈ value u' I, val u i = ↑x → val u' i = ↑x}

/-- A structured subset keeps only the superset's dependencies (p. 465), since whatever `u'` is
paired with in a row, `u` is paired with there too. -/
theorem dep_subset_of_structSub (h : I ∈ structSub u' u) : dep u' v I ⊆ dep u v I := by
  rintro ⟨x, y⟩ ⟨i, hi, hx, hy⟩
  refine ⟨i, hi, ?_, hy⟩
  rcases h i hi with h' | h'
  · exact h' ▸ hx
  · simp [h'] at hx

/-- A fully structured subset keeps all of the superset's dependencies at its own values
(p. 466). -/
theorem dep_eq_of_structSubAll (h : I ∈ structSubAll u' u) :
    dep u' v I = {p ∈ dep u v I | p.1 ∈ value u' I} := by
  ext ⟨x, y⟩
  refine ⟨fun hp ↦ ⟨dep_subset_of_structSub h.1 hp, ?_⟩, ?_⟩
  · obtain ⟨i, hi, hx, -⟩ := hp
    exact ⟨i, hi, hx⟩
  · rintro ⟨⟨i, hi, hx, hy⟩, hxu'⟩
    exact ⟨i, hi, h.2 i hi x hxu' hx, hy⟩

/-! ### Distributivity -/

/-- Distributivity `dist_u(D)` ((72)): `u` keeps its values, and `D` relates the cell of each
value in the input to its cell in the output. -/
def dist (u : R) (D : Update (Set S)) : Update (Set S) :=
  {(I, J) | value u I = value u J ∧ ∀ x ∈ value u I, cell u x I ~[D] cell u x J}

/-- The distributivity operator `_u(D)` ((74)): the rows where `u` is ★ pass unchanged, `u` has a
value, and `D` updates the rest distributively over `u`. -/
def distrib (u : R) (D : Update (Set S)) : Update (Set S) :=
  {(I, J) | cell u ⊥ I = cell u ⊥ J ∧ (value u I).Nonempty ∧
    nonDummy u I ~[dist u D] nonDummy u J}

theorem mem_distrib : I ~[distrib u D] J ↔ cell u ⊥ I = cell u ⊥ J ∧ (value u I).Nonempty ∧
    value u I = value u J ∧ ∀ x ∈ value u I, cell u x I ~[D] cell u x J := by
  simp only [distrib, dist, Set.mem_ofPred_eq, value_nonDummy, cell_coe_nonDummy]

/-- Distributivity over a test tests every cell. -/
theorem distrib_test (u : R) (C : Condition (Set S)) :
    distrib u (test C) =
      test {I : Set S | (value u I).Nonempty ∧ ∀ x ∈ value u I, cell u ↑x I ∈ C} := by
  ext ⟨I, J⟩
  simp only [mem_distrib, mem_test, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hbot, hne, hv, hc⟩
    obtain rfl : I = J := eq_of_forall_cell_eq (u := u) fun e ↦ by
      induction e using Flat.recBotCoe with
      | bot => exact hbot
      | coe x =>
        by_cases hx : x ∈ value u I
        · exact (hc x hx).1
        · rw [cell_coe_eq_empty hx, cell_coe_eq_empty (hv ▸ hx)]
    exact ⟨rfl, hne, fun x hx ↦ (hc x hx).2⟩
  · rintro ⟨rfl, hne, hc⟩
    exact ⟨rfl, hne, rfl, fun x hx ↦ ⟨rfl, hc x hx⟩⟩

/-- Distributivity over a dref's own atomic condition is redundant (p. 470): each cell holds one
value of the dref. -/
theorem distrib_test_atom_self (P : (Fin 1 → E) → Prop) (u : R) :
    distrib u (test (atom P ![u])) = test (atom P ![u] : Condition (Set S)) := by
  rw [distrib_test]
  congr 1
  ext I
  simp only [mem_atom_vec1, Set.mem_ofPred_eq]
  refine and_congr_right fun _ ↦ forall₂_congr fun x hx ↦ ?_
  simp [value_cell hx]

/-! ### Maximization -/

/-- Maximization `max^u(D)` ((69)): introduce `u` and update with `D`, keeping the outputs whose
non-dummy substate for `u` no other output's strictly contains. -/
def max (u : R) (D : Update (Set S)) : Update (Set S) := maxBy (nonDummy u) (intro u ○ D)

/-- Maximization of a fully structured subset `max^{u'⊑u}(D)` ((70)). -/
def maxSub (u' u : R) (D : Update (Set S)) : Update (Set S) :=
  max u' (test (structSubAll u' u) ○ D)

theorem mem_max : I ~[max u D] J ↔ MaximalFor (I ~[intro u ○ D] ·) (nonDummy u) J :=
  Iff.rfl

theorem max_subset (u : R) (D : Update (Set S)) : max u D ⊆ intro u ○ D :=
  maxBy_subset _ _

theorem mem_max_of_forall_subset (hJ : I ~[intro u ○ D] J)
    (h : ∀ K, I ~[intro u ○ D] K → nonDummy u K ⊆ nonDummy u J) : I ~[max u D] J :=
  mem_max.2 ⟨hJ, fun K hK _ ↦ h K hK⟩

/-- Maximization of a union-closed condition stores every individual that satisfies it (p. 466):
the non-dummy substate of a maximal output contains that of every output. -/
theorem nonDummy_subset_of_mem_max (hC : SupClosed C) (hJ : I ~[max u (test C)] J)
    (hK : I ~[intro u ○ test C] K) : nonDummy u K ⊆ nonDummy u J := by
  have hJ' := mem_max.1 hJ
  obtain ⟨hIJ, hJC⟩ := mem_comp_test.1 hJ'.prop
  obtain ⟨hIK, hKC⟩ := mem_comp_test.1 hK
  have hIJK : I ~[intro u ○ test C] (J ∪ K) := by
    refine mem_comp_test.2 ⟨?_, hC hJC hKC⟩
    have := Set.LiftRel.union hIJ hIK
    rwa [Set.union_self] at this
  exact fun k hk ↦ hJ'.le_of_le hIJK (nonDummy_mono Set.subset_union_left)
    (nonDummy_mono Set.subset_union_right hk)

/-- Maximization of a dref's own atomic condition pairs every input row with every individual
that satisfies it (p. 466): its outputs are the introductions of `u` whose non-dummy rows are
exactly those pairs. -/
theorem mem_max_test_atom_self_iff {P : (Fin 1 → E) → Prop} (hI : I.Nonempty) (hP : ∃ x, P ![x]) :
    I ~[max u (test (atom P ![u]))] J ↔
      I ~[intro u] J ∧ nonDummy u J = Set.image2 (fun i x ↦ extend i u ↑x) I {x | P ![x]} := by
  set W : Set S := Set.image2 (fun i x ↦ extend i u ↑x) I {x | P ![x]}
  have hW : I ~[intro u ○ test (atom P ![u])] W := by
    obtain ⟨x₀, hx₀⟩ := hP
    refine mem_comp_test.2 ⟨⟨fun i hi ↦ ⟨_, ⟨i, hi, x₀, hx₀, rfl⟩, ↑x₀, rfl⟩,
      fun _ ⟨i, hi, x, _, hj⟩ ↦ ⟨i, hi, ↑x, hj.symm⟩⟩, mem_atom_vec1.2 ⟨?_, ?_⟩⟩
    · obtain ⟨i, hi⟩ := hI
      exact ⟨x₀, _, ⟨i, hi, x₀, hx₀, rfl⟩, val_extend_self ..⟩
    · rintro x ⟨_, ⟨i, -, y, hy, rfl⟩, hx⟩
      rwa [← Flat.coe_inj.1 ((val_extend_self ..).symm.trans hx)]
  have hsub : ∀ K, I ~[intro u ○ test (atom P ![u])] K → nonDummy u K ⊆ W := by
    rintro K hK k ⟨hk, hne⟩
    obtain ⟨hIK, hKP⟩ := mem_comp_test.1 hK
    obtain ⟨i, hi, e, rfl⟩ := hIK.2 k hk
    obtain ⟨x, hx⟩ := Flat.ne_bot_iff_exists.1 hne
    rw [val_extend_self] at hx
    subst hx
    exact ⟨i, hi, x, (mem_atom_vec1.1 hKP).2 x ⟨_, hk, val_extend_self ..⟩, rfl⟩
  constructor
  · intro hJ
    have hJ' := mem_comp_test.1 (max_subset u _ hJ)
    refine ⟨hJ'.1, (hsub J (max_subset u _ hJ)).antisymm fun j hj ↦ ?_⟩
    have hne : val u j ≠ ⊥ := by
      obtain ⟨_, -, _, -, rfl⟩ := hj
      simp [val_extend_self]
    exact nonDummy_subset_of_mem_max (supClosed_atom _ _) hJ hW ⟨hj, hne⟩
  · rintro ⟨hIJ, hJW⟩
    refine mem_max_of_forall_subset (mem_comp_test.2 ⟨hIJ, ?_⟩) fun K hK ↦ hJW ▸ hsub K hK
    have hv : value u J = value u W := by rw [← value_nonDummy, hJW]
    rw [mem_atom_vec1, hv]
    exact mem_atom_vec1.1 (mem_comp_test.1 hW).2

/-! ### Copies -/

/-- The state where `u'` holds `u`'s value, or ★, in every row of `I`: the fully structured subset
of `u` that keeps all of its values. -/
def copy (u' u : R) (I : Set S) : Set S := (fun i ↦ extend i u' (val u i)) '' I

theorem mem_intro_copy (I : Set S) : I ~[intro u'] copy u' u I :=
  ⟨fun i hi ↦ ⟨_, ⟨i, hi, rfl⟩, _, rfl⟩, fun _ ⟨i, hi, hj⟩ ↦ ⟨i, hi, _, hj.symm⟩⟩

theorem value_copy_of_ne (hv : v ≠ u') (I : Set S) : value v (copy u' u I) = value v I := by
  ext x
  simp [copy, val_extend_of_ne _ _ _ _ hv]

theorem value_copy_self (I : Set S) : value u' (copy u' u I) = value u I := by
  ext x
  simp [copy, val_extend_self]

theorem cell_copy_self (I : Set S) (e : Flat E) :
    cell u' e (copy u' u I) = copy u' u (cell u e I) := by
  ext j
  simp only [copy, mem_cell, Set.mem_image]
  grind [val_extend_self]

section Copy

variable (hu : u ≠ u')
include hu

theorem copy_mem_structSubAll (I : Set S) : copy u' u I ∈ structSubAll u' u := by
  refine ⟨?_, ?_⟩ <;> rintro _ ⟨i, -, rfl⟩ <;> simp [val_extend_self, val_extend_of_ne _ _ _ _ hu]

/-- Maximization of a structured subset under a test is maximal at the copy, provided the copy
passes the test. -/
theorem mem_maxSub_test_copy (hC : copy u' u I ∈ C) :
    I ~[maxSub u' u (test C)] copy u' u I := by
  refine mem_max_of_forall_subset ⟨_, mem_intro_copy I,
    mem_test_comp.2 ⟨copy_mem_structSubAll hu I, rfl, hC⟩⟩ ?_
  rintro K ⟨K₀, hIK, hK⟩ k ⟨hk, hne⟩
  obtain ⟨⟨hK₀, -⟩, hK₀K⟩ := mem_test_comp.1 hK
  obtain ⟨rfl, -⟩ := hK₀K
  obtain ⟨i, hi, e, rfl⟩ := hIK.2 k hk
  refine ⟨⟨i, hi, ?_⟩, hne⟩
  rcases hK₀ _ hk with h | h
  · rw [val_extend_self, val_extend_of_ne _ _ _ _ hu] at h
    rw [h]
  · exact absurd h hne

end Copy

/-! ### Preservation -/

/-- An update preserves the drefs `w` when its inputs and outputs match row for row on them:
every input row has an output row and every output row an input row with the same values for
every `wₖ`. -/
def Preserves (w : ι → R) (D : Update (Set S)) : Prop :=
  ∀ ⦃I J⦄, I ~[D] J → Set.LiftRel (fun i j ↦ ∀ k, val (w k) i = val (w k) j) I J

theorem Preserves.value_eq (h : Preserves ![v] D) (hIJ : I ~[D] J) : value v J = value v I := by
  ext x
  refine ⟨fun ⟨j, hj, hx⟩ ↦ ?_, fun ⟨i, hi, hx⟩ ↦ ?_⟩
  · obtain ⟨i, hi, hij⟩ := (h hIJ).2 j hj
    exact ⟨i, hi, (hij 0).trans hx⟩
  · obtain ⟨j, hj, hij⟩ := (h hIJ).1 i hi
    exact ⟨j, hj, (hij 0).symm.trans hx⟩

theorem Preserves.comp (h₁ : Preserves w D) (h₂ : Preserves w D') : Preserves w (D ○ D') :=
  fun _ _ ⟨_, hIK, hKJ⟩ ↦ (Set.liftRel_comp.2 ⟨_, h₁ hIK, h₂ hKJ⟩).imp
    fun ⟨_, h, h'⟩ k ↦ (h k).trans (h' k)

theorem preserves_test (w : ι → R) (C : Condition (Set S)) : Preserves w (test C) :=
  fun _ _ ⟨hIJ, _⟩ ↦ hIJ ▸ Set.liftRel_refl_of_refl_on fun _ _ _ ↦ rfl

theorem preserves_cumul {D : Update S} (h : ∀ k, Fixes (w k) D) : Preserves w (cumul D) :=
  fun _ _ hIJ ↦ hIJ.imp fun hij k ↦ (h k _ _ hij).symm

theorem preserves_intro (h : ∀ k, w k ≠ u) : Preserves w (intro u : Update (Set S)) :=
  preserves_cumul fun k ↦ fixes_randomAssign_of_ne (h k)

theorem value_intro_of_ne (h : v ≠ u) (hIJ : I ~[intro u] J) : value v J = value v I :=
  (preserves_intro (w := ![v]) (Fin.forall_fin_one.2 h)).value_eq hIJ

theorem Preserves.max (h : ∀ k, w k ≠ u) (hD : Preserves w D) : Preserves w (max u D) :=
  fun _ _ hIJ ↦ ((preserves_intro h).comp hD) (max_subset u D hIJ)

theorem Preserves.maxSub (h : ∀ k, w k ≠ u') (hD : Preserves w D) :
    Preserves w (maxSub u' u D) :=
  ((preserves_test w _).comp hD).max h

theorem Preserves.distrib (hD : Preserves w D) : Preserves w (distrib u D) := by
  intro I J hIJ
  obtain ⟨hbot, -, hv, hc⟩ := mem_distrib.1 hIJ
  rw [← cell_bot_union_biUnion_cell u I, ← cell_bot_union_biUnion_cell u J, ← hbot, ← hv]
  refine (Set.liftRel_refl_of_refl_on fun _ _ _ ↦ rfl).union
    ((Set.liftRel_eq.2 rfl).biUnion fun x hx y _ hxy ↦ ?_)
  subst hxy
  exact hD (hc x hx)

end PCDRT
