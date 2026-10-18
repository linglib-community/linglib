module

public import Linglib.Semantics.Dynamic.RegisterStructure
public import Linglib.Logic.Assignment

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

## Main definitions

* `PCDRT.value`, `PCDRT.cell`, `PCDRT.dep`: a dref's values, the rows where it has a given
  one, and the pairs of values two drefs have in a row.
* `PCDRT.intro`: dref introduction `[u]`.
* `PCDRT.atom`, `PCDRT.atom₂`, `PCDRT.sing`: distributive predication and singular number.
* `PCDRT.structSub`, `PCDRT.structSubAll`: structured inclusion.

## Main results

* `PCDRT.dom_dep`, `PCDRT.cod_dep`: where every row valuing one dref values the other, the
  dependency's domain and codomain are the two drefs' values.
* `PCDRT.value_eq_of_fixes`: a dref an update fixes keeps its values under the lifted update.
* `PCDRT.dep_subset_of_structSub`, `PCDRT.dep_eq_of_structSubAll`: a structured subset keeps
  only, and with the full condition all, of the superset's dependencies.

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

open DynamicSemantics DynamicSemantics.Update SetRel

variable {R S E : Type*} [RegisterStructure R S (Flat E)] {u u' v : R} {I J : Set S}

/-! ### Values, rows and cells -/

/-- The values of `u` in `I`, `uI` ([brasoveanu-2010] (16), (38)); ★ is not a value. -/
def value (u : R) (I : Set S) : Set E := {x | ∃ i ∈ I, RegisterStructure.val u i = ↑x}

/-- The values of `u` are the defined part of the image of its register. -/
theorem value_eq_preimage_image (u : R) (I : Set S) :
    value u I = (↑) ⁻¹' (RegisterStructure.val u '' I) :=
  rfl

/-- The rows of `I` where `u` has the value `x`, `I_{u=x}` ((71)). -/
def cell (u : R) (x : E) (I : Set S) : Set S := {i ∈ I | RegisterStructure.val u i = ↑x}

/-- The dependency between `u` and `v` that `I` stores is the set of pairs of their values in a
row. -/
def dep (u v : R) (I : Set S) : SetRel E E :=
  {p | ∃ i ∈ I, RegisterStructure.val u i = ↑p.1 ∧ RegisterStructure.val v i = ↑p.2}

theorem value_singleton_of_eq {i : S} {x : E} (h : RegisterStructure.val u i = ↑x) :
    value u {i} = {x} := by
  ext y
  simp only [value, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq, h,
    Flat.coe_inj]
  exact eq_comm

theorem dep_singleton_of_eq {i : S} {x y : E} (hu : RegisterStructure.val u i = ↑x)
    (hv : RegisterStructure.val v i = ↑y) : dep u v {i} = {(x, y)} := by
  ext ⟨a, b⟩
  simp only [dep, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq, hu, hv,
    Flat.coe_inj, Prod.mk.injEq]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁.symm, h₂.symm⟩⟩

theorem fst_mem_value_of_mem_dep {p : E × E} (h : p ∈ dep u v I) : p.1 ∈ value u I :=
  let ⟨i, hi, hu, _⟩ := h; ⟨i, hi, hu⟩

theorem snd_mem_value_of_mem_dep {p : E × E} (h : p ∈ dep u v I) : p.2 ∈ value v I :=
  let ⟨i, hi, _, hv⟩ := h; ⟨i, hi, hv⟩

theorem value_mono (h : I ⊆ J) : value u I ⊆ value u J :=
  fun _ ⟨i, hi, hx⟩ ↦ ⟨i, h hi, hx⟩

theorem dep_mono (h : I ⊆ J) : dep u v I ⊆ dep u v J :=
  fun _ ⟨i, hi, hu, hv⟩ ↦ ⟨i, h hi, hu, hv⟩

/-- Where every row valuing `u` also values `v`, the values of `u` are the domain of the
dependency between them. -/
theorem dom_dep (h : ∀ i ∈ I, RegisterStructure.val u i ≠ ⊥ → RegisterStructure.val v i ≠ ⊥) :
    (dep u v I).dom = value u I := by
  refine Set.ext fun x ↦ ⟨fun ⟨y, hp⟩ ↦ fst_mem_value_of_mem_dep hp, fun ⟨i, hi, hx⟩ ↦ ?_⟩
  obtain ⟨y, hy⟩ := Flat.ne_bot_iff_exists.1 (h i hi (hx ▸ Flat.coe_ne_bot))
  exact ⟨y, i, hi, hx, hy⟩

/-- Where every row valuing `v` also values `u`, the values of `v` are the codomain of the
dependency between them. -/
theorem cod_dep (h : ∀ i ∈ I, RegisterStructure.val v i ≠ ⊥ → RegisterStructure.val u i ≠ ⊥) :
    (dep u v I).cod = value v I := by
  refine Set.ext fun y ↦ ⟨fun ⟨x, hp⟩ ↦ snd_mem_value_of_mem_dep hp, fun ⟨i, hi, hy⟩ ↦ ?_⟩
  obtain ⟨x, hx⟩ := Flat.ne_bot_iff_exists.1 (h i hi (hy ▸ Flat.coe_ne_bot))
  exact ⟨x, i, hi, hx, hy⟩

/-- On plural partial assignments, a cell is [spector-2026]'s restriction `G_{x=a}`. -/
theorem cell_eq_restrict {Var D : Type*} [DecidableEq Var] (G : PluralAssign Var D) (x : Var)
    (a : D) : cell x a G = G.restrict x a :=
  rfl

/-- On plural partial assignments, a dref's values are `PluralAssign.value`. -/
theorem value_eq_pluralAssign_value {Var D : Type*} [DecidableEq Var] (G : PluralAssign Var D)
    (x : Var) : value x G = G.value x :=
  rfl

/-! ### Dref introduction and conditions -/

/-- Dref introduction `[u]` ([brasoveanu-2010] (18)): the cumulative lift of CDRT's random
assignment. -/
def intro (u : R) : Update (Set S) := cumul (randomAssign u)

/-- Introducing `u` at a one-row state can give it any value. -/
theorem singleton_mem_intro (i : S) (u : R) (e : Flat E) :
    {i} ~[intro u] {RegisterStructure.extend i u e} :=
  ⟨fun _ hi ↦ ⟨_, rfl, e, by rw [hi]⟩, fun _ hj ↦ ⟨i, rfl, e, by rw [hj]⟩⟩

/-- The lift of an update that fixes `v` leaves `v`'s values alone. -/
theorem value_eq_of_fixes {D : Update S} (h : Fixes v D) (hIJ : I ~[cumul D] J) :
    value v J = value v I := by
  ext x
  constructor
  · rintro ⟨j, hj, hx⟩
    obtain ⟨i, hi, hij⟩ := hIJ.2 j hj
    exact ⟨i, hi, (h i j hij) ▸ hx⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨j, hj, hij⟩ := hIJ.1 i hi
    exact ⟨j, hj, (h i j hij).symm ▸ hx⟩

/-- Introducing `u` leaves every other dref's values alone. -/
theorem value_intro_of_ne (h : v ≠ u) (hIJ : I ~[intro u] J) : value v J = value v I :=
  value_eq_of_fixes (fixes_randomAssign_of_ne h) hIJ

/-- A unary atomic condition `P{u}` ((30)) holds when `u` has values and all of them satisfy
`P`. -/
def atom (P : E → Prop) (u : R) : Condition (Set S) :=
  {I | (value u I).Nonempty ∧ ∀ x ∈ value u I, P x}

/-- A binary atomic condition `P{u, v}` ((32)) holds when some row values both drefs and the
values in every such row are related by `P`. -/
def atom₂ (P : E → E → Prop) (u v : R) : Condition (Set S) :=
  {I | (dep u v I).Nonempty ∧ ∀ p ∈ dep u v I, P p.1 p.2}

/-- Singular number `sing(u)` ((39)) holds when `u` has exactly one value. -/
def sing (u : R) : Condition (Set S) := {I | ∃ x, value u I = {x}}

/-- On plural partial assignments, singular number is [spector-2026]'s `atomic(x)`, a single
value. -/
theorem mem_sing_iff {Var D : Type*} [DecidableEq Var] {G : PluralAssign Var D} {x : Var} :
    G ∈ sing x ↔ ∃ d, G.value x = {d} :=
  Iff.rfl

/-! ### Structured inclusion -/

/-- Structured inclusion `u' ⋐ u` ((66)) holds when in every row `u'` has `u`'s value or ★. -/
def structSub (u' u : R) : Condition (Set S) :=
  {I | ∀ i ∈ I, RegisterStructure.val u' i = RegisterStructure.val u i ∨
    RegisterStructure.val u' i = ⊥}

/-- Full structured inclusion `u' ⊑ u` ((68)) is structured inclusion that also keeps every row
in which `u` has one of `u'`'s values. -/
def structSubAll (u' u : R) : Condition (Set S) :=
  {I | I ∈ structSub u' u ∧ ∀ i ∈ I, ∀ x ∈ value u' I,
    RegisterStructure.val u i = ↑x → RegisterStructure.val u' i = ↑x}

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

end PCDRT
