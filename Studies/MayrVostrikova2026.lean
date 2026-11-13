module

public import Linglib.Core.Order.Minimal
public import Linglib.Semantics.Degree.Quantifier
public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.Quantification.Exceptive
public import Linglib.Data.Examples.MayrVostrikova2026

/-!
# Mayr & Vostrikova (2026): Exceptive-additive *besides*

*Every student besides Ann passed* conveys that Ann did not pass, as the exceptive *but* does,
while *some student besides Ann passed* and *at most two students besides Ann passed*, where *but*
is unacceptable, convey that she did. Mayr and Vostrikova derive both inferences from one entry.
*Besides* and *but* subtract from the restrictor and are exhaustified, and they differ in their
alternatives: *but* is exhaustified against the subtractions of the other individuals, *besides*
against the subtractions of the proper parts of what it subtracts, for an atom the quantification
with nothing subtracted. Where subtracting an atom does not entail that alternative, *besides*
says that the quantification holds without the atom and fails with it. With *every* [the scope
then fails of the atom](##MayrVostrikova2026.besides_subset_sdiff), and with *no* and *exactly n*
[it holds of it](##MayrVostrikova2026.besides_subset_inter); with *every* and *no*, for an atom
or a plurality, this is [the least exception set of
*but*](##MayrVostrikova2026.mem_besides_every_iff). With *some* and *at
least n* the subtraction does entail the alternative and the exhaustification [is
idle](##MayrVostrikova2026.besides_eq_of_restrictorMonotone), which a ban on idle exhaustification
excludes. A modified numeral is a quantifier over degrees above a constituent that says the count
is exactly a degree, and *besides* is exhaustified there, below the numeral: [so many of the
others, and the atom as well](##MayrVostrikova2026.mem_besidesNumeral_iff). In a model where
everyone is a student and any set of them may have passed, *but* with *some* is
[contradictory](##MayrVostrikova2026.but_some_eq_empty) once two other individuals are
alternatives, and *but* with *no* or *every*, exhaustified against every subtraction, holds
[where the excepted set is the least exception set](##MayrVostrikova2026.mem_but_univ_no_iff) of
[von-fintel-1993]. For collective predicates the constituent under the numeral is the
informativity-based maximality of [buccola-spector-2016], which over a distributive predicate
[picks the greatest degree](##MayrVostrikova2026.isMaxInf_iff_isGreatest) and over a predicate
with no entailments between degrees picks every true one, so that there the exhaustification of
*besides* [is idle again](##MayrVostrikova2026.exh_isMaxInf_eq_self).

## Implementation notes

* Restrictor and scope are functions from worlds to sets, and the alternatives of an exceptive
  are given by the sets they subtract, so *besides* is *but* over the proper parts of its
  exception set (`Set.Iio`). These are the paper's semantic alternatives for an atom and for a
  plurality; it does not commit to how they are generated.
* The statements for *every*, *no* and *exactly n* are instances of the library's
  `Exceptive.Restrictive.sdiff_nonempty` and `Exceptive.Restrictive.inter_nonempty` for
  co-intersective and intersective determiners, a classification the paper does not use.
* The operator is `Exhaustification.exh`, which denies the alternatives the prejacent does not
  entail and can contradict it, the paper's choice over innocent exclusion.
* Containment, that the excepted individual is in the restrictor, is a definedness condition of
  the paper's entry. It is not formalized; where the subtraction does not entail the alternative
  it is entailed by the exhaustified meaning.
* The constituent under a modified numeral, the paper's `MAX` over the silent *many*, is
  `Det.exactly`, and the numeral is `Quantifier.MaxIn` at the set of degrees it admits.

## TODO

* Existential determiners and *wh*-phrases, where `MAX` ranges over pluralities.
* *Sufficient* and *can*, and collective predicates with entailments between degrees, as
  *gather*.
* The comparison with innocent exclusion on *some student but Ann and Bill*.
* *Most* and *many*, the definite, and *zero*.

## References

* [mayr-vostrikova-2026]
* [von-fintel-1993]
* [buccola-spector-2016]
* [keenan-1987]
-/

@[expose] public section

namespace MayrVostrikova2026

open Quantifier Quantifier.Det Quantifier.Exceptive Exhaustification Set

variable {α W : Type*} {Q : Det α} {A B : W → Set α} {C : Set α} {a : α} {w : W}

/-! ### The two exceptives -/

/-- (10), (15): *but* exhaustifies the subtraction of `C` against the subtractions of the sets in
`F`, those its focus alternatives name. -/
def but (F : Set (Set α)) (Q : Det α) (A B : W → Set α) (C : Set α) : Set W :=
  exh (subtraction Q A B '' F) (subtraction Q A B C)

/-- (40b), (44): *besides* exhaustifies the subtraction of `C` against the subtractions of its
proper parts. -/
def besides (Q : Det α) (A B : W → Set α) (C : Set α) : Set W := but (Iio C) Q A B C

-- (41), (46c)
theorem besides_singleton :
    besides Q A B {a} = exh {subtraction Q A B ∅} (subtraction Q A B {a}) := by
  rw [besides, but, show Iio ({a} : Set α) = {∅} from Set.ext fun _ ↦ ssubset_singleton_iff,
    image_singleton]

-- (42), (47), (55)
theorem mem_besides_singleton_iff (h : ¬ subtraction Q A B {a} ⊆ subtraction Q A B ∅) :
    w ∈ besides Q A B {a} ↔ Restrictive Q (A w) {a} (B w) := by
  rw [besides_singleton, exh_singleton_subtraction_empty h]
  rfl

/-! ### Exception and addition -/

/-- Under an intersective determiner, *no*, *exactly n*, *besides* an atom conveys that the
scope holds of it, the additive inference. -/
theorem besides_subset_inter (hQ : Q.Intersective)
    (h : ¬ subtraction Q A B {a} ⊆ subtraction Q A B ∅) (hw : w ∈ besides Q A B {a}) :
    a ∈ A w ∩ B w :=
  let ⟨_, ⟨hA, rfl⟩, hB⟩ := ((mem_besides_singleton_iff h).1 hw).inter_nonempty hQ
  ⟨hA, hB⟩

/-- Under a co-intersective determiner, *every*, *besides* an atom conveys that the scope fails
of it, the exceptive inference. -/
theorem besides_subset_sdiff (hQ : Q.CoIntersective)
    (h : ¬ subtraction Q A B {a} ⊆ subtraction Q A B ∅) (hw : w ∈ besides Q A B {a}) :
    a ∈ A w \ B w :=
  let ⟨_, ⟨hA, rfl⟩, hB⟩ := ((mem_besides_singleton_iff h).1 hw).sdiff_nonempty hQ
  ⟨hA, hB⟩

-- (42), (45), `Examples.ex_1_besides`, `Examples.ex_43a`: with *every*, *besides* a set that
-- entails none of its alternatives names the least exception set of [von-fintel-1993]'s *but*
theorem mem_besides_every_iff
    (h : ∀ S < C, ¬ subtraction every A B C ⊆ subtraction every A B S) :
    w ∈ besides every A B C ↔ IsExceptionSet every (A w) C (B w) :=
  (mem_exh_image_Iio_subtraction_iff h).trans minimal_every_iff

-- (47), `Examples.ex_2_besides`
theorem mem_besides_no_iff (h : ∀ S < C, ¬ subtraction no A B C ⊆ subtraction no A B S) :
    w ∈ besides no A B C ↔ IsExceptionSet no (A w) C (B w) :=
  (mem_exh_image_Iio_subtraction_iff h).trans minimal_no_iff

/-- Under a left-upward-monotone determiner, *some*, *at least n*, every alternative of *besides*
is entailed and its exhaustification is idle ((56)–(58)). -/
theorem besides_eq_of_restrictorMonotone (hQ : RestrictorMonotone Q) :
    besides Q A B C = subtraction Q A B C :=
  exh_image_Iio_of_antitone (subtraction_anti hQ) C

/-! ### Modified numerals -/

/-- (64), (73b), (76b): under a modified numeral admitting the degrees `U`, *besides* is
exhaustified on the constituent that says the count is exactly a degree. -/
def besidesNumeral (U : Set ℕ) (A B : W → Set α) (C : Set α) : Set W :=
  {w | MaxIn U {m | w ∈ besides (exactly m) A B C}}

/-- A modified numeral with *besides* an atom says that the others in the scope number as the
numeral admits and that the scope holds of the atom, for every numeral ((69), (75), (77)). -/
theorem mem_besidesNumeral_iff {U : Set ℕ} {k : ℕ} (hfin : (A w).Finite)
    (hk : ((A w \ {a}) ∩ B w).ncard = k)
    (h : ¬ subtraction (exactly k) A B {a} ⊆ subtraction (exactly k) A B ∅) :
    w ∈ besidesNumeral U A B {a} ↔ k ∈ U ∧ a ∈ A w ∩ B w := by
  have hm {m : ℕ} (hw : w ∈ besides (exactly m) A B {a}) : m = k :=
    (show exactly m (A w \ {a}) (B w) from hw.1).symm.trans hk
  refine ⟨fun ⟨m, hm, hw, _⟩ ↦ ?_, fun ⟨hU, ha⟩ ↦
    ⟨k, hU, (mem_besides_singleton_iff h).2 ⟨hk, ?_⟩, fun _ hw ↦ (hm hw).le⟩⟩
  · obtain rfl : k = m := hk.symm.trans (show exactly m (A w \ {a}) (B w) from hw.1)
    exact ⟨hm, besides_subset_inter (intersective_exactly k) h hw⟩
  · rw [exactly_apply, ← hk, ← inter_sdiff_right_comm]
    exact (ncard_sdiff_singleton_lt_of_mem ha (hfin.inter_of_left _)).ne'

/-! ### A model: everyone is a student, and a world is the set of those who passed -/

section Existential

variable [DecidableEq α] {F : Set (Set α)} {b c : α}

-- the non-entailment hypothesis holds once some `k` others can pass together with the atom
theorem not_subtraction_exactly_subset {s : Finset α} (ha : a ∉ s) :
    ¬ subtraction (exactly s.card) (fun _ : Finset α ↦ univ) (fun w ↦ (w : Set α)) {a} ⊆
      subtraction (exactly s.card) (fun _ ↦ univ) (fun w ↦ (w : Set α)) ∅ := fun h ↦ by
  have key : (univ \ {a}) ∩ (↑(insert a s) : Set α) = ↑s := by
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_univ, mem_singleton_iff, true_and, Finset.coe_insert,
      mem_insert_iff, Finset.mem_coe]
    exact ⟨fun ⟨hx, hx'⟩ ↦ hx'.resolve_left hx, fun hx ↦ ⟨fun e ↦ ha (e ▸ hx), .inr hx⟩⟩
  have h' := h (show insert a s ∈ _ from (exactly_apply.2 (by rw [key, ncard_coe_finset])))
  rw [mem_subtraction, sdiff_empty, exactly_apply, univ_inter, ncard_coe_finset,
    Finset.card_insert_of_notMem ha] at h'
  omega

-- (56), `Examples.ex_5_at_least`: Bill passes besides Ann; with Ann failing the sentence is false
example :
    {0, 1} ∈ besidesNumeral (Ici 1) (fun _ ↦ univ)
        (fun w : Finset (Fin 3) ↦ (w : Set (Fin 3))) {0} ∧
      {1} ∉ besidesNumeral (Ici 1) (fun _ ↦ univ)
        (fun w : Finset (Fin 3) ↦ (w : Set (Fin 3))) {0} := by
  have h := not_subtraction_exactly_subset (a := (0 : Fin 3)) (s := {1}) (by decide)
  have hk : ∀ w : Finset (Fin 3), 1 ∈ w → 2 ∉ w → ((univ \ {0}) ∩ (w : Set (Fin 3))).ncard = 1 :=
    fun w h1 h2 ↦ by
      rw [show (univ \ {0}) ∩ (w : Set (Fin 3)) = {1} from Set.ext fun x ↦ by
        fin_cases x <;> simp [h1, h2]]
      exact ncard_singleton 1
  rw [mem_besidesNumeral_iff (toFinite _) (hk _ (by decide) (by decide)) h,
    mem_besidesNumeral_iff (toFinite _) (hk _ (by decide) (by decide)) h]
  simp

/-- With two other individuals among its alternatives, *some student but Ann* is contradictory:
the one who passed is not excepted by one of the two alternatives, which is then true ((19),
(20), `Examples.ex_3a_but`). -/
theorem but_some_eq_empty (hb : {b} ∈ F) (hc : {c} ∈ F) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    but F Det.some (fun _ : Finset α ↦ univ) (fun w ↦ (w : Set α)) {a} = ∅ := by
  refine eq_empty_of_forall_notMem fun w ⟨⟨x, ⟨_, hxa⟩, hxw⟩, hall⟩ ↦ ?_
  have key : ∀ d, {d} ∈ F → a ≠ d → x ≠ d → False := fun d hd had hxd ↦ by
    obtain ⟨y, ⟨_, hyd⟩, hy⟩ := hall _ ⟨{d}, hd, rfl⟩ ⟨x, ⟨trivial, hxd⟩, hxw⟩
      (show ({d} : Finset α) ∈ _ from ⟨d, ⟨trivial, had.symm⟩, by simp⟩)
    exact hyd (by simpa using hy)
  by_cases hxb : x = b
  · exact key c hc hac (hxb ▸ hbc)
  · exact key b hb hab hxb

omit [DecidableEq α] in
-- (17), (18): against every subtraction, *no student but `C`* names the least exception set
theorem mem_but_univ_no_iff {w : Finset α} :
    w ∈ but univ no (fun _ : Finset α ↦ univ) (fun w ↦ (w : Set α)) C ↔
      IsExceptionSet no univ C ↑w := by
  rw [but, image_univ]
  refine mem_exh_range_subtraction_iff fun S ↦
    ⟨fun h c hc ↦ by_contra fun hcS ↦ ?_, fun h ↦ subtraction_mono restrictorAntitone_no h⟩
  exact h (show ({c} : Finset α) ∈ _ from fun x hx hxc ↦
    hx.2 (Finset.mem_singleton.1 (Finset.mem_coe.1 hxc) ▸ hc)) ⟨trivial, hcS⟩ (by simp)

-- (10), (16)
theorem mem_but_univ_every_iff [Fintype α] {w : Finset α} :
    w ∈ but univ every (fun _ : Finset α ↦ univ) (fun w ↦ (w : Set α)) C ↔
      IsExceptionSet every univ C ↑w := by
  rw [but, image_univ]
  refine mem_exh_range_subtraction_iff fun S ↦
    ⟨fun h c hc ↦ by_contra fun hcS ↦ ?_, fun h ↦ subtraction_mono restrictorAntitone_every h⟩
  have hc' := h (show Finset.univ.erase c ∈ _ from fun x hx ↦
    Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun e ↦ hx.2 (e ▸ hc), Finset.mem_univ x⟩))
    ⟨trivial, hcS⟩
  exact Finset.notMem_erase c _ (Finset.mem_coe.1 hc')

-- fn. 9: with two students the alternatives are consistent with the prejacent
theorem but_some_two_nonempty :
    (but (range singleton) Det.some (fun _ : Finset (Fin 2) ↦ univ) (fun w ↦ (w : Set (Fin 2)))
      {0}).Nonempty := by
  refine ⟨{1}, ⟨1, ⟨trivial, by decide⟩, by simp⟩, ?_⟩
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ ⟨x, ⟨_, hxi⟩, hx⟩
  obtain rfl : x = 1 := by simpa using hx
  obtain rfl : i = 0 := by_contra fun hi ↦ hxi (Fin.eq_one_of_ne_zero i hi).symm
  exact subset_rfl

end Existential

/-! ### Informativity-based maximality -/

section MaxInf

variable {P P' : ℕ → Set W} {k : ℕ}

/-- (122): a degree is maximal for a degree property at a world when the property holds of it
there and of no degree whose proposition is strictly stronger, and zero is maximal where the
property holds of no degree. -/
def IsMaxInf (P : ℕ → Set W) (w : W) (n : ℕ) : Prop :=
  MinimalFor (w ∈ P ·) P n ∨ n = 0 ∧ ∀ d, w ∉ P d

-- (125a): over a distributive predicate the maximal degree is the greatest
theorem isMaxInf_iff_isGreatest (hP : StrictAnti P) (h : ∃ d, w ∈ P d) :
    IsMaxInf P w k ↔ IsGreatest {d | w ∈ P d} k :=
  (or_iff_left fun h' ↦ h.elim h'.2).trans hP.minimalFor_iff_isGreatest

-- (129), (130): with no entailments between degrees, a nonzero maximal degree of the subtracted
-- property is one of the unsubtracted property, and *besides* has nothing to deny
theorem exh_isMaxInf_eq_self (hsub : ∀ d, P' d ⊆ P d) (hP : ∀ m n, ¬ P m ⊂ P n) (hk : k ≠ 0) :
    exh {{w | IsMaxInf P w k}} {w | IsMaxInf P' w k} = {w | IsMaxInf P' w k} :=
  exh_eq_self <| by
    rintro _ rfl w hw
    exact .inl ((minimalFor_iff_of_forall_not_lt hP).2
      (hsub k (hw.resolve_right fun h ↦ hk h.1).1))

end MaxInf

end MayrVostrikova2026
