module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Quantification.Exceptive
public import Linglib.Data.Examples.MayrVostrikova2026

/-!
# Mayr & Vostrikova (2026): Exceptive-additive *besides*

*Besides* conveys an exception with *every*, as *but* does, and an addition with the determiners
*but* rejects. Mayr and Vostrikova give it the subtraction and exhaustification of *but* with
other alternatives, the subtractions of the proper parts of what it subtracts. Where its
subtraction entails none of these, *besides* [names a minimal verifying
subtraction](##MayrVostrikova2026.mem_besides_iff): with *every* and *no* [the least exception
set](##MayrVostrikova2026.mem_besides_every_iff), and for an atom under an intersective determiner
[something in the scope](##MayrVostrikova2026.mem_inter_of_mem_besides). Under *some* it [is
idle](##MayrVostrikova2026.besides_eq_of_restrictorMonotone), and below a modified numeral it [adds
the atom to the count of the others](##MayrVostrikova2026.mem_besidesNumeral_iff).

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
  `Det.exactly`, which agrees with it where the restrictor and scope share finitely many
  individuals, and the numeral is `Quantifier.MaxIn` at the set of degrees it admits.
* Informativity-based maximality is `MinimalFor` with a degree's proposition as its key. The
  clause of the paper and of [buccola-spector-2016] making zero maximal where the property holds
  of no degree is not formalized, so the paper's separate treatment of degree zero under a
  collective predicate is not either.
* In the model a world is the finite set of those who passed.

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

-- (42), (45), (47), (55): where the subtraction entails none of its alternatives, *besides* says
-- that `C` is a minimal set whose subtraction verifies the quantification
theorem mem_besides_iff (h : ∀ S < C, ¬ subtraction Q A B C ⊆ subtraction Q A B S) :
    w ∈ besides Q A B C ↔ Minimal (fun S ↦ Q (A w \ S) (B w)) C :=
  mem_exh_image_Iio_subtraction_iff h

/-! ### Exception and addition -/

/-- Under an intersective determiner, *no*, *exactly n*, *besides* an atom whose subtraction does
not entail the unsubtracted quantification conveys that the scope holds of it, the additive
inference. -/
theorem mem_inter_of_mem_besides (hQ : Q.Intersective)
    (h : ∀ S < ({a} : Set α), ¬ subtraction Q A B {a} ⊆ subtraction Q A B S)
    (hw : w ∈ besides Q A B {a}) : a ∈ A w ∩ B w :=
  let ⟨_, hAB, rfl⟩ :=
    (restrictive_singleton_iff_minimal.2 ((mem_besides_iff h).1 hw)).inter_nonempty hQ
  hAB

/-- Under a co-intersective determiner, *every*, *besides* an atom whose subtraction does not
entail the unsubtracted quantification conveys that the scope fails of it, the exceptive
inference. -/
theorem mem_sdiff_of_mem_besides (hQ : Q.CoIntersective)
    (h : ∀ S < ({a} : Set α), ¬ subtraction Q A B {a} ⊆ subtraction Q A B S)
    (hw : w ∈ besides Q A B {a}) : a ∈ A w \ B w :=
  let ⟨_, hAB, rfl⟩ :=
    (restrictive_singleton_iff_minimal.2 ((mem_besides_iff h).1 hw)).sdiff_nonempty hQ
  hAB

-- (42), (45), `Examples.ex_1_besides`, `Examples.ex_43a`: with *every*, *besides* a set whose
-- subtraction entails none of its alternatives names the least exception set of
-- [von-fintel-1993]'s *but*
theorem mem_besides_every_iff
    (h : ∀ S < C, ¬ subtraction every A B C ⊆ subtraction every A B S) :
    w ∈ besides every A B C ↔ IsExceptionSet every (A w) C (B w) :=
  (mem_besides_iff h).trans minimal_every_iff

-- (47), `Examples.ex_2_besides`
theorem mem_besides_no_iff (h : ∀ S < C, ¬ subtraction no A B C ⊆ subtraction no A B S) :
    w ∈ besides no A B C ↔ IsExceptionSet no (A w) C (B w) :=
  (mem_besides_iff h).trans minimal_no_iff

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

-- the exhaustified constituent holds of one degree at most, the count of the others
theorem ncard_eq_of_mem_besides_exactly {m : ℕ} (hw : w ∈ besides (exactly m) A B C) :
    ((A w \ C) ∩ B w).ncard = m :=
  hw.1

/-- Where subtracting the atom does not entail the unsubtracted count, a modified numeral with
*besides* says that the others in the scope number as the numeral admits and that the scope holds
of the atom, whichever degrees the numeral admits ((69), (75), (77)). -/
theorem mem_besidesNumeral_iff {U : Set ℕ} {k : ℕ} (hfin : (A w).Finite)
    (h : ∀ S < ({a} : Set α), ¬ subtraction (exactly k) A B {a} ⊆ subtraction (exactly k) A B S)
    (hk : ((A w \ {a}) ∩ B w).ncard = k) :
    w ∈ besidesNumeral U A B {a} ↔ k ∈ U ∧ a ∈ A w ∩ B w := by
  refine ⟨fun ⟨m, hm, hw, _⟩ ↦ ?_, fun ⟨hU, ha⟩ ↦ ⟨k, hU, ?_, fun m hw ↦
    ((ncard_eq_of_mem_besides_exactly hw).symm.trans hk).le⟩⟩
  · obtain rfl : m = k := (ncard_eq_of_mem_besides_exactly hw).symm.trans hk
    exact ⟨hm, mem_inter_of_mem_besides (intersective_exactly m) h hw⟩
  · refine (mem_besides_iff h).2 (restrictive_singleton_iff_minimal.1 ⟨hk, ?_⟩)
    rw [exactly_apply, ← hk, ← inter_sdiff_right_comm]
    exact (ncard_sdiff_singleton_lt_of_mem ha (hfin.inter_of_left _)).ne'

/-! ### A model -/

section Model

/-- Everyone is a student. -/
abbrev students : Finset α → Set α := fun _ ↦ univ

/-- A world is the set of those who passed. -/
abbrev passed : Finset α → Set α := (↑)

variable {F : Set (Set α)} {b c : α}

theorem ncard_others [DecidableEq α] (w : Finset α) :
    ((students w \ {a}) ∩ passed w).ncard = (w.erase a).card := by
  rw [← inter_sdiff_right_comm, univ_inter, ← Finset.coe_erase, ncard_coe_finset]

-- subtracting an atom entails none of its alternatives once `k` others can pass together with it
theorem not_subtraction_exactly_subset [DecidableEq α] {s : Finset α} (ha : a ∉ s) :
    ∀ S < ({a} : Set α), ¬ subtraction (exactly s.card) students passed {a} ⊆
      subtraction (exactly s.card) students passed S := fun S hS h ↦ by
  obtain rfl := ssubset_singleton_iff.1 hS
  have h' := h (show insert a s ∈ subtraction (exactly s.card) students passed {a} from
    (ncard_others _).trans (by rw [Finset.erase_insert ha]))
  rw [mem_subtraction, sdiff_empty, exactly_apply] at h'
  change (univ ∩ (↑(insert a s) : Set α)).ncard = s.card at h'
  rw [univ_inter, ncard_coe_finset, Finset.card_insert_of_notMem ha] at h'
  omega

-- (5), `Examples.ex_5_at_least`: Bill passes besides Ann; with Ann failing the sentence is false
example : {0, 1} ∈ besidesNumeral (Ici 1) students (passed (α := Fin 3)) {0} ∧
    {1} ∉ besidesNumeral (Ici 1) students (passed (α := Fin 3)) {0} := by
  have h := not_subtraction_exactly_subset (a := (0 : Fin 3)) (s := {1}) (by decide)
  rw [mem_besidesNumeral_iff (toFinite _) h ((ncard_others _).trans (by decide)),
    mem_besidesNumeral_iff (toFinite _) h ((ncard_others _).trans (by decide))]
  simp

/-- With two other individuals among its alternatives, *some student but Ann* is contradictory:
the one who passed is not excepted by one of the two alternatives, which is then true ((19),
(20), `Examples.ex_3a_but`). -/
theorem but_some_eq_empty (hb : {b} ∈ F) (hc : {c} ∈ F) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : but F Det.some students passed {a} = ∅ := by
  refine eq_empty_of_forall_notMem fun w ⟨⟨x, ⟨_, hxa⟩, hxw⟩, hall⟩ ↦ ?_
  have key : ∀ d, {d} ∈ F → a ≠ d → x ≠ d → False := fun d hd had hxd ↦ by
    obtain ⟨y, ⟨_, hyd⟩, hy⟩ := hall _ ⟨{d}, hd, rfl⟩ ⟨x, ⟨trivial, hxd⟩, hxw⟩
      (show ({d} : Finset α) ∈ _ from ⟨d, ⟨trivial, had.symm⟩, by simp⟩)
    exact hyd (by simpa using hy)
  by_cases hxb : x = b
  · exact key c hc hac (hxb ▸ hbc)
  · exact key b hb hab hxb

-- (17), (18): against every subtraction, *no student but `C`* names the least exception set
theorem mem_but_univ_no_iff {w : Finset α} :
    w ∈ but univ no students passed C ↔ IsExceptionSet no univ C ↑w := by
  rw [but, image_univ]
  refine mem_exh_range_subtraction_iff fun S ↦
    ⟨fun h c hc ↦ by_contra fun hcS ↦ ?_, fun h ↦ subtraction_mono restrictorAntitone_no h⟩
  exact h (show ({c} : Finset α) ∈ _ from fun x hx hxc ↦
    hx.2 (Finset.mem_singleton.1 (Finset.mem_coe.1 hxc) ▸ hc)) ⟨trivial, hcS⟩ (by simp)

-- (10), (16)
theorem mem_but_univ_every_iff [Fintype α] [DecidableEq α] {w : Finset α} :
    w ∈ but univ every students passed C ↔ IsExceptionSet every univ C ↑w := by
  rw [but, image_univ]
  refine mem_exh_range_subtraction_iff fun S ↦
    ⟨fun h c hc ↦ by_contra fun hcS ↦ ?_, fun h ↦ subtraction_mono restrictorAntitone_every h⟩
  have hc' := h (show Finset.univ.erase c ∈ _ from fun x hx ↦
    Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun e ↦ hx.2 (e ▸ hc), Finset.mem_univ x⟩))
    ⟨trivial, hcS⟩
  exact Finset.notMem_erase c _ (Finset.mem_coe.1 hc')

-- fn. 9: with two students the alternatives are consistent with the prejacent
theorem but_some_two_nonempty :
    (but (range singleton) Det.some students (passed (α := Fin 2)) {0}).Nonempty := by
  refine ⟨{1}, ⟨1, ⟨trivial, by decide⟩, by simp⟩, ?_⟩
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ ⟨x, ⟨_, hxi⟩, hx⟩
  obtain rfl : x = 1 := by simpa using hx
  obtain rfl : i = 0 := by_contra fun hi ↦ hxi (Fin.eq_one_of_ne_zero i hi).symm
  exact subset_rfl

end Model

/-! ### Informativity-based maximality -/

-- (129), (130): where no degree that holds somewhere has a proposition strictly stronger than
-- that of `k`, a maximal `k` of the subtracted property is maximal for the unsubtracted one, and
-- the alternative of *besides* is entailed
theorem exh_minimalFor_eq_self {P P' : ℕ → Set W} {k : ℕ} (hsub : P' k ⊆ P k)
    (hP : ∀ m, (P m).Nonempty → ¬ P m ⊂ P k) :
    exh {{w | MinimalFor (w ∈ P ·) P k}} {w | MinimalFor (w ∈ P' ·) P' k} =
      {w | MinimalFor (w ∈ P' ·) P' k} :=
  exh_eq_self <| by
    rintro _ rfl w hw
    exact ⟨hsub hw.1, fun j hj ↦ not_lt_iff_le_imp_ge.1 (hP j ⟨w, hj⟩)⟩

-- the first hypothesis for (129): a group of `d` students without John is a group of `d` students
example {G : W → Set (Finset α)} (d : ℕ) :
    {w | ∃ X ∈ G w, ↑X ⊆ A w \ C ∧ X.card = d} ⊆ {w | ∃ X ∈ G w, ↑X ⊆ A w ∧ X.card = d} :=
  fun _ ⟨X, hX, hXA, hd⟩ ↦ ⟨X, hX, hXA.trans sdiff_subset, hd⟩

end MayrVostrikova2026
