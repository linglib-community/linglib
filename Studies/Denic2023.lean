module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# Denić (2023): Probabilities and logic in implicature computation

This file formalizes the two puzzles with embedded disjunction of [denic-2023] and their
resolution. *All 20 of Mary's friends are French or Spanish* preferably triggers the
distributive inferences that at least one is French and at least one is Spanish, while *Both of
Mary's friends are French or Spanish* preferably triggers ignorance about them, (6) and (7), and
fewer disjuncts likewise favour the distributive reading, (8) and (9). Under the exhaustification
of [fox-2007], the distributive reading arises when only the disjunction activates its
alternatives, ALT-or, all of which are innocently excludable, and the ignorance reading when the
quantifier does too, ALT-all-or, none of whose alternatives is, (26); since the alternatives
stand in the same entailment relations for any domain size, §3.2, no theory on which
implicatures are a function of entailment can distinguish the two sentences, and the pruning
constraints of [fox-katzir-2011] do not either, §3.3. The proposal, (30), is that an alternative
is pruned the more likely it is given the utterance: with each individual one of the m
properties at random, the probability that some of n individuals is A given that all are one of
the m is `1 − ((m − 1)/m)^n`, increasing in n and decreasing in m, and larger than that of the
universal alternative once n > 1, the assumptions of §4; a threshold on it prunes the existential
alternatives of (6) and (8) but not of (7) and (9). The deviance puzzle, §5, is that *#Each of
those three girls is Mary, Susan, or Jane* is degraded where *is called* is not: the identity
predicate is singleton-denoting, so given common knowledge the three names are borne by the three
girls one each, every existential alternative is settled, and the ignorance inferences the
sentence triggers contradict common knowledge, (40), the blindness of [magri-2009] extended from
scalar to ignorance inferences. Informativeness must then be computed blindly too, §7.3: given
common knowledge the existential alternatives of the deviant sentence are certain and would be
pruned, whereas blind to it their probability lies below every threshold that resolves the
inference puzzle.

## Implementation notes

Worlds assign each of the n individuals exactly one of the m properties, the uniform prior of
§4's assumptions; the prejacent *all are one of them* is then every world, and the conjunctive
alternatives of the chapter's footnote 8, which it sets aside, are unsatisfiable. The
exhaustification results are the substrate's innocent exclusion over sets of worlds, stated for
every n ≥ 2 and m ≥ 2, the distributive reading itself for two disjuncts. Probabilities are the
uniform measure `uniformOn` on reals. The mapping from conditional probability to pruning, which
the chapter leaves open between a linear and a threshold form, is taken as a threshold. Ignorance
inferences are the pragmatic ones of §3.1, about every alternative the exhaustified utterance
leaves open, so the grammatical parse of §7.1 is not modelled. The modified-numeral cases of
[buccola-haida-2019], (43), and the symmetry, modal and downward-entailing challenges of §8 are
recorded in the data only.

## References

* [denic-2023]
* [fox-2007]
* [fox-katzir-2011]
* [magri-2009]
* [buccola-haida-2019]
-/

@[expose] public section

namespace Denic2023

open Exhaustification MeasureTheory ProbabilityTheory

/-- In the worlds for *all of n are A₁ or … or Aₘ* each individual has exactly one of the `m`
properties. -/
abbrev World (n m : ℕ) := Fin n → Fin m

variable {n m : ℕ}

/-- *All n are Aᵢ*, the universal alternative. -/
def allAre (i : Fin m) : Set (World n m) := {w | ∀ x, w x = i}

/-- *Some of the n are Aᵢ*, the existential alternative. -/
def someAre (i : Fin m) : Set (World n m) := {w | ∃ x, w x = i}

/-- Under ALT-or only the disjunction activates its alternatives, (24) and (25). -/
def altOr (n m : ℕ) : Set (Set (World n m)) := Set.range allAre

/-- Under ALT-all-or the quantifier activates its alternatives too, (22) and (23). -/
def altAllOr (n m : ℕ) : Set (Set (World n m)) := Set.range allAre ∪ Set.range someAre

theorem altAllOr_finite : (altAllOr n m).Finite := (Set.finite_range _).union (Set.finite_range _)

/-- The exhaustified utterance leaves an alternative open, entailing neither it nor its
negation, so that the maxim of quantity, (19), yields ignorance about it, §3.1. -/
def LeavesOpen (ALT : Set (Set (World n m))) (a : Set (World n m)) : Prop :=
  (exhIE ALT Set.univ ∩ a).Nonempty ∧ (exhIE ALT Set.univ ∩ aᶜ).Nonempty

/-! ### Entailment cannot tell the sentences apart, §3.2 -/

theorem isInnocentlyExcludable_altOr (hn : 2 ≤ n) (hm : 2 ≤ m) (i : Fin m) :
    IsInnocentlyExcludable (altOr n m) Set.univ (allAre i) :=
  IsInnocentlyExcludable.of_full_exclusion_consistent ⟨i, rfl⟩
    ⟨fun x ↦ if x.val = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩, trivial, by
      rintro _ ⟨j, rfl⟩ h
      have h0 := h ⟨0, by omega⟩
      have h1 := h ⟨1, by omega⟩
      rw [← h0] at h1
      simp at h1⟩

/-- Exhaustifying with ALT-or over two disjuncts gives the distributive reading (6a), that some
are French and some are Spanish. -/
theorem exhIE_altOr (hn : 2 ≤ n) : exhIE (altOr n 2) Set.univ = someAre 0 ∩ someAre 1 := by
  have h2 : ∀ j : Fin 2, j ≠ 1 → j = 0 := by decide
  have h2' : ∀ j : Fin 2, j ≠ 0 → j = 1 := by decide
  ext w
  constructor
  · intro h
    have h0 := h.2 _ (isInnocentlyExcludable_altOr hn le_rfl 0)
    have h1 := h.2 _ (isInnocentlyExcludable_altOr hn le_rfl 1)
    obtain ⟨x, hx⟩ := not_forall.1 (h0 : ¬ ∀ x, w x = 0)
    obtain ⟨y, hy⟩ := not_forall.1 (h1 : ¬ ∀ x, w x = 1)
    exact ⟨⟨y, h2 _ hy⟩, ⟨x, h2' _ hx⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨trivial, fun a ha hall ↦ ?_⟩
    obtain ⟨i, rfl⟩ := ha.1
    exact absurd (((hall x).symm.trans hx).symm.trans ((hall y).symm.trans hy)) (by decide)

/-- With ALT-or the existential alternatives are entailed, so no ignorance arises about
them, (6b). -/
theorem exhIE_altOr_subset_someAre (hn : 2 ≤ n) (i : Fin 2) :
    exhIE (altOr n 2) Set.univ ⊆ someAre i := by
  rw [exhIE_altOr hn]
  fin_cases i
  · exact Set.inter_subset_left
  · exact Set.inter_subset_right

theorem const_mem_exhMW (hn : 1 ≤ n) (i : Fin m) :
    (fun _ ↦ i : World n m) ∈ exhMW (altAllOr n m) Set.univ := by
  refine ⟨trivial, ?_⟩
  rintro ⟨v, -, hle, hnle⟩
  apply hnle
  rintro a (⟨j, rfl⟩ | ⟨j, rfl⟩) hu
  · obtain rfl : j = i := (hu ⟨0, by omega⟩).symm
    intro x
    by_contra hx
    obtain ⟨y, hy⟩ := hle _ (Or.inr ⟨v x, rfl⟩) ⟨x, rfl⟩
    exact hx hy.symm
  · obtain rfl : j = i := by obtain ⟨x, hx⟩ := hu; exact hx.symm
    refine ⟨⟨0, by omega⟩, ?_⟩
    by_contra hx
    obtain ⟨y, hy⟩ := hle _ (Or.inr ⟨v ⟨0, by omega⟩, rfl⟩) ⟨_, rfl⟩
    exact hx hy.symm

theorem split_mem_exhMW (hn : 2 ≤ n) {i k : Fin m} (hik : i ≠ k) :
    (fun x ↦ if x.val = 0 then i else k : World n m) ∈ exhMW (altAllOr n m) Set.univ := by
  refine ⟨trivial, ?_⟩
  rintro ⟨v, -, hle, hnle⟩
  apply hnle
  have hv : ∀ x, v x = i ∨ v x = k := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨y, hy⟩ := hle _ (Or.inr ⟨v x, rfl⟩) ⟨x, rfl⟩
    dsimp only at hy
    split_ifs at hy <;> simp_all
  rintro a (⟨j, rfl⟩ | ⟨j, rfl⟩) hu
  · exfalso
    have h0 := hu ⟨0, by omega⟩
    have h1 := hu ⟨1, by omega⟩
    simp at h0 h1
    exact hik (h0.trans h1.symm)
  · obtain ⟨x, hx⟩ := hu
    dsimp only at hx
    have hj : j = i ∨ j = k := by split_ifs at hx <;> simp_all
    by_contra hv'
    rcases hj with rfl | rfl
    · have hall : ∀ x, v x = k := fun x ↦ (hv x).resolve_left fun h ↦ hv' ⟨x, h⟩
      have h0 := hle _ (Or.inl ⟨k, rfl⟩) hall ⟨0, by omega⟩
      simp at h0
      exact hik h0
    · have hall : ∀ x, v x = i := fun x ↦ (hv x).resolve_right fun h ↦ hv' ⟨x, h⟩
      have h1 := hle _ (Or.inl ⟨i, rfl⟩) hall ⟨1, by omega⟩
      simp at h1
      exact hik h1.symm

/-- With ALT-all-or, no alternative is innocently excludable over any domain of at least two (26).
-/
theorem not_isInnocentlyExcludable_altAllOr (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ∀ a ∈ altAllOr n m, ¬ IsInnocentlyExcludable (altAllOr n m) Set.univ a := by
  rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩) h
  · exact (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (Or.inl ⟨i, rfl⟩)).1 h
      (const_mem_exhMW (by omega) i) (fun _ ↦ rfl)
  · have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
    obtain ⟨k, hk⟩ := exists_ne i
    exact (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (Or.inr ⟨i, rfl⟩)).1 h
      (split_mem_exhMW hn hk.symm) ⟨⟨0, by omega⟩, by simp⟩

theorem exhIE_altAllOr (hn : 2 ≤ n) (hm : 2 ≤ m) : exhIE (altAllOr n m) Set.univ = Set.univ := by
  ext w
  exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨trivial, fun a ha ↦
    absurd ha (not_isInnocentlyExcludable_altAllOr hn hm a ha.1)⟩⟩

/-- With ALT-all-or every alternative is left open, giving ignorance about all of them (7b). -/
theorem leavesOpen_altAllOr (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ∀ a ∈ altAllOr n m, LeavesOpen (altAllOr n m) a := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  simp only [LeavesOpen, exhIE_altAllOr hn hm]
  rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · obtain ⟨k, hk⟩ := exists_ne i
    exact ⟨⟨fun _ ↦ i, trivial, fun _ ↦ rfl⟩,
      ⟨fun x ↦ if x.val = 0 then i else k, trivial, fun h ↦ hk (by simpa using h ⟨1, by omega⟩)⟩⟩
  · obtain ⟨k, hk⟩ := exists_ne i
    exact ⟨⟨fun _ ↦ i, trivial, ⟨0, by omega⟩, rfl⟩, ⟨fun _ ↦ k, trivial, fun ⟨_, h⟩ ↦ hk h⟩⟩

/-! ### Probabilistic informativeness, §4 -/

theorem ncard_someAre_compl (i : Fin m) : (someAre (n := n) i)ᶜ.ncard = (m - 1) ^ n := by
  have : (someAre (n := n) i)ᶜ = {f | ∀ x, f x ≠ i} := by
    ext f; simp [someAre]
  rw [this, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  show Fintype.card {f : World n m // ∀ x, f x ≠ i} = _
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ j ↦ j ≠ i)), Fintype.card_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_fin, Fintype.card_subtype_eq]

theorem ncard_someAre (i : Fin m) : (someAre (n := n) i).ncard = m ^ n - (m - 1) ^ n := by
  have h := Set.ncard_add_ncard_compl (someAre (n := n) i)
  rw [ncard_someAre_compl, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin] at h
  omega

theorem ncard_allAre (i : Fin m) : (allAre (n := n) i).ncard = 1 := by
  rw [show allAre (n := n) i = {fun _ ↦ i} from Set.ext fun w ↦
    ⟨fun h ↦ funext h, fun h x ↦ congrFun h x⟩, Set.ncard_singleton]

/-- Under the uniform prior of §4, some of the n individuals is `Aᵢ` with probability `1 − ((m −
1)/m)^n`. -/
theorem uniformOn_real_someAre (hm : 1 ≤ m) (i : Fin m) :
    (uniformOn (Set.univ : Set (World n m))).real (someAre i) = 1 - ((m - 1 : ℝ) / m) ^ n := by
  rw [uniformOn_real_apply, Set.univ_inter, ncard_someAre, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hle : (m - 1) ^ n ≤ m ^ n := Nat.pow_le_pow_left (Nat.sub_le m 1) n
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hm, Nat.cast_one, sub_div,
    div_self (pow_ne_zero n hm'), div_pow]

theorem uniformOn_real_allAre (i : Fin m) :
    (uniformOn (Set.univ : Set (World n m))).real (allAre i) = (1 / m : ℝ) ^ n := by
  rw [uniformOn_real_apply, Set.univ_inter, ncard_allAre, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, one_div_pow]
  push_cast
  rfl

/-- The more individuals, the likelier that some of them is `Aᵢ`, §4's assumption (i). -/
theorem uniformOn_real_someAre_lt (hm : 2 ≤ m) {n' : ℕ} (h : n < n') (i : Fin m) :
    (uniformOn (Set.univ : Set (World n m))).real (someAre i) <
      (uniformOn (Set.univ : Set (World n' m))).real (someAre i) := by
  rw [uniformOn_real_someAre (by omega), uniformOn_real_someAre (by omega)]
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  refine sub_lt_sub_left (pow_lt_pow_right_of_lt_one₀ ?_ ?_ h) 1
  · apply div_pos <;> linarith
  · rw [div_lt_one (by linarith)]; linarith

/-- With more than one individual, that some of them is `Aᵢ` is likelier than that all are,
§4's assumption (ii). -/
theorem uniformOn_real_allAre_lt_someAre (hn : 2 ≤ n) (hm : 2 ≤ m) (i : Fin m) :
    (uniformOn (Set.univ : Set (World n m))).real (allAre i) <
      (uniformOn (Set.univ : Set (World n m))).real (someAre i) := by
  rw [uniformOn_real_someAre (by omega), uniformOn_real_allAre]
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : (1 / m : ℝ) ^ n < 1 / m :=
    pow_lt_self_of_lt_one₀ (by positivity) (by rw [div_lt_one (by linarith)]; linarith) hn
  have hb : ((m - 1 : ℝ) / m) ^ n < (m - 1) / m :=
    pow_lt_self_of_lt_one₀ (div_pos (by linarith) (by linarith))
      (by rw [div_lt_one (by linarith)]; linarith) hn
  have : (1 / m : ℝ) + (m - 1) / m = 1 := by field_simp; ring
  linarith

/-- The more disjuncts, the less likely that some individual is `A₁`, §4's assumption (iii). -/
theorem uniformOn_real_someAre_anti (hn : 1 ≤ n) (hm : 2 ≤ m) {m' : ℕ} (h : m < m')
    (i : Fin m) (i' : Fin m') :
    (uniformOn (Set.univ : Set (World n m'))).real (someAre i') <
      (uniformOn (Set.univ : Set (World n m))).real (someAre i) := by
  rw [uniformOn_real_someAre (by omega), uniformOn_real_someAre (by omega)]
  have hm₁ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm₂ : (m : ℝ) < m' := by exact_mod_cast h
  refine sub_lt_sub_left (pow_lt_pow_left₀ ?_ (div_nonneg (by linarith) (by linarith))
    (by omega)) 1
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- In the threshold form of (30), an alternative is pruned when its probability given the
utterance reaches the threshold. -/
def Pruned (θ p : ℝ) : Prop := θ ≤ p

/-- One threshold prunes the existential alternatives of all-20-or (6) and simple-disj (8) but keeps
those of all-2-or (7) and complex-disj (9). -/
theorem threshold_separates :
    ∃ θ : ℝ, Pruned θ ((uniformOn (Set.univ : Set (World 20 2))).real (someAre 0)) ∧
      Pruned θ ((uniformOn (Set.univ : Set (World 4 2))).real (someAre 0)) ∧
      ¬ Pruned θ ((uniformOn (Set.univ : Set (World 2 2))).real (someAre 0)) ∧
      ¬ Pruned θ ((uniformOn (Set.univ : Set (World 4 4))).real (someAre 0)) := by
  refine ⟨4 / 5, ?_, ?_, ?_, ?_⟩ <;>
    (rw [Pruned, uniformOn_real_someAre (by norm_num)]; norm_num)

/-! ### The deviance puzzle, §5 to §7 -/

/-- In the common-knowledge worlds for *each of the n girls is one of the n names* under the
identity copula, the names are borne by different girls. -/
def distinct (n : ℕ) : Set (World n n) := {w | Function.Injective w}

/-- A predicate of individuals is singleton-denoting given common knowledge `CK` (§5) when at
every common-knowledge world it holds of at most one individual. -/
def SingletonDenoting (CK : Set (World n m)) (P : World n m → Fin n → Prop) : Prop :=
  ∀ w ∈ CK, ∀ x y, P w x → P w y → x = y

/-- *Is Mary* is singleton-denoting given that the names are borne by different girls, (37a). -/
theorem singletonDenoting_distinct (i : Fin n) :
    SingletonDenoting (distinct n) (fun w x ↦ w x = i) :=
  fun _ hw _ _ hx hy ↦ hw (hx.trans hy.symm)

/-- *Is called Mary* is not singleton-denoting, since two girls may bear the name (37b). -/
theorem not_singletonDenoting_univ (hn : 2 ≤ n) (i : Fin m) :
    ¬ SingletonDenoting (Set.univ : Set (World n m)) (fun w x ↦ w x = i) :=
  fun h ↦ absurd (h (fun _ ↦ i) trivial ⟨0, by omega⟩ ⟨1, by omega⟩ rfl rfl) (by simp)

theorem distinct_subset_someAre (i : Fin n) : distinct n ⊆ someAre i :=
  fun _ hw ↦ Finite.injective_iff_surjective.1 hw i

/-- Common knowledge settles an alternative when it holds or fails at every world compatible
with it. -/
def Settled (CK a : Set (World n m)) : Prop := CK ⊆ a ∨ CK ⊆ aᶜ

/-- Deviant-be (31) is deviant (40) because exhaustification with ALT-all-or leaves every
existential alternative open, so ignorance about it is inferred, while common knowledge settles
it. -/
theorem deviant_be (hn : 2 ≤ n) (i : Fin n) :
    LeavesOpen (altAllOr n n) (someAre i) ∧ Settled (distinct n) (someAre i) :=
  ⟨leavesOpen_altAllOr hn hn _ (Or.inr ⟨i, rfl⟩), Or.inl (distinct_subset_someAre i)⟩

/-- For non-deviant-called (32) the same ignorance is inferred, but common knowledge settles
nothing, since the girls may all be called Mary or none may be. -/
theorem non_deviant_called (hn : 2 ≤ n) (hm : 2 ≤ m) (i : Fin m) :
    LeavesOpen (altAllOr n m) (someAre i) ∧ ¬ Settled (Set.univ : Set (World n m)) (someAre i) := by
  refine ⟨leavesOpen_altAllOr hn hm _ (Or.inr ⟨i, rfl⟩), ?_⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  obtain ⟨k, hk⟩ := exists_ne i
  rintro (h | h)
  · exact hk (h (Set.mem_univ (fun _ ↦ k))).choose_spec
  · exact h (Set.mem_univ (fun _ ↦ i)) ⟨⟨0, by omega⟩, rfl⟩

theorem uniformOn_distinct_real_someAre (i : Fin n) :
    (uniformOn (distinct n)).real (someAre i) = 1 := by
  rw [uniformOn_real_apply, Set.inter_eq_left.2 (distinct_subset_someAre i), div_self]
  exact Nat.cast_ne_zero.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨id, Function.injective_id⟩).ne'

/-- Informativeness must be computed blindly to common knowledge, as only then are the existential
alternatives of deviant-be kept (§7.3). -/
theorem blind_informativeness (θ : ℝ) (h : 3 / 4 < θ) (h1 : θ ≤ 1) :
    ¬ Pruned θ ((uniformOn (Set.univ : Set (World 3 3))).real (someAre 0)) ∧
      Pruned θ ((uniformOn (distinct 3)).real (someAre 0)) := by
  rw [Pruned, Pruned, uniformOn_real_someAre (by norm_num), uniformOn_distinct_real_someAre]
  norm_num
  exact ⟨by linarith, h1⟩

end Denic2023
