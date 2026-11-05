module

public import Studies.ChristopoulosZompi2023
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.Data.Finset.Powerset

/-!
# Zompì (2023): *ABA in Multidimensional Paradigms

This file formalizes the Max/Dep account of exponent selection in [zompi-2023]. An exponent's
context specification may be both underspecified and overspecified for the cell it realizes;
each departure is penalized by a violable faithfulness constraint, `Max` for expected features
the specification lacks and `Dep` for spurious features it adds ([wolf-2008], after
[mccarthy-prince-1995]), relativized to the paradigm's dimensions, and the winner is selected
by strict-domination evaluation ([prince-smolensky-1993]). Cells are the cumulative case and
number decompositions of `ChristopoulosZompi2023`, with candidates carried by the same rule
type as that study's Subset Principle, so that only the competition changes.

Evaluation is lexicographic minimization of the ranked violation vector (`mem_eval_iff`), the
engine of `OptimalityTheory.Tableau` (`mem_eval_iff_optimal`). On it, the two minimally
compliant patterns of the case-number paradigm are derived from opposite rankings of the same
two candidate specifications, East Frisian with ABA down the nominative column and Malayalam
with ABA down the plural row (`eastFrisian_pattern`, `malayalam_pattern`); the checkerboard
pattern, in which one exponent takes the nominative singular and the accusative plural but
neither of the other two cells, is excluded over every ranking and every two-candidate
vocabulary (`checkerboard_excluded`); unidimensional *ABA down the singular case column survives
the move to violable constraints (`unidimensional_ABA_excluded`), and only because
specifications respect the feature entailments
(`illformed_spec_breaks_unidimensional_ABA`); and with `Dep` outranking `Max` the system is the
Subset Principle with feature counting ([wolf-2008], [halle-1997]) whenever some candidate is
subset-applicable (`depTop_eq_subsetPrinciple`), under which
[both Russian-doll triples obey *ABA](##subsetPrinciple_contiguous), too strong a generalization.

## Implementation notes

* Rankings of the four dimension-relativized constraints are enumerated rather than generated
  by `List.permutations`, which does not reduce in the kernel.
* `checkerboard_excluded` and `unidimensional_ABA_excluded` range over two-candidate vocabularies
  on the paradigm's feature space; the dissertation's argument is vocabulary-general.

## TODO

* The vocabulary-general checkerboard exclusion, by the dissertation's argument that each
  dimension-relativized constraint's verdict at a cell transfers to the cell sharing that
  dimension, so that the leftmost decisive column at the nominative singular or the accusative
  plural decides one of the other two cells.

## References

* [zompi-2023]
* [wolf-2008]
* [mccarthy-prince-1995]
* [prince-smolensky-1993]
* [halle-1997]
* [starke-2009]
* [smith-moskal-xu-kang-bobaljik-2019]
* [caha-2009]
-/

@[expose] public section

namespace Zompi2023

open Morphology ChristopoulosZompi2023
open SubsetRule (card)

/- The `decide` proofs below range over `featSpace` and lists of feature sets. The
substrate puts `Fintype (Finset K)` in scope, through which `decide` would enumerate every set
of features instead. -/
attribute [-instance] Finset.fintype

/-- The number feature of the cumulative decomposition. -/
inductive NumFeature | pl
  deriving DecidableEq, Repr

/-- The singular, the lower cell of the number chain. -/
abbrev sg : Fin 2 := 0

/-- The plural. -/
abbrev pl : Fin 2 := 1

/-- Cumulative number: SG ∅ ⊂ PL {#pl}. -/
def number : Fin 2 → Finset NumFeature := ![∅, {.pl}]

/-- The bundles of the case-number paradigm, ordered factorwise. -/
abbrev Bundle := Finset K × Finset NumFeature

/-- The cumulative two-dimensional decomposition ((163)): SCC-style case
(NOM ∅ ⊂ ACC {k₁} ⊂ DAT {k₁,k₂}) crossed with cumulative number. -/
def zdecomp : Fin 3 × Fin 2 → Bundle := Prod.map scc number

variable {F : Type*}

/-- A candidate: the Subset Principle's rule, re-read as an OT candidate, whose features may now be
unfaithful to the context in both directions. -/
abbrev Cand (F : Type*) := SubsetRule Bundle F

/-- The inflectional dimensions the constraints are relativized to. -/
inductive Dim | kase | num
  deriving DecidableEq, Repr

/-- The number of features of a bundle on one dimension. -/
def Dim.count : Dim → Bundle → ℕ
  | .kase, b => b.1.card
  | .num, b => b.2.card

/-- The constraint inventory: `Max`/`Dep` relativized to a dimension ((162)),
plus the unrelativized globals of (161) used for the corner rankings. -/
inductive Con | maxD (d : Dim) | depD (d : Dim) | maxG | depG
  deriving DecidableEq, Repr

/-- Violation counts: `Max`-type stars for expected features the rule lacks, `Dep`-type stars for
spurious features the rule adds, each the size of a difference of bundles, on one factor or over
all of them. -/
def viol : Con → Bundle → Cand F → ℕ
  | .maxD d, c, r => d.count (c \ r.features)
  | .depD d, c, r => d.count (r.features \ c)
  | .maxG, c, r => grade ℕ (c \ r.features)
  | .depG, c, r => grade ℕ (r.features \ c)

/-- One Eval cut: keep the candidates with fewest violations of `C`. -/
def cut (c : Bundle) (cands : List (Cand F)) (C : Con) : List (Cand F) :=
  match (cands.map (viol C c)).min? with
  | none => cands
  | some m => cands.filter (fun r ↦ viol C c r = m)

/-- Strict-domination Eval: successive cuts down the ranking, top constraint
first. -/
def eval (rk : List Con) (v : List (Cand F)) (c : Bundle) : List (Cand F) :=
  rk.foldl (cut c) v

/-- `r` is the unique survivor of Eval at `c`. -/
def Wins (rk : List Con) (v : List (Cand F)) (c : Bundle) (r : Cand F) : Prop :=
  eval rk v c = [r]

instance [DecidableEq F] {rk : List Con} {v : List (Cand F)} {c : Bundle}
    {r : Cand F} : Decidable (Wins rk v c r) :=
  inferInstanceAs (Decidable (eval rk v c = [r]))

/-! ### The shared lexicographic-minimization core

`eval` is the strict-domination filter cascade; the phonology OT engine is
lexicographic arg-min over a fixed-length violation profile, `OptimalityTheory.Tableau`, a
finite candidate set scored by a `Lex (Fin n → ℕ)` profile with the winner set
`Tableau.optimal`. `eval` and this engine are one object, not two parallel engines:
`mem_eval_iff` characterizes an Eval survivor as a lexicographic minimizer of the ranked
violation vector, and `mem_eval_iff_optimal` reads that off the tableau whose candidates are
`v` and whose profile is that vector. So morphological Max/Dep Eval and phonological OT
provably share the same lexicographic core. -/

section SharedCore
open OptimalityTheory

/-- The candidate's violation vector at a cell, ordered by the ranking — the
`List ℕ` reading of the OT `ViolationProfile`. -/
def rankedViols (rk : List Con) (c : Bundle) (r : Cand F) : List ℕ :=
  rk.map (fun C ↦ viol C c r)

@[simp] theorem rankedViols_nil (c : Bundle) (r : Cand F) : rankedViols [] c r = [] :=
  rfl

@[simp] theorem rankedViols_cons (C : Con) (rk : List Con) (c : Bundle) (r : Cand F) :
    rankedViols (C :: rk) c r = viol C c r :: rankedViols rk c r := rfl

theorem mem_cut_iff {C : Con} {c : Bundle} {v : List (Cand F)} {r : Cand F} :
    r ∈ cut c v C ↔ r ∈ v ∧ ∀ s ∈ v, viol C c r ≤ viol C c s := by
  unfold cut
  cases hm : (v.map (viol C c)).min? with
  | none =>
    have hv : v = [] := by simpa using List.min?_eq_none_iff.mp hm
    subst hv; simp
  | some m =>
    obtain ⟨hmem, hmin⟩ := List.min?_eq_some_iff (α := ℕ) |>.mp hm
    obtain ⟨s₀, hs₀v, hs₀⟩ := List.mem_map.mp hmem
    rw [List.mem_filter]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hrv, hrm⟩
      exact ⟨hrv, fun s hs ↦ hrm ▸ hmin _ (List.mem_map_of_mem hs)⟩
    · rintro ⟨hrv, hle⟩
      exact ⟨hrv, le_antisymm ((hle _ hs₀v).trans_eq hs₀)
        (hmin _ (List.mem_map_of_mem hrv))⟩

theorem mem_eval_iff {rk : List Con} {v : List (Cand F)} {c : Bundle} {r : Cand F} :
    r ∈ eval rk v c ↔ r ∈ v ∧ ∀ s ∈ v, rankedViols rk c r ≤ rankedViols rk c s := by
  induction rk generalizing v with
  | nil => simp [eval]
  | cons C rk ih =>
    rw [show eval (C :: rk) v c = eval rk (cut c v C) c from rfl, ih]
    constructor
    · rintro ⟨hrcut, htail⟩
      obtain ⟨hrv, hrmin⟩ := mem_cut_iff.mp hrcut
      refine ⟨hrv, fun s hs ↦ ?_⟩
      rw [rankedViols_cons, rankedViols_cons, List.cons_le_cons_iff']
      rcases lt_or_eq_of_le (hrmin s hs) with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, htail s (mem_cut_iff.mpr ⟨hs, fun t ht ↦ heq ▸ hrmin t ht⟩)⟩
    · rintro ⟨hrv, hcons⟩
      have hrmin : ∀ s ∈ v, viol C c r ≤ viol C c s := fun s hs ↦ by
        have := hcons s hs
        rw [rankedViols_cons, rankedViols_cons, List.cons_le_cons_iff'] at this
        rcases this with hlt | ⟨heq, _⟩
        · exact le_of_lt hlt
        · exact le_of_eq heq
      refine ⟨mem_cut_iff.mpr ⟨hrv, hrmin⟩, fun s hs ↦ ?_⟩
      obtain ⟨hsv, hsmin⟩ := mem_cut_iff.mp hs
      have := hcons s hsv
      rw [rankedViols_cons, rankedViols_cons, List.cons_le_cons_iff'] at this
      rcases this with hlt | ⟨_, htail⟩
      · exact absurd (hsmin r hrv) (not_le_of_gt hlt)
      · exact htail

private theorem map_eq_ofFn_get {α β : Type*} (l : List α) (f : α → β) :
    l.map f = List.ofFn (fun i : Fin l.length ↦ f (l.get i)) := by
  apply List.ext_getElem <;> simp

theorem rankedViols_eq_ofFn (rk : List Con) (c : Bundle) (r : Cand F) :
    rankedViols rk c r = List.ofFn (fun i : Fin rk.length ↦ viol (rk.get i) c r) :=
  map_eq_ofFn_get rk (fun C ↦ viol C c r)

/-- The Eval competition as an `OptimalityTheory.Tableau`: candidate set `v`, profile the
ranked violation vector, rank position `i` reading the `i`-th constraint as a violation count.
This is a phonological OT tableau with morphological Max/Dep constraints. -/
def zTableau [DecidableEq F] (rk : List Con) (v : List (Cand F)) (c : Bundle) :
    Tableau (Cand F) rk.length :=
  ⟨v.toFinset, fun i ↦ viol (rk.get i) c⟩

theorem mem_eval_iff_optimal [DecidableEq F] {rk : List Con} {v : List (Cand F)}
    {c : Bundle} {r : Cand F} : r ∈ eval rk v c ↔ r ∈ (zTableau rk v c).optimal := by
  rw [mem_eval_iff, Tableau.mem_optimal_iff]
  refine and_congr List.mem_toFinset.symm (forall_congr' fun s ↦ ?_)
  refine imp_congr List.mem_toFinset.symm ?_
  rw [rankedViols_eq_ofFn, rankedViols_eq_ofFn, List.ofFn_le_ofFn_iff]
  rfl

end SharedCore

/-- The 24 rankings of the four dimension-relativized constraints of the
case-number paradigm, enumerated (kernel-reducible, unlike
`List.permutations`). -/
def rankings : List (List Con) :=
  let M : Con := .maxD .kase; let N : Con := .maxD .num
  let D : Con := .depD .kase; let E : Con := .depD .num
  [[M,N,D,E],[M,N,E,D],[M,D,N,E],[M,D,E,N],[M,E,N,D],[M,E,D,N],
   [N,M,D,E],[N,M,E,D],[N,D,M,E],[N,D,E,M],[N,E,M,D],[N,E,D,M],
   [D,M,N,E],[D,M,E,N],[D,N,M,E],[D,N,E,M],[D,E,M,N],[D,E,N,M],
   [E,M,N,D],[E,M,D,N],[E,N,M,D],[E,N,D,M],[E,D,M,N],[E,D,N,M]]

/-- The candidate feature space of the case-number paradigm. -/
def featSpace : Finset Bundle :=
  ({.k1, .k2} : Finset K).powerset ×ˢ ({.pl} : Finset NumFeature).powerset

/-- The possible context specifications ((163)) are the contexts themselves: feature-structural
entailments hold inside specifications too, κ_dat only alongside κ_dep. The dissertation makes this
well-formedness an entry condition on candidates and flags it as crucial for unidimensional
*ABA. -/
def specSpace : List Bundle :=
  (List.finRange 3 ×ˢ List.finRange 2).map zdecomp

/-! ### The two minimally compliant patterns (§4.1.3) -/

/-- East Frisian 3M candidates ((165)): *z-* specified for plural, *h-* for
accusative. -/
def eastFrisian : List (Cand String) := [⟨(∅, {.pl}), "z"⟩, ⟨({.k1}, ∅), "h"⟩]

/-- With `Dep(#) ≫ Dep(K)` and `Max(K) ≫ Max(#)`, East Frisian has *h-* in NOM.SG, ACC.SG, ACC.PL
and *z-* in NOM.PL ((164), (166)). -/
theorem eastFrisian_pattern :
    Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        (zdecomp (nom, sg)) ⟨({.k1}, ∅), "h"⟩ ∧
      Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        (zdecomp (nom, pl)) ⟨(∅, {.pl}), "z"⟩ ∧
      Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        (zdecomp (acc, sg)) ⟨({.k1}, ∅), "h"⟩ ∧
      Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        (zdecomp (acc, pl)) ⟨({.k1}, ∅), "h"⟩ := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Malayalam 1EX candidates ((168)): same two specifications, exponents
*ñan-* and *enn-*. -/
def malayalam : List (Cand String) := [⟨(∅, {.pl}), "ñan"⟩, ⟨({.k1}, ∅), "enn"⟩]

/-- With `Dep(K) ≫ Dep(#)` and `Max(#) ≫ Max(K)`, Malayalam has *ñan-* in NOM.SG, NOM.PL, ACC.PL and
*enn-* in ACC.SG ((167), (169)). -/
theorem malayalam_pattern :
    Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        (zdecomp (nom, sg)) ⟨(∅, {.pl}), "ñan"⟩ ∧
      Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        (zdecomp (nom, pl)) ⟨(∅, {.pl}), "ñan"⟩ ∧
      Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        (zdecomp (acc, sg)) ⟨({.k1}, ∅), "enn"⟩ ∧
      Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        (zdecomp (acc, pl)) ⟨(∅, {.pl}), "ñan"⟩ := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### The checkerboard exclusion -/

theorem checkerboard_excluded :
    ∀ rk ∈ rankings, ∀ fa ∈ featSpace, ∀ fb ∈ featSpace,
      Wins rk [(⟨fa, 0⟩ : Cand ℕ), ⟨fb, 1⟩] (zdecomp (nom, sg)) ⟨fa, 0⟩ →
      Wins rk [(⟨fa, 0⟩ : Cand ℕ), ⟨fb, 1⟩] (zdecomp (acc, pl)) ⟨fa, 0⟩ →
      Wins rk [(⟨fa, 0⟩ : Cand ℕ), ⟨fb, 1⟩] (zdecomp (acc, sg)) ⟨fa, 0⟩ ∨
        Wins rk [(⟨fa, 0⟩ : Cand ℕ), ⟨fb, 1⟩] (zdecomp (nom, pl)) ⟨fa, 0⟩ := by
  decide

/-- With violable constraints, no ranking and two-candidate vocabulary of well-formed specs yields
ABA down the singular case column (§4.1.4). -/
theorem unidimensional_ABA_excluded :
    ∀ rk ∈ rankings, ∀ fa ∈ specSpace, ∀ fb ∈ specSpace,
      Wins rk [(⟨fa, 0⟩ : Cand ℕ), ⟨fb, 1⟩] (zdecomp (nom, sg)) ⟨fa, 0⟩ →
      Wins rk [(⟨fa, 0⟩ : Cand ℕ), ⟨fb, 1⟩] (zdecomp (dat, sg)) ⟨fa, 0⟩ →
      ¬ Wins rk [(⟨fa, 0⟩ : Cand ℕ), ⟨fb, 1⟩] (zdecomp (acc, sg)) ⟨fb, 1⟩ := by
  decide

theorem illformed_spec_breaks_unidimensional_ABA :
    Wins [.maxD .kase, .depD .kase, .maxD .num, .depD .num]
        [(⟨({.k2}, ∅), 0⟩ : Cand ℕ), ⟨({.k1}, {.pl}), 1⟩] (zdecomp (nom, sg))
        ⟨({.k2}, ∅), 0⟩ ∧
      Wins [.maxD .kase, .depD .kase, .maxD .num, .depD .num]
        [(⟨({.k2}, ∅), 0⟩ : Cand ℕ), ⟨({.k1}, {.pl}), 1⟩] (zdecomp (acc, sg))
        ⟨({.k1}, {.pl}), 1⟩ ∧
      Wins [.maxD .kase, .depD .kase, .maxD .num, .depD .num]
        [(⟨({.k2}, ∅), 0⟩ : Cand ℕ), ⟨({.k1}, {.pl}), 1⟩] (zdecomp (dat, sg))
        ⟨({.k2}, ∅), 0⟩ := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### The corner rankings: Wolf's mimicry -/

/-- Under the Subset Principle every chain of the product order obeys *ABA, among them both
Russian-doll triples from the nominative singular to the accusative plural: too strong a
generalization (§4.1.1, p. 69), since East Frisian and Malayalam each break one of them. -/
theorem subsetPrinciple_contiguous {v : RuleSet (Cand F)} (hv : v.Antihomophonous) :
    IsContiguous fun c ↦ v.realize card (zdecomp c) := by
  have hs : ∀ a b : Fin 3, a ≤ b → scc a ≤ scc b := by decide
  have hn : ∀ a b : Fin 2, a ≤ b → number a ≤ number b := by decide
  exact (SubsetRule.isContiguous_realize hv).comp_monotone
    (Monotone.prodMap (fun a b ↦ hs a b) fun a b ↦ hn a b)

-- p. 69: so the Subset Principle cannot state East Frisian, *h-* around a *z-* in NOM.PL
theorem subsetPrinciple_not_eastFrisian {v : RuleSet (Cand String)} (hv : v.Antihomophonous)
    (h₁ : v.realize card (zdecomp (nom, sg)) = some "h")
    (h₃ : v.realize card (zdecomp (acc, pl)) = some "h") :
    v.realize card (zdecomp (nom, pl)) ≠ some "z" := fun h₂ ↦
  absurd (h₁.symm.trans ((subsetPrinciple_contiguous hv (i := (nom, sg)) (j := (nom, pl))
    (k := (acc, pl)) (by decide) (by decide) (h₁.trans h₃.symm)).trans h₂)) (by decide)

private theorem depG_eq_zero_iff {c : Bundle} {r : Cand F} :
    viol .depG c r = 0 ↔ Applies r c := by
  show (r.features.1 \ c.1).card + (r.features.2 \ c.2).card = 0 ↔
    r.features.1 ⊆ c.1 ∧ r.features.2 ⊆ c.2
  simp [Finset.sdiff_eq_empty_iff_subset]

private theorem maxG_le_iff {c : Bundle} {r s : Cand F} (hr : Applies r c) (hs : Applies s c) :
    viol .maxG c r ≤ viol .maxG c s ↔ card s ≤ card r := by
  have h₁ := Finset.card_sdiff_add_card_eq_card (show r.features.1 ⊆ c.1 from hr.1)
  have h₂ := Finset.card_sdiff_add_card_eq_card (show r.features.2 ⊆ c.2 from hr.2)
  have h₃ := Finset.card_sdiff_add_card_eq_card (show s.features.1 ⊆ c.1 from hs.1)
  have h₄ := Finset.card_sdiff_add_card_eq_card (show s.features.2 ⊆ c.2 from hs.2)
  show (c.1 \ r.features.1).card + (c.2 \ r.features.2).card ≤
      (c.1 \ s.features.1).card + (c.2 \ s.features.2).card ↔
    s.features.1.card + s.features.2.card ≤ r.features.1.card + r.features.2.card
  omega

-- [wolf-2008] [halle-1997]
theorem mem_eval_depG_maxG_iff {v : List (Cand F)} {c : Bundle} {r : Cand F}
    (hv : ∃ s ∈ v, Applies s c) :
    r ∈ eval [.depG, .maxG] v c ↔ r ∈ v ∧ Applies r c ∧
      ∀ s ∈ v, Applies s c → card s ≤ card r := by
  simp only [mem_eval_iff, rankedViols_cons, rankedViols_nil, List.cons_le_cons_iff', le_refl,
    and_true, ← le_iff_lt_or_eq]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun ⟨hr, hmax⟩ s hs ↦ ?_⟩
  · obtain ⟨s₀, hs₀, ha₀⟩ := hv
    have hr : Applies r c := depG_eq_zero_iff.1 <| by
      have := depG_eq_zero_iff.2 ha₀
      rcases h s₀ hs₀ with h | h <;> omega
    refine ⟨hr, fun s hs ha ↦ ?_⟩
    have hd := (depG_eq_zero_iff.2 hr).trans (depG_eq_zero_iff.2 ha).symm
    obtain h | h := h s hs
    · omega
    · exact (maxG_le_iff hr ha).1 h.2
  · by_cases ha : Applies s c
    · exact .inr ⟨(depG_eq_zero_iff.2 hr).trans (depG_eq_zero_iff.2 ha).symm,
        (maxG_le_iff hr ha).2 (hmax s hs ha)⟩
    · have := depG_eq_zero_iff.2 hr
      have := mt (depG_eq_zero_iff (r := s) (c := c)).1 ha
      exact .inl (by omega)

/-- Whenever some candidate is subset-applicable, the unique survivor of the ranking `Dep ≫ Max`
is what the Subset Principle with feature counting inserts ([wolf-2008] on [halle-1997]; dual to
[starke-2009]). -/
theorem depTop_eq_subsetPrinciple {v : List (Cand F)} {c : Bundle} {r : Cand F}
    (hv : ∃ s ∈ v, Applies s c) (h : Wins [.depG, .maxG] v c r) :
    RuleSet.realize v card c = some r.exponent := by
  obtain ⟨hr, ha, hmax⟩ := (mem_eval_depG_maxG_iff hv).1 (show r ∈ eval _ v c from h ▸ by simp)
  refine RuleSet.realize_eq_of_forall_le hr ha hmax fun s hs hsa hcard ↦ ?_
  have hmem : s ∈ eval [.depG, .maxG] v c := (mem_eval_depG_maxG_iff hv).2 ⟨hs, hsa, fun t ht hta ↦
    (hmax t ht hta).trans_eq hcard.symm⟩
  rw [show eval [.depG, .maxG] v c = [r] from h, List.mem_singleton] at hmem
  rw [hmem]

end Zompi2023
