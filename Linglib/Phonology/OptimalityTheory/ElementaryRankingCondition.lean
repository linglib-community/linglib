module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.OptimalityTheory.Typology
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Data.Fintype.Perm
public import Linglib.Core.GroupTheory.Perm.MinOn
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Elementary ranking conditions

This file defines Prince's elementary ranking conditions (ERCs). An ERC records, for a desired
winner against a competitor, which constraints prefer the winner, which prefer the loser, and
which are indifferent. A ranking satisfies an ERC when some constraint preferring the winner
dominates every constraint preferring the loser, so that a candidate is optimal under a ranking
exactly when the ranking satisfies its ERC against every competitor.

## Main definitions

* `ERCVal`, `ERC ι`: the values `W`, `L`, and `e`, and sign vectors over the constraints `ι`.
* `ERC.SatisfiedBy r α`: the ranking `r` satisfies the ERC `α`; `ERC.linearExtensions E` is
  the set of rankings satisfying every ERC in a finite set `E`.
* `ERC.W`, `ERC.L`, `ERC.support`: the winner-preferring, loser-preferring, and non-neutral
  constraints of an ERC.
* `ERC.IsTrivial`, `ERC.IsContradictory`, `ERC.IsSimple`: an ERC with no `L`, one with an `L`
  and no `W`, and one with exactly one `W` and one `L`.
* `ercOfProfiles`, `tableauERC`, `simpleERC`: the ERC of a winner and a loser given by their
  violation vectors, of two candidates of a tableau, and of a single domination `i ≫ j`.

## Main statements

* `ERC.satisfiedBy_iff_dominance`: a ranking satisfies an ERC iff every `L`-constraint is
  dominated by some `W`-constraint.
* `ERC.satisfiedBy_iff_lead`: a ranking satisfies an ERC iff its earliest non-neutral
  constraint, when one exists, is a `W`.
* `ERC.SatisfiedBy.mono`: raising coordinates in the order `L ≤ e ≤ W` weakens an ERC.
* `ERC.trivial_satisfiedBy`: an ERC with no `L` holds under every ranking.
* `ERC.linearExtensions_singleton_subset_iff`: given a `W` in the entailing ERC and an `L` in
  the entailed one, entailment between single ERCs is the coordinatewise order.
* `ERC.card_filter_satisfiedBy_mul_card`: the rankings satisfying an ERC with a non-neutral
  constraint are the fraction `|W| / |W ∪ L|` of all rankings.
* `ERC.not_satisfiedBy_neg`: an ERC with a non-neutral constraint and its negative hold under
  no common ranking.
* `satisfiedBy_ercOfProfiles_iff_le`: a ranking satisfies the ERC of a winner and a loser iff
  the winner's violations, read in the order of the ranking, are lexicographically at most the
  loser's.
* `Tableau.ofRanking_mem_optimal_iff_satisfiedBy`: a candidate is optimal under a ranking iff
  the ranking satisfies its ERC against every competitor.

## Implementation notes

* `ERCVal` is mathlib's `SignType`, with `W = 1`, `L = -1`, and `e = 0`, so that
  `ercOfProfiles` is a coordinatewise `SignType.sign`, Prince's negative of an ERC is `-α`, and
  satisfaction and the classes of ERCs are decidable through the instances of `SignType`.
* `ERC.IsTrivial` requires that an ERC have no `L`, Prince's class `W*`, whereas Prince calls
  an ERC trivial when it lacks a `W` or an `L`.
* Consistency and entailment of ERC sets have no definitions of their own: a finite set `E` is
  consistent when `ERC.linearExtensions E` is nonempty, and `E` entails `E'` when
  `ERC.linearExtensions E ⊆ ERC.linearExtensions E'`.
* `ERC.satisfiedBy_iff_exists_dominant`, Prince's `∃∀` form, requires a constraint to exist,
  as Prince assumes, since over no constraints the `∀∃` form holds vacuously and the `∃∀`
  form fails.

## TODO

Prince's fusion calculus. The fusion of two ERCs is computed coordinatewise, with `L`
absorbing, `e` the identity, and each value idempotent. Its main results, in terms of
`ERC.linearExtensions`:
* a set of ERCs entails its fusion;
* a set is inconsistent iff some subset fuses to an ERC with an `L` and no `W`;
* a set entails an ERC iff the fusion of some subset entails it.

## References

* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
* [J. Riggle, *The Complexity of Ranking Hypotheses in Optimality Theory*
  (2009)][riggle-2009a]
* [N. Merchant, J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
-/

@[expose] public section

namespace OptimalityTheory

variable {ι : Type*} {n : ℕ}

/-! ### The three values -/

/-- An ERC value: `W` (winner-preferring), `L` (loser-preferring), or `e` (neutral), as
mathlib's `SignType` (`ERCVal.W`, `ERCVal.L`, `ERCVal.e`). -/
abbrev ERCVal := SignType

namespace ERCVal

/-- The winner-preferring value (`1`). -/
@[match_pattern] abbrev W : ERCVal := .pos
/-- The loser-preferring value (`-1`). -/
@[match_pattern] abbrev L : ERCVal := .neg
/-- The neutral value (`0`). -/
@[match_pattern] abbrev e : ERCVal := .zero

end ERCVal

/-! ### Elementary ranking conditions -/

/-- An *elementary ranking condition* over the constraints `ι`: a sign vector `ι → ERCVal`. -/
abbrev ERC (ι : Type*) := ι → ERCVal

namespace ERC

variable (α : ERC ι)

/-- An ERC is *trivial* when it has no `L`-constraint, so that every ranking satisfies it:
Prince's class `W*`. Prince's own term is wider and covers every ERC that lacks a `W` or an
`L`. -/
def IsTrivial : Prop := ∀ k, α k ≠ .L

instance [Fintype ι] : Decidable α.IsTrivial := Fintype.decidableForallFintype

/-- An ERC is *contradictory* when it has an `L`-constraint but no `W`-constraint: Prince's
class `L⁺`. -/
def IsContradictory : Prop := (∀ k, α k ≠ .W) ∧ (∃ k, α k = .L)

instance [Fintype ι] : Decidable α.IsContradictory := inferInstanceAs (Decidable (_ ∧ _))

/-- A *simple* ERC has exactly one `W` and one `L`. -/
def IsSimple : Prop := (∃! w, α w = .W) ∧ (∃! l, α l = .L)

end ERC

/-! ### ERC satisfaction -/

@[simp] private theorem ERCVal.lt_zero_iff (x : ERCVal) : x < 0 ↔ x = .L := by
  revert x; decide

@[simp] private theorem ERCVal.zero_lt_iff (x : ERCVal) : 0 < x ↔ x = .W := by
  revert x; decide

private theorem ERCVal.eq_L_of_le {x : ERCVal} (h : x ≤ .L) : x = .L := by
  revert x; decide

private theorem ERCVal.eq_W_of_le {x : ERCVal} (h : .W ≤ x) : x = .W := by
  revert x; decide

namespace ERC

variable (r : Ranking ι n) (α : ERC ι)

/-- A ranking `r` *satisfies* the ERC `α` when the sign vector of `α`, read in the order of `r`,
is lexicographically nonnegative. -/
def SatisfiedBy : Prop := toLex 0 ≤ toLex (α ∘ r)

/-- A ranking satisfies an ERC iff its earliest non-neutral constraint, when one exists, is
winner-preferring, which is Prince's description of satisfaction by a left-to-right sweep. -/
theorem satisfiedBy_iff_lead :
    α.SatisfiedBy r ↔ ∀ he : ∃ p, α (r p) ≠ .e, α (r (Fin.find _ he)) = .W :=
  ⟨fun h he => (ERCVal.zero_lt_iff _).mp ((Pi.lex_le_iff_find _ _).mp h he),
   fun h => (Pi.lex_le_iff_find _ _).mpr fun he => (ERCVal.zero_lt_iff _).mpr (h he)⟩

/-- Satisfaction in Prince's `∀∃` form, his (3): every loser-preferring constraint is dominated
by some winner-preferring one. -/
theorem satisfiedBy_iff_dominance :
    α.SatisfiedBy r ↔ ∀ c, α c = .L → ∃ w, α w = .W ∧ r.Dominates w c := by
  rw [SatisfiedBy, show toLex (0 : Fin n → ERCVal) = toLex ((0 : ι → ERCVal) ∘ r) from rfl,
    Pi.toLex_comp_le_iff_forall_exists]
  simp only [Pi.zero_apply, ERCVal.lt_zero_iff, ERCVal.zero_lt_iff, Ranking.Dominates]

instance : Decidable (α.SatisfiedBy r) :=
  inferInstanceAs (Decidable (toLex 0 ≤ toLex (α ∘ r)))

/-- Satisfaction in Prince's `∃∀` form, his (4): some winner-preferring constraint dominates
every loser-preferring one. The two forms agree because the ranking is total. -/
theorem satisfiedBy_iff_exists_dominant [NeZero n] :
    α.SatisfiedBy r ↔ ∃ d, ∀ c, α c = .L → (α d = .W ∧ r.Dominates d c) := by
  rw [SatisfiedBy, show toLex (0 : Fin n → ERCVal) = toLex ((0 : ι → ERCVal) ∘ r) from rfl,
    Pi.toLex_comp_le_iff_exists_forall]
  simp only [Pi.zero_apply, ERCVal.lt_zero_iff, ERCVal.zero_lt_iff, Ranking.Dominates]

theorem trivial_satisfiedBy {α : ERC ι} (htriv : α.IsTrivial) (r : Ranking ι n) :
    α.SatisfiedBy r :=
  (satisfiedBy_iff_dominance r α).mpr fun l hl => absurd hl (htriv l)

/-- W-extension and L-retraction, Prince's Proposition 1.1(a): raising coordinates in the order
`L ≤ e ≤ W` weakens an ERC, so that a ranking satisfying `α` satisfies every `β ≥ α`. -/
theorem SatisfiedBy.mono {α β : ERC ι} {r : Ranking ι n} (h : α.SatisfiedBy r) (hαβ : α ≤ β) :
    β.SatisfiedBy r := by
  rw [satisfiedBy_iff_dominance] at h ⊢
  intro c hc
  obtain ⟨w, hw, hd⟩ := h c (ERCVal.eq_L_of_le ((hαβ c).trans_eq hc))
  exact ⟨w, ERCVal.eq_W_of_le (hw.symm.trans_le (hαβ w)), hd⟩

/-! ### The winner- and loser-preferring constraints -/

section Support

variable [Fintype ι] {α : ERC ι} {k : ι}

/-- `W(α)`, the winner-preferring constraints of an ERC ([merchant-riggle-2016]). -/
def W (α : ERC ι) : Finset ι := {k | α k = .W}

/-- `L(α)`, the loser-preferring constraints of an ERC ([merchant-riggle-2016]). -/
def L (α : ERC ι) : Finset ι := {k | α k = .L}

/-- The non-neutral constraints of an ERC, its support as a sign vector. -/
def support (α : ERC ι) : Finset ι := {k | α k ≠ .e}

@[simp] theorem mem_W : k ∈ α.W ↔ α k = .W := by
  rw [W, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ k)

@[simp] theorem mem_L : k ∈ α.L ↔ α k = .L := by
  rw [L, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ k)

@[simp] theorem mem_support : k ∈ α.support ↔ α k ≠ .e := by
  rw [support, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ k)

theorem W_subset_support : α.W ⊆ α.support := fun k hk ↦
  mem_support.2 fun h ↦ absurd ((mem_W.1 hk).symm.trans h) (by decide)

theorem L_subset_support : α.L ⊆ α.support := fun k hk ↦
  mem_support.2 fun h ↦ absurd ((mem_L.1 hk).symm.trans h) (by decide)

@[simp] theorem support_neg : (-α).support = α.support := by
  ext; simp

@[simp] theorem W_neg : (-α).W = α.L := by
  ext k
  rw [mem_W, mem_L, Pi.neg_apply, neg_eq_iff_eq_neg]
  rfl

end Support

/-! ### The earliest non-neutral constraint

A ranking satisfies an ERC with a non-neutral constraint exactly when the earliest of its
non-neutral constraints is winner-preferring. Each non-neutral constraint comes first equally
often, so that the rankings satisfying the ERC are the fraction `|W| / |W ∪ L|` of all
rankings. -/

section Earliest

variable [Fintype ι] {α : ERC ι} {r : Ranking ι n}

/-- A ranking satisfies an ERC with a non-neutral constraint iff its earliest non-neutral
constraint is winner-preferring. -/
theorem satisfiedBy_iff_exists_isMinOn (hα : ∃ k, α k ≠ .e) :
    α.SatisfiedBy r ↔ ∃ x ∈ α.W, IsMinOn r.symm α.support x := by
  obtain ⟨k, hk⟩ := hα
  rw [satisfiedBy_iff_dominance]
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hmin⟩ c hc ↦ ⟨x, mem_W.1 hx, ?_⟩⟩
  · obtain ⟨x, hx, hmin⟩ := α.support.exists_min_image r.symm ⟨k, mem_support.2 hk⟩
    refine ⟨x, mem_W.2 ?_, isMinOn_iff.2 hmin⟩
    rcases h' : α x with _ | _ | _
    · exact absurd h' (mem_support.1 hx)
    · obtain ⟨w, hw, hdom⟩ := h x h'
      exact absurd (hmin w (W_subset_support (mem_W.2 hw))) (not_le.2 hdom)
    · rfl
  · refine (isMinOn_iff.1 hmin c (L_subset_support (mem_L.2 hc))).lt_of_ne fun h ↦ ?_
    obtain rfl := r.symm.injective h
    exact absurd ((mem_W.1 hx).symm.trans hc) (by decide)

/-- The sign vector of an ERC, read in the order of a ranking, is lexicographically positive iff
the ranking's earliest non-neutral constraint exists and is winner-preferring. This is strict
satisfaction, which holds of no ranking when every constraint is neutral. -/
theorem lex_pos_iff_exists_isMinOn :
    toLex 0 < toLex (α ∘ r) ↔ ∃ x ∈ α.W, IsMinOn r.symm α.support x := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hmin⟩ ↦ ?_⟩
  · have hα : ∃ k, α k ≠ .e := by
      by_contra! h0
      exact h.ne (congrArg toLex (funext fun p ↦ (h0 (r p)).symm))
    exact (satisfiedBy_iff_exists_isMinOn hα).1 h.le
  · have hx' := mem_support.1 (W_subset_support hx)
    refine lt_of_le_of_ne ((satisfiedBy_iff_exists_isMinOn ⟨x, hx'⟩).2 ⟨x, hx, hmin⟩)
      fun h ↦ hx' ?_
    simpa using (congrFun (toLex_inj.1 h) (r.symm x)).symm

/-- An ERC with a non-neutral constraint and its negative hold under no common ranking, since
they share their earliest non-neutral constraint, which prefers the winner of only one of
them. -/
theorem not_satisfiedBy_neg (hα : ∃ k, α k ≠ .e) (h : α.SatisfiedBy r) : ¬ (-α).SatisfiedBy r := by
  obtain ⟨x, hx, hxm⟩ := (satisfiedBy_iff_exists_isMinOn hα).1 h
  rw [satisfiedBy_iff_exists_isMinOn (by simpa using hα), support_neg, W_neg]
  rintro ⟨y, hy, hym⟩
  obtain rfl : x = y := r.symm.injective <| le_antisymm
    (isMinOn_iff.1 hxm y (L_subset_support hy)) (isMinOn_iff.1 hym x (W_subset_support hx))
  exact absurd ((mem_W.1 hx).symm.trans (mem_L.1 hy)) (by decide)

open Finset in
/-- The rankings satisfying an ERC, counted against all rankings: their number times the number
of non-neutral constraints is `n!` times the number of winner-preferring ones. -/
theorem card_filter_satisfiedBy_mul_card (α : ERC (Fin n)) :
    #{σ : Ranking (Fin n) n | α.SatisfiedBy σ} * #α.support = n.factorial * #α.W := by
  rcases α.support.eq_empty_or_nonempty with h | ⟨k, hk⟩
  · have hW : α.W = ∅ := subset_empty.1 (h ▸ W_subset_support)
    rw [h, hW, card_empty, mul_zero, mul_zero]
  · classical
    have hα : ∃ k, α k ≠ .e := ⟨k, mem_support.1 hk⟩
    have := Equiv.Perm.card_filter_isMinOn_symm_univ_mul_card α.support α.W
    rw [Fintype.card_fin, Finset.inter_eq_left.2 W_subset_support] at this
    convert this using 3
    ext σ
    simp only [mem_filter, mem_univ, true_and, satisfiedBy_iff_exists_isMinOn hα]

end Earliest

end ERC

/-! ### Linear extensions

A ranking satisfies a finite set of ERCs when it satisfies each member. The set is *consistent*
when some ranking satisfies it, that is, when `ERC.linearExtensions E` is nonempty, and `E`
*entails* `E'` when `ERC.linearExtensions E ⊆ ERC.linearExtensions E'`. -/

namespace ERC

/-- The rankings satisfying every member of a finite set of ERCs, which Merchant and Riggle call
its *linear extensions*. -/
def linearExtensions (E : Finset (ERC (Fin n))) : Finset (Ranking (Fin n) n) :=
  Finset.univ.filter fun r => ∀ α ∈ E, ERC.SatisfiedBy r α

@[simp] theorem mem_linearExtensions {E : Finset (ERC (Fin n))} {r : Ranking (Fin n) n} :
    r ∈ linearExtensions E ↔ ∀ α ∈ E, ERC.SatisfiedBy r α := by
  simp [linearExtensions]

@[simp] theorem linearExtensions_empty :
    linearExtensions (∅ : Finset (ERC (Fin n))) = Finset.univ := by
  ext r; simp

/-- Some ranking puts `p` first and `q` second. -/
private theorem exists_ranking_first_second (p q : Fin n) :
    ∃ r : Ranking (Fin n) n, (∀ c, c ≠ p → r.Dominates p c) ∧
      ∀ c, c ≠ p → c ≠ q → r.Dominates q c := by
  let k : Fin n → ℕ := fun c ↦ if c = p then 0 else if c = q then 1 else 2
  obtain ⟨r, hr⟩ := Ranking.exists_dominates_iff (n := n) (fun c ↦ toLex (k c, c))
    fun c d h ↦ (Prod.ext_iff.mp (toLex.injective h)).2
  refine ⟨r, fun c hc ↦ (hr p c).2 (Prod.Lex.toLex_lt_toLex.2 (.inl ?_)),
    fun c hcp hcq ↦ (hr q c).2 (Prod.Lex.toLex_lt_toLex.2 (.inl ?_))⟩
  all_goals (simp only [k]; split_ifs <;> simp_all)

/-- Raising coordinates weakens an ERC: the linear extensions of `α` are among those of every
`β ≥ α`. -/
theorem linearExtensions_singleton_subset_of_le {α β : ERC (Fin n)} (hαβ : α ≤ β) :
    linearExtensions {α} ⊆ linearExtensions {β} := fun r hr ↦ by
  simp only [mem_linearExtensions, Finset.mem_singleton, forall_eq] at hr ⊢
  exact hr.mono hαβ

/-- Entailment between single ERCs is the coordinatewise order, Prince's Proposition 1.1. Prince
assumes both ERCs nontrivial, with a `W` and an `L` each, whereas the proof needs only a `W` in
the entailing ERC and an `L` in the entailed one: a coordinate on which `α` exceeds `β` yields a
ranking satisfying `α` alone, which puts that coordinate first and a `W` of `α` or an `L` of `β`
second. -/
theorem linearExtensions_singleton_subset_iff {α β : ERC (Fin n)} (hα : ∃ k, α k = .W)
    (hβ : ∃ k, β k = .L) : linearExtensions {α} ⊆ linearExtensions {β} ↔ α ≤ β := by
  refine ⟨fun h i ↦ le_of_not_gt fun hlt ↦ ?_, linearExtensions_singleton_subset_of_le⟩
  have h' (r : Ranking (Fin n) n) (hr : α.SatisfiedBy r) : β.SatisfiedBy r := by
    have hmem : r ∈ linearExtensions {α} := by simpa using hr
    simpa using h hmem
  have first {r : Ranking (Fin n) n} {p : Fin n} (hp : ∀ c, c ≠ p → r.Dominates p c) (x : Fin n) :
      ¬ r.Dominates x p := fun hx ↦ by
    by_cases hxp : x = p
    · subst hxp
      exact lt_irrefl _ hx
    · exact lt_asymm (hp x hxp) hx
  obtain ⟨w, hw⟩ := hα
  obtain ⟨l, hl⟩ := hβ
  have hcases : ∀ x y : ERCVal, y < x → (y = .L ∧ x ≠ .L) ∨ (x = .W ∧ y ≠ .W) := by decide
  rcases hcases _ _ hlt with ⟨hβi, hαi⟩ | ⟨hαi, hβi⟩
  · -- `i` first: `β` fails at `i`, and `α` holds through `i` or through `w` second
    obtain ⟨r, h₁, h₂⟩ := exists_ranking_first_second i w
    have hαr : α.SatisfiedBy r := (satisfiedBy_iff_dominance r α).2 fun c hc ↦ by
      have hci : c ≠ i := fun e ↦ hαi (e ▸ hc)
      by_cases hαW : α i = .W
      · exact ⟨i, hαW, h₁ c hci⟩
      · exact ⟨w, hw, h₂ c hci fun e ↦ by simp [e, hw] at hc⟩
    obtain ⟨x, -, hx⟩ := (satisfiedBy_iff_dominance r β).1 (h' r hαr) i hβi
    exact first h₁ x hx
  · -- `i` first: `α` holds through `i`, and `β` fails at `i` or at `l` second
    obtain ⟨r, h₁, h₂⟩ := exists_ranking_first_second i l
    have hαr : α.SatisfiedBy r := (satisfiedBy_iff_dominance r α).2 fun c hc ↦
      ⟨i, hαi, h₁ c fun e ↦ by simp [e, hαi] at hc⟩
    have hβr := (satisfiedBy_iff_dominance r β).1 (h' r hαr)
    by_cases hβL : β i = .L
    · obtain ⟨x, -, hx⟩ := hβr i hβL
      exact first h₁ x hx
    · obtain ⟨x, hxW, hx⟩ := hβr l hl
      have hxi : x = i := by
        by_contra hxi
        by_cases hxl : x = l
        · subst hxl
          exact lt_irrefl _ hx
        · exact lt_asymm (h₂ x hxi hxl) hx
      exact hβi (hxi ▸ hxW)

end ERC

/-! ### Simple ERCs -/

/-- The ERC requiring constraint `i` to dominate constraint `j`, with every other constraint
neutral. -/
def simpleERC [DecidableEq ι] (i j : ι) : ERC ι :=
  fun k => if k = i then .W else if k = j then .L else .e

section Simple

variable [DecidableEq ι] {i j : ι}

theorem simpleERC_eq_W_iff (k : ι) :
    simpleERC i j k = .W ↔ k = i := by
  simp only [simpleERC]; split_ifs with h₁ h₂ <;> simp_all

theorem simpleERC_eq_L_iff (hij : i ≠ j) (k : ι) :
    simpleERC i j k = .L ↔ k = j := by
  simp only [simpleERC]; split_ifs with h₁ h₂ <;> simp_all

@[simp] theorem simpleERC_apply_W : simpleERC i j i = .W :=
  (simpleERC_eq_W_iff i).mpr rfl

theorem simpleERC_apply_L (hij : i ≠ j) : simpleERC i j j = .L :=
  (simpleERC_eq_L_iff hij j).mpr rfl

theorem simpleERC_self_isTrivial (i : ι) : (simpleERC i i).IsTrivial := fun k => by
  simp only [simpleERC]; split_ifs <;> decide

theorem simpleERC_satisfiedBy_iff (hij : i ≠ j) (r : Ranking ι n) :
    (simpleERC i j).SatisfiedBy r ↔ r.Dominates i j := by
  rw [ERC.satisfiedBy_iff_dominance]
  constructor
  · intro h
    obtain ⟨w, hw, hdom⟩ := h j ((simpleERC_eq_L_iff hij j).mpr rfl)
    rwa [(simpleERC_eq_W_iff w).mp hw] at hdom
  · intro hdom l hl
    rw [(simpleERC_eq_L_iff hij l).mp hl]
    exact ⟨i, simpleERC_apply_W, hdom⟩

theorem simpleERC_satisfiedBy_toRel_iff (i j : ι) (r : Ranking ι n) :
    (simpleERC i j).SatisfiedBy r ↔ r.toRel i j := by
  rcases eq_or_ne i j with rfl | hij
  · exact iff_of_true (ERC.trivial_satisfiedBy (simpleERC_self_isTrivial i) r) (le_refl _)
  · rw [simpleERC_satisfiedBy_iff hij, r.toRel_iff_dominates hij]

theorem simpleERC_consistent {i j : Fin n} (hij : i ≠ j) :
    (ERC.linearExtensions {simpleERC i j}).Nonempty :=
  have ⟨r, hr⟩ := Ranking.exists_dominates hij
  ⟨r, by simp [(simpleERC_satisfiedBy_iff hij r).mpr hr]⟩

theorem simpleERC_isSimple (hij : i ≠ j) : (simpleERC i j).IsSimple :=
  ⟨⟨i, simpleERC_apply_W, fun y hy => (simpleERC_eq_W_iff y).mp hy⟩,
   ⟨j, simpleERC_apply_L hij, fun y hy => (simpleERC_eq_L_iff hij y).mp hy⟩⟩

theorem simpleERC_isSimple_or_isTrivial (i j : ι) :
    (simpleERC i j).IsSimple ∨ (simpleERC i j).IsTrivial := by
  rcases eq_or_ne i j with rfl | hij
  exacts [.inr (simpleERC_self_isTrivial i), .inl (simpleERC_isSimple hij)]

end Simple

/-! ### The ERCs of violation profiles and tableaux -/

/-- The ERC of a winner and a loser given by their violation vectors: the coordinatewise sign of
the loser's violations less the winner's, as in Riggle's Definition 3. -/
def ercOfProfiles (winner loser : ι → ℕ) : ERC ι :=
  fun k => SignType.sign ((loser k : ℤ) - (winner k : ℤ))

theorem ercOfProfiles_eq_W_iff (w l : ι → ℕ) (k : ι) :
    ercOfProfiles w l k = .W ↔ w k < l k := by
  simp only [ercOfProfiles, SignType.pos_eq_one, sign_eq_one_iff]; omega

theorem ercOfProfiles_eq_L_iff (w l : ι → ℕ) (k : ι) :
    ercOfProfiles w l k = .L ↔ l k < w k := by
  simp only [ercOfProfiles, SignType.neg_eq_neg_one, sign_eq_neg_one_iff]; omega

theorem ercOfProfiles_eq_e_iff (w l : ι → ℕ) (k : ι) :
    ercOfProfiles w l k = .e ↔ w k = l k := by
  simp only [ercOfProfiles, SignType.zero_eq_zero, sign_eq_zero_iff]; omega

@[simp] theorem mem_W_ercOfProfiles [Fintype ι] {w l : ι → ℕ} {k : ι} :
    k ∈ (ercOfProfiles w l).W ↔ w k < l k :=
  ERC.mem_W.trans (ercOfProfiles_eq_W_iff w l k)

@[simp] theorem mem_L_ercOfProfiles [Fintype ι] {w l : ι → ℕ} {k : ι} :
    k ∈ (ercOfProfiles w l).L ↔ l k < w k :=
  ERC.mem_L.trans (ercOfProfiles_eq_L_iff w l k)

@[simp] theorem mem_support_ercOfProfiles [Fintype ι] {w l : ι → ℕ} {k : ι} :
    k ∈ (ercOfProfiles w l).support ↔ w k ≠ l k :=
  ERC.mem_support.trans (ercOfProfiles_eq_e_iff w l k).not

/-- Swapping winner and loser negates the ERC, which is Prince's *negative* of an ERC, his
(20). -/
theorem ercOfProfiles_swap (w l : ι → ℕ) :
    ercOfProfiles l w = -ercOfProfiles w l := by
  funext k
  rw [Pi.neg_apply, ercOfProfiles, ercOfProfiles, ← neg_sub, Left.sign_neg]

/-- The ERC with the values of a list, with the length proof discharged by `decide` for literals,
as in `ercOfList [.W, .e, .L, .e] : ERC (Fin 4)`. -/
def ercOfList (vs : List ERCVal) (h : vs.length = n := by decide) : ERC (Fin n) :=
  fun i => vs[i.val]'(by omega)

theorem lex_nonneg_ercOfProfiles_iff (w l : ViolationProfile n) :
    toLex (fun _ => (0 : ERCVal)) ≤ toLex (ercOfProfiles (ofLex w) (ofLex l)) ↔ w ≤ l :=
  (Pi.lex_le_iff_forall _ _).trans <|
    (forall_congr' fun p => imp_congr
      ((ERCVal.lt_zero_iff _).trans (ercOfProfiles_eq_L_iff w l p))
      (exists_congr fun q => and_congr_right fun _ =>
        (ERCVal.zero_lt_iff _).trans (ercOfProfiles_eq_W_iff w l q))).trans
    (Pi.lex_le_iff_forall (ofLex w) (ofLex l)).symm

/-- A ranking satisfies the ERC of a winner and a loser iff the winner's violations, read in the
order of the ranking, are lexicographically at most the loser's. -/
theorem satisfiedBy_ercOfProfiles_iff_le (r : Ranking ι n) (w l : ι → ℕ) :
    (ercOfProfiles w l).SatisfiedBy r ↔ toLex (w ∘ r) ≤ toLex (l ∘ r) :=
  lex_nonneg_ercOfProfiles_iff (toLex (w ∘ r)) (toLex (l ∘ r))

/-- The sign vector of the ERC of a winner and a loser is lexicographically positive in the order
of a ranking iff the winner's violations, read in that order, are strictly below the loser's. -/
theorem lex_pos_ercOfProfiles_iff_lt (r : Ranking ι n) (w l : ι → ℕ) :
    toLex 0 < toLex (ercOfProfiles w l ∘ r) ↔ toLex (w ∘ r) < toLex (l ∘ r) := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
  refine and_congr (satisfiedBy_ercOfProfiles_iff_le r w l) (not_congr ?_)
  simp only [toLex_inj, funext_iff]
  exact forall_congr' fun p ↦ eq_comm.trans (ercOfProfiles_eq_e_iff w l (r p))

/-- The ERC of a winner `w` against a loser `l` in the tableau `t`: the ranking requirements for
`w` to beat `l`. -/
def tableauERC {C : Type*} (t : Tableau C n) (w l : C) : ERC (Fin n) :=
  ercOfProfiles (t.constraints · w) (t.constraints · l)

/-- A ranking satisfies the ERC of `w` against `l` iff, under that ranking, the profile of `w`
is at most the profile of `l`. -/
theorem tableauERC_satisfiedBy_iff {C : Type*} (t : Tableau C n) (r : Ranking (Fin n) n)
    (w l : C) : (tableauERC t w l).SatisfiedBy r ↔ r • t.profile w ≤ r • t.profile l :=
  satisfiedBy_ercOfProfiles_iff_le r (t.constraints · w) (t.constraints · l)

theorem tableauERC_satisfiedBy_id_iff {C : Type*} (t : Tableau C n) (w l : C) :
    (tableauERC t w l).SatisfiedBy (1 : Ranking (Fin n) n) ↔ t.profile w ≤ t.profile l := by
  rw [tableauERC_satisfiedBy_iff]; exact Iff.rfl

theorem mem_optimal_iff_forall_satisfiedBy {C : Type*} (t : Tableau C n) (w : C) :
    w ∈ t.optimal ↔
      w ∈ t.candidates ∧
        ∀ l ∈ t.candidates, (tableauERC t w l).SatisfiedBy (1 : Ranking (Fin n) n) :=
  Tableau.mem_optimal_iff.trans <| and_congr_right fun _ =>
    forall₂_congr fun l _ => (tableauERC_satisfiedBy_id_iff t w l).symm

/-- A candidate `w` is optimal in `Tableau.ofRanking con r` iff `r` satisfies the ERC of `w`
against every competitor. -/
theorem Tableau.ofRanking_mem_optimal_iff_satisfiedBy {C : Type*} (con : ConstraintSet C ι)
    (r : Ranking ι n) (candidates : Finset C) (w : C) :
    w ∈ (Tableau.ofRanking con r candidates).optimal ↔
      w ∈ candidates ∧ ∀ l ∈ candidates, (ercOfProfiles (con · w) (con · l)).SatisfiedBy r :=
  Tableau.mem_optimal_iff.trans <| and_congr_right fun _ ↦ forall₂_congr fun l _ ↦
    (satisfiedBy_ercOfProfiles_iff_le r (con · w) (con · l)).symm

/-- The winner–loser ERCs of the candidate `o` at the input `i`, one against each rival. -/
def ConstraintSystem.ercs {I O : Type*} (S : ConstraintSystem I O ι) (i : I) (o : O) :
    Set (ERC ι) :=
  {α | ∃ o' ∈ S.gen i, o' ≠ o ∧ ercOfProfiles (S.con · (i, o)) (S.con · (i, o')) = α}

/-- A ranking picks a candidate whose violations differ from every rival's iff it satisfies the
candidate's ERC against each rival ([prince-2002]). -/
theorem ConstraintSystem.picksAt_iff_forall_ercs_satisfiedBy {I O : Type*}
    {S : ConstraintSystem I O ι} {σ : Ranking ι n} {i : I} {o : O} (ho : o ∈ S.gen i)
    (hvp : ∀ o' ∈ S.gen i, o' ≠ o → (S.con · (i, o)) ≠ (S.con · (i, o'))) :
    S.PicksAt σ i o ↔ ∀ α ∈ S.ercs i o, α.SatisfiedBy σ := by
  refine ⟨fun h α hα ↦ ?_, fun h ↦ ConstraintSystem.picksAt_iff.2 ⟨ho, fun o' ho' hne ↦ ?_⟩⟩
  · obtain ⟨o', ho', hne, rfl⟩ := hα
    exact (satisfiedBy_ercOfProfiles_iff_le σ _ _).2
      ((ConstraintSystem.picksAt_iff.1 h).2 o' ho' hne).le
  · refine lt_of_le_of_ne ((satisfiedBy_ercOfProfiles_iff_le σ _ _).1
      (h _ ⟨o', ho', hne, rfl⟩)) fun heq ↦ hvp o' ho' hne (funext fun c ↦ ?_)
    simpa using congrFun (toLex_inj.1 heq) (σ.symm c)

end OptimalityTheory
