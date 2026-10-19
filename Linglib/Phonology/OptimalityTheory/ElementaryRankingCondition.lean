module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# Elementary ranking conditions

OT's algebraic ranking-inference layer ([prince-2002]; [riggle-2009a]). An
ERC value is a *sign*, so the alphabet is mathlib's `SignType` — `W` (`+1`,
winner-preferring), `L` (`-1`, loser-preferring), `e` (`0`, neutral) — which buys
`ercOfProfiles` as a coordinatewise `SignType.sign`, the antithetical ERC as pointwise
negation, per-coordinate entailment as `SignType`'s own order `L ≤ e ≤ W`, and the
decidability instances for free.

A ranking satisfies an ERC iff its sign vector, read in the ranking's priority order,
is lex-nonnegative — equivalently (`ERC.satisfiedBy_iff_dominance`), every
`L`-constraint is outranked by some `W`-constraint ([prince-2002] §0 (3)/(4)).

## Main declarations

* `ERCVal`, `ERC ι` — the sign alphabet and sign vectors `ι → ERCVal` over the constraints `ι`.
* `ERC.SatisfiedBy` — satisfaction of one ERC by a ranking `Ranking ι n`;
  `ERC.linearExtensions` the permutations of `Fin n` satisfying a `Finset` of them.
  Consistency and entailment of ERC sets are `Nonempty` and `⊆` of linear-extension sets — no
  separate algebra.
* `ercOfProfiles`, `tableauERC` — ERCs from violation vectors and winner–loser
  pairs; `satisfiedBy_ercOfProfiles_iff_le` bridges to the Core lex order, and
  `Tableau.ofRanking_mem_optimal_iff_satisfiedBy` identifies optimality with ERC satisfaction.
* `simpleERC` — a single-`W`/single-`L` ERC, one Hasse edge `i ≫ j`
  ([merchant-riggle-2016]).
-/

@[expose] public section

namespace OptimalityTheory

variable {ι : Type*} {n : ℕ}

/-! ### The three-valued alphabet `ERCVal` -/

/-- An ERC value is a sign ([prince-2002] §0): `W` (winner-preferring), `L`
(loser-preferring), `e` (neutral). This is mathlib's `SignType` — see `ERCVal.W`,
`ERCVal.L`, `ERCVal.e`. -/
abbrev ERCVal := SignType

namespace ERCVal

/-- Winner-preferring value (`+1`). -/
@[match_pattern] abbrev W : ERCVal := .pos
/-- Loser-preferring value (`-1`). -/
@[match_pattern] abbrev L : ERCVal := .neg
/-- Neutral / indifferent value (`0`). -/
@[match_pattern] abbrev e : ERCVal := .zero

end ERCVal

/-! ### Elementary ranking conditions -/

/-- An elementary ranking condition over the constraints `ι`: a sign vector `ι → ERCVal`
([prince-2002] §0). -/
abbrev ERC (ι : Type*) := ι → ERCVal

namespace ERC

variable (α : ERC ι)

/-- An ERC is *trivial* if it has no `L`-constraint, so every ranking satisfies it. -/
def IsTrivial : Prop := ∀ k, α k ≠ .L

instance [Fintype ι] : Decidable α.IsTrivial := Fintype.decidableForallFintype

/-- An ERC is *contradictory* if it has an `L`-constraint but no
`W`-constraint, so no ranking satisfies it — Prince's class `𝓛⁺`. -/
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

namespace ERC

variable (r : Ranking ι n) (α : ERC ι)

/-- A ranking `r` *satisfies* ERC `α` iff its sign vector, read in `r`'s priority
order, is lexicographically nonnegative. -/
def SatisfiedBy : Prop := toLex 0 ≤ toLex (α ∘ r)

/-- **Prince's leading-entry characterization** ([prince-2002] §0): a ranking
satisfies an ERC iff the `r`-earliest non-neutral constraint, when one exists, is
winner-preferring. -/
theorem satisfiedBy_iff_lead :
    α.SatisfiedBy r ↔ ∀ he : ∃ p, α (r p) ≠ .e, α (r (Fin.find _ he)) = .W :=
  ⟨fun h he => (ERCVal.zero_lt_iff _).mp ((Pi.lex_le_iff_find _ _).mp h he),
   fun h => (Pi.lex_le_iff_find _ _).mpr fun he => (ERCVal.zero_lt_iff _).mpr (h he)⟩

/-- [prince-2002] §0 (3): satisfaction unfolds to the `∀∃` dominance form — every
loser-preferring constraint is dominated by some winner-preferring one. -/
theorem satisfiedBy_iff_dominance :
    α.SatisfiedBy r ↔ ∀ c, α c = .L → ∃ w, α w = .W ∧ r.Dominates w c := by
  rw [SatisfiedBy, show toLex (0 : Fin n → ERCVal) = toLex ((0 : ι → ERCVal) ∘ r) from rfl,
    Pi.toLex_comp_le_iff_forall_exists]
  simp only [Pi.zero_apply, ERCVal.lt_zero_iff, ERCVal.zero_lt_iff, Ranking.Dominates]

instance : Decidable (α.SatisfiedBy r) :=
  inferInstanceAs (Decidable (toLex 0 ≤ toLex (α ∘ r)))

/-- [prince-2002] §0 (4): the `∀∃` form is equivalent to the `∃∀` form — *some*
`W`-constraint dominates *every* `L`-constraint — because the ranking is total. -/
theorem satisfiedBy_iff_exists_dominant [NeZero n] :
    α.SatisfiedBy r ↔ ∃ d, ∀ c, α c = .L → (α d = .W ∧ r.Dominates d c) := by
  rw [SatisfiedBy, show toLex (0 : Fin n → ERCVal) = toLex ((0 : ι → ERCVal) ∘ r) from rfl,
    Pi.toLex_comp_le_iff_exists_forall]
  simp only [Pi.zero_apply, ERCVal.lt_zero_iff, ERCVal.zero_lt_iff, Ranking.Dominates]

/-- A trivial ERC is satisfied by every ranking. -/
theorem trivial_satisfiedBy {α : ERC ι} (htriv : α.IsTrivial) (r : Ranking ι n) :
    α.SatisfiedBy r :=
  (satisfiedBy_iff_dominance r α).mpr fun l hl => absurd hl (htriv l)

end ERC

/-! ### Linear extensions

Satisfaction of a `Finset (ERC (Fin n))` needs no vocabulary of its own: a ranking
satisfies the set iff `∀ α ∈ E, α.SatisfiedBy r`, the set is *consistent*
([prince-2002]) iff `(ERC.linearExtensions E).Nonempty`, and `E` *entails* `E'`
iff `ERC.linearExtensions E ⊆ ERC.linearExtensions E'`. -/

namespace ERC

/-- The rankings satisfying every member of a set of ERCs, as a `Finset` — its
*linear extensions* ([merchant-riggle-2016]). -/
def linearExtensions (E : Finset (ERC (Fin n))) : Finset (Ranking (Fin n) n) :=
  Finset.univ.filter fun r => ∀ α ∈ E, ERC.SatisfiedBy r α

@[simp] theorem mem_linearExtensions {E : Finset (ERC (Fin n))} {r : Ranking (Fin n) n} :
    r ∈ linearExtensions E ↔ ∀ α ∈ E, ERC.SatisfiedBy r α := by
  simp [linearExtensions]

/-- The empty set constrains nothing: every ranking is a linear extension. -/
@[simp] theorem linearExtensions_empty :
    linearExtensions (∅ : Finset (ERC (Fin n))) = Finset.univ := by
  ext r; simp

end ERC

/-! ### Simple ERCs -/

/-- The simple ERC asserting constraint `i` must dominate constraint `j`; all
other constraints are `e`. -/
def simpleERC [DecidableEq ι] (i j : ι) : ERC ι :=
  fun k => if k = i then .W else if k = j then .L else .e

section Simple

variable [DecidableEq ι] {i j : ι}

/-- The only `W` of `simpleERC i j` is at `i`. -/
theorem simpleERC_eq_W_iff (k : ι) :
    simpleERC i j k = .W ↔ k = i := by
  simp only [simpleERC]; split_ifs with h₁ h₂ <;> simp_all

/-- The only `L` of `simpleERC i j` (with `i ≠ j`) is at `j`. -/
theorem simpleERC_eq_L_iff (hij : i ≠ j) (k : ι) :
    simpleERC i j k = .L ↔ k = j := by
  simp only [simpleERC]; split_ifs with h₁ h₂ <;> simp_all

@[simp] theorem simpleERC_apply_W : simpleERC i j i = .W :=
  (simpleERC_eq_W_iff i).mpr rfl

theorem simpleERC_apply_L (hij : i ≠ j) : simpleERC i j j = .L :=
  (simpleERC_eq_L_iff hij j).mpr rfl

/-- The diagonal simple ERC `i ≫ i` has no `L`, hence is trivial. -/
theorem simpleERC_self_isTrivial (i : ι) : (simpleERC i i).IsTrivial := fun k => by
  simp only [simpleERC]; split_ifs <;> decide

/-- A simple ERC `i ≫ j` (with `i ≠ j`) is satisfied by `r` iff `i` dominates
`j` under `r`. -/
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

/-- Side-condition-free form: `simpleERC i j` is satisfied by `r` iff `i` is
ranked at least as high as `j` (`Ranking.toRel`). On the diagonal the ERC is
trivial and the relation reflexive, so no `i ≠ j` guard is needed. -/
theorem simpleERC_satisfiedBy_toRel_iff (i j : ι) (r : Ranking ι n) :
    (simpleERC i j).SatisfiedBy r ↔ r.toRel i j := by
  rcases eq_or_ne i j with rfl | hij
  · exact iff_of_true (ERC.trivial_satisfiedBy (simpleERC_self_isTrivial i) r) (le_refl _)
  · rw [simpleERC_satisfiedBy_iff hij, r.toRel_iff_dominates hij]

/-- A simple ERC `i ≫ j` (with `i ≠ j`) is consistent. -/
theorem simpleERC_consistent {i j : Fin n} (hij : i ≠ j) :
    (ERC.linearExtensions {simpleERC i j}).Nonempty :=
  have ⟨r, hr⟩ := Ranking.exists_dominates hij
  ⟨r, by simp [(simpleERC_satisfiedBy_iff hij r).mpr hr]⟩

/-- `simpleERC i j` (with `i ≠ j`) is a simple ERC. -/
theorem simpleERC_isSimple (hij : i ≠ j) : (simpleERC i j).IsSimple :=
  ⟨⟨i, simpleERC_apply_W, fun y hy => (simpleERC_eq_W_iff y).mp hy⟩,
   ⟨j, simpleERC_apply_L hij, fun y hy => (simpleERC_eq_L_iff hij y).mp hy⟩⟩

/-- Every `simpleERC` is simple or (on the diagonal) trivial. -/
theorem simpleERC_isSimple_or_isTrivial (i j : ι) :
    (simpleERC i j).IsSimple ∨ (simpleERC i j).IsTrivial := by
  rcases eq_or_ne i j with rfl | hij
  exacts [.inr (simpleERC_self_isTrivial i), .inl (simpleERC_isSimple hij)]

end Simple

/-! ### Bridges: profiles, tableaux, and the Core lex order -/

/-- The ERC of a winner/loser pair of violation vectors: the coordinatewise sign of
the violation difference ([prince-2002] §0; [riggle-2009a] Def. 3). -/
def ercOfProfiles (winner loser : ι → ℕ) : ERC ι :=
  fun k => SignType.sign ((loser k : ℤ) - (winner k : ℤ))

/-- `ercOfProfiles` is `W` exactly where the winner has strictly fewer
violations. -/
theorem ercOfProfiles_eq_W_iff (w l : ι → ℕ) (k : ι) :
    ercOfProfiles w l k = .W ↔ w k < l k := by
  simp only [ercOfProfiles, SignType.pos_eq_one, sign_eq_one_iff]; omega

/-- `ercOfProfiles` is `L` exactly where the winner has strictly more
violations. -/
theorem ercOfProfiles_eq_L_iff (w l : ι → ℕ) (k : ι) :
    ercOfProfiles w l k = .L ↔ l k < w k := by
  simp only [ercOfProfiles, SignType.neg_eq_neg_one, sign_eq_neg_one_iff]; omega

/-- `ercOfProfiles` is `e` exactly where violations are equal. -/
theorem ercOfProfiles_eq_e_iff (w l : ι → ℕ) (k : ι) :
    ercOfProfiles w l k = .e ↔ w k = l k := by
  simp only [ercOfProfiles, SignType.zero_eq_zero, sign_eq_zero_iff]; omega

/-- The *antithetical* ERC ([prince-2002] §2): swapping winner and loser negates it. -/
theorem ercOfProfiles_swap (w l : ι → ℕ) :
    ercOfProfiles l w = -ercOfProfiles w l := by
  funext k
  rw [Pi.neg_apply, ercOfProfiles, ercOfProfiles, ← neg_sub, Left.sign_neg]

/-- Construct an ERC from a list of `ERCVal`, with a length proof discharged by
`decide` for literals: `def myERC : ERC (Fin 4) := ercOfList [.W, .e, .L, .e]`. -/
def ercOfList (vs : List ERCVal) (h : vs.length = n := by decide) : ERC (Fin n) :=
  fun i => vs[i.val]'(by omega)

/-- Lex-nonnegativity of the sign vector is lex-comparison of the profiles: the sign
of the first difference decides both. -/
theorem lex_nonneg_ercOfProfiles_iff (w l : ViolationProfile n) :
    toLex (fun _ => (0 : ERCVal)) ≤ toLex (ercOfProfiles (ofLex w) (ofLex l)) ↔ w ≤ l :=
  (Pi.lex_le_iff_forall _ _).trans <|
    (forall_congr' fun p => imp_congr
      ((ERCVal.lt_zero_iff _).trans (ercOfProfiles_eq_L_iff w l p))
      (exists_congr fun q => and_congr_right fun _ =>
        (ERCVal.zero_lt_iff _).trans (ercOfProfiles_eq_W_iff w l q))).trans
    (Pi.lex_le_iff_forall (ofLex w) (ofLex l)).symm

/-- ERC satisfaction *is* lexicographic domination: `r` satisfies the ERC of a
winner/loser pair iff the winner's violations, read in `r`'s priority order, are lex-≤
the loser's ([prince-2002]). Precomposition with the ranking is absorbed by
instantiating `lex_nonneg_ercOfProfiles_iff` at the ranked readings. -/
theorem satisfiedBy_ercOfProfiles_iff_le (r : Ranking ι n) (w l : ι → ℕ) :
    (ercOfProfiles w l).SatisfiedBy r ↔ toLex (w ∘ r) ≤ toLex (l ∘ r) :=
  lex_nonneg_ercOfProfiles_iff (toLex (w ∘ r)) (toLex (l ∘ r))

/-- The ERC of a winner-loser pair `(w, l)` in tableau `t`: the ranking requirements
for `w` to beat `l`. -/
def tableauERC {C : Type*} (t : Tableau C n) (w l : C) : ERC (Fin n) :=
  ercOfProfiles (t.constraints · w) (t.constraints · l)

/-- Tableau form of the bridge: the winner-loser ERC is satisfied by `r` iff `r`
ranks the winner at-or-above the loser under the tableau's lex evaluation. -/
theorem tableauERC_satisfiedBy_iff {C : Type*} (t : Tableau C n) (r : Ranking (Fin n) n)
    (w l : C) : (tableauERC t w l).SatisfiedBy r ↔ r • t.profile w ≤ r • t.profile l :=
  satisfiedBy_ercOfProfiles_iff_le r (t.constraints · w) (t.constraints · l)

/-- At the identity ranking, ERC satisfaction is exactly the tableau's own lex
comparison — connecting ERC inference to the tableau's winner set. -/
theorem tableauERC_satisfiedBy_id_iff {C : Type*} (t : Tableau C n) (w l : C) :
    (tableauERC t w l).SatisfiedBy (1 : Ranking (Fin n) n) ↔ t.profile w ≤ t.profile l := by
  rw [tableauERC_satisfiedBy_iff]; exact Iff.rfl

/-- A candidate is the tableau's optimum iff, under the identity ranking, its ERC
against every competitor is satisfied — ERC consistency *is* optimality. -/
theorem mem_optimal_iff_forall_satisfiedBy {C : Type*} (t : Tableau C n) (w : C) :
    w ∈ t.optimal ↔
      w ∈ t.candidates ∧
        ∀ l ∈ t.candidates, (tableauERC t w l).SatisfiedBy (1 : Ranking (Fin n) n) :=
  Tableau.mem_optimal_iff.trans <| and_congr_right fun _ =>
    forall₂_congr fun l _ => (tableauERC_satisfiedBy_id_iff t w l).symm

/-- **Optimality under a ranking is ERC satisfaction**: `w` is optimal in `Tableau.ofRanking con r`
iff `r` satisfies the winner–loser ERC of `w` against every competitor, so factorial typology and
ERC consistency are two readouts of one constraint set. -/
theorem Tableau.ofRanking_mem_optimal_iff_satisfiedBy {C : Type*} (con : ConstraintSet C ι)
    (r : Ranking ι n) (candidates : Finset C) (w : C) :
    w ∈ (Tableau.ofRanking con r candidates).optimal ↔
      w ∈ candidates ∧ ∀ l ∈ candidates, (ercOfProfiles (con · w) (con · l)).SatisfiedBy r :=
  Tableau.mem_optimal_iff.trans <| and_congr_right fun _ ↦ forall₂_congr fun l _ ↦
    (satisfiedBy_ercOfProfiles_iff_le r (con · w) (con · l)).symm

end OptimalityTheory
