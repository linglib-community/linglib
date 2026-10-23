module

public import Linglib.Phonology.OptimalityTheory.Grammar
public import Linglib.Phonology.OptimalityTheory.Typology
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Order.Setoid.Basic

/-!
# Merchant and Prince (2022): The Mother of All Tableaux

Merchant and Prince study the large-scale structure of an OT typology, the partition of the
rankings (legs) into grammars. A row of a tableau asserted optimal generates the elementary ranking
conditions of its winner–loser comparisons (`rowERCs`), and the grammar of that row, in the hub of
Merchant and Riggle, consists of the legs under which the row wins lexicographically
(`mem_rowGrammar_legs_iff_lex`).

Any partition of the legs has border point pairs, legs in different blocks that differ by
transposing two adjacent constraints. For each constraint `c`, the pairs that transpose `c` with
the constraint below it relate blocks (`BorderLT`), and the transpositions below `c` join blocks
into an equivalence (`gepoRel`). The hypertransitive closure of the first relation with respect to
the second (`HtcLT`) need not be an order. Merchant and Prince's Theorema Egregium says that a
partition is a typology, the typology of some OT system, iff all these closures are irreflexive
(`isTypology_iff_isAcyclic`). Their partition (164) has a cycle and is no typology; their
partition (165) is the typology of the tableau (166).

## Main definitions

* `BorderLT`, `PrefixSwap`, `gepoRel`, `HtcLT`: the relations of a partition's GEPO for a
  constraint, definitions (160), (161), (163) and (169).
* `IsAcyclic`: every GEPO's hypertransitive closure is irreflexive, definitions (277) and (278).
* `Instantiates`: a function on legs reads a GEPO's equivalence as `=` and its relation as `<`.
* `IsTypology`: the partition is the typology of some `ConstraintSystem`.

## Main results

* `exists_instantiates_iff`: a GEPO can be instantiated iff it is acyclic, Lemma (280).
* `toLex_lt_of_not_rel`: under instantiating functions each leg's own block has the least row,
  Lemma (287).
* `isTypology_of_instantiates`: an instantiated GMOAT is a typology, Theorem (288).
* `isTypology_iff_isAcyclic`: the Theorema Egregium, Theorem (290).

## Implementation notes

Numbers refer to version 2.1.1 of the paper. The relations are stated on legs rather than on
blocks: a relation between blocks holds iff it holds between some of their legs, and the
equivalence `gepoRel` contains `π`, so every relation built from it is saturated by `π`.
`PrefixSwap` also relates legs of the same block, which (161) excludes but its equivalence closure
(163) contains anyway. The hypertransitive closure is the transitive closure of the base relation
composed on both sides with the equivalence, which is the least relation closed under the clauses
of (152).

Merchant and Prince prove Theorem (288) through prefix separation (Lemma (286)). Here Lemma (287)
is proved directly by bubbling: moving the constraint a leg ranks `k`-th up to position `k` never
increases its instantiating function, and strictly decreases it whenever the block changes, so
the blocks whose rows tie with a leg's row on its top `k` constraints are the blocks that meet the
legs sharing its top `k` positions.

## References

* [merchant-prince-2022]
* [merchant-riggle-2016]
* [prince-smolensky-1993]
* [prince-2002]
-/

@[expose] public section

namespace MerchantPrince2022

open OptimalityTheory

section RowGrammar

variable {C : Type*} [DecidableEq C] {n : ℕ}

/-- The ERC set of a tableau row `w` collects `w`'s winner–loser ERCs against every other
candidate, the ranking conditions a leg must satisfy for `w` to be optimal ([prince-2002]). -/
def rowERCs (t : Tableau C n) (w : C) : Finset (ERC (Fin n)) :=
  (t.candidates.erase w).image (tableauERC t w)

/-- The **grammar of a tableau row** is the grammar of the row's ERC set in the `Grammar` hub
([merchant-prince-2022]; [merchant-riggle-2016]). The hypothesis `h` says that the row's conditions
are consistent, so that `w` is an optimum that no competitor harmonically bounds. -/
def rowGrammar (t : Tableau C n) (w : C)
    (h : (ERC.linearExtensions (rowERCs t w)).Nonempty) : Grammar n :=
  Grammar.ofERCs (rowERCs t w) h

@[simp] theorem mem_rowGrammar_legs {t : Tableau C n} {w : C}
    {h : (ERC.linearExtensions (rowERCs t w)).Nonempty} {r : Ranking (Fin n) n} :
    r ∈ (rowGrammar t w h).legs ↔ ∀ α ∈ rowERCs t w, ERC.SatisfiedBy r α := by
  simp only [rowGrammar, Grammar.legs_ofERCs, ERC.mem_linearExtensions]

theorem mem_rowGrammar_legs_iff_lex {t : Tableau C n} {w : C}
    {h : (ERC.linearExtensions (rowERCs t w)).Nonempty} {r : Ranking (Fin n) n} :
    r ∈ (rowGrammar t w h).legs ↔
      ∀ l ∈ t.candidates.erase w,
        r • t.profile w ≤ r • t.profile l := by
  rw [mem_rowGrammar_legs]
  unfold rowERCs
  constructor
  · intro hsat l hl
    exact (tableauERC_satisfiedBy_iff t r w l).mp
      (hsat _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩))
  · intro hlex α hα
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hα
    exact (tableauERC_satisfiedBy_iff t r w l).mpr (hlex l hl)

end RowGrammar

/-! ### Border points and the GMOAT of a partition -/

section GMOAT

universe u

variable {ι : Type u} {n : ℕ} (π : Setoid (Ranking ι n)) (c : ι)

/-- `BorderLT π c r s` holds when the leg `r` ranks `c` immediately above some constraint, `s`
transposes the two, and `r` and `s` lie in different blocks of `π`, so that `{r, s}` is a border
point pair (159). Between blocks it is the base relation `≺π.bp.c` of (160). -/
def BorderLT (r s : Ranking ι n) : Prop :=
  ∃ k, ∃ hk : k + 1 < n, r ⟨k, Nat.lt_of_succ_lt hk⟩ = c ∧ s = r.swapAt k hk ∧ ¬ π r s

/-- `PrefixSwap c r s` holds when `s` transposes two adjacent constraints that `r` ranks below
`c`. These pairs generate the base relation `≡π.bp.c` of (161). -/
def PrefixSwap (r s : Ranking ι n) : Prop :=
  ∃ k, ∃ hk : k + 1 < n, (r.symm c).val < k ∧ s = r.swapAt k hk

/-- The GEPO equivalence `~π.bp.c` of (163) joins the blocks of `π` across transpositions below
`c`. -/
def gepoRel : Setoid (Ranking ι n) := π ⊔ Relation.EqvGen.setoid (PrefixSwap c)

/-- The hypertransitive closure `<π.htc.bp.c` of (152) and (169) closes the base relation under
composition and under the GEPO equivalence on either side. -/
def HtcLT : Ranking ι n → Ranking ι n → Prop :=
  Relation.TransGen fun r s ↦ ∃ μ ν, gepoRel π c r μ ∧ BorderLT π c μ ν ∧ gepoRel π c ν s

/-- The GMOAT of a partition is **acyclic** (definitions (277) and (278)) when for every
constraint the hypertransitive closure of the base relation is irreflexive, and hence, being
transitive, a strict partial order. -/
def IsAcyclic : Prop := ∀ c r, ¬ HtcLT π c r r

/-- A function on legs **instantiates** the GEPO of `c` when it is constant on GEPO-equivalent
legs and increases strictly across the base relation. -/
def Instantiates (f : Ranking ι n → ℕ) : Prop :=
  gepoRel π c ≤ Setoid.ker f ∧ ∀ r s, BorderLT π c r s → f r < f s

/-- A partition of the rankings is a **typology** when it is the typology of some OT system over
the constraints. -/
def IsTypology : Prop := ∃ (I O : Type u) (S : ConstraintSystem I O ι), S.typology = π

variable {π c}

theorem le_gepoRel : π ≤ gepoRel π c := le_sup_left

theorem PrefixSwap.gepoRel {r s : Ranking ι n} (h : PrefixSwap c r s) : gepoRel π c r s :=
  (le_sup_right : Relation.EqvGen.setoid (PrefixSwap c) ≤ _) (Relation.EqvGen.rel _ _ h)

theorem HtcLT.trans_gepoRel {r s t : Ranking ι n} (h : HtcLT π c r s)
    (hst : gepoRel π c s t) : HtcLT π c r t := by
  obtain ⟨b, hrb, μ, ν, hbμ, hμν, hνs⟩ := Relation.TransGen.tail'_iff.1 h
  exact Relation.TransGen.tail' hrb ⟨μ, ν, hbμ, hμν, (gepoRel π c).iseqv.trans hνs hst⟩

theorem irreflexive_htcLT_of_forall {κ : Type*} (g : κ → Ranking ι n → ℕ)
    (hg : ∀ j, gepoRel π c ≤ Setoid.ker (g j))
    (hle : ∀ r s, BorderLT π c r s → ∀ j, g j r ≤ g j s)
    (hlt : ∀ r s, BorderLT π c r s → ∃ j, g j r < g j s) : ∀ r, ¬ HtcLT π c r r := by
  intro r h
  obtain ⟨b, ⟨μ, ν, hrμ, hμν, hνb⟩, hbr⟩ := Relation.TransGen.head'_iff.1 h
  have hmono (j : κ) : g j b ≤ g j r := by
    clear h hrμ
    induction hbr with
    | refl => exact le_rfl
    | tail _ hst ih =>
      obtain ⟨μ', ν', h₁, h₂, h₃⟩ := hst
      exact ih.trans ((Setoid.ker_def.1 (hg j h₁)).le.trans
        ((hle _ _ h₂ j).trans (Setoid.ker_def.1 (hg j h₃)).le))
  obtain ⟨j, hj⟩ := hlt μ ν hμν
  exact ((Setoid.ker_def.1 (hg j hrμ)).trans_lt hj |>.trans_le
    ((Setoid.ker_def.1 (hg j hνb)).le.trans (hmono j))).false

/-- A GEPO can be instantiated iff it is acyclic (Lemma (280)). -/
theorem exists_instantiates_iff [Fintype ι] [DecidableEq ι] :
    (∃ f, Instantiates π c f) ↔ ∀ r, ¬ HtcLT π c r r := by
  classical
  refine ⟨fun ⟨f, hf⟩ ↦ irreflexive_htcLT_of_forall (fun (_ : Unit) ↦ f) (fun _ ↦ hf.1)
    (fun r s h _ ↦ (hf.2 r s h).le) fun r s h ↦ ⟨(), hf.2 r s h⟩, fun h ↦ ?_⟩
  refine ⟨fun r ↦ (Finset.univ.filter (HtcLT π c · r)).card, fun r s hrs ↦ ?_, fun r s hrs ↦ ?_⟩
  · refine Setoid.ker_def.2 (congrArg Finset.card (Finset.filter_congr fun x _ ↦ ?_))
    exact ⟨fun hx ↦ hx.trans_gepoRel hrs, fun hx ↦ hx.trans_gepoRel
      ((gepoRel π c).iseqv.symm hrs)⟩
  · convert Relation.TransGen.card_filter_lt_card_filter h (.single ⟨r, s,
      (gepoRel π c).iseqv.refl r, hrs, (gepoRel π c).iseqv.refl s⟩)
    all_goals exact Iff.rfl

/-! #### Filtration by instantiating functions -/

private theorem exists_bubble (P : Ranking ι n → Ranking ι n → Prop) (hrefl : ∀ μ, P μ μ)
    (htrans : ∀ a b d, P a b → P b d → P a d) (c : ι) (k : ℕ) (μ₀ : Ranking ι n)
    (hstep : ∀ μ : Ranking ι n, ∀ m (hm : m + 1 < n), k ≤ m → μ ⟨m + 1, hm⟩ = c →
      (∀ j : Fin n, j.val < k → μ j = μ₀ j) → P μ (μ.swapAt m hm)) :
    ∀ d (μ : Ranking ι n), (μ.symm c).val = k + d → (∀ j : Fin n, j.val < k → μ j = μ₀ j) →
      ∃ μ', (μ'.symm c).val = k ∧ (∀ j : Fin n, j.val < k → μ' j = μ₀ j) ∧ P μ μ' := by
  intro d
  induction d with
  | zero => exact fun μ hμ hpre ↦ ⟨μ, hμ, hpre, hrefl μ⟩
  | succ d ih =>
    intro μ hμ hpre
    have hm : k + d + 1 < n := by have := (μ.symm c).isLt; omega
    have hc : μ ⟨k + d + 1, hm⟩ = c := by
      rw [← μ.apply_symm_apply c]
      exact congrArg μ (Fin.ext (by simp only; omega))
    have hsymm : (μ.swapAt (k + d) hm).symm c = ⟨k + d, Nat.lt_of_succ_lt hm⟩ :=
      (Equiv.symm_apply_eq _).2 (by rw [Ranking.swapAt_apply_left, hc])
    obtain ⟨μ', h₁, h₂, h₃⟩ := ih (μ.swapAt (k + d) hm) (by rw [hsymm])
      fun j hj ↦ by rw [Ranking.swapAt_apply_of_ne (by omega) (by omega)]; exact hpre j hj
    exact ⟨μ', h₁, h₂, htrans _ _ _ (hstep μ (k + d) hm (Nat.le_add_right k d) hc hpre) h₃⟩

private theorem le_symm_apply {l ν : Ranking ι n} {t : ℕ} {c : ι} (ht : t < n)
    (hc : l ⟨t, ht⟩ = c) (hν : ∀ j : Fin n, j.val < t → ν j = l j) : t ≤ (ν.symm c).val := by
  subst hc
  by_contra hlt
  have := hν _ (not_le.1 hlt)
  rw [Equiv.apply_symm_apply] at this
  have := congrArg Fin.val (l.injective this)
  simp only at this
  omega

private theorem apply_eq_of_lt_succ {l ν : Ranking ι n} {k : ℕ} {c : ι} (hk : k < n)
    (hc : l ⟨k, hk⟩ = c) (hpos : (ν.symm c).val = k) (hν : ∀ j : Fin n, j.val < k → ν j = l j)
    (j : Fin n) (hj : j.val < k + 1) : ν j = l j := by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
  · exact hν j hj
  · rw [← (Equiv.symm_apply_eq _).1 (Fin.ext (hpos.trans hj.symm)), ← hc]
    exact congrArg l (Fin.ext hj.symm)

variable {f : ι → Ranking ι n → ℕ}

private theorem eq_of_forall_apply_eq (hf : Instantiates π c (f c)) (l : Ranking ι n) (k : ℕ)
    (hk : k < n) (hc : l ⟨k, hk⟩ = c) :
    ∀ d t, t + d = n → k < t → ∀ ν : Ranking ι n, (∀ j : Fin n, j.val < t → ν j = l j) →
      f c ν = f c l := by
  intro d
  induction d with
  | zero =>
    intro t ht _ ν hν
    exact congrArg (f c) (Equiv.ext fun j ↦ hν j (by have := j.isLt; omega))
  | succ d ih =>
    intro t ht hkt ν hν
    have htn : t < n := by omega
    have hstep (μ : Ranking ι n) (m : ℕ) (hm : m + 1 < n) (htm : t ≤ m)
        (hpre : ∀ j : Fin n, j.val < t → μ j = ν j) : f c μ = f c (μ.swapAt m hm) := by
      refine Setoid.ker_def.1 (hf.1 (PrefixSwap.gepoRel ⟨m, hm, ?_, rfl⟩))
      have : μ.symm c = ⟨k, hk⟩ := (Equiv.symm_apply_eq _).2
        ((hc.symm.trans (hν ⟨k, hk⟩ hkt).symm).trans (hpre ⟨k, hk⟩ hkt).symm)
      rw [this]
      exact lt_of_lt_of_le hkt htm
    obtain ⟨ν', h₁, h₂, h₃⟩ := exists_bubble (fun a b ↦ f c a = f c b) (fun _ ↦ rfl)
      (fun _ _ _ ↦ Eq.trans) (l ⟨t, htn⟩) t ν (fun μ m hm htm _ hpre ↦ hstep μ m hm htm hpre)
      ((ν.symm (l ⟨t, htn⟩)).val - t) ν (by have := le_symm_apply htn rfl hν; omega)
      fun _ _ ↦ rfl
    exact h₃.trans (ih (t + 1) (by omega) (by omega) ν'
      (apply_eq_of_lt_succ htn rfl h₁ fun j hj ↦ (h₂ j hj).trans (hν j hj)))

/-- Under instantiating functions, within the top `k` constraints of `l` every leg's row either
matches that of `l`, via a block agreeing with `l`, or lies lexicographically above it (Lemma
(287)). -/
private theorem filtration (hf : ∀ c, Instantiates π c (f c)) (l : Ranking ι n) :
    ∀ k ≤ n, ∀ μ : Ranking ι n,
      (∃ j : Fin n, j.val < k ∧ (∀ j' < j, f (l j') μ = f (l j') l) ∧ f (l j) l < f (l j) μ) ∨
      ((∀ j : Fin n, j.val < k → f (l j) μ = f (l j) l) ∧
        ∃ μ', π μ μ' ∧ ∀ j : Fin n, j.val < k → μ' j = l j) := by
  intro k
  induction k with
  | zero => exact fun _ μ ↦ .inr ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _),
      μ, π.iseqv.refl μ, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk μ
    rcases ih (by omega) μ with ⟨j, hj, hpre, hlt⟩ | ⟨heq, μ', hμμ', hpre⟩
    · exact .inl ⟨j, by omega, hpre, hlt⟩
    have hkn : k < n := by omega
    generalize hc : l ⟨k, hkn⟩ = c
    have hstep (a : Ranking ι n) (m : ℕ) (hm : m + 1 < n) (hcm : a ⟨m + 1, hm⟩ = c) :
        f c (a.swapAt m hm) ≤ f c a ∧ (f c (a.swapAt m hm) = f c a → π a (a.swapAt m hm)) := by
      by_cases hπ : π a (a.swapAt m hm)
      · exact ⟨(Setoid.ker_def.1 ((hf c).1 (le_gepoRel hπ))).ge, fun _ ↦ hπ⟩
      · have hlt := (hf c).2 _ _ ⟨m, hm, by rw [Ranking.swapAt_apply_left, hcm],
          Ranking.swapAt_swapAt.symm, fun h ↦ hπ (π.iseqv.symm h)⟩
        exact ⟨hlt.le, fun h ↦ absurd h hlt.ne⟩
    obtain ⟨μ'', h₁, h₂, h₃⟩ := exists_bubble
      (fun a b ↦ f c b ≤ f c a ∧ (f c b = f c a → π a b))
      (fun a ↦ ⟨le_rfl, fun _ ↦ π.iseqv.refl a⟩)
      (fun a b d hab hbd ↦ ⟨hbd.1.trans hab.1, fun he ↦
        have hba : f c b = f c a := le_antisymm hab.1 (he ▸ hbd.1)
        π.iseqv.trans (hab.2 hba) (hbd.2 (he.trans hba.symm))⟩)
      c k μ' (fun a m hm _ hcm _ ↦ hstep a m hm hcm) ((μ'.symm c).val - k) μ'
      (by have := le_symm_apply hkn hc hpre; omega) fun _ _ ↦ rfl
    have hpre'' := apply_eq_of_lt_succ hkn hc h₁ fun j hj ↦ (h₂ j hj).trans (hpre j hj)
    have hl : f c μ'' = f c l :=
      eq_of_forall_apply_eq (hf c) l k hkn hc (n - (k + 1)) (k + 1) (by omega) (by omega) μ''
        hpre''
    have hμ : f c μ = f c μ' := Setoid.ker_def.1 ((hf c).1 (le_gepoRel hμμ'))
    by_cases hfc : f c μ = f c l
    · refine .inr ⟨fun j hj ↦ ?_, μ'', π.iseqv.trans hμμ' (h₃.2 (hl.trans (hfc.symm.trans hμ))),
        hpre''⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact heq j hj
      · rw [show j = ⟨k, hkn⟩ from Fin.ext hj, hc]
        exact hfc
    · refine .inl ⟨⟨k, hkn⟩, Nat.lt_succ_self k, fun j' hj' ↦ heq j' hj', ?_⟩
      rw [hc]
      exact lt_of_le_of_ne ((hl.symm.trans_le h₃.1).trans_eq hμ.symm) (Ne.symm hfc)

/-- Under instantiating functions, every leg outside a leg's block has a strictly higher row in that
leg's rank order (Lemma (287)). -/
theorem toLex_lt_of_not_rel (hf : ∀ c, Instantiates π c (f c)) (l : Ranking ι n)
    {μ : Ranking ι n} (h : ¬ π l μ) :
    toLex ((fun c ↦ f c l) ∘ l) < toLex ((fun c ↦ f c μ) ∘ l) := by
  rcases filtration hf l n le_rfl μ with ⟨j, -, hpre, hlt⟩ | ⟨-, μ', hμμ', hpre⟩
  · exact ⟨j, fun j' hj' ↦ (hpre j' hj').symm, hlt⟩
  · obtain rfl : μ' = l := Equiv.ext fun j ↦ hpre j j.isLt
    exact absurd (π.iseqv.symm hμμ') h

private theorem exists_lt_of_language_ne {I O : Type*} (S : ConstraintSystem I O ι)
    {r : Ranking ι n} {k : ℕ} (hk : k + 1 < n) {i : I}
    (hne : S.language r i ≠ S.language (r.swapAt k hk) i) :
    ∃ x ∈ S.language r i, ∃ y ∈ S.language (r.swapAt k hk) i,
      (∀ j < (⟨k, by omega⟩ : Fin n), S.con (r j) (i, x) = S.con (r j) (i, y)) ∧
        S.con (r ⟨k, by omega⟩) (i, x) < S.con (r ⟨k, by omega⟩) (i, y) := by
  have hgen : (S.gen i).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    exact hne ((Finset.subset_empty.1 (h0 ▸ Tableau.optimal_subset)).trans
      (Finset.subset_empty.1 (h0 ▸ Tableau.optimal_subset)).symm)
  obtain ⟨x, hx⟩ := ConstraintSystem.language_nonempty (r := r) hgen
  obtain ⟨y, hy⟩ := ConstraintSystem.language_nonempty (r := r.swapAt k hk) hgen
  have hxy : (fun c ↦ S.con c (i, x)) ≠ fun c ↦ S.con c (i, y) := fun he ↦ hne <|
    Finset.ext fun o ↦ by
      rw [ConstraintSystem.mem_language_iff_of_mem hx, ConstraintSystem.mem_language_iff_of_mem hy]
      exact and_congr_right fun _ ↦ forall_congr' fun c ↦ by rw [congrFun he c]
  have hne' {e : Ranking ι n} {v w : ι → ℕ} (h : v ≠ w) : toLex (v ∘ e) ≠ toLex (w ∘ e) :=
    fun he ↦ h (funext fun c ↦ by simpa using congrFun (toLex.injective he) (e.symm c))
  have hlt : toLex ((fun c ↦ S.con c (i, x)) ∘ r) < toLex ((fun c ↦ S.con c (i, y)) ∘ r) :=
    lt_of_le_of_ne (Tableau.le_of_mem_optimal hx (show y ∈ S.gen i from Tableau.optimal_subset hy))
      (hne' hxy)
  have hlt' : toLex ((fun c ↦ S.con c (i, y)) ∘ r.swapAt k hk) <
      toLex ((fun c ↦ S.con c (i, x)) ∘ r.swapAt k hk) :=
    lt_of_le_of_ne (Tableau.le_of_mem_optimal hy (show x ∈ S.gen i from Tableau.optimal_subset hx))
      (hne' hxy.symm)
  have hcov : (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n) ⋖ ⟨k + 1, hk⟩ :=
    ⟨Fin.mk_lt_mk.2 (Nat.lt_succ_self k), fun j h₁ h₂ ↦ by
      rw [Fin.lt_def] at h₁ h₂
      simp only at h₁ h₂
      omega⟩
  obtain ⟨h₁, h₂, -⟩ := Pi.eq_and_lt_and_gt_of_toLex_comp_swap r hcov hlt hlt'
  exact ⟨x, hx, y, hy, h₁, h₂⟩

/-- A typology has an acyclic GMOAT (the left-to-right half of Theorem (290)). -/
theorem IsTypology.isAcyclic (h : IsTypology π) : IsAcyclic π := by
  obtain ⟨I, O, S, rfl⟩ := h
  intro c
  let g (i : I) (r : Ranking ι n) : ℕ :=
    if h : (S.language r i).Nonempty then S.con c (i, h.choose) else 0
  have hg_of_mem {i r o} (ho : o ∈ S.language r i) : g i r = S.con c (i, o) := by
    have hne : (S.language r i).Nonempty := ⟨o, ho⟩
    simp only [g, hne, ↓reduceDIte]
    exact ConstraintSystem.con_eq_of_mem_language hne.choose_spec ho c
  have hg_of_eq {i r s} (h : S.language r i = S.language s i) : g i r = g i s := by
    simp only [g, h]
  refine irreflexive_htcLT_of_forall g (fun i ↦ sup_le (fun r s h ↦ ?_) ?_) (fun r s h i ↦ ?_)
    fun r s h ↦ ?_
  · exact hg_of_eq (congrFun (ConstraintSystem.typology_iff.1 h) i)
  · refine Setoid.eqvGen_le fun r s ⟨k, hk, hck, hs⟩ ↦ ?_
    subst hs
    by_cases hL : S.language r i = S.language (r.swapAt k hk) i
    · exact hg_of_eq hL
    obtain ⟨x, hx, y, hy, h₁, -⟩ := exists_lt_of_language_ne S hk hL
    have := h₁ (r.symm c) hck
    rw [Equiv.apply_symm_apply] at this
    exact (hg_of_mem hx).trans (this.trans (hg_of_mem hy).symm)
  · obtain ⟨k, hk, hrk, rfl, -⟩ := h
    by_cases hL : S.language r i = S.language (r.swapAt k hk) i
    · exact (hg_of_eq hL).le
    obtain ⟨x, hx, y, hy, -, h₂⟩ := exists_lt_of_language_ne S hk hL
    rw [hg_of_mem hx, hg_of_mem hy, ← hrk]
    exact h₂.le
  · obtain ⟨k, hk, hrk, rfl, hπ⟩ := h
    obtain ⟨i, hL⟩ := Function.ne_iff.1 (mt ConstraintSystem.typology_iff.2 hπ)
    obtain ⟨x, hx, y, hy, -, h₂⟩ := exists_lt_of_language_ne S hk hL
    refine ⟨i, ?_⟩
    rw [hg_of_mem hx, hg_of_mem hy, ← hrk]
    exact h₂

variable [Fintype ι] [DecidableEq ι]

/-- An instantiated GMOAT is a typology (Theorem (288)). -/
theorem isTypology_of_instantiates (hf : ∀ c, Instantiates π c (f c)) : IsTypology π := by
  let S : ConstraintSystem PUnit.{u + 1} (Ranking ι n) ι := ⟨fun _ ↦ Finset.univ, fun c x ↦ f c x.2⟩
  have hrow : ∀ {μ ν : Ranking ι n}, π μ ν → ∀ c, f c μ = f c ν := fun h c ↦
    Setoid.ker_def.1 ((hf c).1 (le_gepoRel h))
  have hmem : ∀ r μ, μ ∈ S.language r PUnit.unit ↔ π r μ := by
    intro r μ
    refine ⟨fun h ↦ not_not.1 fun hrμ ↦ ?_, fun h ↦ Tableau.mem_optimal_iff.2
      ⟨Finset.mem_univ _, fun ν _ ↦ ?_⟩⟩
    · exact (toLex_lt_of_not_rel hf r hrμ).not_ge
        (Tableau.le_of_mem_optimal h (Finset.mem_univ r))
    · show toLex ((fun c ↦ f c μ) ∘ r) ≤ toLex ((fun c ↦ f c ν) ∘ r)
      rw [show (fun c ↦ f c μ) = fun c ↦ f c r from funext fun c ↦ (hrow h c).symm]
      by_cases hrν : π r ν
      · rw [show (fun c ↦ f c ν) = fun c ↦ f c r from funext fun c ↦ (hrow hrν c).symm]
      · exact (toLex_lt_of_not_rel hf r hrν).le
  refine ⟨PUnit, Ranking ι n, S, Setoid.ext fun r s ↦ ?_⟩
  rw [ConstraintSystem.typology_iff]
  refine ⟨fun h ↦ (hmem r s).1 (h ▸ (hmem s s).2 (π.iseqv.refl s)), fun h ↦ funext fun _ ↦
    Finset.ext fun μ ↦ ?_⟩
  rw [hmem, hmem]
  exact ⟨π.iseqv.trans (π.iseqv.symm h), π.iseqv.trans h⟩

/-- A partition of the rankings is a typology iff its GMOAT is acyclic, Merchant and Prince's
**Theorema Egregium** (Theorem (290)). -/
theorem isTypology_iff_isAcyclic : IsTypology π ↔ IsAcyclic π := by
  refine ⟨IsTypology.isAcyclic, fun h ↦ ?_⟩
  choose f hf using fun c ↦ exists_instantiates_iff.2 (h c)
  exact isTypology_of_instantiates hf

end GMOAT

/-! ### Two partitions of the rankings of three constraints -/

section Examples

/-- Three constraints `X`, `Y`, `Z`. -/
inductive Con
  | X
  | Y
  | Z
  deriving DecidableEq, Fintype

/-- The leg `a ≫ b ≫ c`. -/
def leg (a b c : Con) (h : [a, b, c].Nodup := by decide) (h' : ∀ x, x ∈ [a, b, c] := by decide) :
    Ranking Con 3 :=
  Ranking.ofList [a, b, c] h h'

/-- The block `O = {YXZ, XZY, ZYX}` of the partition (164). -/
def blockO : Finset (Ranking Con 3) := {leg .Y .X .Z, leg .X .Z .Y, leg .Z .Y .X}

/-- The partition (164) of the six legs into `O` and `B = {XYZ, ZXY, YZX}`. -/
def partition164 : Setoid (Ranking Con 3) := Setoid.ker (· ∈ blockO)

theorem partition164_iff {r s : Ranking Con 3} : partition164 r s ↔ (r ∈ blockO ↔ s ∈ blockO) :=
  Setoid.ker_def.trans eq_iff_iff

/-- The GEPO of `X` in (164) has a cycle through the border point pairs `{XZY, ZXY}` and `{ZXY,
ZYX}`. -/
theorem htcLT_X_cycle : HtcLT partition164 .X (leg .X .Z .Y) (leg .X .Z .Y) := by
  have h₁ : BorderLT partition164 .X (leg .X .Z .Y) (leg .Z .X .Y) :=
    ⟨0, by decide, by decide, by decide, by rw [partition164_iff]; decide⟩
  have h₂ : BorderLT partition164 .X (leg .Z .X .Y) (leg .Z .Y .X) :=
    ⟨1, by decide, by decide, by decide, by rw [partition164_iff]; decide⟩
  have h₃ : gepoRel partition164 .X (leg .Z .Y .X) (leg .X .Z .Y) :=
    le_gepoRel (partition164_iff.2 (by decide))
  exact .tail (.single ⟨_, _, Setoid.refl' _ _, h₁, Setoid.refl' _ _⟩)
    ⟨_, _, Setoid.refl' _ _, h₂, h₃⟩

/-- The partition (164) is not a typology. -/
theorem not_isTypology_partition164 : ¬ IsTypology partition164 :=
  fun h ↦ h.isAcyclic .X _ htcLT_X_cycle

/-- The typology (165) separates `GB`, the legs with `X ≫ Y`, from `GO`, those with `Y ≫ X`. -/
def typology165 : Setoid (Ranking Con 3) := Setoid.ker fun r ↦ r.Dominates .X .Y

/-- The rows of the violation tableau (166). -/
inductive Row
  | gb
  | go
  deriving DecidableEq, Fintype

/-- In the violation tableau (166), `GB` violates `Y` once and `GO` violates `X` once. -/
def uvt166 : ConstraintSystem Unit Row Con where
  gen _ := Finset.univ
  con c x := match c, x.2 with
    | .X, .go => 1
    | .Y, .gb => 1
    | _, _ => 0

theorem language_uvt166 (r : Ranking Con 3) :
    uvt166.language r () = {if r.Dominates .X .Y then .gb else .go} := by
  revert r
  decide +kernel

/-- The tableau (166) generates the partition (165). -/
theorem typology_uvt166 : uvt166.typology = typology165 := by
  refine Setoid.ext fun r s ↦ ?_
  have key (r : Ranking Con 3) :
      uvt166.language r = fun _ ↦ {if r.Dominates .X .Y then .gb else .go} :=
    funext fun _ ↦ language_uvt166 r
  show uvt166.language r = uvt166.language s ↔ r.Dominates .X .Y = s.Dominates .X .Y
  rw [key, key, eq_iff_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only [h]⟩
  have := congrFun h ()
  by_cases hr : r.Dominates .X .Y <;> by_cases hs : s.Dominates .X .Y <;> simp_all

theorem isTypology_typology165 : IsTypology typology165 :=
  ⟨Unit, Row, uvt166, typology_uvt166⟩

/-- The GMOAT of the typology (165) is acyclic; in particular `<π.bp.X` is an order. -/
theorem isAcyclic_typology165 : IsAcyclic typology165 :=
  isTypology_typology165.isAcyclic

end Examples

end MerchantPrince2022
