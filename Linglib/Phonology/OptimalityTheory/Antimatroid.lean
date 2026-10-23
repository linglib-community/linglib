module

public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
public import Linglib.Core.Combinatorics.Antimatroid
public import Mathlib.Order.Prod.Lex.Basic

/-!
# ERC sets and antimatroids

Merchant and Riggle show that consistent sets of elementary ranking conditions (ERCs) over `n`
constraints and antimatroids on `Fin n` are the same objects. A set of ERCs determines the
family of the top segments of the rankings that satisfy it, which is an antimatroid; an
antimatroid determines one ERC for each of its rooted circuits. The two maps are inverse to
each other, the second up to logical equivalence, and both preserve entailment.

## Main definitions

* `ERC.IsFeasible E S`: `S` is the set of the top `k` constraints of a ranking satisfying `E`.
* `ERC.toAntimatroid E`: the antimatroid of a consistent set of ERCs.
* `ERC.ofAntimatroid A`: the ERCs of the rooted circuits of an antimatroid.

## Main statements

* `ERC.toAntimatroid_ofAntimatroid`: an antimatroid is the antimatroid of its ERCs.
* `ERC.satisfiedBy_ofAntimatroid_toAntimatroid_iff`: the ERCs of the antimatroid of `E` are
  satisfied by exactly the rankings that satisfy `E`.
* `ERC.isFeasible_iff_forall_singleton_of_simple`: for ERCs that each rank one constraint over
  one other, the feasible sets are those feasible for each ERC alone, while
  `ERC.exists_forall_isFeasible_singleton_not_isFeasible` shows this fails in general.

## Implementation notes

* Rankings satisfying a set of ERCs are built by sorting the constraints by a key into a
  lexicographic product (`Ranking.exists_dominates_iff`), and their top segments are read off
  with `Ranking.exists_take_eq`.
* The paper's remark after its definition of the feasible family, and its proof of union
  closure, assume that a set feasible for each ERC alone is feasible for all of them;
  `ERC.exists_forall_isFeasible_singleton_not_isFeasible` refutes this, so union closure is
  proved by merging rankings instead.
* The paper states that the ERCs of the antimatroid of `E` equal `E`, but proves that they are
  satisfied by the same rankings. Equality fails, since a chain's rooted circuits include its
  transitive edges, so the theorem states the equivalence.
* Antimatroids carry a ground set, as mathlib's `Matroid` does; the inverse laws assume it is
  all of `Fin n`, which is the paper's setting.

## References

* [N. Merchant, J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
* [B. L. Dietrich, *A circuit set characterization of antimatroids* (1987)][dietrich-1987]
-/

@[expose] public section

namespace OptimalityTheory

namespace ERC

variable {n : ℕ} {E F : Set (ERC (Fin n))} {S T : Set (Fin n)}

/-! ### The feasible sets of a set of ERCs -/

/-- A set of constraints is feasible for a set of ERCs when it is the set of the top `k`
constraints of a ranking that satisfies all of them. -/
def IsFeasible (E : Set (ERC (Fin n))) (S : Set (Fin n)) : Prop :=
  ∃ r : Ranking (Fin n) n, (∀ α ∈ E, SatisfiedBy r α) ∧ ∃ k, ↑(r.take k) = S

theorem isFeasible_take {r : Ranking (Fin n) n} (hr : ∀ α ∈ E, SatisfiedBy r α)
    (k : Fin (n + 1)) : IsFeasible E ↑(r.take k) :=
  ⟨r, hr, k, rfl⟩

theorem isFeasible_coe_iff (E : Finset (ERC (Fin n))) (S : Finset (Fin n)) :
    IsFeasible (E : Set (ERC (Fin n))) (S : Set (Fin n)) ↔
      ∃ r ∈ linearExtensions E, ∃ k, r.take k = S := by
  simp [IsFeasible]

theorem linearExtensions_nonempty_iff (E : Finset (ERC (Fin n))) :
    (linearExtensions E).Nonempty ↔ ∃ r : Ranking (Fin n) n, ∀ α ∈ (E : Set _), SatisfiedBy r α :=
  by simp [Finset.Nonempty]

theorem IsFeasible.mono (h : ∀ r : Ranking (Fin n) n, (∀ α ∈ E, SatisfiedBy r α) →
    ∀ α ∈ F, SatisfiedBy r α) (hS : IsFeasible E S) : IsFeasible F S := by
  obtain ⟨r, hr, k, hk⟩ := hS
  exact ⟨r, h r hr, k, hk⟩

theorem satisfiedBy_iff_forall_isFeasible_take (r : Ranking (Fin n) n) :
    (∀ α ∈ E, SatisfiedBy r α) ↔ ∀ k, IsFeasible E ↑(r.take k) := by
  refine ⟨fun h k ↦ isFeasible_take h k, fun h α hα ↦ ?_⟩
  rw [satisfiedBy_iff_dominance]
  intro l hl
  obtain ⟨r', hr', k', hk'⟩ := h (r.symm l).succ
  have hlr' : l ∈ r'.take k' := by rw [← Finset.mem_coe, hk']; simp
  obtain ⟨w, hwW, hdom⟩ := (satisfiedBy_iff_dominance r' α).mp (hr' α hα) l hl
  have hw : w ∈ r.take (r.symm l).succ := by
    rw [← Finset.mem_coe, ← hk', Finset.mem_coe]; exact r'.mem_take_of_dominates hdom hlr'
  refine ⟨w, hwW, Fin.lt_def.mpr ?_⟩
  have hwl : w ≠ l := fun h ↦ lt_irrefl _ (h ▸ hdom)
  have hne : (r.symm w : ℕ) ≠ r.symm l := fun h ↦ hwl (r.symm.injective (Fin.ext h))
  simp only [Ranking.mem_take, Fin.val_succ] at hw
  omega

theorem isFeasible_singleton_iff {α : ERC (Fin n)} (hα : ∃ r : Ranking (Fin n) n, SatisfiedBy r α)
    (S : Finset (Fin n)) :
    IsFeasible {α} ↑S ↔ ((∃ l ∈ S, α l = .L) → ∃ w ∈ S, α w = .W) := by
  classical
  constructor
  · rintro ⟨r, hr, k, hk⟩ ⟨l, hlS, hlL⟩
    obtain ⟨w, hwW, hdom⟩ := (satisfiedBy_iff_dominance r α).mp (hr α rfl) l hlL
    rw [Finset.coe_inj] at hk
    exact ⟨w, hk ▸ r.mem_take_of_dominates hdom (hk ▸ hlS), hwW⟩
  · intro hloc
    obtain ⟨r₀, hr₀⟩ := hα
    let key : Fin n → ℕ ×ₗ (ℕ ×ₗ Fin n) := fun i ↦
      toLex (if i ∈ S then 0 else 1, toLex (if α i = .W then 0 else 1, i))
    obtain ⟨r, hr⟩ := Ranking.exists_dominates_iff (n := n) key fun i j h ↦
      congrArg Prod.snd (toLex_inj.mp (congrArg Prod.snd (toLex_inj.mp h)))
    obtain ⟨k, hk⟩ := r.exists_take_eq S fun i hi j hj ↦
      (hr i j).2 (Prod.Lex.lt_iff.2 (Or.inl (by simp [key, hi, hj])))
    refine ⟨r, fun β hβ ↦ ?_, k, by rw [hk]⟩
    · rw [Set.mem_singleton_iff.mp hβ, satisfiedBy_iff_dominance]
      intro l hl
      by_cases hlS : l ∈ S
      · obtain ⟨w, hwS, hwW⟩ := hloc ⟨l, hlS, hl⟩
        refine ⟨w, hwW, (hr w l).2 (Prod.Lex.lt_iff.2 (Or.inr ⟨by simp [key, hwS, hlS], ?_⟩))⟩
        exact Prod.Lex.lt_iff.2 (Or.inl (by simp [key, hwW, hl]))
      · obtain ⟨w, hwW, -⟩ := (satisfiedBy_iff_dominance r₀ α).mp hr₀ l hl
        refine ⟨w, hwW, (hr w l).2 (Prod.Lex.lt_iff.2 ?_)⟩
        by_cases hwS : w ∈ S
        · exact Or.inl (by simp [key, hwS, hlS])
        · exact Or.inr ⟨by simp [key, hwS, hlS],
            Prod.Lex.lt_iff.2 (Or.inl (by simp [key, hwW, hl]))⟩

/-! ### Union closure -/

theorem IsFeasible.union (hS : IsFeasible E S) (hT : IsFeasible E T) :
    IsFeasible E (S ∪ T) := by
  classical
  obtain ⟨r₁, hr₁, k₁, rfl⟩ := hS
  obtain ⟨r₂, hr₂, k₂, rfl⟩ := hT
  set S' := r₁.take k₁
  set T' := r₂.take k₂
  let b : Fin n → ℕ := fun i ↦ if i ∈ S' then 0 else if i ∈ T' then 1 else 2
  let g : Fin n → Ranking (Fin n) n := fun i ↦ if b i = 1 then r₂ else r₁
  have hkey : Function.Injective fun i ↦ toLex (b i, (g i).symm i) := by
    intro i j h
    obtain ⟨hb, hg⟩ := Prod.mk.inj (toLex_inj.mp h)
    rw [show g j = g i by simp only [g, hb]] at hg
    exact (g i).symm.injective hg
  obtain ⟨r, hr⟩ := Ranking.exists_dominates_iff (n := n) _ hkey
  have hlt : ∀ w l, b w ≤ b l → (g l).Dominates w l → r.Dominates w l := by
    intro w l hb hwl
    rw [hr, Prod.Lex.lt_iff]
    rcases hb.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, show (g w).symm w < (g l).symm l by rwa [show g w = g l by simp [g, h]]⟩
  have hblock : ∀ w l, (g l).Dominates w l → b w ≤ b l := by
    intro w l hwl
    by_cases hl : l ∈ S'
    · rw [show g l = r₁ by simp [g, b, hl]] at hwl
      have hw : w ∈ S' := r₁.mem_take_of_dominates hwl hl
      simp [b, hl, hw]
    · by_cases hl' : l ∈ T'
      · by_cases hw : w ∈ S'
        · simp [b, hw, hl, hl']
        · rw [show g l = r₂ by simp [g, b, hl, hl']] at hwl
          have hw' : w ∈ T' := r₂.mem_take_of_dominates hwl hl'
          simp [b, hw, hw', hl, hl']
      · simp only [b, hl, hl', ite_false]
        split_ifs <;> omega
  have hg : ∀ i, ∀ α ∈ E, SatisfiedBy (g i) α := fun i ↦ by
    simp only [g]; split_ifs; exacts [hr₂, hr₁]
  refine ⟨r, fun α hα ↦ ?_, ?_⟩
  · rw [satisfiedBy_iff_dominance]
    intro l hl
    obtain ⟨w, hw, hdom⟩ := (satisfiedBy_iff_dominance _ α).mp (hg l α hα) l hl
    exact ⟨w, hw, hlt w l (hblock w l hdom) hdom⟩
  · refine (r.exists_take_eq (S' ∪ T') fun i hi j hj ↦ ?_).imp fun _ h ↦ by
      rw [h, Finset.coe_union]
    rw [hr, Prod.Lex.lt_iff]
    refine Or.inl (show b i < b j from ?_)
    simp only [Finset.mem_union, not_or] at hi hj
    rcases hi with hi | hi <;> simp [b, hi, hj.1, hj.2]; split_ifs <;> omega

/-! ### The antimatroid of a set of ERCs -/

/-- The antimatroid of a consistent set of ERCs, whose feasible sets are the top segments of the
rankings that satisfy it. -/
def toAntimatroid (E : Set (ERC (Fin n)))
    (hcons : ∃ r : Ranking (Fin n) n, ∀ α ∈ E, SatisfiedBy r α) : Antimatroid (Fin n) where
  E := Set.univ
  IsFeasible := IsFeasible E
  empty_feasible := by
    obtain ⟨r, hr⟩ := hcons
    exact ⟨r, hr, 0, by simp⟩
  feasible_sub _ _ := Set.subset_univ _
  ground_feasible := by
    obtain ⟨r, hr⟩ := hcons
    exact ⟨r, hr, Fin.last n, by simp⟩
  augmentation S hS hne := by
    classical
    obtain ⟨r, hr, k, rfl⟩ := hS
    have hkn : (k : ℕ) < n := by
      by_contra hge
      refine hne ?_
      rw [show k = Fin.last n from Fin.ext (by have := k.isLt; simp; omega), Ranking.take_last,
        Finset.coe_univ]
    refine ⟨r ⟨k, hkn⟩, Set.mem_univ _, by simp, r, hr, (⟨k, hkn⟩ : Fin n).succ, ?_⟩
    rw [Ranking.take_succ, Finset.coe_insert]
    rfl
  removal S hS hne := by
    classical
    obtain ⟨r, hr, k, rfl⟩ := hS
    have hk0 : 0 < (k : ℕ) := by
      obtain ⟨x, hx⟩ := hne
      rw [Finset.mem_coe, Ranking.mem_take] at hx
      omega
    let j : Fin n := ⟨k - 1, by omega⟩
    have hk : k = j.succ := Fin.ext (by simp [j]; omega)
    refine ⟨r j, by simp [hk, Ranking.take_succ], r, hr, j.castSucc, ?_⟩
    rw [hk, Ranking.take_succ, Finset.coe_insert, Set.insert_sdiff_of_mem _ (Set.mem_singleton _),
      Set.sdiff_singleton_eq_self (by simp)]
  union_closed _ _ := IsFeasible.union

@[simp] theorem toAntimatroid_E (hcons : ∃ r : Ranking (Fin n) n, ∀ α ∈ E, SatisfiedBy r α) :
    (toAntimatroid E hcons).E = Set.univ :=
  rfl

@[simp] theorem toAntimatroid_isFeasible
    (hcons : ∃ r : Ranking (Fin n) n, ∀ α ∈ E, SatisfiedBy r α) :
    (toAntimatroid E hcons).IsFeasible S ↔ IsFeasible E S :=
  Iff.rfl

/-! ### The simple fragment

When every ERC ranks a single winner over a single loser, or imposes nothing, the ERCs encode a
partial order, and the feasible sets are its order ideals: the sets feasible for each ERC alone.
In general that intersection is strictly larger. -/

theorem isFeasible_iff_forall_singleton_of_simple
    (hcons : ∃ r : Ranking (Fin n) n, ∀ α ∈ E, SatisfiedBy r α)
    (hsimple : ∀ α ∈ E, α.IsSimple ∨ α.IsTrivial) (S : Finset (Fin n)) :
    IsFeasible E ↑S ↔ ∀ α ∈ E, IsFeasible {α} ↑S := by
  classical
  refine ⟨fun h α hα ↦ h.mono fun r hr β hβ ↦ hr β (Set.mem_singleton_iff.mp hβ ▸ hα),
    fun h ↦ ?_⟩
  obtain ⟨r₀, hr₀⟩ := hcons
  have hloc := fun α hα ↦ (isFeasible_singleton_iff ⟨r₀, hr₀ α hα⟩ S).mp (h α hα)
  let key : Fin n → ℕ ×ₗ Fin n := fun i ↦ toLex (if i ∈ S then 0 else 1, r₀.symm i)
  obtain ⟨r, hr⟩ := Ranking.exists_dominates_iff (n := n) key fun i j h ↦
    r₀.symm.injective (congrArg Prod.snd (toLex_inj.mp h))
  obtain ⟨k, hk⟩ := r.exists_take_eq S fun i hi j hj ↦
    (hr i j).2 (Prod.Lex.lt_iff.2 (Or.inl (by simp [key, hi, hj])))
  refine ⟨r, fun α hα ↦ ?_, k, by rw [hk]⟩
  rw [satisfiedBy_iff_dominance]
  intro l hl
  obtain ⟨⟨wα, -, hwα⟩, -⟩ := (hsimple α hα).resolve_right fun htriv ↦ htriv l hl
  obtain ⟨w, hw, hdom⟩ := (satisfiedBy_iff_dominance r₀ α).mp (hr₀ α hα) l hl
  refine ⟨w, hw, (hr w l).2 (Prod.Lex.lt_iff.2 ?_)⟩
  by_cases hlS : l ∈ S
  · obtain ⟨w', hw'S, hw'⟩ := hloc α hα ⟨l, hlS, hl⟩
    obtain rfl : w = w' := (hwα w hw).trans (hwα w' hw').symm
    exact Or.inr ⟨by simp [key, hw'S, hlS], hdom⟩
  · by_cases hwS : w ∈ S
    · exact Or.inl (by simp [key, hwS, hlS])
    · exact Or.inr ⟨by simp [key, hwS, hlS], hdom⟩

theorem exists_forall_isFeasible_singleton_not_isFeasible :
    ∃ (E : Finset (ERC (Fin 4))) (S : Finset (Fin 4)), (linearExtensions E).Nonempty ∧
      (∀ α ∈ E, IsFeasible {α} (S : Set (Fin 4))) ∧
        ¬ IsFeasible (E : Set (ERC (Fin 4))) (S : Set (Fin 4)) := by
  refine ⟨{fun i ↦ if i = 0 then .W else if i = 1 then .L else if i = 2 then .W else .e,
    fun i ↦ if i = 0 then .L else if i = 1 then .W else if i = 2 then .e else .W}, {0, 1},
    by decide +kernel, fun α hα ↦ ?_, by rw [isFeasible_coe_iff]; decide +kernel⟩
  obtain ⟨r, hr⟩ : (linearExtensions ({fun i ↦ if i = 0 then .W else if i = 1 then .L else
      if i = 2 then .W else .e, fun i ↦ if i = 0 then .L else if i = 1 then .W else if i = 2 then
      .e else .W} : Finset (ERC (Fin 4)))).Nonempty := by decide +kernel
  rw [isFeasible_singleton_iff ⟨r, mem_linearExtensions.mp hr α hα⟩]
  revert α
  decide +kernel

/-! ### The ERCs of an antimatroid -/

open Classical in
/-- The ERC of a rooted circuit has the other members of its carrier as winners, its root as
loser, and the constraints outside the carrier as neutral. -/
noncomputable def ofRootedCircuit {A : Antimatroid (Fin n)} (rc : A.RootedCircuit) :
    ERC (Fin n) :=
  fun k ↦ if k ∈ rc.carrier ∧ k ≠ rc.root then .W else if k = rc.root then .L else .e

/-- The ERCs of an antimatroid, one for each of its rooted circuits. -/
noncomputable def ofAntimatroid (A : Antimatroid (Fin n)) : Set (ERC (Fin n)) :=
  Set.range (ofRootedCircuit (A := A))

variable {A B : Antimatroid (Fin n)}

@[simp] theorem ofRootedCircuit_eq_L_iff (rc : A.RootedCircuit) (k : Fin n) :
    ofRootedCircuit rc k = .L ↔ k = rc.root := by
  unfold ofRootedCircuit; grind

@[simp] theorem ofRootedCircuit_eq_W_iff (rc : A.RootedCircuit) (k : Fin n) :
    ofRootedCircuit rc k = .W ↔ k ∈ rc.carrier ∧ k ≠ rc.root := by
  unfold ofRootedCircuit; grind

theorem ofRootedCircuit_eq_simpleERC (rc : A.RootedCircuit) {w l : Fin n}
    (hcarrier : rc.carrier = {w, l}) (hroot : rc.root = l) (hwl : w ≠ l) :
    ofRootedCircuit rc = simpleERC w l := by
  funext k
  simp only [ofRootedCircuit, simpleERC, hcarrier, hroot, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  by_cases hkw : k = w <;> by_cases hkl : k = l <;> simp_all

/-! ### Dietrich's characterization -/

theorem satisfiedBy_ofAntimatroid_iff (hE : A.E = Set.univ) (r : Ranking (Fin n) n) :
    (∀ α ∈ ofAntimatroid A, SatisfiedBy r α) ↔ ∀ k, A.IsFeasible ↑(r.take k) := by
  classical
  constructor
  · intro hsat k
    induction k using Fin.induction with
    | zero => simpa using A.empty_feasible
    | succ k ih =>
      rw [Ranking.take_succ, Finset.coe_insert]
      set P : Set (Fin n) := ↑(r.take k.castSucc)
      by_contra hnotfeas
      have hxP : r k ∉ P := by simp [P]
      have hcrit : ¬∃ F, A.IsFeasible F ∧ F ∩ (A.E \ P) = {r k} := by
        rintro ⟨F, hF, hFW⟩
        have hFE := A.feasible_sub F hF
        have hFP : F \ P = {r k} := by
          rw [← hFW]
          ext y
          simp only [Set.mem_sdiff, Set.mem_inter_iff]
          exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, hFE h1, h2⟩, fun ⟨h1, _, h3⟩ ↦ ⟨h1, h3⟩⟩
        have hxF : r k ∈ F := (hFP.symm.subset rfl).1
        have hins : insert (r k) P = F ∪ P := by
          ext y
          simp only [Set.mem_insert_iff, Set.mem_union]
          refine ⟨?_, ?_⟩
          · rintro (rfl | h)
            exacts [Or.inl hxF, Or.inr h]
          · rintro (h | h)
            · by_cases hyP : y ∈ P
              · exact Or.inr hyP
              · exact Or.inl (show y ∈ ({r k} : Set (Fin n)) from hFP ▸ ⟨h, hyP⟩)
            · exact Or.inr h
        exact hnotfeas (hins ▸ A.union_closed F P hF ih)
      obtain ⟨rc, hroot, hcarrier⟩ := A.exists_rootedCircuit_of_critical
        (hE ▸ Set.finite_univ) Set.sdiff_subset ⟨hE ▸ Set.mem_univ _, hxP⟩ hcrit
      obtain ⟨w, hwW, hdom⟩ := (satisfiedBy_iff_dominance r _).mp (hsat _ ⟨rc, rfl⟩) rc.root
        ((ofRootedCircuit_eq_L_iff rc rc.root).mpr rfl)
      have hwP : w ∉ P := (hcarrier ((ofRootedCircuit_eq_W_iff rc w).mp hwW).1).2
      refine hwP ?_
      rw [hroot] at hdom
      simpa [P, Ranking.Dominates] using hdom
  · rintro hfeas α ⟨rc, rfl⟩
    rw [satisfiedBy_iff_dominance]
    intro l hl
    obtain rfl := (ofRootedCircuit_eq_L_iff rc l).mp hl
    set P : Set (Fin n) := ↑(r.take (r.symm rc.root).succ)
    have hmem : rc.root ∈ P ∩ rc.carrier := ⟨by simp [P], rc.root_mem⟩
    obtain ⟨w, hwmem, hwne⟩ : ∃ w ∈ P ∩ rc.carrier, w ≠ rc.root := by
      by_contra hall
      push Not at hall
      exact rc.not_free ⟨_, hfeas _,
        Set.Subset.antisymm (Set.singleton_subset_iff.mpr hmem) fun w hw ↦ hall w hw⟩
    refine ⟨w, (ofRootedCircuit_eq_W_iff rc w).mpr ⟨hwmem.2, hwne⟩, Fin.lt_def.mpr ?_⟩
    have hwlt : (r.symm w : ℕ) < r.symm rc.root + 1 := by simpa [P] using hwmem.1
    have hne : (r.symm w : ℕ) ≠ r.symm rc.root := fun h ↦ hwne (r.symm.injective (Fin.ext h))
    omega

/-! ### The inverse laws -/

private theorem exists_feasible_enum_list {S : Set (Fin n)} (hS : A.IsFeasible S) :
    ∃ l : List (Fin n), l.Nodup ∧ {x | x ∈ l} = S ∧ ∀ i, A.IsFeasible {x | x ∈ l.take i} := by
  induction hcard : S.ncard using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    rcases Set.eq_empty_or_nonempty S with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, fun i ↦ by simpa using A.empty_feasible⟩
    · obtain ⟨z, hz, hz_feas⟩ := A.removal S hS hne
      obtain ⟨l', hnd', hset', hfeas'⟩ := ih (S \ {z}).ncard
        (hcard ▸ Set.ncard_sdiff_singleton_lt_of_mem hz (Set.toFinite S)) hz_feas rfl
      have hzl' : z ∉ l' := fun h ↦ (hset'.subset h).2 rfl
      have hfull : {x | x ∈ l' ++ [z]} = S := by
        ext y
        simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_singleton]
        refine ⟨?_, fun hy ↦ ?_⟩
        · rintro (h | rfl)
          exacts [(hset'.subset h).1, hz]
        · rcases eq_or_ne y z with rfl | hyz
          · exact Or.inr rfl
          · exact Or.inl (hset'.superset ⟨hy, hyz⟩)
      refine ⟨l' ++ [z], hnd'.append (List.nodup_singleton z)
        fun a ha hb ↦ (List.mem_singleton.mp hb ▸ hzl') ha, hfull, fun i ↦ ?_⟩
      rcases Nat.lt_or_ge l'.length i with h | h
      · rw [List.take_of_length_le (by simp; omega), hfull]
        exact hS
      · rw [List.take_append, Nat.sub_eq_zero_of_le h]
        simpa using hfeas' i

private theorem exists_feasible_ext_list (hE : A.E = Set.univ) {S : Set (Fin n)}
    (hS : A.IsFeasible S) :
    ∃ l : List (Fin n), l.Nodup ∧ (∀ x ∈ l, x ∉ S) ∧ {x | x ∈ l} = Set.univ \ S ∧
      ∀ i, A.IsFeasible (S ∪ {x | x ∈ l.take i}) := by
  induction hcard : (Set.univ \ S).ncard using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    rcases eq_or_ne S Set.univ with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, by simp, fun i ↦ by simpa using hS⟩
    · obtain ⟨y, _, hyS, hy_feas⟩ := A.augmentation S hS (hE ▸ hne)
      have hlt : (Set.univ \ insert y S).ncard < (Set.univ \ S).ncard :=
        Set.ncard_lt_ncard ⟨Set.sdiff_subset_sdiff_right (Set.subset_insert y S),
          fun h ↦ (h ⟨Set.mem_univ y, hyS⟩).2 (Set.mem_insert y S)⟩ (Set.toFinite _)
      obtain ⟨l', hnd', hout', hset', hfeas'⟩ := ih _ (hcard ▸ hlt) hy_feas rfl
      have hyl' : y ∉ l' := fun h ↦ hout' y h (Set.mem_insert y S)
      refine ⟨y :: l', List.nodup_cons.mpr ⟨hyl', hnd'⟩, ?_, ?_, fun i ↦ ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hyS
        · exact fun hxS ↦ hout' x hx (Set.mem_insert_of_mem y hxS)
      · ext z
        simp only [Set.mem_ofPred_eq, List.mem_cons, Set.mem_sdiff, Set.mem_univ, true_and]
        refine ⟨?_, fun hz ↦ ?_⟩
        · rintro (rfl | hz)
          exacts [hyS, fun hzS ↦ hout' z hz (Set.mem_insert_of_mem y hzS)]
        · rcases eq_or_ne z y with rfl | hzy
          · exact Or.inl rfl
          · refine Or.inr (hset'.superset ⟨Set.mem_univ z, fun hmem ↦ ?_⟩)
            rcases Set.mem_insert_iff.mp hmem with rfl | h
            exacts [hzy rfl, hz h]
      · cases i with
        | zero => simpa using hS
        | succ j =>
          have heq : S ∪ {x | x ∈ (y :: l').take (j + 1)} =
              insert y S ∪ {x | x ∈ l'.take j} := by
            ext z
            simp only [List.take_succ_cons, Set.mem_union, Set.mem_ofPred_eq, List.mem_cons,
              Set.mem_insert_iff]
            tauto
          rw [heq]
          exact hfeas' j

theorem isFeasible_ofAntimatroid_iff (hE : A.E = Set.univ) (S : Set (Fin n)) :
    IsFeasible (ofAntimatroid A) S ↔ A.IsFeasible S := by
  classical
  refine ⟨fun ⟨r, hsat, k, hk⟩ ↦ hk ▸ (satisfiedBy_ofAntimatroid_iff hE r).mp hsat k,
    fun hS ↦ ?_⟩
  obtain ⟨l₀, hnd₀, hset₀, hfeas₀⟩ := exists_feasible_enum_list hS
  obtain ⟨l₁, hnd₁, hout₁, hset₁, hfeas₁⟩ := exists_feasible_ext_list hE hS
  set l := l₀ ++ l₁ with hldef
  have hnd : l.Nodup := hnd₀.append hnd₁ fun a ha hb ↦ hout₁ a hb (hset₀.subset ha)
  have hcover : ∀ x, x ∈ l := by
    intro x
    by_cases hx : x ∈ S
    · exact List.mem_append_left _ (hset₀.superset hx)
    · exact List.mem_append_right _ (hset₁.superset ⟨Set.mem_univ x, hx⟩)
  set e := List.Nodup.getEquivOfForallMemList l hnd hcover
  have hlen : l.length = n := by simpa using Fintype.card_congr e
  have hchain : ∀ (k : ℕ) (hk : k < n + 1),
      ↑(Ranking.take ((finCongr hlen).symm.trans e) ⟨k, hk⟩) = {x | x ∈ l.take k} := by
    intro k hk
    ext x
    simp only [Finset.mem_coe, Ranking.mem_take, Set.mem_ofPred_eq]
    have hsymm : ((((finCongr hlen).symm.trans e).symm x : Fin n) : ℕ) = l.idxOf x := rfl
    rw [hsymm]
    exact (List.mem_take_iff_idxOf_lt (hcover x)).symm
  refine ⟨(finCongr hlen).symm.trans e, ?_, ?_⟩
  · rw [satisfiedBy_ofAntimatroid_iff hE]
    intro k
    rw [show k = (⟨k, k.isLt⟩ : Fin (n + 1)) from rfl, hchain]
    rcases Nat.lt_or_ge l₀.length k with h | h
    · rw [hldef, List.take_append, List.take_of_length_le h.le]
      have hsplit : {x | x ∈ l₀ ++ l₁.take (k - l₀.length)} =
          S ∪ {x | x ∈ l₁.take (k - l₀.length)} := by
        rw [← hset₀]
        ext z
        simp [List.mem_append]
      rw [hsplit]
      exact hfeas₁ _
    · rw [hldef, List.take_append, Nat.sub_eq_zero_of_le h]
      simpa using hfeas₀ k
  · have hlen₀ : S.ncard = l₀.length := by
      rw [← hset₀, show {x | x ∈ l₀} = (↑l₀.toFinset : Set (Fin n)) by simp [List.coe_toFinset],
        Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd₀]
    have hcard : S.ncard ≤ n := by
      have : l₀.length ≤ l.length := by simp [hldef]
      omega
    refine ⟨⟨S.ncard, by omega⟩, ?_⟩
    rw [hchain S.ncard (by omega), hlen₀, hldef, List.take_left]
    exact hset₀

theorem exists_satisfiedBy_ofAntimatroid (hE : A.E = Set.univ) :
    ∃ r : Ranking (Fin n) n, ∀ α ∈ ofAntimatroid A, SatisfiedBy r α := by
  obtain ⟨r, hr, -⟩ := (isFeasible_ofAntimatroid_iff hE _).mpr A.ground_feasible
  exact ⟨r, hr⟩

theorem toAntimatroid_ofAntimatroid (hE : A.E = Set.univ) :
    toAntimatroid (ofAntimatroid A) (exists_satisfiedBy_ofAntimatroid hE) = A :=
  Antimatroid.ext hE.symm (funext fun S ↦ propext (isFeasible_ofAntimatroid_iff hE S))

theorem satisfiedBy_ofAntimatroid_toAntimatroid_iff
    (hcons : ∃ r : Ranking (Fin n) n, ∀ α ∈ E, SatisfiedBy r α) (r : Ranking (Fin n) n) :
    (∀ α ∈ ofAntimatroid (toAntimatroid E hcons), SatisfiedBy r α) ↔ ∀ α ∈ E, SatisfiedBy r α :=
  by rw [satisfiedBy_ofAntimatroid_iff rfl, satisfiedBy_iff_forall_isFeasible_take]; rfl

theorem satisfiedBy_ofAntimatroid_mono (hA : A.E = Set.univ) (hB : B.E = Set.univ)
    (h : ∀ S, A.IsFeasible S → B.IsFeasible S) (r : Ranking (Fin n) n)
    (hr : ∀ α ∈ ofAntimatroid A, SatisfiedBy r α) : ∀ α ∈ ofAntimatroid B, SatisfiedBy r α :=
  (satisfiedBy_ofAntimatroid_iff hB r).mpr fun k ↦
    h _ ((satisfiedBy_ofAntimatroid_iff hA r).mp hr k)

end ERC

end OptimalityTheory
