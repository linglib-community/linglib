module

public import Linglib.Logic.Trivalent.Supervaluation
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Logic.Trivalent.Powerset
public import Linglib.Semantics.Quantification.NumberTree
public import Mathlib.Logic.Function.DependsOn

/-!
# George (2008): a new predictive theory of presupposition projection

George derives projection from the classical meaning of an operator by deploying it on the repairs
of its arguments, which replace presupposition failure by falsehood or by truth. A quantifier
considers the repair by truth only when its argument is true of nothing in a set it depends on,
and deployment fails where an argument is disappointing, its presupposition alone ruling out a
truth still possible. So *each* and *none* [presuppose that the scope is defined throughout the
restrictor](##George2008.deployWithConcern_all_eq_undefined_iff), *exactly n* is [true where n
individuals are](##George2008.deployWithConcern_cardinal_eq_true_iff) and [disappointing where
fewer than n are defined](##George2008.disappointing_cardinal_iff), and conjunction becomes
[asymmetric](##George2008.deployWithConcern₂_and).

## Implementation notes

* The definitions are stated for the nuclear scope of a determiner, the quantifier it makes of a
  classical restrictor, which is its own only repair. A relevant set is one the quantifier
  `DependsOn`, and the repair by truth is available where some relevant set holds no individual of
  which the argument is true, which is the paper's note 10 reading of "the relevant set".

## TODO

* Presuppositional restrictors (§3.1) and *at least one* (§3.2): deployment on a three-valued
  restrictor.

## References

* [george-2008]
* [peters-1979]
-/

@[expose] public section

namespace George2008

open Quantifier Trivalent

variable {E : Type*}

/-! ### Repairs and deployment: Definitions 1–4 -/

/-- A repair of a predicate (§2.2.1), read at a designation standard: at K3 presupposition failure
counts as falsehood, George's `g^{0/#}`, and at LP as truth, his `g^{1/#}`. -/
def repair (d : Designation) (g : E → Trivalent) : Set E := {x | d.threshold ≤ g x}

@[simp] theorem mem_repair_k3 {g : E → Trivalent} {x : E} :
    x ∈ repair .k3 g ↔ g x = .true := by
  simp [repair]

@[simp] theorem mem_repair_lp {g : E → Trivalent} {x : E} :
    x ∈ repair .lp g ↔ g x ≠ .false := by
  simp [repair]

/-- The available repairs of an argument of `Q` (Definition 4): the repair by falsehood, and the
repair by truth where the argument is true of nothing in some set that `Q` depends on, a relevant
set (Definitions 2 and 3). -/
def availableRepairs (Q : Set E → Prop) (g : E → Trivalent) : Set (Set E) :=
  insert (repair .k3 g)
    {X | (∃ Y, DependsOn Q Y ∧ ∀ y ∈ Y, g y ≠ .true) ∧ X = repair .lp g}

/-- The deployment of `Q` on an argument (Definition 1): the value every available repair gives,
and failure where they differ. -/
noncomputable def deploy (Q : Set E → Prop) (g : E → Trivalent) : Trivalent :=
  supervaluationOn (availableRepairs Q g) Q

/-! ### Disappointment: Definitions 5–7 -/

/-- An argument is disappointing (Definition 6) when no argument presupposition-equivalent to it,
failing where it fails (Definition 5), deploys `Q` to truth, though some argument does. -/
def Disappointing (Q : Set E → Prop) (g : E → Trivalent) : Prop :=
  (∀ g' : E → Trivalent, gapExt g' = gapExt g → deploy Q g' ≠ .true) ∧ ∃ d, deploy Q d = .true

open Classical in
/-- Deployment with concern for disappointment (Definition 7): failure where the argument is
disappointing, and deployment otherwise. -/
noncomputable def deployWithConcern (Q : Set E → Prop) (g : E → Trivalent) : Trivalent :=
  if Disappointing Q g then .undefined else deploy Q g

section Deploy

variable {Q : Set E → Prop} {g : E → Trivalent}

theorem repair_k3_mem_availableRepairs : repair .k3 g ∈ availableRepairs Q g :=
  Set.mem_insert _ _

theorem repair_lp_mem_availableRepairs {R : Set E} (hQ : DependsOn Q R)
    (hg : ∀ x ∈ R, g x ≠ .true) : repair .lp g ∈ availableRepairs Q g :=
  Set.mem_insert_of_mem _ ⟨⟨R, hQ, hg⟩, rfl⟩

theorem deploy_eq_true_iff : deploy Q g = .true ↔ ∀ X ∈ availableRepairs Q g, Q X :=
  supervaluationOn_eq_true_iff

theorem apply_repair_k3_of_deploy_eq_true (h : deploy Q g = .true) : Q (repair .k3 g) :=
  deploy_eq_true_iff.1 h _ repair_k3_mem_availableRepairs

theorem dependsOn_iff {R : Set E} :
    DependsOn Q R ↔ ∀ X X' : Set E, (∀ x ∈ R, x ∈ X ↔ x ∈ X') → (Q X ↔ Q X') :=
  ⟨fun hQ _ _ h ↦ Iff.of_eq (hQ fun x hx ↦ propext (h x hx)),
    fun h X X' hX ↦ propext (h X X' fun x hx ↦ Iff.of_eq (hX x hx))⟩

theorem apply_congr_of_dependsOn {R X X' : Set E} (hQ : DependsOn Q R)
    (h : ∀ x ∈ R, x ∈ X ↔ x ∈ X') : Q X ↔ Q X' :=
  dependsOn_iff.1 hQ X X' h

theorem deploy_eq_true_iff_of_defined {R : Set E} (hQ : DependsOn Q R)
    (hg : ∀ x ∈ R, g x ≠ .undefined) : deploy Q g = .true ↔ Q (repair .k3 g) := by
  refine ⟨apply_repair_k3_of_deploy_eq_true, fun h ↦ deploy_eq_true_iff.2 fun X hX ↦ ?_⟩
  rcases hX with rfl | ⟨-, rfl⟩
  · exact h
  · refine (apply_congr_of_dependsOn hQ fun x hx ↦ ?_).1 h
    have := hg x hx
    cases hgx : g x <;> simp_all

theorem deploy_ne_undefined_of_defined {R : Set E} (hQ : DependsOn Q R)
    (hg : ∀ x ∈ R, g x ≠ .undefined) : deploy Q g ≠ .undefined := by
  rw [deploy, ne_eq, supervaluationOn_eq_undefined_iff]
  rintro ⟨⟨X, hX, hQX⟩, ⟨X', hX', hQX'⟩⟩
  have key : ∀ X ∈ availableRepairs Q g, (Q X ↔ Q (repair .k3 g)) := by
    rintro X (rfl | ⟨-, rfl⟩)
    · exact .rfl
    · refine apply_congr_of_dependsOn hQ fun x hx ↦ ?_
      have := hg x hx
      cases hgx : g x <;> simp_all
  exact hQX' ((key X' hX').2 ((key X hX).1 hQX))

theorem availableRepairs_eq_singleton {R : Set E} (hR : ∀ Y, DependsOn Q Y → R ⊆ Y)
    (hg : ∃ x ∈ R, g x = .true) : availableRepairs Q g = {repair .k3 g} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨repair_k3_mem_availableRepairs, ?_⟩
  rintro X (rfl | ⟨⟨Y, hY, hYg⟩, -⟩)
  · rfl
  · obtain ⟨x, hx, hgx⟩ := hg
    exact absurd hgx (hYg x (hR Y hY hx))

end Deploy

/-! ### Relevant sets of determiners -/

section Determiner

variable {q : NumberTree} {R : Set E}

theorem dependsOn_toDet (q : NumberTree) (R : Set E) : DependsOn (q.toDet R) R := by
  refine dependsOn_iff.2 fun B B' h ↦ ?_
  have hd : R \ B = R \ B' := Set.ext fun x ↦ and_congr_right fun hx ↦ not_congr (h x hx)
  have hi : R ∩ B = R ∩ B' := Set.ext fun x ↦ and_congr_right fun hx ↦ h x hx
  simp only [NumberTree.toDet_apply, hd, hi]

-- §2.2.2
theorem subset_of_dependsOn_toDet [Finite E] {a b : ℕ} (hab : a + b + 1 = R.ncard)
    (hq : ¬ (q (a + 1) b ↔ q a (b + 1))) {Y : Set E} (hY : DependsOn (q.toDet R) Y) : R ⊆ Y := by
  intro x hxR
  by_contra hxY
  have hcard : (R \ {x}).ncard = a + b := by
    have := Set.ncard_sdiff_singleton_add_one hxR (Set.toFinite R)
    omega
  obtain ⟨t, htR, ht⟩ := Set.exists_subset_encard_eq (s := R \ {x}) (k := b)
    (by rw [← (Set.toFinite _).cast_ncard_eq, hcard]; exact_mod_cast Nat.le_add_left b a)
  have htn : t.ncard = b := by
    rw [← Nat.cast_inj (R := ℕ∞), (Set.toFinite t).cast_ncard_eq, ht]
  have hxt : x ∉ t := fun h ↦ (htR h).2 rfl
  have htR' : t ⊆ R := htR.trans Set.sdiff_subset
  have hagree : ∀ i ∈ Y, (i ∈ t ↔ i ∈ insert x t) := fun i hi ↦ by
    have : i ≠ x := fun h ↦ hxY (h ▸ hi)
    simp [this]
  have := apply_congr_of_dependsOn hY hagree
  simp only [NumberTree.toDet_apply] at this
  rw [Set.inter_eq_right.2 htR', Set.inter_eq_right.2 (Set.insert_subset hxR htR'),
    Set.ncard_insert_of_notMem hxt, htn] at this
  have h₁ : (R \ t).ncard = a + 1 := by
    have := Set.ncard_sdiff htR'
    omega
  have h₂ : (R \ insert x t).ncard = a := by
    rw [Set.insert_eq, Set.union_comm, ← Set.sdiff_sdiff]
    have := Set.ncard_sdiff_singleton_add_one (a := x) (s := R \ t) ⟨hxR, hxt⟩
    omega
  rw [h₁, h₂] at this
  exact hq this

theorem toDet_all_iff [Finite E] {B : Set E} : NumberTree.all.toDet R B ↔ R ⊆ B := by
  rw [NumberTree.toDet_apply]
  change (R \ B).ncard = 0 ↔ _
  rw [Set.ncard_eq_zero, Set.sdiff_eq_empty]

theorem toDet_no_iff [Finite E] {B : Set E} : NumberTree.no.toDet R B ↔ ∀ x ∈ R, x ∉ B := by
  rw [NumberTree.toDet_apply]
  change (R ∩ B).ncard = 0 ↔ _
  rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x hx hb ↦ h x ⟨hx, hb⟩, fun h x ⟨hx, hb⟩ ↦ h x hx hb⟩

theorem toDet_cardinal_iff {n : ℕ} {B : Set E} :
    (NumberTree.cardinal {n}).toDet R B ↔ (R ∩ B).ncard = n := by
  simp [NumberTree.toDet_apply]

end Determiner

/-! ### Predictions for quantifiers: §3 -/

section Predictions

variable {R : Set E} {g : E → Trivalent}

private theorem sep_true_eq : {x ∈ R | g x = .true} = R ∩ repair .k3 g := by
  ext; simp

private theorem deployWithConcern_eq_true_iff {Q : Set E → Prop} :
    deployWithConcern Q g = .true ↔ ¬ Disappointing Q g ∧ deploy Q g = .true := by
  unfold deployWithConcern
  split_ifs with h <;> simp [h]

private theorem not_disappointing_of_deploy_eq_true {Q : Set E → Prop} (h : deploy Q g = .true) :
    ¬ Disappointing Q g :=
  fun hd ↦ hd.1 g rfl h

open Classical in
/-- The argument that keeps the failures of `g` and is true elsewhere. -/
private noncomputable def trueOffGaps (g : E → Trivalent) : E → Trivalent :=
  fun x ↦ if g x = .undefined then .undefined else .true

open Classical in
/-- The argument that keeps the failures of `g` and is false elsewhere. -/
private noncomputable def falseOffGaps (g : E → Trivalent) : E → Trivalent :=
  fun x ↦ if g x = .undefined then .undefined else .false

private theorem gapExt_trueOffGaps : gapExt (trueOffGaps g) = gapExt g := by
  ext x; by_cases h : g x = .undefined <;> simp [trueOffGaps, h]

private theorem gapExt_falseOffGaps : gapExt (falseOffGaps g) = gapExt g := by
  ext x; by_cases h : g x = .undefined <;> simp [falseOffGaps, h]

variable [Finite E]

-- §3.3
theorem deployWithConcern_all_eq_true_iff :
    deployWithConcern (NumberTree.all.toDet R) g = .true ↔ ∀ x ∈ R, g x = .true := by
  rw [deployWithConcern_eq_true_iff]
  refine ⟨fun ⟨_, h⟩ x hx ↦ ?_, fun h ↦ ?_⟩
  · simpa using toDet_all_iff.1 (apply_repair_k3_of_deploy_eq_true h) hx
  · have hd : deploy (NumberTree.all.toDet R) g = .true :=
      (deploy_eq_true_iff_of_defined (dependsOn_toDet _ R) fun x hx ↦ by simp [h x hx]).2
        (toDet_all_iff.2 fun x hx ↦ by simpa using h x hx)
    exact ⟨not_disappointing_of_deploy_eq_true hd, hd⟩

/-- §3.3: *each* presupposes that the scope is defined of every individual of the restrictor. -/
theorem deployWithConcern_all_eq_undefined_iff :
    deployWithConcern (NumberTree.all.toDet R) g = .undefined ↔ ∃ x ∈ R, g x = .undefined := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hy, hgy⟩ ↦ ?_⟩
  · by_contra hc
    push Not at hc
    have hnd : ¬ Disappointing (NumberTree.all.toDet R) g := fun hd ↦ by
      refine hd.1 (trueOffGaps g) gapExt_trueOffGaps ?_
      refine (deploy_eq_true_iff_of_defined (dependsOn_toDet _ R) fun x hx ↦ ?_).2
        (toDet_all_iff.2 fun x hx ↦ ?_) <;> simp [trueOffGaps, hc x hx]
    simp only [deployWithConcern, hnd, ↓reduceIte] at h
    exact deploy_ne_undefined_of_defined (dependsOn_toDet _ R) hc h
  · have hd : Disappointing (NumberTree.all.toDet R) g := by
      refine ⟨fun g' hg' h ↦ ?_, fun _ ↦ .true, ?_⟩
      · have hy' : g' y = .undefined := by
          have : y ∈ gapExt g' := hg' ▸ (show y ∈ gapExt g from hgy)
          simpa using this
        have := toDet_all_iff.1 (apply_repair_k3_of_deploy_eq_true h) hy
        simp [hy'] at this
      · exact (deploy_eq_true_iff_of_defined (dependsOn_toDet _ R) fun _ _ ↦ by simp).2
          (toDet_all_iff.2 fun _ _ ↦ by simp)
    simp [deployWithConcern, hd]

-- §3.4
theorem deployWithConcern_no_eq_true_iff :
    deployWithConcern (NumberTree.no.toDet R) g = .true ↔ ∀ x ∈ R, g x = .false := by
  rw [deployWithConcern_eq_true_iff]
  refine ⟨fun ⟨hnd, h⟩ x hx ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    by_cases hu : g x = .undefined
    · -- a failure in the restrictor makes the scope disappointing
      refine hnd ⟨fun g' hg' h' ↦ ?_, g, h⟩
      have hx' : g' x = .undefined := by
        have : x ∈ gapExt g' := hg' ▸ (show x ∈ gapExt g from hu)
        simpa using this
      by_cases ht : ∃ z ∈ R, g' z = .true
      · obtain ⟨z, hz, hgz⟩ := ht
        exact toDet_no_iff.1 (apply_repair_k3_of_deploy_eq_true h') z hz (by simpa using hgz)
      · push Not at ht
        have := deploy_eq_true_iff.1 h' _ (repair_lp_mem_availableRepairs (dependsOn_toDet _ R) ht)
        exact toDet_no_iff.1 this x hx (by simp [hx'])
    · have ht : g x = .true := by
        rcases trichotomy (g x) with h' | h' | h' <;> simp_all
      exact toDet_no_iff.1 (apply_repair_k3_of_deploy_eq_true h) x hx (by simpa using ht)
  · have hd : deploy (NumberTree.no.toDet R) g = .true :=
      (deploy_eq_true_iff_of_defined (dependsOn_toDet _ R) fun x hx ↦ by simp [h x hx]).2
        (toDet_no_iff.2 fun x hx ↦ by simp [h x hx])
    exact ⟨not_disappointing_of_deploy_eq_true hd, hd⟩

/-- §3.4: *none* presupposes that the scope is defined of every individual of the restrictor. -/
theorem deployWithConcern_no_eq_undefined_iff :
    deployWithConcern (NumberTree.no.toDet R) g = .undefined ↔ ∃ x ∈ R, g x = .undefined := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hy, hgy⟩ ↦ ?_⟩
  · by_contra hc
    push Not at hc
    have hnd : ¬ Disappointing (NumberTree.no.toDet R) g := fun hd ↦ by
      refine hd.1 (falseOffGaps g) gapExt_falseOffGaps ?_
      refine (deploy_eq_true_iff_of_defined (dependsOn_toDet _ R) fun x hx ↦ ?_).2
        (toDet_no_iff.2 fun x hx ↦ ?_) <;> simp [falseOffGaps, hc x hx]
    simp only [deployWithConcern, hnd, ↓reduceIte] at h
    exact deploy_ne_undefined_of_defined (dependsOn_toDet _ R) hc h
  · have hd : Disappointing (NumberTree.no.toDet R) g := by
      refine ⟨fun g' hg' h ↦ ?_, fun _ ↦ .false, ?_⟩
      · have hy' : g' y = .undefined := by
          have : y ∈ gapExt g' := hg' ▸ (show y ∈ gapExt g from hgy)
          simpa using this
        by_cases ht : ∃ z ∈ R, g' z = .true
        · obtain ⟨z, hz, hgz⟩ := ht
          exact toDet_no_iff.1 (apply_repair_k3_of_deploy_eq_true h) z hz (by simpa using hgz)
        · push Not at ht
          have := deploy_eq_true_iff.1 h _
            (repair_lp_mem_availableRepairs (dependsOn_toDet _ R) ht)
          exact toDet_no_iff.1 this y hy (by simp [hy'])
      · exact (deploy_eq_true_iff_of_defined (dependsOn_toDet _ R) fun _ _ ↦ by simp).2
          (toDet_no_iff.2 fun _ _ ↦ by simp)
    simp [deployWithConcern, hd]

/-- §3.5: *exactly n* is true where the scope is true of exactly `n` individuals of the
restrictor, whatever it says of the others. -/
theorem deployWithConcern_cardinal_eq_true_iff {n : ℕ} (hn : 1 ≤ n) :
    deployWithConcern ((NumberTree.cardinal {n}).toDet R) g = .true ↔
      {x ∈ R | g x = .true}.ncard = n := by
  rw [deployWithConcern_eq_true_iff]
  refine ⟨fun ⟨_, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [sep_true_eq]
    exact toDet_cardinal_iff.1 (apply_repair_k3_of_deploy_eq_true h)
  · have hpos : ∃ x ∈ R, g x = .true := by
      obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := {x ∈ R | g x = .true}) (by omega)
      exact ⟨x, hx.1, hx.2⟩
    have hle : n ≤ R.ncard := h ▸ Set.ncard_le_ncard (Set.sep_subset R _)
    have hR : ∀ Y, DependsOn ((NumberTree.cardinal {n}).toDet R) Y → R ⊆ Y :=
      fun Y hY ↦ subset_of_dependsOn_toDet (a := R.ncard - n) (b := n - 1) (by omega)
        (by simp; omega) hY
    have hd : deploy ((NumberTree.cardinal {n}).toDet R) g = .true := by
      rw [deploy, availableRepairs_eq_singleton hR hpos, supervaluationOn_eq_true_iff]
      rintro X rfl
      exact toDet_cardinal_iff.2 (by rw [← sep_true_eq]; exact h)
    exact ⟨not_disappointing_of_deploy_eq_true hd, hd⟩

open Classical in
/-- §3.5: the scope of *exactly n* is disappointing exactly where fewer than `n` individuals of the
restrictor satisfy its presupposition, a weaker than universal presupposition. -/
theorem disappointing_cardinal_iff {n : ℕ} (hn : 1 ≤ n) (hnR : n ≤ R.ncard) :
    Disappointing ((NumberTree.cardinal {n}).toDet R) g ↔
      {x ∈ R | g x ≠ .undefined}.ncard < n := by
  have hR : ∀ Y, DependsOn ((NumberTree.cardinal {n}).toDet R) Y → R ⊆ Y :=
    fun Y hY ↦ subset_of_dependsOn_toDet (a := R.ncard - n) (b := n - 1) (by omega)
      (by simp; omega) hY
  -- an argument true of exactly the individuals of a set `T ⊆ R` of size `n`, failing where
  -- `g` fails, deploys the quantifier to truth
  have key : ∀ T ⊆ R, T.ncard = n → ∀ h : E → Trivalent,
      (∀ x ∈ R, h x = .true ↔ x ∈ T) → deploy ((NumberTree.cardinal {n}).toDet R) h = .true := by
    intro T hTR hT h hh
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := T) (by omega)
    rw [deploy, availableRepairs_eq_singleton hR ⟨x, hTR hx, (hh x (hTR hx)).2 hx⟩,
      supervaluationOn_eq_true_iff]
    rintro X rfl
    refine toDet_cardinal_iff.2 ?_
    rw [← hT]
    congr 1
    ext y
    exact ⟨fun ⟨hy, hhy⟩ ↦ (hh y hy).1 (by simpa using hhy),
      fun hy ↦ ⟨hTR hy, by simpa using (hh y (hTR hy)).2 hy⟩⟩
  constructor
  · rintro ⟨hd, -⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨T, hT, hTn⟩ := Set.exists_subset_encard_eq (s := {x ∈ R | g x ≠ .undefined})
      (k := n) (by rw [← (Set.toFinite _).cast_ncard_eq]; exact_mod_cast hlt)
    have hTn' : T.ncard = n := by
      rw [← Nat.cast_inj (R := ℕ∞), (Set.toFinite T).cast_ncard_eq, hTn]
    let g' : E → Trivalent := fun x ↦
      if g x = .undefined then .undefined else if x ∈ T then .true else .false
    have hgap : gapExt g' = gapExt g := by
      ext x; by_cases h : g x = .undefined <;> by_cases hx : x ∈ T <;> simp [g', h, hx]
    refine hd g' hgap (key T (fun x hx ↦ (hT hx).1) hTn' g' fun x hx ↦ ?_)
    by_cases hu : g x = .undefined
    · simp only [g', hu, ↓reduceIte]
      exact ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd hu (hT h).2⟩
    · by_cases hxT : x ∈ T <;> simp [g', hu, hxT]
  · intro hlt
    refine ⟨fun g' hg' h ↦ ?_, ?_⟩
    · have := toDet_cardinal_iff.1 (apply_repair_k3_of_deploy_eq_true h)
      have hsub : R ∩ repair .k3 g' ⊆ {x ∈ R | g x ≠ .undefined} := by
        rintro x ⟨hx, hgx⟩
        refine ⟨hx, fun hu ↦ ?_⟩
        have hx' : x ∈ gapExt g' := by rw [hg']; exact hu
        rw [mem_repair_k3] at hgx
        rw [Trivalent.mem_gapExt, hgx] at hx'
        exact absurd hx' (by decide)
      have := Set.ncard_le_ncard hsub
      omega
    · obtain ⟨T, hT, hTn⟩ := Set.exists_subset_encard_eq (s := R) (k := n)
        (by rw [← (Set.toFinite _).cast_ncard_eq]; exact_mod_cast hnR)
      have hTn' : T.ncard = n := by
        rw [← Nat.cast_inj (R := ℕ∞), (Set.toFinite T).cast_ncard_eq, hTn]
      exact ⟨fun x ↦ if x ∈ T then .true else .false,
        key T hT hTn' _ fun x _ ↦ by by_cases hx : x ∈ T <;> simp [hx]⟩

end Predictions

/-! ### Connectives: §2.1 and §2.3.1 -/

section Connectives

/-- Deployment on two truth values (Definition 1): the value a binary truth function takes at every
pair of their repairs, both `0` and `1` for `#` (`Trivalent.toFinset`), as note 11 has it for
truth values, and failure where the pairs differ. -/
def deploy₂ (f : Bool → Bool → Bool) (a b : Trivalent) : Trivalent :=
  if ∀ x ∈ a.toFinset, ∀ y ∈ b.toFinset, f x y then .true
  else if ∀ x ∈ a.toFinset, ∀ y ∈ b.toFinset, f x y = Bool.false then .false
  else .undefined

/-- A first truth value is disappointing (Definition 6) when no value failing where it fails
deploys the function to truth, whatever follows, though some pair of values does. -/
def DisappointingLeft (f : Bool → Bool → Bool) (a : Trivalent) : Prop :=
  (∀ a', (a' = .undefined ↔ a = .undefined) → ∀ c, deploy₂ f a' c ≠ .true) ∧
    ∃ d₁ d₂, deploy₂ f d₁ d₂ = .true

/-- A second truth value is disappointing after `a` when no value failing where it fails deploys
the function to truth after `a`, though some value does. -/
def DisappointingRight (f : Bool → Bool → Bool) (a b : Trivalent) : Prop :=
  (∀ b', (b' = .undefined ↔ b = .undefined) → deploy₂ f a b' ≠ .true) ∧
    ∃ d, deploy₂ f a d = .true

instance (f : Bool → Bool → Bool) (a : Trivalent) : Decidable (DisappointingLeft f a) := by
  unfold DisappointingLeft; infer_instance

instance (f : Bool → Bool → Bool) (a b : Trivalent) : Decidable (DisappointingRight f a b) := by
  unfold DisappointingRight; infer_instance

/-- Deployment on two truth values with concern for disappointment (Definition 7). -/
def deployWithConcern₂ (f : Bool → Bool → Bool) (a b : Trivalent) : Trivalent :=
  if DisappointingLeft f a ∨ DisappointingRight f a b then .undefined else deploy₂ f a b

-- §2.1
theorem deploy₂_and : deploy₂ (· && ·) = (· ⊓ ·) := by
  funext a b; revert a b; decide

theorem deploy₂_or : deploy₂ (· || ·) = (· ⊔ ·) := by
  funext a b; revert a b; decide

/-- With concern for disappointment conjunction becomes Peters' Middle Kleene conjunction, which
filters a presupposition of its second conjunct and not of its first (§2.3.1). -/
theorem deployWithConcern₂_and : deployWithConcern₂ (· && ·) = meetMiddle := by
  funext a b; revert a b; decide

-- §2.3.1
theorem deployWithConcern₂_or : deployWithConcern₂ (· || ·) = (· ⊔ ·) := by
  funext a b; revert a b; decide

end Connectives

end George2008
