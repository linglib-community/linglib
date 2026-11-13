module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Pragmatics.Bidirectional
public import Mathlib.Basic.Rel
public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Tactic.DeriveFintype

/-!
# Jäger (2002): Some notes on the formal properties of bidirectional optimality theory

Jäger replaces Blutner's mutual recursion of the Q- and the I-principle, z-optimality, by a single
fixed point, x-optimality. That the two are unique and coincide belongs to `BidirectionalOT`;
[without transitivity they come apart](##exists_isWeakSolution_inter_ne_superoptimalSet). For binary
markedness constraints he builds the x-optimal pairs in stages from
[bidirectional conditional intersection](##mem_foldl_biInter_iff), so any class of relations closed
like the rational ones [contains them](##ClosureConditions.superoptimalSet_mem). His worked example
[pairs cheap with cheap and expensive with expensive](##superoptimalSet_beSmall).

## Implementation notes

* A binary markedness constraint is the language it keeps; strings on both sides share one type.
* Lemma 2 is mathlib's `Function.Lex.wellFoundedLT`, an instance on `ViolationProfile`.

## TODO

* The rational relations as an instance of `ClosureConditions`, for Theorem 4 as printed.
* Frank and Satta's Theorem 3, and the motivating examples (1)–(6).

## References

* [jaeger-2002]
* [blutner-2000]
* [frank-satta-1998]
-/

@[expose] public section

namespace Jaeger2002

open BidirectionalOT OptimalityTheory Set
open scoped SetRel

/-! ### Well-foundedness and transitivity -/

-- Lemma 2
example {C : Type*} (ranking : List (Constraint C)) (G : Set C) :
    (ViolationProfile.ofList ranking '' G).IsWF :=
  IsWF.of_wellFoundedLT _

/-- Three meanings, for an order that is well-founded and not transitive. -/
inductive Meaning where
  | first
  | second
  | third
  deriving DecidableEq, Fintype

/-- The position of a meaning in the chain. -/
def Meaning.rank : Meaning → ℕ
  | .first => 0
  | .second => 1
  | .third => 2

/-- Each meaning is more economical than the next one only. -/
instance : LT Meaning := ⟨fun a b ↦ a.rank + 1 = b.rank⟩

instance : DecidableLT Meaning := fun a b ↦ inferInstanceAs (Decidable (a.rank + 1 = b.rank))

/-- The harmony of a pair is its meaning. -/
abbrev Meaning.harmony : Unit × Meaning → Meaning := Prod.snd

instance : WellFoundedLT Meaning :=
  ⟨(Subrelation.wf (r := InvImage (· < ·) Meaning.rank)
    (fun {a b} (h : a.rank + 1 = b.rank) ↦ show a.rank < b.rank by omega)
    (InvImage.wf Meaning.rank wellFounded_lt)).apply⟩

theorem superoptimalSet_meaning :
    superoptimalSet univ Meaning.harmony = {((), .first), ((), .third)} := by
  have : superoptimal Finset.univ Meaning.harmony =
      {((), .first), ((), .third)} := by decide
  simpa using (coe_superoptimal Finset.univ Meaning.harmony).symm.trans
    (congrArg _ this)

theorem isWeakSolution_meaning :
    IsWeakSolution univ Meaning.harmony univ {((), .first)} := by
  refine ⟨Set.eq_univ_of_forall fun p ↦ ⟨trivial, ?_⟩, ?_⟩
  · rintro ⟨q, -, hq, hlt⟩
    have hlt : q.2.rank + 1 = p.2.rank := hlt
    rw [show q.2 = p.2 from hq] at hlt
    exact Nat.succ_ne_self _ hlt
  · ext ⟨⟨⟩, m⟩
    cases m
    · exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨trivial, fun ⟨_, _, _, hlt⟩ ↦ Nat.succ_ne_zero _ hlt⟩⟩
    · exact ⟨fun h ↦ (h.2 ⟨((), .first), trivial, rfl, rfl⟩).elim, fun h ↦ by simp at h⟩
    · exact ⟨fun h ↦ (h.2 ⟨((), .second), trivial, rfl, rfl⟩).elim, fun h ↦ by simp at h⟩

/-- Theorem 2 needs transitivity: for a well-founded order without it, a pair can be x-optimal and
not z-optimal. -/
theorem exists_isWeakSolution_inter_ne_superoptimalSet :
    ¬ IsTrans Meaning (· < ·) ∧ (Meaning.harmony '' univ).IsWF ∧
      ∃ Q I, IsWeakSolution univ Meaning.harmony Q I ∧
        Q ∩ I ≠ superoptimalSet univ Meaning.harmony := by
  refine ⟨fun h ↦ absurd (h.trans .first .second .third rfl rfl) (by decide),
    IsWF.of_wellFoundedLT _, _, _, isWeakSolution_meaning, fun h ↦ ?_⟩
  have : ((), Meaning.third) ∈ univ ∩ ({((), Meaning.first)} : Set (Unit × Meaning)) := by
    rw [h, superoptimalSet_meaning]
    simp
  simp at this

/-! ### The worked example -/

section WorkedExample

variable {T : Type*} (v : T → ℕ)

/-- The worked example's two constraints, each saying "Be small!", ranked input over output. -/
def beSmall : T × T → ViolationProfile 2 := ViolationProfile.ofList [fun p ↦ v p.1, fun p ↦ v p.2]

variable {v}

theorem beSmall_lt_iff {p q : T × T} :
    beSmall v p < beSmall v q ↔ v p.1 < v q.1 ∨ v p.1 = v q.1 ∧ v p.2 < v q.2 :=
  ViolationProfile.ofList_cons_lt_iff.trans <| or_congr .rfl <| and_congr .rfl <|
    ViolationProfile.ofList_cons_lt_iff.trans <|
      or_iff_left fun ⟨_, h⟩ ↦ ViolationProfile.not_ofList_nil_lt h

-- p. 441
theorem beSmall_lt_and_not_lt :
    beSmall (Fin.val : Fin 3 → ℕ) (0, 2) < beSmall (Fin.val : Fin 3 → ℕ) (1, 0) ∧
      ¬ ((0, 2) : Fin 3 × Fin 3) < (1, 0) :=
  ⟨beSmall_lt_iff.2 (.inl (by decide)), fun h ↦ by simp [Prod.lt_iff] at h⟩

theorem strictMono_beSmall [PartialOrder T] (hv : StrictMono v) : StrictMono (beSmall v) := by
  refine ViolationProfile.strictMono_ofList ?_ fun p q h ↦ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨fun _ _ h ↦ hv.monotone h.1, fun _ _ h ↦ hv.monotone h.2⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    exact (Prod.lt_iff.1 h).imp (fun h ↦ hv h.1) fun h ↦ hv h.2

-- p. 442: each stage adds the next pair of equal cost
theorem stage_beSmall (hv : Function.Injective v) (hlow : IsLowerSet (range v)) (n : ℕ) :
    stage univ (beSmall v) n = {p | p.1 = p.2 ∧ v p.1 < n} := by
  induction n with
  | zero =>
    rw [← bot_eq_zero', stage_bot]
    simp
  | succ n ih =>
    have hrem : remaining univ {p : T × T | p.1 = p.2 ∧ v p.1 < n} =
        {p | n ≤ v p.1 ∧ n ≤ v p.2} := by
      ext ⟨a, b⟩
      simp only [remaining, mem_ofPred_eq, mem_univ, true_and, Prod.forall, ne_eq, and_imp]
      grind
    rw [← Order.succ_eq_add_one, stage_succ, ih, stageStep, hrem]
    ext ⟨a, b⟩
    simp only [mem_union, mem_ofPred_eq, minimalFor_iff_forall_lt, beSmall_lt_iff, Prod.forall,
      not_and, not_le, Order.succ_eq_add_one]
    constructor
    · rintro (⟨rfl, ha⟩ | ⟨⟨ha, hb⟩, hmin⟩)
      · exact ⟨rfl, Nat.lt_succ_of_lt ha⟩
      · obtain ⟨s, hs⟩ : n ∈ range v := hlow ha ⟨a, rfl⟩
        have hva : v a = n := by
          by_contra hne
          have := @hmin s s (.inl (by omega))
          omega
        have hvb : v b = n := by
          by_contra hne
          have := @hmin s s (.inr ⟨by omega, by omega⟩)
          omega
        exact ⟨hv (hva.trans hvb.symm), by omega⟩
    · rintro ⟨rfl, ha⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
      · exact .inl ⟨rfl, h⟩
      · refine .inr ⟨⟨h.ge, h.ge⟩, fun {c d} hlt hc ↦ ?_⟩
        omega

/-- The worked example: bidirectional optimality predicts iconicity, pairing cheap inputs with cheap
outputs and expensive with expensive. -/
theorem superoptimalSet_beSmall [LinearOrder T] [WellFoundedLT T] (hv : StrictMono v) :
    superoptimalSet univ (beSmall v) = diagonal T := by
  rw [superoptimalSet_eq_graphOn _ (OrderIso.refl T) (strictMono_beSmall hv)
    (IsWF.of_wellFoundedLT _) (subset_univ _)]
  ext ⟨a, b⟩
  simp [mem_graphOn]

-- pp. 441-442: three stages exhaust `{1, 2, 3} × {1, 2, 3}`
theorem stage_three_beSmall :
    stage univ (beSmall (Fin.val : Fin 3 → ℕ)) 3 =
      superoptimalSet univ (beSmall (Fin.val : Fin 3 → ℕ)) := by
  rw [stage_beSmall Fin.val_injective (by simp [Fin.range_val, isLowerSet_Iio]),
    superoptimalSet_beSmall Fin.val_strictMono]
  ext ⟨a, b⟩
  simp only [mem_ofPred_eq, mem_diagonal_iff, Fin.is_lt, and_true]

-- p. 450: with counting constraints no finite stage suffices
theorem stage_ne_superoptimalSet_beSmall (n : ℕ) :
    stage univ (beSmall (id : ℕ → ℕ)) n ≠ superoptimalSet univ (beSmall (id : ℕ → ℕ)) := by
  rw [superoptimalSet_beSmall strictMono_id,
    stage_beSmall Function.injective_id (by simp [isLowerSet_univ])]
  intro h
  have : (n, n) ∈ diagonal ℕ := rfl
  rw [← h] at this
  exact lt_irrefl _ this.2

end WorkedExample

/-! ### Conditional intersection -/

section Conditional

variable {β γ : Type*}

/-- Definition 10: the conditional intersection of [frank-satta-1998]. -/
def condInter (R : SetRel β γ) (L : Set γ) : SetRel β γ :=
  (R ○ L.graphOn id) ∪ ((R.dom \ (R ○ L.graphOn id).dom).graphOn id ○ R)

/-- The backward conditional intersection, the mirror image of `condInter`. -/
def backInter (R : SetRel β γ) (L : Set β) : SetRel β γ :=
  (L.graphOn id ○ R) ∪ (R ○ (R.cod \ (L.graphOn id ○ R).cod).graphOn id)

-- p. 441
theorem mem_condInter {R : SetRel β γ} {L : Set γ} {x : β} {y : γ} :
    (x, y) ∈ condInter R L ↔ (x, y) ∈ R ∧ (y ∈ L ∨ ∀ z ∈ L, (x, z) ∉ R) := by
  simp only [condInter, mem_union, SetRel.mem_comp, mem_graphOn, mem_sdiff, SetRel.mem_dom, id]
  grind

theorem mem_backInter {R : SetRel β γ} {L : Set β} {x : β} {y : γ} :
    (x, y) ∈ backInter R L ↔ (x, y) ∈ R ∧ (x ∈ L ∨ ∀ z ∈ L, (z, y) ∉ R) := by
  simp only [backInter, mem_union, SetRel.mem_comp, mem_graphOn, mem_sdiff, SetRel.mem_cod, id]
  grind

end Conditional

variable {σ : Type*}

/-- A binary markedness constraint given by the language it keeps, on the input or the output. -/
inductive BinaryMarkedness (σ : Type*) where
  | input (L : Set σ)
  | output (L : Set σ)

/-- The language a binary markedness constraint keeps. -/
def BinaryMarkedness.language : BinaryMarkedness σ → Set σ
  | .input L | .output L => L

open Classical in
/-- A pair violates a binary markedness constraint once when its input or output leaves the
language. -/
noncomputable def BinaryMarkedness.violations : BinaryMarkedness σ → Constraint (σ × σ)
  | .input L => Constraint.binary (·.1 ∉ L)
  | .output L => Constraint.binary (·.2 ∉ L)

theorem BinaryMarkedness.violations_le_one (c : BinaryMarkedness σ) (p : σ × σ) :
    c.violations p ≤ 1 := by
  classical
  cases c <;> simp only [violations] <;> exact Constraint.binary_le_one ..

/-- Definition 12: bidirectional conditional intersection, which keeps the pairs of `R` that are
optimal for the constraint globally, where `condInter` compares only the outputs of each input. -/
def biInter (ε : σ) (R : SetRel σ σ) : BinaryMarkedness σ → SetRel σ σ
  | .input L => (backInter (R.dom ×ˢ {ε}) L).dom.graphOn id ○ R
  | .output L => R ○ (condInter ({ε} ×ˢ R.cod) L).cod.graphOn id

theorem mem_biInter {ε : σ} {R : SetRel σ σ} {c : BinaryMarkedness σ} {p : σ × σ} :
    p ∈ biInter ε R c ↔ MinimalFor (· ∈ R) c.violations p := by
  obtain ⟨x, y⟩ := p
  cases c with
  | input L =>
    simp only [biInter, SetRel.mem_comp, mem_graphOn, SetRel.mem_dom, mem_backInter, mem_prod,
      mem_singleton_iff, id, minimalFor_iff_forall_lt, BinaryMarkedness.violations,
      Constraint.binary_apply]
    grind
  | output L =>
    simp only [biInter, SetRel.mem_comp, mem_graphOn, SetRel.mem_cod, mem_condInter, mem_prod,
      mem_singleton_iff, id, minimalFor_iff_forall_lt, BinaryMarkedness.violations,
      Constraint.binary_apply]
    grind

/-- Lemma 3: successive bidirectional conditional intersection keeps the pairs of `R` that have no
better alternative whatsoever. -/
theorem mem_foldl_biInter_iff {ε : σ} (C : List (BinaryMarkedness σ)) (R : SetRel σ σ) {p : σ × σ} :
    p ∈ C.foldl (biInter ε) R ↔
      MinimalFor (· ∈ R) (ViolationProfile.ofList (C.map BinaryMarkedness.violations)) p := by
  induction C generalizing R with
  | nil => exact ViolationProfile.minimalFor_ofList_nil.symm
  | cons c C ih =>
    rw [List.foldl_cons, ih, List.map_cons, ViolationProfile.minimalFor_ofList_cons,
      show (· ∈ biInter ε R c) = MinimalFor (· ∈ R) c.violations from
        funext fun _ ↦ propext mem_biInter]

/-! ### The number of stages -/

-- Lemma 5, corrected: at most `2^p` harmonies, so at most `2^p` stages
theorem stage_two_pow {F M : Type*} {G : Set (F × M)} {ranking : List (Constraint (F × M))}
    (hbin : ∀ c ∈ ranking, ∀ p ∈ G, c p ≤ 1) :
    stage G (ViolationProfile.ofList ranking) (2 ^ ranking.length : ℕ) =
      superoptimalSet G (ViolationProfile.ofList ranking) := by
  refine stage_eq_superoptimalSet_of_encard_le (encard_le_coe_iff_finite_ncard_le.2 ?_)
  have hsub : ViolationProfile.ofList ranking '' G ⊆
      range fun b : Fin ranking.length → Fin 2 ↦ toLex fun i ↦ (b i : ℕ) := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨fun i ↦ ⟨ranking.get i p, Nat.lt_succ_of_le (hbin _ (List.get_mem ..) p hp)⟩, rfl⟩
  refine ⟨(finite_range _).subset hsub, (ncard_le_ncard hsub (finite_range _)).trans ?_⟩
  rw [← image_univ]
  exact (ncard_image_le finite_univ).trans (by simp)

/-- Two pairs sharing no component. -/
def twoPairs : Finset (Fin 2 × Fin 2) := {(0, 0), (1, 1)}

/-- One binary constraint telling the two pairs of `twoPairs` apart. -/
def oneConstraint : Constraint (Fin 2 × Fin 2) := Constraint.binary (·.2 = 1)

/-- Lemma 5 is false as printed: with one binary constraint it puts every x-optimal pair in the
first stage, which holds only the pair the constraint prefers. -/
theorem stage_two_pow_pred_ne :
    stage (twoPairs : Set _) (ViolationProfile.ofList [oneConstraint])
        (2 ^ ([oneConstraint].length - 1) : ℕ) ≠
      superoptimalSet (twoPairs : Set _) (ViolationProfile.ofList [oneConstraint]) := by
  intro heq
  have hX : ((1, 1) : Fin 2 × Fin 2) ∈
      superoptimalSet (twoPairs : Set _) (ViolationProfile.ofList [oneConstraint]) := by
    rw [← coe_superoptimal]
    exact Finset.mem_coe.2 (by decide)
  rw [← heq, show (2 ^ ([oneConstraint].length - 1) : ℕ) = Order.succ ⊥ from rfl, stage_succ,
    stage_bot] at hX
  obtain h | h := hX
  · exact h
  · exact h.not_prop_of_lt (j := (0, 0)) (by decide) ⟨by decide, fun _ hq ↦ hq.elim⟩

/-! ### Theorem 4 -/

/-- The closure conditions of Figure 4 that the construction uses. -/
structure ClosureConditions (ε : σ) (𝓛 : Set (Set σ)) (𝓡 : Set (SetRel σ σ)) : Prop where
  /-- The language holding only the empty string, a finite language. -/
  singleton_mem : {ε} ∈ 𝓛
  /-- Languages are closed under difference. -/
  diff_mem {L L' : Set σ} : L ∈ 𝓛 → L' ∈ 𝓛 → L \ L' ∈ 𝓛
  /-- Relations are closed under union. -/
  union_mem {R S : SetRel σ σ} : R ∈ 𝓡 → S ∈ 𝓡 → R ∪ S ∈ 𝓡
  /-- Relations are closed under composition. -/
  comp_mem {R S : SetRel σ σ} : R ∈ 𝓡 → S ∈ 𝓡 → R ○ S ∈ 𝓡
  /-- The domain of a relation is a language. -/
  dom_mem {R : SetRel σ σ} : R ∈ 𝓡 → R.dom ∈ 𝓛
  /-- The range of a relation is a language. -/
  cod_mem {R : SetRel σ σ} : R ∈ 𝓡 → R.cod ∈ 𝓛
  /-- The Cartesian product of two languages is a relation. -/
  prod_mem {L L' : Set σ} : L ∈ 𝓛 → L' ∈ 𝓛 → L ×ˢ L' ∈ 𝓡
  /-- The identity on a language is a relation. -/
  graphOn_id_mem {L : Set σ} : L ∈ 𝓛 → L.graphOn id ∈ 𝓡

namespace ClosureConditions

variable {ε : σ} {𝓛 : Set (Set σ)} {𝓡 : Set (SetRel σ σ)} (hc : ClosureConditions ε 𝓛 𝓡)
  {R : SetRel σ σ} {L : Set σ}

include hc

theorem condInter_mem (hR : R ∈ 𝓡) (hL : L ∈ 𝓛) : condInter R L ∈ 𝓡 :=
  have h := hc.comp_mem hR (hc.graphOn_id_mem hL)
  hc.union_mem h (hc.comp_mem (hc.graphOn_id_mem (hc.diff_mem (hc.dom_mem hR) (hc.dom_mem h))) hR)

theorem backInter_mem (hR : R ∈ 𝓡) (hL : L ∈ 𝓛) : backInter R L ∈ 𝓡 :=
  have h := hc.comp_mem (hc.graphOn_id_mem hL) hR
  hc.union_mem h (hc.comp_mem hR (hc.graphOn_id_mem (hc.diff_mem (hc.cod_mem hR) (hc.cod_mem h))))

theorem biInter_mem (hR : R ∈ 𝓡) {c : BinaryMarkedness σ} (hcL : c.language ∈ 𝓛) :
    biInter ε R c ∈ 𝓡 := by
  cases c with
  | input L =>
    exact hc.comp_mem (hc.graphOn_id_mem (hc.dom_mem (hc.backInter_mem
      (hc.prod_mem (hc.dom_mem hR) hc.singleton_mem) hcL))) hR
  | output L =>
    exact hc.comp_mem hR (hc.graphOn_id_mem (hc.cod_mem (hc.condInter_mem
      (hc.prod_mem hc.singleton_mem (hc.cod_mem hR)) hcL)))

theorem foldl_biInter_mem (hR : R ∈ 𝓡) {C : List (BinaryMarkedness σ)}
    (hC : ∀ c ∈ C, c.language ∈ 𝓛) : C.foldl (biInter ε) R ∈ 𝓡 := by
  induction C generalizing R with
  | nil => exact hR
  | cons c C ih =>
    exact ih (hc.biInter_mem hR (hC c List.mem_cons_self))
      fun d hd ↦ hC d (List.mem_cons_of_mem _ hd)

theorem remaining_mem {G X : SetRel σ σ} (hG : G ∈ 𝓡) (hX : X ∈ 𝓡) : remaining G X ∈ 𝓡 := by
  have : remaining G X = (G.dom \ X.dom).graphOn id ○ G ○ (G.cod \ X.cod).graphOn id := by
    ext ⟨x, y⟩
    simp only [remaining, mem_ofPred_eq, SetRel.mem_comp, mem_graphOn, mem_sdiff, SetRel.mem_dom,
      SetRel.mem_cod, id, Prod.forall, ne_eq]
    grind
  rw [this]
  exact hc.comp_mem
    (hc.comp_mem (hc.graphOn_id_mem (hc.diff_mem (hc.dom_mem hG) (hc.dom_mem hX))) hG)
    (hc.graphOn_id_mem (hc.diff_mem (hc.cod_mem hG) (hc.cod_mem hX)))

/-- Theorem 4 in the generality of p. 449: if the generator and the languages of its binary
markedness constraints belong to a class with the closure properties of Figure 4, so does the set
of x-optimal pairs. -/
theorem superoptimalSet_mem {G : SetRel σ σ} (hG : G ∈ 𝓡) {C : List (BinaryMarkedness σ)}
    (hC : ∀ c ∈ C, c.language ∈ 𝓛) :
    superoptimalSet G (ViolationProfile.ofList (C.map BinaryMarkedness.violations)) ∈ 𝓡 := by
  set f := ViolationProfile.ofList (C.map BinaryMarkedness.violations)
  have hstage : ∀ n : ℕ, stage G f n ∈ 𝓡 := fun n ↦ by
    induction n with
    | zero =>
      have hE : (∅ : Set σ) ∈ 𝓛 := by simpa using hc.diff_mem hc.singleton_mem hc.singleton_mem
      rw [← bot_eq_zero', stage_bot]
      simpa using hc.prod_mem hE hE
    | succ n ih =>
      rw [← Order.succ_eq_add_one, stage_succ, stageStep,
        show {p | MinimalFor (· ∈ remaining G (stage G f n)) f p} =
          C.foldl (biInter ε) (remaining G (stage G f n)) from
        Set.ext fun _ ↦ (mem_foldl_biInter_iff C _).symm]
      exact hc.union_mem ih (hc.foldl_biInter_mem (hc.remaining_mem hG ih) hC)
  rw [← stage_two_pow fun c hc' p _ ↦ ?_]
  · exact hstage _
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc'
    exact b.violations_le_one p

end ClosureConditions

end Jaeger2002
