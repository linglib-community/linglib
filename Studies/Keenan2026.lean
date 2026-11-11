module

public import Linglib.Core.ModelTheory.Monadic
public import Linglib.Semantics.Quantification.Individual
public import Linglib.Semantics.Quantification.Polyadic
public import Mathlib.ModelTheory.Graph
public import Studies.KeenanStavi1986

/-!
# Keenan (2026): The Logical Structure of English Quantifiers

Keenan's classes of determiner denotations are invariance classes, each the power set of what it
depends on (`Det.invariants`). The intersective and co-intersective ones [generate the conservative
ones](##generateCompleteBoolean_iff_conservative) and are the only ones [reducible to a
quantification over all individuals](##sortallyReducible_iff). Object quantifiers outrun them: [the
Boolean functions of accusative individuals are the accusative
extensions](##generateCompleteBoolean_acc_individual_iff), [a condition that is the two anaphor
conditions together](##aec_iff_aac_and_isPredicateAnaphor). *Different students answered different
questions* is [beyond the Frege boundary on an exact range](##reducible_diffDiff_iff), and (56) has
only infinite models, unlike any monadic sentence (`FirstOrder.Language.exists_finite_realize`).

## Implementation notes

The complete Boolean closure is the inductive `GenerateCompleteBoolean` in place of the stages of
(24). A Boolean function of two variables is `Prop → Prop → Prop`, of which only the
four values on truth values matter. `diffDiff` is the displayed (59), without the condition added
in prose that there be at least two members of the restrictor; that case is the first disjunct of
`reducible_diffDiff_iff`. That theorem sharpens [keenan-1992]'s Example 2, which asks only that both
sets have two members: with more members of the restrictor than subsets of the second set the
function is constantly false, hence reducible, and its proof's relation witnesses only three
pupils. The accusative extension and the two tests for reducibility, stated in that paper, are in
`Quantifier.Polyadic`. Sizes are `Set.ncard`, as in `Quantification/Counting`, so the determiners
counting with them are meant for finite sets.

## TODO

* Theorem 11's undecidability half, and decidability from the finite model property.
* The new conservative determiners of Section 2.6 as denotations, beyond (32).
* (67), and the *else-else* anaphora of (69) and (70), as functions of relations.

## References

* [keenan-2026]
* [keenan-1992]
* [keenan-1993]
* [zuber-keenan-2019]
* [gaifman-1964]
* [hales-1964]
-/

@[expose] public section

namespace Keenan2026

open Quantifier Quantifier.Det Quantifier.Polyadic Function

variable {α : Type*} {d : Det α}

/-! ### Subject quantifiers -/

-- Theorem 3
theorem eq_bot_or_eq_top (h : d.Intersective) (h' : d.CoIntersective) : d = ⊥ ∨ d = ⊤ := by
  have key (A B : Set α) : d A B ↔ d ∅ ∅ :=
    (h A B _ _ (Set.inter_self _).symm).trans (h' _ _ _ _ (by simp))
  by_cases h₀ : d ∅ ∅
  · exact .inr <| funext₂ fun A B ↦ propext <| iff_true_intro ((key A B).2 h₀)
  · exact .inl <| funext₂ fun A B ↦ propext <| iff_false_intro (h₀ ∘ (key A B).1)

/-- Theorem 6: the closure of the intersective and co-intersective functions under complements and
arbitrary joins is exactly the conservative functions, [keenan-1993]'s characterization. -/
theorem generateCompleteBoolean_iff_conservative :
    GenerateCompleteBoolean {d : Det α | d.Intersective ∨ d.CoIntersective} d ↔ d.Conservative := by
  rw [← mem_invariants_inter_sdiff_iff, ← generateCompleteBoolean_union_iff]
  rfl

/-- Def. 17: a determiner denotation is sortally reducible when its value is its value on the
universe at a Boolean function of restrictor and scope, so that it needs no restrictor. -/
def SortallyReducible (d : Det α) : Prop :=
  ∃ h : Prop → Prop → Prop, ∀ A B, d A B ↔ d Set.univ {x | h (x ∈ A) (x ∈ B)}

private theorem table_inter {h : Prop → Prop → Prop} (hft : h False True ↔ h False False)
    (hff : h False False ↔ h True False) {p q p' q' : Prop} (e : p ∧ q ↔ p' ∧ q') :
    h p q ↔ h p' q' := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hp' : p' <;> by_cases hq' : q' <;> simp_all

private theorem table_sdiff {h : Prop → Prop → Prop} (hft : h False True ↔ h False False)
    (hff : h False False ↔ h True True) {p q p' q' : Prop} (e : p ∧ ¬ q ↔ p' ∧ ¬ q') :
    h p q ↔ h p' q' := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hp' : p' <;> by_cases hq' : q' <;> simp_all

/-- Theorem 7: a conservative function is sortally reducible exactly when it is intersective or
co-intersective, so *Most poets daydream* has no paraphrase quantifying over all individuals. -/
theorem sortallyReducible_iff (hd : d.Conservative) :
    SortallyReducible d ↔ d.Intersective ∨ d.CoIntersective := by
  refine ⟨fun ⟨h, hh⟩ ↦ ?_, ?_⟩
  · have hb {A B A' B' : Set α} (e : ∀ x, h (x ∈ A) (x ∈ B) ↔ h (x ∈ A') (x ∈ B')) :
        d A B ↔ d A' B' := by
      rw [hh A B, hh A' B']
      exact iff_of_eq (congrArg _ (Set.ext e))
    have constant (hc : ∀ S T, d Set.univ S ↔ d Set.univ T) :
        d.Intersective ∨ d.CoIntersective :=
      .inl fun A B A' B' _ ↦ (hh A B).trans ((hc _ _).trans (hh A' B').symm)
    by_cases hft : h False True ↔ h False False
    · by_cases htt : h True True ↔ h True False
      · refine constant fun S T ↦ hb fun x ↦ ?_
        by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp only [Set.mem_univ, hS, hT, htt]
      · by_cases hff : h False False ↔ h True False
        · exact .inl fun A B A' B' e ↦ hb fun x ↦ table_inter hft hff (Set.ext_iff.1 e x)
        · have hff' : h False False ↔ h True True := by tauto
          exact .inr fun A B A' B' e ↦ hb fun x ↦ table_sdiff hft hff' (Set.ext_iff.1 e x)
    · have key (S : Set α) : d Set.univ S ↔ d ∅ ∅ := by
        have hS : {x | h (x ∈ (∅ : Set α)) (x ∈ {x | x ∈ S ↔ h False True})} = S :=
          Set.ext fun x ↦ by
            by_cases hx : x ∈ S <;> by_cases hT : h False True <;>
              simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, hx, hT, iff_true,
                iff_false, not_true_eq_false, not_false_eq_true] <;> tauto
        have hd' := hd ∅ {x | x ∈ S ↔ h False True}
        rwa [Set.empty_inter, hh ∅ {x | x ∈ S ↔ h False True}, hS] at hd'
      exact constant fun S T ↦ (key S).trans (key T).symm
  · rintro (h | h)
    · exact ⟨(· ∧ ·), fun A B ↦ h _ _ _ _ (Set.univ_inter _).symm⟩
    · exact ⟨(· → ·), fun A B ↦ h _ _ _ _ (Set.ext fun x ↦ by simp)⟩

-- Theorem 8, Subjects are Boolean
theorem generateCompleteBoolean_individual (Q : Quantifier α) :
    GenerateCompleteBoolean (Set.range individual) Q := by
  refine (generateCompleteBoolean_iff_factorsThrough (B := Quantifier α) (W := Set α)
    (OrderIso.refl _)).2 ?_
  refine fun A B e ↦ congrArg _ (Set.ext fun a ↦ ?_)
  exact iff_of_eq (congrFun e ⟨individual a, a, rfl⟩)

-- *Most* is neither, given two individuals
theorem not_sortallyReducible_most [Nontrivial α] : ¬ SortallyReducible (most : Det α) := fun h ↦ by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hself : (most : Det α) {a} {a} := by simp [most, NumberTree.most, NumberTree.toDet]
  rcases (sortallyReducible_iff conservative_most).1 h with h | h
  · have e : ({a} : Set α) ∩ {a} = {a, b} ∩ {a} := by simp
    have hs := (h _ _ _ _ e).1 hself
    have h₁ : ({a, b} \ {a} : Set α) = {b} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      grind
    simp [most, NumberTree.most, NumberTree.toDet, h₁] at hs
  · have := (h ∅ ∅ {a} {a} (by simp)).2 hself
    simp [most, NumberTree.most, NumberTree.toDet] at this

/-- Def. 16a: *more ... than C*. -/
noncomputable def moreThanC (C : Set α) : Det α := fun A B ↦ (A ∩ C).ncard < (A ∩ B).ncard

/-- Def. 16b as printed: *as many ... as C*. -/
noncomputable def asManyAsC (C : Set α) : Det α := fun A B ↦ (A ∩ B).ncard ≤ (A ∩ C).ncard

theorem conservative_moreThanC (C : Set α) : (moreThanC C).Conservative := fun A B ↦ by
  simp [moreThanC, ← Set.inter_assoc]

theorem not_asManyAsC_iff {C A B : Set α} : ¬ asManyAsC C A B ↔ moreThanC C A B := not_le

-- Against "Proportional Ds are conservative"
theorem exists_proportional_not_conservative [Nonempty α] :
    ∃ d : Det α, d.Proportional ∧ ¬ d.Conservative := by
  refine ⟨fun A B ↦ A = ∅ ∧ B = ∅, fun A B A' B' h h' _ ↦ ?_, fun h ↦ ?_⟩
  · have hA (X Y : Set α) (hXY : 0 < (X \ Y).ncard + (X ∩ Y).ncard) : X ≠ ∅ := by
      rintro rfl
      simp at hXY
    exact iff_of_false (fun e ↦ hA A B h e.1) fun e ↦ hA A' B' h' e.1
  · have := (h ∅ Set.univ).2 ⟨rfl, by simp⟩
    exact Set.univ_nonempty.ne_empty this.2

/-! ### Counting -/

section Counting

variable [Fintype α]

omit [Fintype α] in
private theorem ncard_eq_card {β : Type*} {f : Set α × Set α → β} {P : Det α → Prop}
    (h : ∀ d, P d ↔ d ∈ invariants f) : {d | P d}.ncard = Nat.card (invariants f) := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight h)

private theorem ncard_intersective :
    {d : Det α | d.Intersective}.ncard = 2 ^ 2 ^ Fintype.card α :=
  (ncard_eq_card (f := fun p ↦ p.1 ∩ p.2) (P := Det.Intersective) fun _ ↦ .rfl).trans
    KeenanStavi1986.card_existential

omit [Fintype α] in
/-- Theorem 4(b): the co-intersective functions are the type ⟨1⟩ quantifiers through the complement
of the scope. -/
def coIntersectiveOrderIso : invariants (fun p : Set α × Set α ↦ p.1 \ p.2) ≃o Quantifier α :=
  invariantsOrderIso (s := fun T ↦ (Set.univ, Tᶜ)) fun T ↦ by simp

private theorem ncard_coIntersective :
    {d : Det α | d.CoIntersective}.ncard = 2 ^ 2 ^ Fintype.card α := by
  rw [ncard_eq_card (f := fun p ↦ p.1 \ p.2) (P := Det.CoIntersective) fun _ ↦ .rfl,
    card_invariants fun T ↦ ⟨(Set.univ, Tᶜ), by simp⟩, Nat.card_eq_fintype_card (α := Set α),
    Fintype.card_set]

-- Under Theorem 4: `2 ^ 2 ^ n + 2 ^ 2 ^ n - 2` functions are intersective or co-intersective.
theorem ncard_intersective_or_coIntersective :
    {d : Det α | d.Intersective ∨ d.CoIntersective}.ncard + 2 = 2 * 2 ^ 2 ^ Fintype.card α := by
  have hinter : {d : Det α | d.Intersective} ∩ {d | d.CoIntersective} = {⊥, ⊤} := by
    ext d
    refine ⟨fun ⟨h, h'⟩ ↦ eq_bot_or_eq_top h h', ?_⟩
    rintro (rfl | rfl)
    · exact ⟨fun _ _ _ _ _ ↦ .rfl, fun _ _ _ _ _ ↦ .rfl⟩
    · exact ⟨fun _ _ _ _ _ ↦ .rfl, fun _ _ _ _ _ ↦ .rfl⟩
  have := Set.ncard_union_add_ncard_inter {d : Det α | d.Intersective} {d | d.CoIntersective}
  rw [hinter, Set.ncard_pair bot_ne_top, ncard_intersective, ncard_coIntersective] at this
  rw [two_mul, ← this]
  rfl

example : {d : Det (Fin 2) | d.Intersective ∨ d.CoIntersective}.ncard = 30 := by
  have := ncard_intersective_or_coIntersective (α := Fin 2)
  rw [Fintype.card_fin] at this
  omega

private theorem ncard_intersectionCondition :
    {d : Det α | d.IntersectionCondition}.ncard = 2 ^ 3 ^ Fintype.card α := by
  have h (d : Det α) : d.IntersectionCondition ↔
      d ∈ invariants fun p : Set α × Set α ↦
        (⟨(p.2, p.1 ∩ p.2), Set.inter_subset_right⟩ : Nested α) := by
    refine ⟨fun h A B A' B' e ↦ ?_, fun h A B ↦ h _ _ _ _ (Subtype.ext (by simp))⟩
    have hv := congrArg Subtype.val e
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, hB⟩ := hv
    rw [h A B, h A' B, hB]
  rw [ncard_eq_card h, card_invariants fun p ↦ ⟨(p.1.2, p.1.1),
    Subtype.ext (Prod.ext rfl (Set.inter_eq_left.2 p.2))⟩, KeenanStavi1986.card_nested]

-- Against 1020: the Theorem and Proposition of [zuber-keenan-2019] Section IV
theorem ncard_conservative_or_intersectionCondition :
    {d : Det α | d.Conservative ∨ d.IntersectionCondition}.ncard + 2 ^ 2 ^ Fintype.card α =
      2 * 2 ^ 3 ^ Fintype.card α := by
  have hinter : {d : Det α | d.Conservative} ∩ {d | d.IntersectionCondition} =
      {d | d.Intersective} :=
    Set.ext fun _ ↦ ⟨fun ⟨h, h'⟩ ↦ h.intersectionCondition_iff.1 h',
      fun h ↦ ⟨h.conservative, h.conservative.intersectionCondition_iff.2 h⟩⟩
  have := Set.ncard_union_add_ncard_inter {d : Det α | d.Conservative} {d | d.IntersectionCondition}
  have hc : {d : Det α | d.Conservative}.ncard = 2 ^ 3 ^ Fintype.card α :=
    (ncard_eq_card fun _ ↦ mem_conservativeSubalgebra.symm).trans KeenanStavi1986.card_consDet
  rw [hinter, ncard_intersective, hc, ncard_intersectionCondition] at this
  rw [two_mul, ← this]
  rfl

example : {d : Det (Fin 2) | d.Conservative ∨ d.IntersectionCondition}.ncard = 1008 := by
  have := ncard_conservative_or_intersectionCondition (α := Fin 2)
  rw [Fintype.card_fin] at this
  omega

end Counting

/-! ### Object quantifiers -/

section Object

variable {F : (α → α → Prop) → Set α}

/-- (45), the Accusative Extensions Condition: membership of `a` in `F R` depends only on the row of
`a` in `R`. -/
def AEC (F : (α → α → Prop) → Set α) : Prop := ∀ R S a b, R a = S b → (a ∈ F R ↔ b ∈ F S)

/-- The Accusative Anaphor Condition: membership of `a` in `F R` depends only on `a` and its row. -/
def AAC (F : (α → α → Prop) → Set α) : Prop := ∀ a R S, R a = S a → (a ∈ F R ↔ a ∈ F S)

/-- Def. 20: on a fixed relation, membership of `a` in `F R` depends only on the row of `a`. -/
def IsPredicateAnaphor (F : (α → α → Prop) → Set α) : Prop :=
  ∀ R a b, R a = R b → (a ∈ F R ↔ b ∈ F R)

theorem aec_acc (Q : Quantifier α) : AEC (acc Q) := fun _ _ _ _ e ↦ by simp [acc, e]

theorem aec_iff_exists_acc : AEC F ↔ ∃ Q : Quantifier α, F = acc Q :=
  ⟨fun h ↦ ⟨fun X ↦ ∃ a, a ∈ F fun _ ↦ X, funext fun R ↦ Set.ext fun x ↦
    ⟨fun hx ↦ ⟨x, (h R (fun _ ↦ {y | R x y}) x x rfl).1 hx⟩,
      fun ⟨w, ha⟩ ↦ (h (fun _ ↦ {y | R x y}) R w x rfl).1 ha⟩⟩,
    fun ⟨Q, h⟩ ↦ h ▸ aec_acc Q⟩

/-- The Accusative Extensions Condition is the Accusative Anaphor Condition together with
Def. 20. So a proper accusative anaphor is never a predicate anaphor. -/
theorem aec_iff_aac_and_isPredicateAnaphor : AEC F ↔ AAC F ∧ IsPredicateAnaphor F := by
  classical
  refine ⟨fun h ↦ ⟨fun _ _ _ e ↦ h _ _ _ _ e, fun _ _ _ e ↦ h _ _ _ _ e⟩, ?_⟩
  rintro ⟨h, h'⟩ R S a b e
  have h₁ : update R b (R a) a = R a := by by_cases hab : a = b <;> simp [hab]
  have h₂ : update R b (R a) b = S b := by simp [e]
  rw [h a _ _ h₁.symm, h' (update R b (R a)) a b (by rw [h₁, update_self]), h b _ _ h₂]

/-- The object functions generated from the accusative extensions of the individuals by complements
and arbitrary joins are exactly those satisfying the Accusative Extensions Condition. So (41): the
denotable objects failing that condition, such as *himself*, are not Boolean functions of
individuals. -/
theorem generateCompleteBoolean_acc_individual_iff :
    GenerateCompleteBoolean (Set.range fun b : α ↦ acc (individual b)) F ↔ AEC F := by
  rw [generateCompleteBoolean_iff_factorsThrough (Set.curryOrderIso _ _)]
  refine ⟨fun h R S a b e ↦ iff_of_eq (h (a := (R, a)) (b := (S, b)) (funext ?_)), fun h ↦ ?_⟩
  · rintro ⟨_, c, rfl⟩
    exact congrFun e c
  · refine fun ⟨R, a⟩ ⟨S, b⟩ e ↦ propext (h R S a b (funext fun c ↦ ?_))
    exact congrFun e ⟨_, c, rfl⟩

-- Theorem 10
theorem acc_injective [Nonempty α] : Injective (acc : Quantifier α → _) := fun P Q h ↦
  funext fun A ↦ by
    obtain ⟨a⟩ := ‹Nonempty α›
    simpa [acc, Set.ext_iff] using congrArg (a ∈ ·) (congrFun h fun x y ↦ (x, y) ∈ Set.univ ×ˢ A)

/-- (47): the reflexive. -/
def self (R : α → α → Prop) : Set α := {a | R a a}

theorem aac_self : AAC (self (α := α)) := fun a _ _ e ↦ iff_of_eq (congrFun e a)

-- The Fact under (47)
theorem not_aec_self [Nontrivial α] : ¬ AEC (self (α := α)) := fun h ↦ by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  exact hab ((h (fun x y ↦ y = a) (fun x y ↦ y = a) a b rfl).1 rfl).symm

/-- (51a): *every ... but himself*. -/
def everyButSelf (p : Set α) (R : α → α → Prop) : Set α := {a | p \ {a} ⊆ {y | R a y}}

theorem aac_everyButSelf (p : Set α) : AAC (everyButSelf p) := fun a R S e ↦ by
  simp [everyButSelf, e]

-- (50c) is a proper accusative anaphor
theorem not_aec_everyButSelf {p : Set α} {a b : α} (ha : a ∈ p) (hab : a ≠ b) :
    ¬ AEC (everyButSelf p) := fun h ↦ by
  have := (h (fun _ y ↦ y ∈ p \ {a}) (fun _ y ↦ y ∈ p \ {a}) a b rfl).1 fun _ hy ↦ hy
  exact (this ⟨ha, hab⟩).2 rfl

/-- (53b): *more ... than Ben*, comparing the rows of the same relation. -/
noncomputable def moreThan (b : α) (p : Set α) (R : α → α → Prop) : Set α :=
  {a | ({y | R b y} ∩ p).ncard < ({y | R a y} ∩ p).ncard}

theorem isPredicateAnaphor_moreThan (b : α) (p : Set α) : IsPredicateAnaphor (moreThan b p) :=
  fun R a c e ↦ by simp [moreThan, e]

-- (53b) is not an accusative anaphor
theorem not_aac_moreThan [Finite α] {p : Set α} {a b : α} (hab : a ≠ b) (hp : p.Nonempty) :
    ¬ AAC (moreThan b p) := fun h ↦ by
  have hpos : 0 < p.ncard := (Set.ncard_pos p.toFinite).2 hp
  have := (h a (fun x y ↦ x = a ∧ y ∈ p) (fun _ y ↦ y ∈ p) (by simp)).1 (by
    simpa [moreThan, hab.symm] using hpos)
  simp [moreThan] at this

/-- (55b): *at least as many ... as any other student*, which entails that its subject is a
student. -/
noncomputable def atLeastAsManyAsAnyOther (s p : Set α) (R : α → α → Prop) : Set α :=
  {a | a ∈ s ∧ ∀ b ∈ s, b ≠ a → ({y | R b y} ∩ p).ncard ≤ ({y | R a y} ∩ p).ncard}

theorem not_aac_atLeastAsManyAsAnyOther [Finite α] {s p : Set α} {a c : α} (ha : a ∈ s) (hc : c ∈ s)
    (hac : c ≠ a) (hp : p.Nonempty) : ¬ AAC (atLeastAsManyAsAnyOther s p) := fun h ↦ by
  have := (h a (fun _ _ ↦ False) (fun x y ↦ x = c) (funext fun y ↦ by simp [hac.symm])).1
    ⟨ha, fun b _ _ ↦ by simp⟩
  have hle := this.2 c hc hac
  simp [hac.symm] at hle
  exact hp.ne_empty ((Set.ncard_eq_zero p.toFinite).1 hle)

theorem not_isPredicateAnaphor_atLeastAsManyAsAnyOther {s p : Set α} {a b : α} (ha : a ∈ s)
    (hb : b ∉ s) : ¬ IsPredicateAnaphor (atLeastAsManyAsAnyOther s p) := fun h ↦
  hb ((h (fun _ _ ↦ False) a b rfl).1 ⟨ha, fun _ _ _ ↦ by simp⟩).1

end Object

/-! ### Beyond the Frege boundary -/

section Reducibility

variable {A B : Set α}

/-- (59), *Different students answered different questions*: distinct members of `A` differ in
what they bear the relation to in `B`. -/
def diffDiff (A B : Set α) (R : α → α → Prop) : Prop := A.InjOn fun a ↦ {y | R a y} ∩ B

-- (61), *No two students answered the same questions*, is (59) itself
theorem diffDiff_iff_forall_ne {R : α → α → Prop} :
    diffDiff A B R ↔ ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → {y | R a y} ∩ B ≠ {y | R a' y} ∩ B :=
  ⟨fun h _ ha _ ha' hne e ↦ hne (h ha ha' e), fun h _ ha _ ha' e ↦ by_contra fun hne ↦
    h _ ha _ ha' hne e⟩

-- The Fact under (59)
theorem diffDiff_inter_prod {R : α → α → Prop} :
    diffDiff A B R ↔ diffDiff A B fun x y ↦ R x y ∧ x ∈ A ∧ y ∈ B := by
  have e {a : α} (ha : a ∈ A) : {y | R a y ∧ a ∈ A ∧ y ∈ B} ∩ B = {y | R a y} ∩ B := by
    ext y; simp [ha]
  exact ⟨fun h a ha c hc hac ↦ h ha hc (by simpa [e ha, e hc] using hac),
    fun h a ha c hc hac ↦ h ha hc (by simpa [e ha, e hc] using hac)⟩

/-- Diff-Diff lies beyond the Frege boundary exactly when its restrictor has two members, its
second set two members, and there are enough subsets of the second set to tell the members of the
restrictor apart. Otherwise it is constant, or the restrictor has two members and the second set
one, when it asks whether exactly one of them is related to that member. -/
theorem reducible_diffDiff_iff :
    Reducible (diffDiff A B) ↔ A.Subsingleton ∨ B.Subsingleton ∨ IsEmpty (A ↪ Set B) := by
  classical
  constructor
  · rintro ⟨f, g, hF⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, ha, a', ha', haa⟩, ⟨b, hb, b', hb', hbb⟩, hι⟩ := hcon
    obtain ⟨ι⟩ := hι
    -- rows in `B` that the function cannot tell apart give two relations it must confuse
    have main (r r' : Set B) (hrr : r ≠ r')
        (he : ∀ R x, diffDiff A B (update R x (· ∈ Subtype.val '' r)) ↔
          diffDiff A B (update R x (· ∈ Subtype.val '' r'))) : False := by
      let A₁ : A := ⟨a, ha⟩
      let A₂ : A := ⟨a', ha'⟩
      let ρ : A ↪ Set B := (ι.setValue A₁ r).setValue A₂ r'
      have hne : A₁ ≠ A₂ := fun e ↦ haa (congrArg Subtype.val e)
      have hρ₁ : ρ A₁ = r := by
        rw [show ρ A₁ = _ from Embedding.setValue_eq_of_ne hne (by simpa using hrr)]
        exact Embedding.setValue_eq ..
      have hρ₂ : ρ A₂ = r' := Embedding.setValue_eq ..
      let rows : α → Set α := fun x ↦ if hx : x ∈ A then Subtype.val '' ρ ⟨x, hx⟩ else ∅
      have hrows {x : α} (hx : x ∈ A) : rows x = Subtype.val '' ρ ⟨x, hx⟩ := dite_eq_left hx
      let R : α → α → Prop := fun x y ↦ y ∈ rows x
      have hsub (t : Set B) : Subtype.val '' t ∩ B = Subtype.val '' t :=
        Set.inter_eq_left.2 (Subtype.coe_image_subset _ _)
      have hR : diffDiff A B R := fun x hx z hz e ↦ by
        change rows x ∩ B = rows z ∩ B at e
        rw [hrows hx, hrows hz, hsub, hsub] at e
        exact congrArg Subtype.val (ρ.injective (Set.image_injective.2 Subtype.val_injective e))
      have hself : update R a' (· ∈ Subtype.val '' r') = R := by
        refine funext fun x ↦ ?_
        by_cases hx : x = a'
        · subst hx
          rw [update_self]
          funext y
          exact (congrArg (y ∈ ·) ((hrows ha').trans (by rw [show ρ ⟨x, ha'⟩ = r' from hρ₂]))).symm
        · exact update_of_ne hx _ _
      have hR' := (he R a').2 (by rw [hself]; exact hR)
      refine haa (hR' ha ha' ?_)
      change {y | update R a' (· ∈ Subtype.val '' r) a y} ∩ B =
        {y | update R a' (· ∈ Subtype.val '' r) a' y} ∩ B
      rw [update_of_ne haa, update_self]
      change rows a ∩ B = Subtype.val '' r ∩ B
      rw [hrows ha, show ρ ⟨a, ha⟩ = r from hρ₁]
    have h₁ : (∅ : Set B) ≠ {⟨b, hb⟩} := (Set.singleton_nonempty _).ne_empty.symm
    have h₂ : (∅ : Set B) ≠ {⟨b', hb'⟩} := (Set.singleton_nonempty _).ne_empty.symm
    have h₃ : ({⟨b, hb⟩} : Set B) ≠ {⟨b', hb'⟩} := fun e ↦
      hbb (congrArg Subtype.val (Set.singleton_injective e))
    rcases Reducible.exists_interchangeable ⟨f, g, hF⟩ (· ∈ Subtype.val '' (∅ : Set B))
      (· ∈ Subtype.val '' ({⟨b, hb⟩} : Set B)) (· ∈ Subtype.val '' ({⟨b', hb'⟩} : Set B))
      with e | e | e
    exacts [main _ _ h₁ e, main _ _ h₂ e, main _ _ h₃ e]
  · rintro (h | h | h)
    · exact ⟨fun _ ↦ True, ⊥, fun R ↦ iff_of_true (h.injOn _) trivial⟩
    · refine ⟨fun S ↦ A.InjOn (· ∈ S), Det.some B, fun R ↦ ?_⟩
      have key (x z : α) : {y | R x y} ∩ B = {y | R z y} ∩ B ↔
          (x ∈ acc (Det.some B) R ↔ z ∈ acc (Det.some B) R) := by
        simp only [mem_acc, Det.some, Set.inter_comm B]
        refine ⟨fun e ↦ by rw [e], fun e ↦ Set.ext fun y ↦ and_congr_left fun hy ↦ ?_⟩
        refine ⟨fun hx ↦ ?_, fun hz ↦ ?_⟩
        · obtain ⟨w, hw, hwB⟩ := e.1 ⟨y, hx, hy⟩
          exact h hwB hy ▸ hw
        · obtain ⟨w, hw, hwB⟩ := e.2 ⟨y, hz, hy⟩
          exact h hwB hy ▸ hw
      exact ⟨fun hR x hx z hz e ↦ hR hx hz ((key x z).2 (iff_of_eq e)),
        fun hR x hx z hz e ↦ hR hx hz (propext ((key x z).1 e))⟩
    · refine ⟨fun _ ↦ False, ⊥, fun R ↦ iff_of_false (fun hR ↦ ?_) id⟩
      refine h.false ⟨fun a ↦ Subtype.val ⁻¹' ({y | R a y} ∩ B), fun x z e ↦ ?_⟩
      refine Subtype.ext (hR x.2 z.2 (Set.ext fun y ↦ and_congr_left fun hy ↦ ?_))
      have := Set.ext_iff.1 e ⟨y, hy⟩
      simpa [hy] using this

-- *Every student criticized himself*, by the Reducibility Equivalence, as in [keenan-1992]
theorem not_reducible_every_self (hA : A.Nontrivial) :
    ¬ Reducible fun R ↦ every A (self R) := fun h ↦ by
  obtain ⟨a, ha, b, hb, hab⟩ := hA
  have e := h.eq_of_forall_prod (reducible_iterate (Q₁ := every) (Q₂ := every) (A := A) (B := A))
    fun P Y ↦ ⟨fun h x hx y hy ↦ ⟨(h hx).1, (h hy).2⟩, fun h x hx ↦ h hx hx⟩
  have hid : iterate every every A A (· = ·) := by
    rw [← e]
    exact fun x _ ↦ rfl
  exact hab (hid ha hb)

end Reducibility

/-! ### Two-place predicates force infinite models -/

section Infinite

open FirstOrder FirstOrder.Language BoundedFormula

/-- (56): *Everyone likes someone*, *no two people like the same person*, and *there is someone that
nobody likes*, with *like* the one relation symbol of the language of graphs. -/
def everyoneLikesSomeone : Language.graph.Sentence :=
  (∀' ∃' adj.boundedFormula₂ (&0) (&1)) ⊓
    (∀' ∀' ∀' (adj.boundedFormula₂ (&0) (&2) ⟹ adj.boundedFormula₂ (&1) (&2) ⟹
      Term.bdEqual (&0) (&1))) ⊓
    (∃' ∀' ∼(adj.boundedFormula₂ (&1) (&0)))

variable {M : Type*} [Language.graph.Structure M]

/-- The relation interpreting the relation symbol. -/
def like (a b : M) : Prop := Structure.RelMap adj ![a, b]

theorem realize_everyoneLikesSomeone : M ⊨ everyoneLikesSomeone ↔
    (∀ x : M, ∃ y, like x y) ∧ (∀ x x' y : M, like x y → like x' y → x = x') ∧
      ∃ y : M, ∀ x, ¬ like x y := by
  simp [everyoneLikesSomeone, Sentence.Realize, Formula.Realize, like, Fin.snoc, and_assoc]

-- The proof under (56)
theorem infinite_of_realize (h : M ⊨ everyoneLikesSomeone) : Infinite M := by
  obtain ⟨h₁, h₂, y, hy⟩ := realize_everyoneLikesSomeone.1 h
  choose f hf using h₁
  have hinj : Injective f := fun x x' e ↦ h₂ x x' (f x) (hf x) (e ▸ hf x')
  refine not_finite_iff_infinite.1 fun _ ↦ ?_
  obtain ⟨x, rfl⟩ := Finite.injective_iff_surjective.1 hinj y
  exact hy x (hf x)

/-- The natural numbers with *like* as *is one less than*. -/
@[instance_reducible] def succStructure : Language.graph.Structure ℕ where
  funMap f := isEmptyElim f
  RelMap
    | .adj, xs => xs 1 = xs 0 + 1

-- The model under (56)
theorem realize_succStructure : letI := succStructure; ℕ ⊨ everyoneLikesSomeone := by
  let := succStructure
  refine realize_everyoneLikesSomeone.2 ⟨fun x ↦ ⟨x + 1, rfl⟩, fun x x' y h h' ↦ ?_,
    0, fun x h ↦ ?_⟩
  · change y = x + 1 at h
    change y = x' + 1 at h'
    omega
  · change 0 = x + 1 at h
    omega

end Infinite

end Keenan2026
