module

public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Max
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Kratzer (1989): An Investigation of the Lumps of Thought

This file formalizes [kratzer-1989]'s premise semantics for counterfactuals over situations and
its argument that counterfactual reasoning needs the lumping relation between propositions.
Situations are the elements of a type with a parthood preorder, propositions are sets of
situations, and the worlds are the maximal situations. A proposition lumps another in a world
when it is true there and every part of the world in which it is true is one in which the other
is true too (§2). This is neither logical nor material implication, and a possible-worlds
semantics, whose worlds have no parts, cannot tell it from the latter.

The analysis of §4.2 adds true propositions to the antecedent of a counterfactual while
preserving consistency. Taken at face value it predicts (§4.3) that if Paula weren't buying a
pound of apples, the Atlantic Ocean might be drying up, since the true disjunction that Paula
is buying apples or the Atlantic is drying up can be added consistently to the antecedent and,
with it, yields the consequent. The repair of §4.4 is that a proposition brings along
everything it lumps. In a world where the Atlantic is not drying up, every situation where the
disjunction holds is one where Paula is buying apples, so the disjunction lumps the first
disjunct, which contradicts the antecedent. The spurious *might*-counterfactual is blocked, and
the proposition that the Atlantic is not drying up survives and settles the question. The
formal definitions of §4.6 build this into the crucial set, the family of premise sets over
which *would* and *might* quantify.

## Main definitions

* `Kratzer1989.Lumps`: lumping in a situation.
* `Kratzer1989.Follows`, `Kratzer1989.IsConsistent`, `Kratzer1989.IsCompatible`: logical
  consequence, consistency, and compatibility, which quantify over worlds only.
* `Kratzer1989.Would`, `Kratzer1989.Might`: the counterfactuals over a family of premise sets.
* `Kratzer1989.consistentPremiseSets`: the premise sets of the analysis of §4.2.
* `Kratzer1989.IsCrucial`: membership in the crucial set of §4.6.

## Main results

* `Kratzer1989.Lumps.iff_of_isMin`: at a situation without proper parts lumping is joint truth.
* `Kratzer1989.closedUnderConsequence_iff`: strong closure under logical consequence is closure
  of the whole set.
* `Kratzer1989.might_iff_not_would_compl`: *might* is the dual of *would*.
* `Kratzer1989.might_consistentPremiseSets_atlantic`: the analysis of §4.2 validates (10a).
* `Kratzer1989.not_might_crucialSet_atlantic`: the crucial set blocks it.

## Implementation notes

The set `F` of propositions relevant at a world is a parameter. The paper requires its members
to be true in the world and persistent, among further conditions left open, and says the two
closure conditions must be relativized to it; `ClosedUnderLumping` and `ClosedUnderConsequence`
are stated relative to `F`.

The model has three worlds, the actual one, one where only Paula's purchase differs, and one
where the Atlantic dries, and two parts of the actual world, one supporting only the purchase
and one supporting only the Atlantic's calm. The second is what keeps the calm from lumping the
purchase. The relevant propositions are (9a), (9b), and (9d); the moon disjunction (9e) runs in
parallel.

## TODO

Closure under logical consequence is idle in the Paula example. The paper motivates it with the
King Ludwig example of §5.2, which needs the non-accidental generalizations of §5.

## References

* [A. Kratzer, *An investigation of the lumps of thought* (1989)][kratzer-1989]
* [kratzer-2012], Chapter 5, the revised version of the paper
-/

@[expose] public section

namespace Kratzer1989

open Set

section Situations

variable {S : Type*} [Preorder S] {F A B : Set (Set S)} {p q : Set S} {w : S}
  {𝒜 : Set (Set (Set S))}

/-- `p` lumps `q` in `w` when `p` is true in `w` and `q` is true in every part of `w` in which `p`
is true (§2). -/
structure Lumps (p q : Set S) (w : S) : Prop where
  /-- `p` is true in `w`. -/
  holds : w ∈ p
  /-- `q` is true in every part of `w` in which `p` is true. -/
  localImpl : ∀ ⦃s⦄, s ≤ w → s ∈ p → s ∈ q

/-- At a situation without proper parts lumping is joint truth. In a possible-worlds semantics
every situation is such a world, so lumping cannot be told from material implication between
true propositions, which §2 argues it is not. -/
theorem Lumps.iff_of_isMin {S : Type*} [PartialOrder S] {p q : Set S} {w : S} (hw : IsMin w) :
    Lumps p q w ↔ w ∈ p ∧ w ∈ q :=
  ⟨fun h ↦ ⟨h.holds, h.localImpl le_rfl h.holds⟩,
    fun ⟨hp, hq⟩ ↦ ⟨hp, fun _ hs _ ↦ hw.eq_of_ge hs ▸ hq⟩⟩

variable (S) in
/-- The worlds, the maximal situations. -/
def worlds : Set S := {s | IsMax s}

@[simp] theorem mem_worlds {s : S} : s ∈ worlds S ↔ IsMax s := Iff.rfl

/-- `A` logically implies `q` when `q` is true in every world in which all of `A` is (§3.3). -/
def Follows (A : Set (Set S)) (q : Set S) : Prop := worlds S ∩ ⋂₀ A ⊆ q

/-- `A` is consistent when all of it is true in some world (§3.3). -/
def IsConsistent (A : Set (Set S)) : Prop := (worlds S ∩ ⋂₀ A).Nonempty

/-- `p` is compatible with `A` when adding it to `A` preserves consistency (§3.3). -/
def IsCompatible (p : Set S) (A : Set (Set S)) : Prop := IsConsistent (insert p A)

theorem Follows.mono (h : Follows B q) (hBA : B ⊆ A) : Follows A q :=
  (inter_subset_inter_right _ (sInter_subset_sInter hBA)).trans h

theorem isCompatible_iff_not_follows_compl : IsCompatible p A ↔ ¬ Follows A pᶜ := by
  simp only [IsCompatible, IsConsistent, Follows, sInter_insert, not_subset, Set.Nonempty,
    mem_inter_iff, mem_compl_iff, not_not]
  exact ⟨fun ⟨s, hw, hp, hA⟩ ↦ ⟨s, ⟨hw, hA⟩, hp⟩, fun ⟨s, ⟨hw, hA⟩, hp⟩ ↦ ⟨s, hw, hp, hA⟩⟩

/-! ### Counterfactuals over premise sets

Both analyses of the paper evaluate *if p, would q* and *if p, might q* against a family of
premise sets, and differ only in the family. -/

/-- *Would q* over the premise sets `𝒜`: every premise set has an extension in `𝒜` that
logically implies `q`. -/
def Would (𝒜 : Set (Set (Set S))) (q : Set S) : Prop := ∀ A ∈ 𝒜, ∃ A' ∈ 𝒜, A ⊆ A' ∧ Follows A' q

/-- *Might q* over the premise sets `𝒜`: some premise set has `q` compatible with all of its
extensions in `𝒜`. -/
def Might (𝒜 : Set (Set (Set S))) (q : Set S) : Prop :=
  ∃ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ⊆ A' → IsCompatible q A'

/-- *Might q* is the negation of *would not q* (§4.2). -/
theorem might_iff_not_would_compl : Might 𝒜 q ↔ ¬ Would 𝒜 qᶜ := by
  simp only [Might, Would, isCompatible_iff_not_follows_compl, not_forall, not_exists, not_and,
    exists_prop]

/-- The premise sets of the analysis of §4.2: the ways of adding propositions of `F` to the
antecedent `p` while preserving consistency. -/
def consistentPremiseSets (F : Set (Set S)) (p : Set S) : Set (Set (Set S)) :=
  {A | A ⊆ insert p F ∧ p ∈ A ∧ IsConsistent A}

/-! ### The crucial set (§4.6) -/

/-- `A` is (weakly) closed under lumping in `w` relative to `F`: whatever in `F` a member of `A`
lumps in `w` is in `A`. -/
def ClosedUnderLumping (F A : Set (Set S)) (w : S) : Prop := ∀ p ∈ A, ∀ q ∈ F, Lumps p q w → q ∈ A

/-- `A` is (strongly) closed under logical consequence relative to `F`: whatever in `F` a subset
of `A` logically implies is in `A`. -/
def ClosedUnderConsequence (F A : Set (Set S)) : Prop := ∀ B ⊆ A, ∀ q ∈ F, Follows B q → q ∈ A

/-- Since consequence is monotone in the premises, strong closure under logical consequence is
closure under the consequences of the whole set. -/
theorem closedUnderConsequence_iff : ClosedUnderConsequence F A ↔ ∀ q ∈ F, Follows A q → q ∈ A :=
  ⟨fun h q hq ↦ h A subset_rfl q hq, fun h _ hB q hq hBq ↦ h q hq (hBq.mono hB)⟩

/-- `A` belongs to the crucial set `F_{w,p}`: it is a consistent subset of `F ∪ {p}` containing
`p`, closed under lumping in `w`, whose members other than `p` are closed under logical
consequence. -/
structure IsCrucial (F : Set (Set S)) (w : S) (p : Set S) (A : Set (Set S)) : Prop where
  subset : A ⊆ insert p F
  /-- Condition (i). -/
  consistent : IsConsistent A
  /-- Condition (ii). -/
  antecedent_mem : p ∈ A
  /-- Condition (iii). -/
  closedUnderLumping : ClosedUnderLumping F A w
  /-- Condition (iv). -/
  closedUnderConsequence : ClosedUnderConsequence F (A \ {p})

/-- The crucial set `F_{w,p}`. -/
def crucialSet (F : Set (Set S)) (w : S) (p : Set S) : Set (Set (Set S)) := {A | IsCrucial F w p A}

@[simp] theorem mem_crucialSet : A ∈ crucialSet F w p ↔ IsCrucial F w p A := Iff.rfl

/-- The crucial set refines the premise sets of §4.2 by the two closure conditions. -/
theorem crucialSet_subset_consistentPremiseSets : crucialSet F w p ⊆ consistentPremiseSets F p :=
  fun _ h ↦ ⟨h.subset, h.antecedent_mem, h.consistent⟩

end Situations

/-! ### Paula's apples -/

/-- The situations: three worlds and two parts of the actual world. -/
inductive Sit
  | actual
  | noApples
  | atlantic
  | purchase
  | calm
  deriving DecidableEq, Fintype

/-- Parthood: the two partial situations are parts of the actual world. -/
protected def Sit.le (a b : Sit) : Prop :=
  a = b ∨ ((a = .purchase ∨ a = .calm) ∧ b = .actual)

instance : DecidableRel Sit.le := fun _ _ ↦ by unfold Sit.le; infer_instance

instance : PartialOrder Sit where
  le := Sit.le
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := Sit) (· ≤ ·) := fun a b ↦ inferInstanceAs (Decidable (Sit.le a b))

instance (s : Sit) : Decidable (IsMax s) := inferInstanceAs (Decidable (∀ b, s ≤ b → b ≤ s))

/-- (9a): Paula is buying a pound of apples. -/
def pa : Set Sit := {.purchase, .actual}

/-- The Atlantic Ocean is drying up. -/
def ad : Set Sit := {.atlantic}

/-- (9b): the Atlantic Ocean is not drying up. -/
def notAd : Set Sit := {.calm, .actual, .noApples}

/-- (9d): Paula is buying a pound of apples or the Atlantic Ocean is drying up. -/
def paOrAd : Set Sit := pa ∪ ad

/-- The antecedent of (10a): Paula is not buying a pound of apples. -/
def notPa : Set Sit := {.noApples, .atlantic}

/-- The propositions relevant at the actual world: (9a), (9b), and (9d). -/
def facts : Set (Set Sit) := {pa, notAd, paOrAd}

/-- Decide a claim about the situations and propositions. -/
scoped macro "decide_sit" : tactic =>
  `(tactic| ((try simp only [pa, ad, notAd, paOrAd, notPa, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_sInter, Set.sInter_insert,
      Set.sInter_singleton, mem_worlds, Set.mem_compl_iff]) <;> decide))

/-- The facts are true in the actual world and persistent, as §4.6 requires. -/
theorem actual_mem_and_isUpperSet_of_mem_facts :
    ∀ q ∈ facts, Sit.actual ∈ q ∧ IsUpperSet q := by
  simp only [facts, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, IsUpperSet]
  decide_sit

/-- The disjunction lumps its first disjunct in the actual world (§4.4): the Atlantic is not
drying up in any part of it. -/
theorem lumps_paOrAd_pa : Lumps paOrAd pa Sit.actual := ⟨by decide_sit, by decide_sit⟩

/-- Lumping is not logical implication (§2): the disjunction does not imply its first disjunct. -/
theorem not_follows_paOrAd_pa : ¬ Follows {paOrAd} pa := fun h ↦
  absurd (h ⟨(by decide : IsMax Sit.atlantic), by decide_sit⟩) (by decide_sit)

/-- Nor is it material implication (§2): the calm of the Atlantic and the purchase are both true
in the actual world, but a part of it supports the first without the second. -/
theorem not_lumps_notAd_pa : ¬ Lumps notAd pa Sit.actual := fun h ↦
  (by decide_sit : Sit.calm ∉ pa) (h.localImpl (by decide) (by decide_sit))

theorem not_lumps_notAd_paOrAd : ¬ Lumps notAd paOrAd Sit.actual := fun h ↦
  (by decide_sit : Sit.calm ∉ paOrAd) (h.localImpl (by decide) (by decide_sit))

/-! ### The analysis of §4.2 and its failure (§4.3) -/

/-- (10a) under the analysis of §4.2: adding the disjunction to the antecedent keeps the
premises consistent and makes the Atlantic's drying compatible with every extension. -/
theorem might_consistentPremiseSets_atlantic : Might (consistentPremiseSets facts notPa) ad := by
  refine ⟨{notPa, paOrAd}, ⟨by simp [facts, insert_subset_iff], by simp,
    ⟨.atlantic, by decide_sit⟩⟩, ?_⟩
  rintro A' ⟨_, hp, s, hw, hs⟩ hAA'
  have hpaOrAd : s ∈ paOrAd := hs paOrAd (hAA' (by simp))
  have hnotPa : s ∈ notPa := hs notPa hp
  obtain rfl : s = .atlantic := by
    revert hnotPa hpaOrAd; clear hs hw hp hAA'; revert s; decide_sit
  refine ⟨.atlantic, by decide_sit, fun t ht ↦ ?_⟩
  rcases mem_insert_iff.mp ht with rfl | ht
  · decide_sit
  · exact hs t ht

/-! ### The repair (§4.4) -/

theorem isCrucial_notPa_notAd : IsCrucial facts Sit.actual notPa {notPa, notAd} where
  subset := by simp [facts, insert_subset_iff]
  consistent := ⟨.noApples, by decide_sit⟩
  antecedent_mem := by simp
  closedUnderLumping := by
    rintro q hq r hr hl
    rcases mem_insert_iff.mp hq with rfl | rfl
    · exact absurd hl.holds (by decide_sit)
    · rcases hr with rfl | rfl | rfl
      · exact absurd hl not_lumps_notAd_pa
      · simp
      · exact absurd hl not_lumps_notAd_paOrAd
  closedUnderConsequence := by
    rintro B hB r hr hBr
    have hB' : B ⊆ {notAd} := fun t ht ↦ by
      obtain ⟨rfl | rfl, hne⟩ := hB ht
      · exact absurd rfl hne
      · rfl
    have h := hBr.mono hB'
    rcases hr with rfl | rfl | rfl
    · exact absurd (h ⟨(by decide : IsMax Sit.noApples), by decide_sit⟩) (by decide_sit)
    · refine ⟨by simp, fun h ↦ ?_⟩
      exact absurd (congrArg (Sit.calm ∈ ·) h) (by decide_sit)
    · exact absurd (h ⟨(by decide : IsMax Sit.noApples), by decide_sit⟩) (by decide_sit)

/-- (10a) under lumping: no crucial premise set keeps the Atlantic's drying compatible. The
disjunction cannot be added, since it brings along the purchase, which contradicts the
antecedent; and once the Atlantic's calm is added the consequent is out. -/
theorem not_might_crucialSet_atlantic : ¬ Might (crucialSet facts Sit.actual notPa) ad := by
  rintro ⟨A, hA, hall⟩
  have hpa : pa ∉ A := fun h ↦ by
    obtain ⟨s, hw, hs⟩ := hA.consistent
    have h₁ := hs pa h
    have h₂ := hs notPa hA.antecedent_mem
    revert h₁ h₂; clear hs hw; revert s; decide_sit
  have hpaOrAd : paOrAd ∉ A := fun h ↦
    hpa (hA.closedUnderLumping paOrAd h pa (by simp [facts]) lumps_paOrAd_pa)
  have hsub : A ⊆ {notPa, notAd} := by
    intro t ht
    rcases hA.subset ht with rfl | rfl | rfl | rfl
    · simp
    · exact absurd ht hpa
    · simp
    · exact absurd ht hpaOrAd
  obtain ⟨s, hw, hs⟩ := hall _ isCrucial_notPa_notAd hsub
  have h₁ := hs ad (mem_insert _ _)
  have h₂ := hs notAd (by simp)
  revert h₁ h₂; clear hs hw; revert s; decide_sit

theorem would_crucialSet_compl_ad : Would (crucialSet facts Sit.actual notPa) adᶜ :=
  not_not.mp (might_iff_not_would_compl.not.mp not_might_crucialSet_atlantic)

end Kratzer1989
