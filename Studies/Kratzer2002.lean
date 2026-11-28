module

public import Studies.Kratzer1989
public import Linglib.Semantics.Mereology.Exemplification
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Relation

/-!
# Kratzer (2002): Facts: particulars or information units?

Situations are parts of worlds and carry the lower set topology, and a proposition is a set of
situations. A fact that exemplifies a proposition `p` is a situation that contains nothing that does
not contribute to the truth of `p`: every part of it is in `p`, or it is a minimal member of `p`.
This is `Mereology.Exemplifies`.

Knowing `p` requires a belief about a fact that exemplifies `p`. In a world where `q` is nowhere
true, the facts that exemplify `q ∪ r` are those that exemplify `r`, so a belief in the disjunction
that is not about such a fact is true and is not knowledge. In a model with three teapots and a pair
of scissors, the proposition that there are three teapots is exemplified by the three teapots alone,
the proposition that there are two by each pair of them, and the proposition that there are teapots
by every situation that contains only teapots. No set of stars exemplifies the proposition that
there are infinitely many.

A proposition `p` lumps `q` in a world `w` if `p` is true in `w` and `q` is true in every part of
`w` in which `p` is, that is, if `p` is included in `q` near `w`. If `w` exemplifies `p`, then `p`
lumps `q` in `w` iff `q` is true in every part of `w`, or `w` is a minimal member of `p` and `q` is
true in `w`.

The facts that counterfactuals are evaluated against are propositions. We define `IsNatural sim p`,
a persistent proposition that does not distinguish maximally similar situations, and
`naturalExtension sim s`, the least natural proposition true in `s`. If `f` is part of `w`, the
natural extension of `f` lumps that of `g` in `w` iff `f` is in the natural extension of `g`, so a
set of natural extensions none of which includes another is closed under lumping. The natural
extension of a fact in a natural proposition `r` is incompatible with the negation of `r`. In the
model of [kratzer-1989], the natural extensions of the two parts of the actual world are the
proposition that Paula is buying apples and the proposition that the Atlantic is not drying up, and
the premise semantics on them, without closure under lumping, makes it true that the Atlantic would
not be drying up if Paula weren't buying apples.

## Implementation notes

The text formalized is chapter 6 of [kratzer-2012], the revised version of the paper, and the
examples are numbered as there. Maximal similarity of situations is a relation `sim` on which
nothing is assumed, and the natural extension of a situation is the set of situations reached
from it by steps of parthood and similarity. The definition of knowledge has two further
conditions, that the belief is de re of the fact and that it is reliable, which are not
formalized.

## TODO

* The conditions of de re belief and of reliability in the definition of knowledge, and the
  proposition that is true in a situation that contains all the stars of its world.
* Base Sets as natural extensions of the members of a partition of the world.

## References

* [kratzer-2002]
* [kratzer-2012]
* [kratzer-1989]
-/

@[expose] public section

namespace Kratzer2002

open Kratzer1989 Situation Mereology Topology Set

/-! ### Facts that exemplify propositions -/

section Facts

variable {S : Type*} [TopologicalSpace S] [PartialOrder S] [Topology.IsLowerSet S]
  {p q r : Set S} {w s : S}

/-- If `q` is true in no part of `w`, then a part of `w` exemplifies `q ∪ r` iff it exemplifies `r`.
-/
theorem exemplifies_union_iff (hq : Disjoint q (Iic w)) (hs : s ≤ w) :
    Exemplifies (q ∪ r) s ↔ Exemplifies r s :=
  iff_of_eq <| (dependsOn_exemplifies_Iic s).congr <| Set.ext fun _ ↦ and_congr_right fun hy ↦
    or_iff_right fun hyq ↦ Set.disjoint_left.1 hq hyq ((mem_Iic.1 hy).trans hs)

-- §6.5: lumping is inclusion near the world
theorem lumps_iff_eventually : Lumps p q w ↔ w ∈ p ∧ ∀ᶠ s in 𝓝 w, s ∈ p → s ∈ q := by
  rw [IsLowerSet.nhds_eq_principal_Iic, Filter.eventually_principal]
  exact ⟨fun h ↦ ⟨h.holds, fun s hs ↦ h.localImpl hs⟩, fun h ↦ ⟨h.1, fun s hs ↦ h.2 s hs⟩⟩

theorem lumps_iff_of_exemplifies (h : Exemplifies p w) :
    Lumps p q w ↔ Iic w ⊆ q ∨ Minimal (· ∈ p) w ∧ w ∈ q := by
  refine ⟨fun hl ↦ ?_, ?_⟩
  · obtain hi | hm := exemplifies_iff.1 h
    · exact .inl fun s hs ↦ hl.localImpl hs (hi hs)
    · exact .inr ⟨hm, hl.localImpl le_rfl hl.holds⟩
  · rintro (hq | ⟨hm, hq⟩)
    · exact ⟨h.mem, fun s hs _ ↦ hq hs⟩
    · exact ⟨h.mem, fun s hs hsp ↦ hm.eq_of_le hsp hs ▸ hq⟩

end Facts

/-! ### Teapots and stars

The situations of the first model are the nonempty sets of four things, three teapots `0`, `1`,
`2` and a pair of scissors `3`, ordered by inclusion. -/

section Models

attribute [local instance high] Topology.lowerSet

/-- The three teapots. -/
def teapots : Finset (Fin 4) := {0, 1, 2}

/-- The proposition that there are at least `n` teapots, (7) and (9). -/
def atLeast (n : ℕ) : Set {s : Finset (Fin 4) // s.Nonempty} := {s | n ≤ (s.1 ∩ teapots).card}

instance (n : ℕ) : DecidablePred (· ∈ atLeast n) :=
  fun s ↦ inferInstanceAs (Decidable (n ≤ (s.1 ∩ teapots).card))

/-- The proposition that there are three teapots is exemplified by the three teapots alone, the
proposition that there are two by the pairs of teapots, and the proposition that there are teapots
by the situations that contain only teapots. -/
theorem exemplifies_atLeast_iff : ∀ x : {s : Finset (Fin 4) // s.Nonempty},
    (Exemplifies (atLeast 3) x ↔ x.1 = teapots) ∧
      (Exemplifies (atLeast 2) x ↔ x.1 ⊆ teapots ∧ x.1.card = 2) ∧
        (Exemplifies (atLeast 1) x ↔ x.1 ⊆ teapots) := by
  decide

-- (12)
theorem not_exemplifies_infinite (x : Set ℕ) : ¬ Exemplifies {s : Set ℕ | s.Infinite} x := by
  rw [exemplifies_iff]
  rintro (h | h)
  · exact h (Set.empty_subset x) Set.finite_empty
  · obtain ⟨a, ha⟩ := h.prop.nonempty
    exact h.not_prop_of_lt (Set.sdiff_singleton_ssubset.2 ha)
      (h.prop.sdiff (Set.finite_singleton a))

end Models

/-! ### Natural propositions and propositional facts -/

section Natural

variable {S : Type*} [Preorder S] (sim : S → S → Prop) {p r a : Set S} {A : Set (Set S)}
  {D : Set S} {w f g : S}

/-- A proposition is natural if it is persistent and does not distinguish maximally similar
situations (§6.6). -/
structure IsNatural (p : Set S) : Prop where
  /-- The proposition is persistent. -/
  isUpperSet : IsUpperSet p
  /-- The proposition is true in the situations maximally similar to one it is true in. -/
  mem_of_sim : ∀ ⦃s t⦄, sim s t → s ∈ p → t ∈ p

/-- The natural extension of `s`: the situations reached from `s` by steps of parthood and of
maximal similarity (§6.6). -/
def naturalExtension (s : S) : Set S :=
  {t | Relation.ReflTransGen (fun a b ↦ a ≤ b ∨ sim a b) s t}

theorem mem_naturalExtension_self (s : S) : s ∈ naturalExtension sim s := .refl

theorem isNatural_naturalExtension (s : S) : IsNatural sim (naturalExtension sim s) :=
  ⟨fun _ _ hab ha ↦ ha.tail (.inl hab), fun _ _ hab ha ↦ ha.tail (.inr hab)⟩

variable {sim}

theorem IsNatural.naturalExtension_subset (hp : IsNatural sim p) {s : S} (hs : s ∈ p) :
    naturalExtension sim s ⊆ p := fun t ht ↦ by
  induction ht with
  | refl => exact hs
  | tail _ hbc ih => exact hbc.elim (fun h ↦ hp.isUpperSet h ih) fun h ↦ hp.mem_of_sim h ih

/-- If `f` is part of `w`, then the natural extension of `f` lumps that of `g` in `w` iff `f` is in
the natural extension of `g`. -/
theorem lumps_naturalExtension_iff (hf : f ≤ w) :
    Lumps (naturalExtension sim f) (naturalExtension sim g) w ↔ f ∈ naturalExtension sim g :=
  ⟨fun h ↦ h.localImpl hf (mem_naturalExtension_self sim f),
    fun h ↦ ⟨.single (.inl hf), fun _ _ hs ↦
      (isNatural_naturalExtension sim g).naturalExtension_subset h hs⟩⟩

-- §6.6
theorem not_isCompatible_compl_naturalExtension (hr : IsNatural sim r) (hf : f ∈ r) :
    ¬ IsCompatible rᶜ {naturalExtension sim f} := fun ⟨_, _, hv⟩ ↦
  hv rᶜ (mem_insert _ _) (hr.naturalExtension_subset hf (hv _ (mem_insert_of_mem _ rfl)))

/-- If no natural extension of a member of `D` includes another and the antecedent `a` is false in
`w`, then every set of them with `a` is closed under lumping in `w`. -/
theorem closedUnderLumping_of_isAntichain (hD : ∀ f ∈ D, f ≤ w)
    (hF : IsAntichain (· ⊆ ·) (naturalExtension sim '' D))
    (hA : A ⊆ insert a (naturalExtension sim '' D)) (ha : w ∉ a) :
    ClosedUnderLumping (naturalExtension sim '' D) A w := by
  rintro p hp _ ⟨g, hg, rfl⟩ hl
  obtain rfl | ⟨f, hf, rfl⟩ := hA hp
  · exact absurd hl.holds ha
  · have hfg := (isNatural_naturalExtension sim g).naturalExtension_subset
      ((lumps_naturalExtension_iff (hD f hf)).1 hl)
    exact hF.eq ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩ hfg ▸ hp

end Natural

-- (31), (33)
theorem not_isCompatible_compl_of_exemplifies_union {S : Type*} [TopologicalSpace S]
    [PartialOrder S] [Topology.IsLowerSet S] {sim : S → S → Prop} {q r : Set S} {w f : S}
    (hr : IsNatural sim r) (hq : Disjoint q (Iic w)) (hf : f ≤ w)
    (he : Exemplifies (q ∪ r) f) : ¬ IsCompatible rᶜ {naturalExtension sim f} :=
  not_isCompatible_compl_naturalExtension hr ((exemplifies_union_iff hq hf).1 he).mem

/-! ### Paula's apples

In the model of [kratzer-1989] the actual world has two parts, Paula's purchase and the calm of
the Atlantic. The calm has a counterpart in the world in which only the purchase differs, which
in the model is that world itself. -/

section Paula

/-- Maximal similarity in the model: the calm of the Atlantic in the actual world is similar to the
world in which only Paula's purchase differs. -/
def sim (a b : Sit) : Prop := a = .calm ∧ b = .noApples

-- the propositional fact of the purchase is (9a) of [kratzer-1989]
theorem naturalExtension_purchase : naturalExtension sim Sit.purchase = pa := by
  refine Subset.antisymm (IsNatural.naturalExtension_subset
    ⟨by unfold IsUpperSet; decide_sit, by rintro s t ⟨rfl, rfl⟩; decide_sit⟩ (by decide_sit)) ?_
  rintro s (rfl | rfl)
  exacts [.refl, .single (.inl (by decide))]

-- the propositional fact of the calm is (9b)
theorem naturalExtension_calm : naturalExtension sim Sit.calm = notAd := by
  refine Subset.antisymm (IsNatural.naturalExtension_subset
    ⟨by unfold IsUpperSet; decide_sit, by rintro s t ⟨rfl, rfl⟩; decide_sit⟩ (by decide_sit)) ?_
  rintro s (rfl | rfl | rfl)
  exacts [.refl, .single (.inl (by decide)), .single (.inr ⟨rfl, rfl⟩)]

/-- With the natural extensions of Paula's purchase and of the calm of the Atlantic as the facts,
the premise semantics without closure under lumping makes it true that the Atlantic would not be
drying up if Paula weren't buying apples. -/
theorem would_consistentPremiseSets_compl_ad :
    Would (consistentPremiseSets (naturalExtension sim '' {Sit.purchase, Sit.calm}) notPa)
      adᶜ := by
  rw [image_pair, naturalExtension_purchase, naturalExtension_calm]
  rintro A ⟨hA, hpA, s, hw, hs⟩
  have hpa : pa ∉ A := fun h ↦ by
    have h₁ := hs pa h
    have h₂ := hs notPa hpA
    revert h₁ h₂; clear hs hw; revert s; decide_sit
  refine ⟨{notPa, notAd}, ⟨by simp [insert_subset_iff], by simp, .noApples, by decide_sit⟩,
    fun t ht ↦ ?_, ?_⟩
  · rcases hA ht with rfl | rfl | rfl
    · simp
    · exact absurd ht hpa
    · simp
  · rintro v ⟨hv, hvs⟩
    have h₁ := hvs notPa (by simp)
    have h₂ := hvs notAd (by simp)
    revert h₁ h₂; clear hvs hv; revert v; decide_sit

end Paula

end Kratzer2002
