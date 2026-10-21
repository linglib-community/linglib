module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Agree: closest goals, horizons, and valuation

This file defines the structural conditions of Agree over syntactic objects and its valuation
step over feature bundles. A closest goal for a probe is a node of the probe's c-command domain
that satisfies the probe's relativization and that no other such node asymmetrically
c-commands, which is the Minimal Link Condition of [chomsky-1995] with mutually c-commanding
candidates equidistant. A target lies behind a horizon for a probe when a leaf of the horizon
category lies in the probe's domain and c-commands the target, so that the probe's search
terminates before reaching it ([keine-2019]). Valuation copies a goal's value into an unvalued
probe slot and is inflationary in the subsumption order on bundles, so Agree only adds
information.

The closest-goal predicate is the tree-native form of the list search `Probe.search`. A probe's
search over an enumeration of its domain sorted by c-command finds one of its closest visible
goals (`isClosestGoalIn_of_search_eq_some`). At the positions of a planar object whose terms each
occur once, it is minimality under the branching positions above a candidate, the closeness of
`PhraseStructure.ancestors`, wherever no candidate dominates another.

## Main definitions

* `Minimalist.SyntacticObject.isClosestGoalIn`: a goal in the probe's domain that no other
  candidate asymmetrically c-commands.
* `Minimalist.SyntacticObject.behindHorizonIn`: a target c-commanded by a horizon-category leaf
  in the probe's domain.
* `Minimalist.FeatureBundle.valueAt`, `Minimalist.FeatureBundle.applyAgree`: valuation of an
  unvalued slot, and the probe's bundle valued from a goal's.

## Main results

* `Minimalist.PlanarSyntacticObject.isClosestGoalIn_termAt_iff`,
  `Minimalist.PlanarSyntacticObject.isClosestGoalIn_termAt_iff_minimalFor`: a closest goal at
  positions, and as minimality under closeness.

## References

* [chomsky-1995], [chomsky-2000]
* [keine-2019]
* [aissen-polian-2025]
-/

@[expose] public section

namespace Minimalist

namespace SyntacticObject

variable {root probe goal : SyntacticObject} {pred : SyntacticObject → Prop}

/-! ### Closest goals -/

/-- A closest `pred`-goal for `probe` in `root` is a node of `probe`'s c-command domain
satisfying `pred` that no other `pred`-node of the domain asymmetrically c-commands. Mutually
c-commanding candidates are equidistant and do not block each other. -/
def isClosestGoalIn (root probe goal : SyntacticObject) (pred : SyntacticObject → Prop) : Prop :=
  goal ∈ cCommandDomain root probe ∧ pred goal ∧
    ∀ x ∈ cCommandDomain root probe, pred x → ¬ AsymmCCommands root x goal

instance [DecidablePred pred] (root probe goal : SyntacticObject) :
    Decidable (isClosestGoalIn root probe goal pred) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ x ∈ cCommandDomain root probe, _))

/-- A probe's search over an enumeration of its domain sorted by c-command finds one of its
closest visible goals. -/
theorem isClosestGoalIn_of_search_eq_some {p : Probe SyntacticObject} {dom : List SyntacticObject}
    (hdom : (dom : Multiset SyntacticObject) = cCommandDomain root probe)
    (hord : dom.Pairwise λ x y => ¬ AsymmCCommands root y x)
    (h : p.search dom = some goal) :
    isClosestGoalIn root probe goal (p.sat ·) := by
  refine ⟨?_, Probe.sat_of_search_eq_some h, λ x hx hvx hasym => ?_⟩
  · rw [← hdom]; exact Multiset.mem_coe.2 (Probe.mem_of_search_eq_some h)
  · rw [← hdom] at hx
    exact Probe.not_rel_of_search_eq_some hord h x (Multiset.mem_coe.1 hx) hvx
      (λ e => hasym.2 (e ▸ hasym.1)) hasym

/-- Sisters are equidistant. A closest goal need only be free of asymmetric c-command by the
`pred`-nodes of the domain that are not its sisters, since a sister never asymmetrically
c-commands it. -/
theorem isClosestGoalIn_iff_forall_not_sister :
    isClosestGoalIn root probe goal pred ↔
      goal ∈ cCommandDomain root probe ∧ pred goal ∧ ∀ x ∈ cCommandDomain root probe, pred x →
        ¬ Sisters root x goal → ¬ AsymmCCommands root x goal :=
  and_congr_right λ _ => and_congr_right λ _ => forall₂_congr λ _ _ => imp_congr_right λ _ =>
    ⟨λ h _ => h, λ h hasym => (em _).elim (λ hs => Sisters.not_asymmCCommands hs hasym)
      (λ hs => h hs hasym)⟩

/-! ### Horizons -/

/-- A target lies behind a horizon of category `c` for `probe` in `root` when a `c` leaf of
`probe`'s c-command domain c-commands it, so that `probe`'s search terminates before reaching it
([keine-2019]). With N a horizon for the wh-probe on C, the D head of `[DP D [PossP Psr N]]`
stays visible while the possessor, c-commanded by N, does not ([aissen-polian-2025]). -/
def behindHorizonIn (root probe target : SyntacticObject) (c : Cat) : Prop :=
  ∃ n ∈ cCommandDomain root probe, isLeafOf c n ∧ CCommands root n target

instance (root probe target : SyntacticObject) (c : Cat) :
    Decidable (behindHorizonIn root probe target c) :=
  Multiset.decidableExistsMultiset

end SyntacticObject

/-! ### Closest goals at positions

When every term of a planar object occurs once, c-command between terms is c-command between
their positions, so a closest goal is the term at a position that the probe's position c-commands
and that no candidate position asymmetrically c-commands. Among candidates none of which dominates
another this is minimality under closeness, the generators above a position
(`PhraseStructure.ancestors`), the key under which a probe finds its goal. -/

namespace PlanarSyntacticObject

open RoseTree PhraseStructure

variable {t : PlanarSyntacticObject} {pred : SyntacticObject → Prop} {a g : t.val.Positions}

/-- When every term occurs once, c-command between the terms at two positions is c-command between
the positions. -/
theorem cCommands_termAt_termAt_iff (hu : Function.Injective t.termAt) {p q : t.val.Positions} :
    t.toSyntacticObject.CCommands (t.termAt p) (t.termAt q) ↔ t.val.CCommands p q := by
  rw [cCommands_termAt_iff fun _ h ↦ hu h]
  exact ⟨fun ⟨_, hq', he⟩ ↦ hu he ▸ hq', fun h ↦ ⟨q, h, rfl⟩⟩

/-- When every term occurs once, a closest goal is the term at a position the probe's position
c-commands that no candidate position asymmetrically c-commands. -/
theorem isClosestGoalIn_termAt_iff (hu : Function.Injective t.termAt) :
    SyntacticObject.isClosestGoalIn t.toSyntacticObject (t.termAt a) (t.termAt g) pred ↔
      t.val.CCommands a g ∧ pred (t.termAt g) ∧ ∀ q : t.val.Positions, t.val.CCommands a q →
        pred (t.termAt q) → ¬ (t.val.CCommands q g ∧ ¬ t.val.CCommands g q) := by
  unfold SyntacticObject.isClosestGoalIn SyntacticObject.AsymmCCommands
  simp only [SyntacticObject.mem_cCommandDomain]
  rw [cCommands_termAt_termAt_iff hu]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h q hq hpq ↦ ?_, fun h x hx hpx ↦ ?_⟩
  · rw [← cCommands_termAt_termAt_iff hu, ← cCommands_termAt_termAt_iff hu]
    exact h _ ((cCommands_termAt_termAt_iff hu).2 hq) hpq
  · obtain ⟨q, hq, rfl⟩ := (cCommands_termAt_iff fun _ h ↦ hu h).1 hx
    rw [cCommands_termAt_termAt_iff hu, cCommands_termAt_termAt_iff hu]
    exact h q hq hpx

/-- When every term occurs once and no candidate position dominates another, a closest goal is the
term at a candidate position minimal under closeness: the Minimal Link Condition is `MinimalFor`
keyed by the branching positions above. -/
theorem isClosestGoalIn_termAt_iff_minimalFor (hu : Function.Injective t.termAt)
    (hS : IsAntichain (· ≤ ·) {q : t.val.Positions | t.val.CCommands a q ∧ pred (t.termAt q)}) :
    SyntacticObject.isClosestGoalIn t.toSyntacticObject (t.termAt a) (t.termAt g) pred ↔
      MinimalFor (fun q : t.val.Positions ↦ t.val.CCommands a q ∧ pred (t.termAt q))
        (fun q ↦ ancestors {p | t.val.IsBranchingAt p} q.val) g := by
  rw [isClosestGoalIn_termAt_iff hu, minimalFor_iff_forall_lt, and_assoc]
  refine and_congr_right fun hg ↦ and_congr_right fun hpg ↦
    ⟨fun h q hlt hq ↦ ?_, fun h q hq hpq hcc ↦ ?_⟩
  · have hne : q ≠ g := by rintro rfl; exact lt_irrefl _ hlt
    exact h q hq.1 hq.2 ((ancestors_ssubset_ancestors_iff_cCommands
      (fun hle ↦ hS hq ⟨hg, hpg⟩ hne (Subtype.coe_le_coe.1 hle))
      (fun hle ↦ hS ⟨hg, hpg⟩ hq hne.symm (Subtype.coe_le_coe.1 hle))).1 hlt)
  · have hne : q ≠ g := by rintro rfl; exact hcc.2 hcc.1
    exact h ((ancestors_ssubset_ancestors_iff_cCommands
      (fun hle ↦ hS ⟨hq, hpq⟩ ⟨hg, hpg⟩ hne (Subtype.coe_le_coe.1 hle))
      (fun hle ↦ hS ⟨hg, hpg⟩ ⟨hq, hpq⟩ hne.symm (Subtype.coe_le_coe.1 hle))).2 hcc) ⟨hq, hpq⟩

end PlanarSyntacticObject

namespace FeatureBundle

variable (probe goal : FeatureBundle) (t : FeatureType)

/-! ### Valuation -/

/-- The bundle `b` with dimension `t` valued by `v` when its slot is unvalued; a valued or absent
slot is left as it is. -/
def valueAt (b : FeatureBundle) (t : FeatureType) (v : t.ValueOf) : FeatureBundle :=
  Function.update b t ((b t).valueWith v)

@[simp] theorem valueAt_apply_self (b : FeatureBundle) (v : t.ValueOf) :
    b.valueAt t v t = (b t).valueWith v := by
  simp [valueAt]

/-- Valuation is inflationary in the subsumption order, so Agree only adds information. -/
theorem le_valueAt (b : FeatureBundle) (v : t.ValueOf) : b ≤ b.valueAt t v :=
  le_update_self_iff.mpr (FeatureSlot.le_valueWith v _)

/-- The probe's bundle valued from the goal's value at dimension `t`, or `none` when the goal has
no value to transmit. -/
def applyAgree : Option FeatureBundle :=
  (goal.getValuedFeature t).map (probe.valueAt t)

@[simp] theorem applyAgree_bot : probe.applyAgree ⊥ t = none := rfl

theorem applyAgree_eq_none_iff : probe.applyAgree goal t = none ↔ ¬ goal.hasValuedFeature t := by
  cases h : goal t <;> simp [applyAgree, getValuedFeature, hasValuedFeature, FeatureSlot.value?,
    FeatureSlot.isValued, h]

/-- A probe valued by Agree only gains information. -/
theorem le_of_applyAgree_eq_some {probe' : FeatureBundle}
    (h : probe.applyAgree goal t = some probe') : probe ≤ probe' := by
  obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact le_valueAt t probe v

end FeatureBundle

end Minimalist
