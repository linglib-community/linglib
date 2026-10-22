module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Agree: closest goals, horizons, and valuation

This file states the structural conditions of Agree over syntactic objects and its valuation step
over feature bundles. A probe on the head at a position of a planar object searches the positions
the head c-commands, closest by the branching positions above them, and so finds a goal that no
other satisfier asymmetrically c-commands: the Minimal Link Condition, with mutually c-commanding
candidates equidistant. A target lies behind a horizon when a leaf of the horizon category in the
probe's domain c-commands it, and valuation copies a goal's value into an unvalued probe slot,
only adding information.

## Main definitions

* `Minimalist.PlanarSyntacticObject.goals`: the terms a probe on a head finds.
* `Minimalist.SyntacticObject.behindHorizonIn`: a target c-commanded by a horizon-category leaf
  in the probe's domain.
* `Minimalist.FeatureBundle.valueAt`, `Minimalist.FeatureBundle.applyAgree`: valuation of an
  unvalued slot, and the probe's bundle valued from a goal's.

## Main results

* `Minimalist.PlanarSyntacticObject.not_finds_of_cCommands`: a satisfier that asymmetrically
  c-commands a position blocks the goal there.
* `Minimalist.PlanarSyntacticObject.finds_above_branching_iff`: among satisfiers none of which
  dominates another, a probe finds those that no satisfier asymmetrically c-commands.

## References

* [chomsky-1995], [chomsky-2000]
* [keine-2019]
* [aissen-polian-2025]
-/

@[expose] public section

namespace Minimalist

/-! ### Closest goals

A probe on the head at a position searches the positions the head c-commands, keyed by the
branching positions above each (`PlanarSyntacticObject.above`), and finds a goal minimal under the
key, the Minimal Link Condition of [chomsky-1995]. -/

namespace PlanarSyntacticObject

variable {t : PlanarSyntacticObject} {p : Probe t.val.Positions} {s : Set t.val.Positions}
  {q g : t.val.Positions}

/-- A satisfier that asymmetrically c-commands a position blocks the goal there, whatever else the
probe's domain holds. -/
theorem not_finds_of_cCommands (hq : q ∈ s) (hsq : p.sat q) (hqg : t.val.CCommands q g)
    (hgq : ¬ t.val.CCommands g q) : ¬ p.Finds s (t.above t.branching) g := fun h ↦
  h.inspects.2 hq hsq (above_branching_lt_of_cCommands hqg hgq)

/-- Among satisfiers none of which dominates another, a probe finds those that no satisfier
asymmetrically c-commands: mutually c-commanding candidates are equidistant. -/
theorem finds_above_branching_iff (hs : IsAntichain (· ≤ ·) {q | q ∈ s ∧ p.sat q}) :
    p.Finds s (t.above t.branching) g ↔ (g ∈ s ∧ p.sat g) ∧
      ∀ ⦃q⦄, q ∈ s → p.sat q → ¬ (t.val.CCommands q g ∧ ¬ t.val.CCommands g q) := by
  simpa only [Probe.Finds, and_imp] using minimalFor_iff_of_isAntichain hs (fun _ h ↦ h.2 h.1)
    fun _ _ ↦ above_branching_lt_iff

variable (t) in
/-- The terms a probe on the head `h` finds: those at the closest satisfying positions that an
occurrence of `h` c-commands. -/
def goals (p : Probe t.val.Positions) (h : SyntacticObject) : Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.val.CCommands a q} (t.above t.branching) g).image t.termAt

theorem mem_goals {h x : SyntacticObject} : x ∈ t.goals p h ↔
    ∃ a, t.termAt a = h ∧ ∃ g, p.Finds {q | t.val.CCommands a q} (t.above t.branching) g ∧
      t.termAt g = x := by
  simp only [goals, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨g, ⟨a, ha, hg⟩, hx⟩ ↦ ⟨a, ha, g, hg, hx⟩,
    fun ⟨a, ha, g, hg, hx⟩ ↦ ⟨g, ⟨a, ha, hg⟩, hx⟩⟩

end PlanarSyntacticObject

namespace SyntacticObject

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
