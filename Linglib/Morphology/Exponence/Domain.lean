module

public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Fintype.Defs

/-!
# Domain rules

This file defines domain rules, rules of exponence that apply exactly at the contexts of a
finite domain, ordered by domain inclusion so that the rule with the narrower domain is the more
specific. O'Donnell's finitely supported rules, whose domain is the finite set of forms a rule
generates, and Stump's rules of paradigm linkage, whose domain is a set of content cells, are
domain rules.

## Main definitions

* `Exponence.DomainRule`: a finite domain with an exponent, with its `Exponence.Rule` instance;
  its specificity key is the domain, ordered by inclusion.

## Main results

* `DomainRule.le_iff`, `DomainRule.lt_iff`: specificity is domain inclusion.
* `DomainRule.factorsThrough_applies_iff`: a rule's applicability factors through a map exactly
  when its domain is a union of the map's fibers.
* `DomainRule.isChain_of_nested`: rules whose overlapping domains are nested satisfy Pāṇinian
  Determinism, their Elsewhere winners forming a chain.
* `DomainRule.exists_not_isContiguous_realizeMinimal`: without Pāṇinian Determinism, minimal
  selection over upper-set domains realizes ABA even with distinct exponents on distinct
  rules.

## References

* [odonnell-2015]
* [stump-2006]
-/

@[expose] public section

namespace Morphology.Exponence

/-- A domain rule carries an exponent and applies exactly at the contexts of a finite
domain. -/
structure DomainRule (Ctx E : Type*) where
  /-- The domain is the finite set of contexts the rule applies at. -/
  dom : Finset Ctx
  /-- The exponent is what the rule assigns. -/
  exponent : E
  deriving DecidableEq

namespace DomainRule

variable {Ctx E : Type*} {r s : DomainRule Ctx E} {c : Ctx}

instance : Rule (DomainRule Ctx E) Ctx E := ⟨DomainRule.exponent, fun r c ↦ c ∈ r.dom⟩

@[simp] theorem applies_iff : Applies r c ↔ c ∈ r.dom := Iff.rfl

@[simp] theorem rule_exponent : Rule.exponent r = r.exponent := rfl

/-- A rule's domain is the set of contexts it applies in. -/
theorem coe_dom : (r.dom : Set Ctx) = applySet r := rfl

/-- A domain rule's applicability factors through `A` exactly when its domain is a union of
fibers of `A`. -/
theorem factorsThrough_applies_iff {V : Type*} {A : Ctx → V} :
    (Applies r).FactorsThrough A ↔ ∀ c c', A c = A c' → (c ∈ r.dom ↔ c' ∈ r.dom) :=
  ⟨fun h _ _ hA ↦ Iff.of_eq (h hA), fun h _ _ hA ↦ propext (h _ _ hA)⟩

/-- Rules whose overlapping domains are nested satisfy Pāṇinian Determinism, their Elsewhere
winners at any context forming a chain. -/
theorem isChain_of_nested {v : RuleSet (DomainRule Ctx E)}
    (h : ∀ r ∈ v, ∀ s ∈ v, ¬ Disjoint r.dom s.dom → r.dom ⊆ s.dom ∨ s.dom ⊆ r.dom) (c : Ctx) :
    IsChain (fun r s ↦ r.dom ≤ s.dom) {r | v.IsElsewhereWinner (·.dom) c r} :=
  fun r (hr : v.IsElsewhereWinner (·.dom) c r) s (hs : v.IsElsewhereWinner (·.dom) c s) _ ↦
    h r hr.prop.1 s hs.prop.1 (Finset.not_disjoint_iff.mpr ⟨c, hr.prop.2, hs.prop.2⟩)

variable [DecidableEq Ctx]

instance : DecidableRel (Applies : DomainRule Ctx E → Ctx → Prop) :=
  fun r c ↦ inferInstanceAs (Decidable (c ∈ r.dom))

instance [Fintype Ctx] {V : Type*} [DecidableEq V] (r : DomainRule Ctx E) (A : Ctx → V) :
    Decidable ((Applies r).FactorsThrough A) :=
  decidable_of_iff _ factorsThrough_applies_iff.symm

/-- Without Pāṇinian Determinism, minimal selection realizes ABA. Over feature bundles ordered by
inclusion, a rule `S` for feature `1`, a rule `R` for feature `0`, and a rule `T` for features
`1` and `2` each apply on an upper set, and listed in that order they realize `R`, `S`, `R` on the
chain `{0} ⊆ {0, 1} ⊆ {0, 1, 2}`: at `{0, 1}` the winners `S` and `R` are incomparable, and the
list order picks `S`. -/
theorem exists_not_isContiguous_realizeMinimal :
    ∃ v : RuleSet (DomainRule (Finset (Fin 3)) String), v.Antihomophonous ∧
      (∀ r ∈ v, IsUpperSet (r.dom : Set (Finset (Fin 3)))) ∧
        ¬ IsContiguous (v.realizeMinimal (·.dom)) := by
  let up (x : Finset (Fin 3)) : Finset (Finset (Fin 3)) := Finset.univ.filter (x ⊆ ·)
  have hup (x) : IsUpperSet (up x : Set (Finset (Fin 3))) := fun a b hab ha ↦ by
    simp only [up, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.trans hab
  refine ⟨[⟨up {1}, "S"⟩, ⟨up {0}, "R"⟩, ⟨up {1, 2}, "T"⟩], by decide, ?_, fun h ↦ ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hup _, hup _, hup _⟩
  · exact absurd (h (i := {0}) (j := {0, 1}) (k := {0, 1, 2}) (by decide) (by decide) (by decide))
      (by decide)

end DomainRule

end Morphology.Exponence
