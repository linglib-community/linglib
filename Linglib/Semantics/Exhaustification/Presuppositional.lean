module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Homogeneity.Defs
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Exhaustification.InnocentInclusion

/-!
# Presuppositional exhaustification

The presuppositional exhaustivity operator `pex^{IE+II}` of Del Pinal, Bassi and Sauerland,
extending the `pex^{IE}` of Bassi, Del Pinal and Sauerland, asserts its prejacent alone. It
presupposes that the relevant innocently excludable alternatives are false and that the relevant
innocently includable ones other than the prejacent are homogeneous, true together or false
together, so negation denies the assertion and leaves the presupposition. When the prejacent lies
between the meet and the join of those alternatives, as `◇(p ∨ q)` lies between `◇p ∧ ◇q` and
`◇p ∨ ◇q`, homogeneity makes it true where all of them are and false where none is.

## Main declarations

* `pexIEII`: the operator.
* `pexIEII_eq_one_iff_forall_mem`, `pexIEII_eq_neg_one_iff_forall_notMem`: a prejacent between
  the meet and the join of its relevant includable alternatives is true together with all of them
  and false together with all of them.

## References

* [delpinal-bassi-sauerland-2024]
* [bassi-delpinal-sauerland-2021]
* [bar-lev-fox-2020]
-/

@[expose] public section

namespace Exhaustification

open Homogeneity

variable {World : Type*}

open Classical in
/-- `pex^{IE+II}` asserts the prejacent and presupposes that the innocently excludable
alternatives in the relevance set `Rc` are false and that the innocently includable ones in it,
other than the prejacent, are homogeneous. -/
noncomputable def pexIEII (ALT : Set (Set World)) (φ : Set World) (Rc : Set (Set World)) :
    World → SignType :=
  {w | (∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → w ∉ ψ) ∧
    Homogeneous (II ALT φ \ {φ} ∩ Rc) w}.indicator fun w ↦ SignType.ofProp (w ∈ φ)

variable {ALT : Set (Set World)} {φ : Set World} {Rc : Set (Set World)} {w : World}

theorem pexIEII_ne_zero_iff :
    pexIEII ALT φ Rc w ≠ 0 ↔ (∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → w ∉ ψ) ∧
      Homogeneous (II ALT φ \ {φ} ∩ Rc) w := by
  simp [pexIEII]

theorem pexIEII_eq_one_iff : pexIEII ALT φ Rc w = 1 ↔ pexIEII ALT φ Rc w ≠ 0 ∧ w ∈ φ := by
  simp [pexIEII]

theorem pexIEII_eq_neg_one_iff : pexIEII ALT φ Rc w = -1 ↔ pexIEII ALT φ Rc w ≠ 0 ∧ w ∉ φ := by
  simp [pexIEII]

theorem pexIEII_eq_one_iff_forall_mem (hl : ⋂₀ (II ALT φ \ {φ} ∩ Rc) ⊆ φ)
    (hu : φ ⊆ ⋃₀ (II ALT φ \ {φ} ∩ Rc)) :
    pexIEII ALT φ Rc w = 1 ↔ pexIEII ALT φ Rc w ≠ 0 ∧ ∀ α ∈ II ALT φ \ {φ} ∩ Rc, w ∈ α :=
  pexIEII_eq_one_iff.trans <| and_congr_right fun h ↦ (pexIEII_ne_zero_iff.1 h).2.mem_iff hl hu

theorem pexIEII_eq_neg_one_iff_forall_notMem (hl : ⋂₀ (II ALT φ \ {φ} ∩ Rc) ⊆ φ)
    (hu : φ ⊆ ⋃₀ (II ALT φ \ {φ} ∩ Rc)) :
    pexIEII ALT φ Rc w = -1 ↔ pexIEII ALT φ Rc w ≠ 0 ∧ ∀ α ∈ II ALT φ \ {φ} ∩ Rc, w ∉ α :=
  pexIEII_eq_neg_one_iff.trans <| and_congr_right fun h ↦
    (pexIEII_ne_zero_iff.1 h).2.notMem_iff hl hu

theorem pexIEII_ne_zero_iff_of_inter_eq_empty (h : II ALT φ \ {φ} ∩ Rc = ∅) :
    pexIEII ALT φ Rc w ≠ 0 ↔ ∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → w ∉ ψ := by
  simp [pexIEII_ne_zero_iff, h]

end Exhaustification
