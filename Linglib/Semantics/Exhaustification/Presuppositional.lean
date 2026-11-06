module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Homogeneity.Defs
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Exhaustification.InnocentInclusion

/-!
# Presuppositional exhaustification

A presuppositional exhaustivity operator asserts its prejacent alone and presupposes what the
exhaustivity operator asserts besides. Bassi, Del Pinal and Sauerland's `pex^{IE}` presupposes
that the relevant innocently excludable alternatives are false (`excludesIE`), and in trivalent
form it is true where the prejacent is true and the presupposition holds, and false exactly where
the prejacent is false, so that it contributes nothing to the falsity conditions of its
prejacent. Del Pinal, Bassi and Sauerland's `pex^{IE+II}` adds the presupposition that the
relevant innocently includable alternatives other than the prejacent are homogeneous, true
together or false together, and its presupposition survives negation: negation denies the
assertion and leaves the presupposition. When the prejacent lies between the meet and the join of
those alternatives, as `◇(p ∨ q)` lies between `◇p ∧ ◇q` and `◇p ∨ ◇q`, homogeneity makes it true
where all of them are and false where none is.

## Main definitions

* `pexIE`: the operator of Bassi, Del Pinal and Sauerland, the Strong Kleene conjunction of the
  prejacent with the presupposition.
* `pexIEII`: the operator of Del Pinal, Bassi and Sauerland, defined where its presupposition
  holds.

## Main results

* `pexIE_eq_true_iff_mem_exhIE`, `pexIE_nonneg_iff`: `pex^{IE}` is designated at K3 exactly where
  the exhaustified prejacent is true and at LP exactly where the prejacent is.
* `pexIEII_eq_pexIE`: without relevant includable alternatives, the two operators agree when the
  relevant excludable alternatives entail the prejacent.
* `pexIEII_eq_true_iff_forall_mem`, `pexIEII_eq_false_iff_forall_notMem`: a prejacent between
  the meet and the join of its relevant includable alternatives is true together with all of them
  and false together with all of them.

## Implementation notes

The two operators differ in their falsity conditions. Bassi, Del Pinal and Sauerland give the
trivalent entry as their (14) and set aside, in footnote 15, an entry that is false only where the
presupposition holds, since the contribution of `pex` to the falsity conditions of its prejacent
must be vacuous; the two entries agree when every excludable alternative is stronger than the
prejacent. The set-aside entry is the indicator of `excludesIE` on the prejacent, the form of a
trigger in `Presupposition`. Del Pinal, Bassi and Sauerland state `pex^{IE+II}` as an assertion
and a presupposition and say that, other than the includable alternatives, they follow the earlier
paper; their negative free choice under negation, `¬pex^{IE+II}[□(T ∧ B)]` (their (20)), has the
presupposition `□T ↔ □B` project from under negation although `□T` and `□B` are weaker than the
prejacent, which takes the analogue of the set-aside entry for includable alternatives. `pexIEII`
follows the later paper.

## References

* [delpinal-bassi-sauerland-2024]
* [bassi-delpinal-sauerland-2021]
* [bar-lev-fox-2020]
-/

@[expose] public section

namespace Exhaustification

open Homogeneity

variable {World : Type*}

/-! ### `pex^{IE}` -/

open Classical in
/-- `pex^{IE}` ([bassi-delpinal-sauerland-2021], (14)) is true where the prejacent is true and the
relevant innocently excludable alternatives are false, and false exactly where the prejacent is
false: the Strong Kleene conjunction of the prejacent with the presupposition. -/
noncomputable def pexIE (ALT : Set (Set World)) (φ : Set World) (Rc : Set (Set World)) :
    World → Trivalent := fun w ↦
  Trivalent.ofProp (w ∈ φ) ⊓ (Trivalent.ofProp (w ∈ excludesIE ALT φ Rc) ⊔ .undefined)

section PexIE

variable {ALT : Set (Set World)} {φ : Set World} {Rc : Set (Set World)} {w : World}

theorem pexIE_eq_true_iff : pexIE ALT φ Rc w = .true ↔ w ∈ φ ∧ w ∈ excludesIE ALT φ Rc := by
  simp [pexIE]

theorem pexIE_eq_false_iff : pexIE ALT φ Rc w = .false ↔ w ∉ φ := by
  simp [pexIE]

/-- With every alternative relevant, `pex^{IE}` is true exactly where the exhaustified prejacent
is. -/
theorem pexIE_eq_true_iff_mem_exhIE (h : ALT ⊆ Rc) : pexIE ALT φ Rc w = .true ↔ w ∈ exhIE ALT φ :=
  pexIE_eq_true_iff.trans <| and_congr_right fun _ ↦
    forall₂_congr fun _ hψ ↦ ⟨fun H ↦ H (h hψ.1), fun H _ ↦ H⟩

/-- `pex^{IE}` is not false exactly where its prejacent is true. -/
theorem pexIE_nonneg_iff : .undefined ≤ pexIE ALT φ Rc w ↔ w ∈ φ := by
  rw [Trivalent.undefined_le_iff_ne_false, Ne, pexIE_eq_false_iff, not_not]

end PexIE

/-! ### `pex^{IE+II}` -/

open Classical in
/-- `pex^{IE+II}` asserts the prejacent and presupposes that the innocently excludable
alternatives in the relevance set `Rc` are false and that the innocently includable ones in it,
other than the prejacent, are homogeneous. -/
noncomputable def pexIEII (ALT : Set (Set World)) (φ : Set World) (Rc : Set (Set World)) :
    World → Trivalent :=
  fun w ↦ Trivalent.transplication (Trivalent.ofProp (w ∈ (excludesIE ALT φ Rc ∩
    {w | Homogeneous {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ} w})))
    (Trivalent.ofProp (w ∈ φ))

variable {ALT : Set (Set World)} {φ : Set World} {Rc : Set (Set World)} {w : World}

theorem pexIEII_ne_undefined_iff :
    pexIEII ALT φ Rc w ≠ .undefined ↔ w ∈ excludesIE ALT φ Rc ∧
      Homogeneous {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ} w := by
  simp [pexIEII]

theorem pexIEII_eq_true_iff :
    pexIEII ALT φ Rc w = .true ↔ pexIEII ALT φ Rc w ≠ .undefined ∧ w ∈ φ := by
  simp [pexIEII]

theorem pexIEII_eq_false_iff :
    pexIEII ALT φ Rc w = .false ↔ pexIEII ALT φ Rc w ≠ .undefined ∧ w ∉ φ := by
  simp [pexIEII]

/-- A prejacent between the meet and the join of its relevant includable alternatives is true
under `pex` exactly where the presupposition holds and all of them are true. -/
theorem pexIEII_eq_true_iff_forall_mem
    (hl : ⋂₀ {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ} ⊆ φ)
    (hu : φ ⊆ ⋃₀ {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ}) :
    pexIEII ALT φ Rc w = .true ↔ pexIEII ALT φ Rc w ≠ .undefined ∧
      ∀ α ∈ {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ}, w ∈ α :=
  pexIEII_eq_true_iff.trans <|
    and_congr_right fun h ↦ (pexIEII_ne_undefined_iff.1 h).2.mem_iff hl hu

/-- A prejacent between the meet and the join of its relevant includable alternatives is false
under `pex` exactly where the presupposition holds and all of them are false. -/
theorem pexIEII_eq_false_iff_forall_notMem
    (hl : ⋂₀ {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ} ⊆ φ)
    (hu : φ ⊆ ⋃₀ {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ}) :
    pexIEII ALT φ Rc w = .false ↔ pexIEII ALT φ Rc w ≠ .undefined ∧
      ∀ α ∈ {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ}, w ∉ α :=
  pexIEII_eq_false_iff.trans <| and_congr_right fun h ↦
    (pexIEII_ne_undefined_iff.1 h).2.notMem_iff hl hu

theorem pexIEII_ne_undefined_iff_of_inter_eq_empty
    (h : {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ} = ∅) :
    pexIEII ALT φ Rc w ≠ .undefined ↔ w ∈ excludesIE ALT φ Rc := by
  simp [pexIEII_ne_undefined_iff, h]

/-- Without relevant includable alternatives, `pex^{IE+II}` is `pex^{IE}` when the relevant
excludable alternatives entail the prejacent: where the prejacent is false, so are they. -/
theorem pexIEII_eq_pexIE (h : {a ∈ Rc | IsInnocentlyIncludable ALT φ a ∧ a ≠ φ} = ∅)
    (hIE : ∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → ψ ⊆ φ) :
    pexIEII ALT φ Rc = pexIE ALT φ Rc := by
  funext w
  refine Trivalent.eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · rw [pexIEII_eq_true_iff, pexIEII_ne_undefined_iff_of_inter_eq_empty h, pexIE_eq_true_iff,
      and_comm]
  · rw [pexIEII_eq_false_iff, pexIEII_ne_undefined_iff_of_inter_eq_empty h, pexIE_eq_false_iff,
      and_iff_right_iff_imp]
    exact fun hw ψ hψ hR hwψ ↦ hw (hIE ψ hψ hR hwψ)

end Exhaustification
