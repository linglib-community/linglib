/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Mereological.Parthood

/-!
# Angular Locality

Angular Locality is the locality principle of mereological syntax: a part `γ` may subjoin to
`β` only if `γ` is an `n`-part of some object `α` that is a 1-part of `β`. The mover is found by
going down the extended projection of the target to some head `α`, and from there in one
dimension only: further down the same extended projection, or to the specifier of `α`, the
specifier of that, and so on. The path turns through at most one angle. So the specifier of `v`
can subjoin to `T`, as a subject does, and so can a specifier of that specifier. Reaching a
complement inside that specifier would take a second turn.

Two consequences are proved here. The target contains the mover, which excludes lowering,
sideward and parallel subjunction. And in an acyclic structure a complement cannot subjoin again
to its own head, which is antilocality.

A domain of an object `b`, typically a specifier, is a set of parts that parthood leaves only in
the second dimension, from `b` or from a 2-part of `b`. Those objects are the edge of `b`.
Whether the objects inside a specifier form a domain depends on the structure, so being a domain
is a hypothesis here; the licensed derivations of `Derivation.lean` preserve it. An object inside
a domain can subjoin to an object outside it only if it is `b` or lies on the edge of `b`, so the
edge is the escape hatch of the domain.

## Main definitions

* `Parthood.CanSubjoin`: Angular Locality for subjunction of one object to another.
* `Parthood.IsDomain`: a set of objects is a locality domain of an object.

## Main results

* `Parthood.descendant_of_canSubjoin`: the target contains the mover.
* `Parthood.not_canSubjoin_of_imm_one`: antilocality, in an acyclic structure.
* `Parthood.IsDomain.canSubjoin_iff_nPart_two`: an object inside a domain reaches an object
  outside it exactly when it lies on the edge of the domain.

## References

* [adger-2025]
-/

@[expose] public section

namespace MereologicalSyntax.Parthood

open Relation

variable {α : Type*} {P Q : Parthood α} {n : Dim} {γ β : α}

/-- Angular Locality allows `γ` to subjoin to `β` only if `γ` is an `n`-part of some 1-part of
`β`. -/
def CanSubjoin (P : Parthood α) (γ β : α) : Prop := ∃ n a, P.NPart n γ a ∧ P.NPart .one a β

/-- Decided by running through the 1-parts of `β` first, which most objects are not. -/
instance [Fintype α] [DecidableEq α] : DecidableRel P.CanSubjoin := fun γ β ↦
  decidable_of_iff (∃ a, P.NPart .one a β ∧ ∃ n, P.NPart n γ a)
    ⟨fun ⟨a, ha, n, hn⟩ ↦ ⟨n, a, hn, ha⟩, fun ⟨n, a, hn, ha⟩ ↦ ⟨a, ha, n, hn⟩⟩

theorem CanSubjoin.mono (h : P ≤ Q) (hγβ : P.CanSubjoin γ β) : Q.CanSubjoin γ β :=
  let ⟨n, a, h₁, h₂⟩ := hγβ
  ⟨n, a, h₁.mono h, h₂.mono h⟩

/-- Lowering, sideward, and parallel subjunction are ruled out, since the target must contain the
mover. -/
theorem descendant_of_canSubjoin (h : P.CanSubjoin γ β) : P.Descendant γ β :=
  let ⟨_, _, h₁, h₂⟩ := h
  (descendant_of_nPart h₁).trans (descendant_of_nPart h₂)

theorem isSome_part_one_of_canSubjoin (h : P.CanSubjoin γ β) : (P.part .one β).isSome :=
  let ⟨_, _, _, h₂⟩ := h
  let ⟨c, _, hc⟩ := TransGen.tail'_iff.1 h₂
  Option.isSome_iff_exists.2 ⟨c, hc⟩

/-! ### Antilocality -/

/-- In an acyclic structure a complement cannot subjoin again to its own head, which is
antilocality. -/
theorem not_canSubjoin_of_imm_one (hP : P.Acyclic) (h : P.Imm .one γ β) :
    ¬ P.CanSubjoin γ β := by
  rintro ⟨_, a, hγa, haβ⟩
  rcases haβ.eq_or_nPart_of_imm h with rfl | haγ
  · exact hP _ (descendant_of_nPart hγa)
  · exact hP _ ((descendant_of_nPart hγa).trans (descendant_of_nPart haγ))

/-! ### Locality domains -/

/-- `S` is a domain of `b` when its objects are parts and every parthood edge leaving `S` is a
2-edge from `b` or from a 2-part of `b`, the edge of `b`. -/
structure IsDomain (P : Parthood α) (S : Set α) (b : α) : Prop where
  /-- The objects of the domain are parts. -/
  isPart : ∀ x ∈ S, P.IsPart x
  /-- Parthood leaves the domain only in the second dimension, from `b` or from a 2-part of
  `b`. -/
  exit : ∀ x ∈ S, ∀ n y, P.Imm n x y → y ∉ S → n = .two ∧ (x = b ∨ P.NPart .two x b)

instance [Fintype α] [DecidableEq α] {S : Set α} [DecidablePred (· ∈ S)] {b : α} :
    Decidable (P.IsDomain S b) :=
  decidable_of_iff ((∀ x ∈ S, P.IsPart x) ∧
      ∀ x ∈ S, ∀ n y, P.Imm n x y → y ∉ S → n = .two ∧ (x = b ∨ P.NPart .two x b))
    ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

namespace IsDomain

variable {S : Set α} {b x y : α}

theorem exit_of_nPart (hD : P.IsDomain S b) (h : P.NPart n x y) (hx : x ∈ S) (hy : y ∉ S) :
    n = .two ∧ (x = b ∨ P.NPart .two x b) := by
  revert hx
  induction h using TransGen.head_induction_on with
  | @single a h => exact fun hx ↦ hD.exit a hx _ _ h hy
  | @head a c h' _ ih =>
    intro hx
    by_cases hc : c ∈ S
    · obtain ⟨rfl, hcb⟩ := ih hc
      exact ⟨rfl, .inr (hcb.elim (fun e ↦ e ▸ .single h') (.head h'))⟩
    · exact hD.exit a hx _ _ h' hc

theorem eq_or_nPart_two_of_canSubjoin (hD : P.IsDomain S b) (hγ : γ ∈ S) (hβ : β ∉ S)
    (h : P.CanSubjoin γ β) : γ = b ∨ P.NPart .two γ b := by
  obtain ⟨_, a, hγa, haβ⟩ := h
  by_cases ha : a ∈ S
  · exact absurd (hD.exit_of_nPart haβ ha hβ).1 (by decide)
  · exact (hD.exit_of_nPart hγa hγ ha).2

end IsDomain

theorem canSubjoin_of_nPart_two {b d : α} (hγ : P.NPart .two γ b) (hbd : P.Imm .two b d)
    (hd : P.NPart .one d β) : P.CanSubjoin γ β :=
  ⟨.two, d, hγ.tail hbd, hd⟩

/-- From inside a domain of the 2-part `b` of `d`, an object reaches an object above `d` in `d`'s
extended projection exactly when it is a 2-part of `b`, which is the escape hatch. -/
theorem IsDomain.canSubjoin_iff_nPart_two {S : Set α} {b d : α} (hD : P.IsDomain S b)
    (hbd : P.Imm .two b d) (hd : P.NPart .one d β) (hγ : γ ∈ S) (hγb : γ ≠ b) (hβ : β ∉ S) :
    P.CanSubjoin γ β ↔ P.NPart .two γ b :=
  ⟨fun h ↦ (hD.eq_or_nPart_two_of_canSubjoin hγ hβ h).resolve_left hγb,
    fun h ↦ canSubjoin_of_nPart_two h hbd hd⟩

end MereologicalSyntax.Parthood
