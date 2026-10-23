module

public import Linglib.Syntax.Mereological.Parthood

/-!
# Angular Locality

Angular Locality is the locality principle of mereological syntax: a part `γ` may subjoin to
`β` only if `γ` is an `n`-part of some object `α` that is a 1-part of `β`. Since parthood is
transitive within a dimension only, a subjunction path may turn through at most one angle, from
dimension `n` into dimension 1. Everything the classical theory stipulates about cyclic domains
and their escape hatches follows: 2-parts are the locality domains, and an object leaves a 2-part
just when it is a 2-part of it.

A domain of a 2-part `b` is a set of parts that parthood leaves only through 2-edges from `b` or
from a 2-part of `b`, the edge of `b`. The material inside a 2-part is such a domain, and it stays
one while its edge moves out.

## Main definitions

* `Parthood.CanSubjoin γ β`: Angular Locality for subjunction of `γ` to `β`.
* `Parthood.IsDomain P S b`: `S` is a locality domain of `b`.

## Main statements

* `Parthood.descendant_of_canSubjoin`: the target contains the mover.
* `Parthood.not_canSubjoin_of_imm_one`: antilocality, from irreflexivity of parthood.
* `Parthood.IsDomain.canSubjoin_iff_nPart_two`: an object inside a domain reaches an object
  outside it exactly when it lies on the edge of `b`.

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

theorem descendant_of_canSubjoin (h : P.CanSubjoin γ β) : P.Descendant γ β :=
  let ⟨_, _, h₁, h₂⟩ := h
  (descendant_of_nPart h₁).trans (descendant_of_nPart h₂)

theorem isSome_onePart_of_canSubjoin (h : P.CanSubjoin γ β) : (P.onePart β).isSome :=
  let ⟨_, _, _, h₂⟩ := h
  let ⟨c, _, hc⟩ := TransGen.tail'_iff.1 h₂
  Option.isSome_iff_exists.2 ⟨c, hc⟩

/-! ### Antilocality -/

theorem not_canSubjoin_of_imm_one (hP : P.Acyclic) (h : P.Imm .one γ β) :
    ¬ P.CanSubjoin γ β := by
  rintro ⟨_, a, hγa, haβ⟩
  obtain ⟨c, hac, hcβ⟩ := TransGen.tail'_iff.1 haβ
  obtain rfl : c = γ := Option.some_injective _ (hcβ.symm.trans h)
  rcases reflTransGen_iff_eq_or_transGen.1 hac with rfl | hac
  · exact hP _ (descendant_of_nPart hγa)
  · exact hP _ ((descendant_of_nPart hγa).trans (descendant_of_nPart hac))

/-! ### Locality domains -/

/-- `S` is a domain of `b` when its objects are parts and every parthood edge leaving `S` is a
2-edge from `b` or from a 2-part of `b`. -/
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

theorem IsDomain.canSubjoin_iff_nPart_two {S : Set α} {b d : α} (hD : P.IsDomain S b)
    (hbd : P.Imm .two b d) (hd : P.NPart .one d β) (hγ : γ ∈ S) (hγb : γ ≠ b) (hβ : β ∉ S) :
    P.CanSubjoin γ β ↔ P.NPart .two γ b :=
  ⟨fun h ↦ (hD.eq_or_nPart_two_of_canSubjoin hγ hβ h).resolve_left hγb,
    fun h ↦ canSubjoin_of_nPart_two h hbd hd⟩

end MereologicalSyntax.Parthood
