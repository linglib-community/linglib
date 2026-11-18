/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.Autosegmental.Factors

/-!
# Representations on two tiers

A representation on two tiers has an upper tier of autosegments over a lower tier of slots. Its
lines all run between the two tiers, so the lines from the upper to the lower tier
[determine it](##Autosegmental.AR.ext_of_upper_lower), and every statement about its lines
reduces to that one pair of tiers: the No-Crossing Constraint
[is the constraint on them](##Autosegmental.AR.noCrossing_iff_two_tier), and one representation
embeds in another as a factor when its two words occur at
[a pair of bounded offsets](##Autosegmental.AR.factorEmbeds_iff_two_tier) at which its lines are
lines of the host. Embedding and freedom from a banned-subgraph grammar are therefore decidable.
`AR.ofLines` writes such a representation down from its two words and a finite set of lines, and
[every one arises so](##Autosegmental.AR.ofLines_eta). Jardine's autosegmental graph primitive
is `AR.primitive`, a melody over one timing slot.

## Implementation notes

`AR.ofLines` drops the pairs out of range, as `SimpleGraph.fromEdgeSet` drops loops.
[jardine-2019]'s Definition 1 requires of a primitive only that each of its lines ends at the
timing slot. `AR.primitive` associates every melody node, as the primitives of the paper's `gT`
are.

## References

* [jardine-2016b]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

universe u

/-- The two tiers of a two-tier representation, the upper tier of autosegments and the lower
tier of slots. -/
inductive Tier
  | upper
  | lower
  deriving DecidableEq, Fintype

@[simp] theorem Tier.card : Fintype.card Tier = 2 := rfl

/-- The two-tier alphabet puts labels in `α` on the upper tier and labels in `β` on the lower. -/
abbrev TwoTier (α β : Type u) : Tier → Type u := fun t ↦ Tier.rec α β t

instance {α β : Type u} [DecidableEq α] [DecidableEq β] : ∀ t, DecidableEq (TwoTier α β t)
  | .upper => inferInstanceAs (DecidableEq α)
  | .lower => inferInstanceAs (DecidableEq β)

namespace AR

open Tier

variable {τ : Tier → Type*} {F X Y : AR τ}

/-! ### Lines -/

theorem link_iff_of_upper_lower (h : ∀ p q, X.Link upper lower p q ↔ Y.Link upper lower p q)
    (i j : Tier) (p q : ℕ) : X.Link i j p q ↔ Y.Link i j p q := by
  cases i <;> cases j
  · exact iff_of_false (fun h ↦ h.ne rfl) (fun h ↦ h.ne rfl)
  · exact h p q
  · exact link_comm.trans ((h q p).trans link_comm)
  · exact iff_of_false (fun h ↦ h.ne rfl) (fun h ↦ h.ne rfl)

/-- Two representations on two tiers are equal when their words are and they have the same lines
from the upper to the lower tier. -/
theorem ext_of_upper_lower (hu : X.word upper = Y.word upper) (hl : X.word lower = Y.word lower)
    (h : ∀ p q, X.Link upper lower p q ↔ Y.Link upper lower p q) : X = Y :=
  ext (funext fun t ↦ by cases t <;> assumption) (link_iff_of_upper_lower h)

/-- A representation with no line from the upper to the lower tier has no lines. -/
theorem not_link_of_lines_eq_empty (h : X.lines upper lower = ∅) (i j : Tier) (p q : ℕ) :
    ¬ X.Link i j p q := fun hl ↦
  not_link_one i j p q <| (link_iff_of_upper_lower (Y := 1) (fun p q ↦ by simp [Link, h]) ..).1 hl

/-! ### The No-Crossing Constraint -/

theorem noCrossing_iff_two_tier :
    X.NoCrossing ↔ IsNonCrossing (X.lines upper lower : SetRel ℕ ℕ) := by
  refine ⟨fun h ↦ h upper lower, fun h i j ↦ ?_⟩
  cases i <;> cases j
  exacts [isNonCrossing_lines_self _, h, isNonCrossing_lines_comm.1 h, isNonCrossing_lines_self _]

/-- A representation with at most one slot obeys the NCC. -/
theorem noCrossing_of_length_lower_le_one (h : (X.word lower).length ≤ 1) : X.NoCrossing :=
  noCrossing_iff_two_tier.2 <| isNonCrossing_lines_iff.2 fun _ _ _ _ h₁ h₂ _ ↦ by
    have := h₁.lt_right
    have := h₂.lt_right
    omega

/-! ### Factor embedding -/

theorem isFactorAt_iff_two_tier {o : Tier → ℕ} : F.IsFactorAt X o ↔
    F.word upper <+: (X.word upper).drop (o upper) ∧
      F.word lower <+: (X.word lower).drop (o lower) ∧
        ∀ p q, F.Link upper lower p q → X.Link upper lower (p + o upper) (q + o lower) := by
  refine ⟨fun h ↦ ⟨h.window upper, h.window lower, h.link_map upper lower⟩, fun ⟨hu, hl, hk⟩ ↦
    ⟨fun t ↦ by cases t <;> assumption, ?_⟩⟩
  rintro (_ | _) (_ | _) p q h
  exacts [absurd rfl h.ne, hk p q h, (hk q p h.symm).symm, absurd rfl h.ne]

/-- One representation embeds in another as a factor iff its words occur in the host's at a pair
of bounded offsets and its lines are lines of the host there. -/
theorem factorEmbeds_iff_two_tier : F ⊑ X ↔
    ∃ a ≤ (X.word upper).length, ∃ b ≤ (X.word lower).length,
      F.word upper <+: (X.word upper).drop a ∧ F.word lower <+: (X.word lower).drop b ∧
        ∀ p < (F.word upper).length, ∀ q < (F.word lower).length,
          F.Link upper lower p q → X.Link upper lower (p + a) (q + b) := by
  rw [factorEmbeds_iff_bounded]
  constructor
  · rintro ⟨o, hb, h⟩
    obtain ⟨hu, hl, hk⟩ := isFactorAt_iff_two_tier.1 h
    exact ⟨o upper, hb upper, o lower, hb lower, hu, hl, fun p _ q _ ↦ hk p q⟩
  · rintro ⟨a, ha, b, hb, hu, hl, hk⟩
    exact ⟨fun t ↦ Tier.rec a b t, fun t ↦ by cases t <;> assumption,
      isFactorAt_iff_two_tier.2 ⟨hu, hl, fun p q h ↦ hk p h.lt_left q h.lt_right h⟩⟩

instance [∀ t, DecidableEq (τ t)] : Decidable (F ⊑ X) :=
  decidable_of_iff _ factorEmbeds_iff_two_tier.symm

instance [∀ t, DecidableEq (τ t)] (B : List (AR τ)) : Decidable (X.Free B) :=
  inferInstanceAs (Decidable (∀ F ∈ B, ¬ F ⊑ X))

/-! ### Representations from words and lines -/

section OfLines

variable {α β : Type u} (u : List α) (v : List β) (L : Finset (ℕ × ℕ))

/-- `ofLines u v L` has the upper tier `u` over the lower tier `v`, with a line for each pair in
`L` of a position of `u` and a position of `v`. -/
def ofLines : AR (TwoTier α β) where
  word
    | upper => u
    | lower => v
  lines
    | upper, lower => L.filter fun x ↦ x.1 < u.length ∧ x.2 < v.length
    | lower, upper => (L.filter fun x ↦ x.1 < u.length ∧ x.2 < v.length).map
        (Equiv.prodComm ℕ ℕ).toEmbedding
    | _, _ => ∅
  lines_self t := by cases t <;> rfl
  swap_mem_lines i j p q h := by cases i <;> cases j <;> simp_all
  fst_lt_of_mem_lines i j p q h := by cases i <;> cases j <;> simp_all

@[simp] theorem word_ofLines_upper : (ofLines u v L).word upper = u := rfl

@[simp] theorem word_ofLines_lower : (ofLines u v L).word lower = v := rfl

/-- The lines of `ofLines` are the given pairs within range of its tiers. -/
@[simp] theorem lines_ofLines : (ofLines u v L).lines upper lower =
    L.filter fun x ↦ x.1 < u.length ∧ x.2 < v.length := rfl

variable {u v L} in
@[simp] theorem link_ofLines {p q : ℕ} :
    (ofLines u v L).Link upper lower p q ↔ (p, q) ∈ L ∧ p < u.length ∧ q < v.length :=
  Finset.mem_filter

/-- Every representation on two tiers is `ofLines` of its words and its lines. -/
@[simp] theorem ofLines_eta (X : AR (TwoTier α β)) :
    ofLines (X.word upper) (X.word lower) (X.lines upper lower) = X :=
  ext_of_upper_lower rfl rfl fun _ _ ↦
    link_ofLines.trans ⟨fun h ↦ h.1, fun h ↦ ⟨h, Link.lt_left h, Link.lt_right h⟩⟩

variable (as : List α) (b : β)

/-- The autosegmental graph primitive of [jardine-2019] Definition 1 has one timing slot `b`,
with every node of the melody `as` associated to it. -/
def primitive : AR (TwoTier α β) := ofLines as [b] (Finset.range as.length ×ˢ {0})

@[simp] theorem word_primitive_upper : (primitive as b).word upper = as := rfl

@[simp] theorem word_primitive_lower : (primitive as b).word lower = [b] := rfl

variable {as b} in
@[simp] theorem link_primitive {p q : ℕ} :
    (primitive as b).Link upper lower p q ↔ p < as.length ∧ q = 0 := by
  simp only [primitive, link_ofLines, Finset.mem_product, Finset.mem_range, Finset.mem_singleton,
    List.length_singleton]
  omega

/-- Primitives obey the NCC, having one timing slot. -/
theorem noCrossing_primitive : (primitive as b).NoCrossing :=
  noCrossing_of_length_lower_le_one le_rfl

end OfLines

/-! ### Surfacing -/

variable {α β : Type u} {X : AR (TwoTier α β)} {a : α} {j : ℕ}

variable (X a j) in
/-- Slot `j` surfaces with label `a` when some `a`-labelled autosegment links to it. -/
def SurfacesWith : Prop :=
  ∃ k, X.Link upper lower k j ∧ (X.word upper)[k]? = some a

theorem SurfacesWith.lt (h : X.SurfacesWith a j) : j < (X.word lower).length :=
  h.choose_spec.1.lt_right

end AR

end Autosegmental
