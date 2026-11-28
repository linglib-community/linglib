/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Negation.Strength
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.WithBot

/-!
# Distributions of polarity items

The *negativity* of a context is the greatest strength of negation that it carries and the
greatest that it holds outright, each `⊥` when there is none. The *distribution* of a polarity item
is the set of contexts in which it occurs, a context being given by its negativity and by whether
it licenses free choice.

Three families of distributions generate those of the literature. The negative polarity items of
a strength `s` occur where the context carries `s`, the positive polarity items of `s` occur where
the context does not hold `s`, and the free choice items occur where the context licenses free
choice. An item that is both a negative polarity item and a free choice item, as English *any* is,
has the join of two of these, and an item that a strength licenses and a greater strength
excludes, as Dutch *ooit* 'ever' is, has a meet. A distribution is that of a negative polarity
item when a context of no negativity is outside it, and that of a positive polarity item when the
context of clausal negation is outside it.

## Main definitions

* `PolarityItem.Negativity`: the strength a context carries and the strength it holds.
* `PolarityItem.Distribution`: a set of contexts, each a negativity with a free choice status.
* `PolarityItem.Distribution.npi`, `PolarityItem.Distribution.ppi`,
  `PolarityItem.Distribution.fci`: the three generating families.
* `PolarityItem.Distribution.IsNPI`, `PolarityItem.Distribution.IsPPI`.

## Main results

* `PolarityItem.Distribution.npiOrderEmbedding`: a stronger requirement gives a smaller
  distribution, and conversely.
* `PolarityItem.Distribution.mem_ppi_iff_notMem_npi`: where a context carries what it holds, the
  positive and the negative polarity items of a strength are in complementary distribution.

## Implementation notes

* A distribution is any set of contexts with decidable membership, so that a judgment about a
  named context is decided by evaluating the condition that defines the distribution. Any such set
  is allowed. Which sets are the distributions of items is what the
  laws of polarity say, so those are statements about distributions and not conditions on the
  type.
* The names that authors give to distributions differ: the negative polarity items of the
  anti-additive strength are Zwarts's *strong* items and van der Wouden's items of *medium*
  strength. The distributions are therefore named by the strength, and an author's terms are
  given in the study of that author.
* Free choice is not a degree of negativity, so it is a separate component of a context.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [szabolcsi-2004]
* [chierchia-2006]
-/

@[expose] public section

namespace PolarityItem

open Negation

/-- The degrees of negativity of a context: the greatest strength of negation that it carries and
the greatest that it holds outright, each `⊥` when there is none. -/
@[ext]
structure Negativity where
  /-- The greatest strength of negation that the context carries. -/
  carried : WithBot Strength
  /-- The greatest strength of negation that the context holds outright. -/
  held : WithBot Strength
  deriving DecidableEq

namespace Negativity

/-- A context of no negativity carries and holds no strength. -/
instance : Bot Negativity := ⟨⟨⊥, ⊥⟩⟩

@[simp] theorem bot_carried : (⊥ : Negativity).carried = ⊥ := rfl

@[simp] theorem bot_held : (⊥ : Negativity).held = ⊥ := rfl

/-- The negativity of a context that carries and holds exactly the strengths up to `s`. -/
def ofStrength (s : Strength) : Negativity := ⟨s, s⟩

@[simp] theorem ofStrength_carried (s : Strength) : (ofStrength s).carried = s := rfl

@[simp] theorem ofStrength_held (s : Strength) : (ofStrength s).held = s := rfl

end Negativity

/-- The distribution of a polarity item: the contexts in which it occurs, each given by its
negativity and by whether it licenses free choice. -/
structure Distribution where
  /-- The contexts in which the item occurs. -/
  carrier : Set (Negativity × Bool)
  /-- Whether a context is in the distribution is decidable. -/
  [decidableMem : DecidablePred (· ∈ carrier)]

namespace Distribution

instance : SetLike Distribution (Negativity × Bool) where
  coe := carrier
  coe_injective := fun a b h ↦ by
    cases a
    cases b
    cases h
    congr

instance : PartialOrder Distribution := .ofSetLike Distribution

instance (d : Distribution) (x : Negativity × Bool) : Decidable (x ∈ d) := d.decidableMem x

instance : Max Distribution :=
  ⟨fun d d' ↦ { carrier := {x | x ∈ d ∨ x ∈ d'}
                decidableMem := fun x ↦ inferInstanceAs (Decidable (x ∈ d ∨ x ∈ d')) }⟩

instance : Min Distribution :=
  ⟨fun d d' ↦ { carrier := {x | x ∈ d ∧ x ∈ d'}
                decidableMem := fun x ↦ inferInstanceAs (Decidable (x ∈ d ∧ x ∈ d')) }⟩

variable {s t : Strength} {n : Negativity} {fc : Bool} {d d' : Distribution}
  {x : Negativity × Bool}

@[simp] theorem mem_sup : x ∈ d ⊔ d' ↔ x ∈ d ∨ x ∈ d' := .rfl

@[simp] theorem mem_inf : x ∈ d ⊓ d' ↔ x ∈ d ∧ x ∈ d' := .rfl

/-- The distribution of the negative polarity items of strength `s`: the contexts that carry
`s`. -/
def npi (s : Strength) : Distribution where
  carrier := {x | (s : WithBot Strength) ≤ x.1.carried}
  decidableMem := fun x ↦ inferInstanceAs (Decidable ((s : WithBot Strength) ≤ x.1.carried))

/-- The distribution of the positive polarity items of strength `s`: the contexts that do not hold
`s` outright. -/
def ppi (s : Strength) : Distribution where
  carrier := {x | ¬(s : WithBot Strength) ≤ x.1.held}
  decidableMem := fun x ↦ inferInstanceAs (Decidable ¬(s : WithBot Strength) ≤ x.1.held)

/-- The distribution of the free choice items: the contexts that license free choice. -/
def fci : Distribution where
  carrier := {x | x.2 = true}
  decidableMem := fun x ↦ inferInstanceAs (Decidable (x.2 = true))

@[simp] theorem mem_npi : (n, fc) ∈ npi s ↔ (s : WithBot Strength) ≤ n.carried := .rfl

@[simp] theorem mem_ppi : (n, fc) ∈ ppi s ↔ ¬(s : WithBot Strength) ≤ n.held := .rfl

@[simp] theorem mem_fci : (n, fc) ∈ fci ↔ fc = true := .rfl

/-- A stronger requirement gives a smaller distribution. -/
theorem npi_antitone : Antitone npi := fun _ _ h ↦ IsConcreteLE.le_iff.2 fun ⟨_, _⟩ hp ↦
  mem_npi.2 (le_trans (WithBot.coe_le_coe.2 h) (mem_npi.1 hp))

/-- A stronger blocker gives a larger distribution. -/
theorem ppi_monotone : Monotone ppi := fun _ _ h ↦ IsConcreteLE.le_iff.2 fun ⟨_, _⟩ hp ↦
  mem_ppi.2 fun ht ↦ mem_ppi.1 hp (le_trans (WithBot.coe_le_coe.2 h) ht)

/-- The distributions of the negative polarity items, as an order embedding of the strengths in
reverse. -/
def npiOrderEmbedding : Strengthᵒᵈ ↪o Distribution :=
  .ofMapLEIff (fun s ↦ npi s.ofDual) fun s t ↦
    ⟨fun h ↦ show t.ofDual ≤ s.ofDual from WithBot.coe_le_coe.1 (mem_npi.1
        (IsConcreteLE.le_iff.1 h
          (mem_npi.2 (le_refl _) : (Negativity.ofStrength s.ofDual, false) ∈ npi s.ofDual))),
      fun h ↦ npi_antitone h⟩

@[simp] theorem npiOrderEmbedding_apply (s : Strengthᵒᵈ) : npiOrderEmbedding s = npi s.ofDual :=
  rfl

/-- Where a context carries what it holds, the positive and the negative polarity items of a
strength are in complementary distribution. -/
theorem mem_ppi_iff_notMem_npi (h : n.carried = n.held) : (n, fc) ∈ ppi s ↔ (n, fc) ∉ npi s := by
  simp [h]

/-- The distribution of a negative polarity item: a context of no negativity that does not license
free choice is outside it. -/
def IsNPI (d : Distribution) : Prop := ((⊥ : Negativity), false) ∉ d

/-- The distribution of a positive polarity item: the context of clausal negation is outside
it. -/
def IsPPI (d : Distribution) : Prop := (Negativity.ofStrength .antimorphic, false) ∉ d

instance : DecidablePred IsNPI := fun d ↦ inferInstanceAs (Decidable (_ ∉ d))

instance : DecidablePred IsPPI := fun d ↦ inferInstanceAs (Decidable (_ ∉ d))

theorem isNPI_npi (s : Strength) : (npi s).IsNPI := by simp [IsNPI]

theorem isPPI_ppi (s : Strength) : (ppi s).IsPPI := by
  simp [IsPPI, WithBot.coe_le_coe]

theorem not_isPPI_npi (s : Strength) : ¬(npi s).IsPPI := by
  simp [IsPPI, WithBot.coe_le_coe]

theorem not_isNPI_ppi (s : Strength) : ¬(ppi s).IsNPI := by simp [IsNPI]

theorem isNPI_fci : fci.IsNPI := by simp [IsNPI]

end Distribution

end PolarityItem
