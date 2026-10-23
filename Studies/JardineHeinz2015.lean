/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.MergeAR
public import Linglib.Phonology.Tone.Basic

/-!
# Jardine and Heinz (2015): A Concatenation Operation to Derive Autosegmental Graphs

Jardine and Heinz derive autosegmental graphs by concatenating graph primitives. Concatenation
bridges the two graphs tier by tier and merges the last melody node of the first with the first
melody node of the second when the two bear the same label, the multiplication of `MergeAR`; a
string denotes the product of its symbols' primitives there. The operation has the empty graph
as unit and is associative, and it preserves the No-Crossing Constraint and, over OCP-clean
primitives, the OCP; these are the theorems of `Autosegmental/MergeAR.lean`.

Because only the seam merges, a primitive that violates the OCP keeps its violation. The
authors use this for Kishambaa, where a high-toned noun with a downstepped second high contrasts
with one whose high spreads over both morae: a primitive `H H` with only its second `H` linked
derives the downstep, and concatenating then collapsing every run, the method they set aside,
would derive the spread instead.

## Main statements

* `mul_G₁_G₂`: Example 3, the merge of `b` with `b` at the seam (Figure 4).
* `realize_γ₁_γ₂`, `realize_γ₁_γ₁`: the Kishambaa graphs of Figure 12.
* `collapse_prod_γ₁_γ₂`, `realize_γ₁_γ₂_ne_collapse`: collapsing after concatenation derives the
  spread graph for the downstep form, so it does not agree with merging concatenation once a
  primitive violates the OCP.

## References

* [jardine-heinz-2015]
-/

@[expose] public section

namespace JardineHeinz2015

open Autosegmental MergeAR

/-! ### Example 1: concatenation merges the seam -/

/-- The melody symbols `a` and `b` of Example 1. -/
inductive Mel
  | a
  | b
  deriving DecidableEq

/-- Example 1's labels: melody symbols over `true`, and the one timing symbol `c` over
`false`. -/
abbrev Γ := TwoTier Mel Unit

/-- `G₁` of Figure 2: the melody `a b`, both associated to one timing node. -/
abbrev G₁ : AR Γ := AR.primitive [.a, .b] ()

/-- `G₂` of Figure 2: `b` over a timing node. -/
abbrev G₂ : AR Γ := AR.primitive [.b] ()

/-- The graph of Figure 4: `a` then the merged `b`, over two timing nodes, with the merged `b`
associated to both. -/
abbrev fig4 : AR Γ := AR.ofWords [.a, .b] [(), ()] fun p q ↦ q = 0 ∨ p = 1

/-- Concatenating `G₁` and `G₂` merges their `b` nodes (Example 3, Figure 4). -/
theorem mul_G₁_G₂ : toAR (ofAR G₁ * ofAR G₂ : MergeAR true Γ) = fig4 := by decide

/-! ### Kishambaa: an OCP-violating primitive -/

open Tone Tone.TRN

/-- The mora, the tone-bearing unit. -/
abbrev μ : TBUKind := .mora

/-- The symbols of the Kishambaa alphabet (Figure 13). -/
inductive Sym
  | γ₁
  | γ₂
  deriving DecidableEq

/-- `γ₁` is a high-toned mora; `γ₂` is a mora carrying a high preceded by a floating high. -/
def Sym.melody : Sym → List TRN
  | .γ₁ => [H]
  | .γ₂ => [H, H]

/-- The lines of a symbol's primitive: `γ₁`'s high is linked, and only the second high of
`γ₂`. -/
def Sym.lines : Sym → ℕ → ℕ → Prop
  | .γ₁ => fun _ _ ↦ True
  | .γ₂ => fun p _ ↦ p = 1

instance : ∀ s : Sym, DecidableRel s.lines
  | .γ₁ => fun _ _ ↦ inferInstanceAs (Decidable True)
  | .γ₂ => fun p _ ↦ inferInstanceAs (Decidable (p = 1))

/-- The primitives of Figure 13. -/
def g (s : Sym) : AR (TwoTier TRN TBUKind) := AR.ofWords s.melody [μ] (s.lines)

/-- The realization of a string by merging concatenation, the product of its symbols'
primitives (Definition 5). -/
def realize (w : List Sym) : MergeAR true (TwoTier TRN TBUKind) := (w.map fun s ↦ ofAR (g s)).prod

theorem not_isCleanAt_g_γ₂ : ¬ (g .γ₂).IsCleanAt true := by
  simp [AR.IsCleanAt, g, Sym.melody]

/-- Figure 12a, 'snake': one high spread over two morae. -/
abbrev snake : AR (TwoTier TRN TBUKind) := AR.ofWords [H] [μ, μ] fun _ _ ↦ True

/-- Figure 12b, 'sheep': a high and a downstepped high, one per mora. -/
abbrev sheep : AR (TwoTier TRN TBUKind) := AR.ofWords [H, H] [μ, μ] fun p q ↦ p = q

/-- `γ₁γ₁` derives the spread high of Figure 12a. -/
theorem realize_γ₁_γ₁ : toAR (realize [.γ₁, .γ₁]) = snake := by decide

/-- `γ₁γ₂` derives the high and downstepped high of Figure 12b: the floating high of `γ₂`
merges with the high of `γ₁`, and the linked high stays distinct. -/
theorem realize_γ₁_γ₂ : toAR (realize [.γ₁, .γ₂]) = sheep := by decide

/-- Collapsing every run after concatenating merges all three highs of `γ₁γ₂`, deriving the
spread graph of Figure 12a instead. -/
theorem collapse_prod_γ₁_γ₂ : ([Sym.γ₁, .γ₂].map g).prod.collapse true = snake := by decide

theorem realize_γ₁_γ₂_ne_collapse :
    toAR (realize [.γ₁, .γ₂]) ≠ ([Sym.γ₁, .γ₂].map g).prod.collapse true := by
  rw [realize_γ₁_γ₂, collapse_prod_γ₁_γ₂]
  decide

end JardineHeinz2015
