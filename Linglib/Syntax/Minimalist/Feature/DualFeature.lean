module

public import Linglib.Syntax.Minimalist.Feature.Basic

/-!
# Coordination resolution over a dual-feature system

This file defines the resolution of features on a coordinate structure in a dual-feature
system ([adamson-anagnostopoulou-2025], after [smith-2015]), whose application in the paper is
to gender. A nominal's bundle has an interpretable feature set, sent to LF, and an
uninterpretable one, sent to PF. Resolution percolates the interpretable sets of the conjuncts
to the coordination and converts them by intersection, so that the coordination bears exactly
the features every conjunct has. Uninterpretable sets are not intersected but realized set by
set, and their realization converges only when every set receives the same exponent; at
Transfer the redundancy rule sends a nominal's interpretable features to PF when it has no
uninterpretable ones. The features a nominal contributes are a node of a feature geometry with
the nodes it depends on, so in a rooted geometry every two conjuncts share the root and resolution
needs no default.

## Main definitions

* `Minimalist.DualFeature.Bundle`: the interpretable and the uninterpretable features of a
  nominal, built by `Minimalist.DualFeature.Bundle.single` from one feature and its
  interpretability and sent to PF by `Minimalist.DualFeature.Bundle.toPF`.
* `Minimalist.DualFeature.resolve`: the intersection of two conjuncts' interpretable features.
* `Minimalist.DualFeature.realizeAll`: the exponent a family of feature sets all receive.

## References

* [adamson-anagnostopoulou-2025]
* [smith-2015]
-/

@[expose] public section

namespace Minimalist.DualFeature

variable {F E : Type*}

/-- The features of a nominal in a dual-feature system, the interpretable ones sent to LF and
the uninterpretable ones sent to PF. -/
structure Bundle (F : Type*) where
  /-- The interpretable features. -/
  interp : Finset F
  /-- The uninterpretable features. -/
  uninterp : Finset F
  deriving DecidableEq

namespace Bundle

/-- A bundle of interpretable features only. -/
def ofInterp (s : Finset F) : Bundle F := ⟨s, ∅⟩

/-- A bundle of uninterpretable features only. -/
def ofUninterp (s : Finset F) : Bundle F := ⟨∅, s⟩

/-- A single feature with the interpretability its host carries. -/
def single (v : F) : Interpretability → Bundle F
  | .interpretable => ⟨{v}, ∅⟩
  | .uninterpretable => ⟨∅, {v}⟩

/-- The features of two stacked layers. -/
instance [DecidableEq F] : Union (Bundle F) :=
  ⟨fun a b => ⟨a.interp ∪ b.interp, a.uninterp ∪ b.uninterp⟩⟩

@[simp] theorem interp_union [DecidableEq F] (a b : Bundle F) :
    (a ∪ b).interp = a.interp ∪ b.interp := rfl
@[simp] theorem uninterp_union [DecidableEq F] (a b : Bundle F) :
    (a ∪ b).uninterp = a.uninterp ∪ b.uninterp := rfl
@[simp] theorem interp_ofInterp (s : Finset F) : (ofInterp s).interp = s := rfl
@[simp] theorem uninterp_ofInterp (s : Finset F) : (ofInterp s).uninterp = ∅ := rfl
@[simp] theorem interp_ofUninterp (s : Finset F) : (ofUninterp s).interp = ∅ := rfl
@[simp] theorem uninterp_ofUninterp (s : Finset F) : (ofUninterp s).uninterp = s := rfl

/-- The features a nominal sends to PF at Transfer, its interpretable ones when it has no
uninterpretable ones, the redundancy rule. -/
def toPF [DecidableEq F] (b : Bundle F) : Finset F :=
  if b.uninterp = ∅ then b.interp else b.uninterp

@[simp] theorem toPF_ofInterp [DecidableEq F] (s : Finset F) : (ofInterp s).toPF = s := by
  simp [toPF]

end Bundle

/-- Resolution of two conjuncts, the interpretable features that percolate from both, converted
by intersection. -/
def resolve [DecidableEq F] (a b : Bundle F) : Finset F := a.interp ∩ b.interp

theorem resolve_comm [DecidableEq F] (a b : Bundle F) : resolve a b = resolve b a :=
  Finset.inter_comm _ _

/-- Single-feature conjuncts resolve to their feature exactly when both are interpretable and
match. -/
@[simp] theorem resolve_single [DecidableEq F] (x y : F) (i j : Interpretability) :
    resolve (.single x i) (.single y j) =
      if i = .interpretable ∧ j = .interpretable ∧ x = y then {x} else ∅ := by
  cases i <;> cases j <;> by_cases h : x = y <;> simp [resolve, Bundle.single, h]

/-- Realization of a family of feature sets, the exponent they all receive. -/
def realizeAll [DecidableEq E] (realize : Finset F → Option E) : List (Finset F) → Option E
  | [] => none
  | s :: ss => if ∀ t ∈ ss, realize t = realize s then realize s else none

@[simp] theorem realizeAll_singleton [DecidableEq E] (realize : Finset F → Option E)
    (s : Finset F) : realizeAll realize [s] = realize s := by
  simp [realizeAll]

end Minimalist.DualFeature
