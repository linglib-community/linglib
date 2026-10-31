module

public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Interpretable and uninterpretable features

This file defines interpretability and the dual-feature system of [adamson-anagnostopoulou-2025],
together with the operations of that system on coordinations.

A feature is interpretable if it is read at LF and uninterpretable otherwise ([chomsky-1995]). In
a dual-feature system ([smith-2015]) a nominal bears two sets of features of one kind: its
interpretable features (iFs), which Transfer sends to LF, and its uninterpretable features (uFs),
which Transfer sends to PF. A nominal with no uFs sends its iFs to PF as well, by the redundancy
rule.

In a coordination, one feature set of each conjunct percolates to &P, either its iFs or its uFs.
Conversion intersects the percolated iF sets, so that &P bears the iFs that every conjunct bears.
Percolated uF sets are not intersected. PF realizes each of them, and realization succeeds only if
every set receives the same exponent.

## Main definitions

* `Minimalist.Interpretability`: interpretable or uninterpretable.
* `Minimalist.DualFeature.Bundle`: a set of iFs and a set of uFs.
* `Minimalist.DualFeature.Bundle.toPF`: the features a bundle sends to PF.
* `Minimalist.DualFeature.resolve`: the iFs two conjuncts share.
* `Minimalist.DualFeature.realizeAll`: the exponent of a family of feature sets.

## Implementation notes

A bundle is a function on `Interpretability`, so bundles are ordered and combined pointwise. The
features of a nominal built from two layers are the join `⊔` of the layers' bundles.

## References

* [chomsky-1995]
* [smith-2015]
* [adamson-anagnostopoulou-2025]
-/

@[expose] public section

namespace Minimalist

/-- Whether a feature is read at LF. -/
inductive Interpretability where
  | interpretable
  | uninterpretable
  deriving Repr, DecidableEq, Fintype

namespace DualFeature

variable {F E : Type*}

/-- The features of a nominal: a set of iFs and a set of uFs. -/
abbrev Bundle (F : Type*) := Interpretability → Finset F

namespace Bundle

/-- The bundle with the features `s` at `i` and none at the other interpretability. -/
def single (i : Interpretability) (s : Finset F) : Bundle F := Function.update ⊥ i s

@[simp] theorem single_self (i : Interpretability) (s : Finset F) : single i s i = s :=
  Function.update_self ..

@[simp] theorem single_of_ne {i j : Interpretability} (h : j ≠ i) (s : Finset F) :
    single i s j = ∅ :=
  Function.update_of_ne h ..

/-- The features a bundle sends to PF: its uFs, or its iFs if it has no uFs. The second case is
the redundancy rule, (13) of [adamson-anagnostopoulou-2025]. -/
def toPF [DecidableEq F] (b : Bundle F) : Finset F :=
  if b .uninterpretable = ∅ then b .interpretable else b .uninterpretable

@[simp] theorem toPF_single_interpretable [DecidableEq F] (s : Finset F) :
    (single .interpretable s).toPF = s := by
  simp [toPF]

end Bundle

section Resolve

variable [DecidableEq F]

/-- The iFs that two conjuncts both bear, the output of conversion, (29) of
[adamson-anagnostopoulou-2025]. -/
def resolve (a b : Bundle F) : Finset F := a .interpretable ∩ b .interpretable

@[simp] theorem mem_resolve {a b : Bundle F} {x : F} :
    x ∈ resolve a b ↔ x ∈ a .interpretable ∧ x ∈ b .interpretable :=
  Finset.mem_inter

theorem resolve_comm (a b : Bundle F) : resolve a b = resolve b a :=
  Finset.inter_comm _ _

@[simp] theorem resolve_single (i j : Interpretability) (s t : Finset F) :
    resolve (.single i s) (.single j t) =
      if i = .interpretable ∧ j = .interpretable then s ∩ t else ∅ := by
  cases i <;> cases j <;> simp [resolve]

end Resolve

/-- The exponent that every set in `l` receives, if `l` is nonempty and there is one. PF realizes
each percolated set separately (p. 25 of [adamson-anagnostopoulou-2025]). -/
def realizeAll [DecidableEq E] (realize : Finset F → Option E) : List (Finset F) → Option E
  | [] => none
  | s :: ss => if ∀ t ∈ ss, realize t = realize s then realize s else none

theorem realizeAll_eq_some_iff [DecidableEq E] {realize : Finset F → Option E}
    {l : List (Finset F)} {e : E} :
    realizeAll realize l = some e ↔ l ≠ [] ∧ ∀ s ∈ l, realize s = some e := by
  cases l with
  | nil => simp [realizeAll]
  | cons s ss =>
    simp only [realizeAll, ne_eq, reduceCtorEq, not_false_eq_true, List.mem_cons,
      forall_eq_or_imp, true_and]
    split_ifs with h
    · exact ⟨fun hs ↦ ⟨hs, fun t ht ↦ (h t ht).trans hs⟩, And.left⟩
    · exact iff_of_false (by simp) fun ⟨hs, ht⟩ ↦ h fun t h' ↦ (ht t h').trans hs.symm

@[simp] theorem realizeAll_singleton [DecidableEq E] (realize : Finset F → Option E)
    (s : Finset F) : realizeAll realize [s] = realize s := by
  simp [realizeAll]

end DualFeature

end Minimalist
