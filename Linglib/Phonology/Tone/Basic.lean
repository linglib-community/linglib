/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# Tonal root nodes and subtonal features

Tone is paradigmatic: a **tonal root node** (TRN) bundles the two subtonal features
`[±upper]` (which register half) and `[±raised]` (which target within it) of [yip-1980] and
[pulleyblank-1986], each possibly unspecified, and links to a tone-bearing unit. Following
[lionnet-2022], both are paradigmatic targets. `[±upper]` is Yip's and Pulleyblank's register
feature, a choice of register half; the register features `h` and `l` of [snider-1999], which
shift the register relative to the preceding one, are syntagmatic and a different object,
`Tone.RegisterFeature` in `Tone/Register.lean`. The register-only systems of [lionnet-2025]
have register features and no TRN.

## Main definitions

* `Subtonal`, `TRN` — the two feature dimensions and the root node; `TRN.bundleEquiv`
  identifies a root node with its feature bundle `Subtonal → Option Bool`.
* `TRN.H`, `TRN.M`, `TRN.L`, `TRN.superHigh` — the four full specifications;
  `TRN.empty` — the unspecified node.
* `TRN.assimilate`, `TRN.merge`, `TRN.dock` — the feature operations, through the bundle.
* `TBUKind` — the tone-bearing unit.

## References

* [yip-1980]
* [pulleyblank-1986]
* [lionnet-2022]
* [snider-1999]
* [lionnet-2025]
* [goldsmith-1976]
-/

@[expose] public section

namespace Tone

/-- The two subtonal feature dimensions ([lionnet-2022] ex. 51, after [yip-1980],
[pulleyblank-1986]): `upper`, which register half; `raised`, which target within it. A
value is `some true` (`+`), `some false` (`-`), or `none` (unspecified). -/
inductive Subtonal where
  | upper
  | raised
  deriving DecidableEq, Repr, Inhabited

/-- A **tonal root node**: a `[±upper]` and a `[±raised]` value, each possibly unspecified.
A structure rather than the bundle `Subtonal → Option Bool`, so that `DecidableEq` derives
and literals reduce; `TRN.bundleEquiv` is the bundle view. -/
structure TRN where
  upper : Option Bool
  raised : Option Bool
  deriving DecidableEq, Repr, Inhabited

namespace TRN

/-- The fully unspecified node. -/
@[match_pattern] def empty : TRN := ⟨none, none⟩

/-- High, `[+upper, -raised]` ([lionnet-2022] ex. 51). -/
@[match_pattern] def H : TRN := ⟨some true, some false⟩

/-- Mid, `[-upper, +raised]` ([lionnet-2022] ex. 51). -/
@[match_pattern] def M : TRN := ⟨some false, some true⟩

/-- Low, `[-upper, -raised]` ([lionnet-2022] ex. 51). -/
@[match_pattern] def L : TRN := ⟨some false, some false⟩

/-- The fourth specification `[+upper, +raised]`: the gap of Laal's three-tone system
([lionnet-2022] ex. 51). -/
@[match_pattern] def superHigh : TRN := ⟨some true, some true⟩

/-- The feature bundle of a node. -/
def toBundle (t : TRN) : Subtonal → Option Bool
  | .upper => t.upper
  | .raised => t.raised

/-- The node of a feature bundle. -/
def ofBundle (b : Subtonal → Option Bool) : TRN := ⟨b .upper, b .raised⟩

@[simp] theorem toBundle_upper (t : TRN) : t.toBundle .upper = t.upper := rfl

@[simp] theorem toBundle_raised (t : TRN) : t.toBundle .raised = t.raised := rfl

@[simp] theorem ofBundle_toBundle (t : TRN) : ofBundle t.toBundle = t := rfl

@[simp] theorem toBundle_ofBundle (b : Subtonal → Option Bool) : (ofBundle b).toBundle = b := by
  funext f; cases f <;> rfl

/-- A root node is its feature bundle. -/
def bundleEquiv : TRN ≃ (Subtonal → Option Bool) where
  toFun := toBundle
  invFun := ofBundle
  left_inv := ofBundle_toBundle
  right_inv := toBundle_ofBundle

/-- **Subtonal assimilation** at `f`: the target takes its value at `f` from the source,
its other feature untouched. Laal M-lowering ([lionnet-2022] §5.2) is `assimilate .raised`:
a `[-raised]` value spreads onto M, `[-upper, +raised]`, giving L. -/
def assimilate (f : Subtonal) (src tgt : TRN) : TRN :=
  ofBundle (Function.update tgt.toBundle f (src.toBundle f))

/-- **Merger** of two nodes ([lionnet-2022] ex. 53–54): each feature from the left node
where it is specified, else from the right — the fusion of two
associated tones ([goldsmith-1976]); the tier-level merger of a run of identical tones is
`OCP.collapse`. -/
def merge (t₁ t₂ : TRN) : TRN := ofBundle fun f ↦ (t₁.toBundle f).or (t₂.toBundle f)

@[simp] theorem merge_self (t : TRN) : merge t t = t := by
  cases t with | mk u r => cases u <;> cases r <;> rfl

/-- **Docking** of a floating feature ([lionnet-2022] §5.3): a free `[±f]` lands on a node,
overwriting its value at `f`. -/
def dock (f : Subtonal) (v : Bool) (t : TRN) : TRN :=
  ofBundle (Function.update t.toBundle f (some v))

end TRN

/-! ### Tone-bearing units -/

/-- The prosodic unit that carries tone or register: the syllable in most tone languages, the
mora in others, among them Drubea and Numèè, where it bears register features and no tonal root
node ([lionnet-2025]). -/
inductive TBUKind where
  | mora
  | syllable
  deriving DecidableEq, Repr

end Tone
