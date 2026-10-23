/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# Phonological transformations as correspondence relations

Jardine's dissertation (Ch. 7) models a phonological process as a relation between input and output
strings, presented by a set of correspondence graphs and carved out by banned-subgraph
constraints, which is what makes the relation local. A correspondence graph is a two-tier
representation with the input over `true`, the output over `false`, and the correspondence arcs
as its links; precedence is the order on each tier. A banned subgraph is a factor
(`AR.FactorEmbeds`), so an output-only markedness constraint is a factor with an empty input
tier and no links.

## Main definitions

* `Rep`: a correspondence representation, the input word over `true` and the output word over
  `false`.
* `relRep`: the string relation of a set of correspondence graphs (the dissertation's
  Definition 25).
* `IsLocalRep`: a relation presented by a finite banned-subgraph grammar.

## References

* [jardine-2016b]
-/

@[expose] public section

namespace Autosegmental
namespace Correspondence

universe u
variable {S T : Type u}

/-- A correspondence representation is a two-tier representation with the input over `true`
and the output over `false`. -/
abbrev Rep (S T : Type u) := AR (TwoTier S T)

/-- **R(CG)** ([jardine-2016b] Def. 25): the string relation realized by a set of
correspondence representations. -/
def relRep (CG : Rep S T → Prop) (w : List S) (v : List T) : Prop :=
  ∃ G : Rep S T, CG G ∧ G.word true = w ∧ G.word false = v

theorem relRep_mono {CG CG' : Rep S T → Prop} (h : ∀ G, CG G → CG' G) {w v} :
    relRep CG w v → relRep CG' w v := by
  rintro ⟨G, hG, hi, ho⟩
  exact ⟨G, h G hG, hi, ho⟩

/-- A string relation is **local** when it is realized by the correspondence representations
free of a finite banned-subgraph grammar, Jardine's `CG(φ)`. -/
def IsLocalRep (R : List S → List T → Prop) : Prop :=
  ∃ φ : List (Rep S T), R = relRep (·.Free φ)

end Correspondence
end Autosegmental
