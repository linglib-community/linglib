module

public import Linglib.Discourse.Commitment.Basic
public import Linglib.Semantics.Attitudes.Preference.Structure

/-!
# Sincerity

A public commitment is sincere when the committer privately holds what it is committed to under
the attitude of its force, belief for a doxastic commitment and preference for a preferential one.
Sincerity relates a commitment state to an attitude for each holder, given as the propositions
the holder holds at each world. Condoravdi and Lauer's sincerity
condition on a directive use of an imperative is the preferential case, with effective preferences
(`Desire.Preferential.Want`) as the attitude. Through the consistency of the effective preference
structure it makes successive imperatives consistent (`Studies/CondoravdiLauer2012.lean`), and it
excludes a force-augmenting particle from contexts in which the preference it expresses is
unrealizable (`Studies/Deo2025.lean`). The doxastic case is the Sincerity of van der Leer's frames
(`Commitment.Frame.sincere_iff_forall_sincere_toState`).

## Main definitions

* `Commitment.Sincere M K w`: every holder in `K` holds at `w` what it is committed to, under the
  attitude `M` gives the holder.
* `Commitment.effectivePreference P`: effective preference as the attitude of preferential
  commitments, with doxastic commitments unconstrained.

## References

* [condoravdi-lauer-2012]
* [deo-2025-bara]
* [van-der-leer-2026]
-/

@[expose] public section

namespace Commitment

open Desire.Preferential

variable {κ A W : Type*}

open scoped SetRel

/-- A commitment state is sincere at `w` relative to the attitudes `M` when every holder holds at
`w`, under its attitude `M k`, each proposition it is committed to. -/
def Sincere (M : κ → W → Set (Set W)) (K : State κ W) (w : W) : Prop :=
  ∀ k p, k ~[K] p → p ∈ M k w

/-- The attitudes of [condoravdi-lauer-2012]'s sincerity condition hold a preferential commitment
when its content is an effective preference and leave doxastic commitments unconstrained. -/
def effectivePreference (P : A → W → PreferenceStructure W) : A × Force → W → Set (Set W)
  | (_, .doxastic) => ⊤
  | (a, .preferential) => fun w ↦ {p | Want P a p w}

variable {M : κ → W → Set (Set W)} {K L : State κ W} {w : W}

theorem Sincere.mono (hL : Sincere M L w) (h : K ⊆ L) : Sincere M K w :=
  fun k p hp ↦ hL k p (h hp)

theorem Sincere.mem (hs : Sincere M K w) {k : κ} {p : Set W} (h : k ~[K] p) : p ∈ M k w :=
  hs k p h

theorem Sincere.want {P : A → W → PreferenceStructure W} {K : State (A × Force) W}
    (hs : Sincere (effectivePreference P) K w) {a : A} {p : Set W} (h : (a, .preferential) ~[K] p) :
    Want P a p w :=
  hs.mem h

end Commitment
