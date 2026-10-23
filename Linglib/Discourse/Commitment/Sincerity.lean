module

public import Linglib.Discourse.Commitment.Basic
public import Linglib.Semantics.Attitudes.Preference.Structure

/-!
# Sincerity

A public commitment is sincere when the committer privately holds what it is committed to under
the attitude of its force, belief for a doxastic commitment and preference for a preferential one.
Sincerity relates a commitment state to the participants' attitudes, given as the propositions
each participant holds under each attitude at each world. Condoravdi and Lauer's sincerity
condition on a directive use of an imperative is the preferential case, with effective preferences
(`Desire.Preferential.Want`) as the attitude. Through the consistency of the effective preference
structure it makes successive imperatives consistent (`Studies/CondoravdiLauer2012.lean`), and it
excludes a force-augmenting particle from contexts in which the preference it expresses is
unrealizable (`Studies/Deo2025.lean`). The doxastic case is the Sincerity of van der Leer's frames
(`Commitment.Frame.sincere_iff_forall_sincere_toState`).

## Main definitions

* `Commitment.Sincere M K w`: every undertaken commitment in `K` is held at `w` under `M`.
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

variable {A W : Type*}

/-- A commitment state is sincere at `w` relative to the attitudes `M` when the committer of every
undertaken commitment holds its content at `w` under the attitude `M` assigns to its force. -/
def Sincere (M : Force → A → W → Set (Set W)) (K : State A W) (w : W) : Prop :=
  ∀ c ∈ K, c.stance = .commit → c.content ∈ M c.force c.committer w

/-- The attitudes of [condoravdi-lauer-2012]'s sincerity condition hold a preferential commitment
when its content is an effective preference and leave doxastic commitments unconstrained. -/
def effectivePreference (P : A → W → PreferenceStructure W) : Force → A → W → Set (Set W)
  | .doxastic => ⊤
  | .preferential => fun a w ↦ {p | Want P a p w}

variable {M : Force → A → W → Set (Set W)} {K L : State A W} {w : W}

theorem Sincere.mono (hL : Sincere M L w) (h : K ⊆ L) : Sincere M K w := fun c hc ↦ hL c (h hc)

theorem Sincere.mem (hs : Sincere M K w) {a : A} {p : Set W} {f : Force} {s : Source}
    (h : commit a p f s ∈ K) : p ∈ M f a w :=
  hs _ h rfl

theorem Sincere.want {P : A → W → PreferenceStructure W} (hs : Sincere (effectivePreference P) K w)
    {a : A} {p : Set W} {s : Source} (h : commit a p .preferential s ∈ K) : Want P a p w :=
  hs.mem h

end Commitment
