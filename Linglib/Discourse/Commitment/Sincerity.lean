module

public import Linglib.Discourse.Commitment.Basic
public import Linglib.Semantics.Attitudes.Preference.Structure

/-!
# Sincerity

A public commitment is sincere when the committer privately holds what it is committed to under
the attitude of its force: belief for a doxastic commitment, preference for a preferential one.
Sincerity is a relation between a commitment state and the participants' attitudes,
`Force → A → W → Set (Set W)`, the propositions each participant holds under each attitude at
each world. [condoravdi-lauer-2012]'s sincerity condition on a directive use of an imperative is
the preferential case, with the effective preferences `Desire.Preferential.Want` as the attitude;
through the consistency of the effective preference structure it is what makes successive
imperatives consistent (`Studies/CondoravdiLauer2012.lean`) and what excludes a force-augmenting
particle from contexts in which the preference it expresses is unrealizable
(`Studies/Deo2025.lean`). The doxastic case is the Sincerity of [van-der-leer-2026]'s frames
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

/-- `K` is sincere at `w` relative to the attitudes `M`: the committer of every undertaken
commitment holds its content at `w` under the attitude `M` assigns to its force. -/
def Sincere (M : Force → A → W → Set (Set W)) (K : State A W) (w : W) : Prop :=
  ∀ c ∈ K, c.stance = .commit → c.content ∈ M c.force c.committer w

/-- Effective preference as an attitude ([condoravdi-lauer-2012]): a preferential commitment is
held when it is an effective preference, and a doxastic commitment is unconstrained. -/
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
