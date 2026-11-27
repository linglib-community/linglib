module

public import Linglib.Discourse.Centering.Center

/-!
# Centering theory: the pronominalization rule

Rule 1 of centering theory requires an utterance that pronominalizes any forward-looking center
of the previous utterance to pronominalize its backward-looking center. Its unconditional form
requires the backward-looking center to be pronominalized whatever else is.

## Main definitions

* `Centering.PronominalizationConstraint`: Rule 1.
* `Centering.CbPronominalized`: the backward-looking center is pronominalized.

## Main results

* `Centering.CbPronominalized.constraint`: the unconditional form implies Rule 1.
* `Centering.CbPronominalized.mono`: counting more forms as pronouns preserves the
  unconditional form.
* `Centering.PronominalizationConstraint.cb_eq_of_pronominalized_eq_singleton`: under
  Rule 1, a forward-looking center of the previous utterance that is the only entity
  pronominalized is the backward-looking center.

## Implementation notes

The forms that count as pronouns are a decidable set of forms. Both forms of the rule are stated
of `cb`, so where several backward-looking centers tie they constrain the first in surface order.

## References

* [grosz-joshi-weinstein-1995]
* [gordon-grosz-gilliom-1993]
* [poesio-stevenson-eugenio-hitzeman-2004]
* [walker-joshi-prince-1998]
-/

@[expose] public section

namespace Centering

variable {E R F : Type*}

/-! ### Rule 1 -/

section Rule1

variable [DecidableEq E] [LinearOrder R] (P : Set F) [DecidablePred (· ∈ P)]
  (prev cur : Utterance E R F)

/-- The backward-looking center of `cur` after `prev`, if any, is realized by a form in `P`: the
unconditional form of Rule 1 of [gordon-grosz-gilliom-1993]. -/
def CbPronominalized : Prop := ∀ c ∈ cb prev cur.cf, c ∈ cur.pronominalized P

instance : Decidable (CbPronominalized P prev cur) :=
  inferInstanceAs (Decidable (∀ c ∈ cb prev cur.cf, c ∈ cur.pronominalized P))

/-- Rule 1 of [grosz-joshi-weinstein-1995], for the pronouns `P`: if `cur` pronominalizes any
forward-looking center of `prev`, it pronominalizes its backward-looking center. -/
def PronominalizationConstraint : Prop :=
  (prev.cf ∩ cur.pronominalized P).Nonempty → CbPronominalized P prev cur

instance : Decidable (PronominalizationConstraint P prev cur) :=
  inferInstanceAs
    (Decidable ((prev.cf ∩ cur.pronominalized P).Nonempty → CbPronominalized P prev cur))

variable {P prev cur}

/-- The unconditional form implies Rule 1. -/
theorem CbPronominalized.constraint (h : CbPronominalized P prev cur) :
    PronominalizationConstraint P prev cur :=
  fun _ ↦ h

/-- Rule 1 holds of an utterance that pronominalizes no forward-looking center of the previous
one. -/
theorem pronominalizationConstraint_of_disjoint (h : Disjoint prev.cf (cur.pronominalized P)) :
    PronominalizationConstraint P prev cur :=
  fun hne ↦ absurd (Finset.disjoint_iff_inter_eq_empty.mp h) hne.ne_empty

/-- Under Rule 1, if the only entity `cur` pronominalizes is a forward-looking center of `prev`,
it is the backward-looking center, as [walker-joshi-prince-1998] note. -/
theorem PronominalizationConstraint.cb_eq_of_pronominalized_eq_singleton {e : E}
    (h : PronominalizationConstraint P prev cur) (he : e ∈ prev.cf)
    (hP : cur.pronominalized P = {e}) : cb prev cur.cf = some e := by
  have hmem : e ∈ cur.pronominalized P := hP ▸ Finset.mem_singleton_self e
  obtain ⟨c, hc⟩ : ∃ c, cb prev cur.cf = some c := Option.ne_none_iff_exists'.1 fun h0 ↦
    Finset.disjoint_left.1 (cb_eq_none_iff.1 h0) he (Utterance.pronominalized_subset_cf hmem)
  have hce := h ⟨e, Finset.mem_inter.2 ⟨he, hmem⟩⟩ c hc
  rw [hP, Finset.mem_singleton] at hce
  rw [hc, hce]

/-- Counting more forms as pronouns preserves the unconditional form of Rule 1. -/
theorem CbPronominalized.mono {Q : Set F} [DecidablePred (· ∈ Q)] (hPQ : P ⊆ Q)
    (h : CbPronominalized P prev cur) : CbPronominalized Q prev cur :=
  fun c hc ↦ Utterance.pronominalized_mono hPQ (h c hc)

end Rule1

end Centering
