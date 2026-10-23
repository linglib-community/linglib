module

public import Linglib.Semantics.Modality.Background
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Attitudes.Preference.Conditional

/-!
# Best-worlds desire semantics

On the best-worlds semantics, *a wants p* when the best worlds of a domain, ranked by the
subject's preferences as a Kratzer ordering source, are `p`-worlds (`Want`). Von Fintel takes the
domain to be the worlds compatible with what the subject believes whatever she chooses to do,
and gives *want*, *glad* and *sorry* one family of entries: *want* presupposes that its domain
contains both `p`-worlds and non-`p`-worlds, *glad* adds that the subject believes `p` and that
the domain contains her belief worlds, and *sorry* has the presupposition of *glad* and the
assertion of wanting `p` false.

## Main definitions

* `Desire.BestWorlds.Want`: the best worlds of a domain under an ordering source are `p`-worlds.
* `Desire.BestWorlds.want`, `Desire.BestWorlds.glad`, `Desire.BestWorlds.regret`: von Fintel's
  entries as trivalent propositions, with world-indexed belief worlds, domain and ordering source.

## Main results

* `Desire.BestWorlds.Want.not_compl`: on a finite frame `p` and `¬p` are not both wanted.
* `Desire.BestWorlds.Want.mono`: the semantics is upward monotone in `p`, the doxastic-closure
  problem Villalta raises.
* `Desire.BestWorlds.want_inter_iff`: wanting a conjunction is wanting each conjunct, which makes
  *sorry* anti-additive in its complement.
* `Desire.BestWorlds.support_regret`: *sorry* has the presupposition of *glad*.
* `Desire.BestWorlds.ssubset_of_glad_ne_zero`: the presupposition of *glad* makes the domain
  properly contain the belief worlds.

## Implementation notes

The domain is a parameter. Von Fintel's is the set DOX* of worlds compatible with what the subject
believes however she acts, a superset of her belief worlds; Phillips-Brown's rendering takes the
belief worlds themselves. Von Fintel's condition that the domain of *want* be DOX* constrains the
domain rather than the complement and is left to the caller, and his presupposition that `p` be
contingent in the domain is Heim's (`Desire.IsContingent`). The subject is fixed, so the domain
and the ordering source are indexed by worlds alone. `glad` is his best-worlds entry (50), which
he replaces by a comparison of the belief worlds with the non-`p` worlds, (52), after the Honda
Civic case; the replacement is `VonFintel1999.gladBetter`.

## References

* [von-fintel-1999]
* [heim-1992]
* [kratzer-1981]
* [villalta-2008]
* [phillips-brown-2025]
-/

@[expose] public section

namespace Desire.BestWorlds

open Modality

variable {W : Type*}

/-! ### Wanting over a domain -/

section Want

/-- `Want A dom p` holds when every best world of `dom` under the ordering source `A` is a
`p`-world. -/
def Want (A : Set (W → Prop)) (dom p : Set W) : Prop := (premisePreorder A).minimals dom ⊆ p

variable {A : Set (W → Prop)} {dom p q : Set W}

theorem want_iff : Want A dom p ↔ ∀ w ∈ dom, (∀ z ∈ dom, (z ≤[A] w) → (w ≤[A] z)) → w ∈ p :=
  ⟨fun h _ hw hb ↦ h ⟨hw, hb⟩, fun h w hw ↦ h w hw.1 hw.2⟩

instance [Fintype W] [DecidableRel (premisePreorder A).le] [DecidablePred (· ∈ dom)]
    [DecidablePred (· ∈ p)] : Decidable (Want A dom p) :=
  decidable_of_iff _ want_iff.symm

/-- Wanting a conjunction is wanting each conjunct. -/
theorem want_inter_iff : Want A dom (p ∩ q) ↔ Want A dom p ∧ Want A dom q :=
  Set.subset_inter_iff

theorem Want.mono_on (hpq : ∀ w ∈ dom, w ∈ p → w ∈ q) (h : Want A dom p) : Want A dom q :=
  fun w hw ↦ hpq w hw.1 (h hw)

theorem Want.mono (hpq : p ⊆ q) (h : Want A dom p) : Want A dom q := h.trans hpq

theorem Want.not_compl [Finite W] (h : dom.Nonempty) (hp : Want A dom p) : ¬ Want A dom pᶜ :=
  fun hnp ↦
    let ⟨_, hw⟩ := Preorder.minimals_nonempty (premisePreorder A) h
    hnp hw (hp hw)

end Want

/-! ### *Want*, *glad* and *sorry* -/

section Entries

variable (dox base : W → Set W) (g : W → Set (W → Prop)) (p : Set W)

open Classical in
/-- *a wants p* presupposes that the domain `base` contains both `p`-worlds and non-`p`-worlds
and asserts that its best worlds under the ordering source `g` are `p`-worlds
([von-fintel-1999]'s (45)). -/
noncomputable def want : W → SignType :=
  {w | IsContingent (base w) p}.indicator fun w ↦ SignType.ofProp (Want (g w) (base w) p)

/-- *a is glad that p* presupposes, besides the presupposition of *want*, that `a` believes `p`
and that the domain contains her belief worlds, and asserts that `a` wants `p`
([von-fintel-1999]'s (50)). -/
noncomputable def glad : W → SignType :=
  {w | dox w ⊆ p ∧ dox w ⊆ base w}.indicator (want base g p)

/-- *a regrets that p* has the presupposition of *glad* and asserts that `a` wants `p` false
([von-fintel-1999]'s (53)), restricting *want* `¬p` as *glad* restricts *want* `p`. -/
noncomputable def regret : W → SignType :=
  {w | dox w ⊆ p ∧ dox w ⊆ base w}.indicator (want base g pᶜ)

variable {dox base g p} {w : W}

@[simp] theorem want_eq_zero_iff : want base g p w = 0 ↔ ¬ IsContingent (base w) p := by
  simp [want]

@[simp] theorem want_eq_one_iff :
    want base g p w = 1 ↔ IsContingent (base w) p ∧ Want (g w) (base w) p := by
  simp [want]

@[simp] theorem want_eq_neg_one_iff :
    want base g p w = -1 ↔ IsContingent (base w) p ∧ ¬ Want (g w) (base w) p := by
  simp [want]

private theorem isContingent_compl {D : Set W} : IsContingent D pᶜ ↔ IsContingent D p := by
  rw [IsContingent, IsContingent, Set.sdiff_compl, ← Set.sdiff_eq, and_comm]

variable (dox base g p) in
/-- *Sorry* has the presupposition of *glad*, since *want* presupposes as much of `¬p` as of
`p`. -/
theorem support_regret :
    Function.support (regret dox base g p) = Function.support (glad dox base g p) := by
  ext; simp [regret, glad, isContingent_compl]

/-- If *glad* is defined, its domain properly contains the belief worlds ([von-fintel-1999], p.
123). -/
theorem ssubset_of_glad_ne_zero (h : glad dox base g p w ≠ 0) : dox w ⊂ base w := by
  obtain ⟨hp, hb, -, v, hv⟩ : dox w ⊆ p ∧ dox w ⊆ base w ∧ IsContingent (base w) p := by
    simpa [glad] using h
  exact hb.ssubset_of_not_superset fun h ↦ hv.2 (hp (h hv.1))

end Entries

end Desire.BestWorlds
