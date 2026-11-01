module

public import Linglib.Semantics.Modality.Background
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Attitudes.Preference.Conditional
public import Linglib.Semantics.Presupposition.Strawson

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

/-! ### Strawson monotonicity

Von Fintel calls *glad* upward entailing; its presupposition that the domain contains non-`p`
worlds can fail at a larger argument, so `isStrawsonUE_glad` is the Strawson form he states for
*want*. With suitable ordering sources *sorry* also covers *regret*, *amazed* and *surprised*. -/

namespace Desire.BestWorlds

open Modality Presupposition Trivalent

variable {W : Type*} (dox base : W → Set W) (g : W → Set (W → Prop))

/-- *Want* is Strawson upward entailing in its complement ([von-fintel-1999], §3.2). -/
theorem isStrawsonUE_want : IsStrawsonUE (want base g) :=
  .of_monotone (a := fun p w ↦ Want (g w) (base w) p) (fun _ _ h _ hw ↦ hw.trans h)
    fun _ _ h ↦ by simp_all

theorem isStrawsonUE_glad : IsStrawsonUE (glad dox base g) :=
  .of_monotone (a := fun p w ↦ Want (g w) (base w) p) (fun _ _ h _ hw ↦ hw.trans h)
    fun _ _ h ↦ by simp_all [glad]

/-- *Glad* is not Strawson downward entailing ([von-fintel-1999], §3.3). -/
theorem not_isStrawsonDE_glad :
    ¬ IsStrawsonDE (glad (fun _ : Fin 3 ↦ {0}) (fun _ ↦ .univ) (fun _ ↦ {(· = 1)})) := by
  have hb : (premisePreorder {(· = 1)}).minimals (Set.univ : Set (Fin 3)) = {1} := by
    rw [Preorder.minimals_ofCriteria_eq ⟨1, Set.mem_univ _, by simp⟩]
    ext
    simp
  intro h
  have := h (p := {0}) (q := {0, 1}) (by simp) 0
  simp [glad, Want, IsContingent, hb] at this
  exact this ⟨2, by simp⟩ ⟨1, by simp⟩

/-- *Sorry* is Strawson anti-additive in its complement, since wanting a disjunction false is
wanting each disjunct false. -/
theorem isStrawsonAntiAdditive_regret : IsStrawsonAntiAdditive (regret dox base g) :=
  .of_isAntiAdditive (a := fun p w ↦ Want (g w) (base w) pᶜ)
    (fun p q ↦ funext fun w ↦ propext <| by
      show Want (g w) (base w) (p ∪ q)ᶜ ↔ Want (g w) (base w) pᶜ ∧ Want (g w) (base w) qᶜ
      rw [Set.compl_union]
      exact want_inter_iff)
    fun _ _ h ↦ by simp_all [regret]

theorem isStrawsonDE_regret : IsStrawsonDE (regret dox base g) :=
  (isStrawsonAntiAdditive_regret dox base g).isStrawsonDE

/-- *Sorry that Robin bought a car* does not classically entail *sorry that Robin bought a Honda
Civic* ([von-fintel-1999]'s (30)). -/
theorem not_antitone_posSupport_regret :
    ¬ Antitone fun p : Set Bool ↦
      posSupport (regret (fun _ ↦ {true}) (fun _ ↦ .univ) (fun _ ↦ {(· = false)}) p) := by
  have hb : (premisePreorder {(· = false)}).minimals ({false, true} : Set Bool) = {false} := by
    rw [Preorder.minimals_ofCriteria_eq ⟨false, by simp, by simp⟩]
    ext
    simp
  exact not_antitone_posSupport (p := ∅) (q := {true}) (w := true) (Set.empty_subset _)
    (by simp [regret, Want, IsContingent, hb]) (by simp [regret])

/-- *Sorry that Robin bought a Civic* does not Strawson-entail *sorry that Robin bought a Civic or
a Golf*, defined and false when the subject prefers the Golf. The subject believes world `0` and
prefers world `1`. -/
theorem not_isStrawsonUE_regret :
    ¬ IsStrawsonUE (regret (fun _ : Fin 3 ↦ {0}) (fun _ ↦ .univ) (fun _ ↦ {(· = 1)})) := by
  have hb : (premisePreorder {(· = 1)}).minimals (Set.univ : Set (Fin 3)) = {1} := by
    rw [Preorder.minimals_ofCriteria_eq ⟨1, Set.mem_univ _, by simp⟩]
    ext
    simp
  exact not_isStrawsonUE (p := {0}) (q := {0, 1}) (w := 0) (by simp)
    (by simp [regret, Want, IsContingent, hb])
    (by simp [regret, Want, IsContingent, hb]; exact ⟨2, by simp⟩)

end Desire.BestWorlds
