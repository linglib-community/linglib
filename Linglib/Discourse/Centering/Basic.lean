module

public import Linglib.Core.Data.List.MinMax
public import Linglib.Core.Order.Argmax
public import Mathlib.Data.Finset.Option

/-!
# Centering theory: centers and the pronominalization rule

This file defines the centers of centering theory. An utterance realizes entities in grammatical
roles, and the roles are ranked. The *forward-looking centers* of an utterance are the entities it
realizes, each ranked by the highest role in which it is realized, and its *preferred center* is
the highest-ranked of them. The *backward-looking centers* of an utterance are the highest-ranked
forward-looking centers of the previous utterance among the entities it realizes. Rule 1 requires
an utterance that pronominalizes any forward-looking center of the previous utterance to
pronominalize its backward-looking center.

## Main definitions

* `Discourse.Centering.Utterance.cf`, `Discourse.Centering.Utterance.rank`: the forward-looking
  centers of an utterance and their ranking.
* `Discourse.Centering.backwardCenters`: the backward-looking centers of a set of entities after
  an utterance, the maximizers of its ranking on the forward-looking centers in the set.
* `Discourse.Centering.cb`: the backward-looking center, the first of them in surface order.
* `Discourse.Centering.Utterance.cp`: the preferred center.
* `Discourse.Centering.Utterance.pronominalized`: the entities an utterance realizes by a form
  in a given set.
* `Discourse.Centering.PronominalizationConstraint`: Rule 1.
* `Discourse.Centering.CbPronominalized`: the backward-looking center is pronominalized.
* `Discourse.Centering.Utterance.indexed`: an utterance with each role refined by surface
  position.

## Main results

* `Discourse.Centering.cb_mem_backwardCenters`: `cb` is one of the backward-looking centers.
* `Discourse.Centering.backwardCenters_eq_toFinset_cb_iff`: it is the only one exactly when
  there is at most one.
* `Discourse.Centering.card_backwardCenters_le_one`: there is at most one when no two entities
  are realized in the same role.
* `Discourse.Centering.backwardCenters_indexed`: after an utterance ranked by role and then by
  surface position, `cb` is the only backward-looking center.
* `Discourse.Centering.cb_cf_self`: the preferred center of an utterance is the
  backward-looking center of its own forward-looking centers.
* `Discourse.Centering.cb_eq_of_cp_eq`: the preferred center of the previous utterance is the
  backward-looking center of any set of entities containing it.
* `Discourse.Centering.CbPronominalized.mono`: counting more forms as pronouns preserves
  `CbPronominalized`.

## Implementation notes

The ranking is a `LinearOrder` on the role type, higher meaning more prominent. Two entities
realized in the same role tie, so the ranking of entities by `Utterance.rank` is a total preorder
and `backwardCenters` can have several elements. `cb` and `Utterance.cp` choose among the
maximizers with `List.argmax`, which takes the first realization in surface order among those in
the highest role.

The backward-looking centers are those of a finite set of entities, the entities that the current
utterance realizes: `cur.cf` when realization is direct, and a larger set when an utterance also
realizes entities that its noun phrases are only associated with.

The forms that count as pronouns for Rule 1 are a decidable set of forms. Rule 1 and
`CbPronominalized` are stated of `cb`, so where several backward-looking centers tie they
constrain the first in surface order.

## References

* [grosz-joshi-weinstein-1995]
* [gordon-grosz-gilliom-1993]
* [poesio-stevenson-eugenio-hitzeman-2004]
-/

@[expose] public section

namespace Discourse.Centering

variable {E R F : Type*}

/-- A noun phrase realizing `entity` in the grammatical role `role` by an expression of form
`form`. -/
structure Realization (E R F : Type*) where
  entity : E
  role : R
  form : F
  deriving Repr, DecidableEq

/-- An utterance as its noun-phrase realizations in surface order. -/
structure Utterance (E R F : Type*) where
  realizations : List (Realization E R F)
  deriving Repr, DecidableEq

namespace Utterance

/-- `e ∈ u` when some realization in `u` is of `e`. -/
instance : Membership E (Utterance E R F) := ⟨fun u e ↦ ∃ r ∈ u.realizations, r.entity = e⟩

theorem mem_iff {u : Utterance E R F} {e : E} : e ∈ u ↔ ∃ r ∈ u.realizations, r.entity = e :=
  Iff.rfl

instance [DecidableEq E] (u : Utterance E R F) (e : E) : Decidable (e ∈ u) :=
  inferInstanceAs (Decidable (∃ r ∈ u.realizations, r.entity = e))

/-! ### Forward-looking centers -/

section Cf

variable [DecidableEq E] (u : Utterance E R F) {e : E}

/-- The forward-looking centers of `u`: the entities it realizes. -/
def cf : Finset E := (u.realizations.map (·.entity)).toFinset

@[simp] theorem mem_cf : e ∈ u.cf ↔ e ∈ u := by simp [cf, mem_iff]

@[simp] theorem cf_mk_nil : (⟨[]⟩ : Utterance E R F).cf = ∅ := rfl

/-- The utterance `u` with the role of each realization refined by its surface position, an
earlier realization outranking a later one in the same role. -/
def indexed : Utterance E (R ×ₗ ℕᵒᵈ) F :=
  ⟨u.realizations.zipIdx.map fun p ↦ ⟨p.1.entity, toLex (p.1.role, OrderDual.toDual p.2), p.1.form⟩⟩

@[simp] theorem cf_indexed : u.indexed.cf = u.cf := by
  have h : u.indexed.realizations.map (·.entity) = u.realizations.map (·.entity) := by
    conv_rhs => rw [← List.zipIdx_map_fst 0 u.realizations]
    simp only [indexed, List.map_map]
    rfl
  exact congrArg List.toFinset h

variable (P : Set F) [DecidablePred (· ∈ P)]

/-- The entities `u` realizes by a form in `P`. -/
def pronominalized : Finset E :=
  ((u.realizations.filter (·.form ∈ P)).map (·.entity)).toFinset

variable {u P}

@[simp] theorem mem_pronominalized :
    e ∈ u.pronominalized P ↔ ∃ r ∈ u.realizations, r.entity = e ∧ r.form ∈ P := by
  simp [pronominalized, and_assoc, and_comm]

theorem pronominalized_subset_cf : u.pronominalized P ⊆ u.cf := fun _ he ↦
  let ⟨r, hr, he, _⟩ := mem_pronominalized.mp he
  u.mem_cf.mpr ⟨r, hr, he⟩

theorem pronominalized_mono {Q : Set F} [DecidablePred (· ∈ Q)] (hPQ : P ⊆ Q) :
    u.pronominalized P ⊆ u.pronominalized Q := fun _ he ↦
  let ⟨r, hr, he, hP⟩ := mem_pronominalized.mp he
  mem_pronominalized.mpr ⟨r, hr, he, hPQ hP⟩

end Cf

/-! ### Ranks -/

section Rank

variable [DecidableEq E] [LinearOrder R] (u : Utterance E R F) {e : E}

/-- The rank of `e` in `u`: the highest role in which `u` realizes it, `⊥` if it does not. -/
def rank (e : E) : WithBot R := ((u.realizations.filter (·.entity = e)).map (·.role)).maximum

theorem role_le_rank {r : Realization E R F} (hr : r ∈ u.realizations) :
    (r.role : WithBot R) ≤ u.rank r.entity :=
  List.le_maximum_of_mem' (List.mem_map_of_mem (List.mem_filter.2 ⟨hr, by simp⟩))

theorem rank_le_iff {b : WithBot R} :
    u.rank e ≤ b ↔ ∀ r ∈ u.realizations, r.entity = e → (r.role : WithBot R) ≤ b := by
  refine ⟨fun h r hr he ↦ by subst he; exact (u.role_le_rank hr).trans h, fun h ↦ ?_⟩
  exact List.maximum_le_of_forall_le fun a ha ↦ by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    exact h r (List.mem_filter.1 hr).1 (by simpa using (List.mem_filter.1 hr).2)

theorem exists_rank_eq (h : e ∈ u) :
    ∃ r ∈ u.realizations, r.entity = e ∧ u.rank e = r.role := by
  obtain ⟨r, hr, rfl⟩ := h
  have hne : (u.realizations.filter (·.entity = r.entity)).map (·.role) ≠ [] :=
    List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_filter.2 ⟨hr, by simp⟩))
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 (List.maximum_ne_bot_of_ne_nil hne)
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 (List.maximum_mem hm.symm)
  exact ⟨r', (List.mem_filter.1 hr').1, by simpa using (List.mem_filter.1 hr').2, hm.symm⟩

end Rank

/-- The preferred center of `u`: the entity it realizes in the highest role, the first in surface
order if several are. -/
def cp [LinearOrder R] (u : Utterance E R F) : Option E :=
  (u.realizations.argmax (·.role)).map (·.entity)

@[simp] theorem cp_mk_nil [LinearOrder R] : (⟨[]⟩ : Utterance E R F).cp = none := rfl

theorem cp_mem [LinearOrder R] {u : Utterance E R F} {e : E} (h : u.cp = some e) : e ∈ u := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, List.argmax_mem hr, rfl⟩

end Utterance

/-! ### Backward-looking centers -/

section Cb

variable [DecidableEq E] [LinearOrder R] {prev : Utterance E R F} {s : Finset E} {e e' : E}

/-- The backward-looking centers of `s` after `prev`: the forward-looking centers of `prev` in
`s` that `prev` ranks highest. -/
def backwardCenters (prev : Utterance E R F) (s : Finset E) : Finset E :=
  (prev.cf ∩ s).argmax prev.rank

/-- The backward-looking center of `s` after `prev`: the entity in `s` that `prev` realizes in
the highest role, the first in the surface order of `prev` if several are. -/
def cb (prev : Utterance E R F) (s : Finset E) : Option E :=
  ((prev.realizations.filter (·.entity ∈ s)).argmax (·.role)).map (·.entity)

theorem mem_backwardCenters : e ∈ backwardCenters prev s ↔
    e ∈ prev ∧ e ∈ s ∧ ∀ e' ∈ prev, e' ∈ s → prev.rank e' ≤ prev.rank e := by
  simp [backwardCenters, Finset.mem_argmax, and_assoc]

theorem backwardCenters_subset : backwardCenters prev s ⊆ prev.cf ∩ s := Finset.argmax_subset

theorem backwardCenters_eq_empty_iff : backwardCenters prev s = ∅ ↔ Disjoint prev.cf s := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [backwardCenters, h, Finset.argmax_empty]⟩
  by_contra hne
  exact (Finset.argmax_nonempty (f := prev.rank) (Finset.nonempty_iff_ne_empty.mpr hne)).ne_empty h

@[simp] theorem cb_mk_nil (s : Finset E) : cb (⟨[]⟩ : Utterance E R F) s = none := rfl

/-- The backward-looking center is realized in `prev` by a realization in a role at least as
high as that of every realization in `prev` of an entity in `s`. -/
theorem exists_realization_of_cb (h : cb prev s = some e) :
    ∃ r ∈ prev.realizations, r.entity = e ∧ e ∈ s ∧
      ∀ r' ∈ prev.realizations, r'.entity ∈ s → r'.role ≤ r.role := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hr₁, hr₂⟩ := List.mem_filter.mp (List.argmax_mem hr)
  exact ⟨r, hr₁, rfl, of_decide_eq_true hr₂, fun r' h₁ h₂ ↦
    List.le_of_mem_argmax (List.mem_filter.mpr ⟨h₁, decide_eq_true h₂⟩) hr⟩

theorem cb_mem_left (h : cb prev s = some e) : e ∈ prev :=
  let ⟨r, hr, he, _⟩ := exists_realization_of_cb h
  ⟨r, hr, he⟩

theorem cb_mem_right (h : cb prev s = some e) : e ∈ s :=
  let ⟨_, _, _, he, _⟩ := exists_realization_of_cb h
  he

theorem cb_eq_none_iff : cb prev s = none ↔ Disjoint prev.cf s := by
  simp [cb, List.filter_eq_nil_iff, Finset.disjoint_left, Utterance.mem_iff]

/-- No forward-looking center of `prev` in `s` outranks the backward-looking center. -/
theorem rank_le_of_cb (h : cb prev s = some e) (he' : e' ∈ s) : prev.rank e' ≤ prev.rank e := by
  obtain ⟨r, hr, rfl, -, hmax⟩ := exists_realization_of_cb h
  exact prev.rank_le_iff.2 fun r' hr' he ↦
    (WithBot.coe_le_coe.2 (hmax r' hr' (he ▸ he'))).trans (prev.role_le_rank hr)

/-- The backward-looking center is one of the backward-looking centers. -/
theorem cb_mem_backwardCenters (h : cb prev s = some e) : e ∈ backwardCenters prev s :=
  mem_backwardCenters.2 ⟨cb_mem_left h, cb_mem_right h, fun _ _ he' ↦ rank_le_of_cb h he'⟩

/-- The backward-looking center is the only backward-looking center exactly when there is at
most one. -/
theorem backwardCenters_eq_toFinset_cb_iff :
    backwardCenters prev s = (cb prev s).toFinset ↔ (backwardCenters prev s).card ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h]
    cases cb prev s <;> simp
  · rcases hc : cb prev s with - | e
    · simpa using backwardCenters_eq_empty_iff.2 (cb_eq_none_iff.1 hc)
    · rw [Option.toFinset_some]
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨cb_mem_backwardCenters hc, fun x hx ↦
        Finset.card_le_one.1 h x hx e (cb_mem_backwardCenters hc)⟩

/-- There is at most one backward-looking center after an utterance that realizes no two
entities in the same role. -/
theorem card_backwardCenters_le_one (s : Finset E)
    (h : ∀ r₁ ∈ prev.realizations, ∀ r₂ ∈ prev.realizations,
      r₁.role = r₂.role → r₁.entity = r₂.entity) :
    (backwardCenters prev s).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
  obtain ⟨hpa, hca, hma⟩ := mem_backwardCenters.1 ha
  obtain ⟨hpb, hcb, hmb⟩ := mem_backwardCenters.1 hb
  have hab := le_antisymm (hmb a hpa hca) (hma b hpb hcb)
  obtain ⟨ra, hra, rfl, hea⟩ := prev.exists_rank_eq hpa
  obtain ⟨rb, hrb, rfl, heb⟩ := prev.exists_rank_eq hpb
  exact h ra hra rb hrb (WithBot.coe_injective (hea.symm.trans (hab.trans heb)))

/-! ### The preferred center -/

/-- The preferred center of `prev` is the backward-looking center of any set containing it. -/
theorem cb_eq_of_cp_eq (hp : prev.cp = some e) (he : e ∈ s) : cb prev s = some e := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact Option.map_eq_some_iff.mpr ⟨r, List.argmax_filter_of_mem hr (decide_eq_true he), rfl⟩

/-- The preferred center of an utterance is the backward-looking center of its own
forward-looking centers. -/
theorem cb_cf_self (u : Utterance E R F) : cb u u.cf = u.cp := by
  have h : u.realizations.filter (·.entity ∈ u.cf) = u.realizations :=
    List.filter_eq_self.mpr fun r hr ↦ decide_eq_true (u.mem_cf.mpr ⟨r, hr, rfl⟩)
  rw [cb, h, Utterance.cp]

/-- No forward-looking center outranks the preferred center. -/
theorem Utterance.rank_le_of_cp {u : Utterance E R F} (h : u.cp = some e) (e' : E) :
    u.rank e' ≤ u.rank e := by
  by_cases he' : e' ∈ u
  · exact rank_le_of_cb ((cb_cf_self u).trans h) (u.mem_cf.mpr he')
  · exact u.rank_le_iff.2 fun r hr he ↦ absurd ⟨r, hr, he⟩ he'

/-! ### Ranking by role and then by surface position -/

/-- Refining the ranking by surface position does not change the backward-looking center. -/
@[simp] theorem cb_indexed (u : Utterance E R F) (s : Finset E) : cb u.indexed s = cb u s := by
  have h : u.realizations.filter (·.entity ∈ s) =
      (u.realizations.zipIdx.filter (·.1.entity ∈ s)).map Prod.fst := by
    conv_lhs => rw [← List.zipIdx_map_fst 0 u.realizations]
    rw [List.filter_map]; rfl
  rw [cb, cb, h, Utterance.indexed, List.filter_map, List.argmax_map, List.argmax_map,
    Option.map_map, Option.map_map]
  exact congrArg _ (List.argmax_toLex_toDual_snd ((List.pairwise_snd_lt_zipIdx _ _).filter _))

/-- After an utterance ranked by role and then by surface position, the backward-looking center
is the only backward-looking center. -/
theorem backwardCenters_indexed (u : Utterance E R F) (s : Finset E) :
    backwardCenters u.indexed s = (cb u s).toFinset := by
  rw [← cb_indexed]
  refine backwardCenters_eq_toFinset_cb_iff.2 (card_backwardCenters_le_one s ?_)
  simp only [Utterance.indexed, List.mem_map, forall_exists_index, and_imp]
  rintro _ p hp rfl _ q hq rfl h
  have hpq : p.2 = q.2 := OrderDual.toDual.injective (Prod.ext_iff.mp (toLex.injective h)).2
  have hp' := List.mem_zipIdx_iff_getElem?.mp hp
  rw [hpq, List.mem_zipIdx_iff_getElem?.mp hq] at hp'
  exact show p.1.entity = q.1.entity from congrArg Realization.entity (Option.some.inj hp').symm

end Cb

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

/-- Counting more forms as pronouns preserves the unconditional form of Rule 1. -/
theorem CbPronominalized.mono {Q : Set F} [DecidablePred (· ∈ Q)] (hPQ : P ⊆ Q)
    (h : CbPronominalized P prev cur) : CbPronominalized Q prev cur :=
  fun c hc ↦ Utterance.pronominalized_mono hPQ (h c hc)

end Rule1

end Discourse.Centering
