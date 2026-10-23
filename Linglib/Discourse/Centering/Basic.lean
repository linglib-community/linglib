module

public import Mathlib.Data.List.Sort
public import Mathlib.Order.RelClasses

/-!
# Centering theory: centers and the pronominalization rule

Grosz, Joshi, and Weinstein's centering theory tracks the entities an utterance is about. An
utterance realizes entities in grammatical roles; its forward-looking centers are those entities
ranked by role, the first of them its preferred center, and its backward-looking center is the
highest-ranked forward-looking center of the previous utterance that it realizes. Rule 1 says
that if the utterance pronominalizes any forward-looking center of the previous one, it
pronominalizes its backward-looking center.

## Main declarations

* `Discourse.Centering.Realization` and `Discourse.Centering.Utterance`: a noun phrase realizing
  an entity in a role, by a pronoun or not, and an utterance as its realizations in surface
  order. `e ∈ u` says that `u` realizes `e`.
* `Utterance.ranked`, `Utterance.cf`, `Utterance.cp`: the realizations in rank order, the
  forward-looking centers, and the preferred center.
* `Discourse.Centering.cb`: the backward-looking center, for any current utterance with
  decidable membership, characterized by `cb_eq_some_iff` and `role_le_of_cb`.
* `Discourse.Centering.PronominalizationConstraint` and `CbPronominalized`: Rule 1 and Gordon,
  Grosz, and Gilliom's unconditional strengthening of it.

## Implementation notes

The ranking of forward-looking centers is a `LinearOrder` on the role type, higher meaning more
prominent; two realizations in the same role tie, and the sort is stable, so ties keep surface
order. An entity realized twice is listed twice among the forward-looking centers, which leaves
the backward-looking center, the preferred center, and Rule 1 unaffected.

The current utterance of `cb` is any type with decidable entity membership, so that a study can
let an utterance realize an entity indirectly, as in [poesio-stevenson-eugenio-hitzeman-2004].

## References

* [grosz-joshi-weinstein-1995]
* [gordon-grosz-gilliom-1993]
* [kameyama-1986]
* [poesio-stevenson-eugenio-hitzeman-2004]
-/

@[expose] public section

namespace Discourse.Centering

variable {E R : Type*}

/-- A noun phrase realizing `entity` in the grammatical role `role`, a pronoun or not. -/
structure Realization (E R : Type*) where
  entity : E
  role : R
  isPronoun : Bool
  deriving Repr, DecidableEq

/-- An utterance as its noun-phrase realizations in surface order. -/
structure Utterance (E R : Type*) where
  realizations : List (Realization E R)
  deriving Repr, DecidableEq

namespace Utterance

/-- `e ∈ u` when some realization in `u` is of `e`. -/
instance : Membership E (Utterance E R) := ⟨fun u e ↦ ∃ r ∈ u.realizations, r.entity = e⟩

theorem mem_iff {u : Utterance E R} {e : E} : e ∈ u ↔ ∃ r ∈ u.realizations, r.entity = e :=
  Iff.rfl

/-- `u` realizes `e` by a pronoun. -/
def Pronominalizes (u : Utterance E R) (e : E) : Prop :=
  ∃ r ∈ u.realizations, r.entity = e ∧ r.isPronoun = true

section Decidable

variable [DecidableEq E] (u : Utterance E R) (e : E)

instance : Decidable (e ∈ u) := inferInstanceAs (Decidable (∃ r ∈ u.realizations, r.entity = e))

instance : Decidable (u.Pronominalizes e) :=
  inferInstanceAs (Decidable (∃ r ∈ u.realizations, r.entity = e ∧ r.isPronoun = true))

end Decidable

/-! ### Forward-looking centers -/

section Cf

variable [LinearOrder R] (u : Utterance E R) {e : E}

/-- The realizations of `u` in rank order: descending by role, ties in surface order. -/
def ranked : List (Realization E R) := u.realizations.insertionSort fun a b ↦ b.role ≤ a.role

theorem ranked_perm : u.ranked.Perm u.realizations := List.perm_insertionSort _ _

@[simp] theorem mem_ranked {r : Realization E R} : r ∈ u.ranked ↔ r ∈ u.realizations :=
  List.mem_insertionSort _

theorem ranked_pairwise : u.ranked.Pairwise fun a b ↦ b.role ≤ a.role :=
  @List.pairwise_insertionSort _ _ _ (Order.Preimage.instTotal (r := (· ≥ ·)))
    (Order.Preimage.instIsTrans (r := (· ≥ ·))) _

/-- The forward-looking centers of `u`: its entities in rank order. -/
def cf : List E := u.ranked.map (·.entity)

/-- The preferred center of `u`: its highest-ranked forward-looking center. -/
def cp : Option E := u.cf.head?

@[simp] theorem cf_mk_nil : (⟨[]⟩ : Utterance E R).cf = [] := by simp [cf, ranked]

@[simp] theorem cp_mk_nil : (⟨[]⟩ : Utterance E R).cp = none := by simp [cp]

@[simp] theorem mem_cf : e ∈ u.cf ↔ e ∈ u := by simp [cf, mem_iff]

theorem cp_mem_cf (h : u.cp = some e) : e ∈ u.cf := List.mem_of_mem_head? (Option.mem_def.mpr h)

theorem cp_mem (h : u.cp = some e) : e ∈ u := u.mem_cf.mp (u.cp_mem_cf h)

end Cf

end Utterance

/-! ### The backward-looking center -/

section Cb

variable [LinearOrder R] {U : Type*} [Membership E U] [∀ (u : U) (e : E), Decidable (e ∈ u)]

/-- The backward-looking center of `cur` after `prev`: the highest-ranked forward-looking center
of `prev` that `cur` realizes, if any. -/
def cb (prev : Utterance E R) (cur : U) : Option E := prev.cf.find? (· ∈ cur)

variable {prev : Utterance E R} {cur : U} {e : E}

@[simp] theorem cb_mk_nil (cur : U) : cb (⟨[]⟩ : Utterance E R) cur = none := by simp [cb]

theorem cb_mem_cf (h : cb prev cur = some e) : e ∈ prev.cf := List.mem_of_find?_eq_some h

theorem mem_of_cb (h : cb prev cur = some e) : e ∈ cur :=
  decide_eq_true_eq.mp (List.find?_eq_some_iff_append.mp h).1

theorem cb_eq_some_iff : cb prev cur = some e ↔
    e ∈ cur ∧ ∃ l₁ l₂, prev.cf = l₁ ++ e :: l₂ ∧ ∀ e' ∈ l₁, e' ∉ cur := by
  simp [cb, List.find?_eq_some_iff_append]

theorem cb_eq_none_iff : cb prev cur = none ↔ ∀ e ∈ prev.cf, e ∉ cur := by
  simp [cb, List.find?_eq_none]

theorem role_le_of_cb (h : cb prev cur = some e) {r : Realization E R}
    (hr : r ∈ prev.realizations) (hcur : r.entity ∈ cur) :
    ∃ r' ∈ prev.realizations, r'.entity = e ∧ r.role ≤ r'.role := by
  obtain ⟨-, l₁, l₂, hl, hl₁⟩ := cb_eq_some_iff.mp h
  obtain ⟨m₁, m₂, hm, rfl, hm₂⟩ := List.map_eq_append_iff.mp hl
  obtain ⟨r', m₂', rfl, rfl, -⟩ := List.map_eq_cons_iff.mp hm₂
  have hs := prev.ranked_pairwise
  rw [hm, List.pairwise_append, List.pairwise_cons] at hs
  have hr₀ : r ∈ m₁ ++ r' :: m₂' := hm ▸ prev.mem_ranked.mpr hr
  refine ⟨r', prev.mem_ranked.mp (hm ▸ List.mem_append_right _ (List.mem_cons_self ..)), rfl, ?_⟩
  rcases List.mem_append.mp hr₀ with hr₁ | hr₂
  · exact absurd hcur (hl₁ _ (List.mem_map_of_mem hr₁))
  · rcases List.mem_cons.mp hr₂ with rfl | hr₂
    · exact le_rfl
    · exact hs.2.1.1 r hr₂

end Cb

/-! ### Rule 1 -/

section Rule1

variable [DecidableEq E] [LinearOrder R] (prev cur : Utterance E R)

/-- The backward-looking center of `cur` after `prev`, if any, is pronominalized: Gordon, Grosz,
and Gilliom's unconditional strengthening of Rule 1, motivated by the repeated-name penalty. -/
def CbPronominalized : Prop := ∀ c ∈ cb prev cur, cur.Pronominalizes c

instance : Decidable (CbPronominalized prev cur) :=
  inferInstanceAs (Decidable (∀ c ∈ cb prev cur, cur.Pronominalizes c))

/-- Rule 1 of [grosz-joshi-weinstein-1995]: if `cur` pronominalizes any forward-looking center of
`prev`, it pronominalizes its backward-looking center. -/
def PronominalizationConstraint : Prop :=
  (∃ e ∈ prev.cf, cur.Pronominalizes e) → CbPronominalized prev cur

instance : Decidable (PronominalizationConstraint prev cur) :=
  inferInstanceAs (Decidable ((∃ e ∈ prev.cf, cur.Pronominalizes e) → CbPronominalized prev cur))

variable {prev cur}

/-- The unconditional strengthening implies Rule 1. -/
theorem CbPronominalized.constraint (h : CbPronominalized prev cur) :
    PronominalizationConstraint prev cur :=
  fun _ ↦ h

/-- Rule 1 holds vacuously when `cur` uses no pronoun. -/
theorem pronominalizationConstraint_of_forall_not (h : ∀ e, ¬ cur.Pronominalizes e) :
    PronominalizationConstraint prev cur :=
  fun ⟨e, _, he⟩ ↦ absurd he (h e)

end Rule1

end Discourse.Centering
