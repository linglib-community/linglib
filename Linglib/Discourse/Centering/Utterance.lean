module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Centering theory: utterances and their forward-looking centers

An utterance realizes entities in grammatical roles by expressions of some form, and the roles are
ranked. The *forward-looking centers* of an utterance are the entities it realizes, each ranked by
the highest role in which it is realized.

## Main definitions

* `Discourse.Centering.Realization`, `Discourse.Centering.Utterance`: a noun phrase as an entity,
  a role and a form, and an utterance as a list of them in surface order.
* `Discourse.Centering.Utterance.cf`: the forward-looking centers, a finset of entities.
* `Discourse.Centering.Utterance.rank`: the rank of an entity, the highest role in which the
  utterance realizes it.
* `Discourse.Centering.Utterance.pronominalized`: the entities realized by a form in a given set.
* `Discourse.Centering.Utterance.indexed`: the utterance with each role refined by surface
  position.

## Implementation notes

The ranking is a `LinearOrder` on the role type, higher meaning more prominent. An entity realized
in several roles is ranked by the highest of them. Two entities realized in the same role tie, so
the ranking of entities by `Utterance.rank` is a total preorder.
`Utterance.indexed` separates them by surface position, an earlier realization outranking a later
one.

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

end Utterance

end Discourse.Centering
