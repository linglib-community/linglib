module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Data.Examples.MitrovicSauerland2016
public import Linglib.Fragments.English.Coordination
public import Linglib.Fragments.English.FocusParticles
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.Japanese.FocusParticles
public import Linglib.Fragments.Hungarian.Coordination
public import Linglib.Fragments.Hungarian.FocusParticles
public import Linglib.Fragments.Latin.Determiners
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Tactic.DeriveFintype

/-!
# Mitrović and Sauerland (2016): Two Conjunctions Are Better Than One

Mitrović and Sauerland decompose the conjunction of two noun phrases into a junctor J, which
intersects two generalized quantifiers, and a head μ on each conjunct, which denotes the subset
relation and so is the quantifier *every*. Languages differ in which of the three heads they
pronounce: English *and* is J, Japanese *mo* is μ, and Hungarian pronounces all three. Only μ can
have the additive and quantificational uses of Japanese *mo*.

## Implementation notes

* The heads an example pronounces are those its gloss line writes outside parentheses, or for
  Latin *-que* and *atque* those of the configurations (38b) and (39). The examples are (1c),
  (23)–(29) with fn. 9, and (33).
* The J coordinators with Fragment entries are English *and*, Japanese *to*, the verbal
  conjunction of Table 1, and Hungarian *és*; the μ coordinators are Japanese *mo*, Hungarian *is*
  and Latin *-que*. A coordinator's additive use is `Coordinator.IsAlsoAdditive` against the
  additive particles of its language in the Fragments.

## TODO

* Table 1, fifteen languages whose quantificational conjunction is the nominal one and not the
  verbal one, and the Indo-European shift from μ to J of §3.3.

## References

* [mitrovic-sauerland-2016]
* [mitrovic-sauerland-2014]
-/

@[expose] public section

namespace MitrovicSauerland2016

open Quantifier
open scoped Denotes

/-! ### The two heads, (12) -/

section Semantics

variable {α : Type*}

/-- The head μ denotes the subset relation between two predicates, (12a). -/
def mu (R S : α → Prop) : Prop := R ≤ S

/-- The shift from an individual to its characteristic property, the singleton. -/
def shift (a : α) : α → Prop := (· = a)

-- (15)
theorem mu_eq_every : (mu : Det α) = Det.every := rfl

theorem mu_shift (a : α) : mu (shift a) = Quantifier.individual a :=
  funext fun _ ↦ propext ⟨fun h ↦ h a rfl, fun h _ hx ↦ hx ▸ h⟩

-- (13)
theorem conjunction_eq {j : Coordinator} (hj : j.role = .conjunctive) (a b : α) :
    j.denote {mu (shift a), mu (shift b)} = Quantifier.individual a ⊓ Quantifier.individual b := by
  rw [mu_shift, mu_shift, Coordinator.denote_of_conjunctive hj, sInf_pair]

/-- The conjunction holds of a predicate that holds of each conjunct, so it has no collective
reading, (14). -/
theorem conjunction_apply {j : Coordinator} (hj : j.role = .conjunctive) (a b : α)
    (P : α → Prop) : j.denote {mu (shift a), mu (shift b)} P ↔ P a ∧ P b := by
  rw [conjunction_eq hj]; rfl

theorem shift_inf_shift_eq_bot_iff {a b : α} : shift a ⊓ shift b = ⊥ ↔ a ≠ b := by
  simp [funext_iff, shift]

end Semantics

/-! ### The collective μ′, (20)–(22) -/

section Collective

variable {α : Type*} [SemilatticeSup α] {x y : α} {P : α → Prop}

/-- `muPrime x P`, the collective μ′ that (20) tries, holds when `P` is true of some sum of which
`x` is a part. -/
def muPrime (x : α) (P : α → Prop) : Prop := ∃ y, y ⊔ x = y ∧ P y

theorem muPrime_iff_mem_lowerClosure : muPrime x P ↔ x ∈ lowerClosure {y | P y} := by
  simp [muPrime, and_comm]

theorem muPrime_of_le (hxy : x ≤ y) (hy : P y) : muPrime x P := ⟨y, sup_eq_left.2 hxy, hy⟩

-- (21), (19)
theorem muPrime_of_collective {a b : α} (h : P (a ⊔ b)) : muPrime a P ∧ muPrime b P :=
  ⟨muPrime_of_le le_sup_left h, muPrime_of_le le_sup_right h⟩

theorem muPrime_of_distributive {a b : α} (ha : P a) (hb : P b) : muPrime a P ∧ muPrime b P :=
  ⟨muPrime_of_le le_rfl ha, muPrime_of_le le_rfl hb⟩

end Collective

/-- For two members of a team of three (22), the conjunction of their μ′ phrases holds of forming
the team, though neither collective nor distributive reading does ((20)). -/
theorem muPrime_team :
    (muPrime ({0} : Finset (Fin 3)) (· = Finset.univ) ∧
      muPrime ({1} : Finset (Fin 3)) (· = Finset.univ)) ∧
      ({0} ⊔ {1} : Finset (Fin 3)) ≠ Finset.univ ∧ ({0} : Finset (Fin 3)) ≠ Finset.univ :=
  ⟨⟨muPrime_of_le (by decide) rfl, muPrime_of_le (by decide) rfl⟩, by decide, by decide⟩

/-- An indeterminate quantifier whose particle is conjunctive denotes μ, (15). -/
theorem mu_of_conjunctive_particle {q : IndeterminateQuantifier}
    (hq : q.particle.role = .conjunctive) {α : Type} [Fintype α] {d : Det.Family}
    (h : d ∈ ⟦q⟧) : d α = mu := by
  obtain rfl : d = q.reading := h
  rw [IndeterminateQuantifier.reading_of_conjunctive hq]
  rfl

-- (1a)
theorem dare_mo_denotes_mu {α : Type} [Fintype α] {d : Det.Family}
    (h : d ∈ ⟦Japanese.Determiners.dareMo⟧) : d α = mu :=
  mu_of_conjunctive_particle rfl h

-- (40)
theorem quisque_denotes_mu {α : Type} [Fintype α] {d : Det.Family}
    (h : d ∈ ⟦Latin.Determiners.quisque⟧) : d α = mu :=
  mu_of_conjunctive_particle rfl h

/-! ### Exponence, §3.1 -/

/-- The heads of the structure for the conjunction of two noun phrases, (11) and (13), are J and
a μ head on each conjunct. -/
inductive Head where
  | j
  | mu (conjunct : Fin 2)
  deriving DecidableEq, Repr, Fintype

theorem card_head : Fintype.card Head = 3 := rfl

/-- The labels of the heads in the rows. -/
def Head.labels : List (String × Head) := [("j", .j), ("mu-first", .mu 0), ("mu-second", .mu 1)]

/-- The heads an example pronounces. -/
def pronounced (d : Datum) : Finset Head :=
  ((d.features "head").filterMap (List.lookup · Head.labels)).toFinset

/-- The sets of heads the examples pronounce. -/
def attested : Finset (Finset Head) := (Examples.all.map pronounced).toFinset

theorem attested_eq : attested = {{.j}, {.mu 1}, {.mu 0, .mu 1}, {.j, .mu 1}, Finset.univ} := by
  decide

/-- The examples pronounce exactly the nonempty sets of heads in which the μ of the first conjunct
comes only with that of the second, all but the sets that keep the first μ and drop the
second. -/
theorem mem_attested_iff {h : Finset Head} :
    h ∈ attested ↔ h.Nonempty ∧ (Head.mu 0 ∈ h → Head.mu 1 ∈ h) := by
  rw [attested_eq]; revert h; decide

/-- The examples that pronounce all three heads are Southeastern Macedonian (26), Serbo-Croatian
(27), whose J is adversative, Hungarian (28) and Avar (29). -/
theorem languages_pronounced_eq_univ :
    (Examples.all.filter (pronounced · = Finset.univ)).map (·.language) =
      ["mace1250", "sout1528", "hung1274", "avar1256"] := by
  decide

/-! ### Other uses, §3 -/

/-- The coordinators the paper takes for J that have Fragment entries. -/
def jCoordinators : List Coordinator :=
  [English.Coordination.and_, Japanese.Coordination.to_, Hungarian.Coordination.es]

/-- The coordinators the paper takes for μ that have Fragment entries. -/
def muCoordinators : List Coordinator :=
  [Japanese.Coordination.mo, Hungarian.Coordination.is_, Latin.Coordination.que]

/-- The additive particles of their languages in the Fragments. -/
def additiveParticles : List AdditiveParticle :=
  [English.FocusParticles.too, English.FocusParticles.also, Japanese.FocusParticles.mo,
    Hungarian.FocusParticles.is_]

/-- The indeterminate quantifiers of their languages in the Fragments. -/
def quantifiers : List IndeterminateQuantifier :=
  Japanese.Determiners.indefinites ++ [Latin.Determiners.quisque]

theorem coordinators_conjunctive :
    ∀ c ∈ jCoordinators ++ muCoordinators, c.role = .conjunctive := by
  decide

/-- Every μ coordinator has a use outside conjunction, as an additive particle or as the particle
of an indeterminate quantifier. -/
theorem mu_has_other_use : ∀ c ∈ muCoordinators,
    (∃ a ∈ additiveParticles, c.IsAlsoAdditive a) ∨ ∃ q ∈ quantifiers, q.particle = c := by
  decide

/-- No J coordinator has an additive or a quantificational use. -/
theorem j_has_no_other_use : ∀ c ∈ jCoordinators,
    (∀ a ∈ additiveParticles, ¬ c.IsAlsoAdditive a) ∧ ∀ q ∈ quantifiers, q.particle ≠ c := by
  decide

end MitrovicSauerland2016
