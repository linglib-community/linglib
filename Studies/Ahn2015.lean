module

public import Mathlib.Data.Set.Lattice.Bounded
public import Linglib.Data.Examples.Ahn2015
public import Linglib.Semantics.Exhaustification.Excluder

/-!
# The semantics of additive *either*

Ahn takes *too* and additive *either* to be two-place predicates over the host proposition and a
silent propositional anaphor `q`, presupposed to be a distinct focus alternative of the host, and
lets them assert a conjunction and a disjunction respectively (`too`, `either`, `Antecedent`).
Negation then scopes over the assertion: *Mary didn't buy them too* asserts `¬(q ∧ p)`, which
with the discourse-given `q` is `¬p` (`not_too_of_antecedent`), while *John didn't leave either*
asserts `¬(q ∨ p)`, so both the host and the antecedent are denied (`either_compl`). Since the
additive component is asserted rather than presupposed, denying it with an anaphoric *as well*
is consistent where denying an existential is not (`abrusan_contrast`).

The distribution of *either* follows from the disjunction under the exhaustification account of
polarity items: the alternatives of a disjunction are the disjuncts and their conjunction, and
the naive exhaustifier, Chierchia's `O` (`Exhaustification.exh`), negates every alternative the
prejacent fails to entail. In a
positive context that leaves the disjunction without either disjunct, a contradiction
(`either_positive_contradiction`); under negation the negated disjunction entails every
alternative, so exhaustification is vacuous (`either_negative_vacuous`), and likewise in any
downward-entailing context (`either_vacuous_in_de`), which is why the account overgenerates to
all such contexts and leaves the strong-NPI restriction to negation open. *Too* entails all of
its alternatives, so it is exhaustified vacuously everywhere and is no polarity item
(`too_entails_alts`). The paper's judgments are its rows: *either* is acceptable exactly in a
negative host whose antecedent is not positive, and *too* fails only for want of an antecedent
(`either_iff_negative`, `too_any_polarity`).

## References

* [ahn-2015]
* [rullmann-2003]
* [heim-1992]
* [kripke-2009]
* [rooth-1992]
* [chierchia-2013]
* [sauerland-2004]
-/

@[expose] public section

namespace Ahn2015

open Exhaustification

variable {World : Type*} (q p : Set World)

/-! ### Too and either -/

/-- *Too* and *either* share the presupposition that the anaphor is a focus alternative of the
host distinct from it. -/
def Antecedent (C : Set (Set World)) : Prop := q ∈ C ∧ q ≠ p

/-- *Too* asserts its additive meaning as the conjunction `q ⊓ p` with the anaphor. -/
abbrev too : Set World := q ⊓ p

/-- *Either* asserts the disjunctive counterpart, `q ⊔ p`. -/
abbrev either : Set World := q ⊔ p

theorem too_compl : (too q p)ᶜ = qᶜ ⊔ pᶜ := compl_inf

theorem not_too_of_antecedent {w : World} (hq : w ∈ q) : w ∈ (too q p)ᶜ ↔ w ∉ p := by
  simp [hq]

theorem either_compl : (either q p)ᶜ = qᶜ ⊓ pᶜ := compl_sup

theorem abrusan_contrast {e : Set World} (he : p ≤ e) :
    p ⊓ eᶜ = ⊥ ∧ p ⊓ (too q p)ᶜ = p ⊓ qᶜ := by
  refine ⟨?_, ?_⟩
  · exact le_bot_iff.1 (inf_le_inf_right _ he |>.trans (by rw [inf_compl_eq_bot]))
  · rw [too_compl, inf_sup_left, inf_compl_eq_bot, sup_bot_eq, inf_comm]

/-! ### Exhaustification -/

/-- The alternatives of a disjunction are the disjuncts and their conjunction. -/
def disjAlts : Set (Set World) := {q ⊔ p, q, p, q ⊓ p}

theorem too_entails_alts : exh {q ⊓ p, q, p, q ⊔ p} (too q p) = too q p :=
  exh_eq_self fun a ha => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    exacts [le_rfl, inf_le_left, inf_le_right, inf_le_left.trans le_sup_left]

theorem either_positive_contradiction (hq : ¬ either q p ≤ q) (hp : ¬ either q p ≤ p) :
    exh (disjAlts q p) (either q p) = ⊥ := by
  refine le_bot_iff.1 ?_
  calc exh (disjAlts q p) (either q p) ≤ either q p ⊓ qᶜ ⊓ pᶜ :=
        le_inf (le_inf inf_le_left (exh_subset_compl (by simp [disjAlts]) hq))
          (exh_subset_compl (by simp [disjAlts]) hp)
    _ = ⊥ := by rw [inf_assoc, ← compl_sup, inf_compl_eq_bot]

theorem either_negative_vacuous :
    exh ((disjAlts q p).image compl) (either q p)ᶜ = (either q p)ᶜ :=
  exh_eq_self fun a ⟨b, hb, hba⟩ => by
    subst hba
    simp only [disjAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    exacts [le_rfl, compl_le_compl le_sup_left, compl_le_compl le_sup_right,
      compl_le_compl (inf_le_left.trans le_sup_left)]

theorem either_vacuous_in_de (C : Set World → Set World) (hDE : Antitone C) :
    C (either q p) ⊆ C (q ⊓ p) :=
  hDE (inf_le_left.trans le_sup_left)

/-! ### The data -/

theorem either_iff_negative :
    ∀ e ∈ Examples.all, e.feature? "particle" = some "either" →
      (e.judgment = .acceptable ↔
        e.feature? "polarity" = some "negative" ∧ e.feature? "antecedent" ≠ some "positive") := by
  decide

theorem too_any_polarity :
    ∀ e ∈ Examples.all, e.feature? "particle" = some "too" → ¬ e.JudgedFelicitous →
      e.feature? "polarity" = some "positive" ∧ (e.context ≠ "") := by
  decide

end Ahn2015
