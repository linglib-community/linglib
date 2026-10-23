module

public import Mathlib.Data.Finset.Card
public import Linglib.Semantics.Plurality.Reciprocal

/-!
# Reciprocals are definites

Formalization of [beck-2001] (NLS 9). *Each other* uniformly denotes "the other ones
among them" — an anaphoric plural definite recasting [heim-lasnik-may-1991] — and a
reciprocal sentence is a special kind of relational plural. The paper admits exactly
four semantic readings — collective, Strong Reciprocity, Weak Reciprocity, and
situation-based WR — tracking the readings of relational plurals. The other
interpretations of the [dalrymple-et-al-1998] survey are not semantic: Partitioned SR
and One-way WR are cover effects ([schwarzschild-1996] subgroups and exceptions),
Intermediate Reciprocity is situation-based WR under a subsituation context (§5), and
Inclusive Alternative Ordering is left underived, a lexical process limited to
spatio-temporal relations (§6.3).

## Main definitions

* `otherOnesAmongThem` — the HLM definite ((76)), in its singularity-parts case.
* `CollectiveReading` — predication of the reciprocal group itself ((84)).
* `SituationWeakReciprocity` — WR with cumulation over the situation argument ((193),
  bivalent, singleton covers).

## Main results

* `strongReciprocity_iff_otherOnes`, `collectiveReading_iff_strong` — SR is double
  distribution over the definite ((81)); with a distributive relation the collective
  schema collapses into SR.
* `situationWR_imp_weakReciprocity` — under persistence, situation-based WR entails
  WR: the right edge of the entailment chain SR → sitWR → WR feeding the Strongest
  Meaning Hypothesis ((219), fn. 15).

The six-scheme entailment lattice ((28)) and the WR-as-cumulation identity ((120),
`weakReciprocity_iff_liftRel`) live in `Plurality/Reciprocal.lean` and are
consumed here. The convergence with [haug-dalrymple-2020] on presuppositional
distinctness is housed in `Studies/HaugDalrymple2020.lean` (the later paper draws the
comparison); the trivalent divergence from [sternefeld-1998] is noted at
`SituationWeakReciprocity`.

## References

* [beck-2001] — the paper; [heim-lasnik-may-1991] — the recast analysis.
* [dalrymple-et-al-1998] — the reading survey and the Strongest Meaning Hypothesis;
  [langendoen-1978] — reciprocity as relational-plural predication;
  [fiengo-lasnik-1973] — Partitioned SR; [kanski-1987] — IAO.
* [link-1983], [schwarzschild-1996], [sharvy-1980], [beck-sauerland-2000] — the
  plural-predication substrate: `*`, covers, maximality, `**`.
* [sternefeld-1998] — the WR-by-cumulation analysis §4 builds on and improves.
-/

@[expose] public section

namespace Beck2001

open Reciprocal

variable {α : Type*}

section
variable [DecidableEq α]

/-! ### The HLM definite -/

/-- The reciprocal's denotation ((76)): "the other ones among them" — the maximal
    subgroup of the antecedent `A` not overlapping the contrast argument `x`. In the
    singularity-parts case (distinctness = non-identity, p. 92) this is `A.erase x`;
    the full (76) routes through Sharvy maximality and Link `*`, with non-overlap
    replacing non-identity when covers contain genuine subgroups ((78)). -/
def otherOnesAmongThem (A : Finset α) (x : α) : Finset α :=
  A.erase x

theorem otherOnesAmongThem_excludes (A : Finset α) (x : α) :
    x ∉ otherOnesAmongThem A x :=
  Finset.notMem_erase x A

theorem otherOnesAmongThem_subset (A : Finset α) (x : α) :
    otherOnesAmongThem A x ⊆ A :=
  Finset.erase_subset x A

/-- On a plural antecedent the definite is defined (nonempty) at every member — the
    plurality presupposition ((115), §4.3.1). -/
theorem otherOnesAmongThem_nonempty (A : Finset α) (x : α) (hne : 1 < A.card) :
    (otherOnesAmongThem A x).Nonempty := by
  obtain ⟨y, hy, hyx⟩ := A.exists_mem_ne hne x
  exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩

/-! ### The semantic readings, read off the definite -/

/-- On a plural antecedent, SR is double distribution over the definite ((81)): distribute
    over the antecedent, then over "the other ones among them". -/
theorem strongReciprocity_iff_otherOnes (R : α → α → Prop) {A : Finset α} (hA : 1 < A.card) :
    StrongReciprocity R A ↔ ∀ x ∈ A, ∀ y ∈ otherOnesAmongThem A x, R x y := by
  rw [strongReciprocity_iff, and_iff_right (Finset.one_lt_card_iff_nontrivial.1 hA)]
  constructor
  · intro h x hx y hy
    obtain ⟨hyx, hyA⟩ := Finset.mem_erase.mp hy
    exact h hx hyA hyx.symm
  · intro h x hx y hy hxy
    exact h x hx y (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩)

/-- The collective reading ((84)): the relation holds of each member and the
    reciprocal group itself, with no distribution over that group — "the forks are
    propped against each other". -/
def CollectiveReading (R : α → Finset α → Prop) (A : Finset α) : Prop :=
  ∀ x ∈ A, R x (otherOnesAmongThem A x)

/-- On a plural antecedent and with a relation that distributes to members, the collective
    schema is exactly SR: (81) and (84) differ only in distribution over the definite. -/
theorem collectiveReading_iff_strong (R : α → α → Prop) {A : Finset α} (hA : 1 < A.card) :
    CollectiveReading (fun x Y => ∀ y ∈ Y, R x y) A ↔ StrongReciprocity R A := by
  rw [strongReciprocity_iff_otherOnes R hA]
  rfl

end

/-! ### Situation-based Weak Reciprocity

(120)'s bivalent collapse — WR is `**` of the strict-distinct relation — is the
substrate theorem `weakReciprocity_iff_liftRel`, shared with
[sternefeld-1998]'s (26b); the two analyses differ only trivalently, where
[sternefeld-1998] asserts distinctness and [beck-2001] presupposes it ((113), the
distinct-subgroups effect of §4.3.2). What remains of the paper's own reading
inventory is the situation layer. -/

variable {σ : Type*}

/-- Situation-based WR ((193), bivalent, singleton covers): every relevant
    subsituation contains a distinct pair in the relation, and every member
    participates in some relevant subsituation, in each direction. -/
def SituationWeakReciprocity (R : α → α → σ → Prop) (A : Finset α)
    (subs : Finset σ) : Prop :=
  (∀ s ∈ subs, ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ R x y s) ∧
    (∀ x ∈ A, ∃ s ∈ subs, ∃ y ∈ A, x ≠ y ∧ R x y s) ∧
      (∀ y ∈ A, ∃ s ∈ subs, ∃ x ∈ A, x ≠ y ∧ R x y s)

/-- Under persistence — what holds in a subsituation holds in the evaluation
    situation — situation-based WR entails WR at the evaluation situation: the right
    edge of the entailment chain SR → sitWR → WR that feeds the paper's Strongest
    Meaning Hypothesis ((219), fn. 15). -/
theorem situationWR_imp_weakReciprocity (R : α → α → σ → Prop) (A : Finset α)
    (subs : Finset σ) (s : σ)
    (hpers : ∀ x y, ∀ s' ∈ subs, R x y s' → R x y s)
    (h : SituationWeakReciprocity R A subs) :
    WeakReciprocity (fun a b => R a b s) A := by
  obtain ⟨-, hx, hy⟩ := h
  refine ⟨fun x hxA => ?_, fun y hyA => ?_⟩
  · obtain ⟨s', hs', y, hyA, hxy, hR⟩ := hx x hxA
    exact ⟨y, hyA, hpers x y s' hs' hR, hxy⟩
  · obtain ⟨s', hs', x, hxA, hxy, hR⟩ := hy y hyA
    exact ⟨x, hxA, hpers x y s' hs' hR, hxy⟩

end Beck2001
