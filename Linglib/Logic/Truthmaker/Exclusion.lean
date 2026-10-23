module

public import Linglib.Logic.Truthmaker.Bilateral
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Order.Concept

/-!
# Exclusion

This file defines exclusion between states and what it determines in unilateral truthmaker
semantics. Given an exclusion relation, two states conflict when a part of one excludes a part of
the other, and a state is possible when it does not conflict with itself. Plebani, Rosella and
Saitta, and independently Champollion and Bernard, derive possibility in this way, while Fine
takes the possible states as given. Fine constrains exclusion by three conditions and negates a
proposition `P` by fusing states that together exclude its verifiers. This gives the exclusive
negation `−P`, and its regular closure, the exclusionary negation `∼P`.

## Main definitions

* `Truthmaker.Conflict excl s t`: some part of `s` excludes some part of `t`.
* `Truthmaker.possible excl`: the states that do not conflict with themselves.
* `Truthmaker.PossibleFusion excl`: two possible states that do not conflict have a possible
  fusion.
* `Truthmaker.UpwardExclusion`, `Truthmaker.DownwardExclusion`, `Truthmaker.NullExclusion`:
  Fine's conditions on exclusion.
* `Truthmaker.Excludes excl Q P`: every verifier of `Q` excludes a verifier of `P`, and every
  verifier of `P` is excluded by a verifier of `Q`.
* `Truthmaker.exclusiveNeg`, `Truthmaker.exclusionaryNeg`: Fine's negations `−P` and `∼P`.
* `Truthmaker.ClassicalExclusion excl P`: Fine's classical exclusion over the possible states `P`.

## Main results

* `Truthmaker.isConjunctivePart_iff_excludes`: containment is exclusion with parthood in place of
  exclusion.
* `Truthmaker.mem_possible_iff_forall`: a state is possible exactly when no two of its parts
  conflict.
* `Truthmaker.coe_upperClosure_exclusionaryNeg`: under Upward Exclusion, the states containing a
  verifier of `∼P` are those that conflict with every verifier of `P`, the polar of `P` under
  conflict.
* `Truthmaker.sSup_exclusiveNeg`: the subject-matter of `−P` is the fusion of the excluders of
  verifiers of `P`.
* `Truthmaker.forall_exists_conflict_iff`: the half of Downward Exclusion that rules out emergent
  exclusion says that a state conflicting with a fusion conflicts with one of its members.
* `Truthmaker.exclusionaryNeg_singleton`: the negation of a single state is the regular closure of
  its excluders.
* `Truthmaker.exclusionaryNeg_regularClosure`: negation does not see regular closure.
* `Truthmaker.exclusionaryNeg_regularClosure_iUnion`, `Truthmaker.exclusionaryNeg_iSups`: the de
  Morgan laws for the exclusionary negation.
* `Truthmaker.exclusionaryNeg_exclusionaryNeg`: double negation holds of every regular proposition
  if it holds of every single state.
* `Truthmaker.ClassicalExclusion.exclusive`, `Truthmaker.ClassicalExclusion.exhaustive`: under
  classical exclusion a single state paired with its negation is exclusive and exhaustive.
* `Truthmaker.Canonical.possible_excl`: in the canonical space, where a literal excludes its mirror
  image, the derived possibility is Fine's consistency.
* `Truthmaker.RedBlueGreen.exclusionaryNeg_exclusionaryNeg_ne`: double negation can fail.

## Implementation notes

Fine's published Downward Exclusion condition omits the regular closure of the excluders, which
Champollion and Bernard report as a typo. It is stated here with the closure. The de Morgan laws
are proved by computing the inexact verifiers and the subject-matter of each side, which determine
a regular proposition (`Truthmaker.regularClosure_eq_iff`). Fine states that negation does not see
regular closure for regular propositions only and his de Morgan laws for regular ones, but they
hold without regularity. The law for conjunctions needs no distributivity, only that the conjuncts
have verifiers and that the null state verifies none of them.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [M. Plebani, G. Rosella and V. Saitta, *Truthmakers, Incompatibility, and Modality*
  (2022)][plebani-rosella-saitta-2022]
* [L. Champollion and T. Bernard, *Negation and modality in unilateral truthmaker semantics*
  (2024)][champollion-bernard-2024]
-/

@[expose] public section

open SetFamily

namespace Truthmaker

variable {S : Type*}

/-- A proposition `Q` excludes `P` when every verifier of `Q` excludes a verifier of `P` and every
verifier of `P` is excluded by a verifier of `Q`. -/
def Excludes (excl : S → S → Prop) (Q P : Set S) : Prop :=
  Q ⊆ {q | ∃ p ∈ P, excl q p} ∧ P ⊆ {p | ∃ q ∈ Q, excl q p}

/-! ### Conflict and possibility -/

section Preorder

variable [Preorder S] {excl : S → S → Prop} {s t : S}

theorem isConjunctivePart_iff_excludes {s t : Set S} :
    IsConjunctivePart t s ↔ Excludes (· ≥ ·) s t :=
  Iff.rfl

variable (excl) in
/-- Two states conflict when some part of the first excludes some part of the second. -/
def Conflict (s t : S) : Prop :=
  ∃ s' ≤ s, ∃ t' ≤ t, excl s' t'

theorem Conflict.of_excl (h : excl s t) : Conflict excl s t :=
  ⟨s, le_rfl, t, le_rfl, h⟩

theorem Conflict.mono {s' t' : S} (h : Conflict excl s t) (hs : s ≤ s') (ht : t ≤ t') :
    Conflict excl s' t' :=
  let ⟨a, ha, b, hb, hx⟩ := h
  ⟨a, ha.trans hs, b, hb.trans ht, hx⟩

theorem Conflict.symm [Std.Symm excl] (h : Conflict excl s t) : Conflict excl t s :=
  let ⟨a, ha, b, hb, hx⟩ := h
  ⟨b, hb, a, ha, Std.Symm.symm _ _ hx⟩

variable (excl) in
/-- A state is possible when it does not conflict with itself, and every part of a possible state
is possible. -/
def possible : LowerSet S where
  carrier := {s | ¬ Conflict excl s s}
  lower' := by
    intro s t hts hs hc
    exact hs (hc.mono hts hts)

theorem mem_possible : s ∈ possible excl ↔ ¬ Conflict excl s s :=
  Iff.rfl

theorem mem_possible_iff_forall : s ∈ possible excl ↔ ∀ t ≤ s, ∀ u ≤ s, ¬ Conflict excl t u :=
  ⟨fun hs _ ht _ hu hc ↦ hs (hc.mono ht hu), fun h ↦ h s le_rfl s le_rfl⟩

variable (excl) in
/-- Upward Exclusion holds when a state that excludes `p` excludes every state containing `p`. -/
def UpwardExclusion : Prop :=
  ∀ ⦃q p p' : S⦄, excl q p → p ≤ p' → excl q p'

theorem UpwardExclusion.conflict_iff (hU : UpwardExclusion excl) :
    Conflict excl s t ↔ ∃ s' ≤ s, excl s' t :=
  ⟨fun ⟨a, ha, _, hb, hx⟩ ↦ ⟨a, ha, hU hx hb⟩, fun ⟨a, ha, hx⟩ ↦ ⟨a, ha, t, le_rfl, hx⟩⟩

end Preorder

section SemilatticeSup

variable [SemilatticeSup S] {excl : S → S → Prop} {s t : S}

theorem sup_not_mem_possible (h : excl s t) : s ⊔ t ∉ possible excl :=
  fun hp ↦ hp ((Conflict.of_excl h).mono le_sup_left le_sup_right)

theorem not_conflict_of_sup_mem_possible (h : s ⊔ t ∈ possible excl) : ¬ Conflict excl s t :=
  fun hc ↦ h (hc.mono le_sup_left le_sup_right)

variable (excl) in
/-- Possible Fusion holds when two possible states that do not conflict have a possible
fusion. -/
def PossibleFusion : Prop :=
  ∀ ⦃s : S⦄, s ∈ possible excl → ∀ ⦃t : S⦄, t ∈ possible excl → ¬ Conflict excl s t →
    s ⊔ t ∈ possible excl

theorem possibleFusion_iff : PossibleFusion excl ↔
    ∀ s ∈ possible excl, ∀ t ∈ possible excl, (s ⊔ t ∈ possible excl ↔ ¬ Conflict excl s t) :=
  ⟨fun h _ hs _ ht ↦ ⟨not_conflict_of_sup_mem_possible, fun hc ↦ h hs ht hc⟩,
    fun h _ hs _ ht ↦ (h _ hs _ ht).2⟩

end SemilatticeSup

/-! ### Fine's exclusion conditions and negations -/

section CompleteLattice

variable [CompleteLattice S] {excl : S → S → Prop} {P : Set S}

variable (excl) in
/-- Downward Exclusion holds when every state that excludes the fusion of `P` lies in the regular
closure of the excluders of members of `P`. -/
def DownwardExclusion : Prop :=
  ∀ ⦃P : Set S⦄ ⦃q : S⦄, excl q (sSup P) → q ∈ regularClosure {r | ∃ p ∈ P, excl r p}

variable (excl) in
/-- Null Exclusion holds when the null state neither excludes nor is excluded, and every other
state excludes some state and is excluded by some state. -/
def NullExclusion : Prop :=
  (∀ s : S, ¬ excl ⊥ s ∧ ¬ excl s ⊥) ∧ ∀ s : S, s ≠ ⊥ → (∃ t, excl s t) ∧ ∃ t, excl t s

variable (excl) in
/-- The exclusive negation of `P` is verified by the fusions of propositions that exclude `P`. -/
def exclusiveNeg (P : Set S) : Set S :=
  {q | ∃ Q, Excludes excl Q P ∧ sSup Q = q}

variable (excl) in
/-- The exclusionary negation of `P` is the regular closure of its exclusive negation. -/
def exclusionaryNeg (P : Set S) : Set S :=
  regularClosure (exclusiveNeg excl P)

theorem sSup_image_mem_exclusiveNeg {f : S → S} (hf : ∀ p ∈ P, excl (f p) p) :
    sSup (f '' P) ∈ exclusiveNeg excl P :=
  ⟨f '' P, ⟨Set.forall_mem_image.2 fun p hp ↦ ⟨p, hp, hf p hp⟩,
    fun p hp ↦ ⟨f p, Set.mem_image_of_mem f hp, hf p hp⟩⟩, rfl⟩

theorem exclusiveNeg_nonempty_iff :
    (exclusiveNeg excl P).Nonempty ↔ ∀ p ∈ P, ∃ r, excl r p := by
  refine ⟨fun ⟨_, Q, ⟨_, hPQ⟩, _⟩ p hp ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨q, -, hqp⟩ := hPQ hp
    exact ⟨q, hqp⟩
  · choose! f hf using h
    exact ⟨_, sSup_image_mem_exclusiveNeg hf⟩

theorem exclusiveNeg_nonempty (hN : NullExclusion excl) (hP : ⊥ ∉ P) :
    (exclusiveNeg excl P).Nonempty :=
  exclusiveNeg_nonempty_iff.2 fun p hp ↦ (hN.2 p (ne_of_mem_of_not_mem hp hP)).2

@[simp] theorem exclusiveNeg_empty : exclusiveNeg excl (∅ : Set S) = {⊥} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨∅, ⟨Set.empty_subset _, Set.empty_subset _⟩, by simpa using hx.symm⟩⟩
  rintro ⟨Q, ⟨hQ, -⟩, rfl⟩
  obtain rfl : Q = ∅ := Set.eq_empty_of_forall_notMem fun q hq ↦ by simpa using hQ hq
  simp

theorem mem_upperClosure_exclusiveNeg {x : S} :
    x ∈ upperClosure (exclusiveNeg excl P) ↔ ∀ p ∈ P, ∃ r ≤ x, excl r p := by
  refine ⟨fun h p hp ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, ⟨Q, ⟨-, hPQ⟩, rfl⟩, hle⟩ := mem_upperClosure.1 h
    obtain ⟨q, hq, hqp⟩ := hPQ hp
    exact ⟨q, (le_sSup hq).trans hle, hqp⟩
  · choose! f hfx hf using h
    exact mem_upperClosure.2
      ⟨_, sSup_image_mem_exclusiveNeg hf, sSup_le (Set.forall_mem_image.2 hfx)⟩

theorem coe_upperClosure_exclusiveNeg (hU : UpwardExclusion excl) (P : Set S) :
    (upperClosure (exclusiveNeg excl P) : Set S) = upperPolar (flip (Conflict excl)) P := by
  ext x
  rw [SetLike.mem_coe, mem_upperClosure_exclusiveNeg]
  exact forall₂_congr fun _ _ ↦ hU.conflict_iff.symm

theorem coe_upperClosure_exclusionaryNeg (hU : UpwardExclusion excl) (P : Set S) :
    (upperClosure (exclusionaryNeg excl P) : Set S) = upperPolar (flip (Conflict excl)) P := by
  rw [exclusionaryNeg, upperClosure_regularClosure, coe_upperClosure_exclusiveNeg hU]

theorem sSup_exclusiveNeg (h : ∀ p ∈ P, ∃ r, excl r p) :
    sSup (exclusiveNeg excl P) = sSup {r | ∃ p ∈ P, excl r p} := by
  classical
  choose! f hf using h
  refine le_antisymm (sSup_le fun _ ⟨_, ⟨hQ, _⟩, hQx⟩ ↦ hQx ▸ sSup_le_sSup hQ)
    (sSup_le fun r ⟨p, hp, hrp⟩ ↦ ?_)
  have hg : ∀ p' ∈ P, excl (Function.update f p r p') p' := fun p' hp' ↦ by
    by_cases h : p' = p
    · subst h
      simpa using hrp
    · simpa [h] using hf p' hp'
  calc r = Function.update f p r p := by simp
    _ ≤ sSup (Function.update f p r '' P) := le_sSup (Set.mem_image_of_mem _ hp)
    _ ≤ sSup (exclusiveNeg excl P) := le_sSup (sSup_image_mem_exclusiveNeg hg)

theorem exclusiveNeg_iUnion {ι : Type*} (P : ι → Set S) :
    exclusiveNeg excl (⋃ i, P i) = Set.iSups fun i ↦ exclusiveNeg excl (P i) := by
  ext x
  constructor
  · rintro ⟨Q, ⟨hQ, hPQ⟩, rfl⟩
    refine Set.mem_iSups.2 ⟨fun i ↦ sSup {q ∈ Q | ∃ p ∈ P i, excl q p},
      fun i ↦ ⟨_, ⟨fun q hq ↦ hq.2, fun p hp ↦ ?_⟩, rfl⟩, ?_⟩
    · obtain ⟨q, hq, hqp⟩ := hPQ (Set.mem_iUnion_of_mem i hp)
      exact ⟨q, ⟨hq, p, hp, hqp⟩, hqp⟩
    · rw [← sSup_iUnion]
      congr 1
      ext q
      simp only [Set.mem_iUnion, Set.mem_sep_iff]
      refine ⟨fun ⟨_, hq, _⟩ ↦ hq, fun hq ↦ ?_⟩
      obtain ⟨p, hp, hqp⟩ := hQ hq
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp
      exact ⟨i, hq, p, hpi, hqp⟩
  · intro hx
    obtain ⟨f, hf, rfl⟩ := Set.mem_iSups.1 hx
    choose Q hQ hQf using hf
    refine ⟨⋃ i, Q i, ⟨fun q hq ↦ ?_, fun p hp ↦ ?_⟩, by rw [sSup_iUnion]; exact iSup_congr hQf⟩
    · obtain ⟨i, hqi⟩ := Set.mem_iUnion.1 hq
      obtain ⟨p, hp, hqp⟩ := (hQ i).1 hqi
      exact ⟨p, Set.mem_iUnion_of_mem i hp, hqp⟩
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp
      obtain ⟨q, hq, hqp⟩ := (hQ i).2 hpi
      exact ⟨q, Set.mem_iUnion_of_mem i hq, hqp⟩

theorem exclusionaryNeg_singleton (p : S) :
    exclusionaryNeg excl {p} = regularClosure {q | excl q p} := by
  refine le_antisymm (regularClosure.le_closure_iff.1 ?_) (regularClosure.monotone ?_)
  · rintro _ ⟨Q, ⟨hQ, hpQ⟩, rfl⟩
    obtain ⟨q, hq, hqp⟩ := hpQ (Set.mem_singleton p)
    have hQE : Q ⊆ {q | excl q p} := fun r hr ↦ by
      obtain ⟨_, hp', h⟩ := hQ hr
      rwa [Set.mem_singleton_iff.1 hp'] at h
    exact ⟨mem_upperClosure.2 ⟨q, hqp, le_sSup hq⟩, sSup_le_sSup hQE⟩
  · intro q hq
    refine ⟨{q}, ⟨fun r hr ↦ ⟨p, rfl, Set.mem_singleton_iff.1 hr ▸ hq⟩, fun p' hp' ↦
      ⟨q, rfl, Set.mem_singleton_iff.1 hp' ▸ hq⟩⟩, sSup_singleton⟩

theorem exclusionaryNeg_sups_singleton (hU : UpwardExclusion excl) (hD : DownwardExclusion excl)
    (p q : S) : exclusionaryNeg excl ({p} ⊻ {q}) =
      regularClosure (exclusionaryNeg excl {p} ∪ exclusionaryNeg excl {q}) := by
  rw [Set.singleton_sups_singleton, exclusionaryNeg_singleton, exclusionaryNeg_singleton,
    exclusionaryNeg_singleton]
  refine le_antisymm (regularClosure.le_closure_iff.1 fun r hr ↦ ?_)
    (regularClosure.le_closure_iff.1 (Set.union_subset
      (regularClosure.monotone fun _ h ↦ hU h le_sup_left)
      (regularClosure.monotone fun _ h ↦ hU h le_sup_right)))
  have hr' := hD (P := {p, q}) (q := r) (by rwa [sSup_pair])
  refine regularClosure.monotone ?_ hr'
  rintro x ⟨_, rfl | rfl, hx⟩
  · exact .inl (regularClosure.le_closure _ hx)
  · exact .inr (regularClosure.le_closure _ hx)

theorem exclusionaryNeg_nonempty (hN : NullExclusion excl) (hP : ⊥ ∉ P) :
    (exclusionaryNeg excl P).Nonempty :=
  (exclusiveNeg_nonempty hN hP).mono (regularClosure.le_closure _)

theorem bot_not_mem_exclusionaryNeg (hN : NullExclusion excl) (hP : P.Nonempty) :
    ⊥ ∉ exclusionaryNeg excl P := by
  rintro ⟨h₁, -⟩
  obtain ⟨_, ⟨Q, ⟨-, hPQ⟩, rfl⟩, hle⟩ := mem_upperClosure.1 h₁
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq, hqp⟩ := hPQ hp
  obtain rfl : q = ⊥ := le_bot_iff.1 ((le_sSup hq).trans hle)
  exact (hN.1 p).1 hqp

theorem DownwardExclusion.exists_conflict (hD : DownwardExclusion excl) {s : S}
    (hs : excl s (sSup P)) : ∃ p ∈ P, Conflict excl s p :=
  let ⟨r, ⟨p, hp, hrp⟩, hrs⟩ := mem_upperClosure.1 (hD hs).1
  ⟨p, hp, r, hrs, p, le_rfl, hrp⟩

theorem exists_conflict_of_conflict_sSup (hU : UpwardExclusion excl)
    (hD : DownwardExclusion excl) {x : S} (h : Conflict excl x (sSup P)) :
    ∃ p ∈ P, Conflict excl x p :=
  let ⟨_, hrx, _, ht, hrt⟩ := h
  let ⟨p, hp, hc⟩ := hD.exists_conflict (hU hrt ht)
  ⟨p, hp, hc.mono hrx le_rfl⟩

theorem forall_exists_conflict_iff (hU : UpwardExclusion excl) :
    (∀ ⦃x : S⦄ ⦃P : Set S⦄, Conflict excl x (sSup P) → ∃ p ∈ P, Conflict excl x p) ↔
      ∀ ⦃q : S⦄ ⦃P : Set S⦄, excl q (sSup P) → q ∈ upperClosure {r | ∃ p ∈ P, excl r p} := by
  refine ⟨fun h q P hq ↦ ?_, fun h x P ⟨r, hrx, t, ht, hrt⟩ ↦ ?_⟩
  · obtain ⟨p, hp, hc⟩ := h (Conflict.of_excl hq)
    obtain ⟨r, hrq, hrp⟩ := hU.conflict_iff.1 hc
    exact mem_upperClosure.2 ⟨r, ⟨p, hp, hrp⟩, hrq⟩
  · obtain ⟨r', ⟨p, hp, hr'p⟩, hr'r⟩ := mem_upperClosure.1 (h (hU hrt ht))
    exact ⟨p, hp, r', hr'r.trans hrx, p, le_rfl, hr'p⟩

theorem exclusionaryNeg_regularClosure (hU : UpwardExclusion excl) (hD : DownwardExclusion excl)
    (P : Set S) : exclusionaryNeg excl (regularClosure P) = exclusionaryNeg excl P := by
  have hex : (∀ y ∈ regularClosure P, ∃ r, excl r y) ↔ ∀ p ∈ P, ∃ r, excl r p :=
    ⟨fun h p hp ↦ h p (regularClosure.le_closure P hp), fun h _ hy ↦
      let ⟨p, hp, hpy⟩ := mem_upperClosure.1 hy.1
      let ⟨r, hr⟩ := h p hp
      ⟨r, hU hr hpy⟩⟩
  refine regularClosure_eq_iff.2 ⟨SetLike.ext fun x ↦ ?_, fun hne ↦ ?_⟩
  · rw [mem_upperClosure_exclusiveNeg, mem_upperClosure_exclusiveNeg]
    exact ⟨fun h p hp ↦ h p (regularClosure.le_closure P hp), fun h _ hy ↦
      let ⟨p, hp, hpy⟩ := mem_upperClosure.1 hy.1
      let ⟨r, hrx, hr⟩ := h p hp
      ⟨r, hrx, hU hr hpy⟩⟩
  · have h := exclusiveNeg_nonempty_iff.1 hne
    rw [sSup_exclusiveNeg h, sSup_exclusiveNeg (hex.1 h)]
    exact le_antisymm (sSup_le fun r ⟨_, hy, hry⟩ ↦ (hD (hU hry hy.2)).2)
      (sSup_le_sSup fun r ⟨p, hp, hr⟩ ↦ ⟨p, regularClosure.le_closure P hp, hr⟩)

theorem exclusionaryNeg_iSups {ι : Type*} (hU : UpwardExclusion excl)
    (hD : DownwardExclusion excl) (hN : NullExclusion excl) {P : ι → Set S}
    (hne : ∀ i, (P i).Nonempty) (hP : ∀ i, ⊥ ∉ P i) :
    exclusionaryNeg excl (Set.iSups P) = regularClosure (⋃ i, exclusionaryNeg excl (P i)) := by
  have hcl := regularClosure.closure_iSup_closure fun i ↦ exclusiveNeg excl (P i)
  simp only [Set.iSup_eq_iUnion] at hcl
  rw [exclusionaryNeg, show regularClosure (⋃ i, exclusionaryNeg excl (P i)) = _ from hcl,
    regularClosure_eq_iff]
  refine ⟨SetLike.ext fun x ↦ ?_, fun hex ↦ ?_⟩
  · rw [mem_upperClosure_exclusiveNeg, upperClosure_iUnion, UpperSet.mem_iInf_iff]
    simp only [mem_upperClosure_exclusiveNeg, ← hU.conflict_iff]
    refine ⟨fun h ↦ by_contra fun hcon ↦ ?_, fun ⟨i, hi⟩ y hy ↦ ?_⟩
    · obtain ⟨f, hf⟩ := Set.univ_pi_nonempty_iff.2 fun i ↦
        (show ∃ p ∈ P i, ¬ Conflict excl x p by simpa using not_exists.1 hcon i)
      have hc := h _ (Set.iSup_mem_iSups fun i ↦ (Set.mem_univ_pi.1 hf i).1)
      rw [← sSup_range] at hc
      obtain ⟨_, ⟨i, rfl⟩, hci⟩ := exists_conflict_of_conflict_sSup hU hD hc
      exact (Set.mem_univ_pi.1 hf i).2 hci
    · obtain ⟨f, hf, rfl⟩ := Set.mem_iSups.1 hy
      exact (hi _ (hf i)).mono le_rfl (le_iSup f i)
  · rw [sSup_exclusiveNeg (exclusiveNeg_nonempty_iff.1 hex), sSup_iUnion,
      iSup_congr fun i ↦ sSup_exclusiveNeg (exclusiveNeg_nonempty_iff.1
        (exclusiveNeg_nonempty hN (hP i)))]
    refine le_antisymm (sSup_le fun r ⟨_, hy, hry⟩ ↦ ?_)
      (iSup_le fun i ↦ sSup_le fun r ⟨p, hp, hrp⟩ ↦ ?_)
    · obtain ⟨f, hf, rfl⟩ := Set.mem_iSups.1 hy
      rw [← sSup_range] at hry
      exact (hD hry).2.trans (sSup_le fun r' ⟨_, ⟨i, rfl⟩, hr'⟩ ↦
        le_iSup_of_le i (le_sSup ⟨f i, hf i, hr'⟩))
    · obtain ⟨y, hy, hpy⟩ := Set.exists_mem_iSups_ge hne hp
      exact le_sSup ⟨y, hy, hU hrp hpy⟩

/-! ### Classical exclusion -/

variable (excl) in
/-- An exclusion relation is classical over the possible states `P` when a state is incompatible
with the states it excludes, two incompatible possible states have a part of the first that
excludes the second, and every possible state is compatible with an excluder of each impossible
state. -/
structure ClassicalExclusion (P : LowerSet S) : Prop where
  /-- A state and a state it excludes have an impossible fusion. -/
  sup_not_mem : ∀ ⦃s t : S⦄, excl s t → s ⊔ t ∉ P
  /-- Two possible states with an impossible fusion have a part of the first that excludes the
  second. -/
  exists_le_excl : ∀ ⦃s t : S⦄, s ∈ P → t ∈ P → s ⊔ t ∉ P → ∃ s' ≤ s, excl s' t
  /-- Every possible state has a possible fusion with some excluder of each impossible state. -/
  exists_excl : ∀ ⦃t : S⦄, t ∉ P → ∀ s ∈ P, ∃ t', excl t' t ∧ s ⊔ t' ∈ P

variable {P : LowerSet S}

theorem ClassicalExclusion.exclusive (h : ClassicalExclusion excl P) (p : S) :
    (BilProp.mk {p} (exclusionaryNeg excl {p})).Exclusive P := by
  intro s hs t ht hpt
  rw [Set.mem_singleton_iff.1 hs] at hpt
  replace ht : t ∈ exclusionaryNeg excl {p} := ht
  rw [exclusionaryNeg_singleton] at ht
  obtain ⟨e, he, het⟩ := mem_upperClosure.1 ht.1
  exact h.sup_not_mem he (P.lower ((sup_le_sup_right het p).trans (sup_comm t p).le) hpt)

theorem ClassicalExclusion.exhaustive (h : ClassicalExclusion excl P) (p : S) :
    (BilProp.mk {p} (exclusionaryNeg excl {p})).Exhaustive P := by
  intro s hs
  by_cases hsp : s ⊔ p ∈ P
  · exact .inl ⟨p, rfl, hsp⟩
  refine .inr ?_
  change ∃ t ∈ exclusionaryNeg excl {p}, s ⊔ t ∈ P
  rw [exclusionaryNeg_singleton]
  by_cases hp : p ∈ P
  · obtain ⟨s', hs's, hx⟩ := h.exists_le_excl hs hp hsp
    exact ⟨s', regularClosure.le_closure _ hx, by rwa [sup_eq_left.2 hs's]⟩
  · obtain ⟨t', hx, hst'⟩ := h.exists_excl hp s hs
    exact ⟨t', regularClosure.le_closure _ hx, hst'⟩

end CompleteLattice

section Frame

variable [Order.Frame S] {excl : S → S → Prop}

theorem exclusionaryNeg_regularClosure_iUnion {ι : Type*} (hU : UpwardExclusion excl)
    (hD : DownwardExclusion excl) (hN : NullExclusion excl) {P : ι → Set S}
    (hP : ∀ i, ⊥ ∉ P i) : exclusionaryNeg excl (regularClosure (⋃ i, P i)) =
      Set.iSups fun i ↦ exclusionaryNeg excl (P i) := by
  rw [exclusionaryNeg_regularClosure hU hD, exclusionaryNeg, exclusiveNeg_iUnion,
    regularClosure_iSups fun i ↦ exclusiveNeg_nonempty hN (hP i)]
  rfl

theorem exclusionaryNeg_exclusionaryNeg (hU : UpwardExclusion excl) (hD : DownwardExclusion excl)
    (hN : NullExclusion excl) (h : ∀ p : S, exclusionaryNeg excl (exclusionaryNeg excl {p}) = {p})
    {P : Set S} (hP : regularClosure.IsClosed P) (hP' : ⊥ ∉ P) :
    exclusionaryNeg excl (exclusionaryNeg excl P) = P := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · have h₀ : exclusionaryNeg excl (∅ : Set S) = {⊥} := by
      rw [exclusionaryNeg, exclusiveNeg_empty, regularClosure_singleton]
    rw [h₀, exclusionaryNeg_singleton,
      show {q | excl q ⊥} = ∅ from Set.eq_empty_of_forall_notMem fun q hq ↦ (hN.1 q).2 hq,
      regularClosure_empty]
  have hsingle : ∀ p : P, ⊥ ∉ ({(p : S)} : Set S) := fun p hp ↦
    hP' (Set.mem_singleton_iff.1 hp ▸ p.2)
  have h₁ : exclusionaryNeg excl P = Set.iSups fun p : P ↦ exclusionaryNeg excl {(p : S)} := by
    conv_lhs => rw [← hP.closure_eq, ← Set.iUnion_of_singleton_coe P]
    exact exclusionaryNeg_regularClosure_iUnion hU hD hN hsingle
  rw [h₁, exclusionaryNeg_iSups hU hD hN (fun p ↦ exclusionaryNeg_nonempty hN (hsingle p))
    fun p ↦ bot_not_mem_exclusionaryNeg hN (Set.singleton_nonempty _)]
  simp only [h]
  rw [Set.iUnion_of_singleton_coe, hP.closure_eq]

end Frame

/-! ### The canonical space -/

namespace Canonical

variable {α : Type*}

/-- In the canonical space a literal excludes its mirror image and nothing else holds. -/
def excl (s t : Set (α × Bool)) : Prop :=
  ∃ x, s = {x} ∧ t = {mirror x}

instance : Std.Symm (excl (α := α)) :=
  ⟨fun _ _ ⟨x, hs, ht⟩ ↦ ⟨mirror x, ht, by rw [hs, mirror_mirror]⟩⟩

theorem conflict_excl_iff {s t : Set (α × Bool)} :
    Conflict excl s t ↔ ∃ x ∈ s, mirror x ∈ t := by
  constructor
  · rintro ⟨_, h₁, _, h₂, x, rfl, rfl⟩
    exact ⟨x, h₁ rfl, h₂ rfl⟩
  · rintro ⟨x, hx₁, hx₂⟩
    exact ⟨{x}, Set.singleton_subset_iff.2 hx₁, _, Set.singleton_subset_iff.2 hx₂, x, rfl, rfl⟩

theorem possible_excl : Truthmaker.possible (excl (α := α)) = possible :=
  SetLike.ext fun _ ↦ by
    simp [Truthmaker.mem_possible, conflict_excl_iff, Canonical.mem_possible]

theorem possibleFusion_excl : PossibleFusion (excl (α := α)) := by
  intro s hs t ht hc
  rw [possible_excl] at hs ht ⊢
  rw [conflict_excl_iff] at hc
  rintro x (hx | hx) (hx' | hx')
  · exact hs x hx hx'
  · exact hc ⟨x, hx, hx'⟩
  · exact hc ⟨mirror x, hx', by rwa [mirror_mirror]⟩
  · exact ht x hx hx'

end Canonical

/-! ### Red, blue and green -/

namespace RedBlueGreen

/-- In Fine's example of three colours, red `0`, blue `1` and green `2`, a single colour excludes
every state containing another colour. -/
def excl (s t : Set (Fin 3)) : Prop :=
  ∃ i, s = {i} ∧ ∃ j ∈ t, j ≠ i

theorem exclusionaryNeg_exclusionaryNeg_ne :
    exclusionaryNeg excl (exclusionaryNeg excl {{0}}) ≠ {{0}} := by
  have hblue : ({1} : Set (Fin 3)) ∈ exclusionaryNeg excl {{0}} := by
    rw [exclusionaryNeg_singleton]
    exact regularClosure.le_closure _ ⟨1, rfl, 0, rfl, by decide⟩
  have hmem : sSup ({{0}, {2}} : Set (Set (Fin 3))) ∈
      exclusionaryNeg excl (exclusionaryNeg excl {{0}}) := by
    refine regularClosure.le_closure _ ⟨_, ⟨?_, fun x hx ↦ ?_⟩, rfl⟩
    · rintro _ (rfl | rfl)
      · exact ⟨{1}, hblue, 0, rfl, 1, rfl, by decide⟩
      · exact ⟨{1}, hblue, 2, rfl, 1, rfl, by decide⟩
    · rw [exclusionaryNeg_singleton] at hx
      obtain ⟨_, ⟨i, rfl, j, hj, hji⟩, hix⟩ := mem_upperClosure.1 hx.1
      obtain rfl : j = 0 := hj
      exact ⟨{0}, .inl rfl, 0, rfl, i, hix rfl, fun h ↦ hji h.symm⟩
  intro h
  rw [h, Set.mem_singleton_iff, sSup_pair] at hmem
  have : (2 : Fin 3) ∈ ({0} ⊔ {2} : Set (Fin 3)) := Or.inr rfl
  rw [hmem] at this
  exact absurd this (by decide)

end RedBlueGreen

end Truthmaker
