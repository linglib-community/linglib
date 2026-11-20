module

public import Linglib.Logic.Truthmaker.Exclusion

/-!
# Fine (2017): A theory of truthmaker content I, the unilateral negations

A relation `excl` between states is exclusionary when it satisfies three conditions. Upward
Exclusion: a state that excludes `p` excludes every state containing `p`. Downward Exclusion: a
state that excludes a fusion lies in the regular closure of the excluders of the states fused.
Null Exclusion: the null state neither excludes nor is excluded, and every other state does both.
A proposition `Q` excludes `P` when every verifier of `Q` excludes a verifier of `P` and every
verifier of `P` is excluded by a verifier of `Q` (`Excludes`). The exclusive negation `−P` is
verified by the fusions of the propositions that exclude `P` (`exclusiveNeg`), and the exclusionary
negation `∼P` is its regular closure (`exclusionaryNeg`).

Under Upward Exclusion the states containing a verifier of `∼P` are those that conflict with every
verifier of `P` (`coe_upperClosure_exclusionaryNeg`). Under Upward and Downward Exclusion negation
does not see regular closure (`exclusionaryNeg_regularClosure`), the negation of a disjunction is
the conjunction of the negations (`exclusionaryNeg_regularClosure_iUnion`), and, with Null
Exclusion, the negation of a conjunction of propositions that have verifiers, none of them the
null state, is the disjunction of the negations (`exclusionaryNeg_iSups`). Double negation
restores every regular proposition that the null state does not verify if it restores every single
state (`exclusionaryNeg_exclusionaryNeg`), which it need not
(`RedBlueGreen.exclusionaryNeg_exclusionaryNeg_ne`). Under classical exclusion over a lower set of
possible states (`ClassicalExclusion`), a single state paired with its negation is exclusive and
exhaustive.

Mirror exclusion on the canonical space, where a state with a literal excludes the states
containing the mirror image of each of its literals, satisfies the three conditions
(`Canonical.mirrorExcl`). Under it the law for conjunctions and the lift of double negation fail
for a proposition that the null state verifies (`Canonical.exclusionaryNeg_iSups_ne`,
`Canonical.exclusionaryNeg_exclusionaryNeg_ne`).

## Implementation notes

Downward Exclusion is stated with the regular closure of the set of excluders, the form in which
the proofs of the de Morgan laws apply it. The de Morgan laws are proved by computing the inexact
verifiers and the subject-matter of each side, which determine a regular proposition
(`Truthmaker.regularClosure_eq_iff`). They are stated without the regularity of the propositions
negated. The law for disjunctions needs neither Null Exclusion nor verifiers. The law for
conjunctions needs no distributivity.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
-/

@[expose] public section

open SetFamily Truthmaker
open scoped Bilattice

namespace Fine2017a

variable {S : Type*}

/-- A proposition `Q` excludes `P` when every verifier of `Q` excludes a verifier of `P` and every
verifier of `P` is excluded by a verifier of `Q`. -/
def Excludes (excl : S → S → Prop) (Q P : Set S) : Prop :=
  Q ⊆ {q | ∃ p ∈ P, excl q p} ∧ P ⊆ {p | ∃ q ∈ Q, excl q p}

/-! ### Upward Exclusion -/

section Preorder

variable [Preorder S] {excl : S → S → Prop} {s t : S}

theorem isConjunctivePart_iff_excludes {s t : Set S} :
    IsConjunctivePart t s ↔ Excludes (· ≥ ·) s t :=
  Iff.rfl

variable (excl) in
/-- Upward Exclusion holds when a state that excludes `p` excludes every state containing `p`. -/
def UpwardExclusion : Prop :=
  ∀ ⦃q p p' : S⦄, excl q p → p ≤ p' → excl q p'

theorem UpwardExclusion.conflict_iff (hU : UpwardExclusion excl) :
    Conflict excl s t ↔ ∃ s' ≤ s, excl s' t :=
  ⟨fun ⟨a, ha, _, hb, hx⟩ ↦ ⟨a, ha, hU hx hb⟩, fun ⟨a, ha, hx⟩ ↦ ⟨a, ha, t, le_rfl, hx⟩⟩

end Preorder

/-! ### The exclusion conditions and the negations -/

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
  · obtain ⟨_, ⟨f, hf, rfl⟩, hle⟩ :=
      mem_upperClosure.1 (mem_upperClosure_setOf_sSup_image.2 h)
    exact mem_upperClosure.2 ⟨_, sSup_image_mem_exclusiveNeg hf, hle⟩

theorem coe_upperClosure_exclusiveNeg (hU : UpwardExclusion excl) (P : Set S) :
    (upperClosure (exclusiveNeg excl P) : Set S) = upperPolar (flip (Conflict excl)) P := by
  ext x
  rw [SetLike.mem_coe, mem_upperClosure_exclusiveNeg]
  exact forall₂_congr fun _ _ ↦ hU.conflict_iff.symm

/-- Under Upward Exclusion, the states containing a verifier of the exclusionary negation of `P` are
those that conflict with every verifier of `P`. -/
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
      fun i ↦ ⟨_, ⟨fun q hq ↦ (Set.mem_sep_iff.1 hq).2, fun p hp ↦ ?_⟩, rfl⟩, ?_⟩
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

theorem exclusionaryNeg_eq_empty_of_bot_mem (hN : NullExclusion excl) (hP : ⊥ ∈ P) :
    exclusionaryNeg excl P = ∅ := by
  rw [exclusionaryNeg, Set.eq_empty_of_forall_notMem (s := exclusiveNeg excl P)
    fun _ ⟨_, ⟨_, hPQ⟩, _⟩ ↦ let ⟨_, _, hq⟩ := hPQ hP; (hN.1 _).2 hq, regularClosure_empty]

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

/-- Under Upward, Downward and Null Exclusion, the exclusionary negation of the conjunction of a
family of propositions with verifiers, none verified by the null state, is the disjunction of their
exclusionary negations. -/
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
    · obtain ⟨f, hf⟩ := (Set.univ_pi_nonempty_iff (t := fun i ↦ {p ∈ P i | ¬ Conflict excl x p})).2
        fun i ↦ (show ∃ p ∈ P i, ¬ Conflict excl x p by simpa using not_exists.1 hcon i)
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
    Exclusive P (.mk {p} (exclusionaryNeg excl {p})) := by
  intro s hs t ht hpt
  rw [Set.mem_singleton_iff.1 hs] at hpt
  replace ht : t ∈ exclusionaryNeg excl {p} := ht
  rw [exclusionaryNeg_singleton] at ht
  obtain ⟨e, he, het⟩ := mem_upperClosure.1 ht.1
  exact h.sup_not_mem he (P.lower ((sup_le_sup_right het p).trans (sup_comm t p).le) hpt)

theorem ClassicalExclusion.exhaustive (h : ClassicalExclusion excl P) (p : S) :
    Exhaustive P (.mk {p} (exclusionaryNeg excl {p})) := by
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

/-- In a distributive space, under Upward and Downward Exclusion, the exclusionary negation of the
disjunction of a family of propositions is the conjunction of their exclusionary negations. -/
theorem exclusionaryNeg_regularClosure_iUnion {ι : Type*} (hU : UpwardExclusion excl)
    (hD : DownwardExclusion excl) (P : ι → Set S) :
    exclusionaryNeg excl (regularClosure (⋃ i, P i)) =
      Set.iSups fun i ↦ exclusionaryNeg excl (P i) := by
  rw [exclusionaryNeg_regularClosure hU hD, exclusionaryNeg, exclusiveNeg_iUnion,
    regularClosure_iSups]
  rfl

/-- In a distributive space, under Upward, Downward and Null Exclusion, if double exclusionary
negation restores every single state, it restores every regular proposition that the null state
does not verify. -/
theorem exclusionaryNeg_exclusionaryNeg (hU : UpwardExclusion excl) (hD : DownwardExclusion excl)
    (hN : NullExclusion excl) (h : ∀ p : S, exclusionaryNeg excl (exclusionaryNeg excl {p}) = {p})
    {P : Set S} (hP : IsRegular P) (hP' : ⊥ ∉ P) :
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
    conv_lhs => rw [← hP.regularClosure_eq, ← Set.iUnion_of_singleton_coe P]
    exact exclusionaryNeg_regularClosure_iUnion hU hD _
  rw [h₁, exclusionaryNeg_iSups hU hD hN (fun p ↦ exclusionaryNeg_nonempty hN (hsingle p))
    fun p ↦ bot_not_mem_exclusionaryNeg hN (Set.singleton_nonempty _)]
  simp only [h]
  rw [Set.iUnion_of_singleton_coe, hP.regularClosure_eq]

end Frame

/-! ### Mirror exclusion on the canonical space -/

namespace Canonical

open Truthmaker.Canonical

variable {α : Type*}

/-- In mirror exclusion a state with a literal excludes every state containing the mirror image of
each of its literals. -/
def mirrorExcl (s t : Set (α × Bool)) : Prop :=
  s.Nonempty ∧ ∀ x ∈ s, mirror x ∈ t

theorem upwardExclusion_mirrorExcl : UpwardExclusion (mirrorExcl (α := α)) :=
  fun _ _ _ ⟨hq, h⟩ hp ↦ ⟨hq, fun x hx ↦ hp (h x hx)⟩

theorem downwardExclusion_mirrorExcl : DownwardExclusion (mirrorExcl (α := α)) := by
  intro P q ⟨⟨x, hx⟩, h⟩
  have hE : ∀ y ∈ q, {y} ∈ {r | ∃ p ∈ P, mirrorExcl r p} := fun y hy ↦
    let ⟨p, hp, hyp⟩ := Set.mem_sUnion.1 (h y hy)
    ⟨p, hp, Set.singleton_nonempty y, fun z hz ↦ by rwa [Set.mem_singleton_iff.1 hz]⟩
  exact mem_regularClosure.2 ⟨⟨{x}, hE x hx, Set.singleton_subset_iff.2 hx⟩,
    (fun y hy ↦ Set.mem_sUnion.2 ⟨{y}, hE y hy, rfl⟩ : q ⊆ _)⟩

theorem nullExclusion_mirrorExcl : NullExclusion (mirrorExcl (α := α)) :=
  ⟨fun _ ↦ ⟨fun ⟨⟨_, hx⟩, _⟩ ↦ Set.notMem_empty _ hx,
      fun ⟨⟨x, hx⟩, h⟩ ↦ Set.notMem_empty _ (h x hx)⟩,
    fun s hs ↦
      have hne : s.Nonempty := Set.nonempty_iff_ne_empty.2 hs
      ⟨⟨mirror '' s, hne, fun x hx ↦ Set.mem_image_of_mem _ hx⟩, ⟨mirror '' s, hne.image _,
        fun _ ⟨x, hx, hxy⟩ ↦ by rwa [← hxy, mirror_mirror]⟩⟩⟩

theorem exclusionaryNeg_exclusionaryNeg_singleton (s : Set (α × Bool)) :
    exclusionaryNeg mirrorExcl (exclusionaryNeg mirrorExcl {s}) = {s} := by
  rw [exclusionaryNeg_singleton, exclusionaryNeg_regularClosure upwardExclusion_mirrorExcl
    downwardExclusion_mirrorExcl, exclusionaryNeg]
  suffices h : exclusiveNeg mirrorExcl {t | mirrorExcl t s} = {s} by
    rw [h, regularClosure_singleton]
  have hE : ∀ y ∈ s, mirrorExcl {mirror y} s := fun y hy ↦
    ⟨Set.singleton_nonempty _, fun z hz ↦ by rwa [Set.mem_singleton_iff.1 hz, mirror_mirror]⟩
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨(fun x ↦ {x}) '' s, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨{mirror x}, hE x hx, Set.singleton_nonempty _, fun z hz ↦ ?_⟩
    rw [Set.mem_singleton_iff.1 hz]
    exact Set.mem_singleton _
  · rintro t ⟨⟨y, hy⟩, ht⟩
    refine ⟨{mirror y}, ⟨mirror y, ht y hy, rfl⟩, Set.singleton_nonempty _, fun z hz ↦ ?_⟩
    rwa [Set.mem_singleton_iff.1 hz, mirror_mirror]
  · rw [Set.sSup_eq_sUnion, Set.sUnion_image, Set.biUnion_of_singleton]
  · rintro _ ⟨Q, ⟨hQ, hEQ⟩, rfl⟩
    refine le_antisymm (sSup_le fun q hq z hz ↦ ?_) fun y hy ↦ ?_
    · obtain ⟨t, ht, -, hqt⟩ := hQ hq
      simpa using ht.2 _ (hqt z hz)
    · obtain ⟨q, hq, ⟨z, hz⟩, hqy⟩ := hEQ (hE y hy)
      obtain rfl : z = y := mirror_involutive.injective (Set.mem_singleton_iff.1 (hqy z hz))
      exact Set.mem_sUnion.2 ⟨q, hq, hz⟩

private theorem isRegular_insert_empty_singleton (x : α × Bool) :
    IsRegular ({∅, {x}} : Set (Set (α × Bool))) := by
  refine regularClosure.isClosed_iff_closure_le.2 fun s hs ↦ ?_
  have hs' : s ⊆ {x} := by simpa using (mem_regularClosure.1 hs).2
  rcases Set.subset_singleton_iff_eq.1 hs' with rfl | rfl
  exacts [Set.mem_insert _ _, Set.mem_insert_of_mem _ rfl]

theorem exclusionaryNeg_exclusionaryNeg_ne (b : α) :
    IsRegular ({∅, {(b, true)}} : Set (Set (α × Bool))) ∧
      exclusionaryNeg mirrorExcl (exclusionaryNeg mirrorExcl {∅, {(b, true)}}) ≠
        {∅, {(b, true)}} := by
  refine ⟨isRegular_insert_empty_singleton _, ?_⟩
  rw [exclusionaryNeg_eq_empty_of_bot_mem (P := {∅, {(b, true)}}) nullExclusion_mirrorExcl
    (Set.mem_insert _ _), exclusionaryNeg, exclusiveNeg_empty, regularClosure_singleton]
  intro h
  have hb : ({(b, true)} : Set (α × Bool)) ∈ ({⊥} : Set (Set (α × Bool))) :=
    h ▸ Set.mem_insert_of_mem _ rfl
  exact Set.singleton_ne_empty _ hb

theorem exclusionaryNeg_iSups_ne {a b : α} (hab : a ≠ b) :
    let P : Bool → Set (Set (α × Bool)) := fun i ↦ if i then {∅, {(b, true)}} else {{(a, true)}}
    (∀ i, (P i).Nonempty ∧ IsRegular (P i)) ∧
      exclusionaryNeg mirrorExcl (Set.iSups P) ≠
        regularClosure (⋃ i, exclusionaryNeg mirrorExcl (P i)) := by
  intro P
  refine ⟨fun i ↦ ?_, fun h ↦ ?_⟩
  · cases i
    · exact ⟨Set.singleton_nonempty _, isRegular_singleton _⟩
    · exact ⟨Set.insert_nonempty _ _, isRegular_insert_empty_singleton _⟩
  -- every verifier of `∼{p}`, and so of the disjunction, is part of `p̄`
  have hbound : ∀ x ∈ regularClosure (⋃ i, exclusionaryNeg mirrorExcl (P i)), x ⊆ {(a, false)} := by
    refine fun x hx ↦ (mem_regularClosure.1 hx).2.trans (sSup_le fun y hy ↦ ?_)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    cases i
    · simp only [P, Bool.false_eq_true, ↓reduceIte, exclusionaryNeg_singleton] at hi
      refine (mem_regularClosure.1 hi).2.trans (sSup_le fun r ⟨_, hr⟩ z hz ↦ ?_)
      have : mirror z = (a, true) := hr z hz
      rw [← mirror_mirror z, this]
      rfl
    · simp only [P, ↓reduceIte] at hi
      rw [exclusionaryNeg_eq_empty_of_bot_mem (P := {∅, {(b, true)}}) nullExclusion_mirrorExcl
        (Set.mem_insert _ _)] at hi
      exact hi.elim
  -- `p̄ ⊔ q̄` verifies the negation of the conjunction
  have hpq : sSup ({{(a, false)}, {(b, false)}} : Set (Set (α × Bool))) ∈
      exclusionaryNeg mirrorExcl (Set.iSups P) := by
    refine regularClosure.le_closure _ ⟨_, ⟨?_, fun p hp ↦ ?_⟩, rfl⟩
    · rintro q (rfl | rfl)
      · refine ⟨⨆ i, (if i then ∅ else {(a, true)} : Set (α × Bool)),
          Set.iSup_mem_iSups fun i ↦ by cases i <;> simp [P], Set.singleton_nonempty _, ?_⟩
        rintro _ rfl
        exact Set.mem_iUnion.2 ⟨false, rfl⟩
      · refine ⟨⨆ i, (if i then {(b, true)} else {(a, true)} : Set (α × Bool)),
          Set.iSup_mem_iSups fun i ↦ by cases i <;> simp [P], Set.singleton_nonempty _, ?_⟩
        rintro _ rfl
        exact Set.mem_iUnion.2 ⟨true, rfl⟩
    · obtain ⟨f, hf, rfl⟩ := Set.mem_iSups.1 hp
      have hfa : f false = {(a, true)} := by simpa [P] using hf false
      refine ⟨{(a, false)}, Set.mem_insert _ _, Set.singleton_nonempty _, ?_⟩
      rintro _ rfl
      exact Set.mem_iUnion.2 ⟨false, hfa ▸ rfl⟩
  have hb := hbound _ (h ▸ hpq) (by simp : (b, false) ∈ _)
  exact hab (congrArg Prod.fst (Set.mem_singleton_iff.1 hb)).symm

end Canonical

/-! ### Red, blue and green -/

namespace RedBlueGreen

/-- In Fine's example of three colours, red `0`, blue `1` and green `2`, a single colour excludes
every state containing another colour. -/
def excl (s t : Set (Fin 3)) : Prop :=
  ∃ i, s = {i} ∧ ∃ j ∈ t, j ≠ i

/-- The exclusionary negation of the exclusionary negation of red is not red. -/
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

end Fine2017a
