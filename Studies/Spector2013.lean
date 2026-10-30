module

public import Linglib.Data.Examples.Spector2013
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.Numerals.Basic
public import Mathlib.Order.SuccPred.Nat

/-!
# Spector (2013): Bare Numerals and Scalar Implicatures

Spector compares four accounts of bare numerals: the neo-Gricean account, on which a numeral means
*at least n* and *exactly n* is a scalar implicature; the underspecification account, on which
context picks *at least*, *exactly* or *at most*; Breheny's account, on which a numeral means
*exactly n*; and the ambiguity account, on which it means *at least n* or *exactly n*. On
distributive predicates [Kadmon's rule (7) is the *at least* reading](##collection_iff_atLeast)
and [Geurts's unique-collection entry (42) the *exactly* reading](##uniqueCollection_iff_exactly),
and the exhaustivity operator (45) turns the first into the second. The requirement sentences
(30), (39) and (40) are judged as [their *at least* reading predicts](##requirement_rows): an
*at most* reading would make the Fields-medal sentence true and the *exactly* reading would make
the voting-age sentence false. An *at most* reading arises only as the exact reading strengthened
by background knowledge, so [only where it entails the exact reading](##atMost_eq_exact_inter_iff),
in a downward-entailing environment. Exhaustifying under *whenever*, above a requirement, gives
[the intermediate reading of the professor example](##intermediate_parse_iff).

## Implementation notes

* A numeral's readings are the intervals `Degree.Comparison.interval` of a count or a degree, and
  the lexical entries reach them on the count of `P ∩ Q` in a finite domain.
* A modal environment is the set `A` of values its base allows: a requirement holds when every
  allowed value lies in the reading, `A ⊆ I`, and a permission when one does, `(A ∩ I).Nonempty`.
* The exhaustivity operator (45) is `Exhaustification.exh`. On requirements over the *at least*
  readings it denies the larger numerals (`mem_exh_required_iff`), which on the naturals is the
  next one (`Exhaustification.exhAgainst_lt_iff_succOrder`), as the paper computes (50).
* Prosody, the metalinguistic use of negation and the acquisition and processing evidence the
  paper reviews are not formalized.

## Errata

* p. 284: "In both (36b) and (27)" means (36b) and (37), the obligation to read two papers, as the
  sentence after it shows.

## References

* [spector-2013]
* [horn-1972]
* [carston-1988]
* [breheny-2008]
* [geurts-2006]
* [chierchia-fox-spector-2012]
-/

@[expose] public section

namespace Spector2013

open Degree Exhaustification Numerals Quantifier Set

/-! ### Lexical entries (Sections 2.1, 4 and 6.1) -/

section Entries

variable {α : Type*} {n : ℕ} {P Q : α → Prop}

/-- The rule (7), after Kadmon: *`n` `P` `Q`* holds when some collection of exactly `n`
individuals lies in both `P` and `Q`, the predicates being distributive. -/
def collection (n : ℕ) : Det α := fun P Q ↦ ∃ C ⊆ {x | P x ∧ Q x}, C.ncard = n

/-- Geurts's entry (42): the collection of (7) is unique. -/
def uniqueCollection (n : ℕ) : Det α := fun P Q ↦ ∃! C, C ⊆ {x | P x ∧ Q x} ∧ C.ncard = n

/-- On distributive predicates the rule (7) is the *at least* reading: *three girls went to the
party* (5) says (6), *at least three girls went to the party*. -/
theorem collection_iff_atLeast [Finite α] : collection n P Q ↔ Det.atLeast n P Q :=
  ⟨fun ⟨_, hC, hn⟩ ↦ Det.atLeast_apply.2 (hn ▸ ncard_le_ncard hC),
    fun h ↦ exists_subset_card_eq (Det.atLeast_apply.1 h)⟩

/-- Geurts's entry (42) is the *exactly* reading: *three men came in* (43) is false when more than
three men came in, there being several collections of three. -/
theorem uniqueCollection_iff_exactly [Finite α] (hn : 0 < n) :
    uniqueCollection n P Q ↔ Det.exactly n P Q := by
  rw [Det.exactly_apply]
  refine ⟨fun ⟨C, ⟨hC, hCn⟩, huniq⟩ ↦ ?_, fun h ↦ ⟨_, ⟨subset_rfl, h⟩, fun C ⟨hC, hCn⟩ ↦
    eq_of_subset_of_ncard_le hC (h.trans hCn.symm).le⟩⟩
  by_contra hne
  obtain ⟨x, hx, hxC⟩ := exists_mem_notMem_of_ncard_lt_ncard
    ((ncard_le_ncard hC).lt_of_ne fun h ↦ hne (h.symm.trans hCn))
  obtain ⟨y, hy⟩ := nonempty_of_ncard_ne_zero (hCn.trans_ne hn.ne')
  have := huniq (insert x (C \ {y}))
    ⟨insert_subset hx (sdiff_subset.trans hC), (ncard_exchange hxC hy).trans hCn⟩
  exact hxC (this ▸ mem_insert x _)

-- p. 285: Breheny's weakening, the exact entry with the noun implicitly restricted by some
-- property, is the *at least* reading: *I have exactly four chairs that are P*, for some `P`
theorem exists_exactly_restrict_iff_atLeast [Finite α] :
    (∃ R : α → Prop, Det.exactly n (fun x ↦ P x ∧ R x) Q) ↔ Det.atLeast n P Q := by
  rw [Det.atLeast_apply]
  refine ⟨fun ⟨R, h⟩ ↦ Det.exactly_apply.1 h ▸ ncard_le_ncard fun x hx ↦ ⟨hx.1.1, hx.2⟩,
    fun h ↦ ?_⟩
  obtain ⟨C, hC, hCn⟩ := exists_subset_card_eq h
  refine ⟨(· ∈ C), Det.exactly_apply.2 (Eq.trans (congrArg ncard ?_) hCn)⟩
  ext x
  exact ⟨fun hx ↦ hx.1.2, fun hx ↦ ⟨⟨(hC hx).1, hx⟩, (hC hx).2⟩⟩

end Entries

/-! ### Exhaustification (Section 6.2) -/

-- (45)–(47)
theorem mem_exh_atLeast_iff {k m : ℕ} :
    k ∈ exh (range Comparison.ge.interval) (Comparison.ge.interval m) ↔
      k ∈ Comparison.eq.interval m :=
  mem_exh_range_interval_iff_of_not_isStrict nofun

theorem strictAnti_powerset_atLeast : StrictAnti fun n : ℕ ↦ 𝒫 Comparison.ge.interval n :=
  fun _ _ h ↦ ssubset_iff_subset_not_subset.2 ⟨powerset_mono.2 (Ici_subset_Ici.2 h.le),
    fun h' ↦ h.not_ge (Ici_subset_Ici.1 (powerset_mono.1 h'))⟩

theorem antitone_required (A : Set ℕ) : Antitone fun n ↦ A ⊆ Comparison.ge.interval n :=
  fun _ _ h hA ↦ hA.trans (Ici_subset_Ici.2 h)

theorem antitone_permitted (A : Set ℕ) :
    Antitone fun n ↦ (A ∩ Comparison.ge.interval n).Nonempty :=
  fun _ _ h ↦ Nonempty.mono (inter_subset_inter_right _ (Ici_subset_Ici.2 h))

-- (48)–(50): a requirement, as the set of values it allows, satisfies the exhaustified *we are
-- required to solve `m` problems* when it requires *at least `m`* and not *at least `m + 1`*
theorem mem_exh_required_iff {A : Set ℕ} {m : ℕ} :
    A ∈ exh (range fun n ↦ 𝒫 Comparison.ge.interval n) (𝒫 Comparison.ge.interval m) ↔
      exhAgainst (· < ·) (fun n ↦ A ⊆ Comparison.ge.interval n) m :=
  mem_exh_range_iff_exhAgainst_lt strictAnti_powerset_atLeast m A

/-! ### The neo-Gricean account (Section 2) -/

section NeoGricean

variable {A : Set ℕ} {m : ℕ}

-- (11), (12): under a requirement the wide-scope implicature *not required to solve `m + 1`*
-- follows from the exact reading
theorem necessity_implicature_of_exact (hA : A.Nonempty) (h : A ⊆ Comparison.eq.interval m) :
    exhAgainst (· < ·) (fun n ↦ A ⊆ Comparison.ge.interval n) m := by
  rw [exhAgainst_lt_iff_succOrder (antitone_required A), Order.succ_eq_add_one]
  obtain ⟨k, hk⟩ := hA
  refine ⟨fun j hj ↦ (h hj : j = m).ge, fun hall ↦ ?_⟩
  have h1 : k = m := h hk
  have h2 : m + 1 ≤ k := hall hk
  omega

-- (11), (12): but is weaker than it
theorem necessity_implicature_ne_exact (m : ℕ) :
    ∃ A : Set ℕ, exhAgainst (· < ·) (fun n ↦ A ⊆ Comparison.ge.interval n) m ∧
      ¬ A ⊆ Comparison.eq.interval m := by
  refine ⟨{m, m + 1}, ?_, fun h ↦ ?_⟩
  · rw [exhAgainst_lt_iff_succOrder (antitone_required _), Order.succ_eq_add_one]
    refine ⟨insert_subset (mem_Ici.2 le_rfl) (singleton_subset_iff.2 (mem_Ici.2 (Nat.le_succ m))),
      fun h ↦ ?_⟩
    have : m + 1 ≤ m := h (mem_insert m _)
    omega
  · have : m + 1 = m := h (mem_insert_of_mem _ rfl)
    omega

-- (21), (22): exhaustified against the other numerals, *Peter didn't solve `m + 1` problems*
-- says he solved exactly `m`, an indirect implicature that is not perceived
theorem mem_exh_not_atLeast_iff {k : ℕ} :
    k ∈ exh (range fun j ↦ (Comparison.ge.interval j)ᶜ) (Comparison.ge.interval (m + 1))ᶜ ↔
      k ∈ Comparison.eq.interval m := by
  have h : (fun j ↦ (Comparison.ge.interval j)ᶜ) = (Comparison.lt.interval : ℕ → Set ℕ) :=
    funext fun _ ↦ compl_Ici
  rw [h, show (Comparison.ge.interval (m + 1))ᶜ = Comparison.lt.interval (m + 1) from compl_Ici,
    mem_exh_range_interval_lt_iff, Nat.covBy_iff_add_one_eq]
  simp

-- (19), (20): the *at most* reading of the tax-exemption conditional does not entail (20), which
-- its literal *at least* reading entails, so no strengthening of the literal reading reaches it
theorem atMost_reading_not_entails_literal (m : ℕ) :
    ∃ qualifies : ℕ → Prop, (∀ k ∈ Comparison.le.interval m, ¬ qualifies k) ∧
      ¬ ∀ k ∈ Comparison.gt.interval m, ¬ qualifies k :=
  ⟨(m < ·), fun _ hk h ↦ not_lt.2 hk h, fun h ↦ h (m + 1) (Nat.lt_succ_self m) (Nat.lt_succ_self m)⟩

end NeoGricean

/-! ### The underspecification account (Section 3) -/

-- (25b), (27b): on the *at most* entry (26) the permission holds of any small allowed value
theorem permitted_atMost_of_le {A : Set ℕ} {k m : ℕ} (hk : k ∈ A) (h : k ≤ m) :
    (A ∩ Comparison.le.interval m).Nonempty :=
  ⟨k, hk, h⟩

-- (28), (29): the neo-Gricean reading of (25b) is its intended *at most* paraphrase
theorem permitted_implicature_iff (A : Set ℕ) (m : ℕ) :
    exhAgainst (· < ·) (fun n ↦ (A ∩ Comparison.ge.interval n).Nonempty) m ↔
      (A ∩ Comparison.ge.interval m).Nonempty ∧ A ⊆ Comparison.le.interval m := by
  rw [exhAgainst_lt_iff_succOrder (antitone_permitted A), Order.succ_eq_add_one]
  refine and_congr_right' ⟨fun h k hk ↦ ?_, fun h ⟨k, hk, hk'⟩ ↦ ?_⟩
  · by_contra hkm
    exact h ⟨k, hk, show m + 1 ≤ k by have : ¬ k ≤ m := hkm; omega⟩
  · have h1 : k ≤ m := h hk
    have h2 : m + 1 ≤ k := hk'
    omega

/-- The ages at which one may vote, the context of (30a) and (39). -/
def votingAges : Set ℕ := Ici 18

/-- The ages at which one is eligible for the Fields medal, the context of (30b). -/
def fieldsMedalAges : Set ℕ := Iic 40

/-- The heights at which one may be hired in the military, the context of (40). -/
def militaryHeights : Set ℕ := Ici 6

/-- The requirement sentences (30a), (30b), (39) and (40) are judged as their *at least* reading
predicts; an *at most* reading would make (30b) true, and the *exactly* reading would make (30a),
(39) and (40) false. -/
theorem requirement_rows :
    (votingAges ⊆ Comparison.ge.interval 18 ↔
      Examples.ex30a.verdict = some true) ∧
    (fieldsMedalAges ⊆ Comparison.ge.interval 40 ↔
      Examples.ex30b.verdict = some true) ∧
    (votingAges ⊆ Comparison.ge.interval 18 ↔
      Examples.ex39.verdict = some true) ∧
    (militaryHeights ⊆ Comparison.ge.interval 6 ↔
      Examples.ex40.verdict = some true) ∧
    fieldsMedalAges ⊆ Comparison.le.interval 40 ∧
    ¬ votingAges ⊆ Comparison.eq.interval 18 ∧ ¬ militaryHeights ⊆ Comparison.eq.interval 6 := by
  refine ⟨iff_of_true subset_rfl (by decide), iff_of_false (fun h ↦ ?_) (by decide),
    iff_of_true subset_rfl (by decide), iff_of_true subset_rfl (by decide), subset_rfl,
    fun h ↦ ?_, fun h ↦ ?_⟩
  · have : 40 ≤ 0 := h (Nat.zero_le 40)
    omega
  · have : 19 = 18 := h (Nat.le_succ 18)
    omega
  · have : 7 = 6 := h (Nat.le_succ 6)
    omega

/-! ### The exactly-only account (Section 4) -/

-- (31)–(35): with the background knowledge that qualifying grows with the number of children, the
-- exact reading of the conditional extends downward to *at most* and upward to *at least*
theorem exact_extends_downward {B : ℕ → Prop} (hB : Monotone B) {m : ℕ} (h : ¬ B m) :
    ∀ k ∈ Comparison.le.interval m, ¬ B k :=
  fun _ hk hBk ↦ h (hB hk hBk)

theorem exact_extends_upward {B : ℕ → Prop} (hB : Monotone B) {m : ℕ} (h : B m) :
    ∀ k ∈ Comparison.ge.interval m, B k :=
  fun _ hk ↦ hB hk h

-- (36b), pp. 284–285: the discourse is consistent on the *at least* reading of *four*, and the
-- exact reading strengthened by any background `B` stays inconsistent with *five*
theorem chairs_row (B : Set ℕ) :
    ((Comparison.ge.interval 4 ∩ Comparison.ge.interval 5).Nonempty ↔
      Examples.ex36b.judgment = .acceptable) ∧
    Comparison.eq.interval 4 ∩ B ∩ Comparison.ge.interval 5 = ∅ :=
  ⟨iff_of_true ⟨5, Nat.le_succ 4, mem_Ici.2 le_rfl⟩ rfl,
    eq_empty_of_forall_notMem fun k ⟨⟨h4, _⟩, h5⟩ ↦ by
      have h4 : k = 4 := h4
      have h5 : 5 ≤ k := h5
      omega⟩

-- (39), (40): exhaustified, a requirement of an *at least* reading names the least allowed value,
-- on any scale of degrees
theorem exhAgainst_required_Ici_iff {D : Type*} [PartialOrder D] {n m : D} :
    exhAgainst (· < ·) (fun k ↦ Ici n ⊆ Comparison.ge.interval k) m ↔ n = m :=
  exhAgainst_lt_iff_maximal.trans <| by simp [eq_comm]

/-! ### The ambiguity account (Section 5) -/

section Ambiguity

variable {W : Type*}

/-- (41c): an *at most* reading arises only as the exact reading conjoined with background
knowledge, so only where it entails the exact reading. -/
theorem atMost_eq_exact_inter_iff (C : Set ℕ → Set W) (m : ℕ) :
    (∃ B, C (Comparison.le.interval m) = C (Comparison.eq.interval m) ∩ B) ↔
      C (Comparison.le.interval m) ⊆ C (Comparison.eq.interval m) :=
  ⟨fun ⟨_, h⟩ ↦ h ▸ inter_subset_left, fun h ↦ ⟨_, (inter_eq_right.2 h).symm⟩⟩

-- p. 287: in a downward-entailing environment it does: *nobody read four books or fewer* entails
-- *nobody read exactly four books*
theorem atMost_subset_exact_of_antitone {C : Set ℕ → Set W} (hC : Antitone C) (m : ℕ) :
    C (Comparison.le.interval m) ⊆ C (Comparison.eq.interval m) :=
  hC (singleton_subset_iff.2 (mem_Iic.2 le_rfl))

-- p. 287: unembedded it does not: *John read four or fewer books* does not entail *exactly four*
theorem not_atMost_subset_exact {m : ℕ} (hm : 0 < m) :
    ¬ Comparison.le.interval m ⊆ Comparison.eq.interval m :=
  fun h ↦ hm.ne (h (Nat.zero_le m) : 0 = m)

end Ambiguity

/-! ### Intermediate implicatures (Section 6.2) -/

section Intermediate

variable {S : Type*} (n : S → ℕ) (managed : S → Prop) (m : ℕ)

-- (53a): on the *at least* parse the first conjunct contradicts the second whenever some exam
-- demanded more than `m`
theorem atLeast_parse_contradiction
    (h : ∀ s, Ici (n s) ⊆ Comparison.ge.interval m → managed s) :
    ¬ ∃ s, m < n s ∧ ¬ managed s :=
  fun ⟨s, hs, hm⟩ ↦ hm (h s (Ici_subset_Ici.2 hs.le))

-- (53a): on the *exactly* parse the sentence speaks only of exams the context excludes
theorem exact_parse_vacuous (s : S) : ¬ Ici (n s) ⊆ Comparison.eq.interval m := fun h ↦ by
  have h1 : n s = m := h self_mem_Ici
  have h2 : n s + 1 = m := h (Nat.le_succ (n s))
  omega

/-- The intended parse (53b) of the professor example, exhaustification under *whenever* and
above the demand, restricts the first conjunct to the exams whose least demand is `m` (54). -/
theorem intermediate_parse_iff :
    (∀ s, exhAgainst (· < ·) (fun k ↦ Ici (n s) ⊆ Comparison.ge.interval k) m → managed s) ↔
      ∀ s, n s = m → managed s := by
  simp only [exhAgainst_required_Ici_iff]

-- (53), (54): with an exam for each least demand and success up to `m`, the intended parse is
-- consistent with the second conjunct and the *at least* parse is not
theorem intermediate_parse_consistent :
    (∀ s : ℕ, exhAgainst (· < ·) (fun k ↦ Ici s ⊆ Comparison.ge.interval k) m → s ≤ m) ∧
      (∀ s, m < s → ¬ s ≤ m) ∧ ¬ ∀ s : ℕ, Ici s ⊆ Comparison.ge.interval m → s ≤ m :=
  ⟨(intermediate_parse_iff id (· ≤ m) m).2 fun _ h ↦ h.le, fun _ h ↦ not_le.2 h,
    fun h ↦ atLeast_parse_contradiction id (· ≤ m) m h ⟨m + 1, Nat.lt_succ_self m, by omega⟩⟩

end Intermediate

end Spector2013
