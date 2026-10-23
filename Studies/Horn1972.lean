module

public import Linglib.Data.Examples.Horn1972
public import Linglib.Semantics.Degree.Comparison
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Fin.Rev

/-!
# Horn (1972): On the Semantic Properties of Logical Operators in English

This file formalizes [horn-1972]'s account of scalar predicates and of the lexicalization of
negated operators. A scale is a strict chain of propositions, each entailing the weaker ones
(`IsScale`); asserting a member asserts its lower bound and conversationally implicates the
negation of the stronger members, so that *some* implicates *not all*, a cardinal *n* asserts
at least *n* and implicates at most *n*, and *or* implicates *not and*. The implicature can be
asserted, contradicted or suspended, and suspension (*warm, if not hot*) is possible only by a
stronger member (`suspends_iff_lt`); of the stronger members, the further up the scale the
negated one lies, the safer the inference (`safer_of_le`), and the negation of the strongest is
forced. The relation between *some* and *not all* is implicature rather than entailment: the
two conjoin without redundancy and *some* is consistent with *all*.

Chapter 4 derives the missing O corner of Aristotle's square. An operator is *compatible* with
a lower negation when `Q φ` and `Q ¬φ` can hold together (`Compatible`); on the quantifier
scale this holds below the midpoint (*some*, *half*) and fails above it (*most*, *all*), and
for monotone quantifiers the compatibility of `Q` excludes that of its contradictory
(`not_compatible_compl`). The lexicalization hypotheses (4.59) and (4.62) let an outer
negation `~Q` lexicalize iff `Q` is compatible and an inner negation `Q~` iff it is not, so
*none* arises both as `~some` and as `all~` while `~all = some~` has no route
(`o_corner_unlexicalizable`); the connectives pattern alike, with *nor* but no *nand*.

## Implementation notes

* Quantifiers are conditions on the number of satisfiers out of a domain of size `n`, the
  operational procedure of (4.55); *many* and *few*, which depend on an expected size, are
  left out. Cardinals use the numeral substrate's lower-bound readings, and the connectives a
  four-world model of two disjuncts (`ConnWorld`).
* The modal and deontic scales, the polarity facts of Chapter 3 and the presupposition theory
  of Section 1.1 are not formalized, and with them their example rows, the understatement and
  anomaly judgments of Section 2.5 and the intonation rows among them.
* The example rows are read by the `…_rows` theorems, each judgment beside the fact that
  derives it, the quantifiers on a domain of four individuals.

## References

* [horn-1972]
-/

@[expose] public section

namespace Horn1972

open Degree

variable {W : Type*} {n : ℕ}

/-! ### Scalar predicates -/

/-- A scale of propositions ordered from weakest to strongest: each strictly entails the weaker
ones. -/
def IsScale (P : Fin (n + 1) → Set W) : Prop := StrictAnti P

variable {P : Fin (n + 1) → Set W}

/-- The stronger member entails the weaker. -/
theorem IsScale.subset (h : IsScale P) {i j : Fin (n + 1)} (hij : i ≤ j) : P j ⊆ P i :=
  h.antitone hij

/-- Asserting the upper-bound implicature of `P i` against `P j`, *only P i*, the first of the
constructions of (1.73). -/
def assertBound (P : Fin (n + 1) → Set W) (i j : Fin (n + 1)) : Set W := P i \ P j

theorem assertBound_subset (i j : Fin (n + 1)) : assertBound P i j ⊆ P i := Set.sdiff_subset

theorem assertBound_disjoint (i j : Fin (n + 1)) : Disjoint (assertBound P i j) (P j) :=
  Set.disjoint_sdiff_left

/-- Suspension, *P i, if not P j*, admits a member without asserting it and is possible only by
a stronger one: *hot, if not warm* is out. -/
theorem suspends_iff_lt (h : IsScale P) (i j : Fin (n + 1)) : P j ⊂ P i ↔ i < j :=
  ⟨λ hlt => not_le.mp λ hji => hlt.not_subset (h.subset hji), λ hij => h hij⟩

/-- (2.69iii): among the stronger members, negating one further up the scale is the safer
inference, since it excludes less. -/
theorem safer_of_le (h : IsScale P) (i : Fin (n + 1)) {j k : Fin (n + 1)} (hjk : j ≤ k) :
    assertBound P i j ⊆ assertBound P i k :=
  Set.sdiff_subset_sdiff_right (h.subset hjk)

theorem compl_subset_compl_last (h : IsScale P) (j : Fin (n + 1)) :
    (P j)ᶜ ⊆ (P (Fin.last n))ᶜ :=
  Set.compl_subset_compl.mpr (h.subset (Fin.le_last j))

/-- The redundancy test (2.21): *P and Q* is redundant when `P ∧ ¬Q` is contradictory, which
is when `P` entails `Q`. -/
def Redundant (p q : Set W) : Prop := p ∩ qᶜ = ∅

theorem redundant_iff_subset (p q : Set W) : Redundant p q ↔ p ⊆ q := by
  rw [Redundant, ← Set.sdiff_eq, Set.sdiff_eq_empty]

/-! ### Cardinal numbers (Section 1.21) -/

theorem atLeast_succ_ssubset (m : ℕ) :
    Comparison.ge.interval (m + 1) ⊂ Comparison.ge.interval m :=
  Set.Ici_ssubset_Ici.2 m.lt_succ_self

/-- (1.59b): negating a cardinal contradicts its lower bound, *fewer than m*. -/
theorem compl_atLeast_eq_fewerThan (m : ℕ) :
    (Comparison.ge.interval m)ᶜ = Comparison.lt.interval m :=
  Set.compl_Ici

theorem bare_eq_atLeast_inter_atMost (m : ℕ) :
    Comparison.eq.interval m = Comparison.ge.interval m ∩ Comparison.le.interval m := by
  simp [Set.Ici_inter_Iic]

/-- (1.60a): *I have three children, in fact more* is consistent, so the upper bound is no
entailment. -/
theorem atLeast_consistent_with_more (m : ℕ) :
    (Comparison.ge.interval m ∩ Comparison.gt.interval m).Nonempty :=
  ⟨m + 1, by simp⟩

/-- (1.60b): *I have only three children, in fact fewer* is contradictory, since *only* asserts
the upper bound. -/
theorem only_inconsistent_with_fewer (m : ℕ) :
    Disjoint (Comparison.ge.interval m ∩ Comparison.le.interval m) (Comparison.lt.interval m) := by
  simp [Set.Ici_inter_Iic]

/-! ### The quantificational scale (Section 2.1) -/

/-- The quantifiers as conditions on the number of satisfiers among `n` individuals. -/
def someQ (n : ℕ) : Set (Fin (n + 1)) := {c | 1 ≤ c.val}

def halfQ (n : ℕ) : Set (Fin (n + 1)) := {c | n ≤ 2 * c.val}

def mostQ (n : ℕ) : Set (Fin (n + 1)) := {c | n < 2 * c.val}

def allQ (n : ℕ) : Set (Fin (n + 1)) := {c | c.val = n}

def noneQ (n : ℕ) : Set (Fin (n + 1)) := {c | c.val = 0}

def notAllQ (n : ℕ) : Set (Fin (n + 1)) := {c | c.val ≠ n}

instance : DecidablePred (· ∈ someQ n) := fun c ↦ decidable_of_iff (1 ≤ c.val) Iff.rfl

instance : DecidablePred (· ∈ halfQ n) := fun c ↦ decidable_of_iff (n ≤ 2 * c.val) Iff.rfl

instance : DecidablePred (· ∈ mostQ n) := fun c ↦ decidable_of_iff (n < 2 * c.val) Iff.rfl

instance : DecidablePred (· ∈ allQ n) := fun c ↦ decidable_of_iff (c.val = n) Iff.rfl

/-- The positive scale (2.4a) on its proportional members: on a domain of at least three
individuals *all* strictly entails *most*, which strictly entails *some*. -/
theorem allQ_ssubset_mostQ (hn : 3 ≤ n) : allQ n ⊂ mostQ n :=
  ⟨λ c hc => by simp only [allQ, mostQ, Set.mem_ofPred_eq] at hc ⊢; omega, λ h => by
    have := h (a := ⟨n - 1, by omega⟩) (by simp only [mostQ, Set.mem_ofPred_eq]; omega)
    simp only [allQ, Set.mem_ofPred_eq] at this; omega⟩

theorem mostQ_ssubset_someQ (hn : 2 ≤ n) : mostQ n ⊂ someQ n :=
  ⟨λ c hc => by simp only [someQ, mostQ, Set.mem_ofPred_eq] at hc ⊢; omega, λ h => by
    have := h (a := ⟨1, by omega⟩) (by simp only [someQ, Set.mem_ofPred_eq]; omega)
    simp only [mostQ, Set.mem_ofPred_eq] at this; omega⟩

theorem allQ_subset_someQ (hn : 1 ≤ n) : allQ n ⊆ someQ n := λ c hc => by
  simp only [allQ, Set.mem_ofPred_eq] at hc; simp only [someQ, Set.mem_ofPred_eq]; omega

theorem someQ_not_subset_notAllQ (hn : 1 ≤ n) : ¬ someQ n ⊆ notAllQ n := λ h =>
  h (a := Fin.last n) (by simp [someQ]; omega) (by simp)

/-- (2.24b): *some but not all* is not redundant, so *not all* is an implicature of *some*
rather than an entailment. -/
theorem some_notAll_not_redundant (hn : 1 ≤ n) : ¬ Redundant (someQ n) (notAllQ n) := by
  rw [redundant_iff_subset]; exact someQ_not_subset_notAllQ hn

/-- (2.24a): *somebody left, in fact everyone did* is consistent. -/
theorem someQ_inter_allQ_nonempty (hn : 1 ≤ n) : (someQ n ∩ allQ n).Nonempty :=
  ⟨Fin.last n, by simp [someQ]; omega, by simp [allQ]⟩

/-! ### Aristotle's square and the compatibility with a lower negation (Chapter 4) -/

/-- `Q` applied to the complement predicate: the count of satisfiers becomes `n - c`. -/
def innerNeg (Q : Set (Fin (n + 1))) : Set (Fin (n + 1)) := {c | Fin.rev c ∈ Q}

theorem compl_someQ : (someQ n)ᶜ = noneQ n := by
  ext c; simp [someQ, noneQ]

theorem innerNeg_allQ : innerNeg (allQ n) = noneQ n := by
  ext c; simp only [innerNeg, allQ, noneQ, Set.mem_ofPred_eq, Fin.val_rev]; omega

theorem compl_allQ : (allQ n)ᶜ = notAllQ n := by
  ext c; simp [allQ, notAllQ]

theorem innerNeg_someQ : innerNeg (someQ n) = notAllQ n := by
  ext c; simp only [innerNeg, someQ, notAllQ, Set.mem_ofPred_eq, Fin.val_rev]; omega

theorem allQ_disjoint_noneQ (hn : 1 ≤ n) : Disjoint (allQ n) (noneQ n) :=
  Set.disjoint_left.mpr λ c hc hc' => by
    simp only [allQ, noneQ, Set.mem_ofPred_eq] at hc hc'; omega

theorem someQ_union_notAllQ (hn : 1 ≤ n) : someQ n ∪ notAllQ n = Set.univ := by
  ext c; simp only [someQ, notAllQ, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  omega

/-- (4.55): `Q φ` and `Q ¬φ` are compatible when some count puts both a predicate and its
complement into `Q`. -/
def Compatible (Q : Set (Fin (n + 1))) : Prop := ∃ c, c ∈ Q ∧ Fin.rev c ∈ Q

instance (Q : Set (Fin (n + 1))) [DecidablePred (· ∈ Q)] : Decidable (Compatible Q) :=
  inferInstanceAs (Decidable (∃ c, c ∈ Q ∧ _ ∈ Q))

theorem someQ_compatible (hn : 2 ≤ n) : Compatible (someQ n) :=
  ⟨⟨1, by omega⟩, by simp [someQ], by simp [someQ, Fin.val_rev]; omega⟩

theorem halfQ_compatible (k : ℕ) : Compatible (halfQ (2 * k)) :=
  ⟨⟨k, by omega⟩, by simp [halfQ], by simp [halfQ, Fin.val_rev]; omega⟩

theorem mostQ_not_compatible : ¬ Compatible (mostQ n) := by
  rintro ⟨c, hc, hc'⟩
  simp only [mostQ, Set.mem_ofPred_eq, Fin.val_rev] at hc hc'
  omega

theorem allQ_not_compatible (hn : 1 ≤ n) : ¬ Compatible (allQ n) := by
  rintro ⟨c, hc, hc'⟩
  simp only [allQ, Set.mem_ofPred_eq, Fin.val_rev] at hc hc'
  omega

/-- A quantifier that is monotone in the count. -/
def IsUpward (Q : Set (Fin (n + 1))) : Prop := ∀ c d, c ≤ d → c ∈ Q → d ∈ Q

theorem not_compatible_compl {Q : Set (Fin (n + 1))} (hQ : IsUpward Q) (h : Compatible Q) :
    ¬ Compatible Qᶜ := by
  rintro ⟨d, hd, hd'⟩
  obtain ⟨c, hc, hc'⟩ := h
  have h1 : ¬ c ≤ d := λ hcd => hd (hQ c d hcd hc)
  have h2 : ¬ Fin.rev c ≤ Fin.rev d := λ hcd => hd' (hQ _ _ hcd hc')
  simp only [Fin.le_def, Fin.val_rev, not_le] at h1 h2
  omega

/-- (4.59ii) and (4.62ii): an outer negation `~Q` lexicalizes iff `Q` is compatible with a
lower negation. -/
def OuterNegationLexicalizes (Q : Set (Fin (n + 1))) : Prop := Compatible Q

/-- (4.59iii) and (4.62i): an inner negation `Q~` lexicalizes iff `Q` is not compatible. -/
def InnerNegationLexicalizes (Q : Set (Fin (n + 1))) : Prop := ¬ Compatible Q

theorem e_corner_lexicalizable (hn : 2 ≤ n) :
    OuterNegationLexicalizes (someQ n) ∧ InnerNegationLexicalizes (allQ n) :=
  ⟨someQ_compatible hn, allQ_not_compatible (by omega)⟩

theorem o_corner_unlexicalizable (hn : 2 ≤ n) :
    ¬ OuterNegationLexicalizes (allQ n) ∧ ¬ InnerNegationLexicalizes (someQ n) :=
  ⟨allQ_not_compatible (by omega), not_not.mpr (someQ_compatible hn)⟩

/-! ### The connectives (Sections 2.13 and 4.23) -/

/-- The worlds of two disjuncts: which of them hold. -/
inductive ConnWorld where
  | neither
  | onlyA
  | onlyB
  | both
  deriving DecidableEq, Repr

/-- *A or B*, inclusive. -/
def orConn : ConnWorld → Prop
  | .neither => False
  | _ => True

/-- *A and B*. -/
def andConn : ConnWorld → Prop
  | .both => True
  | _ => False

/-- Negating both disjuncts. -/
def ConnWorld.swap : ConnWorld → ConnWorld
  | .neither => .both
  | .onlyA => .onlyB
  | .onlyB => .onlyA
  | .both => .neither

/-- Compatibility with a lower negation for a connective. -/
def CompatibleConn (C : ConnWorld → Prop) : Prop := ∃ w, C w ∧ C (ConnWorld.swap w)

theorem orConn_compatible : CompatibleConn orConn := ⟨.onlyA, trivial, trivial⟩

theorem andConn_not_compatible : ¬ CompatibleConn andConn := by
  rintro ⟨w, hw, hw'⟩; cases w <;> simp [andConn, ConnWorld.swap] at hw hw'

/-- (2.46)–(2.48): *and* entails *or*, and *or* implicates rather than entails *not and*, the
implicature being cancelled by *or both*. -/
theorem orConn_not_subset_compl_andConn : ¬ ∀ w, orConn w → ¬ andConn w :=
  λ h => h .both trivial trivial

/-! ### The data

The judgments of the example rows, each beside the fact that derives it: the cardinal rows of
Section 1.21, the connective scale of Section 2.13, and the compatibility and lexicalization
rows of Chapter 4 on a domain of four individuals. -/

section Data

open Examples

/-- The cardinal rows of Section 1.21: *three* asserts its lower bound and implicates the upper,
(1.59); suspension runs up the scale only, (1.58b); *in fact more* cancels the implicature while
*only three, in fact fewer* contradicts an assertion, (1.60). -/
theorem cardinal_rows :
    (ex1_59a.judgment = .acceptable ∧
      Comparison.eq.interval 3 = Comparison.ge.interval 3 ∩ Comparison.le.interval 3) ∧
    (ex1_59b.judgment = .acceptable ∧
      (Comparison.ge.interval 3)ᶜ = Comparison.lt.interval 3) ∧
    (ex1_58b_more.judgment = .acceptable ∧
      Comparison.ge.interval 4 ⊂ Comparison.ge.interval 3) ∧
    (ex1_58b_fewer.judgment = .ungrammatical ∧
      ¬ Comparison.ge.interval 2 ⊂ Comparison.ge.interval 3) ∧
    (ex1_60a.judgment = .acceptable ∧
      (Comparison.ge.interval 3 ∩ Comparison.gt.interval 3).Nonempty) ∧
    (ex1_60b.judgment = .ungrammatical ∧
      Disjoint (Comparison.ge.interval 3 ∩ Comparison.le.interval 3)
        (Comparison.lt.interval 3)) :=
  ⟨⟨rfl, bare_eq_atLeast_inter_atMost 3⟩, ⟨rfl, compl_atLeast_eq_fewerThan 3⟩,
    ⟨rfl, atLeast_succ_ssubset 3⟩, ⟨rfl, ssubset_asymm (atLeast_succ_ssubset 2)⟩,
    ⟨rfl, atLeast_consistent_with_more 3⟩, ⟨rfl, only_inconsistent_with_fewer 3⟩⟩

/-- (2.46): *and* entails *or*, and *or* only implicates *not and*, since the world of both
disjuncts verifies *or*. -/
theorem connective_scale_row :
    ex2_46.judgment = .acceptable ∧ (∀ w, andConn w → orConn w) ∧
      ¬ ∀ w, orConn w → ¬ andConn w :=
  ⟨rfl, fun w hw ↦ by cases w <;> simp_all [andConn, orConn],
    orConn_not_subset_compl_andConn⟩

/-- The quantifiers the rows name. -/
inductive RowQuantifier where
  | all | most | half | some
  deriving DecidableEq, Repr

/-- A row quantifier as a condition on counts, on a domain of four individuals. -/
def RowQuantifier.set : RowQuantifier → Set (Fin 5)
  | .all => allQ 4
  | .most => mostQ 4
  | .half => halfQ 4
  | .some => someQ 4

instance (q : RowQuantifier) : Decidable (Compatible q.set) :=
  match q with
  | .all => inferInstanceAs (Decidable (Compatible (allQ 4)))
  | .most => inferInstanceAs (Decidable (Compatible (mostQ 4)))
  | .half => inferInstanceAs (Decidable (Compatible (halfQ 4)))
  | .some => inferInstanceAs (Decidable (Compatible (someQ 4)))

/-- The quantifier a row's `quantifier` feature names. -/
def quantifier? (e : Datum) : Option RowQuantifier :=
  e.parse? "quantifier"
    [("all", .all), ("most", .most), ("half", .half), ("some", .some)]

/-- The lower-negation rows (4.56) and the *some* of (4.60a): a row is acceptable exactly where
its quantifier is compatible with a lower negation. -/
theorem compatibility_rows :
    ∀ e ∈ Examples.all, e.Fits quantifier? fun q ↦ .ofProp (Compatible q.set) := by
  decide

theorem compatibility_read : Datum.ReadCount quantifier? Examples.all 5 := by decide

/-- (4.57): whatever expected size *many* demands, it is monotone in the count, so *many* and
*not many* cannot both accept a lower negation (`not_compatible_compl`), and the pair splits as
the judgments do. -/
theorem many_rows {Q : Set (Fin (n + 1))} (hQ : IsUpward Q) :
    ex4_57a.judgment = .acceptable ∧
      ex4_57a_prime.judgment = .ungrammatical ∧
      (Compatible Q → ¬ Compatible Qᶜ) :=
  ⟨rfl, rfl, not_compatible_compl hQ⟩

/-- The lexicalization rows: *nor* and *neither* are *and* and *both* over negated disjuncts and
exist since *and* is incompatible, (4.49a) and (4.50a); *nand* and *noth* would be *or* and
*either* over negated disjuncts, which compatibility blocks, (4.49a') and (4.50a'); on the
quantifier scale *none* lexicalizes as `~some` and as `all~` while `~all = some~` has no route,
(4.60a). -/
theorem lexicalization_rows :
    ((∀ e ∈ [ex4_49a, ex4_50a], e.judgment = .acceptable) ∧
      ¬ CompatibleConn andConn) ∧
    ((∀ e ∈ [ex4_49a_prime, ex4_50a_prime], e.judgment = .ungrammatical) ∧
      CompatibleConn orConn) ∧
    (ex4_60a.judgment = .acceptable ∧ OuterNegationLexicalizes (someQ 4) ∧
      InnerNegationLexicalizes (allQ 4) ∧ ¬ OuterNegationLexicalizes (allQ 4) ∧
      ¬ InnerNegationLexicalizes (someQ 4)) :=
  ⟨⟨by decide, andConn_not_compatible⟩, ⟨by decide, orConn_compatible⟩,
    ⟨rfl, (e_corner_lexicalizable (by omega)).1, (e_corner_lexicalizable (by omega)).2,
      (o_corner_unlexicalizable (by omega)).1, (o_corner_unlexicalizable (by omega)).2⟩⟩

end Data

end Horn1972
