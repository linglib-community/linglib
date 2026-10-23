module

public import Linglib.Data.Examples.ChemlaSpector2011
public import Linglib.Pragmatics.Implicature.Diagnostics
public import Linglib.Logic.Aristotelian.Square
public import Studies.GeurtsPouscoulous2009
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi

/-!
# Chemla and Spector (2011): Experimental evidence for embedded scalar implicatures

Chemla and Spector argue, against Geurts and Pouscoulous, that scalar inferences computed in
embedded position are detectable. A graded truth-value judgment rates a picture higher when it
satisfies more of a sentence's available readings (§3.2), and the readings a theory makes
available are those its mechanism can derive. A restricted globalist computes the inference at
the speech-act level only, a localist anywhere, and an unrestricted globalist wherever the
result entails the literal reading. Under a universal the local reading entails the literal
one, so Experiment 1 separates only the restricted globalist; under *exactly one* it does not,
so Experiment 2 separates the localist from both globalists.

## Main results

* `exp1_monotone`: in Experiment 1 the ratings rise with the number of true readings.
* `restrictedGlobalist_strong_eq_weak`, `localist_weak_ssubset_strong`: only the localist
  predicts the gap between STRONG and WEAK.
* `unrestrictedGlobalist_local_eq_false`, `exp2_false_lt_local`: the globalists predict LOCAL to
  be rated like FALSE, and it is rated far above.
* `local_isReinforceable`: the local reading passes Sadock's reinforceability diagnostic.
* `de_qLocal_lt_both`, `de_agrees_with_geurts_pouscoulous`: the marginal local reading under
  negation is rated far below the baseline, in line with the fourth experiment of Geurts and
  Pouscoulous (`GeurtsPouscoulous2009.rows_construals_conflict`).

## Implementation notes

* The unrestricted globalist's reach is the semantic condition that a reading entail the
  literal one, so its environment-dependence is derived rather than tabulated.
* Section and figure numbers follow the preprint of December 2010 on the Semantics Archive.

## References

* [chemla-spector-2011]
* [geurts-pouscoulous-2009]
* [sadock-1978]
-/

@[expose] public section

namespace ChemlaSpector2011

open Aristotelian

/-! ### Readings and theories (§1) -/

/-- The three readings the two experiments cross; their entailments differ between the
experiments, which the design exploits. -/
inductive ReadingLabel where
  | literal
  | global
  | local_
  deriving DecidableEq, Repr, Fintype

/-- The three families of theory compute the implicature at the speech-act level only (T1), in
embedded position (T2), or globally but with alternatives that need not be stronger than the
sentence (T3). -/
inductive Theory where
  | restrictedGlobalist
  | localist
  | unrestrictedGlobalist
  deriving DecidableEq, Repr

section Mechanisms

variable {P : Type*} [Fintype P] (readings : ReadingLabel → P → Prop)
  [∀ ℓ p, Decidable (readings ℓ p)]

/-- A globalist derivation reaches a reading exactly when it entails the literal one, since
strengthening the matrix meaning never yields something the literal reading does not follow
from. -/
def GloballyDerivable (ℓ : ReadingLabel) : Prop := ∀ p, readings ℓ p → readings .literal p

instance (ℓ : ReadingLabel) : Decidable (GloballyDerivable readings ℓ) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The readings each theory's mechanism admits. -/
def Theory.admits : Theory → ReadingLabel → Prop
  | .restrictedGlobalist, ℓ => ℓ = .literal ∨ ℓ = .global
  | .localist, _ => True
  | .unrestrictedGlobalist, ℓ => GloballyDerivable readings ℓ

instance : (t : Theory) → (ℓ : ReadingLabel) → Decidable (t.admits readings ℓ)
  | .restrictedGlobalist, _ => inferInstanceAs (Decidable (_ ∨ _))
  | .localist, _ => inferInstanceAs (Decidable True)
  | .unrestrictedGlobalist, _ => inferInstanceAs (Decidable (GloballyDerivable _ _))

/-- The readings a theory leaves available at a picture are those true there and within its
reach; by the conjecture of §3.2 the rating reflects this set. -/
def availableAt (t : Theory) (p : P) : Finset ReadingLabel :=
  Finset.univ.filter fun ℓ ↦ readings ℓ p ∧ t.admits readings ℓ

end Mechanisms

/-- The conjecture of §3.2 says that where strictly more of a sentence's available readings are
true, the rating is higher; it is stated over pairs of a rating and a reading count. -/
abbrev RatingsMonotone (data : List (ℕ × ℕ)) : Prop :=
  data.Pairwise fun d₁ d₂ ↦ d₁.2 < d₂.2 → d₁.1 < d₂.1

/-! ### Pictures (§3, Appendix 2) -/

/-- A six-letter picture places each letter at a vertex of the triangle of opposition, a
falsifier being connected to none of its circles (`E`), a strong verifier to some but not all
(`IO`), and a weak verifier to all (`A`) (Figure 14). -/
abbrev Picture6 := Fin 6 → Triangle

/-- A three-letter picture. -/
abbrev Picture3 := Fin 3 → Triangle

/-! ### Experiment 1: scalar items under a universal (§4) -/

namespace Exp1Some

variable {ι : Type*}

/-- The three readings of (8) over any domain of letters are (10a), each letter is connected
with at least one of its circles, (10b), that and not every letter with all of them, and (10c),
every letter with some but not all of them. -/
def reading : ReadingLabel → (ι → Triangle) → Prop
  | .literal => fun p ↦ ∀ i, ⊥ < p i
  | .global => fun p ↦ (∀ i, ⊥ < p i) ∧ ¬ ∀ i, p i = ⊤
  | .local_ => fun p ↦ ∀ i, p i = .IO

instance [Fintype ι] : (ℓ : ReadingLabel) → (p : ι → Triangle) → Decidable (reading ℓ p)
  | .literal, _ => inferInstanceAs (Decidable (∀ _, _))
  | .global, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .local_, _ => inferInstanceAs (Decidable (∀ _, _))

theorem reading_local_iff (p : ι → Triangle) :
    reading .local_ p ↔ reading .literal p ∧ ∀ i, p i < ⊤ := by
  simp only [reading, ← forall_and]
  exact forall_congr' fun i ↦ by cases p i <;> decide

theorem local_globallyDerivable : GloballyDerivable (reading (ι := ι)) .local_ :=
  fun p h ↦ ((reading_local_iff p).1 h).1

end Exp1Some

/-- The target conditions of Experiment 1 (§4.2.1) make no reading true, only the literal one,
the literal and global ones, or all three. -/
inductive Exp1Condition where
  | false_
  | literal
  | weak
  | strong
  deriving DecidableEq, Repr

/-- The picture of each condition (Figure 4) has six falsifiers, six weak verifiers, four weak
and two strong verifiers, or six strong verifiers. -/
def Exp1Condition.witness : Exp1Condition → Picture6
  | .false_ => fun _ ↦ .E
  | .literal => fun _ ↦ .A
  | .weak => fun i ↦ if i.val < 4 then .A else .IO
  | .strong => fun _ ↦ .IO

/-- The readings true at a condition, read off its witness. -/
def Exp1Condition.truthSet (c : Exp1Condition) : Finset ReadingLabel :=
  Finset.univ.filter (Exp1Some.reading · c.witness)

/-- The row key of a condition. -/
def Exp1Condition.key : Exp1Condition → String
  | .false_ => "false"
  | .literal => "literal"
  | .weak => "weak"
  | .strong => "strong"

/-! ### Experiment 2: scalar items under *exactly one* (§5) -/

namespace Exp2Some

/-- Reading (19a) says that exactly one letter is connected with some or all of its circles, the
others with none. -/
abbrev literal (p : Picture3) : Prop := ∃ i, ⊥ < p i ∧ ∀ j, j ≠ i → p j = .E

/-- Reading (19b) says that exactly one letter is connected with some but not all of its
circles, the others with none. -/
abbrev global (p : Picture3) : Prop :=
  (∃ i, p i = .IO ∧ ∀ j, j ≠ i → p j = .E) ∧ ∀ i, p i ≠ .A

/-- Reading (19c) says that exactly one letter is connected with some but not all of its
circles, the others with none or all. -/
abbrev local_ (p : Picture3) : Prop := ∃ i, p i = .IO ∧ ∀ j, j ≠ i → p j ≠ .IO

/-- The three readings of (21). -/
def reading : ReadingLabel → Picture3 → Prop
  | .literal => literal
  | .global => global
  | .local_ => local_

instance : (ℓ : ReadingLabel) → (p : Picture3) → Decidable (reading ℓ p)
  | .literal, p => inferInstanceAs (Decidable (literal p))
  | .global, p => inferInstanceAs (Decidable (global p))
  | .local_, p => inferInstanceAs (Decidable (local_ p))

/-- Under *exactly one* the local reading no longer entails the literal one, since a strong
verifier among weak verifiers makes it true and the literal reading false, which puts it beyond
a globalist derivation's reach (§5.1). -/
theorem local_not_globallyDerivable : ¬ GloballyDerivable reading .local_ := by
  decide +kernel

end Exp2Some

/-- The target conditions of Experiment 2 (§5.3.1) make no reading true, only the literal one,
only the local one, or all three. -/
inductive Exp2Condition where
  | false_
  | literal
  | local_
  | all
  deriving DecidableEq, Repr

/-- A picture of each condition (Figure 11). -/
def Exp2Condition.witness : Exp2Condition → Picture3
  | .false_ => fun _ ↦ .E
  | .literal => fun i ↦ if i.val = 0 then .A else .E
  | .local_ => fun i ↦ if i.val = 0 then .IO else .A
  | .all => fun i ↦ if i.val = 0 then .IO else .E

/-- The readings true at a condition, read off its witness. -/
def Exp2Condition.truthSet (c : Exp2Condition) : Finset ReadingLabel :=
  Finset.univ.filter (Exp2Some.reading · c.witness)

/-- The row key of a condition. -/
def Exp2Condition.key : Exp2Condition → String
  | .false_ => "false"
  | .literal => "literal"
  | .local_ => "local"
  | .all => "all"

/-- The downward-entailing controls (12) and (13) at the end of each experiment (§4.2.2) make no
reading true, only the marginal local reading, or both readings. -/
inductive DEControlCondition where
  | false_
  | qLocal
  | both
  deriving DecidableEq, Repr

/-- The row key of a condition. -/
def DEControlCondition.key : DEControlCondition → String
  | .false_ => "false"
  | .qLocal => "qlocal"
  | .both => "both"

/-! ### The rows -/

/-- The two experiments. -/
inductive Experiment where
  | one
  | two
  deriving DecidableEq, Repr

def Experiment.key : Experiment → String
  | .one => "1"
  | .two => "2"

/-- The two scalar items, *certains* and *ou*. -/
inductive Item where
  | some
  | or
  deriving DecidableEq, Repr

def Item.key : Item → String
  | .some => "some"
  | .or => "or"

/-- The mean rating, in per-mille, of an item in a condition of an experiment. -/
def rating (e : Experiment) (i : Item) (env cond : String) : Option ℕ :=
  (Examples.all.find? fun r ↦
    r.feature? "experiment" == some e.key && r.feature? "item" == some i.key &&
      r.feature? "environment" == some env && r.feature? "condition" == some cond).bind
    (·.nat? "rating")

/-- The rating of a target condition of Experiment 1. -/
def rating₁ (i : Item) (c : Exp1Condition) : Option ℕ := rating .one i "universal" c.key

/-- The rating of a target condition of Experiment 2. -/
def rating₂ (i : Item) (c : Exp2Condition) : Option ℕ := rating .two i "exactlyOne" c.key

/-- The rating of a downward-entailing control. -/
def ratingDE (e : Experiment) (i : Item) (c : DEControlCondition) : Option ℕ :=
  rating e i "de" c.key

/-! ### Experiment 1 -/

/-- In Figure 5 the ratings of both items rise with the readings true at the condition's
witness, the conjecture of §3.2 on Experiment 1, which subsumes the contrast between STRONG and
WEAK that only the truth of the local reading separates. -/
theorem exp1_monotone (i : Item) :
    ∃ r₀ ∈ rating₁ i .false_, ∃ r₁ ∈ rating₁ i .literal, ∃ r₂ ∈ rating₁ i .weak,
      ∃ r₃ ∈ rating₁ i .strong,
        RatingsMonotone [(r₀, (Exp1Condition.truthSet .false_).card),
          (r₁, (Exp1Condition.truthSet .literal).card), (r₂, (Exp1Condition.truthSet .weak).card),
          (r₃, (Exp1Condition.truthSet .strong).card)] := by
  cases i <;> decide +kernel

/-- The restricted globalist leaves the same readings available at STRONG as at WEAK, the local
reading being true at STRONG but beyond a matrix-only mechanism, so it predicts equal ratings. -/
theorem restrictedGlobalist_strong_eq_weak :
    availableAt Exp1Some.reading .restrictedGlobalist (Exp1Condition.witness .strong) =
      availableAt Exp1Some.reading .restrictedGlobalist (Exp1Condition.witness .weak) := by
  decide

/-- The localist leaves strictly more available at STRONG than at WEAK and so predicts the
gap. -/
theorem localist_weak_ssubset_strong :
    availableAt Exp1Some.reading .localist (Exp1Condition.witness .weak) ⊂
      availableAt Exp1Some.reading .localist (Exp1Condition.witness .strong) := by
  decide

theorem localist_eq_unrestrictedGlobalist_exp1 (c : Exp1Condition) :
    availableAt Exp1Some.reading .localist c.witness =
      availableAt Exp1Some.reading .unrestrictedGlobalist c.witness := by
  cases c <;> decide +kernel

/-- The local reading is reinforceable over the literal one, since at WEAK the literal reading
holds and the local one fails. -/
theorem local_isReinforceable :
    Implicature.IsReinforceable (Exp1Some.reading (ι := Fin 6) .literal)
      (Exp1Some.reading .local_) :=
  ⟨Exp1Condition.witness .weak, by decide, by decide⟩

/-! ### Experiment 2 -/

/-- In Figure 12 the condition where only the local reading of *certains* is true is rated above
the one where only the literal reading is, though the literal reading is false there. -/
theorem exp2_local_gt_literal_some :
    ∃ l ∈ rating₂ .some .local_, ∃ t ∈ rating₂ .some .literal, t < l := by
  decide +kernel

/-- In Figure 12 the local condition is rated far above the false one for both items. -/
theorem exp2_false_lt_local (i : Item) :
    ∃ f ∈ rating₂ i .false_, ∃ l ∈ rating₂ i .local_, f < l := by
  cases i <;> decide +kernel

/-- The unrestricted globalist collapses at the diagnostic condition, where the one reading true
at LOCAL is beyond its reach, so it leaves nothing available there, as at FALSE, and predicts
equal ratings. -/
theorem unrestrictedGlobalist_local_eq_false :
    availableAt Exp2Some.reading .unrestrictedGlobalist (Exp2Condition.witness .local_) =
      availableAt Exp2Some.reading .unrestrictedGlobalist (Exp2Condition.witness .false_) := by
  decide +kernel

theorem localist_false_ssubset_local :
    availableAt Exp2Some.reading .localist (Exp2Condition.witness .false_) ⊂
      availableAt Exp2Some.reading .localist (Exp2Condition.witness .local_) := by
  decide

theorem localist_ne_unrestrictedGlobalist_local :
    availableAt Exp2Some.reading .unrestrictedGlobalist (Exp2Condition.witness .local_) ≠
      availableAt Exp2Some.reading .localist (Exp2Condition.witness .local_) := by
  decide +kernel

/-! ### The downward-entailing controls (§4.4.4, §5.5.4) -/

/-- In Figures 6 and 13 the condition where only the marginal local reading is true is rated far
below the one where both readings are, in both experiments and for both items. -/
theorem de_qLocal_lt_both (e : Experiment) (i : Item) :
    ∃ q ∈ ratingDE e i .qLocal, ∃ b ∈ ratingDE e i .both, q < b := by
  cases e <;> cases i <;> decide +kernel

/-- The same controls are rated higher after the non-monotonic items of Experiment 2 than after
Experiment 1, which §5.5.4 attributes to exposure to salient local readings. -/
theorem de_qLocal_priming (i : Item) :
    ∃ a ∈ ratingDE .one i .qLocal, ∃ b ∈ ratingDE .two i .qLocal, a < b := by
  cases i <;> decide +kernel

/-- Even primed, the local reading under negation stays below the local reading under *exactly
one* (§5.5.4). -/
theorem de_qLocal_lt_local (i : Item) :
    ∃ q ∈ ratingDE .two i .qLocal, ∃ l ∈ rating₂ i .local_, q < l := by
  cases i <;> decide +kernel

/-- The marginal local reading under negation is rated far below the baseline, as the responses
consistent with a local implicature fall far below the genuine-ambiguity baseline in the fourth
experiment of Geurts and Pouscoulous. -/
theorem de_agrees_with_geurts_pouscoulous :
    ∀ i : Item, ∃ q ∈ ratingDE .one i .qLocal, ∃ b ∈ ratingDE .one i .both, q < b :=
  de_qLocal_lt_both .one

end ChemlaSpector2011
