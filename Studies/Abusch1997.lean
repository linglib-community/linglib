module

public import Linglib.Data.Examples.Abusch1997
public import Linglib.Semantics.Attitudes.Acquaintance
public import Linglib.Semantics.Modality.BranchingTime
public import Linglib.Semantics.Tense.Embedding
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Abusch (1997): Sequence of Tense and Temporal De Re

Abusch starts from a theory that evaluates every tense relative to the utterance time, treats
tenses as anaphoric pronouns, and interprets a tense anaphoric across an attitude de re, through
an acquaintance relation to the res time. The simultaneous reading of *Mary believed it was
raining* is then de re with identity as the acquaintance relation. That theory explains neither
the missing forward-shifted readings nor past morphology on a tense that precedes nothing. For
the first, the now of an epistemic alternative is an upper limit for the denotation of tenses,
since from an alternative the past is determinate and the future branches. For the second, every
temporal argument carries a relation variable relating its time to its local evaluation time, an
intensional operator transmits its relation to its complement, and a tense constrains the
relations it has access to: a past requires one of them to be precedence, a present requires
each to exclude it. A present under a past then has no consistent reading in place, so it scopes
out de re, and the counterpart correspondence between the base world and the belief world leaves
only the double access reading.

## Main statements

* `histories_subset_of_upperLimit`, `not_histories_subset_of_branching`: a time the upper limit
  constraint admits lies on every history through the now, and a time after a branching does
  not.
* `PastConstraint.nonLocallyLicensed_of_coindexed`: a past coindexed with its local evaluation
  time is licensed by a transmitted relation.
* `expects_no_simultaneous`: under a present matrix an embedded past has no simultaneous
  reading.
* `doubleAccess_of_counterpart`: a present under a past has only the double access reading.

## Implementation notes

* Relation variables are numbered by the paper's superscripts and times by its indices, `0`
  being the utterance time and `2` the local evaluation time of an attitude complement.
* The feature passing that transmits relations is not modelled: each tense is given the set of
  relation variables it has access to.
* The examples are the rows of `Data.Examples.Abusch1997`.

## References

* [abusch-1997]
* [heim-1994-comments]
* [lewis-1979-attitudes]
* [cresswell-vonstechow-1982]
* [partee-1973]
* [ogihara-1989]
-/

@[expose] public section

namespace Abusch1997

open Tense Acquaintance BranchingTime
open scoped SetRel

variable {E W T : Type*}

/-! ### De re interpretation across attitude contexts -/

/-- On the simultaneous reading of *Mary believed it was raining* (`Examples.ex2`) the embedded past
is anaphoric to the matrix past, hence de re, with identity to the now as acquaintance relation:
Mary ascribes raining to her now under identity with it exactly when it rains at the now of each
of her alternatives. This is also what the reading licensed by the matrix past ascribes, so the
sentence has two equivalent logical forms. -/
theorem simultaneous_deRe {C : Type*} (now : C → T) (rain : T → Set C) (A : Set C) (p : C) :
    AscribesUnder A p (some ∘ now) (now p) rain ↔ ∀ q ∈ A, q ∈ rain (now q) :=
  ascribesUnder_comp_some_apply

/-! ### The upper limit constraint

The now of an epistemic alternative is an upper limit for the denotation of tenses
(`Tense.upperLimitConstraint`). Epistemic alternatives are moments of a branching frame, where
the past of a moment is determinate and its future is not. -/

section Branching

variable {M : Type*} [PartialOrder M] [IsLeftLinear M] {now t t' : M}

/-- From an epistemic alternative the past is determinate, in that a time the upper limit constraint
admits lies on every history through the now. -/
theorem histories_subset_of_upperLimit (h : now ~[toSetRel upperLimitConstraint] t) :
    histories now ⊆ histories t :=
  histories_antitone (mem_toSetRel_upperLimitConstraint.1 h)

/-- The future is not determinate, in that where two later times lie on different branches, neither
lies on every history through the now. -/
theorem not_histories_subset_of_branching (ht' : now ≤ t') (h : ¬ t ≤ t') (h' : ¬ t' ≤ t) :
    ¬ histories now ⊆ histories t := fun hsub ↦
  let ⟨f, hf⟩ := histories_nonempty t'
  (f.le_or_le (hsub (histories_antitone ht' hf)) hf).elim h h'

end Branching

/-- On the forward-shifted reading of *he thought that a burglar attacked him* (`Examples.ex3_ULC`),
an embedded past anaphoric to the later opening of the door violates the upper limit constraint at
the thinking time. -/
theorem forwardShifted_not_upperLimit [LinearOrder T] {thinking opening : T}
    (h : thinking < opening) : compare opening thinking ∉ upperLimitConstraint := by
  simpa using h

/-! ### Transmitted temporal relations -/

/-- A temporal argument, a tense or the covert time of a noun such as *desire*, has a relation
variable, the index of its time, and the index of its local evaluation time. -/
structure TemporalArgument where
  /-- The relation variable. -/
  rel : ℕ
  /-- The index of the argument's time. -/
  index : ℕ
  /-- The index of the local evaluation time. -/
  evalIndex : ℕ

variable {ρ : ℕ → T → T → Prop} {g : ℕ → T} {acc : Finset ℕ} {a : TemporalArgument} {r : ℕ}

/-- The argument's relation holds between its time and its local evaluation time. -/
def TemporalArgument.Con (a : TemporalArgument) (ρ : ℕ → T → T → Prop) (g : ℕ → T) : Prop :=
  ρ a.rel (g a.index) (g a.evalIndex)

/-- A temporal argument is locally licensed when its own relation is temporal precedence. -/
def TemporalArgument.LocallyLicensed [LT T] (a : TemporalArgument) (ρ : ℕ → T → T → Prop) :
    Prop :=
  ρ a.rel = (· < ·)

/-- A temporal argument is non-locally licensed when a transmitted relation, not its own, is
temporal precedence. -/
def TemporalArgument.NonLocallyLicensed [LT T] (a : TemporalArgument) (ρ : ℕ → T → T → Prop)
    (acc : Finset ℕ) : Prop :=
  ∃ r ∈ acc, r ≠ a.rel ∧ ρ r = (· < ·)

/-- The past tense requires one of the relations it has access to to be temporal precedence. -/
def PastConstraint [LT T] (ρ : ℕ → T → T → Prop) (acc : Finset ℕ) : Prop :=
  ∃ r ∈ acc, ρ r = (· < ·)

/-- The present tense requires each of the relations it has access to to exclude temporal
precedence. -/
def PresentConstraint [LT T] (ρ : ℕ → T → T → Prop) (acc : Finset ℕ) : Prop :=
  ∀ r ∈ acc, ∀ t t', ρ r t t' → ¬ t < t'

theorem pastConstraint_singleton [LT T] : PastConstraint ρ {r} ↔ ρ r = (· < ·) := by
  simp [PastConstraint]

theorem PresentConstraint.ne_lt [LT T] (hq : PresentConstraint ρ acc) (hr : r ∈ acc) {t t' : T}
    (h : ρ r t t') : ρ r ≠ (· < ·) :=
  fun hρ ↦ hq r hr t t' h ((congrFun (congrFun hρ t) t').mp h)

section Preorder

variable [Preorder T]

theorem TemporalArgument.not_locallyLicensed_of_coindexed (hcon : a.Con ρ g)
    (h : a.index = a.evalIndex) : ¬ a.LocallyLicensed ρ := fun hl ↦ by
  rw [Con, hl, h] at hcon
  exact lt_irrefl _ hcon

/-- A past coindexed with its local evaluation time is licensed by a transmitted relation. -/
theorem PastConstraint.nonLocallyLicensed_of_coindexed (hp : PastConstraint ρ acc)
    (hcon : a.Con ρ g) (h : a.index = a.evalIndex) : a.NonLocallyLicensed ρ acc :=
  let ⟨r, hr, hρ⟩ := hp
  ⟨r, hr, fun hra ↦ a.not_locallyLicensed_of_coindexed hcon h (hra ▸ hρ :), hρ⟩

end Preorder

/-! ### Non-local and local licensing -/

/-- The matrix tense of *Mary believed*, *John promised* and *Sue expects*, with the relation
`R¹(t₁, t₀)`. -/
def matrix : TemporalArgument := ⟨1, 1, 0⟩

/-- The embedded past of *it was raining* coindexed with the complement's evaluation time, with
the relation `R²(t₂, t₂)`. -/
def embeddedPast : TemporalArgument := ⟨2, 2, 2⟩

theorem simultaneous_nonLocal [Preorder T] (h₁ : matrix.Con ρ g) (h₂ : embeddedPast.Con ρ g)
    (hp₁ : PastConstraint ρ {1}) (hp₂ : PastConstraint ρ {1, 2}) :
    g 1 < g 0 ∧ embeddedPast.NonLocallyLicensed ρ {1, 2} :=
  ⟨by simpa [matrix, TemporalArgument.Con, pastConstraint_singleton.1 hp₁] using h₁,
    hp₂.nonLocallyLicensed_of_coindexed h₂ rfl⟩

/-- On the narrow-scope reading of *John promised to talk about the topic that the participants were
interested in* (`Examples.ex53`), the past of the relative clause, coindexed with the talking time,
is licensed by the matrix relation, so the interest may lie after the utterance time, within the
upper limit constraint. -/
theorem narrowScope_forward (k : ℕ) (hk : k ≠ 1) :
    ∃ (ρ : ℕ → ℤ → ℤ → Prop) (g : ℕ → ℤ), matrix.Con ρ g ∧
      (⟨k, 2, 2⟩ : TemporalArgument).Con ρ g ∧ PastConstraint ρ {1} ∧ PastConstraint ρ {1, k} ∧
      compare (g 2) (g 2) ∈ upperLimitConstraint ∧ g 0 < g 2 :=
  ⟨fun r ↦ if r = 1 then (· < ·) else (· = ·), fun | 0 => 0 | 1 => -5 | _ => 10,
    by show (-5 : ℤ) < 0; decide,
    by show (if k = 1 then (· < ·) else (· = ·)) (10 : ℤ) 10; simp [hk],
    pastConstraint_singleton.2 rfl, ⟨1, by simp, rfl⟩,
    (compare_mem_upperLimitConstraint _ _).2 le_rfl, by show (0 : ℤ) < 10; decide⟩

theorem wideScope_precedes [Preorder T] {k i : ℕ}
    (hcon : (⟨k, i, 0⟩ : TemporalArgument).Con ρ g) (hp : PastConstraint ρ {k}) : g i < g 0 := by
  simpa [TemporalArgument.Con, pastConstraint_singleton.1 hp] using hcon

/-- A present matrix forces local licensing, so the past of *a man she met recently*
(`Examples.ex60`) must itself be precedence, and the meeting precedes the marrying. -/
theorem expects_local [Preorder T] (h₁ : matrix.Con ρ g) (hq : PresentConstraint ρ {1})
    (hp : PastConstraint ρ {1, 3}) (h₃ : (⟨3, 3, 2⟩ : TemporalArgument).Con ρ g) :
    g 3 < g 2 := by
  obtain ⟨r, hr, hρ⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  obtain rfl | rfl := hr
  · exact absurd hρ (hq.ne_lt (Finset.mem_singleton_self _) h₁)
  · simpa [TemporalArgument.Con, hρ] using h₃

/-- *Sue expects to marry a man she loved* (`Examples.ex63`) has no simultaneous reading, since
coindexing the embedded past with the marrying time leaves no relation to license it. -/
theorem expects_no_simultaneous [Preorder T] (h₁ : matrix.Con ρ g)
    (hq : PresentConstraint ρ {1}) (hp : PastConstraint ρ {1, 3})
    (h₃ : (⟨3, 2, 2⟩ : TemporalArgument).Con ρ g) : False := by
  obtain ⟨r, hr, hρ⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  obtain rfl | rfl := hr
  · exact hq.ne_lt (Finset.mem_singleton_self _) h₁ hρ
  · exact (⟨3, 2, 2⟩ : TemporalArgument).not_locallyLicensed_of_coindexed h₃ rfl hρ

/-! ### Present under past -/

/-- *John believed that Mary is pregnant* (`Examples.ex8_doubleAccess`) has no reading with the
present in place, since the matrix past makes `R¹` precedence, and the embedded present, which has
access to `R¹`, requires it to exclude precedence. -/
theorem presentUnderPast_false [Preorder T] (h₁ : matrix.Con ρ g) (hp : PastConstraint ρ {1})
    (hq : PresentConstraint ρ {1, 3}) : False :=
  hq.ne_lt (r := 1) (Finset.mem_insert_self _ _) h₁ (pastConstraint_singleton.1 hp)

/-- On the double access reading the scoped present denotes an interval `I` overlapping the
utterance time, and its trace denotes `J` in the belief world, bounded by the upper limit constraint
at the believer's now. The counterpart correspondence, on which `I` follows the believing time iff
`J` follows the now and `I` overlaps it iff `J` overlaps the now, leaves only the reading where `I`
overlaps the believing time as well. -/
theorem doubleAccess_of_counterpart [LinearOrder T] {I J : Set T} (hI : I.OrdConnected)
    {believing utterance now : T} (hlt : believing < utterance) (hU : utterance ∈ I)
    (hulc : ∃ s ∈ J, s ≤ now)
    (hafter : (∀ s ∈ I, believing < s) ↔ ∀ s ∈ J, now < s)
    (hoverlap : believing ∈ I ↔ now ∈ J) :
    {believing, utterance} ⊆ I ∧ now ∈ J := by
  have hb : believing ∈ I := by
    by_contra hb
    obtain ⟨s, hs, hsn⟩ := hulc
    refine (hafter.1 fun s hs ↦ lt_of_not_ge fun hsb ↦ hb ?_) s hs |>.not_ge hsn
    exact hI.out hs hU ⟨hsb, hlt.le⟩
  exact ⟨Set.pair_subset hb hU, hoverlap.1 hb⟩

end Abusch1997
