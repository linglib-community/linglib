module

public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Quantification.Counting

/-!
# Cohen (1999): Think Generic!

Cohen's inductivist semantics makes a generic sentence a probability judgment: gen(ψ, φ) is
true iff the conditional probability of the scope, given the restrictor and the disjunction
of a set of alternatives to the scope, exceeds one half (definition 1, p. 37). "Mammals
bear live young" is evaluated over the mammals that procreate in some way, so no majority
among all mammals is required, and Thomason's "People have a hard time finding CMU" is
evaluated over the people who sought it. Generics are further ambiguous between this
absolute reading and a relative one whose threshold is the average probability of the scope
over the alternatives; the relative reading verifies "Bulgarians are good weightlifters"
and, since its threshold depends on individuals outside the restrictor, it is not
conservative (definition 3, pp. 55–56). The probability is a relative frequency in the
limit, which imposes two constraints. The reference class may not be explicitly bounded
(§4.4.2), and it must be homogeneous: unrestricted homogeneity is degenerate, since
partitioning by the scope itself separates any mixed reference class (definition 4 and
Salmon's argument, pp. 81–82), so the final truth conditions demand the majority within
every inhabited cell of every salient partition of the restrictor (definition 5, p. 83).
"Mammals are female" then fails under the sex partition however many mammals are female
(§4.4.6). Frequency adverbs apply other thresholds to the same conditional probability —
always 1, never 0, sometimes non-zero, usually the same one half as gen — and respect only
the temporal partition, which is why "Primary school teachers are usually female" is true
while the bare generic is not (definition 10, p. 128; §6.2.3).

We state the three definitions over finite models, derive the degeneracy of unrestricted
homogeneity, the conservativity of the absolute reading and a non-conservativity witness
for the relative one, the recovery of the relativized classical quantifiers at the
frequency-adverb thresholds, and the paper's key examples.

## Implementation notes

Page and definition numbers follow the CSLI edition, a light revision of the 1996
dissertation that renames its independent and dependent readings absolute and relative.
The alternative set enters the truth conditions only through its extensional disjunction
and the relative threshold, so it is carried as a single predicate. A conditional
probability is the uniform measure on the reference class at the scope; with an empty reference
class it is undefined in the paper (p. 37, §5.6) and `0` here, so gen is false there and
decidable through its count form, and a salient cell with an empty reference class imposes no
condition.

## TODO

* The unboundedness constraint (§4.4.2) and lawlikeness (§4.4.3) restrict which sentences
  express generics at all — a matter of reference classes conceivable as unlimited, with no
  content over a fixed finite model — and are not stated.
* Chapter 5's calculus of alternatives (absolute determinables, focus, the connectives) and
  chapter 7's default reasoning are not formalized; the alternative set is taken as given,
  as in §3.2.

## References

* [A. Cohen, *Think Generic! The Meaning and Use of Generic Sentences* (1999)][cohen-1999a]
* [W. C. Salmon, *Objectively Homogeneous Reference Classes* (1977)][salmon-1977]
* [R. Thomason, *Theories of Nonmonotonicity and Natural Language Generics*
  (1988)][thomason-1988]
* [G. N. Carlson, *Reference to Kinds in English* (1977)][carlson-1977a]
-/

@[expose] public section

namespace Cohen1999

open Quantifier Quantifier.GQ MeasureTheory ProbabilityTheory
open scoped ENNReal Finset

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (domain : Finset α)
  (ψ alt φ : α → Prop) [DecidablePred ψ] [DecidablePred alt] [DecidablePred φ]

/-- Cohen's generic quantifier on its absolute reading (definition 1, p. 37) holds when the
conditional probability of the scope `φ`, given the restrictor `ψ` and the disjunction `alt` of
the alternatives to the scope, exceeds one half. -/
def gen : Prop := 2⁻¹ < uniformOn (domain.filter fun x ↦ ψ x ∧ alt x : Set α) {x | φ x}

/-- The relative reading (definition 3, p. 56) holds when the restrictor raises the probability
of the scope above its average over the alternatives. -/
def genRelative : Prop :=
  uniformOn (domain.filter alt : Set α) {x | φ x} <
    uniformOn (domain.filter fun x ↦ ψ x ∧ alt x : Set α) {x | φ x}

/-- The final truth conditions (definition 5, p. 83) ask for the absolute threshold within every
salient cell whose reference class is inhabited. -/
def genSalient {ι : Type*} (cells : ι → α → Prop) [∀ i, DecidablePred (cells i)] : Prop :=
  ∀ i, (domain.filter fun x ↦ (ψ x ∧ cells i x) ∧ alt x).Nonempty →
    gen domain (fun x ↦ ψ x ∧ cells i x) alt φ

/-- A frequency adverb applies its lexical requirement to the same conditional probability
(definition 10, p. 128); gen carries the requirement `(2⁻¹ < ·)`, synonymous with usually. -/
def freq (R : ℝ≥0∞ → Prop) : Prop :=
  R (uniformOn (domain.filter fun x ↦ ψ x ∧ alt x : Set α) {x | φ x})

/-- Unrestricted homogeneity (definition 4, p. 81, after Salmon) holds when every inhabited
sub-reference class preserves the conditional probability of the scope. -/
def Homogeneous : Prop :=
  ∀ (part : α → Prop) [DecidablePred part], (domain.filter fun x ↦ ψ x ∧ part x).Nonempty →
    uniformOn (domain.filter fun x ↦ ψ x ∧ part x : Set α) {x | φ x} =
      uniformOn (domain.filter ψ : Set α) {x | φ x}

variable {domain ψ alt φ}

/-! ### Probabilities on a finite reference class -/

private theorem inv_two_lt_iff (F : Finset α) :
    2⁻¹ < uniformOn (F : Set α) {x | φ x} ↔ #F < 2 * #(F.filter φ) := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  rw [uniformOn_finset_setOf, ENNReal.lt_div_iff_mul_lt (.inl (by simpa using hF.ne_empty))
    (.inl (by simp)), ← ENNReal.div_eq_inv_mul, ENNReal.div_lt_iff (by simp) (by simp)]
  norm_cast
  omega

private theorem uniformOn_lt_iff {F G : Finset α} (hF : F.Nonempty) (hG : G.Nonempty) :
    uniformOn (F : Set α) {x | φ x} < uniformOn (G : Set α) {x | φ x} ↔
      #(F.filter φ) * #G < #(G.filter φ) * #F := by
  rw [uniformOn_finset_setOf, uniformOn_finset_setOf,
    ← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simpa using hF.ne_empty))
      (ENNReal.div_ne_top (by simp) (by simpa using hG.ne_empty)),
    ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  rw [div_lt_div_iff₀ (by exact_mod_cast hF.card_pos) (by exact_mod_cast hG.card_pos)]
  norm_cast

omit [DecidablePred φ] in
private theorem uniformOn_eq_one_iff' {F : Finset α} (hF : F.Nonempty) :
    uniformOn (F : Set α) {x | φ x} = 1 ↔ ∀ x ∈ F, φ x := by
  rw [uniformOn_eq_one_iff F.finite_toSet (Finset.coe_nonempty.2 hF)]
  exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h x hx⟩

omit [DecidablePred φ] in
private theorem uniformOn_eq_zero_iff' (F : Finset α) :
    uniformOn (F : Set α) {x | φ x} = 0 ↔ ∀ x ∈ F, ¬ φ x := by
  rw [uniformOn_eq_zero_iff F.finite_toSet, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x hx hφ ↦ h x ⟨hx, hφ⟩, fun h x hx ↦ h x hx.1 hx.2⟩

/-! ### The absolute reading and the majority quantifier -/

theorem gen_iff_card :
    gen domain ψ alt φ ↔
      #(domain.filter fun x ↦ ψ x ∧ alt x) < 2 * #((domain.filter fun x ↦ ψ x ∧ alt x).filter φ) :=
  inv_two_lt_iff _

instance : Decidable (gen domain ψ alt φ) := decidable_of_iff _ gen_iff_card.symm

theorem genRelative_iff_card (hA : (domain.filter alt).Nonempty)
    (hR : (domain.filter fun x ↦ ψ x ∧ alt x).Nonempty) :
    genRelative domain ψ alt φ ↔
      #((domain.filter alt).filter φ) * #(domain.filter fun x ↦ ψ x ∧ alt x) <
        #((domain.filter fun x ↦ ψ x ∧ alt x).filter φ) * #(domain.filter alt) :=
  uniformOn_lt_iff hA hR

theorem gen_iff_most : gen domain ψ alt φ ↔ most (fun x ↦ x ∈ domain ∧ ψ x ∧ alt x) φ := by
  have h₁ : {x | (x ∈ domain ∧ ψ x ∧ alt x) ∧ φ x}.ncard =
      #((domain.filter fun x ↦ ψ x ∧ alt x).filter φ) := by
    rw [← Set.ncard_coe_finset]; congr 1; ext; simp
  have h₂ : {x | (x ∈ domain ∧ ψ x ∧ alt x) ∧ ¬ φ x}.ncard =
      #((domain.filter fun x ↦ ψ x ∧ alt x).filter fun x ↦ ¬ φ x) := by
    rw [← Set.ncard_coe_finset]; congr 1; ext; simp
  have h₃ := Finset.card_filter_add_card_filter_not (s := domain.filter fun x ↦ ψ x ∧ alt x) φ
  rw [gen_iff_card, most_apply, h₁, h₂]
  omega

omit [MeasurableSingletonClass α] [DecidablePred φ] in
-- p. 128, p. 131
theorem gen_iff_freq : gen domain ψ alt φ ↔ freq domain ψ alt φ (2⁻¹ < ·) :=
  Iff.rfl

-- p. 54
theorem gen_conservativity :
    gen domain ψ alt (fun x ↦ ψ x ∧ φ x) ↔ gen domain ψ alt φ := by
  have : (domain.filter fun x ↦ ψ x ∧ alt x).filter (fun x ↦ ψ x ∧ φ x) =
      (domain.filter fun x ↦ ψ x ∧ alt x).filter φ :=
    Finset.filter_congr fun x hx ↦ and_iff_right (Finset.mem_filter.1 hx).2.1
  unfold gen
  rw [uniformOn_finset_setOf, uniformOn_finset_setOf, this]

theorem monotone_gen : Monotone fun φ ↦ gen domain ψ alt φ := fun φ φ' h hg ↦ by
  classical
  beta_reduce at hg ⊢
  rw [gen_iff_card] at hg ⊢
  exact hg.trans_le <| Nat.mul_le_mul_left 2 <|
    Finset.card_le_card <| Finset.monotone_filter_right _ fun x _ ↦ h x

-- §5.7
theorem gen_self_iff : gen domain ψ φ φ ↔ (domain.filter fun x ↦ ψ x ∧ φ x).Nonempty := by
  rw [gen_iff_card, Finset.filter_true_of_mem (s := domain.filter fun x ↦ ψ x ∧ φ x) (p := φ)
    fun x hx ↦ (Finset.mem_filter.1 hx).2.2, ← Finset.card_pos]
  omega

/-! ### The generalized-quantifier interface

Over the whole carrier with trivial alternatives the absolute reading is the majority
generalized quantifier, hence proportional: its truth depends only on the two cell counts.
The relativized readings are exactly what departs from this. -/

theorem gen_univ_iff_most {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (R S : β → Prop) [DecidablePred R] [DecidablePred S] :
    gen Finset.univ R (fun _ ↦ True) S ↔ most R S := by
  simp only [gen_iff_most, Finset.mem_univ, true_and, and_true]

open Classical in
theorem gen_proportional {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] :
    Proportional (fun R S : β → Prop ↦ gen Finset.univ R (fun _ ↦ True) S) := fun R₁ S₁ R₂ S₂ ↦ by
  simpa only [gen_univ_iff_most] using proportional_most R₁ S₁ R₂ S₂

/-! ### Homogeneity is degenerate unrestricted (definition 4, p. 82) -/

-- p. 82
theorem homogeneous_iff (hR : (domain.filter ψ).Nonempty) :
    Homogeneous domain ψ φ ↔
      no (fun x ↦ x ∈ domain ∧ ψ x) φ ∨ every (fun x ↦ x ∈ domain ∧ ψ x) φ := by
  constructor
  · intro h
    by_cases hno : no (fun x ↦ x ∈ domain ∧ ψ x) φ
    · exact Or.inl hno
    · refine Or.inr ?_
      obtain ⟨x, ⟨hx, hψx⟩, hφx⟩ : ∃ x, (x ∈ domain ∧ ψ x) ∧ φ x := by
        by_contra hc
        exact hno fun y hy hφ ↦ hc ⟨y, hy, hφ⟩
      have hpart : (domain.filter fun y ↦ ψ y ∧ φ y).Nonempty :=
        ⟨x, Finset.mem_filter.2 ⟨hx, hψx, hφx⟩⟩
      have h1 := (uniformOn_eq_one_iff' hpart).2 fun y hy ↦ (Finset.mem_filter.1 hy).2.2
      rw [h φ hpart, uniformOn_eq_one_iff' hR] at h1
      exact fun y hy ↦ h1 y (Finset.mem_filter.2 hy)
  · rintro (hno | hall) part _ hpart
    · rw [(uniformOn_eq_zero_iff' _).2 fun y hy ↦ hno y ⟨(Finset.mem_filter.1 hy).1,
          (Finset.mem_filter.1 hy).2.1⟩,
        (uniformOn_eq_zero_iff' _).2 fun y hy ↦ hno y (Finset.mem_filter.1 hy)]
    · rw [(uniformOn_eq_one_iff' hpart).2 fun y hy ↦ hall y ⟨(Finset.mem_filter.1 hy).1,
          (Finset.mem_filter.1 hy).2.1⟩,
        (uniformOn_eq_one_iff' hR).2 fun y hy ↦ hall y (Finset.mem_filter.1 hy)]

/-! ### Frequency adverbs (definition 10, p. 128)

At the extreme thresholds the restricted classical quantifiers reappear; sometimes is the
existential, so a generic over an empty reference class entails nothing (§5.6). -/

omit [DecidablePred φ] in
theorem freq_eq_one_iff (hR : (domain.filter fun x ↦ ψ x ∧ alt x).Nonempty) :
    freq domain ψ alt φ (· = 1) ↔ every (fun x ↦ x ∈ domain ∧ ψ x ∧ alt x) φ :=
  (uniformOn_eq_one_iff' hR).trans
    ⟨fun h x hx ↦ h x (Finset.mem_filter.2 hx), fun h x hx ↦ h x (Finset.mem_filter.1 hx)⟩

omit [DecidablePred φ] in
theorem freq_eq_zero_iff :
    freq domain ψ alt φ (· = 0) ↔ no (fun x ↦ x ∈ domain ∧ ψ x ∧ alt x) φ :=
  (uniformOn_eq_zero_iff' _).trans
    ⟨fun h x hx ↦ h x (Finset.mem_filter.2 hx), fun h x hx ↦ h x (Finset.mem_filter.1 hx)⟩

omit [DecidablePred φ] in
theorem freq_pos_iff :
    freq domain ψ alt φ (0 < ·) ↔ GQ.some (fun x ↦ x ∈ domain ∧ ψ x ∧ alt x) φ := by
  have h := freq_eq_zero_iff (domain := domain) (ψ := ψ) (alt := alt) (φ := φ)
  unfold freq at h ⊢
  beta_reduce at h ⊢
  rw [pos_iff_ne_zero, Ne, h]
  simp only [no, GQ.some, not_forall, not_not, exists_prop]

/-! ### People have a hard time finding CMU (§3.2.1, after Thomason)

Twenty people, five of whom sought the university: four found it with difficulty, one with
ease. The alternatives — the levels of difficulty of the search — restrict the reference
class to the seekers, so the generic holds with no majority among people. -/

section Examples

abbrev soughtCMU : Fin 20 → Prop := (·.val < 5)
abbrev hardTime : Fin 20 → Prop := (·.val < 4)

theorem cmu_gen : gen Finset.univ (fun _ ↦ True) soughtCMU hardTime := by
  decide

theorem cmu_no_majority : ¬ gen Finset.univ (fun _ ↦ True) (fun _ ↦ True) hardTime := by
  decide

/-! ### Mammals bear live young; mammals are not female (§3.2.1 p. 33, §4.4.6 p. 91)

Twenty mammals, eight of which procreate: six bear live young, two lay eggs. Eleven are
female, among them every procreator. Relativized to the forms of procreation, the first
generic is true though bearers are a minority of all mammals, and the male cell of the sex
partition is empty of procreators, so definition 5 agrees. The second clears definition 1
on the female majority alone but fails definition 5, since the male cell is inhabited and
contains no female — the paper's resolution of the contrast with different alternatives and
the sex partition. By definition 10 the same threshold read as the adverb usually ignores
the non-temporal partition (§6.2.3), so "usually female" stays true. -/

abbrev procreates : Fin 20 → Prop := (·.val < 8)
abbrev bearsLive : Fin 20 → Prop := (·.val < 6)
abbrev female : Fin 20 → Prop := (·.val < 11)

/-- The sex partition divides the females from the males. -/
abbrev sexCell : Bool → Fin 20 → Prop := fun b x ↦ if b then female x else ¬ female x

theorem bearsLive_gen : gen Finset.univ (fun _ ↦ True) procreates bearsLive := by
  decide

theorem bearsLive_no_majority :
    ¬ gen Finset.univ (fun _ ↦ True) (fun _ ↦ True) bearsLive := by
  decide

theorem bearsLive_genSalient :
    genSalient Finset.univ (fun _ ↦ True) procreates bearsLive sexCell := by
  intro i hi
  cases i
  · exact absurd hi (by decide)
  · decide

theorem female_gen : gen Finset.univ (fun _ ↦ True) (fun _ ↦ True) female := by
  decide

theorem female_not_genSalient :
    ¬ genSalient Finset.univ (fun _ ↦ True) (fun _ ↦ True) female sexCell := by
  intro h
  exact absurd (h false (by decide)) (by decide)

/-! ### Relative readings (§3.4.3–3.4.4, pp. 54–56)

Twenty people, fifteen of them weightlifters: the five Bulgarians all lift, two of them
well; one of the ten other lifters is good. A Bulgarian lifter is likelier than an
arbitrary one to be good, though no majority of Bulgarian lifters is. In the soccer
variant, where the lousy players concentrate outside Brazil, the relative reading correctly
rejects "Brazilians are lousy soccer players" yet accepts the sentence with its scope
intersected with the restrictor, whose average is lower — so the reading is not
conservative. -/

abbrev bulgarian : Fin 20 → Prop := (·.val < 5)
abbrev lifter : Fin 20 → Prop := (·.val < 15)
abbrev goodLifter : Fin 20 → Prop := fun x ↦ x.val < 2 ∨ x.val = 5

theorem bulgarians_relative : genRelative Finset.univ bulgarian lifter goodLifter := by
  rw [genRelative_iff_card (by decide) (by decide)]
  decide

theorem bulgarians_not_absolute : ¬ gen Finset.univ bulgarian lifter goodLifter := by
  decide

abbrev brazilian : Fin 20 → Prop := (·.val < 5)
abbrev soccerPlayer : Fin 20 → Prop := (·.val < 15)
abbrev lousy : Fin 20 → Prop := fun x ↦ x.val = 0 ∨ (5 ≤ x.val ∧ x.val < 13)

theorem brazilians_relative_rejected :
    ¬ genRelative Finset.univ brazilian soccerPlayer lousy := by
  rw [genRelative_iff_card (by decide) (by decide)]
  decide

-- p. 55
theorem genRelative_not_conservative :
    ¬ (genRelative Finset.univ brazilian soccerPlayer (fun x ↦ brazilian x ∧ lousy x) ↔
        genRelative Finset.univ brazilian soccerPlayer lousy) := by
  rw [genRelative_iff_card (by decide) (by decide), genRelative_iff_card (by decide) (by decide)]
  decide

end Examples

end Cohen1999
