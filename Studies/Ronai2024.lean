module

public import Linglib.Data.Examples.Ronai2024
public import Studies.ChemlaSpector2011

/-!
# Ronai (2024): Embedded scalar diversity

Ronai tests the embedded scalar implicature of *every N was P* across 42 lexical scales: whether
*Every soup was warm* suggests the strong inference *No soup was hot*, computed in the scope of
the universal, beyond the weak inference *Not every soup was hot* that a global implicature
yields. Experiment 1 has the design of Chemla and Spector and of Gotzner and Romoli with the
scale varied, and the responses track how many readings of the sentence entail the judged
inference. Experiment 2 replaces the false control by the inference task of van Tiel and
Geurts, since the compatible control of Gotzner and Romoli is the negation of the strong
inference itself. The paper's argument for alternative-based accounts, including the model of
Potts et al., is statistical and stays in prose: semantic distance and boundedness predict the
embedded variation as they predict the global rates of van Tiel and Geurts, which a lexical
strengthening in the style of Bergen, Levy and Goodman leaves unexplained, and the null result
of Sun, Tian and Breheny is put down to the corrective context of *P so not Q*.

## Main results

* `supports_iff`: the literal reading supports the true control, the global reading the weak
  inference too, and the local reading the strong inference too.
* `exp1_monotone`: the responses of Figure 1 rise with the number of supporting readings.
* `strong_admitted`: every account but the unmodified neo-Gricean one makes the local reading
  available under a universal: the grammatical theory of Chierchia and of Chierchia, Fox and
  Spector computes it locally, and Sauerland's account negates an alternative that is not
  stronger than the utterance.
* `compatible_iff_not_strong`: the compatible control is the negation of the strong inference.

## Implementation notes

* A scale ⟨P, Q⟩ with `Q ⊆ P` puts each individual of the domain in one of the three cells of
  `Aristotelian.Triangle`, ordered as *none* < *some but not all* < *all*: neither term (`E`),
  the weak term only (`IO`), or the strong term (`A`).
* The rows carry the condition means of Figure 1 and the per-scale strong-inference rates of
  both experiments, computed from the raw data the paper deposits.

## References

* [ronai-2024]
* [chemla-spector-2011]
* [gotzner-romoli-2018]
* [van-tiel-geurts-2016]
* [chierchia-2004]
* [chierchia-fox-spector-2012]
* [sauerland-2004]
* [potts-etal-2016]
* [bergen-levy-goodman-2016]
* [sun-tian-breheny-2018]
-/

@[expose] public section

namespace Ronai2024

open ChemlaSpector2011 Aristotelian

variable {ι : Type*}

/-! ### The inferences judged in Experiment 1 -/

/-- The second sentence of a trial (11) is the true control *at least one N was P*, the weak
inference *not every N was Q*, the strong inference *no N was Q*, or the false control *not
every N was P*. -/
inductive Inference where
  | trueControl
  | weak
  | strong
  | falseControl
  deriving DecidableEq, Repr, Fintype

/-- What each inference says of a domain of individuals. The weak inference is the negation of
the utterance's only alternative on an unmodified neo-Gricean account, *every N was Q*. -/
def Inference.den : Inference → (ι → Triangle) → Prop
  | .trueControl, m => ∃ i, ⊥ < m i
  | .weak, m => ¬ ∀ i, m i = ⊤
  | .strong, m => ∀ i, m i < ⊤
  | .falseControl, m => ¬ Exp1Some.reading .literal m

instance [Fintype ι] (m : ι → Triangle) : (n : Inference) → Decidable (n.den m)
  | .trueControl => inferInstanceAs (Decidable (∃ _, _))
  | .weak => inferInstanceAs (Decidable (¬ _))
  | .strong => inferInstanceAs (Decidable (∀ _, _))
  | .falseControl => inferInstanceAs (Decidable (¬ _))

/-- The row key of an inference. -/
def Inference.key : Inference → String
  | .trueControl => "true"
  | .weak => "weak"
  | .strong => "strong"
  | .falseControl => "false"

/-- The sentence *Some N was Q* (5) is the alternative built by replacing both scalar terms and
the compatible control of a second experiment. -/
def compatible (m : ι → Triangle) : Prop := ∃ i, m i = ⊤

instance [Fintype ι] (m : ι → Triangle) : Decidable (compatible m) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- Negating the alternative *some N was Q* yields the strong inference. -/
theorem compatible_iff_not_strong (m : ι → Triangle) :
    compatible m ↔ ¬ Inference.den .strong m := by
  simp only [compatible, Inference.den, not_forall]
  exact exists_congr fun i ↦ by cases m i <;> decide

theorem compatible_not_literal :
    ∃ m : Bool → Triangle, compatible m ∧ ¬ Exp1Some.reading .literal m :=
  ⟨fun b ↦ if b then .A else .E, by decide⟩

/-! ### Readings and the inferences they support (§3.4) -/

/-- A reading supports an inference when it entails it on every nonempty domain. -/
def Supports (ℓ : ReadingLabel) (n : Inference) : Prop :=
  ∀ {ι : Type} [Nonempty ι] (m : ι → Triangle), Exp1Some.reading ℓ m → n.den m

/-- The literal reading supports the true control alone, the global reading the weak inference
too, and the local reading the strong inference too; no reading supports the false control. -/
def supported : ReadingLabel → Finset Inference
  | .literal => {.trueControl}
  | .global => {.trueControl, .weak}
  | .local_ => {.trueControl, .weak, .strong}

theorem supports_iff (ℓ : ReadingLabel) (n : Inference) : Supports ℓ n ↔ n ∈ supported ℓ := by
  refine ⟨fun h ↦ ?_, fun h ι _ m hm ↦ ?_⟩
  · cases ℓ <;> cases n <;> first
      | decide
      | exact absurd (h (fun _ : Unit ↦ .A) (by decide)) (by decide)
      | exact absurd (h (fun b : Bool ↦ if b then .A else .IO) (by decide)) (by decide)
      | exact absurd (h (fun _ : Unit ↦ .IO) (by decide)) (by decide)
  · cases ℓ <;> cases n <;>
      simp only [supported, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self,
        or_false, false_or] at h
    case literal.trueControl => exact ⟨Classical.arbitrary ι, hm _⟩
    case global.trueControl => exact ⟨Classical.arbitrary ι, hm.1 _⟩
    case global.weak => exact hm.2
    case local_.trueControl =>
      exact ⟨Classical.arbitrary ι, ((Exp1Some.reading_local_iff m).1 hm).1 _⟩
    case local_.weak =>
      exact fun h ↦ absurd (h (Classical.arbitrary ι)) (by rw [hm _]; decide)
    case local_.strong => exact ((Exp1Some.reading_local_iff m).1 hm).2

instance (ℓ : ReadingLabel) (n : Inference) : Decidable (Supports ℓ n) :=
  decidable_of_iff _ (supports_iff ℓ n).symm

theorem supports_strong_iff (ℓ : ReadingLabel) : Supports ℓ .strong ↔ ℓ = .local_ := by
  cases ℓ <;> simp [supports_iff, supported]

/-- The number of readings supporting an inference, which the sliding-scale response tracks. -/
def support (n : Inference) : ℕ := (Finset.univ.filter (Supports · n)).card

/-- Every account but the unmodified neo-Gricean one makes the local reading available under a
universal, the grammatical theory computing it in the scope of *every* and a globalist whose
alternatives need not be stronger than the utterance reaching it because there it entails the
literal reading. -/
theorem strong_admitted (t : Theory) :
    t.admits (Exp1Some.reading (ι := ι)) .local_ ↔ t ≠ .restrictedGlobalist := by
  cases t <;> simp [Theory.admits, Exp1Some.local_globallyDerivable]

/-! ### The rows -/

/-- The mean response to an inference over the 42 scales in Experiment 1 (Figure 1), in
percent. -/
def mean (n : Inference) : Option ℕ :=
  (Examples.all.find? fun r ↦
    r.feature? "example" == some "11" && r.feature? "condition" == some n.key).bind
    (·.nat? "mean")

/-- In Figure 1 the responses rise with the readings supporting the inference, true above weak
above strong above false across the 42 scales. The strong inference above the false control is
the paper's evidence that embedded implicatures are computed, and the weak inference above the
strong one reflects that the global reading supports only the former. -/
theorem exp1_monotone :
    ∃ r₀ ∈ mean .falseControl, ∃ r₁ ∈ mean .strong, ∃ r₂ ∈ mean .weak,
      ∃ r₃ ∈ mean .trueControl,
        RatingsMonotone [(r₀, support .falseControl), (r₁, support .strong),
          (r₂, support .weak), (r₃, support .trueControl)] := by
  decide +kernel

/-! ### Experiment 2 (§4) -/

theorem literal_and_compatible :
    ∃ m : Unit → Triangle, Exp1Some.reading .literal m ∧ compatible m :=
  ⟨fun _ ↦ .A, by decide⟩

theorem not_compatible_of_local {m : ι → Triangle} (h : Exp1Some.reading .local_ m) :
    ¬ compatible m :=
  fun ⟨i, hi⟩ ↦ absurd hi (by rw [h i]; decide)

end Ronai2024
