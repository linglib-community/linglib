module

public import Linglib.Data.Examples.Schwab2023
public import Linglib.Data.Experiments.Schwab2023
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Schwab (2023): Lexical variation in NPI illusions

This file formalizes the paper's scalar account of the negative polarity illusion. Two speeded
acceptability experiments on German contrast the strengthening NPI *jemals* 'ever' with the
attenuating NPI *so recht* 'really' in a 2 × 3 design crossing the item with the position of a
negative quantifier: in the matrix clause, where it licenses the item, inside a relative clause,
where it cannot, or absent (`Data/Examples/Schwab2023`). Only *jemals* is illusorily licensed by
the relative-clause quantifier, an asymmetry that the cue-based retrieval, quantifier-scope and
pragmatic-rescuing accounts of the illusion do not foresee: the paper reads its Bayes factors
(`Data/Experiments/Schwab2023`) as evidence for the *jemals* illusion in both experiments and for
the *so recht* illusion in neither (`illusion_attested`), and for the difference between the two
in the second experiment only (`interaction_attested_iff`). Its readings rank the Bayes factors
consistently (`verdictRank_monotone`).

The account builds on the scalar theories of polarity sensitivity of [krifka-1995a],
[kadmon-landman-1993], [chierchia-2006] and [israel-1996]. A strengthening item is assertable
only where the proposition is stronger than every alternative it evokes, [krifka-1995a]'s
scalar assertion in the form of [condoravdi-2010] (`scalAssert`); an attenuating item where
some compatible alternative would have been more informative, the condition of Schwab and Liu
(`attenAssert`). The two conditions are opposed: when the proposition entails its alternatives,
scalar assertion is the plain update while the attenuating condition is contradictory
(`scalAssert_eq_of_isStrongest`, `attenAssert_eq_empty_of_isStrongest`), and an existential
under negation or an attenuating degree modifier under negation instantiates the licensed case
of each (`scalAssert_not_ever`, `attenAssert_not_atLeast`), while in the affirmative the
existential is covered by its more specific alternatives (`scalAssert_ever_eq_empty`) and the
degree modifier entails its lower ones (`isStrongest_atLeast`). The illusion arises, on the
paper's proposal after the environment-based account of [muller-phillips-2020], when the
parser feeds the mechanism the still-active relative-clause proposition and its Horn-scale
alternatives instead of the main clause: a negative quantifier is the strongest point of its
scale, so the strengthening mechanism accepts it and the attenuating one rejects it
(`illusion_asymmetry`).

## Implementation notes

* Propositions are sets of worlds and the context is a set of worlds; an alternative is
  informative after the assertion when the context updated with the assertion does not entail
  it (`Informative`), the paper's `c + p + p' ≠ c + p`. Alternatives are an arbitrary set of
  propositions, so the lexical scales are hypotheses on it: the specific times of an
  existential and the lower degrees of a degree modifier.
* The Bayes factors and the paper's readings of them are `Data/Experiments/Schwab2023`; an
  effect counts as attested when the paper reads its Bayes factor as at least moderate evidence
  for it, since the paper states no threshold. The posterior estimates are not recorded. The
  parser's activation story that selects the relative-clause proposition is not modeled, only
  what each mechanism returns once it is selected.

## References

* [schwab-2023]
* [krifka-1995a]
* [condoravdi-2010]
* [israel-1996]
* [muller-phillips-2020]
-/

@[expose] public section

namespace Schwab2023

variable {W : Type*}

/-! ### The two scalar licensing conditions (§1.2) -/

/-- An alternative `p'` is informative after asserting `p` in the context `c` when the context
updated with `p` does not already entail it, the `c + p + p' ≠ c + p` of (5) and (6). -/
def Informative (c p p' : Set W) : Prop := ¬ c ∩ p ⊆ p'

theorem informative_iff (c p p' : Set W) : Informative c p p' ↔ c ∩ p ∩ p' ≠ c ∩ p := by
  simp [Informative, Set.inter_eq_left]

/-- (5): scalar assertion. The worlds of the context where `p` holds and no alternative holds
that would have been informative after `p`; a strengthening item is licensed where this is
not contradictory. -/
def scalAssert (c p : Set W) (alts : Set (Set W)) : Set W :=
  {w | w ∈ c ∧ w ∈ p ∧ ¬ ∃ p' ∈ alts, w ∈ p' ∧ Informative c p p'}

/-- (6): the licensing condition for attenuating items. The worlds of the context where `p`
holds and some alternative compatible with the context would have been informative after
`p`. -/
def attenAssert (c p : Set W) (alts : Set (Set W)) : Set W :=
  {w | w ∈ c ∧ w ∈ p ∧ ∃ p' ∈ alts, (c ∩ p').Nonempty ∧ Informative c p p'}

/-- The assertion is the strongest of its alternatives in the context: it entails each of
them. -/
def IsStrongest (c p : Set W) (alts : Set (Set W)) : Prop := ∀ p' ∈ alts, c ∩ p ⊆ p'

variable {c p q : Set W} {alts : Set (Set W)}

/-- An assertion stronger than all its alternatives passes scalar assertion as the plain
update: the licensed case of a strengthening item. -/
theorem scalAssert_eq_of_isStrongest (h : IsStrongest c p alts) : scalAssert c p alts = c ∩ p := by
  ext w
  simp only [scalAssert, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun ⟨hc, hp, _⟩ ↦ ⟨hc, hp⟩, fun ⟨hc, hp⟩ ↦ ⟨hc, hp, fun ⟨p', hp', _, hi⟩ ↦ hi (h p' hp')⟩⟩

/-- An assertion stronger than all its alternatives fails the attenuating condition
outright. -/
theorem attenAssert_eq_empty_of_isStrongest (h : IsStrongest c p alts) :
    attenAssert c p alts = ∅ := by
  ext w
  simp only [attenAssert, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact fun ⟨_, _, p', hp', _, hi⟩ ↦ hi (h p' hp')

theorem scalAssert_eq_empty_of_cover
    (h : ∀ w ∈ c ∩ p, ∃ p' ∈ alts, w ∈ p' ∧ Informative c p p') : scalAssert c p alts = ∅ := by
  ext w
  simp only [scalAssert, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact fun ⟨hc, hp, hn⟩ ↦ hn (h w ⟨hc, hp⟩)

theorem attenAssert_eq_of_exists (h : ∃ p' ∈ alts, (c ∩ p').Nonempty ∧ Informative c p p') :
    attenAssert c p alts = c ∩ p := by
  ext w
  simp only [attenAssert, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun ⟨hc, hp, _⟩ ↦ ⟨hc, hp⟩, fun ⟨hc, hp⟩ ↦ ⟨hc, hp, h⟩⟩

/-! ### The lexical scales (4) -/

section Scales

variable {T D : Type*} [Preorder D] (at' : T → Set W) (μ : W → D)

/-- *ever*: at some time; its alternatives are the specific times (4a). -/
def ever : Set W := ⋃ t, at' t

/-- The alternatives of `ever`. -/
def everAlts : Set (Set W) := Set.range at'

theorem isStrongest_not_ever (c : Set W) :
    IsStrongest c (ever at')ᶜ (compl '' everAlts at') := by
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩ w ⟨_, hw⟩ ht
  exact hw (Set.mem_iUnion.2 ⟨t, ht⟩)

/-- (2a), (4a): under negation *ever* is licensed, scalar assertion being the plain update. -/
theorem scalAssert_not_ever (c : Set W) :
    scalAssert c (ever at')ᶜ (compl '' everAlts at') = c ∩ (ever at')ᶜ :=
  scalAssert_eq_of_isStrongest (isStrongest_not_ever at' c)

/-- (2a): in the affirmative *ever* is covered by its specific times, each informative after
it, so scalar assertion is contradictory and the item unlicensed. -/
theorem scalAssert_ever_eq_empty (c : Set W) (hinf : ∀ t, Informative c (ever at') (at' t)) :
    scalAssert c (ever at') (everAlts at') = ∅ :=
  scalAssert_eq_empty_of_cover fun _ ⟨_, hw⟩ ↦
    let ⟨t, ht⟩ := Set.mem_iUnion.1 hw
    ⟨_, ⟨t, rfl⟩, ht, hinf t⟩

/-- The degree reaches `d`. -/
def atLeast (d : D) : Set W := {w | d ≤ μ w}

theorem atLeast_antitone : Antitone (atLeast μ) := fun _ _ h _ hw ↦ h.trans hw

/-- The alternatives of an attenuating degree modifier at `d` are the lower degrees
([israel-1996]). -/
def lowerAlts (d : D) : Set (Set W) := {p | ∃ d' < d, p = atLeast μ d'}

theorem isStrongest_atLeast (c : Set W) (d : D) : IsStrongest c (atLeast μ d) (lowerAlts μ d) := by
  rintro _ ⟨d', hd', rfl⟩ w ⟨_, hw⟩
  exact atLeast_antitone μ hd'.le hw

/-- (4b): under negation a lower degree is the stronger alternative, and one that is compatible
with the context and informative licenses the attenuating item. -/
theorem attenAssert_not_atLeast (c : Set W) {d d' : D} (hd : d' < d)
    (hne : (c ∩ (atLeast μ d')ᶜ).Nonempty) (hi : Informative c (atLeast μ d)ᶜ (atLeast μ d')ᶜ) :
    attenAssert c (atLeast μ d)ᶜ (compl '' lowerAlts μ d) = c ∩ (atLeast μ d)ᶜ :=
  attenAssert_eq_of_exists ⟨_, ⟨atLeast μ d', ⟨d', hd, rfl⟩, rfl⟩, hne, hi⟩

end Scales

/-! ### The illusion (§4) -/

theorem illusion_asymmetry (hq : IsStrongest c q alts) :
    scalAssert c q alts = c ∩ q ∧ attenAssert c q alts = ∅ :=
  ⟨scalAssert_eq_of_isStrongest hq, attenAssert_eq_empty_of_isStrongest hq⟩

/-! ### The experiments -/

/-- The paper's readings of a Bayes factor, ranked from the strongest evidence for the null to
the strongest for the effect. -/
def verdictRank : Verdict → ℕ
  | .moderateForNull => 0
  | .slightlyForNull => 1
  | .inconclusive => 2
  | .moderateForEffect => 3
  | .veryStrongForEffect => 4

/-- The paper's readings are monotone in the Bayes factor: a larger BF10 is never read as weaker
evidence for its effect. -/
theorem verdictRank_monotone : ∀ e₁ f₁ e₂ f₂,
    (bayesFactors e₁ f₁).bf10.toRat < (bayesFactors e₂ f₂).bf10.toRat →
      verdictRank (bayesFactors e₁ f₁).verdict ≤ verdictRank (bayesFactors e₂ f₂).verdict := by
  decide +kernel

/-- An effect is attested in an experiment when the paper reads its Bayes factor as at least
moderate evidence for it. -/
def Attested (e : Experiment) (f : Effect) : Prop :=
  verdictRank .moderateForEffect ≤ verdictRank (bayesFactors e f).verdict

instance (e : Experiment) (f : Effect) : Decidable (Attested e f) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem illusion_attested (e : Experiment) :
    Attested e .illusionJemals ∧ ¬Attested e .illusionSoRecht := by
  cases e <;> decide

theorem interaction_attested_iff (e : Experiment) : Attested e .interaction ↔ e = .exp2 := by
  cases e <;> decide

end Schwab2023
