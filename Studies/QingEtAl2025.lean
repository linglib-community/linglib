module

public import Linglib.Semantics.Attitudes.Preference.Degree
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Linglib.Semantics.Modality.Background
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.Mandarin.Verbs
public import Linglib.Fragments.Japanese.Verbs
public import Linglib.Fragments.Turkish.Verbs
public import Linglib.Fragments.Romance.Spanish.Verbs
public import Linglib.Data.Examples.QingEtAl2025
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Qing et al. (2025): When Can Non-Veridical Preferential Attitude Predicates Take Questions?

Qing, Özyıldız, Roelofsen, Romero and Uegaki classify non-veridical preferential predicates by
clausal distributivity and evaluative valence. Uegaki and Sudo derive the anti-rogativity of
*hope* from two assumptions, that the predicate is clausally distributive and that it presupposes
Threshold Significance. Neither holds in general: *worry* and Mandarin *qidai* relate the agent
to the question rather than to an answer, and negative predicates such as *fear* lack the
presupposition. Composition with a question is therefore
[trivial, and the predicate anti-rogative, exactly for the distributive positive
class](##QingEtAl2025.trivial_iff_class). Of distributivity, the derivation
[uses only the inference from an answer to the question](##QingEtAl2025.trivial_positive_iff).
Apparent uses of *hope* with a polar question are non-canonical, and the asymmetry between hoping
for the radical and for its negation follows from the goals of a hopeful wondering.

## Implementation notes

Triviality quantifies over the degree function and threshold, the non-logical constants of
Gajewski's analyticity, with the question as its own comparison class. A relational predicate is a
parameter relating the agent to the question, since the paper characterizes the class only as a
relation to the question not reducible to one to any answer. The paper contrasts positive with
negative predicates; a neutral one is taken to lack threshold significance. The pragmatic derivation
compares coming to believe the radical or not by Kratzer's ordering with the event's goals as
ordering source; the event summation of the adjunction analysis is not formalized. Rows carry the
paper's truth values where it gives them and its felicity judgments otherwise; the attested
*hope whether* examples are recorded as marginal, and *temer* with a polar question and *haipa* with
a constituent question are recorded but not predicted.

## Errata

* Non-distributivity is said to block triviality (pp. 10, 13, 16), but the examples refute only the
  inference from the question to an answer, and [a predicate can fail it and stay
  trivial](##QingEtAl2025.trivial_degreeComparisonOr).

## References

* [qing-uegaki-2025]
* [uegaki-sudo-2019]
* [gajewski-2002]
* [villalta-2008]
* [elliott-etal-2017]
* [white-2021]
* [uegaki-2022]
* [tabatowski-2022]
* [ozyildiz-uegaki-2024]
* [kratzer-1981]
-/

@[expose] public section

namespace QingEtAl2025

open Examples Preferential Modality

variable {W E : Type*}

/-! ### The two escapes from triviality (§3)

The concrete models measure preference in the reals. -/

section Triviality

variable (V : (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → Set (Set W) → E → Set (Set W) → W → Prop)

/-- Composition of a predicate family with a question is trivial under a presupposition when in
every model the presupposition entails the assertion, the question serving as its own comparison
class as in Uegaki and Sudo's account. The composition is then true whenever defined, which is
Gajewski's analyticity with the degree function and threshold as the non-logical constants. -/
def Trivial (π : (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → E → Set (Set W) → W → Prop) : Prop :=
  ∀ μ θ x Q w, π μ θ x Q w → V μ θ Q x Q w

/-- A family's declarative use compares degrees in every model, as in [uegaki-sudo-2019] (35). -/
def ComparesDegrees : Prop := ∀ μ θ C x p w, V μ θ C x {p} w ↔ p ∈ preferred μ θ C x w

variable {V}

/-- A positive preferential predicate presupposes threshold significance of a question. A
negative one triggers no such presupposition (§3.2) and presupposes only that the question has an
answer in the comparison class. -/
def presupposition : EvaluativeValence →
    (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → E → Set (Set W) → W → Prop
  | .positive => fun μ θ x Q w ↦ Preferential.ThresholdSignificant (μ x w) θ Q
  | .negative | .neutral => fun _ _ _ Q _ ↦ Q.Nonempty

/-- With a declarative use that compares degrees, composition with a question is trivial under
threshold significance exactly when the predicate is P-to-Q entailing on each question, with that
question as comparison class. -/
theorem trivial_positive_iff (hV : ComparesDegrees V) :
    Trivial V (presupposition .positive) ↔ ∀ μ θ Q, IsPToQEntailing {Q} (V μ θ Q) := by
  refine ⟨fun h μ θ Q Q' hQ' x w p hp hVp ↦ ?_,
    fun h μ θ x Q w ⟨p, hp, hlt⟩ ↦ h μ θ Q Q rfl x w p hp ((hV ..).2 ⟨hp, hlt⟩)⟩
  obtain rfl : Q' = Q := hQ'
  exact h μ θ x Q' w ⟨p, hp, ((hV ..).1 hVp).2⟩

theorem comparesDegrees_degreeComparison : ComparesDegrees (W := W) (E := E) degreeComparison :=
  degreeComparison_singleton

-- Class 3, §3.3: Uegaki and Sudo's derivation
theorem trivial_positive :
    Trivial (W := W) (E := E) degreeComparison (presupposition .positive) :=
  (trivial_positive_iff comparesDegrees_degreeComparison).2 fun μ θ Q ↦
    (isClausallyDistributive_degreeComparison μ θ Q _).isPToQEntailing

-- Class 2, §3.2: without it the equivalence fails "even if they are C-distributive"
theorem not_trivial_of_ne_positive [Inhabited E] [Inhabited W] (hV : ComparesDegrees V)
    {v : EvaluativeValence} (hv : v ≠ .positive) : ¬ Trivial V (presupposition v) := fun h ↦ by
  have hp := (hV ..).1 (h (fun _ _ _ ↦ 0) (fun _ ↦ 0) default {∅} default <| by
    cases v <;> simp_all [presupposition])
  simp [mem_preferred] at hp

-- Class 1, §3.1: a relation independent of the model, which thereby fails P-to-Q entailment
theorem not_trivial_relational (v : EvaluativeValence) (R : E → Set (Set W) → W → Prop)
    (hR : ∃ x Q w, Q.Nonempty ∧ ¬ R x Q w) :
    ¬ Trivial (fun _ _ _ ↦ R) (presupposition v) := fun h ↦ by
  obtain ⟨x, Q, w, hQ, hxQ⟩ := hR
  refine hxQ (h (fun _ _ _ ↦ 1) (fun _ ↦ 0) x Q w ?_)
  cases v
  · obtain ⟨p, hp⟩ := hQ
    exact ⟨p, hp, by norm_num⟩
  all_goals exact hQ

/-- A degree comparison, or a relation `R` to the question, in the shape of the disjunctive entry
[uegaki-2022] gives contemplative predicates. -/
def degreeComparisonOr (R : E → Set (Set W) → W → Prop) :
    (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → Set (Set W) → E → Set (Set W) → W → Prop :=
  fun μ θ C x Q w ↦ degreeComparison μ θ C x Q w ∨ R x Q w

/-- Failing Q-to-P entailment does not block triviality (against pp. 10, 13 and 16). Where a
relation `R` to a question holds of no declarative, a degree comparison or `R` is trivial under
threshold significance, yet where `R` holds of a question it relates the agent to no answer. -/
theorem trivial_degreeComparisonOr {R : E → Set (Set W) → W → Prop} (hR : ∀ x p w, ¬ R x {p} w)
    {x : E} {Q : Set (Set W)} {w : W} (hRQ : R x Q w) :
    Trivial (degreeComparisonOr R) (presupposition .positive) ∧
      ∀ C, ¬ IsQToPEntailing {Q} (degreeComparisonOr R (fun _ _ _ ↦ 0) (fun _ ↦ 0) C) := by
  refine ⟨fun μ θ x Q w h ↦ .inl (trivial_positive μ θ x Q w h), fun C h ↦ ?_⟩
  obtain ⟨p, -, hp⟩ := h Q rfl x w (.inr hRQ)
  obtain ⟨q, -, -, hq⟩ | hp := hp
  · simp at hq
  · exact hR _ _ _ hp

end Triviality

/-! ### The classification (Table 2) -/

/-- The three classes of non-veridical preferential predicates. -/
inductive PredicateClass
  /-- Class 1 consists of the predicates that are not clausally distributive, of either valence. -/
  | nonDistributive (v : EvaluativeValence)
  /-- Class 2 consists of the distributive negative predicates. -/
  | distributiveNegative
  /-- Class 3 consists of the positive predicates Uegaki and Sudo describe, only presumed
  distributive, since they take no questions (footnote 10). -/
  | distributivePositive
  deriving DecidableEq, Repr

/-- The valence of a class. -/
def PredicateClass.valence : PredicateClass → EvaluativeValence
  | .nonDistributive v => v
  | .distributiveNegative => .negative
  | .distributivePositive => .positive

/-- The interrogative use of a preferential predicate is a relation `R` to the question in Class 1
and a degree comparison otherwise. -/
def semantics (R : E → Set (Set W) → W → Prop) : PredicateClass →
    (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → Set (Set W) → E → Set (Set W) → W → Prop
  | .nonDistributive _ => fun _ _ _ ↦ R
  | .distributiveNegative | .distributivePositive => degreeComparison

/-- Canonical composition with a question is trivial, hence anti-rogative, exactly for the
distributive positive class (Table 2). -/
theorem trivial_iff_class [Inhabited E] [Inhabited W] (c : PredicateClass)
    (R : E → Set (Set W) → W → Prop) (hR : ∃ x Q w, Q.Nonempty ∧ ¬ R x Q w) :
    Trivial (semantics R c) (presupposition c.valence) ↔ c = .distributivePositive := by
  cases c
  · exact iff_of_false (not_trivial_relational _ R hR) nofun
  · exact iff_of_false (not_trivial_of_ne_positive comparesDegrees_degreeComparison nofun) nofun
  · exact iff_of_true trivial_positive rfl

/-! ### The paper's judgments -/

/-- `attitude? s` is the attitude that the predicate name `s` denotes, read off the Fragment
entry for English, Mandarin, Japanese, Turkish, and Spanish *esperar*, and off the paper for the
other Spanish predicates, *temer* and *preocupar*, which have no Fragment entry. -/
def attitude? : String → Option Attitude
  | "hope" => English.Verbs.hope.attitude
  | "fear" => English.Verbs.fear.attitude
  | "worry" => English.Verbs.worry.attitude
  | "qidai" => Mandarin.qidai.attitude
  | "danxin" => Mandarin.danxin.attitude
  | "xiwang" => Mandarin.xiwang.attitude
  | "haipa" => Mandarin.haipa.attitude
  | "tanosimi" => Japanese.tanoshimi.attitude
  | "sinpai" => Japanese.shinpai.attitude
  | "osore" => Japanese.osore.attitude
  | "nozomu" => Japanese.nozomu.attitude
  | "kork" => Turkish.kork.attitude
  | "um" => Turkish.um.attitude
  | "endiselen" => Turkish.endişelen.attitude
  | "preocupar" => some (.preferential .negative)
  | "temer" => some (.preferential .negative)
  | "esperar" => Spanish.Verbs.esperar.attitude
  | _ => none

/-- The predicates Table 2 classifies as not clausally distributive. -/
def nonDistributive : List String :=
  ["qidai", "tanosimi", "worry", "sinpai", "danxin", "preocupar", "endiselen"]

/-- The class of a predicate named `s`, by Table 2's distributivity and the valence its attitude
records. A distributive predicate of neutral valence is outside the classification. -/
def classOf (s : String) : Attitude → Option PredicateClass
  | .preferential v =>
    if s ∈ nonDistributive then some (.nonDistributive v) else
      match v with
      | .negative => some .distributiveNegative
      | .positive => some .distributivePositive
      | .neutral => none
  | .doxastic _ => none

/-- The class of a row's predicate. -/
def class? (r : Datum) : Option PredicateClass :=
  (r.feature? "predicate").bind fun s ↦ (attitude? s).bind (classOf s)

/-- The valence of a row's predicate, or of its manner adverb or veridical preferential where
the paper's argument turns on valence alone. -/
def valence? (r : Datum) : Option EvaluativeValence :=
  match r.feature? "valence" with
  | some "positive" => some .positive
  | some "negative" => some .negative
  | _ => ((r.feature? "predicate").bind attitude?).bind Attitude.valence

/-- A row holds in its context when it is judged true, where the paper gives a truth value, and
when it is not infelicitous otherwise. -/
def Holds (r : Datum) : Prop :=
  match r.verdict with
  | some t => t = true
  | none => r.judgment ≠ .unacceptable

instance (r : Datum) : Decidable (Holds r) := by unfold Holds; split <;> infer_instance

/-- An interrogative complement composed canonically, as the predicate's argument. -/
def Argument (r : Datum) : Prop :=
  r.feature? "embedding" = some "argument" ∧ r.feature? "clause" ≠ some "declarative"

instance (r : Datum) : Decidable (Argument r) := by unfold Argument; infer_instance

/-- Under canonical composition an interrogative complement is acceptable exactly outside Class 3
(Table 2), but for the *temer* and *haipa* examples the paper sets aside (p. 16). -/
theorem canonical_rows :
    ∀ r ∈ Examples.all, Argument r → ∀ c ∈ class? r,
      (c ≠ .distributivePositive ↔
        r.judgment = .acceptable ∨ r.feature? "predicate" ∈ [some "temer", some "haipa"]) := by
  decide +kernel

-- (38), (41), (44), (49), (52)
theorem tsp_rows :
    ∀ r ∈ Examples.all, r.feature? "polarity" = some "negated" →
      ∀ v ∈ valence? r, (r.judgment = .acceptable ↔ v = .negative) := by
  decide +kernel

-- (23), (36)
theorem nondistributive_rows :
    ∀ r ∈ Examples.all, r.verdict = some false →
      r.feature? "clause" = some "declarative" →
        (∃ s ∈ r.feature? "predicate", s ∈ nonDistributive) ∧
          ∃ r' ∈ Examples.all, r'.context = r.context ∧
          r'.feature? "predicate" = r.feature? "predicate" ∧
          r'.feature? "clause" = some "constituent" ∧ r'.verdict = some true := by
  decide +kernel

-- (71), (73), (75), (76)
theorem diye_rows :
    ∀ r ∈ Examples.all, r.feature? "embedding" = some "diye" → r.judgment = .acceptable := by
  decide +kernel

/-- `turkishVerb? s` is the Fragment verb that the predicate name `s` of a Turkish row names. -/
def turkishVerb? : String → Option Turkish.Verb
  | "kork" => some Turkish.kork
  | "um" => some Turkish.um
  | "endiselen" => some Turkish.endişelen
  | "dolan" => some Turkish.dolan
  | _ => none

/-- The paper's glosses segment its Turkish finite verbs into four inflections, the
imperfective, its negative, its past, and the perfective past, the last two in the first
person. -/
def turkishInflections : List (List (Σ σ, Turkish.Verb.Exponent σ)) :=
  [[⟨_, .iyor⟩], [⟨_, .negative⟩, ⟨_, .iyor⟩],
    [⟨_, .iyor⟩, ⟨_, .pastCopula⟩, ⟨_, .person .one (.personNumber .first .singular)⟩],
    [⟨_, .di⟩, ⟨_, .person .one (.personNumber .first .singular)⟩]]

theorem turkish_forms :
    ∀ r ∈ Examples.all, r.language = .turkish →
      ∃ v ∈ (r.feature? "predicate").bind turkishVerb?, ∃ sfx ∈ turkishInflections,
        Turkish.Verb.template.Licensed (v.suffixes sfx) ∧
          ∃ t ∈ r.glossedTokens, Turkish.Phonology.ofSegmented? t.1 = some (v.inflect sfx) := by
  decide +kernel

-- (73)
theorem dolan_isIntransitive : Turkish.dolan.IsIntransitive := by decide

/-! ### Non-canonical composition (§4) -/

-- (70), §4.2
theorem highlighted_eq_declarative (μ : E → W → Set W → ℝ) (θ : Set (Set W) → ℝ)
    (C : Set (Set W)) (x : E) (p : Set W) (w : W) :
    degreeComparison μ θ C x {p} w ↔ p ∈ preferred μ θ C x w :=
  degreeComparison_singleton μ θ C x p w

section Asymmetry

variable {V : Type*} {p Bp Bnp : V → Prop} {v₁ v₂ : V}

/-- The goals of a hopeful event whose agent hopes `φ` are `φ` or the agent's believing `φ`
(89). -/
def HopefulGoals (φ Bφ : V → Prop) (G : Set (V → Prop)) : Prop := ∀ g ∈ G, g = φ ∨ g = Bφ

theorem hopes_radical (h₁ : Bp v₁) (h₂ : ¬ Bp v₂) : v₁ <[{Bp}] v₂ := by
  simp only [Preorder.ofCriteria_lt_iff, Preorder.ofCriteria_le_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h ↦ (h₂ h).elim, fun h ↦ h₂ (h h₁)⟩

/-- When the agent hopes for the negation (89), coming to believe `p` is no better than not, so the
wondering cannot be hopeful. -/
theorem hopes_negation {G : Set (V → Prop)} (hG : HopefulGoals (fun v ↦ ¬ p v) Bnp G)
    (hp₁ : p v₁) (hn₁ : ¬ Bnp v₁) : ¬ v₁ <[G] v₂ := by
  rintro ⟨-, h⟩
  refine h fun g hg hg₁ ↦ ?_
  rcases hG g hg with rfl | rfl
  · exact absurd hp₁ hg₁
  · exact absurd hg₁ hn₁

-- (87)
theorem fears (h₁ : Bp v₁) (h₂ : ¬ Bp v₂) (hn₂ : ¬ Bnp v₂) :
    v₁ <[{fun v ↦ Bp v ∨ Bnp v}] v₂ := by
  simp only [Preorder.ofCriteria_lt_iff, Preorder.ofCriteria_le_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h ↦ (h.elim h₂ hn₂).elim, fun h ↦ (h (Or.inl h₁)).elim h₂ hn₂⟩

end Asymmetry

-- (45), (50), (62), (63), (75), (76), (78), (79)
theorem asymmetry_rows :
    ∀ r ∈ Examples.all, ∀ t ∈ r.feature? "target", ∀ v ∈ valence? r,
      (v = .positive → (Holds r ↔ t = "radical")) ∧ (v = .negative → Holds r) := by
  decide +kernel

end QingEtAl2025
