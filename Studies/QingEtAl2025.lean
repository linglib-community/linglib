module

public import Studies.UegakiSudo2019
import Mathlib.Basic.Nontrivial.Basic
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
[L-analytic, and the predicate anti-rogative, exactly for the distributive positive
class](##QingEtAl2025.isLAnalytic_iff_class). Of distributivity, the derivation uses
[only the inference from an answer to the question](##QingEtAl2025.trueWhereDefined_positive_iff).
Apparent uses of *hope* with a polar question are non-canonical, and the asymmetry between hoping
for the radical and for its negation follows from the goals of a hopeful wondering.

## Implementation notes

A Class 1 predicate compares degrees on declaratives and relates the agent to a question by a
parameter, since the paper characterizes the class only as a relation to the question not reducible
to one to any answer. The paper contrasts positive with negative predicates; a neutral one is taken
to lack threshold significance. The pragmatic derivation compares coming to believe the radical or
not by Kratzer's ordering with the event's goals as ordering source; the event summation of the
adjunction analysis is not formalized. Rows carry the paper's truth values where it gives them and
its felicity judgments otherwise; the attested *hope whether* examples are recorded as marginal, and
*temer* with a polar question and *haipa* with a constituent question are recorded but not
predicted.

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

open Examples Preferential Modality UegakiSudo2019

variable {W E : Type*}

/-! ### The two escapes from triviality (§3) -/

section LAnalyticity

variable {D : Type*} [LinearOrder D]

local notation "Family" =>
  (E → W → Set W → D) → (Set (Set W) → D) → Set (Set W) → E → Set (Set W) → W → Prop

/-- Composition with a question is true wherever it is defined, the case of L-analyticity Uegaki and
Sudo derive. -/
def TrueWhereDefined (V π : Family) : Prop :=
  ∀ μ θ C x Q w, C ⊆ Q → Q.Nontrivial → π μ θ C x Q w → V μ θ C x Q w

/-- A family's declarative use compares degrees in every model, as in [uegaki-sudo-2019] (35). -/
def ComparesDegrees (V : Family) : Prop :=
  ∀ μ θ C x p w, V μ θ C x {p} w ↔ p ∈ preferred μ θ C x w

/-- A positive preferential predicate presupposes threshold significance of a question. A
negative one triggers no such presupposition (§3.2) and presupposes only that the question has an
answer in the comparison class. -/
def presupposition : EvaluativeValence → Family
  | .positive => thresholdSignificance
  | .negative | .neutral => fun _ _ C _ Q _ ↦ (Q ∩ C).Nonempty

omit [LinearOrder D] in
theorem TrueWhereDefined.isLAnalytic {V π : Family} (h : TrueWhereDefined V π) : IsLAnalytic V π :=
  ⟨True, fun μ θ C x Q w hCQ hQ hπ ↦ iff_of_true (h μ θ C x Q w hCQ hQ hπ) trivial⟩

/-- With a declarative use that compares degrees, composition with a question is true wherever
threshold significance holds exactly when the predicate is P-to-Q entailing on the question. -/
theorem trueWhereDefined_positive_iff {V : Family} (hV : ComparesDegrees V) :
    TrueWhereDefined V (presupposition .positive) ↔
      ∀ μ θ C Q, C ⊆ Q → Q.Nontrivial → IsPToQEntailing {Q} (V μ θ C) := by
  refine ⟨fun h μ θ C Q hCQ hQ Q' hQ' x w p hp hVp ↦ ?_, fun h μ θ C x Q w hCQ hQ ⟨p, hp, hlt⟩ ↦
    h μ θ C Q hCQ hQ Q rfl x w p (hCQ hp) ((hV ..).2 ⟨hp, hlt⟩)⟩
  obtain rfl : Q' = Q := hQ'
  obtain ⟨hpC, hlt⟩ := (hV ..).1 hVp
  exact h μ θ C x Q' w hCQ hQ ⟨p, hpC, hlt⟩

theorem comparesDegrees_degreeComparison :
    ComparesDegrees (D := D) (W := W) (E := E) degreeComparison :=
  degreeComparison_singleton

-- Class 3, §3.3: Uegaki and Sudo's derivation
theorem trueWhereDefined_of_isClausallyDistributive {V : Family} (hV : ComparesDegrees V)
    (hd : ∀ μ θ C, IsClausallyDistributive Set.univ (V μ θ C)) :
    TrueWhereDefined V (presupposition .positive) :=
  (trueWhereDefined_positive_iff hV).2 fun μ θ C _ _ _ Q _ ↦
    (hd μ θ C).isPToQEntailing Q trivial

-- Class 2, §3.2: without the presupposition the assertion stays contingent
theorem not_isLAnalytic_of_isClausallyDistributive [Nontrivial D] [Inhabited E] [Inhabited W]
    {V : Family} (hV : ComparesDegrees V) (hd : ∀ μ θ C, IsClausallyDistributive Set.univ (V μ θ C))
    {v : EvaluativeValence} (hv : v ≠ .positive) : ¬ IsLAnalytic V (presupposition v) := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, hab⟩ := exists_pair_lt D
  let Q : Set (Set W) := {∅, Set.univ}
  have hQ : Q.Nontrivial := ⟨∅, by simp [Q], Set.univ, by simp [Q], Set.empty_ne_univ⟩
  have hπ : ∀ (μ : E → W → Set W → D) θ, presupposition v μ θ Q default Q default := fun μ θ ↦ by
    cases v
    · exact absurd rfl hv
    all_goals exact ⟨∅, by simp [Q], by simp [Q]⟩
  have ht₁ := (ht (fun _ _ _ ↦ b) (fun _ ↦ a) Q default Q default subset_rfl hQ (hπ _ _)).1 <|
    (hd _ _ _ Q trivial _ _).2 ⟨∅, by simp [Q], (hV ..).2 ⟨by simp [Q], hab⟩⟩
  obtain ⟨p, -, hp⟩ := (hd _ _ _ Q trivial _ _).1 <|
    (ht (fun _ _ _ ↦ a) (fun _ ↦ a) Q default Q default subset_rfl hQ (hπ _ _)).2 ht₁
  exact lt_irrefl a ((hV ..).1 hp).2

/-- A Class 1 predicate compares degrees on declaratives, as (19) and (22) require, and relates its
subject to a question by a relation `R` that does not consult the degrees. -/
def relational (R : E → Set (Set W) → W → Prop) : Family :=
  fun μ θ C x Q w ↦ (Q.Subsingleton ∧ degreeComparison μ θ C x Q w) ∨ (Q.Nontrivial ∧ R x Q w)

theorem comparesDegrees_relational (R : E → Set (Set W) → W → Prop) :
    ComparesDegrees (D := D) (relational R) := fun μ θ C x p w ↦ by
  simp [relational]

variable {R : E → Set (Set W) → W → Prop}

-- Class 1, §3.1: `R` is contingent on questions wherever the presupposition holds
theorem not_isLAnalytic_relational [Nontrivial D] (v : EvaluativeValence)
    (hT : ∃ x Q w, Q.Nontrivial ∧ R x Q w) (hF : ∃ x Q w, Q.Nontrivial ∧ ¬ R x Q w) :
    ¬ IsLAnalytic (D := D) (relational R) (presupposition v) := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, hab⟩ := exists_pair_lt D
  have hπ : ∀ x Q w, Q.Nontrivial →
      presupposition v (fun (_ : E) (_ : W) _ ↦ b) (fun _ ↦ a) Q x Q w := fun x Q w hQ ↦ by
    obtain ⟨p, hp⟩ := hQ.nonempty
    cases v
    · exact ⟨p, hp, hab⟩
    all_goals exact ⟨p, hp, hp⟩
  obtain ⟨x₁, Q₁, w₁, hQ₁, hR₁⟩ := hT
  obtain ⟨x₂, Q₂, w₂, hQ₂, hR₂⟩ := hF
  have ht₁ := (ht _ _ Q₁ x₁ Q₁ w₁ subset_rfl hQ₁ (hπ x₁ Q₁ w₁ hQ₁)).1 (.inr ⟨hQ₁, hR₁⟩)
  obtain ⟨hs, -⟩ | ⟨-, hR⟩ := (ht _ _ Q₂ x₂ Q₂ w₂ subset_rfl hQ₂ (hπ x₂ Q₂ w₂ hQ₂)).2 ht₁
  · exact hQ₂.not_subsingleton hs
  · exact hR₂ hR

-- Class 1 escapes by failing P-to-Q entailment
theorem not_isPToQEntailing_relational [Nontrivial D] (hT : ∃ x Q w, Q.Nontrivial ∧ R x Q w)
    (hF : ∃ x Q w, Q.Nontrivial ∧ ¬ R x Q w) :
    ¬ ∀ μ θ C Q, C ⊆ Q → Q.Nontrivial → IsPToQEntailing {Q} (relational (D := D) R μ θ C) :=
  fun h ↦ not_isLAnalytic_relational .positive hT hF
    ((trueWhereDefined_positive_iff (comparesDegrees_relational R)).2 h).isLAnalytic

/-- A degree comparison, or a relation `R` to the question, in the shape of the disjunctive entry
[uegaki-2022] gives contemplative predicates. -/
def degreeComparisonOr (R : E → Set (Set W) → W → Prop) : Family :=
  fun μ θ C x Q w ↦ degreeComparison μ θ C x Q w ∨ R x Q w

/-- Failing Q-to-P entailment does not block triviality (against pp. 10, 13 and 16). Where a
relation `R` to a question holds of no declarative, a degree comparison or `R` compares degrees on
declaratives and is L-analytic under threshold significance, yet where `R` holds of a question it
relates the agent to no answer. -/
theorem isLAnalytic_degreeComparisonOr (hR : ∀ x p w, ¬ R x {p} w) {x : E} {Q : Set (Set W)} {w : W}
    (hRQ : R x Q w) :
    ComparesDegrees (D := D) (degreeComparisonOr R) ∧
      IsLAnalytic (D := D) (degreeComparisonOr R) (presupposition .positive) ∧
      ∀ (a : D) C, ¬ IsQToPEntailing {Q} (degreeComparisonOr R (fun _ _ _ ↦ a) (fun _ ↦ a) C) := by
  refine ⟨fun μ θ C x p w ↦ by simp [degreeComparisonOr, hR], TrueWhereDefined.isLAnalytic ?_,
    fun a C h ↦ ?_⟩
  · exact fun μ θ C x Q w hCQ _ h ↦
      .inl ((degreeComparison_iff_thresholdSignificant μ θ C hCQ x w).2 h)
  · obtain ⟨p, -, hp⟩ := h Q rfl x w (.inr hRQ)
    obtain ⟨q, -, -, hq⟩ | hp := hp
    · exact lt_irrefl a hq
    · exact hR _ _ _ hp

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

/-- The meaning of a predicate of each class. -/
def semantics (R : E → Set (Set W) → W → Prop) : PredicateClass → Family
  | .nonDistributive _ => relational R
  | .distributiveNegative | .distributivePositive => degreeComparison

/-- Canonical composition with a question is L-analytic, hence anti-rogative, exactly for the
distributive positive class (Table 2). -/
theorem isLAnalytic_iff_class [Nontrivial D] [Inhabited E] [Inhabited W] (c : PredicateClass)
    (hT : ∃ x Q w, Q.Nontrivial ∧ R x Q w) (hF : ∃ x Q w, Q.Nontrivial ∧ ¬ R x Q w) :
    IsLAnalytic (D := D) (semantics R c) (presupposition c.valence) ↔
      c = .distributivePositive := by
  have hd (μ : E → W → Set W → D) (θ : Set (Set W) → D) (C : Set (Set W)) :=
    isClausallyDistributive_degreeComparison μ θ C Set.univ
  cases c
  · exact iff_of_false (not_isLAnalytic_relational _ hT hF) nofun
  · exact iff_of_false
      (not_isLAnalytic_of_isClausallyDistributive (v := .negative)
        comparesDegrees_degreeComparison hd nofun) nofun
  · exact iff_of_true
      (trueWhereDefined_of_isClausallyDistributive comparesDegrees_degreeComparison hd).isLAnalytic
      rfl

end LAnalyticity

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
