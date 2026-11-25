module

public import Studies.UegakiSudo2019
import Mathlib.Basic.Nontrivial.Basic
public import Linglib.Languages.English.Verbs.Inventory
public import Linglib.Languages.Mandarin.Verbs
public import Linglib.Languages.Mandarin.Pinyin
public import Linglib.Languages.Japanese.Verbs
public import Linglib.Languages.Turkish.Verbs
public import Linglib.Languages.Romance.Spanish.Verbs
public import Linglib.Data.Examples.QingEtAl2025
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Qing et al. (2026): When Can Nonveridical Preferential Attitude Predicates Take Questions?

Qing, Özyıldız, Roelofsen, Romero and Uegaki classify nonveridical preferential predicates by
clausal distributivity and evaluative valence. Uegaki and Sudo derive the antirogativity of *hope*
from two assumptions, that the predicate is clausally distributive and that it presupposes
Threshold Significance. Neither holds in general: *worry* and Mandarin *qidai* relate the holder to
the question and to no particular answer, and negative predicates such as *fear* lack the
presupposition. Composition with a question is therefore
[L-analytic, and the predicate antirogative, exactly for the distributive positive
class](##QingEtAl2025.isLAnalytic_iff_class). Of distributivity, the derivation uses
[only the inference from an answer to the question](##QingEtAl2025.trueWhereDefined_positive_iff):
a predicate that fails only the converse inference, from the question to an answer,
[is still L-analytic under the presupposition](##QingEtAl2025.isLAnalytic_degreeComparisonOr).

## Implementation notes

A class 1 predicate compares degrees on declaratives and relates the holder to a question by a
parameter, since the article characterizes the class only as a relation to the question not
reducible to one to any answer.

Rows carry the article's truth values where it gives them and its acceptability marks otherwise.
A row marks its predicate by a span that names the language file entry. The four rows that test
the presupposition on a veridical preferential, *like*, *be happy*, *hate* and *be upset*, mark the
word and record the valence the article gives it. Spanish *temer* with a polar question and
Mandarin *haipa* with a constituent question are recorded and not predicted: the article leaves
them unexplained. It sets aside *hope* with a *whether* complement, whose status speakers dispute,
as a matter for nonclassical composition, and no row records one.

## TODO

The spans of the Japanese and Spanish rows are not checked against the forms of their entries. The
article writes Japanese in Kunrei romanization and the entries are in Hepburn, and the Spanish file
has no inflection.

## References

* [qing-uegaki-2025]
* [uegaki-sudo-2019]
* [gajewski-2002]
* [elliott-etal-2017]
* [white-2021]
* [uegaki-2022]
-/

@[expose] public section

namespace QingEtAl2025

open Examples Preferential UegakiSudo2019

variable {W E : Type*}

/-! ### The two ways out of triviality -/

section LAnalyticity

variable {D : Type*} [LinearOrder D]

local notation "Family" =>
  (E → W → Set W → D) → (Set (Set W) → D) → Set (Set W) → E → Set (Set W) → W → Prop

/-- Composition with a question is true wherever it is defined, the case of L-analyticity Uegaki and
Sudo derive. -/
def TrueWhereDefined (V π : Family) : Prop :=
  ∀ μ θ C x Q w, C ⊆ Q → Q.Nontrivial → π μ θ C x Q w → V μ θ C x Q w

/-- A family's declarative use compares degrees in every model, (4). -/
def ComparesDegrees (V : Family) : Prop :=
  ∀ μ θ C x p w, V μ θ C x {p} w ↔ p ∈ preferred μ θ C x w

/-- A positive preferential predicate presupposes threshold significance of a question, (18b). A
negative one triggers no such presupposition and presupposes only that the question has an answer
in the comparison class. -/
def presupposition : Polarity → Family
  | .positive => thresholdSignificance
  | .negative => fun _ _ C _ Q _ ↦ (Q ∩ C).Nonempty

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

-- class 3: Uegaki and Sudo's derivation, (19a)
theorem trueWhereDefined_of_isClausallyDistributive {V : Family} (hV : ComparesDegrees V)
    (hd : ∀ μ θ C, IsClausallyDistributive Set.univ (V μ θ C)) :
    TrueWhereDefined V (presupposition .positive) :=
  (trueWhereDefined_positive_iff hV).2 fun μ θ C _ _ _ Q _ ↦
    (hd μ θ C).isPToQEntailing Q trivial

-- class 2: without the presupposition the assertion stays contingent, (19b)
theorem not_isLAnalytic_of_isClausallyDistributive [Nontrivial D] [Inhabited E] [Inhabited W]
    {V : Family} (hV : ComparesDegrees V)
    (hd : ∀ μ θ C, IsClausallyDistributive Set.univ (V μ θ C)) :
    ¬ IsLAnalytic V (presupposition .negative) := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, hab⟩ := exists_pair_lt D
  let Q : Set (Set W) := {∅, Set.univ}
  have hQ : Q.Nontrivial := ⟨∅, by simp [Q], Set.univ, by simp [Q], Set.empty_ne_univ⟩
  have hπ : ∀ (μ : E → W → Set W → D) θ, presupposition .negative μ θ Q default Q default :=
    fun μ θ ↦ ⟨∅, by simp [Q], by simp [Q]⟩
  have ht₁ := (ht (fun _ _ _ ↦ b) (fun _ ↦ a) Q default Q default subset_rfl hQ (hπ _ _)).1 <|
    (hd _ _ _ Q trivial _ _).2 ⟨∅, by simp [Q], (hV ..).2 ⟨by simp [Q], hab⟩⟩
  obtain ⟨p, -, hp⟩ := (hd _ _ _ Q trivial _ _).1 <|
    (ht (fun _ _ _ ↦ a) (fun _ ↦ a) Q default Q default subset_rfl hQ (hπ _ _)).2 ht₁
  exact lt_irrefl a ((hV ..).1 hp).2

/-- A class 1 predicate compares degrees on declaratives, as (23) and (26) require, and relates its
subject to a question by a relation `R` that does not consult the degrees. -/
def relational (R : E → Set (Set W) → W → Prop) : Family :=
  fun μ θ C x Q w ↦ (Q.Subsingleton ∧ degreeComparison μ θ C x Q w) ∨ (Q.Nontrivial ∧ R x Q w)

theorem comparesDegrees_relational (R : E → Set (Set W) → W → Prop) :
    ComparesDegrees (D := D) (relational R) := fun μ θ C x p w ↦ by
  simp [relational]

variable {R : E → Set (Set W) → W → Prop}

-- class 1: `R` is contingent on questions wherever the presupposition holds, (19b)
theorem not_isLAnalytic_relational [Nontrivial D] (v : Polarity)
    (hT : ∃ x Q w, Q.Nontrivial ∧ R x Q w) (hF : ∃ x Q w, Q.Nontrivial ∧ ¬ R x Q w) :
    ¬ IsLAnalytic (D := D) (relational R) (presupposition v) := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, hab⟩ := exists_pair_lt D
  have hπ : ∀ x Q w, Q.Nontrivial →
      presupposition v (fun (_ : E) (_ : W) _ ↦ b) (fun _ ↦ a) Q x Q w := fun x Q w hQ ↦ by
    obtain ⟨p, hp⟩ := hQ.nonempty
    cases v
    exacts [⟨p, hp, hab⟩, ⟨p, hp, hp⟩]
  obtain ⟨x₁, Q₁, w₁, hQ₁, hR₁⟩ := hT
  obtain ⟨x₂, Q₂, w₂, hQ₂, hR₂⟩ := hF
  have ht₁ := (ht _ _ Q₁ x₁ Q₁ w₁ subset_rfl hQ₁ (hπ x₁ Q₁ w₁ hQ₁)).1 (.inr ⟨hQ₁, hR₁⟩)
  obtain ⟨hs, -⟩ | ⟨-, hR⟩ := (ht _ _ Q₂ x₂ Q₂ w₂ subset_rfl hQ₂ (hπ x₂ Q₂ w₂ hQ₂)).2 ht₁
  · exact hQ₂.not_subsingleton hs
  · exact hR₂ hR

-- class 1 fails P-to-Q entailment
theorem not_isPToQEntailing_relational [Nontrivial D] (hT : ∃ x Q w, Q.Nontrivial ∧ R x Q w)
    (hF : ∃ x Q w, Q.Nontrivial ∧ ¬ R x Q w) :
    ¬ ∀ μ θ C Q, C ⊆ Q → Q.Nontrivial → IsPToQEntailing {Q} (relational (D := D) R μ θ C) :=
  fun h ↦ not_isLAnalytic_relational .positive hT hF
    ((trueWhereDefined_positive_iff (comparesDegrees_relational R)).2 h).isLAnalytic

/-- A degree comparison, or a relation `R` to the question. -/
def degreeComparisonOr (R : E → Set (Set W) → W → Prop) : Family :=
  fun μ θ C x Q w ↦ degreeComparison μ θ C x Q w ∨ R x Q w

/-- A predicate can fail Q-to-P entailment and still be L-analytic. Where a relation `R` to a
question holds of no declarative, a degree comparison or `R` compares degrees on declaratives and is
L-analytic under threshold significance, yet where `R` holds of a question it relates the holder to
no answer. -/
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
  | nonDistributive (v : Polarity)
  /-- Class 2 consists of the distributive negative predicates. -/
  | distributiveNegative
  /-- Class 3 consists of the positive predicates Uegaki and Sudo describe, only presumed
  distributive, since they take no questions. -/
  | distributivePositive
  deriving DecidableEq, Repr

/-- The valence of a class. -/
def PredicateClass.valence : PredicateClass → Polarity
  | .nonDistributive v => v
  | .distributiveNegative => .negative
  | .distributivePositive => .positive

/-- The meaning of a predicate of each class. -/
def semantics (R : E → Set (Set W) → W → Prop) : PredicateClass → Family
  | .nonDistributive _ => relational R
  | .distributiveNegative | .distributivePositive => degreeComparison

/-- Composition with a question is L-analytic, and the predicate antirogative, exactly for the
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
      (not_isLAnalytic_of_isClausallyDistributive comparesDegrees_degreeComparison hd) nofun
  · exact iff_of_true
      (trueWhereDefined_of_isClausallyDistributive comparesDegrees_degreeComparison hd).isLAnalytic
      rfl

end LAnalyticity

/-! ### The predicates of the rows -/

open Examples (Example Lexeme Valence)

/-- The language file entry of each predicate under test. -/
def Examples.Lexeme.entry : Lexeme → Verb
  | .hope => English.Verbs.hope.toVerb
  | .fear => English.Verbs.fear.toVerb
  | .worry => English.Verbs.worry.toVerb
  | .qidai => Mandarin.qidai
  | .danxin => Mandarin.danxin
  | .haipa => Mandarin.haipa
  | .tanosimi => Japanese.tanoshimi
  | .sinpai => Japanese.shinpai
  | .osore => Japanese.osore
  | .preocupar => Spanish.Verbs.preocupar
  | .temer => Spanish.Verbs.temer
  | .endiselen => Turkish.endişelen.toVerb
  | .kork => Turkish.kork.toVerb

/-- The language of each predicate under test. -/
def Examples.Lexeme.language : Lexeme → Glottocode
  | .hope | .fear | .worry => .english
  | .qidai | .danxin | .haipa => .mandarinChinese
  | .tanosimi | .sinpai | .osore => .japanese
  | .preocupar | .temer => .spanish
  | .endiselen | .kork => .turkish

/-- The valence of a predicate, as its entry records it. -/
def Examples.Lexeme.valence? (l : Lexeme) : Option Polarity :=
  l.entry.attitude.bind Attitude.valence

/-- The predicates Table 2 classifies as not clausally distributive. -/
def nonDistributive : List Lexeme :=
  [.qidai, .tanosimi, .worry, .sinpai, .danxin, .preocupar, .endiselen]

/-- The class of a predicate, by Table 2's distributivity and the valence its entry records. -/
def Examples.Lexeme.class? (l : Lexeme) : Option PredicateClass :=
  l.valence?.map fun v ↦
    if l ∈ nonDistributive then .nonDistributive v else
      match v with
      | .positive => .distributivePositive
      | .negative => .distributiveNegative

/-- The polarity of the valence the article gives a veridical preferential. -/
def Examples.Valence.polarity : Valence → Polarity
  | .positive => .positive
  | .negative => .negative

namespace Examples.Example

/-- The class of the predicate an example marks. -/
def class? (x : Example) : Option PredicateClass := (x.lexemes .predicate).head?.bind Lexeme.class?

/-- The valence of the predicate under test: the one the article gives a veridical preferential,
and otherwise the one the entry records. -/
def valence? (x : Example) : Option Polarity :=
  (x.valence.map Valence.polarity).orElse fun _ ↦ (x.lexemes .predicate).head?.bind Lexeme.valence?

/-- The judgment of an example as an embedded question, which is that of the question parse where
the article judges the parses of a clause apart. -/
def questionJudgment (x : Example) : Judgment := (x.reading .question).getD x.datum.judgment

end Examples.Example

-- Table 2, class 3: the positive predicates the article lists beside *hope* have no row
theorem class3_valence :
    ∀ v ∈ [English.Verbs.hope.toVerb, Japanese.nozomu, Mandarin.xiwang, Spanish.Verbs.esperar,
        Turkish.um.toVerb], v.attitude = some (.preferential .positive) := by
  decide

/-! ### The article's judgments -/

/-- The rows the article leaves unexplained: Spanish *temer* with a polar question, (58), and
Mandarin *haipa* with a constituent question, (60) and footnote 10. -/
def unexplained : List Example := [.es_58, .zh_60, .zh_fn10_i]

/-- With an interrogative complement a predicate is acceptable exactly outside the distributive
positive class (Table 2), the unexplained rows apart. -/
theorem acceptable_iff_class :
    ∀ x : Example, x ∉ unexplained → x.clause ≠ some .declarative → ∀ c ∈ x.class?,
      (x.questionJudgment = .acceptable ↔ c ≠ .distributivePositive) := by
  decide +kernel

theorem unexplained_class :
    ∀ x ∈ unexplained,
      x.class? = some .distributiveNegative ∧ x.questionJudgment ≠ .acceptable := by
  decide +kernel

-- (42), (44), (48), (53), (56): negated, where no answer clears the threshold
theorem negated_acceptable_iff :
    ∀ x : Example, x.polarity = some .negated → ∀ v ∈ x.valence?,
      (x.datum.judgment = .acceptable ↔ v = .negative) := by
  decide +kernel

-- (28)–(29), (31)–(34), (36): in one context the question is true and each declarative false
theorem nondistributive_rows :
    ∀ x : Example, x.datum.verdict = some false → x.clause = some .declarative →
      (∃ l ∈ x.lexemes .predicate, l ∈ nonDistributive) ∧
        ∃ y : Example, y.datum.context = x.datum.context ∧
          y.lexemes .predicate = x.lexemes .predicate ∧
          y.clause = some .constituent ∧ y.datum.verdict = some true := by
  decide +kernel

-- (46), (49)–(51), (54): a distributive negative predicate is used of either answer
theorem answer_rows :
    (∀ x : Example, ∀ a ∈ x.answer,
        x.class? = some .distributiveNegative ∧ x.datum.judgment = .acceptable) ∧
      ∀ l ∈ [Lexeme.fear, .kork, .osore], ∀ a : Examples.Answer,
        ∃ x : Example, l ∈ x.lexemes .predicate ∧ x.answer = some a := by
  decide +kernel

/-! ### The words of the rows -/

-- every span names a predicate of the row's language or, on a veridical preferential, none
theorem lexeme_language :
    ∀ x : Example, ∀ l ∈ x.lexemes .predicate, x.datum.language = l.language := by
  decide +kernel

/-- A word is a form of an English verb if the entry realizes it in some cell. -/
def IsFormOf (w : List Char) (v : English.Verbs.Verb) : Prop :=
  ∃ c ∈ [English.Verbs.Verb.Cell.base, .thirdSg, .presentParticiple], w = (v.realize c).toList

instance (w : List Char) (v : English.Verbs.Verb) : Decidable (IsFormOf w v) :=
  inferInstanceAs (Decidable (∃ c ∈ _, _))

/-- The English verb of a predicate. -/
def Examples.Lexeme.english? : Lexeme → Option English.Verbs.Verb
  | .hope => some English.Verbs.hope
  | .fear => some English.Verbs.fear
  | .worry => some English.Verbs.worry
  | _ => none

theorem english_forms :
    ∀ x : Example, x.datum.language = .english → ∀ p ∈ x.datum.spans, ∀ l ∈ lexeme? p,
      ∃ v ∈ l.english?, ∃ w ∈ (p.words x.datum).head?, IsFormOf w.word v := by
  decide +kernel

theorem mandarin_forms :
    ∀ x : Example, x.datum.language = .mandarinChinese → ∀ p ∈ x.datum.spans, ∀ l ∈ lexeme? p,
      ∃ w ∈ (p.words x.datum).head?, ∃ m ∈ l.entry.morphs.head?,
        w.word = Mandarin.toneless m.form := by
  decide +kernel

/-- The Turkish verb of a predicate. -/
def Examples.Lexeme.turkish? : Lexeme → Option Turkish.Verb
  | .endiselen => some Turkish.endişelen
  | .kork => some Turkish.kork
  | _ => none

/-- The article's glosses segment its Turkish finite verbs into the imperfective and its
negative. -/
def turkishInflections : List (List (Σ σ, Turkish.Verb.Exponent σ)) :=
  [[⟨_, .iyor⟩], [⟨_, .negative⟩, ⟨_, .iyor⟩]]

theorem turkish_forms :
    ∀ x : Example, x.datum.language = .turkish → ∀ p ∈ x.datum.spans, ∀ l ∈ lexeme? p,
      ∃ v ∈ l.turkish?, ∃ sfx ∈ turkishInflections,
        Turkish.Verb.template.Licensed (v.suffixes sfx) ∧
          ∃ w ∈ (p.words x.datum).head?,
            Turkish.Phonology.ofSegmented? (String.ofList w.word) = some (v.inflect sfx) := by
  decide +kernel

end QingEtAl2025
