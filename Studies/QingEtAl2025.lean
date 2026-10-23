module

public import Studies.UegakiSudo2019
public import Linglib.Semantics.Modality.Background
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.Mandarin.Verbs
public import Linglib.Fragments.Japanese.Verbs
public import Linglib.Fragments.Turkish.Verbs
public import Linglib.Fragments.Romance.Spanish.Verbs
public import Linglib.Data.Examples.QingEtAl2025

/-!
# Qing et al. (2025): When Can Non-Veridical Preferential Attitude Predicates Take Questions?

Qing, Özyıldız, Roelofsen, Romero and Uegaki classify non-veridical preferential predicates by
clausal distributivity and evaluative valence. Uegaki and Sudo derive the anti-rogativity of
*hope* from two assumptions, that the predicate is clausally distributive and that it presupposes
Threshold Significance. Neither holds in general: *worry* and Mandarin *qidai* relate the agent
to the question rather than to an answer, and negative predicates such as *fear* lack the
presupposition. Composition with a question is therefore trivial, and the predicate
anti-rogative, exactly for the distributive positive class. Apparent uses of *hope* with a polar
question are non-canonical, and the asymmetry between hoping for the radical and for its negation
follows from the goals of a hopeful wondering.

## Main statements

* `relational_not_isDistributive`: a predicate related to a question but to none of its answers
  is not clausally distributive.
* `trivial_iff_class`: composition with a question is trivial exactly for the distributive
  positive class.
* `responsive_rows`, `anti_rogative_rows`, `tsp_rows`, `nondistributive_rows`: the paper's
  judgments in five languages.
* `hopes_radical`, `hopes_negation`: hoping for the radical licenses the wondering and hoping for
  its negation does not.

## Implementation notes

Triviality quantifies over the degree function and threshold, the non-logical constants of
Gajewski's analyticity, with the question as its own comparison class, and the concrete models
measure preference in the reals. A relational predicate is a parameter relating the agent to the
question, since the paper characterizes the class only as a relation to the question not reducible
to one to any answer. The class of a predicate is read off the valence and distributivity its
lexical entry records. The paper contrasts positive with negative predicates; a neutral one is taken
to lack threshold significance, as a negative one does. The pragmatic derivation compares coming to
believe the radical or not by Kratzer's ordering with the event's goals as ordering source; the
event summation of the adjunction analysis is not formalized. The Spanish predicates without a
Fragment entry, *temer* and *preocupar*, are classified here. Rows carry the paper's truth values
where it gives them and its felicity judgments otherwise; the attested *hope whether* examples are
recorded as marginal, and *temer* with a polar question and *haipa* with a constituent question are
recorded but not predicted.

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

/-- A predicate that relates an agent to a question without relating her to any of its answers,
anxious uncertainty for *worry* (§3.1.2) or anticipation of resolution for Mandarin *qidai*
(§3.1.1), is not clausally distributive. This is the diagnostic of (23) to (25). -/
theorem relational_not_isDistributive (R : E → Set (Set W) → W → Prop) {x : E}
    {Q : Set (Set W)} {w : W} (hR : R x Q w) (h : ∀ p ∈ Q, ¬ R x {p} w) :
    ¬ Distributivity.IsDistributive R :=
  Distributivity.not_isDistributive_of_forall_not hR h

/-- Composition of a predicate family with a question is trivial under a presupposition when in
every model the presupposition entails the assertion, the question serving as its own comparison
class as in Uegaki and Sudo's account. The composition is then true whenever defined, which is
Gajewski's analyticity with the degree function and threshold as the non-logical constants. -/
def Trivial
    (V : (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → Set (Set W) → E → Set (Set W) → W → Prop)
    (π : (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → E → Set (Set W) → W → Prop) : Prop :=
  ∀ μ θ x Q w, π μ θ x Q w → V μ θ Q x Q w

/-- A positive preferential predicate presupposes threshold significance of a question. A
negative one triggers no such presupposition (§3.2) and presupposes only that the question has an
answer in the comparison class. -/
def presupposition : Degree.EvaluativeValence →
    (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → E → Set (Set W) → W → Prop
  | .positive => fun μ θ x Q w ↦ Degree.ThresholdSignificant (μ x w) θ Q
  | .negative | .neutral => fun _ _ _ Q _ ↦ Q.Nonempty

theorem trivial_positive :
    Trivial (W := W) (E := E) degreeComparison (presupposition .positive) :=
  fun μ θ x _ w h ↦ (UegakiSudo2019.hope_question_iff_significance μ θ subset_rfl x w).2 h

theorem not_trivial_negative [Inhabited E] [Inhabited W] {v : Degree.EvaluativeValence}
    (hv : v ≠ .positive) : ¬ Trivial (W := W) (E := E) degreeComparison (presupposition v) :=
  fun h ↦ by
    obtain ⟨p, -, -, hp⟩ := h (fun _ _ _ ↦ 0) (fun _ ↦ 0) default {∅} default <| by
      cases v <;> simp_all [presupposition]
    simp at hp

theorem not_trivial_relational (v : Degree.EvaluativeValence) (R : E → Set (Set W) → W → Prop)
    (hR : ∃ x Q w, Q.Nonempty ∧ ¬ R x Q w) :
    ¬ Trivial (fun _ _ _ ↦ R) (presupposition v) := fun h ↦ by
  obtain ⟨x, Q, w, hQ, hxQ⟩ := hR
  refine hxQ (h (fun _ _ _ ↦ 1) (fun _ ↦ 0) x Q w ?_)
  cases v
  · obtain ⟨p, hp⟩ := hQ
    exact ⟨p, hp, by norm_num⟩
  all_goals exact hQ

/-! ### The classification (Table 2) -/

/-- The three classes of non-veridical preferential predicates. -/
inductive PredicateClass
  /-- Class 1 consists of the predicates that are not clausally distributive, of either valence. -/
  | nonDistributive
  /-- Class 2 consists of the distributive negative predicates. -/
  | distributiveNegative
  /-- Class 3 consists of the distributive positive predicates, the class Uegaki and Sudo
  describe. -/
  | distributivePositive
  deriving DecidableEq, Repr

/-- The class of a predicate, read off the valence and distributivity its lexical entry records.
A distributive predicate of neutral valence is outside the classification. -/
def classOf : Attitude → Option PredicateClass
  | .preferential _ false => some .nonDistributive
  | .preferential .negative true => some .distributiveNegative
  | .preferential .positive true => some .distributivePositive
  | _ => none

/-- The interrogative use of a preferential predicate is a degree comparison when it is
distributive and a relation `R` to the question otherwise. -/
def semantics (R : E → Set (Set W) → W → Prop) :
    Bool → (E → W → Set W → ℝ) → (Set (Set W) → ℝ) → Set (Set W) → E → Set (Set W) → W → Prop
  | true => degreeComparison
  | false => fun _ _ _ ↦ R

/-- Canonical composition with a question is trivial, hence anti-rogative, exactly for the
distributive positive class (Table 2). -/
theorem trivial_iff_class [Inhabited E] [Inhabited W] (v : Degree.EvaluativeValence) (d : Bool)
    (R : E → Set (Set W) → W → Prop) (hR : ∃ x Q w, Q.Nonempty ∧ ¬ R x Q w) :
    Trivial (semantics R d) (presupposition v) ↔
      classOf (.preferential v d) = some .distributivePositive := by
  cases d
  · exact iff_of_false (not_trivial_relational v R hR) (by simp [classOf])
  · cases v
    · exact iff_of_true trivial_positive rfl
    all_goals exact iff_of_false (not_trivial_negative nofun) (by simp [classOf])

/-! ### The paper's judgments -/

/-- `attitude? s` is the attitude that the predicate name `s` denotes, read off the Fragment
entry for English, Mandarin, Japanese, Turkish, and Spanish *esperar*, and off the paper's
classification for the other Spanish predicates. -/
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
  | "preocupar" => some (.preferential .negative false)
  | "temer" => some (.preferential .negative true)
  | "esperar" => Spanish.Verbs.esperar.attitude
  | _ => none

/-- The class of a row's predicate. -/
def class? (r : Datum) : Option PredicateClass :=
  ((r.feature? "predicate").bind attitude?).bind classOf

/-- The valence of a row's predicate, or of its manner adverb or veridical preferential where
the paper's argument turns on valence alone. -/
def valence? (r : Datum) : Option Degree.EvaluativeValence :=
  match r.feature? "valence" with
  | some "positive" => some .positive
  | some "negative" => some .negative
  | _ => ((r.feature? "predicate").bind attitude?).bind Attitude.valence

/-- A row holds in its context when it is judged true, where the paper gives a truth value, and
when it is not infelicitous otherwise. -/
def Holds (r : Datum) : Prop :=
  match r.feature? "truth" with
  | some t => t = "true"
  | none => r.judgment ≠ .unacceptable

instance (r : Datum) : Decidable (Holds r) := by unfold Holds; split <;> infer_instance

/-- An interrogative complement composed canonically, as the predicate's argument. -/
def Argument (r : Datum) : Prop :=
  r.feature? "embedding" = some "argument" ∧ r.feature? "clause" ≠ some "declarative"

instance (r : Datum) : Decidable (Argument r) := by unfold Argument; infer_instance

/-- Every acceptable interrogative complement is under a class 1 or class 2 predicate. -/
theorem responsive_rows :
    ∀ r ∈ Examples.all, Argument r → r.judgment = .acceptable →
      ∀ c ∈ class? r, c ≠ .distributivePositive := by
  decide +kernel

/-- Under canonical composition a class 3 predicate takes no question: the paper marks every
such example, *hope whether* and its counterparts in the four other languages. -/
theorem anti_rogative_rows :
    ∀ r ∈ Examples.all, Argument r → class? r = some .distributivePositive →
      r.judgment ≠ .acceptable := by
  decide +kernel

/-- A negated positive preferential is infelicitous where the agent prefers no answer, and a
negated negative one is felicitous, so the negative predicates lack threshold significance.
The rows are (38) to (41), (44), (49), and (52). -/
theorem tsp_rows :
    ∀ r ∈ Examples.all, r.feature? "polarity" = some "negated" →
      ∀ v ∈ valence? r, (r.judgment = .acceptable ↔ v = .negative) := by
  decide +kernel

/-- Every declarative the paper judges false is under a class 1 predicate and sits beside a
constituent question of the same predicate judged true in the same context. This is the
non-distributivity diagnostic of (23) to (36). -/
theorem nondistributive_rows :
    ∀ r ∈ Examples.all, r.feature? "truth" = some "false" →
      r.feature? "clause" = some "declarative" →
        class? r = some .nonDistributive ∧ ∃ r' ∈ Examples.all, r'.context = r.context ∧
          r'.feature? "predicate" = r.feature? "predicate" ∧
          r'.feature? "clause" = some "constituent" ∧ r'.feature? "truth" = some "true" := by
  decide +kernel

/-- Turkish *diye* clauses combine with *um-* "hope", *kork-* "fear", and an intransitive verb
alike, in (71), (73), (75), and (76), as adjoined reports of wondering rather than arguments. -/
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
    ∀ r ∈ Examples.all, r.language = "nucl1301" →
      ∃ v ∈ (r.feature? "predicate").bind turkishVerb?, ∃ sfx ∈ turkishInflections,
        Turkish.Verb.template.Licensed (v.suffixes sfx) ∧
          ∃ t ∈ r.glossedTokens, Turkish.Phonology.ofSegmented? t.1 = some (v.inflect sfx) := by
  decide +kernel

/-- The verb of (73) is intransitive, so its *diye* clause is no argument. -/
theorem dolan_isIntransitive : Turkish.dolan.IsIntransitive := by decide

/-! ### Non-canonical composition (§4) -/

/-- Composed with the highlighted content of *whether p*, the singleton of the radical, a
degree-comparison predicate means its declarative (70). This first candidate analysis (§4.2)
yields the interpretive asymmetry but not the inquisitive implication. -/
theorem highlighted_eq_declarative (μ : E → W → Set W → ℝ) (θ : Set (Set W) → ℝ)
    (C : Set (Set W)) (x : E) (p : Set W) (w : W) :
    degreeComparison μ θ C x {p} w ↔ p ∈ preferred μ θ C x w :=
  degreeComparison_singleton μ θ C x p w

section Asymmetry

variable {V : Type*} {p Bp Bnp : V → Prop} {v₁ v₂ : V}

/-- The goals of a hopeful event whose agent hopes `φ` are `φ` or the agent's believing `φ`
(89). -/
def HopefulGoals (φ Bφ : V → Prop) (G : Set (V → Prop)) : Prop := ∀ g ∈ G, g = φ ∨ g = Bφ

/-- When the agent hopes for the radical, with the goal of believing `p`, the outcome in which
they come to believe `p` is strictly better than the one in which they do not, so the
wondering meets Tabatowski's convention on asking whether `p`. -/
theorem hopes_radical (h₁ : Bp v₁) (h₂ : ¬ Bp v₂) : v₁ <[{Bp}] v₂ := by
  simp only [Preorder.ofCriteria_lt_iff, Preorder.ofCriteria_le_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h ↦ (h₂ h).elim, fun h ↦ h₂ (h h₁)⟩

/-- When the agent hopes for the negation, whichever goal (89) allows, an outcome in which `p`
holds and the agent does not believe `¬p` satisfies neither `¬p` nor believing `¬p`, so coming
to believe `p` is no better than not, and the wondering cannot be hopeful. -/
theorem hopes_negation {G : Set (V → Prop)} (hG : HopefulGoals (fun v ↦ ¬ p v) Bnp G)
    (hp₁ : p v₁) (hn₁ : ¬ Bnp v₁) : ¬ v₁ <[G] v₂ := by
  rintro ⟨-, h⟩
  refine h fun g hg hg₁ ↦ ?_
  rcases hG g hg with rfl | rfl
  · exact absurd hp₁ hg₁
  · exact absurd hg₁ hn₁

/-- Fear constrains no goal (87). The purely epistemic goal of knowing whether `p` makes coming
to believe `p` strictly better than remaining undecided, whichever answer is feared. -/
theorem fears (h₁ : Bp v₁) (h₂ : ¬ Bp v₂) (hn₂ : ¬ Bnp v₂) :
    v₁ <[{fun v ↦ Bp v ∨ Bnp v}] v₂ := by
  simp only [Preorder.ofCriteria_lt_iff, Preorder.ofCriteria_le_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h ↦ (h.elim h₂ hn₂).elim, fun h ↦ (h (Or.inl h₁)).elim h₂ hn₂⟩

end Asymmetry

/-- In the polar cases a positive predicate or adverb holds exactly when the agent's attitude
targets the radical, and a negative one holds either way. The rows are (45), (50), (62), (63),
(75), (76), (78), and (79). -/
theorem asymmetry_rows :
    ∀ r ∈ Examples.all, ∀ t ∈ r.feature? "target", ∀ v ∈ valence? r,
      (v = .positive → (Holds r ↔ t = "radical")) ∧ (v = .negative → Holds r) := by
  decide +kernel

end QingEtAl2025
