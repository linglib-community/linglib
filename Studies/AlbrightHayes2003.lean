module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Positivity
public import Linglib.Data.Examples.AlbrightHayes2003
public import Linglib.Fragments.English.Phonology
public import Linglib.Phonology.Segmental.NaturalClass

/-!
# Albright and Hayes (2003): Rules vs. analogy in English past tenses

[albright-hayes-2003] learn the English past tense as a set of stochastic rules. Every
stem–past pair is a word-specific rule, and minimal generalization over two rules with the same
change keeps the segments they share outward from the change site, reduces the first pair that
differ to the class of their shared features, and frees whatever lies beyond
([albright-hayes-2002] gives the full procedure). Each rule is scored by its reliability in the
lexicon, hits over scope, discounted for small scope by a lower confidence limit
([mikheev-1997]); the most reliable rules, the islands of reliability, exist for the regular
change as well as for irregular ones ([albright-2002] for Italian), and a candidate past takes
the score of its best rule. Two wug experiments ([berko-1958]) on 58 stems that the model chose
to cross islands for the regular and for an irregular past find island effects of the same size
for both, which the single default rule of the dual mechanism model ([pinker-prince-1988],
[prasada-pinker-1993]) cannot produce; the irregular effects replicate [bybee-moder-1983]. A
generalized context model ([nosofsky-1990], with [broe-1993]'s segment similarity) run on the
same lexicon misses the regular islands, follows single similar verbs, and misplaces the regular
allomorphs, because its similarity is variegated where a rule's is structured: the allomorph
depends on the final segment alone.

## Implementation notes

Minimal generalization is `mg` on the substrate's rewrite contexts, in which a leading word
boundary is the anchored word-specific rule and its absence the free variable. The paper's own
steps (6) and footnote 4, the island (8), and the regular allomorphy of (7b) are computed on
the English fragment's segments, whose meet is the featural term and whose natural classes
among the phonemes a stem can end in, `finals`, are what a featural term covers. Reliability is
`Stats`; the statistics reported in Tables 1 and 4 and the ratings and production probabilities
of Appendix A are rows. Vowel changes, which generalize on both sides of the change, the
confidence-limit discount, and the analogical model itself are not modelled.

## References

* [albright-hayes-2003]
* [albright-hayes-2002]
* [albright-2002]
* [berko-1958]
* [pinker-prince-1988]
* [prasada-pinker-1993]
* [bybee-moder-1983]
* [mikheev-1997]
* [nosofsky-1990]
* [broe-1993]
* [hayes-2009]
-/

@[expose] public section

namespace AlbrightHayes2003

open Phonology Subregular.LocalRewrite English English.Phonology

deriving instance DecidableEq for ContextElem

/-! ### Minimal generalization -/

/-- The structural description of a past-tense rule: the stem-final material before the change
site, read left to right, a leading word boundary anchoring it to a whole stem and its absence
standing for the free variable. -/
abbrev Context := List ContextElem

/-- The word-specific rule of a stem ((3)). -/
def wordSpecific (stem : List Segment) : Context := .wordBoundary :: stem.map .seg

/-- Generalization proceeds from the change site outward ((5)). Shared segments are kept, the
first pair that differ become the class of their shared features, and everything beyond them
is freed. -/
def mgRev : List ContextElem → List ContextElem → List ContextElem
  | .seg a :: as, .seg b :: bs => if a = b then .seg a :: mgRev as bs else [.seg (a ⊓ b)]
  | .wordBoundary :: _, .wordBoundary :: _ => [.wordBoundary]
  | _, _ => []

/-- The minimal generalization of two descriptions. -/
def mg (c₁ c₂ : Context) : Context := (mgRev c₁.reverse c₂.reverse).reverse

/-- The rule learned from a list of stems generalizes each stem's word-specific rule in
turn. -/
def learned : List (List Segment) → Context
  | [] => []
  | s :: ss => ss.foldl (fun c w ↦ mg c (wordSpecific w)) (wordSpecific s)

variable {c c₁ c₂ : Context} {stem : List Segment}

private theorem matchesRight_map_seg (l : List Segment) :
    MatchesRight (l.map .seg ++ [.wordBoundary]) l := by
  induction l with
  | nil => trivial
  | cons a l ih => simp [MatchesRight, ih]

theorem matchesLeft_wordSpecific : MatchesLeft (wordSpecific stem) stem := by
  simp only [wordSpecific, MatchesLeft, List.reverse_cons, ← List.map_reverse]
  exact matchesRight_map_seg _

theorem matchesLeft_single_iff (k x : Segment) : MatchesLeft [.seg k] [x] ↔ k ≤ x := by
  simp [MatchesLeft, MatchesRight]

private theorem mgRev_comm (r₁ r₂ : List ContextElem) : mgRev r₁ r₂ = mgRev r₂ r₁ := by
  induction r₁ generalizing r₂ with
  | nil => cases r₂ with
    | nil => rfl
    | cons b bs => cases b <;> rfl
  | cons a as ih => cases r₂ with
    | nil => cases a <;> rfl
    | cons b bs =>
      cases a <;> cases b <;> simp only [mgRev]
      split
      · subst_vars; simp [ih]
      · rename_i h; rw [ite_eq_right (Ne.symm h), inf_comm]

theorem mg_comm : mg c₁ c₂ = mg c₂ c₁ := by simp [mg, mgRev_comm]

private theorem matchesRight_mgRev {r₁ r₂ : List ContextElem} {l : List Segment}
    (h : MatchesRight r₁ l) : MatchesRight (mgRev r₁ r₂) l := by
  induction r₁ generalizing r₂ l with
  | nil => cases r₂ with
    | nil => trivial
    | cons b bs => cases b <;> trivial
  | cons a as ih => cases r₂ with
    | nil => cases a <;> trivial
    | cons b bs => cases a with
      | seg a => cases b with
        | seg b =>
          cases l with
          | nil => exact h.elim
          | cons s ss =>
            simp only [mgRev]
            split
            · exact ⟨h.1, ih h.2⟩
            · exact ⟨inf_le_left.trans h.1, trivial⟩
        | wordBoundary => trivial
      | wordBoundary => cases b with
        | seg _ => trivial
        | wordBoundary =>
          cases l with
          | nil => trivial
          | cons s ss => exact h.elim

theorem matchesLeft_mg_left (h : MatchesLeft c₁ stem) : MatchesLeft (mg c₁ c₂) stem := by
  simp only [MatchesLeft, mg, List.reverse_reverse] at h ⊢
  exact matchesRight_mgRev h

theorem matchesLeft_mg_right (h : MatchesLeft c₂ stem) : MatchesLeft (mg c₁ c₂) stem :=
  mg_comm ▸ matchesLeft_mg_left h

theorem matchesLeft_rtake_one (h : c.length ≤ 1) :
    MatchesLeft c stem ↔ MatchesLeft c (stem.rtake 1) :=
  (matchesLeft_rtake_of_le c h stem).symm

/-! ### Reliability -/

/-- The scope of a rule is the stems of a lexicon meeting its description. -/
def scopeOf {C : Type*} (c : Context) (lex : List (List Segment × C)) : List (List Segment × C) :=
  lex.filter fun x ↦ MatchesLeft c x.1

/-- A rule's performance in a lexicon is the forms meeting its description and, among them,
those whose past shows its change. -/
structure Stats where
  scope : ℕ
  hits : ℕ
  deriving DecidableEq

/-- The statistics of a change in a described context over a lexicon. -/
def Stats.ofLexicon {C : Type*} [DecidableEq C] (ch : C) (c : Context)
    (lex : List (List Segment × C)) : Stats :=
  ⟨(scopeOf c lex).length, ((scopeOf c lex).filter (·.2 = ch)).length⟩

section
variable {C : Type*} [DecidableEq C] (ch : C) (lex : List (List Segment × C))

theorem hits_le_scope : (Stats.ofLexicon ch c lex).hits ≤ (Stats.ofLexicon ch c lex).scope :=
  List.length_filter_le _ _

theorem scope_mono :
    (Stats.ofLexicon ch c₁ lex).scope ≤ (Stats.ofLexicon ch (mg c₁ c₂) lex).scope :=
  (List.monotone_filter_right lex fun _ h ↦
    decide_eq_true (matchesLeft_mg_left (of_decide_eq_true h))).length_le
end

/-- Raw confidence is hits over scope. -/
def Stats.rawConfidence (s : Stats) : ℚ := s.hits / s.scope

/-- `r` is less reliable than `s`, the ratios cross-multiplied. -/
def LessReliable (r s : Stats) : Prop := r.hits * s.scope < s.hits * r.scope

instance (r s : Stats) : Decidable (LessReliable r s) := inferInstanceAs (Decidable (_ < _))

theorem lessReliable_iff {r s : Stats} (hr : 0 < r.scope) (hs : 0 < s.scope) :
    LessReliable r s ↔ r.rawConfidence < s.rawConfidence := by
  simp only [LessReliable, Stats.rawConfidence]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- The general suffixation rule (7a) over the learning set. -/
def general : Stats := ⟨4253, 4034⟩

/-- An island of reliability is a rule the change works better in than the general rule
((8)). -/
def IsIsland (s : Stats) : Prop := LessReliable general s

instance (s : Stats) : Decidable (IsIsland s) := inferInstanceAs (Decidable (LessReliable _ _))

/-! ### The paper's steps on the English fragment -/

def vote : List Segment := [v, o, t]
def need : List Segment := [n, i, d]
def rub : List Segment := [turnedR, wedge, b]
def sag : List Segment := [s, æ, g]
def plan : List Segment := [p, l, æ, n]
def love : List Segment := [l, wedge, v]
def flow : List Segment := [f, l, o]
def jump : List Segment := [dezh, wedge, m, p]
def miss : List Segment := [m, smallCapitalI, s]
def wish : List Segment := [w, smallCapitalI, esh]
def laugh : List Segment := [l, æ, f]
def fill : List Segment := [f, smallCapitalI, l]
def pick : List Segment := [p, smallCapitalI, k]

/-- The phonemes the stem-final contexts of (6)–(8) range over: the English phonemes but /h/, which
never ends a word ([hayes-2009] p. 54). -/
def finals : Finset Segment := English.Phonology.inventory.erase h

theorem filter_matchesLeft_single (k : Segment) (I : Finset Segment) :
    I.filter (fun x ↦ MatchesLeft [.seg k] [x]) = k.naturalClass I := by
  simp only [matchesLeft_single_iff]; rfl

/-- From *vote* and *need* (6) the `-əd` rule learns what [t] and [d] share, a term whose natural
class is exactly [t, d]. -/
theorem learned_vote_need :
    learned [vote, need] = [.seg (t ⊓ d)] ∧
      (t ⊓ d).naturalClass finals = {t, d} := by
  decide

/-- The `-d` rule learned from *rub*, *sag* and *plan* covers [d], so it reaches *need* (footnote
4). -/
theorem learned_rub_sag_plan :
    learned [rub, sag, plan] = [.seg (b ⊓ g ⊓ n)] ∧
      d ∈ (b ⊓ g ⊓ n).naturalClass finals := by
  decide

/-- The voiced segments, as a description. -/
def voiced : Segment := Segment.ofSpecs [(.voice, true)]

/-- The voiceless segments, as a description. -/
def voiceless : Segment := Segment.ofSpecs [(.voice, false)]

/-- The `-d` rule learned from *rub*, *sag*, *plan*, *love* and *flow* covers every voiced segment
but /l/ (7b). -/
theorem learned_voiced :
    learned [rub, sag, plan, love, flow] = [.seg (b ⊓ g ⊓ n ⊓ v ⊓ o)] ∧
      (b ⊓ g ⊓ n ⊓ v ⊓ o).naturalClass finals =
        voiced.naturalClass finals \ {l} ∧
      (b ⊓ g ⊓ n ⊓ v ⊓ o ⊓ l).naturalClass finals =
        voiced.naturalClass finals := by
  decide

/-- The `-t` rule learned from *jump*, *miss* and *laugh* covers every voiceless segment but /k/
(7b). -/
theorem learned_voiceless :
    learned [jump, miss, laugh] = [.seg (p ⊓ s ⊓ f)] ∧
      (p ⊓ s ⊓ f).naturalClass finals =
        voiceless.naturalClass finals \ {k} ∧
      (p ⊓ s ⊓ f ⊓ k).naturalClass finals =
        voiceless.naturalClass finals := by
  decide

/-- The island (8) is `-t` after a voiceless fricative. -/
def voicelessFricative : Segment :=
  Segment.ofSpecs [(.sonorant, false), (.continuant, true), (.voice, false)]

/-- (8) is met by the four voiceless fricatives and nothing else. -/
theorem naturalClass_voicelessFricative :
    voicelessFricative.naturalClass finals = {f, θ, s, esh} := by
  decide

/-- The rule learned from *miss*, *wish* and *laugh* lies inside the island (8), and further
fricative-final forms widen it to the island. -/
theorem learned_le_voicelessFricative :
    learned [miss, wish, laugh] = [.seg (s ⊓ esh ⊓ f)] ∧ voicelessFricative ≤ s ⊓ esh ⊓ f := by
  decide

/-! ### Appendix A -/

/-- A cell of Table 3 records whether the stem occupies an island for the regular past and for some
irregular past. -/
structure IORCategory where
  iorForRegular : Bool
  iorForIrregular : Bool
  deriving DecidableEq

def IORCategory.ofString : String → Option IORCategory
  | "both" => some ⟨true, true⟩
  | "regOnly" => some ⟨true, false⟩
  | "irregOnly" => some ⟨false, true⟩
  | "neither" => some ⟨false, false⟩
  | _ => none

/-- A printed decimal is read as the integer of its digits, ratings in hundredths and
production probabilities in thousandths. -/
def digits (s : String) : ℕ :=
  s.toList.foldl (fun n c ↦ if c.isDigit then 10 * n + (c.toNat - '0'.toNat) else n) 0

/-- A row's numeric feature. -/
def value (key : String) (r : Datum) : ℕ := digits ((r.feature? key).getD "0")

/-- A row's reported rule statistics (Tables 1 and 4). -/
def statsOf (r : Datum) : Option Stats :=
  (r.nat? "ruleScope").bind fun s ↦ (r.nat? "ruleHits").map (⟨s, ·⟩)

/-- In Table 4 the twelve regular islands all outscore the general rule. -/
theorem table4_islands :
    ∀ r ∈ Examples.all, (r.feature? "island").isSome → ∀ s ∈ statsOf r, IsIsland s := by
  decide +kernel

/-- Table 1 ranks *gleed*'s pasts by raw confidence, *gleed* below *gled* below *gleeded*. -/
theorem gleed_ranking :
    ∀ s₁ ∈ statsOf Examples.a1_25_gleed, ∀ s₂ ∈ statsOf Examples.a1_25_gled,
      ∀ s₃ ∈ statsOf Examples.a1_25_gleeded, LessReliable s₁ s₂ ∧ LessReliable s₂ s₃ := by
  decide

/-- The Appendix A rows of one past type in the cells satisfying `p` (the Peripheral stems of
Table A2 have no cell). -/
def rows (regular : Bool) (p : IORCategory → Bool) : List Datum :=
  Examples.all.filter fun r ↦
    r.feature? "pastType" = some (if regular then "regular" else "irregular") ∧
      ((r.feature? "cell").bind IORCategory.ofString).any p

/-- The sum of a numeric feature over rows. -/
def total (key : String) (rs : List Datum) : ℕ := (rs.map (value key)).sum

/-- The mean of `key` over `A` exceeds its mean over `B`, cross-multiplied. -/
def MeanGT (key : String) (A B : List Datum) : Prop :=
  total key A * B.length > total key B * A.length

instance (key : String) (A B : List Datum) : Decidable (MeanGT key A B) :=
  inferInstanceAs (Decidable (_ > _))

/-- Novel regular pasts are rated higher and volunteered more often when the stem lies in an island
of reliability for the regular change (Fig. 2). -/
theorem regulars_ior :
    MeanGT "adjustedRating" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) ∧
      MeanGT "production" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) := by
  decide

theorem irregulars_ior :
    MeanGT "adjustedRating" (rows false (·.iorForIrregular)) (rows false (!·.iorForIrregular)) ∧
      MeanGT "production" (rows false (·.iorForIrregular)) (rows false (!·.iorForIrregular)) := by
  decide

theorem regulars_not_cell_invariant :
    total "adjustedRating" (rows true (· = ⟨true, false⟩)) *
        (rows true (· = ⟨false, true⟩)).length ≠
      total "adjustedRating" (rows true (· = ⟨false, true⟩)) *
        (rows true (· = ⟨true, false⟩)).length := by
  decide

theorem tradeoff :
    MeanGT "adjustedRating" (rows true (· = ⟨true, false⟩)) (rows true (· = ⟨true, true⟩)) ∧
      MeanGT "adjustedRating" (rows true (· = ⟨false, false⟩)) (rows true (· = ⟨false, true⟩)) ∧
      MeanGT "adjustedRating" (rows false (· = ⟨false, true⟩)) (rows false (· = ⟨true, true⟩)) ∧
      MeanGT "adjustedRating" (rows false (· = ⟨false, false⟩))
        (rows false (· = ⟨true, false⟩)) := by
  decide

theorem ruleBased_islands :
    MeanGT "ruleBased" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) := by decide

/-- On the twelve regular pasts in the best islands, the analogical model scores below both the
participants and the rule-based model (Table 4). -/
theorem analogical_misses_islands :
    ∀ r ∈ Examples.all, (r.feature? "island").isSome →
      value "analogical" r < value "adjustedRating" r ∧
        value "analogical" r < value "ruleBased" r := by
  decide +kernel

/-- The pseudo-*burnt* irregulars of (15). -/
def burnt : List Datum := Examples.all.filter (·.feature? "set" = some "burnt")

theorem burnt_underestimated :
    total "ruleBased" burnt < total "adjustedRating" burnt ∧
      total "adjustedRating" burnt < total "analogical" burnt := by
  decide

/-- Participants preferred regular pasts overall. -/
theorem regulars_preferred :
    MeanGT "rating" (Examples.all.filter fun r ↦ r.feature? "pastType" = some "regular")
      (Examples.all.filter fun r ↦ r.feature? "pastType" = some "irregular") := by
  decide

end AlbrightHayes2003
