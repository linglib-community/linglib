module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Wordlist.Stojkovic2026
public import Linglib.Phonology.Hiatus
public import Linglib.Phonology.OptimalityTheory.Correspondence.Deletion
public import Linglib.Phonology.OptimalityTheory.Typology

/-!
# Stojković (2026): Same Form, Different Grammars: The Slavic [ov]~[u] Alternation

The Slavic verbalizer, the suffix of verbs derived from nouns and adjectives, is [u] before the
theme /-je-/ and a vowel with [v] before the theme /-a-/, and the languages fall into three groups
by that vowel: [ov] throughout, [ov] alternating with [ev] after a palatal, and [uv] throughout.
Stojković gives the suffix one underlying form in every language, a defective diphthong whose first
base node has no features and whose second is high and back but neither vowel nor consonant. Under
a ranking leaving well-formedness undominated, [the vowel's backness and height are each settled by
one comparison of two constraints](##language_eq), the [factorial typology](##language_hierarchy)
has the three groups and a fourth pattern, and [one group generates the forms of each
variety](##existsUnique_generates).

## Implementation notes

* A candidate is its string of segments with its correspondence to the input, and every constraint
  is computed from the two. MAX and DEP, stated in the paper over the morphemic and phonetic
  structures of Containment Theory, are the correspondence constraints that count input nodes
  without a correspondent and corresponding pairs whose output has a feature value its input lacks.
* A front vowel shares the [−back] of a palatal and so is a candidate only after one.
* \*CC and DEP[+high] are not in the paper's tableaux. Without \*CC [no ranking gives the
  alternation](##not_alternation) and without DEP[+high] [none gives a mid
  vowel](##fill_false_notMem_language); with \*CC undominated the rank of MAX decides nothing.
  \*CC is evaluated on the verbalizer's candidates alone, and Slavic allows clusters elsewhere.

## TODO

The data of (5), (13), (22) and (32) are not encoded. Contexts fix the two themes, where the paper's
claim is over any following vowel or consonant, which (13) would test.

## References

* [stojkovic-2026]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace Stojkovic2026

open Phonology OptimalityTheory CLDF.Wordlist

/-! ### Segments -/

/-- The first base node of the verbalizer, which has no features. -/
def node₀ : Segment := ⊥

/-- The second base node of the verbalizer, high and back but neither vowel nor consonant. -/
def glide₀ : Segment := Segment.ofSpecs [(.high, true), (.back, true)]

/-- The consonant [v], the second node as a consonant. -/
def v : Segment :=
  Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.high, true), (.back, true)]

/-- `vowel back high` is the vowel with the given backness and height, one of [o], [u], [e]
and [i]. -/
def vowel (back high : Bool) : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.consonantal, false), (.back, back), (.high, high)]

/-! ### Contexts and candidates -/

deriving instance Fintype for Wordlist.Root

/-- The theme after the verbalizer is /-a-/ or /-je-/. -/
inductive Theme where
  | a
  | je
  deriving DecidableEq, Fintype, Repr

/-- The stem-final consonant before the verbalizer, plain or palatal by the root: a plain
consonant has no backness, and a palatal is [−back]. -/
def Wordlist.Root.segment : Wordlist.Root → Segment
  | .plain => Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.high, false)]
  | .palatal =>
    Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.high, true), (.back, false)]

/-- The first segment of a theme, the vowel [a] or the glide [j]. -/
def Theme.segment : Theme → Segment
  | .a => Segment.ofSpecs [(.syllabic, true), (.consonantal, false), (.high, false), (.back, true)]
  | .je =>
    Segment.ofSpecs [(.syllabic, false), (.consonantal, false), (.high, true), (.back, false)]

/-- A context is the stem-final consonant before the verbalizer and the theme after it. -/
structure Context where
  stemFinal : Wordlist.Root
  theme : Theme
  deriving DecidableEq, Fintype, Repr

/-- A candidate realization of the verbalizer. -/
inductive Candidate where
  /-- The underlying form unchanged. -/
  | faithful
  /-- The empty node deleted and the second node the vowel [u]. -/
  | u
  /-- The empty node deleted and the second node the consonant [v]. -/
  | v
  /-- The empty node filled with a backness and a height and the second node [v]. -/
  | fill (back high : Bool)
  deriving DecidableEq, Fintype, Repr

variable (c : Context)

/-- The input is the stem-final consonant, the two nodes of the verbalizer, and the theme. -/
def input : List Segment := [c.stemFinal.segment, node₀, glide₀, c.theme.segment]

/-- `output c k` is the string of segments of the candidate `k`. -/
def output : Candidate → List Segment
  | .faithful => input c
  | .u => [c.stemFinal.segment, vowel true true, c.theme.segment]
  | .v => [c.stemFinal.segment, v, c.theme.segment]
  | .fill back high => [c.stemFinal.segment, vowel back high, v, c.theme.segment]

/-- `corr c k` is the correspondence of the candidate `k` to the input, a deletion of the empty
node for [u] and [v] and position by position for the others. -/
def corr : Candidate → Correspondence.Diagram BinaryRole Segment
  | .u => .deletion (input c) (output c .u) (Fin.succAbove 1)
  | .v => .deletion (input c) (output c .v) (Fin.succAbove 1)
  | k => .parallel (input c) (output c k)

/-- The candidates of a context. A front vowel is a candidate only after a palatal. -/
def candidates : Finset Candidate :=
  {.faithful, .u, .v, .fill true false, .fill true true} ∪
    if c.stemFinal = .palatal then {.fill false false, .fill false true} else ∅

/-! ### Constraints -/

/-- `dep c f val k` counts the corresponding pairs whose output has the value `val` of the feature
`f` and whose input lacks it, the epenthesis of that value. -/
def dep (f : Feature) (val : Bool) (k : Candidate) : ℕ :=
  (corr c k).depViolFeature (·.HasValue f val) .lhs .rhs

/-- The constraints of the analysis, the paper's with \*CC and DEP[+high]. -/
inductive Con where
  /-- NOHIATUS counts the adjacent vowels of the output. -/
  | noHiatus
  /-- \*CC counts the adjacent nonsyllabic segments of the output. -/
  | noCluster
  /-- SPECIFY counts the output nodes that have no features. -/
  | specify
  /-- \*SHARE[−back] counts the adjacent output segments that are both [−back] and whose first is
  a segment of the input, a palatal sharing its frontness with the vowel after it. -/
  | noShare
  /-- DEP[+back]. -/
  | depBack
  /-- DEP[−high]. -/
  | depNonhigh
  /-- DEP[+high]. -/
  | depHigh
  /-- MAX counts the input nodes that have no correspondent in the output. -/
  | maxNode
  deriving DecidableEq, Fintype, Repr

/-- The candidates of each context under the constraints. -/
def system : ConstraintSystem Context Candidate Con where
  gen := candidates
  con
    | .noHiatus => fun (c, k) ↦ Hiatus.count (output c k)
    | .noCluster => fun (c, k) ↦ Constraint.forbidPairs
        (fun a b ↦ a.HasValue .syllabic false ∧ b.HasValue .syllabic false) (output c k)
    | .specify => fun (c, k) ↦ (output c k).count node₀
    | .noShare => fun (c, k) ↦ Constraint.forbidPairs
        (fun a b ↦ a.HasValue .back false ∧ b.HasValue .back false ∧ a ∈ input c) (output c k)
    | .depBack => fun (c, k) ↦ dep c .back true k
    | .depNonhigh => fun (c, k) ↦ dep c .high false k
    | .depHigh => fun (c, k) ↦ dep c .high true k
    | .maxNode => fun (c, k) ↦ (corr c k).maxViol .lhs .rhs

/-- The constraints on the well-formedness of a string, against hiatus, clusters and empty nodes. -/
def wellFormedness : Finset Con := {.noHiatus, .noCluster, .specify}

-- [u] is the one well-formed candidate before /-je-/, where a following [v] forms a cluster.
theorem wellFormed_je_iff (s : Wordlist.Root) (k : Candidate) (hk : k ∈ candidates ⟨s, .je⟩) :
    (∀ i ∈ wellFormedness, system.con i (⟨s, .je⟩, k) = 0) ↔ k = .u := by
  revert s k; decide

-- The filled candidates are the well-formed ones before /-a-/, where [u] forms a hiatus.
theorem wellFormed_a_iff (s : Wordlist.Root) (k : Candidate) (hk : k ∈ candidates ⟨s, .a⟩) :
    (∀ i ∈ wellFormedness, system.con i (⟨s, .a⟩, k) = 0) ↔ ∃ b h, k = .fill b h := by
  revert s k; decide

/-! ### The winner under a ranking -/

/-- The constraint a filled node violates by its backness, DEP[+back] or \*SHARE[−back]. -/
def ofBack (b : Bool) : Con := cond b .depBack .noShare

/-- The constraint a filled node violates by its height, DEP[+high] or DEP[−high]. -/
def ofHigh (h : Bool) : Con := cond h .depHigh .depNonhigh

variable {n : ℕ}

/-- `form r c` is the winner under the ranking `r` in the context `c`. -/
def form (r : Ranking Con n) : Context → Candidate
  | ⟨_, .je⟩ => .u
  | ⟨s, .a⟩ =>
    .fill (s = .plain ∨ r.Dominates .noShare .depBack) (r.Dominates .depNonhigh .depHigh)

variable {r : Ranking Con n}

private theorem mem_candidates_fill (s : Wordlist.Root) (t : Theme) (b h : Bool) :
    Candidate.fill b h ∈ candidates ⟨s, t⟩ ↔ s = .palatal ∨ b = true := by
  revert s t b h; decide

private theorem dominates_not_decide {x y : Con} (hxy : x ≠ y) {f : Bool → Con}
    (hf : f false = x) (ht : f true = y) :
    r.Dominates (f !decide (r.Dominates x y)) (f (decide (r.Dominates x y))) := by
  by_cases h : r.Dominates x y
  · simp [h, hf, ht]
  · simpa [h, hf, ht] using ((trichotomous_of r.Dominates x y).resolve_left h).resolve_left hxy

private theorem con_fill_high (c : Context) (b h : Bool) :
    system.con (ofHigh !h) (c, .fill b h) < system.con (ofHigh !h) (c, .fill b !h) ∧
      ∀ j, system.con j (c, .fill b !h) < system.con j (c, .fill b h) → j = ofHigh h := by
  obtain ⟨_ | _, _ | _⟩ := c <;> revert b h <;> decide

private theorem con_fill_back (t : Theme) (b h : Bool) :
    system.con (ofBack !b) (⟨.palatal, t⟩, .fill b h) <
        system.con (ofBack !b) (⟨.palatal, t⟩, .fill (!b) h) ∧
      ∀ j, system.con j (⟨.palatal, t⟩, .fill (!b) h) < system.con j (⟨.palatal, t⟩, .fill b h) →
        j = ofBack b := by
  cases t <;> revert b h <;> decide

private theorem profile_lt {c : Context} {k k' : Candidate} {x y : Con}
    (hx : system.con x (c, k) < system.con x (c, k'))
    (hy : ∀ j, system.con j (c, k') < system.con j (c, k) → j = y) (hd : r.Dominates x y) :
    (system.tableau r c).profile k < (system.tableau r c).profile k' :=
  Tableau.ofRanking_profile_lt_iff_exists_dominates.2 ⟨x, hx, fun j hj ↦ hy j hj ▸ hd⟩

/-- Under a ranking that leaves well-formedness undominated, the winner is [u] before /-je-/, and
before /-a-/ a vowel with [v] that is high iff DEP[−high] dominates DEP[+high] and, after a palatal,
back iff \*SHARE[−back] dominates DEP[+back]. -/
theorem language_eq (hr : ∀ i ∈ wellFormedness, ∀ j ∉ wellFormedness, r.Dominates i j)
    (c : Context) : system.language r c = {form r c} := by
  have hlt {k k' : Candidate} (hk : ∀ i ∈ wellFormedness, system.con i (c, k) = 0)
      (hk' : ¬∀ i ∈ wellFormedness, system.con i (c, k') = 0) :
      (system.tableau r c).profile k < (system.tableau r c).profile k' := by
    push Not at hk'
    obtain ⟨i, hi, hi'⟩ := hk'
    exact Tableau.ofRanking_profile_lt_of_forall_dominates (U := ↑wellFormedness) hr hk hi hi'
  obtain ⟨s, _ | _⟩ := c
  · set H := decide (r.Dominates .depNonhigh .depHigh)
    set B := decide (s = .plain ∨ r.Dominates .noShare .depBack) with hB
    have hm : Candidate.fill B H ∈ candidates ⟨s, .a⟩ :=
      (mem_candidates_fill ..).2 (by cases s <;> simp [hB])
    have hhigh (b : Bool) : (system.tableau r ⟨s, .a⟩).profile (.fill b H) <
        (system.tableau r ⟨s, .a⟩).profile (.fill b !H) :=
      profile_lt (con_fill_high _ b H).1 (con_fill_high _ b H).2
        (dominates_not_decide (by decide) rfl rfl)
    refine Tableau.optimal_eq_singleton_iff.2 ⟨hm, fun k hk hne ↦ ?_⟩
    by_cases hk0 : ∀ i ∈ wellFormedness, system.con i (⟨s, .a⟩, k) = 0
    · obtain ⟨b, h, rfl⟩ := (wellFormed_a_iff s k hk).1 hk0
      have hback (hb : Candidate.fill (!B) h ∈ candidates ⟨s, .a⟩) (h' : Bool) :
          (system.tableau r ⟨s, .a⟩).profile (.fill B h') <
            (system.tableau r ⟨s, .a⟩).profile (.fill (!B) h') := by
        obtain rfl | rfl := s
        · simpa [hB] using (mem_candidates_fill ..).1 hb
        · refine profile_lt (con_fill_back _ B h').1 (con_fill_back _ B h').2 ?_
          simpa [hB] using dominates_not_decide (r := r) (x := .noShare) (y := .depBack)
            (by decide) (f := ofBack) rfl rfl
      obtain rfl | rfl := Bool.eq_or_eq_not b B <;> obtain rfl | rfl := Bool.eq_or_eq_not h H
      · exact absurd rfl hne
      · exact hhigh _
      · exact hback hk _
      · exact (hback ((mem_candidates_fill ..).2 ((mem_candidates_fill ..).1 hk)) H).trans (hhigh _)
    · exact hlt ((wellFormed_a_iff s _ hm).2 ⟨B, H, rfl⟩) hk0
  · have hm : Candidate.u ∈ candidates ⟨s, .je⟩ := by cases s <;> decide
    exact Tableau.optimal_eq_singleton_iff.2 ⟨hm, fun k hk hne ↦ hlt
      ((wellFormed_je_iff s _ hm).2 rfl) (mt (wellFormed_je_iff s k hk).1 hne)⟩

-- The two comparisons of `language_eq` are all that a ranking's language depends on.
theorem typology_iff {r' : Ranking Con n}
    (hr : ∀ i ∈ wellFormedness, ∀ j ∉ wellFormedness, r.Dominates i j)
    (hr' : ∀ i ∈ wellFormedness, ∀ j ∉ wellFormedness, r'.Dominates i j) :
    system.typology r r' ↔ (r.Dominates .noShare .depBack ↔ r'.Dominates .noShare .depBack) ∧
      (r.Dominates .depNonhigh .depHigh ↔ r'.Dominates .depNonhigh .depHigh) := by
  rw [ConstraintSystem.typology_iff, funext_iff]
  simp only [language_eq hr, language_eq hr', Finset.singleton_inj]
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ⟨s, t⟩ ↦ ?_⟩
  · simpa [form] using h ⟨.palatal, .a⟩
  · cases t <;> simp [form, h₁, h₂]

/-! ### The hierarchies of the paper -/

/-- The hierarchy `x ≫ y ≫ z` of the constraints on sharing and epenthesis below well-formedness and
above MAX, with DEP[+high] immediately below its top. -/
def hierarchy (x y z : Con) : List Con :=
  [.noHiatus, .noCluster, .specify, x, .depHigh, y, z, .maxNode]

/-- The six hierarchies of (31) give the patterns it lists, in order, the first being also the word
stratum grammar (23): [ov] twice, [ov]/[ev] twice, [uv], and [uv]/[iv]. -/
theorem language_hierarchy :
    (∀ s, system.language (.ofList (hierarchy .noShare .depBack .depNonhigh)) ⟨s, .a⟩ =
      {.fill true false}) ∧
    (∀ s, system.language (.ofList (hierarchy .noShare .depNonhigh .depBack)) ⟨s, .a⟩ =
      {.fill true false}) ∧
    (∀ s, system.language (.ofList (hierarchy .depBack .noShare .depNonhigh)) ⟨s, .a⟩ =
      {.fill (s = .plain) false}) ∧
    (∀ s, system.language (.ofList (hierarchy .depBack .depNonhigh .noShare)) ⟨s, .a⟩ =
      {.fill (s = .plain) false}) ∧
    (∀ s, system.language (.ofList (hierarchy .depNonhigh .noShare .depBack)) ⟨s, .a⟩ =
      {.fill true true}) ∧
    (∀ s, system.language (.ofList (hierarchy .depNonhigh .depBack .noShare)) ⟨s, .a⟩ =
      {.fill (s = .plain) true}) := by
  decide

/-- The three groups of languages. -/
inductive Group where
  | ov
  | ovEv
  | uv
  deriving DecidableEq, Fintype, Repr

/-- The hierarchies (17), (21) and (29) of the three groups. -/
def Group.ranking : Group → Ranking Con 8
  | .ov => .ofList (hierarchy .noShare .depNonhigh .depBack)
  | .ovEv => .ofList (hierarchy .depBack .depNonhigh .noShare)
  | .uv => .ofList (hierarchy .depNonhigh .noShare .depBack)

theorem language_ranking (g : Group) (c : Context) :
    system.language g.ranking c = {form g.ranking c} :=
  language_eq (by cases g <;> decide) c

/-! ### The paper's constraints -/

/-- The paper's constraints, those of the analysis without \*CC and DEP[+high]. -/
abbrev PaperCon := {i : Con // i ≠ .noCluster ∧ i ≠ .depHigh}

/-- The candidates of each context under the constraints `e i` alone. -/
def restrict {ι : Type*} (e : ι → Con) : ConstraintSystem Context Candidate ι :=
  ⟨candidates, fun i ↦ system.con (e i)⟩

/-- The candidates of each context under the paper's constraints alone. -/
abbrev paperSystem : ConstraintSystem Context Candidate PaperCon := restrict Subtype.val

private theorem con_high_lt_con_mid (c : Context) (b : Bool) :
    (∀ i, paperSystem.conAt c i (.fill b true) ≤ paperSystem.conAt c i (.fill b false)) ∧
      ∃ i, paperSystem.conAt c i (.fill b true) < paperSystem.conAt c i (.fill b false) := by
  obtain ⟨_ | _, _ | _⟩ := c <;> revert b <;> decide

/-- No ranking of the paper's constraints gives a mid vowel, since a high vowel with the same
backness violates each of them at most as often and DEP[−high] less often. So (31a)–(31d) do not
follow from them. -/
theorem fill_false_notMem_language (r : Ranking PaperCon n) (c : Context) (b : Bool) :
    Candidate.fill b false ∉ paperSystem.language r c := fun h ↦ by
  have hm := Tableau.optimal_subset h
  have hc : Candidate.fill b true ∈ candidates c := by
    obtain ⟨s, t⟩ := c
    exact (mem_candidates_fill ..).2 ((mem_candidates_fill ..).1 hm)
  exact Tableau.ofRanking_notMem_optimal_of_lt hc (Pi.lt_def.2 (con_high_lt_con_mid c b)) h

-- (11): with MAX last, [v] wins before /-a-/ and ties with [u] before /-je-/.
theorem language_of_max_last {r : Ranking PaperCon (n + 1)} (hr : (r (Fin.last n)).1 = .maxNode)
    (s : Wordlist.Root) :
    paperSystem.language r ⟨s, .a⟩ = {.v} ∧ paperSystem.language r ⟨s, .je⟩ = {.u, .v} := by
  have hm : r (Fin.last n) = ⟨.maxNode, by decide⟩ := Subtype.ext hr
  constructor <;>
  · refine (Tableau.ofRanking_optimal_eq_argmin_filter ⟨.v, by cases s <;> decide, ?_⟩).trans ?_ <;>
      rw [hm] <;> cases s <;> decide

private theorem con_a_eq_con_je (s : Wordlist.Root) (i : Con) (hi : i ≠ .noCluster) :
    system.con i (⟨s, .a⟩, .v) = system.con i (⟨s, .je⟩, .u) ∧
      ∀ b h, system.con i (⟨s, .a⟩, .fill b h) = system.con i (⟨s, .je⟩, .fill b h) := by
  revert s i; decide

/-- No ranking of constraints without \*CC gives [u] before /-je-/ and a vowel with [v] before
/-a-/, since [v] before /-a-/ violates them as [u] does before /-je-/, and a filled candidate
violates them alike in both contexts. -/
theorem not_alternation {ι : Type*} {e : ι → Con} (he : ∀ i, e i ≠ .noCluster) (r : Ranking ι n)
    (s : Wordlist.Root) (b h : Bool) :
    ¬((restrict e).language r ⟨s, .a⟩ = {.fill b h} ∧ (restrict e).language r ⟨s, .je⟩ = {.u}) := by
  rintro ⟨ha, hj⟩
  obtain ⟨hm, ha⟩ := Tableau.optimal_eq_singleton_iff.1 ha
  obtain ⟨-, hj⟩ := Tableau.optimal_eq_singleton_iff.1 hj
  have hv : Candidate.v ∈ candidates ⟨s, .a⟩ := by cases s <;> decide
  have hlt := ha .v hv nofun
  have hlt' := hj (.fill b h) ((mem_candidates_fill ..).2 ((mem_candidates_fill ..).1 hm)) nofun
  have e₁ : ((restrict e).tableau r ⟨s, .a⟩).profile .v =
      ((restrict e).tableau r ⟨s, .je⟩).profile .u :=
    congrArg toLex (funext fun p ↦ (con_a_eq_con_je s _ (he (r p))).1)
  have e₂ : ((restrict e).tableau r ⟨s, .a⟩).profile (.fill b h) =
      ((restrict e).tableau r ⟨s, .je⟩).profile (.fill b h) :=
    congrArg toLex (funext fun p ↦ (con_a_eq_con_je s _ (he (r p))).2 b h)
  rw [e₁, e₂] at hlt
  exact lt_asymm hlt hlt'

-- (12): [ov] is not harmonically bounded by [u], which violates MAX where [ov] does not.
theorem u_not_bounds_ov (s : Wordlist.Root) :
    ¬(paperSystem.conAt ⟨s, .je⟩ · .u) < (paperSystem.conAt ⟨s, .je⟩ · (.fill true false)) :=
  fun h ↦ absurd (h.le ⟨.maxNode, by decide⟩) (by cases s <;> decide)

/-! ### The forms of Tables 1 and 2 -/

/-- The letter that writes a vowel of the verbalizer or its [v]. -/
def letter? (s : Segment) : Option Char :=
  [(vowel true false, 'o'), (vowel false false, 'e'), (vowel true true, 'u'),
    (vowel false true, 'i'), (v, 'v')].lookup s

/-- `spelling c k` writes the segments of the verbalizer in the candidate `k`. -/
def spelling (k : Candidate) : String :=
  String.ofList (((output c k).drop 1).dropLast.filterMap letter?)

/-- `context? a` is the context of the verbalizer in the form `a` analyses. The theme is the morph
after the verbalizer. -/
def context? (a : Wordlist.Analysis) : Option Context := do
  let t ← match (← a.form.morphs[2]?).toList.head? with
    | some 'a' => some Theme.a
    | some 'j' => some .je
    | _ => none
  pure ⟨a.root, t⟩

/-- The verbalizer of a form, as the paper takes it to be written. -/
def verbalizer? (a : Wordlist.Analysis) : Option String :=
  a.verbalizer <|> a.form.morphs[1]?

/-- A group generates a form when the form is written with the winner of the group's hierarchy for
its context (`language_ranking`). -/
def Generates (g : Group) (a : Wordlist.Analysis) : Prop :=
  ∃ c ∈ context? a, verbalizer? a = some (spelling c (form g.ranking c))

instance (g : Group) (a : Wordlist.Analysis) : Decidable (Generates g a) :=
  inferInstanceAs (Decidable (∃ c ∈ context? a, _))

/-- The varieties of the two tables. -/
def varieties : List String := (Wordlist.lexemes.map (·.variety)).dedup

/-- The analysed forms of a variety. -/
def formsOf (variety : String) : List Wordlist.Analysis :=
  Wordlist.analyses.filter (·.form.lexeme.variety = variety)

/-- For every variety exactly one group generates all of its forms, the infinitive-stem forms
after a plain and after a palatal root and the present forms alike. The Bulgarian and
Macedonian present in [uv] needs no separate statement, since its theme is /-a-/. -/
theorem existsUnique_generates :
    ∀ variety ∈ varieties, ∃ g : Group,
      (∀ a ∈ formsOf variety, Generates g a) ∧
      ∀ g' : Group, (∀ a ∈ formsOf variety, Generates g' a) → g' = g := by
  decide +kernel

-- The tables list nineteen varieties, where the text speaks of seventeen systems (p. 4).
example : varieties.length = 19 := by decide +kernel

end Stojkovic2026
