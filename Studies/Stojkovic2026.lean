module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Wordlist.Stojkovic2026
public import Linglib.Phonology.Hiatus
public import Linglib.Phonology.OptimalityTheory.Correspondence.Deletion
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Stojković (2026): Same Form, Different Grammars: The Slavic [ov]~[u] Alternation

This file formalizes Stojković's account of the Slavic verbalizer, the suffix of verbs derived
from nouns and adjectives. The suffix is [u] before the theme /-je-/ and a vowel followed by
[v] before the theme /-a-/, where the languages fall into three groups: [ov] throughout, [ov]
alternating with [ev] after a palatal, and [uv] throughout.

Stojković gives the suffix one underlying form in every language, a defective diphthong whose
first base node has no features and whose second is high and back but neither vowel nor
consonant. A candidate leaves that form as it is, deletes the empty node and makes the second a
vowel, or fills the empty node and makes the second [v]. A candidate here is its string of
segments with its correspondence to the input, and every constraint is computed from the two.
One ranking per group then gives [u] before /-je-/ and the group's vowel before /-a-/
(`optimal_eq`), and for every variety of the paper's Tables 1 and 2 exactly one of the three
rankings generates all of its forms (`existsUnique_generates`), the Bulgarian and Macedonian
present in [uv] included, since its theme is /-a-/.

## Main results

* `optimal_eq`: the winner of each group's ranking in each context.
* `image_pattern`: the factorial typology of the variable constraints, the paper's (31).
* `existsUnique_generates`: each variety's forms single out its group.
* `uv_bounds_ov`: over the paper's own constraints [uv] harmonically bounds [ov].

## Implementation notes

The paper states MAX and DEP over the morphemic and phonetic structures of Containment Theory.
They are rendered as the correspondence constraints that count input nodes without a
correspondent and corresponding pairs whose output has a feature value its input lacks. The
candidates are the paper's; a deleted node with [v], which it sets aside, is not among them. A
front vowel shares the [−back] of a palatal and so is a candidate only after one.

## TODO

The paper's tableaux never penalize the epenthesis of [+high], so that over its constraints
[uv] does at least as well as [ov] everywhere and better on DEP[−high] (`uv_bounds_ov`), and
its typology (31) cannot be derived from them (`image_pattern_of_paperFamilies`). The paper
attributes the [o] of the first two groups to the markedness of [+high]; that preference is
made a constraint here, DEP[+high], ranked where each group needs it. The paper's tableau (28)
also marks [iv] for DEP[+back], which its representation of [iv] with a shared [−back] does not
support and which changes no outcome.

## References

* [stojkovic-2026]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace Stojkovic2026

open Phonology OptimalityTheory Data.Wordlist

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
  /-- The empty node deleted and the second node a vowel, [u]. -/
  | delete
  /-- The empty node filled with a backness and a height and the second node [v]. -/
  | fill (back high : Bool)
  deriving DecidableEq, Fintype, Repr

variable (c : Context)

/-- The input is the stem-final consonant, the two nodes of the verbalizer, and the theme. -/
def input : List Segment := [c.stemFinal.segment, node₀, glide₀, c.theme.segment]

/-- `output c k` is the string of segments of the candidate `k`. -/
def output : Candidate → List Segment
  | .faithful => input c
  | .delete => [c.stemFinal.segment, vowel true true, c.theme.segment]
  | .fill back high => [c.stemFinal.segment, vowel back high, v, c.theme.segment]

/-- `corr c k` is the correspondence of the candidate `k` to the input, a deletion of the empty
node for `delete` and position by position for the others. -/
def corr : Candidate → Correspondence BinaryRole Segment
  | .delete => .deletion (input c) (output c .delete) (Fin.succAbove 1)
  | k => .parallel (input c) (output c k)

/-- The candidates of a context. A front vowel is a candidate only after a palatal. -/
def candidates : Finset Candidate :=
  {.faithful, .delete, .fill true false, .fill true true} ∪
    if c.stemFinal = .palatal then {.fill false false, .fill false true} else ∅

/-! ### Constraints -/

/-- NOHIATUS counts the adjacent vowels of the output. -/
def noHiatus : Constraint Candidate := fun k ↦ Hiatus.count (output c k)

/-- SPECIFY counts the output nodes that have no features. -/
def specify : Constraint Candidate := fun k ↦ (output c k).count node₀

/-- MAX counts the input nodes that have no correspondent in the output. -/
def maxNode : Constraint Candidate := fun k ↦ (corr c k).maxViol .lhs .rhs

/-- `dep f val` counts the corresponding pairs whose output has the value `val` of the feature
`f` and whose input lacks it, the epenthesis of that value. -/
def dep (f : Feature) (val : Bool) : Constraint Candidate := fun k ↦
  (corr c k).depViolFeature (·.HasValue f val) .lhs .rhs

/-- \*SHARE[−back] counts the adjacent output segments that are both [−back] and whose first
is a segment of the input, a palatal sharing its frontness with the vowel after it. -/
def noShare : Constraint Candidate := fun k ↦
  ((output c k).zip (output c k).tail).countP fun p ↦
    decide (p.1.HasValue .back false ∧ p.2.HasValue .back false ∧ p.1 ∈ input c)

/-- DEP[+back]. -/
abbrev depBack : Constraint Candidate := dep c .back true

/-- DEP[−high]. -/
abbrev depNonhigh : Constraint Candidate := dep c .high false

/-- DEP[+high]. -/
abbrev depHigh : Constraint Candidate := dep c .high true

/-- A ranking of constraints that vary across the groups, completed by the undominated NOHIATUS
and SPECIFY above them and MAX below. -/
def ranking (vs : List (Context → Constraint Candidate)) : List (Constraint Candidate) :=
  [noHiatus c, specify c] ++ vs.map (· c) ++ [maxNode c]

/-- `optimal c vs` is the set of winners in the context `c` under the ranking `vs`. -/
def optimal (vs : List (Context → Constraint Candidate)) : Finset Candidate :=
  (Tableau.ofList (candidates c) (ranking c vs)).optimal

/-! ### The three groups -/

/-- The three groups of languages. -/
inductive Group where
  | ov
  | ovEv
  | uv
  deriving DecidableEq, Fintype, Repr

/-- The rankings of the paper's (17), (21) and (29), with DEP[+high] added. -/
def Group.ranking : Group → List (Context → Constraint Candidate)
  | .ov => [noShare, depHigh, depBack, depNonhigh]
  | .ovEv => [depBack, depHigh, noShare, depNonhigh]
  | .uv => [depNonhigh, noShare, depBack, depHigh]

/-- `g.form c` is the verbalizer of the group `g` in the context `c`. It is [u] before /-je-/,
and before /-a-/ the group's vowel with [v], the vowel of the middle group being front after a
palatal. -/
def Group.form (g : Group) : Context → Candidate
  | ⟨_, .je⟩ => .delete
  | ⟨s, .a⟩ => .fill (g ≠ .ovEv ∨ s = .plain) (g = .uv)

/-- Each group's ranking gives its verbalizer in every context. -/
theorem optimal_eq (g : Group) (c : Context) : optimal c g.ranking = {g.form c} := by
  obtain ⟨_ | _, _ | _⟩ := c <;> cases g <;> decide

/-! ### The paper's constraints -/

/-- The paper's constraints, without DEP[+high]. -/
def paperConstraints : List (Constraint Candidate) :=
  [noHiatus c, specify c, noShare c, depBack c, depNonhigh c, maxNode c]

/-- Over the paper's constraints [uv] does at least as well as [ov] on every constraint and
better on DEP[−high], before /-a-/. -/
theorem uv_le_ov (s : Wordlist.Root) :
    (∀ con ∈ paperConstraints ⟨s, .a⟩, con (.fill true true) ≤ con (.fill true false)) ∧
      depNonhigh ⟨s, .a⟩ (.fill true true) < depNonhigh ⟨s, .a⟩ (.fill true false) := by
  revert s; decide

/-- No ranking of the paper's constraints gives [ov], since [uv] harmonically bounds it. -/
theorem uv_bounds_ov (s : Wordlist.Root) {rk : List (Constraint Candidate)}
    (hrk : rk.Perm (paperConstraints ⟨s, .a⟩)) :
    Candidate.fill true false ∉
      (Tableau.ofList (candidates ⟨s, .a⟩) rk).optimal := by
  obtain ⟨hle, hlt⟩ := uv_le_ov s
  obtain ⟨i, hi⟩ := List.mem_iff_get.1
    (hrk.mem_iff.2 (by simp [paperConstraints] : depNonhigh ⟨s, .a⟩ ∈ paperConstraints _))
  refine Tableau.ofRanking_notMem_optimal_of_lt (c := .fill true true) (by simp [candidates]) ?_
  exact Pi.lt_def.2 ⟨fun k ↦ hle _ (hrk.mem_iff.1 (rk.get_mem k)), i, by rw [hi]; exact hlt⟩

/-! ### Factorial typology -/

/-- `pattern vs` is the pair of winners before /-a-/ under the ranking `vs`, after a plain
consonant and after a palatal. -/
def pattern (vs : List (Context → Constraint Candidate)) : Finset Candidate × Finset Candidate :=
  (optimal ⟨.plain, .a⟩ vs, optimal ⟨.palatal, .a⟩ vs)

/-- The rankings of the four variable constraints derive exactly the four patterns of the
paper's (31): [ov] throughout, [ov] with [ev], [uv] throughout, and [uv] with [iv], which no
Slavic language is known to show. -/
theorem image_pattern :
    ([noShare, depBack, depNonhigh, depHigh].permutations'.map pattern).toFinset =
      {({.fill true false}, {.fill true false}), ({.fill true false}, {.fill false false}),
        ({.fill true true}, {.fill true true}), ({.fill true true}, {.fill false true})} := by
  decide

/-- The rankings of the paper's three variable constraints derive only the two patterns with
[uv]. -/
theorem image_pattern_of_paperFamilies :
    ([noShare, depBack, depNonhigh].permutations'.map pattern).toFinset =
      {({.fill true true}, {.fill true true}), ({.fill true true}, {.fill false true})} := by
  decide

/-! ### The forms of Tables 1 and 2 -/

/-- The letter that writes a vowel of the verbalizer or its [v]. -/
def letter? (s : Segment) : Option Char :=
  [(vowel true false, 'o'), (vowel false false, 'e'), (vowel true true, 'u'),
    (vowel false true, 'i'), (v, 'v')].lookup s

/-- `spelling c k` writes the segments of the verbalizer in the candidate `k`. -/
def spelling (k : Candidate) : String :=
  String.ofList (((output c k).drop 1).dropLast.filterMap letter?)

/-- `context? a` is the context of the verbalizer in the form `a` analyses. The root is plain or
palatal by the table the form comes from, and the theme is the morph after the verbalizer. -/
def context? (a : Wordlist.Analysis) : Option Context := do
  let t ← match (← a.form.morphs[2]?).toList.head? with
    | some 'a' => some Theme.a
    | some 'j' => some .je
    | _ => none
  pure ⟨a.root, t⟩

/-- The verbalizer a form is written with. Belarusian writes the reduced vowel of [ov] as
*a*, and the paper takes it to be /o/. -/
def verbalizer? (f : Form Wordlist.Cell) : Option String :=
  f.morphs[1]?.map fun s ↦ if f.lexeme.variety = "Belarusian" ∧ s = "av" then "ov" else s

/-- A group generates a form when the form is written with the group's verbalizer for its
context. -/
def Generates (g : Group) (a : Wordlist.Analysis) : Prop :=
  ∃ c ∈ context? a, verbalizer? a.form = some (spelling c (g.form c))

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

end Stojkovic2026
