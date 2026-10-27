module

public import Mathlib.Order.Basic
public import Mathlib.Order.Comparable
public import Linglib.Data.Examples.HofmeisterSag2010

/-!
# Hofmeister and Sag (2010): Cognitive Constraints and Island Effects

This file formalizes Hofmeister and Sag's processing account of island effects. The paper traces
island effects to four factors, namely the length of the filler–gap dependency, the referential
load of the material it spans, the clause boundaries it crosses, and the complexity of the
filler. Each factor is read off a `Stimulus`, the filler with the words between it and the gap,
and stimuli are compared by Pareto dominance over the four factors (`Stimulus.profile`).

Dominance predicts the paper's contrasts. Whatever the dependency, a which-N filler is easier
than a bare one (`which_easier`), the complex-NP island of Experiment 1 is harder than its
baseline even with the richer filler (`cnpc_harder_than_baseline`), and the which-N wh-island of
Experiment 2 is incomparable with its bare baseline (`whIsland_which_incomparable`), where the
experiment found no reading-time difference after the embedded verb.

## Implementation notes

* Each factor is ordinal. A word's referential load follows the accessibility scale of §3.2,
  with pronouns below indefinites below definites and names, a clause boundary's cost follows
  §3.3, with a declarative complement below an interrogative one, a filler's ease is its
  complexity, and the dependency's length counts the words it spans.
* Pareto dominance is the product order on `ℕ × ℕ × ℕ × ℕᵒᵈ`, with ease reversed because more
  ease makes processing easier. No rating or reading time enters a theorem, and the paper's
  acceptability and reading-time results stay in prose.
* The NP-type factor of Experiment 1 was weak and local in reading times and not significant in
  acceptability, so the profiles predict its direction (`cnpc_definite_harder`), not a size.

## References

* [P. Hofmeister and I. A. Sag, *Cognitive Constraints and Island Effects*
  (2010)][hofmeister-sag-2010]
* [E. Gibson, *Linguistic Complexity: Locality of Syntactic Dependencies* (1998)][gibson-1998]
* [R. L. Lewis and S. Vasishth, *An Activation-Based Model of Sentence Processing as Skilled
  Memory Retrieval* (2005)][lewis-vasishth-2005]
* [P. Deane, *Limits to attention: A cognitive theory of island phenomena* (1991)][deane-1991]
* [J. Sprouse, *A program for experimental syntax: Finding the relationship between
  acceptability and grammatical knowledge* (2007)][sprouse-2007]
-/

@[expose] public section

namespace HofmeisterSag2010

open OrderDual

attribute [local instance] decidableLTOfDecidableLE

/-! ### Stimuli and profiles -/

/-- The filler of a dependency is a bare wh-word or a which-N phrase. -/
inductive Filler where
  | bare
  | whichN
  deriving DecidableEq

/-- A word between the filler and the gap is, as far as the four factors see, a discourse
reference of some accessibility, a clause boundary of some kind, or other material. -/
inductive Word where
  | pronoun
  | indefinite
  | definite
  | name
  | that
  | whether
  | other
  deriving DecidableEq

/-- The referential load of a word follows §3.2, since a pronoun refers to an old referent, an
indefinite creates one, and a definite or a name searches for one. -/
def Word.load : Word → ℕ
  | .indefinite => 1
  | .definite => 2
  | .name => 2
  | _ => 0

/-- The cost of the clause boundary a word opens (§3.3) is higher for an interrogative
complement, whose alternatives must be considered as well, than for a declarative one. -/
def Word.boundary : Word → ℕ
  | .that => 1
  | .whether => 2
  | _ => 0

/-- The retrieval ease a filler affords (§3.4) is higher for the richer filler, which resists
interference and rules out early integration sites. -/
def Filler.ease : Filler → ℕ
  | .bare => 0
  | .whichN => 1

/-- A filler–gap dependency, as the factors describe it, consists of its filler and the words it
spans. -/
structure Stimulus where
  /-- The filler. -/
  filler : Filler
  /-- The words between the filler and the gap. -/
  span : List Word

/-- The profile of a stimulus records the length of the span, the boundaries it crosses, the
references it holds, and the ease its filler affords. Its product order, with ease reversed, is
Pareto dominance, so one stimulus is harder than another only when it is at least as hard on
every factor and strictly harder on one. -/
def Stimulus.profile (s : Stimulus) : ℕ × ℕ × ℕ × ℕᵒᵈ :=
  (s.span.length, (s.span.map Word.boundary).sum, (s.span.map Word.load).sum,
    toDual s.filler.ease)

theorem which_easier (span : List Word) :
    (Stimulus.mk .whichN span).profile < (Stimulus.mk .bare span).profile :=
  lt_of_le_of_ne (by simp [Stimulus.profile, Filler.ease]) (by simp [Stimulus.profile, Filler.ease])

/-! ### Experiment 1: the complex-NP island (48) -/

/-- The island-forming NP of (48) is definite, indefinite plural, or indefinite singular. -/
inductive IslandNP where
  | definite
  | plural
  | indefinite
  deriving DecidableEq

/-- `np.word` is the island-forming NP as a word of the span. -/
def IslandNP.word : IslandNP → Word
  | .definite => .definite
  | .plural => .indefinite
  | .indefinite => .indefinite

/-- `cnpc f np` is the complex-NP island of (48), *Emma doubted [the report] that we had
captured __*, with filler `f` and island NP `np`. -/
def cnpc (f : Filler) (np : IslandNP) : Stimulus :=
  ⟨f, [.name, .other, np.word, .that, .pronoun, .other, .other]⟩

/-- The baseline of (48) has the which-N filler, as in *Emma doubted that we had captured __*. -/
def cnpcBaseline : Stimulus := ⟨.whichN, [.name, .other, .that, .pronoun, .other, .other]⟩

-- §5.2
theorem cnpc_which_easier (np : IslandNP) : (cnpc .whichN np).profile < (cnpc .bare np).profile :=
  which_easier _

/-- Every island condition is harder than the baseline, the which-N ones too, since the island
adds a reference and a word to the span (§5.3). -/
theorem cnpc_harder_than_baseline (f : Filler) (np : IslandNP) :
    cnpcBaseline.profile < (cnpc f np).profile := by
  cases f <;> cases np <;> decide

/-- A definite island NP is harder than an indefinite one, the direction of the local reading-
time effects at the complementizer and the verb (§5.2). -/
theorem cnpc_definite_harder (f : Filler) :
    (cnpc f .indefinite).profile < (cnpc f .definite).profile := by
  cases f <;> decide

theorem cnpc_plural_eq_indefinite (f : Filler) :
    (cnpc f .plural).profile = (cnpc f .indefinite).profile := rfl

/-! ### Experiment 2: the wh-island (49) -/

/-- `whIsland f` is the wh-island of (49), *did Albert learn whether they dismissed __*, with
filler `f`. -/
def whIsland (f : Filler) : Stimulus := ⟨f, [.other, .name, .other, .whether, .pronoun, .other]⟩

/-- The baseline of (49) has the bare filler, as in *did Albert learn that they dismissed __*. -/
def whIslandBaseline : Stimulus := ⟨.bare, [.other, .name, .other, .that, .pronoun, .other]⟩

-- §6.2
theorem whIsland_which_easier : (whIsland .whichN).profile < (whIsland .bare).profile :=
  which_easier _

theorem whIsland_bare_harder_than_baseline :
    whIslandBaseline.profile < (whIsland .bare).profile := by decide

theorem whIsland_which_incomparable :
    IncompRel (· ≤ ·) (whIsland .whichN).profile whIslandBaseline.profile := by decide

end HofmeisterSag2010
