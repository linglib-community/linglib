module

public import Studies.Harley2014
public import Linglib.Morphology.DistributedMorphology.PhrasalLocality
public import Linglib.Data.Examples.BobaljikHarley2017
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Gloss

/-!
# Bobaljik and Harley (2017): Suppletion is local: Evidence from Hiaki

Bobaljik's locality condition lets a trigger condition the suppletion of a head only if no maximal
projection separates them. Hiaki verbs supplete for the number of a transitive's object and an
intransitive's subject, and the applicative *-ria*, which needs an agentive verb, shows that [the
suppletive intransitives have no external argument](##fits_iff), so the trigger is always [the
internal argument, the Root's sister](##localNumbers_clause). The refined condition, on which no
phrasal projection may intervene, makes [specifiers non-local](##mayCondition_tree19) and [closes
the loophole of head movement](##mayCondition_moveToVoice), but [admits a number that agreement
copies into the verb](##mayCondition'_tree21).

## Implementation notes

* The two formulations of locality are `DistributedMorphology.MayCondition` and
  `DistributedMorphology.MayCondition'`.
* A terminal is represented by the number it bears, so a DP by the number its determiner copies to
  its label.
* The verb of an applicative example is read off its gloss line, as the word glossed `APPL`, and
  its frame is the one the chapter gives it, in (15) or in the list (10) of suppletive verbs.

## TODO

The typological survey, the subject-conditioned transitive suppletives of Seri and Hiw, and the
evidence from Huichol, Kolyma Yukaghir and Georgian that suppletion follows underlying positions
where agreement follows derived ones are not formalized.

## References

* [bobaljik-harley-2017]
* [bobaljik-2012]
* [harley-2014]
-/

@[expose] public section

namespace BobaljikHarley2017

open PhraseStructure Core.Order
open DistributedMorphology (MayCondition MayCondition' localLabels mayCondition'_of_isHeadAt)
open Clause (Arguments)
open Clause.Arguments (unaccusative unergative transitive)

/-- The categories of the chapter's trees: the schematic X and Y, the Root's, Voice, the
non-agentive v, I and D. -/
inductive Cat
  | x | y | root | voice | v | i | d
  deriving DecidableEq, Repr

/-- Trees whose terminals are represented by the number they bear, if any. -/
abbrev T := Tree Cat (Option Number)

/-- A DP, represented by the number its determiner copies to its label ((11), (12)). -/
abbrev dp (n : Number) : T := .terminal .d (some n)

/-! ### The refined condition -/

/-- The tree (19), a head with a specifier and a complement. -/
def tree19 : T :=
  .node .x [.terminal .d none, .node .x [.terminal .x none, .terminal .d none]]

/-- **Specifiers are not local.** Both DPs of (19) may condition the head under the first
formulation, and only its complement under the refined one. -/
theorem mayCondition_tree19 :
    MayCondition tree19 ⟨[1, 0]⟩ ⟨[0]⟩ ∧ MayCondition tree19 ⟨[1, 0]⟩ ⟨[1, 1]⟩ ∧
      ¬ MayCondition' tree19 ⟨[1, 0]⟩ ⟨[0]⟩ ∧ MayCondition' tree19 ⟨[1, 0]⟩ ⟨[1, 1]⟩ := by
  decide

/-- The tree (19) with the specifier adjoined to the phrase, as in theories whose specifiers are
adjuncts. -/
def tree19Adjoined : T :=
  .adjoin .x [.terminal .d none, .node .x [.terminal .x none, .terminal .d none]]

-- fn. 7
theorem not_mayCondition_tree19Adjoined : ¬ MayCondition tree19Adjoined ⟨[1, 0]⟩ ⟨[0]⟩ := by
  decide

/-- The tree (20), a head with a specifier over a phrase whose head has a specifier and a
complement. -/
def tree20 : T :=
  .node .x [.terminal .d none, .node .x [.terminal .x none,
    .node .y [.terminal .d none, .node .y [.terminal .y none, .terminal .d none]]]]

-- (20)
theorem mayCondition'_tree20 :
    MayCondition' tree20 ⟨[1, 1, 1, 0]⟩ ⟨[1, 1, 1, 1]⟩ ∧
      ¬ MayCondition' tree20 ⟨[1, 1, 1, 0]⟩ ⟨[1, 1, 0]⟩ ∧
      ¬ MayCondition' tree20 ⟨[1, 1, 1, 0]⟩ ⟨[0]⟩ ∧
      ¬ MayCondition tree20 ⟨[1, 1, 1, 0]⟩ ⟨[1, 0]⟩ := by
  decide

/-! ### Hiaki clauses -/

/-- The Root's projection, the internal argument base-generated as the Root's sister (13). -/
def rootP (c : Arguments Number) : T :=
  match c .internal with
  | some n => .node .root [dp n, .terminal .root none]
  | none => .node .root [.terminal .root none]

/-- The verbal projection over the Root's: agentive Voice with the external argument in its
specifier (14), or the non-agentive v of a clause without one. -/
def clause (c : Arguments Number) : T :=
  match c .external with
  | some n => .node .voice [dp n, .node .voice [rootP c, .terminal .voice none]]
  | none => .node .v [rootP c, .terminal .v none]

/-- The position of the Root in the clause. -/
def rootPos (c : Arguments Number) : TreePath :=
  ⟨(if (c .external).isSome then [1, 0] else [0]) ++ [if (c .internal).isSome then 1 else 0]⟩

/-- The numbers that may condition the node at `α` under the refined formulation. -/
def localNumbers (t : T) (α : TreePath) : List Number := (localLabels t α).filterMap Prod.snd

/-- **Only the internal argument is local to the Root.** Whatever arguments a Hiaki clause has, the
numbers that may condition its Root are exactly that of its internal argument. -/
theorem localNumbers_clause (c : Arguments Number) :
    localNumbers (clause c) (rootPos c) = (c .internal).toList := by
  rcases hi : c .internal with _ | n <;> rcases he : c .external with _ | e <;>
    simp only [clause, rootP, rootPos, hi, he] <;> rfl

/-- The context locality gives a Root's Vocabulary Items, its index and the numbers local to it. -/
def structuralSite (c : Arguments Number) (r : DistributedMorphology.Root) :
    DistributedMorphology.Neighborhood (Finset Harley2014.SiteFeature) :=
  ⟨{.root r}, (localNumbers (clause c) (rootPos c)).map fun n ↦ {.internal n}, []⟩

-- Harley's insertion site is the context the refined condition delivers.
theorem structuralSite_eq_site (c : Arguments Number) (r : DistributedMorphology.Root) :
    structuralSite c r = Harley2014.site c r := by
  rw [structuralSite, localNumbers_clause, Harley2014.site]
  cases c .internal <;> rfl

/-- The unergative clause (14) after head movement of the Root to Voice, which leaves a trace. -/
def moveToVoice : T :=
  .node .voice [dp .plural, .node .voice [.node .root [.trace 0 .root],
    .adjoin .voice [.terminal .root none, .terminal .voice none]]]

/-- **The refined condition closes the loophole of head movement.** Moved to Voice, the Root is
local to the external argument under the first formulation and not under the refined one. -/
theorem mayCondition_moveToVoice :
    MayCondition moveToVoice ⟨[1, 1, 0]⟩ ⟨[0]⟩ ∧ ¬ MayCondition' moveToVoice ⟨[1, 1, 0]⟩ ⟨[0]⟩ := by
  decide

/-! ### The applicative diagnostic -/

/-- The applicative *-ria* selects agentive Voice, and clashes with the non-agentive v of a
clause without an external argument. -/
def ApplicativeLicensed (c : Arguments Number) : Prop := (clause c).cat = .voice

instance (c : Arguments Number) : Decidable (ApplicativeLicensed c) :=
  inferInstanceAs (Decidable (_ = _))

theorem applicativeLicensed_iff {c : Arguments Number} :
    ApplicativeLicensed c ↔ c .external ≠ none := by
  unfold ApplicativeLicensed clause
  cases c .external <;> simp

/-- The frames of the verbs of the applicative examples, by their glosses: those the chapter gives
the verbs of (15), agentive intransitive *dance*, agentive transitive *close* and unaccusative
*break*, and transitive for *kill*, whose suppletion (10) tracks its object. -/
def frames : List (List Char × Arguments Number) :=
  [("dance".toList, unergative .singular), ("close".toList, transitive .singular .singular),
    ("break".toList, unaccusative .singular), ("kill".toList, transitive .singular .singular)]

/-- The frame of a verb, given a frame `s` for *go*, whose suppletion (10) tracks its subject. -/
def frame? (s : Arguments Number) (g : List Char) : Option (Arguments Number) :=
  if g = "go".toList then some s else frames.lookup g

/-- The verb of an example, read from its gloss line as the first element of the lexical gloss of
the word that carries `APPL`, where one does. -/
def applicativeVerb? (d : Datum) : Option (List Char) := do
  let w ← d.glossedWords.find? fun w ↦ "APPL".toList ∈ w.labels
  (Gloss.elements (← w.lexicalGloss?)).head?

/-- The examples whose verb carries the applicative suffix, (15), (16) and (18), by their verb and
judgment. -/
def applicativeRows : List (List Char × Judgment) :=
  Examples.all.filterMap fun d ↦ (applicativeVerb? d).map (·, d.judgment)

/-- A frame for the suppletive intransitives fits the examples when the verb of each suffixed
applicative has a frame, which licenses the applicative exactly where it is acceptable. -/
def Fits (s : Arguments Number) : Prop :=
  ∀ p ∈ applicativeRows, ∃ c ∈ frame? s p.1, p.2 = .acceptable ↔ ApplicativeLicensed c

instance (s : Arguments Number) : Decidable (Fits s) := List.decidableBAll _ _

private theorem fits_congr {s s' : Arguments Number}
    (h : s .external = none ↔ s' .external = none) : Fits s ↔ Fits s' :=
  forall₂_congr fun p _ ↦ by
    by_cases hg : p.1 = "go".toList
    · simp [frame?, hg, applicativeLicensed_iff, h]
    · simp only [frame?, hg, ↓reduceIte]

/-- **The suppletive intransitives are unaccusative.** The applicative examples fit a frame for the
suppletive intransitives exactly when it has no external argument. -/
theorem fits_iff (s : Arguments Number) : Fits s ↔ s .external = none := by
  rcases h : s .external with _ | n
  · simpa using (fits_congr (s' := unaccusative .singular) (by simp [h, unaccusative])).mpr
      (by decide +kernel)
  · simpa using (fits_congr (s' := unergative .singular) (by simp [h, unergative])).not.mpr
      (by decide +kernel)

/-! ### Agreement -/

/-- The structure (21), in which agreement has copied the subject's plural onto Infl and V⁰, here
the Root, has moved into I⁰. -/
def tree21 : T :=
  .node .i [dp .plural, .node .i [.adjoin .i [.terminal .root none, .terminal .i (some .plural)],
    .node .v [.trace 0 .root]]]

/-- **Locality does not exclude agreement.** In (21) the number copied onto Infl may condition the
Root under the refined formulation, though the subject's own may not. -/
theorem mayCondition'_tree21 :
    MayCondition' tree21 ⟨[1, 0, 0]⟩ ⟨[1, 0, 1]⟩ ∧ ¬ MayCondition' tree21 ⟨[1, 0, 0]⟩ ⟨[0]⟩ :=
  ⟨mayCondition'_of_isHeadAt (h := ⟨[1, 0]⟩) (by decide) (by decide) (by decide), by decide⟩

end BobaljikHarley2017
