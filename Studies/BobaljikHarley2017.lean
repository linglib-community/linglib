module

public import Studies.Harley2014
public import Linglib.Data.Examples.Harley2014
public import Linglib.Morphology.DistributedMorphology.PhrasalLocality

/-!
# Bobaljik and Harley (2017): Suppletion is local: Evidence from Hiaki

A trigger may condition the suppletion of a head only if no phrasal boundary separates them. In the
first formulation the boundary is a maximal projection, and in the refined one any projection
above the head level, so that a specifier is not local to its head either. Hiaki verbs supplete
for the number of an argument, of the object of a transitive verb and of the subject of an
intransitive one. Since an internal argument is base-generated as the sister of its Root, the
object is local to the Root, while an external argument, in the specifier of VoiceP, is separated
from it by the Root's own projection. The subjects that condition suppletion are therefore those
of unaccusative verbs, which the applicative *-ria*, impossible without an agentive verb,
confirms. The locality is structural rather than word-internal: within a complex head and with a
sister phrase alike, conditioning is local exactly where no phrase intervenes.

The refined condition also decides between the configurations in which the internal argument is
introduced. As the Root's sister it may condition the Root under both formulations. In the
specifier of the categorizer that takes the Root as its complement, as in Embick's resultative
participles, it may do so only under the first. Adjoined to a low functional projection above the
Root, as van Craenenbroeck suggests, it may do so under neither, since the lower segment of that
projection is already a maximal one.

## Main statements

* `localNumbers_clause`: of the arguments of a Hiaki clause only the internal one is local to the
  Root, so the context that locality gives the Root's Vocabulary Items is the one that
  `Harley2014.site` stipulates (`structuralSite_eq_site`).
* `mayCondition_mayCondition'_tree19`, `mayCondition'_tree20`: the refined condition renders
  specifiers non-local, and only the complement of a head may condition it.
* `frame_eq_unaccusative`: the applicative rows force the suppletive intransitives to be
  unaccusative.
* `mayCondition'_iff_configuration`: of the three configurations of an internal argument, the
  refined condition lets it condition the Root only as the Root's sister.

## Implementation notes

* The two formulations of locality are `DistributedMorphology.MayCondition` and
  `DistributedMorphology.MayCondition'`, on which the segments of a maximal category all count as
  maximal, as the chapter's remark on specifiers as adjuncts presupposes. A trigger's features
  are the number on the label of its DP, so a DP is represented by a terminal bearing its
  number.
* The applicative examples are those of `Data/Examples/Harley2014.json`, which the chapter repeats
  as its (15)–(18). The verb classes are taken from them, the suppletive intransitives excepted,
  whose class the rows determine.

## TODO

The typological survey of number-conditioned suppletion and the subject-conditioned transitive
suppletives of Seri and Hiw, which the chapter leaves to further investigation, are not
formalized.

## References

* [bobaljik-harley-2017]
* [harley-2014]
* [bobaljik-2012]
* [embick-2004]
* [van-craenenbroeck-2014]
-/

@[expose] public section

namespace BobaljikHarley2017

open PhraseStructure Core.Order
open DistributedMorphology (MayCondition MayCondition')
open Clause (Arguments)
open Clause.Arguments (unaccusative unergative transitive)

/-! ### The configurations of the chapter -/

/-- The categories are two abstract ones for the schematic trees, the Root's own, Voice, the
verbalizer, a low functional head, and determiner phrases. -/
inductive Cat
  | x | y | root | voice | v | f | d
  deriving DecidableEq, Repr

/-- The terminals are heads, phrases, Roots, DPs with their number, and the heads Voice, v and F. -/
inductive Word
  | head | phrase | root | dp (n : Number) | voice | v | f
  deriving DecidableEq, Repr

/-- Trees over the chapter's categories. -/
abbrev T := Tree Cat Word

/-- The schematic tree (19), a head with a specifier and a complement. -/
def tree19 : T :=
  .node .x [.terminal .d .phrase, .node .x [.terminal .x .head, .terminal .d .phrase]]

/-- Both arguments of a head are local to it under (1), only its complement under (1′) (19). -/
theorem mayCondition_mayCondition'_tree19 :
    MayCondition tree19 ⟨[1, 0]⟩ ⟨[0]⟩ ∧ MayCondition tree19 ⟨[1, 0]⟩ ⟨[1, 1]⟩ ∧
      ¬ MayCondition' tree19 ⟨[1, 0]⟩ ⟨[0]⟩ ∧ MayCondition' tree19 ⟨[1, 0]⟩ ⟨[1, 1]⟩ := by
  decide

/-- The schematic tree (20), a head with a specifier over a phrase whose head has a specifier and a
complement. -/
def tree20 : T :=
  .node .x [.terminal .d .phrase, .node .x [.terminal .x .head,
    .node .y [.terminal .d .phrase, .node .y [.terminal .y .head, .terminal .d .phrase]]]]

/-- Of the phrases of (20) only the complement of Y⁰ may condition it under (1′), and the higher
head X⁰ may not either. -/
theorem mayCondition'_tree20 :
    MayCondition' tree20 ⟨[1, 1, 1, 0]⟩ ⟨[1, 1, 1, 1]⟩ ∧
      ¬ MayCondition' tree20 ⟨[1, 1, 1, 0]⟩ ⟨[1, 1, 0]⟩ ∧
      ¬ MayCondition' tree20 ⟨[1, 1, 1, 0]⟩ ⟨[0]⟩ ∧
      ¬ MayCondition' tree20 ⟨[1, 1, 1, 0]⟩ ⟨[1, 0]⟩ := by
  decide

/-! ### Hiaki clauses -/

/-- The Root's projection, the internal argument base-generated as the Root's sister (13). -/
def rootP (c : Arguments Number) : T :=
  match c .internal with
  | some n => .node .root [.terminal .d (.dp n), .terminal .root .root]
  | none => .node .root [.terminal .root .root]

/-- The clause, VoiceP over the Root's projection, the external argument in its specifier (14). -/
def clause (c : Arguments Number) : T :=
  match c .external with
  | some n => .node .voice [.terminal .d (.dp n), .node .voice [rootP c, .terminal .voice .voice]]
  | none => .node .voice [rootP c, .terminal .voice .voice]

/-- The position of the Root in the clause. -/
def rootPos (c : Arguments Number) : TreePath :=
  ⟨(if (c .external).isSome then [1, 0] else [0]) ++ [if (c .internal).isSome then 1 else 0]⟩

/-- The numbers of the DPs that may condition the head at `α` under (1′). -/
def localNumbers (t : T) (α : TreePath) : List Number :=
  t.positionedTerminals.filterMap fun x ↦
    match x.2.2 with
    | .dp n => if MayCondition' t α x.1 then some n else none
    | _ => none

theorem localNumbers_clause (c : Arguments Number) :
    localNumbers (clause c) (rootPos c) = (c .internal).toList := by
  rcases hi : c .internal with _ | n <;> rcases he : c .external with _ | e <;>
    simp only [clause, rootP, rootPos, hi, he, Option.isSome_none, Option.isSome_some] <;>
    first
    | decide
    | (cases n <;> decide)
    | (cases e <;> decide)
    | (cases n <;> cases e <;> decide)

/-- The context that locality gives a Root's Vocabulary Items, its index and the numbers local to
it. -/
def structuralSite (c : Arguments Number) (r : DistributedMorphology.Root) :
    DistributedMorphology.Neighborhood (Finset Harley2014.SiteFeature) :=
  ⟨{.root r}, (localNumbers (clause c) (rootPos c)).map fun n ↦ {.internal n}, []⟩

theorem structuralSite_eq_site (c : Arguments Number) (r : DistributedMorphology.Root) :
    structuralSite c r = Harley2014.site c r := by
  rw [structuralSite, localNumbers_clause, Harley2014.site]
  cases c .internal <;> rfl

theorem spellout_eq (c : Arguments Number) (r : DistributedMorphology.Root) :
    Harley2014.spellout c r =
      DistributedMorphology.subsetPrinciple Harley2014.vocabulary (structuralSite c r) := by
  rw [structuralSite_eq_site]; rfl

/-- Head movement of the Root to Voice adjoins the Root to Voice, leaving a trace. -/
def moveToVoice (c : Arguments Number) : T :=
  match c .external with
  | some n => .node .voice [.terminal .d (.dp n),
      .node .voice [.node .root [.trace 0 .root],
        .adjoin .voice [.terminal .root .root, .terminal .voice .voice]]]
  | none => .node .voice [.node .root [.trace 0 .root],
      .adjoin .voice [.terminal .root .root, .terminal .voice .voice]]

/-- Moved to Voice, the Root is separated from the external argument by no maximal projection, so
(1) would let an external argument condition it; (1′) does not, since Voice′ is phrasal. -/
theorem mayCondition_moveToVoice (e : Number) :
    MayCondition (moveToVoice (unergative e)) ⟨[1, 1, 0]⟩ ⟨[0]⟩ ∧
      ¬ MayCondition' (moveToVoice (unergative e)) ⟨[1, 1, 0]⟩ ⟨[0]⟩ := by
  cases e <;> decide

/-! ### The applicative diagnostic -/

/-- The classes of the applicative examples. -/
inductive VerbClass
  | unergative | transitive | unaccusative | suppletiveIntransitive | suppletiveTransitive
  deriving DecidableEq, Repr

/-- The applicative *-ria* needs an agentive verb, a clause with an external argument. -/
def ApplicativeLicensed (c : Arguments Number) : Prop := (c .external).isSome

instance (c : Arguments Number) : Decidable (ApplicativeLicensed c) :=
  inferInstanceAs (Decidable (_ = true))

/-- The argument frame of each class, given the frame of the suppletive intransitives. -/
def VerbClass.frame (s : Arguments Number) : VerbClass → Arguments Number
  | .unergative => Clause.Arguments.unergative .singular
  | .transitive | .suppletiveTransitive => Clause.Arguments.transitive .singular .singular
  | .unaccusative => Clause.Arguments.unaccusative .singular
  | .suppletiveIntransitive => s

/-- The classes as named in the rows. -/
def classTable : List (String × VerbClass) :=
  [("unergative", .unergative), ("transitive", .transitive), ("unaccusative", .unaccusative),
    ("suppletiveIntransitive", .suppletiveIntransitive),
    ("suppletiveTransitive", .suppletiveTransitive)]

/-- The applicative examples with a suffixed *-ria*, by their verb class and judgment. -/
def applicativeRows : List (VerbClass × Judgment) :=
  Harley2014.Examples.all.filterMap fun d ↦ do
    guard (d.feature? "applicative" = some "suffixed")
    pure (← d.parse? "verbClass" classTable, d.judgment)

/-- A frame for the suppletive intransitives fits the rows when every suffixed applicative is
acceptable exactly where its frame is agentive. -/
def Fits (s : Arguments Number) : Prop :=
  ∀ p ∈ applicativeRows, p.2 = .acceptable ↔ ApplicativeLicensed (p.1.frame s)

instance (s : Arguments Number) : Decidable (Fits s) := List.decidableBAll _ _

theorem length_applicativeRows : applicativeRows.length = 5 := by decide +kernel

/-- Of the single-argument frames only the unaccusative one fits the applicative rows, so the
suppletive intransitives are unaccusative and their subjects internal arguments, local to the
Root (16). -/
theorem frame_eq_unaccusative (n : Number) :
    Fits (unaccusative n) ∧ ¬ Fits (unergative n) := by
  cases n <;> decide +kernel

/-! ### The configurations of an internal argument -/

/-- An internal argument is introduced as the Root's sister, in the specifier of the categorizer
that takes the Root as its complement, or adjoined to a low functional projection over the
Root. -/
inductive Configuration
  | sister | specifier | lowAdjunct
  deriving DecidableEq, Repr

/-- The tree of a configuration with the internal argument of number `n`, the Root at position
`[1, 1]` in the last two and `[1]` in the first. -/
def Configuration.tree (n : Number) : Configuration → T
  | .sister => .node .root [.terminal .d (.dp n), .terminal .root .root]
  | .specifier => .node .v [.terminal .d (.dp n), .node .v [.terminal .v .v, .terminal .root .root]]
  | .lowAdjunct =>
    .adjoin .f [.terminal .d (.dp n), .node .f [.terminal .f .f, .terminal .root .root]]

/-- The position of the Root in a configuration. -/
def Configuration.rootPos : Configuration → TreePath
  | .sister => ⟨[1]⟩
  | .specifier | .lowAdjunct => ⟨[1, 1]⟩

theorem mayCondition'_iff_configuration (n : Number) (k : Configuration) :
    MayCondition' (k.tree n) k.rootPos ⟨[0]⟩ ↔ k = .sister := by
  cases n <;> cases k <;> decide

/-- Under (1) the internal argument may condition the Root as its sister and as the specifier of
the categorizer, but not adjoined to a low projection, whose lower segment is maximal. -/
theorem mayCondition_iff_configuration (n : Number) (k : Configuration) :
    MayCondition (k.tree n) k.rootPos ⟨[0]⟩ ↔ k ≠ .lowAdjunct := by
  cases n <;> cases k <;> decide

end BobaljikHarley2017
