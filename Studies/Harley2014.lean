/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.Allosemy
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Clause.Arguments
public import Linglib.Data.Examples.Harley2014
public import Linglib.Morphology.DistributedMorphology.RootCategorization
public import Studies.Bobaljik2008
public import Linglib.Data.Examples.Readers

/-!
# Harley (2014): On the identity of roots

This file formalizes Harley's argument that a root of List 1 is individuated neither by
its form nor by its meaning but by an index, on which the Vocabulary Items of List 2 and the
interpretations of List 3 are both keyed. Hiaki root suppletion (√322, *vuite* ~ *tenne* 'run')
shows that roots must already be distinct when their items compete, since an item conditioned
by number would otherwise block every less specified root, and that phonologically individuated
roots would turn suppletion into rewriting; the caboodle item *cahoot* shows an interpretation
bound to one frame with no Elsewhere, so a root is not a concept either. `spellout` realizes a
root at its insertion site, the index with the number of the internal argument below, by the
Subset Principle over the Hiaki vocabulary; `run_isProperlySuppletive` and `cahoot_interp_gap`
are the two flanks. Since [a root's form depends on its internal argument
alone](##dependsOn_spellout), [suppletion is conditioned ergatively](##isErgative_conditions), an
ergative–absolutive pattern in a nominative–accusative language that
[agreement does not follow](##suppletion_not_agreement), and [the suppletive intransitives are
unaccusative](##eq_internal_of_spellout_ne).

The syntactic evidence of §3.1 that roots take complements is formalized on the configurations of
`DistributedMorphology.RootCategorization`. With the argument the sister of the root and adjuncts
adjoined to nP, *one*, an nP anaphor, strands an adjunct and not the argument (`oneStrands_iff`),
and if a selection restriction relates an argument to the head it is merged with, the noun and
the verb of one root share their restriction on the object exactly when the root takes the
object as its complement (`selector_eq_iff`).

## Implementation notes

Footnote 16 settles the Elsewhere direction: the impersonal passive, whose argument is
syntactically absent, surfaces as *tenne*, so *tenne* is the Elsewhere form and *vuite* is
conditioned by a singular internal argument, as in the paper's (14); its (7) is a first pass with
the roles reversed. The paper indexes only √322 and √548, the other indices here are arbitrary
distinct ones, and the caboodle frame of (16) is recorded by its categorizing head. Example
numbers follow the revised manuscript (LingBuzz 001527); the paper's Hiaki examples are the rows
of `Data/Examples/Harley2014.json`.

## References

* [harley-2014]
* [bobaljik-2008]
-/

@[expose] public section

namespace Harley2014

open DistributedMorphology
open DistributedMorphology.Allosemy (toInterpreted embedding)
open Morphology
open Clause Clause.Arguments

/-! ### List 1: roots as indices -/

/-- √322, realized *vuite*~*tenne* 'run' ((3a), (14)). -/
def run : Root := ⟨322⟩

/-- The root realized *weye*~*kaate* 'walk' ((3f), (26)). -/
def walk : Root := ⟨401⟩

/-- The root realized *mea*~*sua* 'kill' ((3g), (27)). -/
def kill : Root := ⟨402⟩

/-- A non-suppletive intransitive root, *bwiika* 'sing', at whose index the
suppletive items must not compete (§2.1). -/
def sing : Root := ⟨500⟩

/-! ### The insertion site -/

/-- A root's Vocabulary Items may mention its index and the number of the
internal argument on the terminal below. -/
inductive SiteFeature where
  | root (r : Root)
  | internal (n : Number)
  deriving DecidableEq, Repr

/-- The neighborhood of root `r` in a clause bearing the numbers `c` has the
internal argument as the terminal below, and the external argument is not in
the local environment (§3.3). -/
def site (c : Arguments Number) (r : Root) : Neighborhood (Finset SiteFeature) :=
  ⟨{.root r}, ((c .internal).map fun n ↦ ({.internal n} : Finset SiteFeature)).toList, []⟩

/-! ### List 2: the suppletive Vocabulary Items -/

/-- A suppletive root has two items ((14), fn. 16), the form conditioned by a
singular internal argument below and the Elsewhere form. -/
def suppletive (r : Root) (sgForm elseForm : String) :
    RuleSet (VocabularyItem SiteFeature String) :=
  [⟨{(0, .root r), (-1, .internal .singular)}, sgForm⟩, {.root r} ⟷ elseForm]

/-- The Hiaki suppletive vocabulary of (3a), (3f), (3g). -/
def vocabulary : RuleSet (VocabularyItem SiteFeature String) :=
  suppletive run "vuite" "tenne" ++ suppletive walk "weye" "kaate" ++ suppletive kill "mea" "sua"

/-- Spell out root `r` in clause `c` by the Subset Principle over
`vocabulary`. -/
def spellout (c : Arguments Number) (r : Root) : Option String :=
  subsetPrinciple vocabulary (site c r)

-- (6a)
theorem run_sg : spellout (unaccusative .singular) run = some "vuite" := by decide

-- (6b)
theorem run_pl : spellout (unaccusative .plural) run = some "tenne" := by decide

-- fn. 16
theorem run_impersonal : spellout empty run = some "tenne" := by decide

-- (26)
theorem walk_sg_pl :
    spellout (unaccusative .singular) walk = some "weye" ∧
      spellout (unaccusative .plural) walk = some "kaate" := by
  decide

-- (27)
theorem kill_sgObj_plObj :
    spellout (transitive .singular .plural) kill = some "mea" ∧
      spellout (transitive .plural .singular) kill = some "sua" := by
  decide

/-! ### §2.1–2.2 Individuation is not phonological -/

-- §2.2
theorem run_two_forms :
    spellout (unaccusative .singular) run ≠ spellout (unaccusative .plural) run := by
  decide

-- §2.1
theorem index_local (c : Arguments Number) : spellout c sing = none := by
  unfold spellout site
  rcases h : c .internal with _ | n
  · rfl
  · cases n <;> rfl

/-! ### §3.3 Conditioning by the internal argument -/

-- §3.3
theorem dependsOn_spellout : DependsOn spellout {.internal} := fun _ _ h ↦
  funext fun _ ↦ by simp only [spellout, site, h .internal rfl]

/-- **The suppletive intransitives are unaccusative** (§3.3): an argument whose number conditions
the form of a root is internal. -/
theorem eq_internal_of_spellout_ne {c : Arguments Number} {p : ArgumentStructure.ArgPosition}
    {n n' : Number}
    (h : spellout (Function.update c p (some n)) ≠ spellout (Function.update c p (some n'))) :
    p = .internal :=
  mem_of_dependsOn dependsOn_spellout h

theorem conditions_S : Conditions spellout .S :=
  ⟨unaccusative .singular, .internal, by decide, .singular, .plural,
    fun h ↦ absurd (congrFun h run) (by decide)⟩

theorem conditions_P : Conditions spellout .P :=
  ⟨transitive .singular .singular, .internal, by decide, .singular, .plural,
    fun h ↦ absurd (congrFun h kill) (by decide)⟩

theorem not_conditions_A : ¬ Conditions spellout .A := by
  rintro ⟨c, p, hr, n, n', h⟩
  obtain rfl := eq_internal_of_spellout_ne h
  generalize c.valency = v at hr
  revert v; decide

/-- **Hiaki suppletion is conditioned ergatively** (§3.3): the number of the sole argument of an
intransitive and of the object of a transitive conditions it, that of a transitive subject does
not. -/
theorem isErgative_conditions : Alignment.IsErgative (Conditions spellout) :=
  ⟨propext (iff_of_true conditions_S conditions_P), fun h ↦ not_conditions_A (h ▸ conditions_S)⟩

-- (29)
theorem suppletion_not_agreement (t : Bobaljik2008.CaseCategory) :
    ¬ ∀ r, (Bobaljik2008.controls .accusative t r ↔ Conditions spellout r) := fun h ↦
  not_conditions_A <| (h .A).1 <|
    (Bobaljik2008.isAccusative_controls_accusative t).1 ▸ (h .S).2 conditions_S

/-! ### §2.3 Individuation is not semantic: the caboodle item -/

/-- √548 *cahoot* ((16)). -/
def cahoot : Root := ⟨548⟩

/-- The List-3 entry of √548: "a conspiracy" in the frame of (16), recorded by
its categorizing head, and no Elsewhere. -/
def cahootLF : RuleSet (VocabularyItem Allosemy.Feature String) :=
  [⟨(embedding {.cat .n}).toFinset, "a conspiracy"⟩]

theorem cahoot_no_elsewhere : winner? cahootLF ∅ = none := by decide

/-! ### Both flanks on the `Realization` carrier

Form varies across contexts (`IsProperlySuppletive`), meaning does not vary
but gaps (an empty `interp` fiber outside the frame, via
`Allosemy.toInterpreted`): `vocabulary` is the List-2 map, `cahootLF` the
List-3 map. -/

/-- List 2 is the `Realization` by Vocabulary Insertion, whose fiber at a root is its
Elsewhere-selected exponent, and `∅` at an index with no item. -/
def realization : Morphology.Realization Root (Arguments Number) String :=
  toRealization vocabulary fun r c ↦ site c r

/-- √322 realizes two nonempty, distinct fibers across two licensed clauses —
the *go*/*went* case the predicate names (§2.2). -/
theorem run_isProperlySuppletive : realization.IsProperlySuppletive run := by
  have hsg : realization.realize run (unaccusative .singular) = {"vuite"} := by
    show (spellout (unaccusative .singular) run).toFinset = _
    simp [run_sg]
  have hpl : realization.realize run (unaccusative .plural) = {"tenne"} := by
    show (spellout (unaccusative .plural) run).toFinset = _
    simp [run_pl]
  refine ⟨unaccusative .singular, unaccusative .plural,
    by simp [Morphology.Realization.IsLicensed, hsg],
    by simp [Morphology.Realization.IsLicensed, hpl], ?_⟩
  rw [hsg, hpl, ne_eq, Finset.singleton_inj]; decide

/-- √548 as a List-3 `Realization.Interpreted` view. -/
def cahootHead :
    Morphology.Realization.Interpreted Unit (Neighborhood (Finset Allosemy.Feature)) Unit String :=
  toInterpreted cahootLF

/-- The idiom's root is interpreted only inside its frame, so elsewhere it fails licensing rather
than showing allosemy (§2.3). -/
theorem cahoot_interp_gap :
    cahootHead.interp.realize () (embedding {.cat .n}) = {"a conspiracy"} ∧
      cahootHead.interp.realize () ∅ = ∅ := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### One-replacement and the selection of objects -/

section OneReplacement

open RootCategorization (Lexicon Attachment Configuration selector)
open Core.Order (TreePath)

/-- The root √STUD of *student*, nominalized by *-ent*, with the argument *chemistry*. -/
def student : Lexicon String := { x := .n, root := "stud", head := "ent", arg := "chemistry" }

/-- A configuration with an adjunct adjoined to its phrase, a PP of word `w` to a phrase of
category `x`. -/
def withAdjunct {W : Type*} (x : Minimalist.Cat) (w : W) (k : Configuration W) :
    Configuration W :=
  k.adjoin (.head x) [] [.terminal (.head .P) w]

/-- *student of chemistry with long hair*, the nP of (22) with the adjunct of (23) adjoined to
it. -/
def studentWithHair (a : Attachment) : Configuration String :=
  withAdjunct .n "with long hair" (a.configuration student)

/-- The dependents of a noun that *one* replaces. -/
inductive Dependent
  | argument | adjunct
  deriving DecidableEq, Repr

/-- The position of a dependent in a configuration with an adjunct adjoined to it. -/
def Dependent.pos {W : Type*} (k : Configuration W) : Dependent → TreePath
  | .argument => k.arg
  | .adjunct => ⟨[1]⟩

/-- *one*, an nP anaphor, strands the dependent from the root. -/
def OneStrands (a : Attachment) (d : Dependent) : Prop :=
  Strands (.head .n) (studentWithHair a).tree (studentWithHair a).root (d.pos (studentWithHair a))

instance (a : Attachment) (d : Dependent) : Decidable (OneStrands a d) :=
  inferInstanceAs (Decidable (Strands _ _ _ _))

/-- The dependents as named in the rows. -/
def dependentTable : List (String × Dependent) :=
  [("argument", .argument), ("adjunct", .adjunct)]

/-- The examples of (18), the dependent each strands with its judgment. -/
def oneData : List (Dependent × Judgment) :=
  Examples.all.filterMap fun d ↦ (d.parse? "stranded" dependentTable).map (·, d.judgment)

theorem oneData_length : oneData.length = 2 := by decide +kernel

-- (18)
theorem oneStrands_iff : ∀ p ∈ oneData, p.2 = .acceptable ↔ OneStrands .complement p.1 := by
  decide +kernel

/-- The verb *study* of (21a), with the object *physics*. -/
def study : Lexicon String := { x := .v, root := "stud", head := "y", arg := "physics" }

/-- The noun *student* of (21b), with the object *physics*. -/
def studentOfPhysics : Lexicon String :=
  { x := .n, root := "stud", head := "ent", arg := "physics" }

/-- The verb and the noun of (21) merge their object with the same head iff the root takes the
object as complement. -/
theorem selector_eq_iff (a : Attachment) :
    selector (a.configuration study).tree (a.configuration study).arg =
      selector (a.configuration studentOfPhysics).tree (a.configuration studentOfPhysics).arg ↔
        a = .complement := by
  cases a <;> decide

end OneReplacement

end Harley2014
