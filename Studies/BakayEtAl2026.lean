/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.LinearAlgebra.Matrix.DotProduct
public import Linglib.Data.Examples.BakayEtAl2026
public import Linglib.Fragments.Turkish.Anaphors
public import Linglib.Syntax.Binding.Tree

/-!
# Bakay, Akkuş and Dillon (2026): hierarchical relations in antecedent retrieval

This file formalizes the structural claims behind three visual-world experiments on the Turkish
reciprocal *birbirleri*, which must be bound by a c-commanding antecedent in its own clause.
Bakay, Akkuş and Dillon ask whether c-command between the noun phrases of one clause guides
antecedent retrieval, and they deconfound it from clause-mateness, case, subjecthood and linear
order. The target, an embedded subject or an indirect object, and the distractor, a possessor
inside the subject or inside an adjunct noun phrase or the complement of a postposition, share
the reciprocal's clause and case. The four embedded structures are phrase-structure trees here,
and Principle A over their clause configuration makes the embedded subject and an indirect
object available and the matrix subject and every distractor unavailable (`available_iff`), as
the paper's coindexations record (`rows_available`).

The paper weighs two ways retrieval could use the relation. On the cue-based account of Lewis
and Vasishth the reciprocal cues features stored with each candidate, and c-command enters
through Kush's `local` feature, carried by the noun phrases attached to the spine of the current
clause or serving as its arguments. On every stimulus that feature holds of exactly the
available antecedents (`local_iff_available`), so the target out-activates each distractor under
any weighting that gives the hierarchical cue weight (`target_retrieved`); a distractor that
matches the reciprocal in number still out-activates one that does not whenever item-level cues
carry weight, the interference both weightings predict (`distractor_interference`). On the
representational account after McElree and Oberauer, the noun phrases that c-command the
retrieval site from within its clause sit in a privileged store. That store holds exactly the
available antecedents (`privileged_iff_available`), so no distractor is accessed
(`not_privileged_second`).

## Implementation notes

* The trees keep the noun phrases, the heads that embed them and the verbal spine, and omit
  adverbs. The embedded clause is the complement of the matrix verb, and an adjunct is a sister
  of the lowest verb phrase.
* Argumenthood in Kush's feature is read off attachment, so a noun phrase is local when its
  mother is a clause or verb-phrase node of the retrieval site's clause.
* A cue is matched either against the hierarchical feature or against an item-level feature,
  and activation is the count of matched cues weighted by where they are matched.

## References

* [Ö. Bakay, F. Akkuş and B. Dillon, *Hierarchical relations guide memory retrieval in sentence
  comprehension: Evidence from a local anaphor in Turkish* (2026)][bakay-etal-2026]
* [N. Chomsky, *Lectures on Government and Binding* (1981)][chomsky-1981]
* [T. Reinhart, *The Syntactic Domain of Anaphora* (1976)][reinhart-1976]
* [R. L. Lewis and S. Vasishth, *An Activation-Based Model of Sentence Processing as Skilled
  Memory Retrieval* (2005)][lewis-vasishth-2005]
* [D. W. Kush, *Respecting Relations: Memory Access and Antecedent Retrieval in Incremental
  Sentence Processing* (2013)][kush-2013]
* [B. McElree, *Accessing Recent Events* (2006)][mcelree-2006]
* [K. Oberauer, *Access to information in working memory: Exploring the focus of attention*
  (2002)][oberauer-2002]
-/

@[expose] public section

namespace BakayEtAl2026

open Core.Order PhraseStructure PhraseStructure.Tree Binding

/-! ### The stimuli -/

/-- The embedded-clause structures of the stimuli, by the clause's second noun phrase. It is a
possessor inside the subject in (5a), a possessor inside an adjunct noun phrase in (5b) and
(10c), the complement of a postposition in (8b) and (10b), and an indirect object in (8a), (8c)
and (10a). -/
inductive Structure
  | possessorInSubject
  | possessorInAdjunct
  | postpositionalAdjunct
  | indirectObject
  deriving DecidableEq, Fintype, Repr

/-- `np` is a one-word noun phrase. -/
def np : Tree Cat Unit := .terminal .N ()

/-- `possessive` is a noun phrase of a possessor and its head noun. -/
def possessive : Tree Cat Unit := .node .N [np, .terminal .N ()]

/-- `reciprocalVP` is the lowest verb phrase, of the reciprocal object and the embedded verb. -/
def reciprocalVP : Tree Cat Unit := .node .V [np, .terminal .V ()]

/-- The embedded clause of a structure. -/
def Structure.clause : Structure → Tree Cat Unit
  | .possessorInSubject => .node .S [possessive, reciprocalVP]
  | .possessorInAdjunct => .node .S [np, .node .V [possessive, reciprocalVP]]
  | .postpositionalAdjunct =>
      .node .S [np, .node .V [.node .P [np, .terminal .P ()], reciprocalVP]]
  | .indirectObject => .node .S [np, .node .V [np, reciprocalVP]]

/-- A stimulus is the matrix subject over the embedded clause and the matrix verb. -/
def Structure.tree (s : Structure) : Tree Cat Unit :=
  .node .S [np, .node .V [s.clause, .terminal .V ()]]

/-- The noun phrases of a stimulus are the matrix subject, the embedded subject, the embedded
clause's second noun phrase, a distractor or an indirect object, and the reciprocal. -/
inductive Role
  | matrixSubject
  | embeddedSubject
  | second
  | reciprocal
  deriving DecidableEq, Fintype, Repr

/-- The position of a noun phrase in a stimulus. -/
def Structure.path : Structure → Role → TreePath
  | _, .matrixSubject => ⟨[0]⟩
  | _, .embeddedSubject => ⟨[1, 0, 0]⟩
  | .possessorInSubject, .second => ⟨[1, 0, 0, 0]⟩
  | .possessorInSubject, .reciprocal => ⟨[1, 0, 1, 0]⟩
  | .indirectObject, .second => ⟨[1, 0, 1, 0]⟩
  | _, .second => ⟨[1, 0, 1, 0, 0]⟩
  | _, .reciprocal => ⟨[1, 0, 1, 1, 0]⟩

theorem path_mem_labeled : ∀ s r, Structure.path s r ∈ labeled (Structure.tree s) {.N} := by
  decide

theorem path_injective (s : Structure) : Function.Injective s.path := by
  revert s; decide

/-- The binding configuration on the noun phrases of a stimulus is its tree's clause
configuration read at their positions. -/
abbrev Structure.configuration (s : Structure) : Configuration Role :=
  s.tree.clauseConfiguration.comap s.path

/-- A noun phrase is an available antecedent when the reciprocal, coindexed with it alone, meets
Principle A. -/
def Role.Available (s : Structure) (r : Role) : Prop :=
  s.configuration.Condition (pair r .reciprocal) ∅ .reciprocal .reciprocal

instance (s : Structure) (r : Role) : Decidable (r.Available s) :=
  inferInstanceAs
    (Decidable (s.configuration.Condition (pair r .reciprocal) ∅ .reciprocal .reciprocal))

theorem available_iff (s : Structure) (r : Role) :
    r.Available s ↔ r = .embeddedSubject ∨ s = .indirectObject ∧ r = .second := by
  revert s r; decide

/-! ### Cue-based retrieval -/

/-- The noun phrase at `p` carries Kush's `local` feature at a retrieval site `q` when its mother
is a clause or verb-phrase node sharing the minimal clause of `q`, so that it hangs from the
spine of that clause. -/
def Local (t : Tree Cat Unit) (p q : TreePath) : Prop :=
  p.parent ∈ labeled t {.S, .V} ∧ (p.parent, q) ∈ mateRelation (labeled t {.S})

instance (t : Tree Cat Unit) (p q : TreePath) : Decidable (Local t p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem local_iff_available (s : Structure) (r : Role) (hr : r ≠ .reciprocal) :
    Local s.tree (s.path r) (s.path .reciprocal) ↔ r.Available s := by
  revert s r; decide

/-- A retrieval cue is matched against the hierarchical feature or against an item-level feature
stored with the candidate. -/
inductive CueSource
  | hierarchical
  | itemLevel
  deriving DecidableEq, Fintype, Repr

/-- A retrieval cue is a feature a candidate should carry, tagged with where it is matched. -/
structure Cue (F : Type*) where
  /-- Where the cue is matched. -/
  source : CueSource
  /-- The feature the cue seeks. -/
  feature : F

section Activation

variable {F : Type*} [DecidableEq F]

/-- `matchCount feats cues s` counts the cues matched at `s` that a candidate with the features
`feats` matches. -/
def matchCount (feats : List F) (cues : List (Cue F)) (s : CueSource) : ℕ :=
  cues.countP fun c ↦ decide (c.source = s ∧ c.feature ∈ feats)

/-- Activation is the count of matched cues, weighted by where they are matched. -/
def weightedActivation (w : CueSource → ℕ) (feats : List F) (cues : List (Cue F)) : ℕ :=
  ∑ s, w s * matchCount feats cues s

theorem matchCount_le {a b : List F} {cues : List (Cue F)}
    (h : ∀ c ∈ cues, c.feature ∈ b → c.feature ∈ a) (s : CueSource) :
    matchCount b cues s ≤ matchCount a cues s :=
  List.countP_mono_left fun c hc hb ↦ by
    simp only [decide_eq_true_eq] at hb ⊢
    exact ⟨hb.1, h c hc hb.2⟩

theorem weightedActivation_lt {w : CueSource → ℕ} {a b : List F} {cues : List (Cue F)}
    (hle : ∀ s, matchCount b cues s ≤ matchCount a cues s)
    (hlt : ∃ s, 0 < w s ∧ matchCount b cues s < matchCount a cues s) :
    weightedActivation w b cues < weightedActivation w a cues :=
  dotProduct_lt_dotProduct_of_nonneg_left hle (fun _ ↦ Nat.zero_le _) hlt

end Activation

/-- A noun phrase is stored with Kush's `local` feature, a clause-mate feature, its number and
its case. -/
inductive Feature
  | «local»
  | clauseMate
  | number (n : Number)
  | marking (c : Case)
  deriving DecidableEq, Repr

/-- The features of the noun phrase `r` of `s`, of number `n` and case `c`. It carries the
`local` feature when Kush's feature holds of it at the reciprocal, and the clause-mate feature
when it shares the reciprocal's minimal clause. -/
def Role.features (s : Structure) (r : Role) (n : Number) (c : Case) : List Feature :=
  (if Local s.tree (s.path r) (s.path .reciprocal) then [.«local»] else []) ++
    (if (s.path r, s.path .reciprocal) ∈ mateRelation (labeled s.tree {.S}) then [.clauseMate]
      else []) ++ [.number n, .marking c]

/-- *Birbirleri* cues the `local` feature, the clause-mate feature and the number of the
fragment's reciprocal, which its antecedent shares. -/
def birbirleriCues : List (Cue Feature) :=
  ⟨.hierarchical, .«local»⟩ :: ⟨.itemLevel, .clauseMate⟩ ::
    (Turkish.Anaphors.birbirlerini.number.map fun n ↦ ⟨.itemLevel, .number n⟩).toList

theorem birbirleriCues_eq :
    birbirleriCues =
      [⟨.hierarchical, .«local»⟩, ⟨.itemLevel, .clauseMate⟩, ⟨.itemLevel, .number .plural⟩] :=
  rfl

theorem features_embeddedSubject (s : Structure) (n : Number) (c : Case) :
    Role.features s .embeddedSubject n c = [.«local», .clauseMate, .number n, .marking c] := by
  cases s <;> rfl

theorem features_second {s : Structure} (hs : s ≠ .indirectObject) (n : Number) (c : Case) :
    Role.features s .second n c = [.clauseMate, .number n, .marking c] := by
  cases s <;> first | exact absurd rfl hs | rfl

theorem target_retrieved {s : Structure} (hs : s ≠ .indirectObject) {w : CueSource → ℕ}
    (hw : 0 < w .hierarchical) (n : Number) (cT cD : Case) :
    weightedActivation w (Role.features s .second n cD) birbirleriCues <
      weightedActivation w (Role.features s .embeddedSubject .plural cT) birbirleriCues := by
  rw [features_second hs, features_embeddedSubject]
  refine weightedActivation_lt (matchCount_le fun c hc _ ↦ ?_) ⟨.hierarchical, hw, ?_⟩
  · simp only [birbirleriCues_eq, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp
  · simp [matchCount, birbirleriCues_eq]

theorem distractor_interference {s : Structure} (hs : s ≠ .indirectObject) {w : CueSource → ℕ}
    (hw : 0 < w .itemLevel) (c : Case) :
    weightedActivation w (Role.features s .second .singular c) birbirleriCues <
      weightedActivation w (Role.features s .second .plural c) birbirleriCues := by
  rw [features_second hs, features_second hs]
  refine weightedActivation_lt (matchCount_le fun c hc hb ↦ ?_) ⟨.itemLevel, hw, ?_⟩
  · simp only [birbirleriCues_eq, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp_all
  · simp [matchCount, birbirleriCues_eq]

/-! ### The privileged representation -/

/-- A noun phrase is in the privileged store at the reciprocal when it c-commands the reciprocal
from within the reciprocal's clause. -/
def Privileged (s : Structure) (r : Role) : Prop :=
  r ∈ s.configuration.domain .reciprocal ∧ s.configuration.commands r .reciprocal

theorem privileged_iff_available {s : Structure} {r : Role} (hr : r ≠ .reciprocal) :
    Privileged s r ↔ r.Available s := by
  rw [Role.Available, Configuration.condition_anaphor (.inr rfl), Set.mem_empty_iff_false,
    false_or, Configuration.locallyBound_pair_iff hr]
  rfl

theorem not_privileged_second {s : Structure} (hs : s ≠ .indirectObject) :
    ¬ Privileged s .second := by
  rw [privileged_iff_available (by decide), available_iff]
  simp [hs]

/-! ### The paper's stimuli -/

/-- The structure a row records, by its distractor or its second noun phrase. -/
def structure? (x : Datum) : Option Structure :=
  x.parse? "distractor" [("possessor in subject", .possessorInSubject),
      ("possessor in adjunct", .possessorInAdjunct),
      ("postpositional adjunct", .postpositionalAdjunct)] <|>
    x.parse? "second" [("indirect object", .indirectObject)]

/-- The noun phrases the rows' readings name. -/
def roles : List (String × Role) :=
  [("matrix subject", .matrixSubject), ("embedded subject", .embeddedSubject),
    ("distractor", .second), ("indirect object", .second)]

theorem rows_parse :
    ∀ x ∈ Examples.all, (structure? x).isSome ∧ ∀ y ∈ x.readings, (roles.lookup y.1).isSome := by
  decide

theorem rows_available : ∀ x ∈ Examples.all, ∀ s ∈ structure? x, ∀ y ∈ x.readings,
    ∀ r ∈ roles.lookup y.1, (y.2 = .acceptable ↔ r.Available s) := by
  decide

end BakayEtAl2026
