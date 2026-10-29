module

public import Studies.BrueningAlKhalaf2020
public import Linglib.Data.Examples.Bruening2025
public import Linglib.Data.Examples.BrueningAlKhalaf2020
public import Linglib.Data.Experiments.Bruening2025
public import Linglib.Syntax.Tree.Projection

/-!
# Bruening 2025: selectional violations in coordination

Bruening replies to Patejuk and Przepiórkowski's critique of Bruening and Al Khalaf. He grants
that coordinated arguments need not match in category, so the revised grammar keeps the 2020
selector's requirements, c-selection checked against every conjunct and S-features checked once
against the conjunct next to the selector, without the requirement that conjuncts share a
category (§§5.2–5.4). He maintains that the two selectional violations are real, limited and
linear, as three surveys bear out, and replaces the 2020 account of the adverbial one by negative
c-selectional features, which the next item merged checks off (§5.8). The examples are the rows of
`Data/Examples/Bruening2025` and the survey results are `Data/Experiments/Bruening2025`.

## Main definitions

* `Selected`, `Site`: what the features name and what a coordination merges with.
* `CFeature`, `Modifier`: a modifier's category and c-selectional feature.
* `MergesWith`: when a coordination of modifiers can merge with its site.

## Implementation notes

* S-features are present or absent. The superset requirement of §5.3 matters only for
  *strengthen* and *withdraw* (§5.6), which the paper excludes semantically (`semantic_rows`).
* The positive features of *-ly* adverbs are left open by the paper beyond excluding nouns; they
  are given verbs and adjectives here, and no theorem uses more than that they exclude nouns.
* Modifiers merge with a site, a position of a tree or a degree head, and whether the site is a
  maximal projection is read off its tree (`PhraseStructure.IsMaximalCategory`): the noun of (104)
  is projected further by its mother, while *so soon* adjoins to the maximal noun phrase *a visit*
  (p. 479). The features name maximal and nonmaximal projections (`Selected`); a modifier is a
  maximal phrase, since it is no head.
* Short displacement as a degree phrase ((105)) is not formalized.

## References

* [bruening-2025]
* [bruening-alkhalaf-2020]
* [patejuk-przepiorkowski-2023]
* [pollard-sag-1987]
-/

@[expose] public section

namespace Bruening2025

open BrueningAlKhalaf2020 (Conjunct Admits Satisfies Licensed checkedOnce phrases? selects? side?
  AdvHead NominalCoordination)
open Agreement (ConjunctAgreement)
open PhraseStructure (Cat IsMaximalCategory)
open PhraseStructure.Cat (N V Adj Adv)
open Core.Order (TreePath)

/-! ### Categorial selection -/

/-- Two complements of one category after *become*-type predicates differ in acceptability, so
predicates c-select ((17); §4.1, after [pollard-sag-1987]). -/
theorem selection_rows : ∃ e₁ ∈ Examples.all, ∃ e₂ ∈ Examples.all,
    e₁.feature? "construction" = some "selection" ∧ e₂.feature? "construction" = some "selection" ∧
      e₁.feature? "complement" = e₂.feature? "complement" ∧ e₁.judgment ≠ e₂.judgment := by
  decide

/-! ### Coordinated arguments -/

/-- A predicate with S-features rejects a clausal subject and one without admits it (§5.7). -/
theorem cp_subjects :
    ¬ Admits (Satisfies (checkedOnce .headFinal) {N}) [.C] ∧
      Admits (Satisfies (fun _ ↦ []) {N}) [.C] := by
  decide

/-! ### Adverbs -/

/-- The degree heads the analysis of adverbs refers to besides the categories of
`PhraseStructure.Cat` (§5.8) are a comparative and an equative. -/
inductive Degree where
  /-- A comparative, *taller*. -/
  | cmpr
  /-- An equative, *as tall as*. -/
  | eq
  deriving DecidableEq

/-- The paper's c-selectional features name the maximal and the nonmaximal projections of a
category, written `NP` and `N` (p. 479), and the degree heads. -/
inductive Selected where
  /-- `maximal c` is a maximal projection of `c`, `NP` for a noun. -/
  | maximal (c : Cat)
  /-- `nonmaximal c` is a nonmaximal projection of `c`, `N` for a noun. -/
  | nonmaximal (c : Cat)
  /-- `degree d` is a degree head. -/
  | degree (d : Degree)
  deriving DecidableEq

/-- What a coordination of modifiers merges with is a position in a tree or a degree head. -/
inductive Site where
  /-- `at t p` is the position `p` of the tree `t`. -/
  | at (t : PhraseStructure.Tree Cat String) (p : TreePath)
  /-- `degree d` is a degree head. -/
  | degree (d : Degree)
  deriving DecidableEq

/-- A site is of a selected kind by its category and by whether its category is maximal, which is
read off the tree. -/
def Selected.Matches : Selected → Site → Prop
  | .maximal c, .at t p => (t.subtreeAt p.toList).map PhraseStructure.Tree.cat = some c ∧
      IsMaximalCategory t.ProjectsAt t.AdjoinsAt p
  | .nonmaximal c, .at t p => (t.subtreeAt p.toList).map PhraseStructure.Tree.cat = some c ∧
      ¬ IsMaximalCategory t.ProjectsAt t.AdjoinsAt p
  | .degree d, .degree d' => d = d'
  | _, _ => False

instance : ∀ (x : Selected) (h : Site), Decidable (x.Matches h)
  | .maximal _, .at _ _ | .nonmaximal _, .at _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .degree _, .degree _ => inferInstanceAs (Decidable (_ = _))
  | .maximal _, .degree _ | .nonmaximal _, .degree _ | .degree _, .at _ _ => isFalse id

/-- A modifier's c-selectional feature (§5.8) either requires what it merges with to be of one of
some kinds or forbids it to be of any of them. -/
inductive CFeature where
  /-- A positive feature, `[C ∈ s]`. -/
  | sel (s : Finset Selected)
  /-- A negative feature, `[C ∉ s]`. -/
  | ban (s : Finset Selected)
  deriving DecidableEq

namespace CFeature

/-- A negative feature is checked off as soon as the next conjunct is merged, and fails if that
conjunct is of a kind it bans. A positive feature waits. -/
def ChecksNext : CFeature → Selected → Prop
  | sel _, _ => True
  | ban s, x => x ∉ s

/-- The negative feature of the conjunct nearest the site is checked against it, and fails if
the site is of a kind it bans. -/
def ChecksSite : CFeature → Site → Prop
  | sel _, _ => True
  | ban s, h => ∀ x ∈ s, ¬ x.Matches h

/-- A positive feature on the coordinator's stack is checked against the site the coordination
merges with, as is every feature on the stack ((75)). -/
def ChecksHost : CFeature → Site → Prop
  | sel s, h => ∃ x ∈ s, x.Matches h
  | ban _, _ => True

instance (f : CFeature) : DecidablePred f.ChecksNext := fun _ ↦ by
  cases f <;> unfold ChecksNext <;> infer_instance

instance (f : CFeature) : DecidablePred f.ChecksSite := fun _ ↦ by
  cases f <;> unfold ChecksSite <;> infer_instance

instance (f : CFeature) : DecidablePred f.ChecksHost := fun _ ↦ by
  cases f <;> unfold ChecksHost <;> infer_instance

end CFeature

/-- A modifier is a phrase of some category with a c-selectional feature. -/
structure Modifier where
  /-- `cat` is the modifier's category, a maximal one, since a modifier is no head. -/
  cat : Selected
  /-- The modifier's c-selectional feature. -/
  feature : CFeature
  deriving DecidableEq

namespace Modifier

/-- An adjective selects a nonmaximal noun (§4.1). -/
def adjective : Modifier := ⟨.maximal Adj, .sel {.nonmaximal N}⟩

/-- An underspecified adverb such as *once*, *twice* or *soon* may merge with anything but a
nonmaximal noun or a comparative (§5.8). -/
def adverb : Modifier := ⟨.maximal Adv, .ban {.nonmaximal N, .degree .cmpr}⟩

/-- An adverb in *-ly* selects what adverbs modify, verbs and adjectives, and not nouns (§4.1). -/
def lyAdverb : Modifier := ⟨.maximal Adv, .sel {.nonmaximal V, .nonmaximal Adj}⟩

/-- A measure phrase such as *three times* selects a comparative (p. 479). -/
def measure : Modifier := ⟨.maximal N, .sel {.degree .cmpr}⟩

/-- The modifier the 2020 analysis's adjective, silent-headed adverb or adverb in *-ly* is here. -/
def ofAdvHead : Option AdvHead → Modifier
  | none => adjective
  | some .silent => adverb
  | some .ly => lyAdverb

end Modifier

/-- A coordination of modifiers `ms` can merge with the site `h` when the negative feature of each
conjunct is checked off by the next conjunct and that of the last by `h`, the last conjunct's
features being on top of the coordinator's stack, and every positive feature on the stack is
satisfied by `h` ((100)–(104)). -/
def MergesWith (ms : List Modifier) (h : Site) : Prop :=
  ms.IsChain (fun x y ↦ x.feature.ChecksNext y.cat) ∧
    (∀ x ∈ HeadDirection.headFinal.nearest ms, x.feature.ChecksSite h) ∧
      ∀ x ∈ ms, x.feature.ChecksHost h

instance (ms : List Modifier) (h : Site) : Decidable (MergesWith ms h) := by
  unfold MergesWith; infer_instance

/-- In (104) the coordination *once and future* merges with *king*, which its mother projects
further, so the host is a nonmaximal noun. -/
def onceAndFutureKing : PhraseStructure.Tree Cat String :=
  .node N [.node .Conj [.terminal Adv "once", .terminal .Conj "and", .terminal Adj "future"],
    .node N [.terminal N "king"]]

/-- In *so soon a visit*, *so soon* adjoins to the maximal noun phrase *a visit* (p. 479). -/
def soSoonAVisit : PhraseStructure.Tree Cat String :=
  .adjoin N [.node Adv [.terminal Adv "so", .terminal Adv "soon"],
    .node N [.terminal .Det "a", .terminal N "visit"]]

/-- The site prenominal modifiers merge with is the nonmaximal noun of (104). -/
abbrev nounSite : Site := .at onceAndFutureKing ⟨[1]⟩

-- (97)
theorem adverb_mergesWith_iff {h : Site} :
    MergesWith [.adverb] h ↔
      ¬ (Selected.nonmaximal N).Matches h ∧ ¬ (Selected.degree .cmpr).Matches h := by
  simp [MergesWith, Modifier.adverb, CFeature.ChecksNext, CFeature.ChecksSite,
    CFeature.ChecksHost]

/-- An underspecified adverb merges with the maximal noun phrase *so soon* adjoins to, not with the
nonmaximal noun of (104) (p. 479). -/
theorem adverb_mergesWith_maximal :
    MergesWith [.adverb] (.at soSoonAVisit ⟨[1]⟩) ∧ ¬ MergesWith [.adverb] nounSite := by
  decide

/-- Coordinated before a noun, an adjective or an underspecified adverb may come first and only an
adjective last, as in the 2020 analysis (p. 480). -/
theorem mergesWith_iff_nominalCoordination (m₁ m₂ : Option AdvHead) :
    MergesWith [.ofAdvHead m₁, .ofAdvHead m₂] nounSite ↔ NominalCoordination m₁ m₂ := by
  rcases m₁ with _ | _ | _ <;> rcases m₂ with _ | _ | _ <;> decide

/-- Coordinated with a measure phrase before a comparative, an underspecified adverb must come
first, as in *twice and maybe even three times taller* ((98)). -/
theorem mergesWith_cmpr_iff : ∀ x ∈ [Modifier.measure, .adverb],
    ∀ y ∈ [Modifier.measure, .adverb], (MergesWith [x, y] (.degree .cmpr) ↔ y = .measure) := by
  decide

/-! ### The paper's examples -/

open Examples

/-- `modifierOf? s` is the modifier the label `s` names. -/
def modifierOf? (s : String) : Option Modifier :=
  [("AP", .adjective), ("non-ly AdvP", .adverb), ("-ly AdvP", .lyAdverb), ("MP", .measure)].lookup s

/-- `modifierList? e` lists a row's modifiers, in order. -/
def modifierList? (e : Datum) : Option (List Modifier) :=
  (e.features "modifier").mapM modifierOf?

/-- `host? e` is the site a row's modifiers merge with, the noun of (104) for a noun. -/
def host? (e : Datum) : Option Site :=
  e.parse? "host" [("N", nounSite), ("CMPR", .degree .cmpr), ("equative", .degree .eq)]

theorem construction_rows : ∀ e ∈ Examples.all, e.feature? "construction" ∈
    [some "argument", some "semantic", some "selection", some "modifiers", some "stacked"] := by
  decide

/-- The revision decides the arguments, alone or coordinated ((9)–(10), (14), (38)–(39), (42b),
(52a)). -/
theorem argument_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "argument" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
      (Admits (Satisfies (checkedOnce d) cats) ps ↔ e.judgment = .acceptable) := by
  decide

/-- Of the acceptable coordinated arguments, the 2020 grammar rejects exactly those whose
conjuncts are all selected and differ in category ((9), (10), (14a)). -/
theorem argument_rows_licensed : ∀ e ∈ Examples.all,
    e.feature? "construction" = some "argument" → e.judgment = .acceptable →
      ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
        (¬ Admits (Licensed (checkedOnce d) cats) ps ↔
          (∀ p ∈ ps, p ∈ cats) ∧ ∃ p ∈ ps, ∃ q ∈ ps, p ≠ q) := by
  decide

/-- On the 2020 paper's arguments the revision keeps every judgment except its (64) and (69), which
it admits. -/
theorem argument_rows_2020 : ∀ e ∈ BrueningAlKhalaf2020.Examples.all,
    e.feature? "construction" = some "argument" →
      ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
        (Admits (Satisfies (checkedOnce d) cats) ps ↔ e.judgment = .acceptable ∨
          (∀ p ∈ ps, p ∈ cats) ∧ ∃ p ∈ ps, ∃ q ∈ ps, p ≠ q) := by
  decide

-- (42c), §5.6
theorem semantic_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "semantic" →
    e.judgment ≠ .acceptable ∧ ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
      Admits (Satisfies (checkedOnce d) cats) ps := by
  decide

/-- The analysis decides the coordinated and lone modifiers ((22), (36), (97)–(99)). -/
theorem modifier_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "modifiers" →
    ∃ ms ∈ modifierList? e, ∃ h ∈ host? e, (MergesWith ms h ↔ e.judgment = .acceptable) := by
  decide

/-- Stacked modifiers each merge with a projection of the noun, so an underspecified adverb
cannot precede an adjective uncoordinated ((20), (66), (67)). -/
theorem stacked_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "stacked" →
    ∃ ms ∈ modifierList? e, ∃ h ∈ host? e,
      ((∀ m ∈ ms, MergesWith [m] h) ↔ e.judgment = .acceptable) := by
  decide

/-- The analysis decides the 2020 paper's prenominal examples ((44), its p. 15, (56a), (57a)). -/
theorem prenominal_rows_2020 : ∀ e ∈ BrueningAlKhalaf2020.Examples.all,
    e.feature? "construction" = some "prenominal" →
      ∃ ms ∈ modifierList? e, (MergesWith ms nounSite ↔ e.judgment = .acceptable) := by
  decide

/-! ### The surveys -/

/-- `c.modifiers` is the lone prenominal modifier of the items of a condition of Experiment 1a. -/
def Exp1aCondition.modifiers : Exp1aCondition → Option (List Modifier)
  | .adjective => some [.adjective]
  | .adverb => some [.adverb]
  | _ => none

/-- The analysis admits the adjectives of Experiment 1a and not the adverbs. -/
theorem exp1a_predictions : ∀ c : Exp1aCondition, ∀ ms ∈ c.modifiers,
    (MergesWith ms nounSite ↔ c = .adjective) := by
  decide

/-- `c.modifiers` is the lone prenominal modifier of the items of a condition of Experiment 2,
whose *one*-replacement rules out a compound. -/
def Exp2Condition.modifiers : Exp2Condition → Option (List Modifier)
  | .adjective => some [.adjective]
  | .adverb => some [.adverb]
  | _ => none

/-- The analysis admits the adjectives of Experiment 2 and not the adverbs. -/
theorem exp2_predictions : ∀ c : Exp2Condition, ∀ ms ∈ c.modifiers,
    (MergesWith ms nounSite ↔ c = .adjective) := by
  decide

/-- `c.phrases` is the complement of the items of a condition of Experiment 1b, all after a
preposition or verb that selects noun phrases only. -/
def Exp1bCondition.phrases : Exp1bCondition → Option (List Cat)
  | .coordination => some [N, .C]
  | .simple => some [.C]
  | _ => none

/-- The revision admits the coordinations of Experiment 1b and not the bare clauses. -/
theorem exp1b_predictions : ∀ c : Exp1bCondition, ∀ ps ∈ c.phrases,
    (Admits (Satisfies (checkedOnce .headInitial) {N}) ps ↔ c = .coordination) := by
  decide

/-- For the speakers whose S-features persist (p. 457), the coordinations of Experiment 1b are out
(§5.9). -/
theorem exp1b_persisting : ∀ c : Exp1bCondition, ∀ ps ∈ c.phrases,
    ¬ Admits (Satisfies (ConjunctAgreement.all.conjuncts .headInitial) {N}) ps := by
  decide

end Bruening2025
