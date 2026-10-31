/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Minimal
public import Mathlib.Tactic.DeriveFintype
public import Studies.BelkNeelemanPhilip2023
public import Studies.CitkoGracaninYuksek2020
public import Linglib.Syntax.Minimalist.Label.RaisingHead

/-!
# Citko and Gračanin-Yuksek (2025): Economy in PF Reduction: Why and When (Not) to Elide Multidominant Structures

Material can go unpronounced in two ways: shared between conjuncts (multidominance) or elided.
Citko and Gračanin-Yuksek argue that economy chooses between them. Among the admissible
derivations of a string with a given reading, the one spending the fewest lexical items, Merges
and ellipses wins, and a derivation is admissible when none of its ellipses is vacuous
(Pronunciation Economy) and no phase edge hosting several wh-phrases reaches PF in a language that
bans multiple wh-fronting there. A coordinated wh-question (*What and when should you teach?*)
therefore shares its heads but not its phrases, while a coordinated sluice (*I forgot what and
when*) shares its whole C′ and elides it once, which hides the vP edge both wh-phrases crossed.

## Implementation notes

* A candidate is a linearized syntactic object spelled out by `Linearization/Spellout.lean`: a token
  at two positions is shared, a moved wh-phrase leaves traces at the vP edge and its base position,
  and the coordinator is left out, so a string is its conjuncts' words. A right node raising
  candidate is a pruning derivation of Belk, Neeleman and Philip, each free pruning an ellipsis.
* The paired reading is the it reading of the authors' earlier paper (`CitkoGracaninYuksek2020`),
  and Pronunciation Economy is that paper's ban on vacuous ellipsis
  (`Minimalist.PronunciationEconomy`).
* As the paper's footnote on the parameter allows, every edge with several wh-specifiers receives
  an asterisk, and a language is the set of categories whose asterisks PF cannot interpret.
* The candidates are the derivations the paper compares; optimality is minimality among them
  (`MinimalFor`) under the pointwise order on costs.

## References

* [B. Citko and M. Gračanin-Yuksek, *Economy in PF Reduction: Why and When (Not) to Elide
  Multidominant Structures* (2025)][citko-gracanin-yuksek-2025]
* [B. Citko and M. Gračanin-Yuksek, *Conjunction saves multiple sluicing: How \*(and) why?*
  (2020)][citko-gracanin-yuksek-2020]
* [N. Chomsky, *Some notes on economy of derivation and representation* (1991)][chomsky-1991]
* [J. Merchant, *The Syntax of Silence* (2001)][merchant-2001]
* [M. Marcolli, N. Chomsky and R. C. Berwick, *Mathematical Structure of Syntactic Merge: An
  Algebraic Model for Generative Linguistics* (2025)][marcolli-chomsky-berwick-2025]
* [Z. Belk, A. Neeleman and J. Philip, *What divides, and what unites, right-node raising*
  (2023)][belk-neeleman-philip-2023]
-/

@[expose] public section

namespace CitkoGracaninYuksek2025

open Minimalist Minimalist.LinearizedSyntacticObject RoseTree
open Minimalist.SyntacticObject (Vertex)
open CitkoGracaninYuksek2020 (tok ItReading)

/-! ### The lexicon -/

def what := tok 1 .D (phon := "what") (features := .single .wh true)
def when := tok 2 .P (phon := "when") (features := .single .wh true)
def who := tok 3 .D (phon := "who") (features := .single .wh true)
def you := tok 4 .D (phon := "you")
def T := tok 5 .T [.v]
def v := tok 6 .v [.V]
def teach := tok 7 .V [.D] "teach"
def should := tok 8 .C [.T] "should"
def will := tok 9 .C [.T] "will"
/-- The null complementizer, and a second one. -/
def c := tok 10 .C [.T]
def c' := tok 11 .C [.T]
/-- The null complementizer bearing [E], and a second one. -/
def cE := tok 12 .C [.T] (ellipsis := true)
def cE' := tok 13 .C [.T] (ellipsis := true)
/-- The tokens a second, separately built clause draws. -/
def you' := tok 14 .D (phon := "you")
def T' := tok 15 .T [.v]
def v' := tok 16 .v [.V]
def teach' := tok 17 .V [.D] "teach"
/-- The auxiliary in T. -/
def shouldT := tok 18 .T [.v] "should"
def saw := tok 20 .V [.D] "saw"

/-! ### The candidates -/

/-- `clause` builds `[CP wh [C′ c [TP subj [T′ T [vP wh [v′ v VP]]]]]]`, the wh-phrase moved through
the edge of vP. -/
def clause (wh c subj T v : LexicalItem.Token)
    (VP : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  wh * (c * (subj * (T * (traceOf wh * (v * VP)))))

/-- In non-bulk sharing under the complementizers `c₁` and `c₂`, each wh-phrase stays in its own
conjunct and the subject, T, v and verb are shared ((10b), (14), (16b), (38d), (45c), (46b)). -/
def nonBulk (c₁ c₂ : LexicalItem.Token) : LinearizedSyntacticObject :=
  (clause what c₁ you T v (teach * traceOf what)) * (clause when c₂ you T v (teach * traceOf when))

/-- In bulk sharing one C′ sits under both wh-phrases, both of which moved through its vP edge
((12b), (20b)). -/
def bulk (c : LexicalItem.Token) : LinearizedSyntacticObject :=
  let c' := c * (you * (T * (traceOf what * (traceOf when * (v * ((teach * traceOf what) *
    traceOf when))))))
  (what * c') * (when * c')

/-- Footnote 21's alternative to `bulk` shares a TP under two complementizers. -/
def bulkTP (c₁ c₂ : LexicalItem.Token) : LinearizedSyntacticObject :=
  let tp := you * (T * (traceOf what * (traceOf when * (v * ((teach * traceOf what) *
    traceOf when)))))
  (what * (c₁ * tp)) * (when * (c₂ * tp))

/-- The ellipsis analysis of the coordinated wh-question (11b) builds two clauses from separate
tokens and elides the first under its [E] complementizer, with its auxiliary in T as the
Sluicing-COMP generalization requires of a sluice. -/
def cwhEllipsis : LinearizedSyntacticObject :=
  (what * (cE * (you * (shouldT * (traceOf what * (v * (teach * traceOf what))))))) *
    (clause when should you' T' v' (teach' * traceOf when))

/-- The double-ellipsis analysis of the coordinated sluice (19b), the authors' earlier one, builds
two clauses from separate tokens and elides both; the second clause's object is a deleted copy of
*what*, which vehicle change reads as *it*. -/
def csEllipsis : LinearizedSyntacticObject :=
  (clause what cE you T v (teach * traceOf what)) *
    (clause when cE' you' T' v' ((teach' * traceOf what) * traceOf when))

/-- Its nonpaired counterpart (45b) leaves the second clause's verb without an object. -/
def csnrEllipsis : LinearizedSyntacticObject :=
  (clause what cE you T v (teach * traceOf what)) *
    (clause when cE' you' T' v' (teach' * traceOf when))

/-- In a multiple question both wh-phrases are fronted through the vP edge, as in (28b) and, under
an [E] complementizer, the multiple sluice (29b). -/
def multipleQuestion (c : LexicalItem.Token) : LinearizedSyntacticObject :=
  who * (what * (c * (traceOf who * (T * (traceOf who * (traceOf what * (v * (saw *
    traceOf what))))))))

/-- The coordinated wh-question (10b), its complementizer shared. -/
abbrev cwh := nonBulk should should
/-- Its bulk-sharing rival (12b). -/
abbrev cwhBulk := bulk should
/-- Its rival with a null complementizer in the first conjunct (14). -/
abbrev cwhNullC := nonBulk c should
/-- Footnote 15 puts the null complementizer in the second conjunct instead. -/
abbrev cwhNullCSecond := nonBulk should c
/-- The embedded coordinated wh-question (15a) with its null complementizer shared, and with two
(15b). -/
abbrev cwhEmbedded := nonBulk c c
abbrev cwhEmbeddedTwoC := nonBulk c c'
/-- Two pronounced complementizers (16b). -/
abbrev cwhTwoAux := nonBulk should will
/-- The coordinated sluice (20b), (26b), (38b). -/
abbrev cs := bulk cE
/-- Its rival with two [E] complementizers over a shared TP (footnote 21). -/
abbrev csTwoC := bulkTP cE cE'
/-- The coordinated sluice with the shape of the coordinated wh-question, one shared [E]
complementizer over two TPs ((38d), (45c)). -/
abbrev csSharedC := nonBulk cE cE
/-- The nonpaired coordinated sluice (46b) has two complementizers, one bearing [E]. -/
abbrev csnr := nonBulk cE c
/-- Its rival in which both complementizers bear [E], set aside after (46b). -/
abbrev csnrTwoE := nonBulk cE cE'

/-! ### Cost -/

/-- A derivation's cost has three dimensions, the lexical items drawn, the Merges, and the
applications of ellipsis. -/
inductive CostDimension
  | lexicalItems
  | mergeOps
  | ellipsisOps
  deriving DecidableEq, Fintype

protected theorem CostDimension.forall {p : CostDimension → Prop} :
    (∀ i, p i) ↔ p .lexicalItems ∧ p .mergeOps ∧ p .ellipsisOps :=
  ⟨fun h ↦ ⟨h _, h _, h _⟩, fun ⟨h₁, h₂, h₃⟩ i ↦ by cases i <;> assumption⟩

/-- The cost of a derivation is a count per dimension, ordered pointwise, so that one derivation is
more economical than another when it spends no more on any dimension and less on one. -/
abbrev DerivationCost := CostDimension → ℕ

instance : DecidableLE DerivationCost := fun _ _ ↦
  decidable_of_iff _ (Pi.le_def.trans CostDimension.forall).symm

instance : DecidableLT DerivationCost := decidableLTOfDecidableLE

/-- The cost of an object counts its tokens as the lexical items drawn, its internal terms as the
Merges, a shared constituent being built once, and its elided domains as the applications of
ellipsis. The terms are [marcolli-chomsky-berwick-2025]'s subtrees, each taken once. -/
def cost (t : LinearizedSyntacticObject) : DerivationCost
  | .lexicalItems => (tokens t).length
  | .mergeOps => (t.val.subtrees.filter (·.arity ≠ 0)).dedup.length
  | .ellipsisOps => (elidedDomains t).length

/-! ### The multiple-wh-fronting parameter (27) -/

/-- `projection t` finds the specifiers and head of the projection at the root of `t`. Going down
the right spine, the specifiers are the left daughters above the head, which is the first
selecting item met; the result is `none` when the spine ends first. This is the drawing
convention `headIndex?` falls back on where the raising head is undefined, as it is wherever a
phrase stands in a specifier. -/
def projection : RoseTree Vertex → Option (List (RoseTree Vertex) × LexicalItem.Token)
  | .node (.inl none) [.node (.inl (some tok)) [], r] =>
      if tok.item.sel = [] then
        (projection r).map fun x ↦ (.node (.inl (some tok)) [] :: x.1, x.2)
      else some ([], tok)
  | .node (.inl none) [l, r] => (projection r).map fun x ↦ (l :: x.1, x.2)
  | _ => none

/-- The token heading a constituent is its raising head, and for a deleted copy the token whose
phrase it copies. -/
def headToken? (s : RoseTree Vertex) : Option LexicalItem.Token :=
  match s.value with
  | .inr (some tok) => some tok
  | _ => treeRaisingHead s

/-- A constituent is a wh-specifier when its head is a wh-token or its trace. -/
def IsWhSpecifier (s : RoseTree Vertex) : Prop :=
  ∃ tok ∈ (headToken? s).toList, tok.item.IsWh

instance (s : RoseTree Vertex) : Decidable (IsWhSpecifier s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The heads of the projections whose edges host several wh-specifiers, each of which receives
an asterisk. -/
def asterisked (t : LinearizedSyntacticObject) : List LexicalItem.Token :=
  t.val.positionedSubtrees.filterMap fun x ↦ (projection x.2).bind fun y ↦
    if 1 < y.1.countP (decide <| IsWhSpecifier ·) then some y.2 else none

/-- The categories of the asterisked projections whose heads reach PF unsilenced. -/
def pfAsterisks (t : LinearizedSyntacticObject) : Finset Cat :=
  (((asterisked t).filter (¬ IsSilenced t ·)).map (·.item.cat)).toFinset

/-- `t` converges at PF in a language whose multiple-wh-fronting parameter is `mwf`, the categories
whose asterisks PF cannot interpret, when no asterisk of those categories reaches PF. -/
def ConvergesIn (mwf : Finset Cat) (t : LinearizedSyntacticObject) : Prop :=
  Disjoint mwf (pfAsterisks t)

instance (mwf : Finset Cat) (t : LinearizedSyntacticObject) : Decidable (ConvergesIn mwf t) :=
  inferInstanceAs (Decidable (Disjoint _ _))

theorem convergesIn_of_pfAsterisks_eq_empty {t : LinearizedSyntacticObject} (h : pfAsterisks t = ∅)
    (mwf : Finset Cat) : ConvergesIn mwf t := by
  rw [ConvergesIn, h]
  exact Finset.disjoint_empty_right _

/-- In English variety A several wh-specifiers are banned at both phase edges. -/
def englishA : Finset Cat := {.v, .C}
/-- In English variety B they are banned at the vP edge only. -/
def englishB : Finset Cat := {.v}
/-- German and Greek lack multiple wh-fronting (30) but have multiple sluicing (31). -/
def german : Finset Cat := {.v}
def greek : Finset Cat := {.v}
/-- Russian moves all its wh-phrases, where English moves one (after (29)). -/
def russian : Finset Cat := ∅
/-- Romanian, where bulk sharing derives coordinated wh-questions (footnote 14). -/
def romanian : Finset Cat := ∅

/-! ### Optimality -/

/-- A derivation is admissible in a language when none of its ellipses is vacuous, Pronunciation
Economy (39), and it converges at PF. -/
def Admissible (mwf : Finset Cat) (t : LinearizedSyntacticObject) : Prop :=
  PronunciationEconomy t ∧ ConvergesIn mwf t

instance (mwf : Finset Cat) (t : LinearizedSyntacticObject) : Decidable (Admissible mwf t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `s` competes with `t` when it yields the same string with the same reading. -/
def Competes (s t : LinearizedSyntacticObject) : Prop :=
  pfPhon s = pfPhon t ∧ (ItReading s ↔ ItReading t)

instance (s t : LinearizedSyntacticObject) : Decidable (Competes s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Economy makes `t` optimal among the candidates `l` in a language when it is admissible and no
admissible competitor among them costs less. -/
def Optimal (mwf : Finset Cat) (l : List LinearizedSyntacticObject)
    (t : LinearizedSyntacticObject) : Prop :=
  MinimalFor (fun s ↦ s ∈ l ∧ Competes s t ∧ Admissible mwf s) cost t

section Optimal

variable {mwf mwf' : Finset Cat} {l : List LinearizedSyntacticObject}
  {t : LinearizedSyntacticObject}

theorem optimal_iff : Optimal mwf l t ↔ (t ∈ l ∧ Admissible mwf t) ∧
    ∀ s ∈ l, Competes s t → Admissible mwf s → cost s ≤ cost t →
      cost t ≤ cost s := by
  simp [Optimal, MinimalFor, Competes, and_imp]

instance : Decidable (Optimal mwf l t) := decidable_of_iff _ optimal_iff.symm

theorem optimal_congr (h : ∀ s ∈ l, pfAsterisks s = ∅) : Optimal mwf l t ↔ Optimal mwf' l t := by
  have key (m : Finset Cat) : (fun s ↦ s ∈ l ∧ Competes s t ∧ Admissible m s) =
      fun s ↦ s ∈ l ∧ Competes s t ∧ PronunciationEconomy s := by
    funext s
    simp +contextual [Admissible, convergesIn_of_pfAsterisks_eq_empty, h]
  simp only [Optimal, key]

end Optimal

/-! ### Coordinated wh-questions (§3.1, §4.1) -/

/-- The derivations of *What and when should you teach?* the paper compares. -/
def cwhCandidates : List LinearizedSyntacticObject := [cwh, cwhEllipsis, cwhBulk, cwhNullC]

theorem cwh_pf : pfPhon cwh = ["what", "when", "should", "you", "teach"] := by decide
theorem pfPhon_cwhCandidates : ∀ t ∈ cwhCandidates, pfPhon t = pfPhon cwh := by decide
-- footnote 15
theorem cwhNullCSecond_pf : pfPhon cwhNullCSecond = ["what", "should", "when", "you", "teach"] := by
  decide
theorem cwhTwoAux_pf : pfPhon cwhTwoAux = ["what", "should", "when", "will", "you", "teach"] := by
  decide

theorem cwh_nonpaired : orphanTraces .raising cwh = [] := by decide
theorem cwhBulk_paired : ItReading cwhBulk := by decide

theorem cwhBulk_lt_cwh : cost cwhBulk < cost cwh := by decide

-- (37b)
theorem pfAsterisks_cwhBulk : pfAsterisks cwhBulk = {.v} := by decide

theorem convergesIn_cwhBulk_iff {mwf : Finset Cat} : ConvergesIn mwf cwhBulk ↔ .v ∉ mwf := by
  rw [ConvergesIn, pfAsterisks_cwhBulk, Finset.disjoint_singleton_right]

theorem pfAsterisks_cwh : pfAsterisks cwh = ∅ := by decide

/-- In both English varieties the coordinated wh-question has one optimal derivation, non-bulk
sharing: the ellipsis analysis and the extra null complementizer cost more, and bulk sharing,
though cheaper, crashes at the vP edge, so the paired reading is unavailable. -/
theorem optimal_cwh_iff : ∀ t ∈ cwhCandidates,
    (Optimal englishA cwhCandidates t ↔ t = cwh) ∧
      (Optimal englishB cwhCandidates t ↔ t = cwh) := by
  decide

-- footnote 14
theorem optimal_cwhBulk_romanian : Optimal romanian cwhCandidates cwhBulk := by decide

-- (15)
theorem cwhEmbedded_lt_twoC :
    pfPhon cwhEmbeddedTwoC = pfPhon cwhEmbedded ∧
      cost cwhEmbedded < cost cwhEmbeddedTwoC := by
  decide

/-! ### Coordinated sluices (§3.2, §4.2, §6.1) -/

/-- The derivations of *what and when* the paper compares, paired and nonpaired. -/
def csCandidates : List LinearizedSyntacticObject :=
  [cs, csEllipsis, csTwoC, csSharedC, csnr, csnrEllipsis, csnrTwoE]

theorem cs_pf : pfPhon cs = ["what", "when"] := by decide
theorem pfPhon_csCandidates : ∀ t ∈ csCandidates, pfPhon t = pfPhon cs := by decide
theorem paired_csCandidates :
    ∀ t ∈ csCandidates, ItReading t ↔ t = cs ∨ t = csEllipsis ∨ t = csTwoC := by
  decide

-- (26b)
theorem v_mem_asterisked_cs : v ∈ asterisked cs := by decide
theorem pfAsterisks_csCandidates : ∀ t ∈ csCandidates, pfAsterisks t = ∅ := by decide

theorem csSharedC_vacuous : ¬ PronunciationEconomy csSharedC := by decide
theorem csnrTwoE_excluded :
    ¬ PronunciationEconomy csnrTwoE ∧ cost csSharedC < cost csnrTwoE := by
  decide

/-- In every language the coordinated sluice has two optimal derivations. For the paired
reading, the elided shared C′ is cheaper than eliding two clauses or sharing TP under two
complementizers. For the nonpaired reading, two complementizers of which only one bears [E] are
cheaper than eliding two clauses, while a shared [E] complementizer, which draws one token fewer,
elides vacuously, as does a second [E]. -/
theorem optimal_cs_iff (mwf : Finset Cat) :
    ∀ t ∈ csCandidates, Optimal mwf csCandidates t ↔ t = cs ∨ t = csnr := by
  intro t ht
  rw [optimal_congr pfAsterisks_csCandidates (mwf' := ∅)]
  revert t
  decide

theorem csEllipsis_admissible_not_optimal (mwf : Finset Cat) :
    Admissible mwf csEllipsis ∧ ¬ Optimal mwf csCandidates csEllipsis :=
  ⟨⟨by decide, convergesIn_of_pfAsterisks_eq_empty (pfAsterisks_csCandidates _ (by decide)) _⟩,
    fun h ↦ absurd ((optimal_cs_iff mwf csEllipsis (by decide)).1 h) (by decide)⟩

-- footnote 30
theorem csnr_silences_shared :
    (∃ p ∈ occurrences csnr teach, ∀ K ∈ elidedDomains csnr, ¬ K ≤ p) ∧
      IsSilenced csnr teach := by decide

/-! ### Multiple questions and multiple sluices (§3.2.2) -/

-- (28b)
theorem pfAsterisks_multipleQuestion : pfAsterisks (multipleQuestion c) = {.v, .C} := by decide

-- (29b)
theorem pfAsterisks_multipleSluice : pfAsterisks (multipleQuestion cE) = {.C} := by decide

theorem convergesIn_multipleQuestion_iff {mwf : Finset Cat} :
    ConvergesIn mwf (multipleQuestion c) ↔ .v ∉ mwf ∧ .C ∉ mwf := by
  rw [ConvergesIn, pfAsterisks_multipleQuestion, Finset.disjoint_insert_right,
    Finset.disjoint_singleton_right]

/-- Multiple sluicing converges exactly where the CP edge does not count. -/
theorem convergesIn_multipleSluice_iff {mwf : Finset Cat} :
    ConvergesIn mwf (multipleQuestion cE) ↔ .C ∉ mwf := by
  rw [ConvergesIn, pfAsterisks_multipleSluice, Finset.disjoint_singleton_right]

theorem multipleQuestion_multipleSluice :
    ¬ ConvergesIn englishA (multipleQuestion c) ∧ ¬ ConvergesIn englishB (multipleQuestion c) ∧
      ConvergesIn russian (multipleQuestion c) ∧
      ¬ ConvergesIn englishA (multipleQuestion cE) ∧ ConvergesIn englishB (multipleQuestion cE) ∧
      ConvergesIn german (multipleQuestion cE) ∧ ConvergesIn greek (multipleQuestion cE) := by
  simp [convergesIn_multipleQuestion_iff, convergesIn_multipleSluice_iff, englishA, englishB,
    german, greek, russian]

/-! ### Right node raising (§6.2) -/

/-- The cost of a derivation of right node raising counts the lexical items and Merges of its
structure, and each free pruning as an application of ellipsis. -/
def rnrCost (d : BelkNeelemanPhilip2023.Derivation) : DerivationCost
  | .lexicalItems => cost d.input .lexicalItems
  | .mergeOps => cost d.input .mergeOps
  | .ellipsisOps => d.free.length

def alice := tok 21 .D (phon := "Alice")
def iris := tok 22 .D (phon := "Iris")
def must := tok 23 .T [.V] "must"
def oughtToBe := tok 25 .T [.V] "ought to be"
def shouldRNR := tok 26 .T [.V] "should"
/-- *Work*, a second *work*, and *working*. -/
def work := tok 27 .V [.P] "work"
def work' := tok 35 .V [.P] "work"
def working := tok 28 .V [.P] "working"
def on := tok 29 .P [.N] "on"
def different := tok 30 .A (phon := "different")
def topics := tok 31 .N (phon := "topics")
def on' := tok 32 .P [.N] "on"
def different' := tok 33 .A (phon := "different")
def topics' := tok 34 .N (phon := "topics")

/-- The pivot, `on different topics`. -/
def pivot : LinearizedSyntacticObject := on * (different * topics)

/-- `[TP subj [T′ T VP]]`. -/
def tp (subj T : LexicalItem.Token) (VP : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  subj * (T * VP)

/-- In example (53b), Belk, Neeleman and Philip's analysis of Larson's mixed pivot, the pivot is
multidominated and its first branch pruned, and then the first verb phrase, by then the bare verb,
is pruned freely. -/
def rnrMixed : BelkNeelemanPhilip2023.Derivation :=
  ⟨(tp alice must (work * pivot)) * (tp iris oughtToBe (working * pivot)),
    [(⟨[0, 1, 1, 1]⟩, ⟨[1, 1, 1, 1]⟩)], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩
/-- Example (54) builds the first verb phrase with its own pivot and elides it. -/
def rnrElided : BelkNeelemanPhilip2023.Derivation :=
  ⟨(tp alice must (work * (on' * (different' * topics')))) * (tp iris oughtToBe (working * pivot)),
    [], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩
/-- Example (55b) multidominates the verb phrase, the verbs matching. -/
def rnrShared : BelkNeelemanPhilip2023.Derivation :=
  let VP := work * pivot
  ⟨(tp alice must VP) * (tp iris shouldRNR VP), [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)], []⟩
/-- The rival of (55b) with the shape of (53b), each conjunct with its own *work*. -/
def rnrMatchedMixed : BelkNeelemanPhilip2023.Derivation :=
  ⟨(tp alice must (work * pivot)) * (tp iris shouldRNR (work' * pivot)),
    [(⟨[0, 1, 1, 1]⟩, ⟨[1, 1, 1, 1]⟩)], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩

theorem rnrMixed_phon : rnrMixed.phon =
    ["Alice", "must", "Iris", "ought to be", "working", "on", "different", "topics"] := by decide
theorem rnrMixed_lt_elided :
    rnrMixed.Licensed ∧ rnrElided.Licensed ∧ rnrElided.phon = rnrMixed.phon ∧
      rnrCost rnrMixed < rnrCost rnrElided := by
  decide

theorem rnrShared_phon : rnrShared.phon =
    ["Alice", "must", "Iris", "should", "work", "on", "different", "topics"] := by decide
theorem rnrShared_lt_mixed :
    rnrShared.Licensed ∧ rnrMatchedMixed.Licensed ∧ rnrMatchedMixed.phon = rnrShared.phon ∧
      rnrCost rnrShared < rnrCost rnrMatchedMixed := by
  decide

/-- Of the three licensed derivations of (56), multidominating the auxiliary phrase is cheapest,
leaving the break before *have* ((51), (57), (58), (59)). -/
theorem rnr56_economy :
    (∀ d ∈ BelkNeelemanPhilip2023.derivations51, d.Licensed) ∧
      BelkNeelemanPhilip2023.shareAuxP.pivotOnset = some "have" ∧
      rnrCost BelkNeelemanPhilip2023.shareAuxP < rnrCost BelkNeelemanPhilip2023.shareVP ∧
      rnrCost BelkNeelemanPhilip2023.shareAuxP < rnrCost BelkNeelemanPhilip2023.sharePP :=
  ⟨BelkNeelemanPhilip2023.pivotOnset_nonfinite.1, by decide, by decide, by decide⟩

end CitkoGracaninYuksek2025
