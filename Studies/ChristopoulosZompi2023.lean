module

public import Linglib.Core.Order.Concept
public import Linglib.Morphology.Exponence.SubsetRule
public import Linglib.Fragments.Latvian.Pronouns
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.Paradigm.Contiguity

/-!
# Christopoulos and Zompì (2023): Weak Case Containment

Three featural decompositions of the nominative, accusative and dative are compared under the
Subset Principle, and what separates them is their natural classes, the sets of cases some
specification picks out: Strong Case Containment has fewer than Weak Case Containment and Weak fewer
than No Case Containment, [each inside the next](##naturalClasses_ssubset). A decomposition derives
ABA [exactly when](##forall_isContiguous_iff_not_isNaturalClass) the accusative alone, or the
nominative and dative together, form a natural class, as they do under No Case Containment. Strong
Case Containment excludes ABA, but
[a rule winning an accusative over another applies in no nominative](##scc_prediction), so it
[cannot derive](##latvian_not_scc) the Latvian stems that Weak Case Containment
[derives](##latvian_stems). Weak Case Containment is, up to its mirror image,
[the most expressive decomposition excluding ABA](##naturalClasses_subset_of_forall_isContiguous).

## Implementation notes

* The cases are the three-cell chain `Fin 3`, in the order NOM ≺ ACC ≺ DAT, so *ABA is
  `IsContiguous` and the PATTERN columns are `Paradigm.abb` and its siblings. Cells of the empirical
  paradigms are products of case, number and gender, and their bundles lie in the product order.
* Clause (1b) presupposes a unique rule with the greatest number of features. As competition it is
  `IsElsewhereWinner` under that count, which leaves two winners at a tie; `realize` breaks ties by
  the order of the rule set, and [the two agree on a derivation](##realize_of_isDerivation). Rule
  sets here list the least specific rule first, so that no result leans on that order.
* Natural classes are extents in the sense of formal concept analysis, `Order.IsExtent`, the
  construction of [broe-1993] for segment inventories. That Weak Case Containment is maximal among
  them is this file's reading: the paper argues that it suffices.
* Rule sets are antihomophonous where fn. 9 says "barring accidental homophony"; a homophonous pair
  is the disjunctive rule (4), with which Strong Case Containment
  [does derive the stems](##latvian_scc_of_disjunctive).
* Features matter beyond the natural classes only for counting. `{k₂}` and `{k₁, k₂}` pick out one
  class, and Table 25 writes `{(k₁,) k₂}` except where `{k₂}` would tie.
* A row of a table gives each case's winner, two alternatives where the table parenthesizes a
  feature, so its rules A, B, C are its distinct winners.

## TODO

* The surface containment predictions of Table 37, from hypothesis (10) (§6.2).
* The markedness features of [mcfadden-2018], rejected on Latvian and Tocharian (§3.3).

## References

* [bobaljik-2012]
* [broe-1993]
* [caha-2009]
* [christopoulos-zompi-2023]
* [halle-1997]
* [mcfadden-2018]
* [smith-moskal-xu-kang-bobaljik-2019]
-/

@[expose] public section

namespace ChristopoulosZompi2023

open Morphology
open SubsetRule (card)

/-- The privative case features k₀–k₃ across the three decompositions. -/
inductive K | k0 | k1 | k2 | k3
  deriving DecidableEq, Fintype, Repr

/-- The nominative, the first of the *ABA order NOM ≺ ACC ≺ DAT. -/
abbrev nom : Fin 3 := 0

/-- The accusative. -/
abbrev acc : Fin 3 := 1

/-- The dative. -/
abbrev dat : Fin 3 := 2

/-- **Strong Case Containment** (Table 1): a chain ∅ ⊂ {k₁} ⊂ {k₁,k₂}. -/
def scc : Paradigm 3 (Finset K) := ![∅, {.k1}, {.k1, .k2}]

/-- **No Case Containment** (Table 2): pairwise incomparable feature sets; k₃ is the NOM/ACC feature
absent from DAT. -/
def ncc : Paradigm 3 (Finset K) := ![{.k0, .k3}, {.k1, .k3}, {.k1, .k2}]

/-- **Weak Case Containment** (Table 24): ACC ⊂ DAT as in SCC, but NOM carries its own k₀,
incomparable to ACC, and there is no k₃. -/
def wcc : Paradigm 3 (Finset K) := ![{.k0}, {.k1}, {.k1, .k2}]

variable {F : Type*}

/-! ### *ABA -/

/-- The cases `S` are a natural class of a decomposition when they are an extent of the relation
between cases and the features they bear: the cases bearing all the features of a specification. -/
abbrev IsNaturalClass (D : Paradigm 3 (Finset K)) (S : Finset (Fin 3)) : Prop :=
  Order.IsExtent (fun c k ↦ k ∈ D c) (S : Set (Fin 3))

instance (D : Paradigm 3 (Finset K)) : DecidablePred (IsNaturalClass D) :=
  fun _ ↦ inferInstanceAs (Decidable (Order.IsExtent _ _))

theorem isNaturalClass_iff {D : Paradigm 3 (Finset K)} {S : Finset (Fin 3)} :
    IsNaturalClass D S ↔ ∃ s : Finset K, ∀ c, s ⊆ D c ↔ c ∈ S := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t.toFinset, fun c ↦ ?_⟩
    rw [← Finset.mem_coe, ← ht]
    simp [mem_lowerPolar_iff, Finset.subset_iff]
  · rintro ⟨s, hs⟩
    refine ⟨(s : Set K), Set.ext fun c ↦ ?_⟩
    simp [mem_lowerPolar_iff, ← hs c, Finset.subset_iff]

theorem inter_subset_and_iff_not_isNaturalClass {D : Paradigm 3 (Finset K)} :
    D nom ∩ D dat ⊆ D acc ∧ (D acc ⊆ D nom ∨ D acc ⊆ D dat) ↔
      ¬ IsNaturalClass D {acc} ∧ ¬ IsNaturalClass D {nom, dat} := by
  simp only [isNaturalClass_iff]
  constructor
  · rintro ⟨hi, hy⟩
    refine ⟨fun ⟨s, h⟩ ↦ ?_, fun ⟨s, h⟩ ↦ ?_⟩
    · have hs : s ⊆ D acc := (h acc).2 (by decide)
      obtain hd | hd := hy
      · exact absurd ((h nom).1 (hs.trans hd)) (by decide)
      · exact absurd ((h dat).1 (hs.trans hd)) (by decide)
    · have hs : s ⊆ D acc := fun k hk ↦
        hi (Finset.mem_inter.2 ⟨(h nom).2 (by decide) hk, (h dat).2 (by decide) hk⟩)
      exact absurd ((h acc).1 hs) (by decide)
  · rintro ⟨hy, hxz⟩
    refine ⟨by_contra fun hn ↦ hxz ⟨D nom ∩ D dat, fun c ↦ ?_⟩,
      by_contra fun hn ↦ hy ⟨D acc, fun c ↦ ?_⟩⟩
    · fin_cases c
      · exact iff_of_true Finset.inter_subset_left (by decide)
      · exact iff_of_false hn (by decide)
      · exact iff_of_true Finset.inter_subset_right (by decide)
    · obtain ⟨h₀, h₂⟩ := not_or.1 hn
      fin_cases c
      · exact iff_of_false h₀ (by decide)
      · exact iff_of_true subset_rfl (by decide)
      · exact iff_of_false h₂ (by decide)

/-- **ABA is a question of natural classes.** A decomposition derives ABA exactly when the
accusative alone, or the nominative and dative together, form a natural class, as the paper has it
of the accusative-specific set of No Case Containment (p. 885). -/
theorem forall_isContiguous_iff_not_isNaturalClass [Nontrivial F] {D : Paradigm 3 (Finset K)} :
    (∀ v : RuleSet (SubsetRule (Finset K) F), v.Antihomophonous →
        IsContiguous fun c ↦ v.realize card (D c)) ↔
      ¬ IsNaturalClass D {acc} ∧ ¬ IsNaturalClass D {nom, dat} := by
  rw [← inter_subset_and_iff_not_isNaturalClass]
  exact (forall₂_congr fun _ _ ↦ isContiguous_fin_three_iff _).trans
    (SubsetRule.forall_realize_eq_iff grade_strictMono)

theorem isContiguous_scc {v : RuleSet (SubsetRule (Finset K) F)} (hv : v.Antihomophonous) :
    IsContiguous fun c ↦ v.realize card (scc c) :=
  (isContiguous_fin_three_iff _).2 <|
    SubsetRule.realize_eq_of_inf_le_of_le hv (by decide) (by decide)

theorem isContiguous_wcc {v : RuleSet (SubsetRule (Finset K) F)} (hv : v.Antihomophonous) :
    IsContiguous fun c ↦ v.realize card (wcc c) :=
  (isContiguous_fin_three_iff _).2 <|
    SubsetRule.realize_eq_of_inf_le_of_le hv (by decide) (by decide)

-- Table 11, row 2: an elsewhere rule beside a rule for the accusative-specific set {k₁, k₃}
theorem ncc_aba_generable :
    ∀ c, RuleSet.realize [(⟨∅, 0⟩ : SubsetRule (Finset K) ℕ), ⟨{.k1, .k3}, 1⟩] card (ncc c) =
      some (Paradigm.aba c) := by
  decide

/-- A decomposition with ACC ⊂ DAT whose nominative and dative share k₃. -/
def accInDat : Paradigm 3 (Finset K) := ![{.k0, .k3}, {.k1}, {.k1, .k2, .k3}]

-- p. 895: containment of the accusative in the dative leaves ABA derivable, by a rule for k₃
theorem acc_ssubset_dat_derives_aba :
    accInDat acc ⊂ accInDat dat ∧
      ∀ c, RuleSet.realize [(⟨∅, 1⟩ : SubsetRule (Finset K) ℕ), ⟨{.k3}, 0⟩] card (accInDat c) =
        some (Paradigm.aba c) := by
  decide

/-! ### The derivation tables -/

/-- The rules for the specifications `w`, each with its specification as exponent, so that the rules
differ exactly where their specifications do. -/
def rules (w : Paradigm 3 (Finset K)) : RuleSet (SubsetRule (Finset K) (Finset K)) :=
  List.ofFn fun a ↦ ⟨w a, w a⟩

/-- The rules for `w` derive it under `D` when, competing by clause (1b), each case has its own rule
as its only winner. -/
abbrev IsDerivation (D w : Paradigm 3 (Finset K)) : Prop :=
  ∀ c a, (rules w).IsElsewhereWinner (OrderDual.toDual ∘ card) (D c) ⟨w a, w a⟩ ↔ w a = w c

-- clause (1b) and `realize` agree wherever (1b) decides
theorem realize_of_isDerivation {D w : Paradigm 3 (Finset K)} (hw : IsDerivation D w) (c : Fin 3) :
    (rules w).realize card (D c) = some (w c) := by
  have hwin := (hw c c).2 rfl
  refine RuleSet.realize_eq_of_forall_realizes ⟨_, hwin.prop.1, hwin.prop.2⟩ ?_
  rintro ψ ⟨r, hr, rfl⟩
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hr.prop.1
  exact (hw c a).1 hr

/-- The derivations under a decomposition, by their winners at NOM, ACC and DAT. -/
def derivations (D : Paradigm 3 (Finset K)) : Finset (Finset K × Finset K × Finset K) :=
  ((D nom).powerset ×ˢ (D acc).powerset ×ˢ (D dat).powerset).filter fun w ↦
    IsDerivation D ![w.1, w.2.1, w.2.2]

/-- A row of a derivation table: the specifications winning at NOM, ACC and DAT, two where the table
parenthesizes a feature, and the PATTERN column. -/
abbrev Row := List (Finset K) × List (Finset K) × List (Finset K) × Paradigm 3 ℕ

/-- The winners a table claims: each row's alternatives, those whose syncretism is the row's PATTERN
column in the form of `ker_eq_ker_iff_fin_three`. -/
def winners (t : List Row) : Finset (Finset K × Finset K × Finset K) :=
  (t.flatMap fun (a, b, c, p) ↦ (a ×ˢ b ×ˢ c).filter fun w ↦
    (w.1 = w.2.1 ↔ p 0 = p 1) ∧ (w.2.1 = w.2.2 ↔ p 1 = p 2) ∧ (w.1 = w.2.2 ↔ p 0 = p 2)).toFinset

/-- The specification written $\{k_0 (, k_3)\}$. -/
def k0k3 : List (Finset K) := [{.k0}, {.k0, .k3}]

/-- The specification written $\{(k_1 ,) k_2\}$. -/
def k1k2 : List (Finset K) := [{.k2}, {.k1, .k2}]

/-- Table 8, under Strong Case Containment. -/
def table8 : List Row :=
  [⟨[∅], [∅], [∅], .aaa⟩,
   ⟨[∅], [{.k1}], [{.k1}], .abb⟩,
   ⟨[∅], [∅], k1k2, .aab⟩,
   ⟨[∅], [{.k1}], [{.k1, .k2}], .abc⟩]

/-- Table 25, under Weak Case Containment. -/
def table25 : List Row :=
  [⟨[∅], [∅], [∅], .aaa⟩,
   ⟨[{.k0}], [{.k1}], [{.k1}], .abb⟩,
   ⟨[{.k0}], [∅], [∅], .abb⟩,
   ⟨[∅], [{.k1}], [{.k1}], .abb⟩,
   ⟨[∅], [∅], k1k2, .aab⟩,
   ⟨[∅], [{.k1}], [{.k1, .k2}], .abc⟩,
   ⟨[{.k0}], [∅], k1k2, .abc⟩,
   ⟨[{.k0}], [{.k1}], [{.k1, .k2}], .abc⟩]

/-- Table 11, under No Case Containment. -/
def table11 : List Row :=
  [⟨[∅], [∅], [∅], .aaa⟩,
   ⟨[∅], [{.k1, .k3}], [∅], .aba⟩,
   ⟨k0k3, [{.k1}], [{.k1}], .abb⟩,
   ⟨k0k3, [∅], [∅], .abb⟩,
   ⟨[∅], [{.k1}], [{.k1}], .abb⟩,
   ⟨[{.k3}], [{.k3}], k1k2, .aab⟩,
   ⟨[∅], [∅], k1k2, .aab⟩,
   ⟨[{.k3}], [{.k3}], [∅], .aab⟩,
   ⟨k0k3, [{.k1, .k3}], k1k2, .abc⟩,
   ⟨k0k3, [{.k1}], [{.k1, .k2}], .abc⟩,
   ⟨[{.k0, .k3}], [{.k3}], k1k2, .abc⟩,
   ⟨[{.k3}], [{.k1, .k3}], [{.k1}], .abc⟩,
   ⟨[∅], [{.k1}], [{.k1, .k2}], .abc⟩,
   ⟨[∅], [{.k1, .k3}], [{.k1}], .abc⟩,
   ⟨[{.k0, .k3}], [{.k3}], [∅], .abc⟩,
   ⟨[{.k3}], [{.k1, .k3}], [∅], .abc⟩,
   ⟨k0k3, [∅], k1k2, .abc⟩]

/-- The derivations of ABC under No Case Containment that Table 11 omits. -/
def table11Omitted : List Row :=
  [⟨[∅], [{.k1, .k3}], k1k2, .abc⟩,
   ⟨k0k3, [{.k1, .k3}], [{.k1}], .abc⟩,
   ⟨k0k3, [{.k1, .k3}], [∅], .abc⟩,
   ⟨[{.k3}], [{.k1, .k3}], k1k2, .abc⟩]

-- p. 883: "an exhaustive list of the derivations"
theorem derivations_scc : derivations scc = winners table8 := by decide +kernel

-- p. 895: "all the possible derivations"
theorem derivations_wcc : derivations wcc = winners table25 := by decide +kernel

/-- Table 11 omits four of the derivations under No Case Containment. -/
theorem derivations_ncc : derivations ncc = winners (table11 ++ table11Omitted) := by
  decide +kernel

/-! ### The argument against Strong Case Containment and its predictions -/

section Predictions

variable {Q E α : Type*} [Preorder Q] [DecidableLE (Finset K × Q)] [LinearOrder α]
  {v : RuleSet (SubsetRule (Finset K × Q) E)} {f : SubsetRule (Finset K × Q) E → α}
  {A B : SubsetRule (Finset K × Q) E} {q q' : Q}

-- (2): under SCC, crossed with any other dimensions, a rule winning an accusative over a different
-- nominative winner applies in no nominative, under any version of the Subset Principle
theorem scc_prediction (hA : v.selectBy f (scc nom, q) = some A)
    (hB : v.selectBy f (scc acc, q) = some B) (hne : A ≠ B) : ¬ Applies B (scc nom, q') := fun h ↦
  SubsetRule.not_le_of_selectBy_ne (by decide) hA hB hne (show B.features ≤ (scc nom, q') from h).1

-- (8) and (9): under WCC a rule winning a dative over a different accusative winner, rule B of an
-- AAB or rule C of an ABC, applies in no nominative or accusative
theorem wcc_prediction (hA : v.selectBy f (wcc acc, q) = some A)
    (hB : v.selectBy f (wcc dat, q) = some B) (hne : A ≠ B) {c : Fin 3} (hc : c ≠ dat) :
    ¬ Applies B (wcc c, q') := fun h ↦ by
  have hmeet : ∀ c : Fin 3, c ≠ dat → wcc c ⊓ wcc dat ≤ wcc acc := by decide
  exact SubsetRule.not_le_of_selectBy_ne (by decide) hA hB hne
    ((le_inf (show B.features ≤ (wcc c, q') from h).1
      (RuleSet.selectBy_applies hB : B.features ≤ (wcc dat, q)).1).trans (hmeet c hc))

end Predictions

/-! ### Latvian *pat-* ~ *paš-* (Table 20, rules (7))

The emphatic pronoun singles out nominative singular across both genders: *pat-s* / *pat-i* against
*paš-* everywhere else. Rules (7): *pat-* in k₀ singular contexts, *paš-* elsewhere. Each value of
number and of gender is its own feature, none contained in another (fn. 26); gender features are
carried by the cells but referenced by no rule. -/

/-- Number. -/
inductive LNum | sg | pl
  deriving DecidableEq, Fintype, Repr

/-- Gender. -/
inductive LGen | masc | fem
  deriving DecidableEq, Fintype, Repr

/-- The Latvian case of each cell of the chain. -/
def toLatvian : Fin 3 → Latvian.Case := ![.nom, .acc, .dat]

/-- The number a value of `LNum` is. -/
def LNum.toNumber : LNum → Number
  | .sg => .singular | .pl => .plural

/-- The gender tag of a value of `LGen`. -/
def LGen.toUD : LGen → UD.Gender
  | .masc => .Masc | .fem => .Fem

/-- The bundles of a Latvian cell: case, number and gender features. -/
abbrev LBundle := Finset K × Finset LNum × Finset LGen

/-- The Latvian decomposition, crossing a decomposition of case with number and gender. -/
def latvian (D : Paradigm 3 (Finset K)) : Fin 3 × LNum × LGen → LBundle :=
  Prod.map D (Prod.map singleton singleton)

/-- Rules (7): *pat-* in k₀ singular contexts; *paš-* elsewhere. -/
def latvianRules : RuleSet (SubsetRule LBundle String) :=
  [⟨⊥, "paš"⟩, ⟨({.k0}, {.sg}, ∅), "pat"⟩]

/-- The stem of Table 20 at a cell: the root of the form of *pats* in the cell's case, number and
gender. -/
def table20stem (c : Fin 3 × LNum × LGen) : Option String :=
  (Latvian.Pronouns.pats (toLatvian c.1) c.2.1.toNumber c.2.2.toUD).bind
    fun ms ↦ (ms.find? (·.kind = .root)).map (·.form)

-- (7), Table 20
theorem latvian_stems :
    ∀ c, latvianRules.realize card (latvian wcc c) = table20stem c := by
  decide

/-- No antihomophonous rule set derives Table 20 under Strong Case Containment, whatever the score:
*paš-* wins the accusative singular over *pat-* and still appears in the nominative plural,
against prediction (2). -/
theorem latvian_not_scc {α : Type*} [LinearOrder α] {v : RuleSet (SubsetRule LBundle String)}
    {f : SubsetRule LBundle String → α} (hv : v.Antihomophonous) :
    ¬ ∀ c, v.realize f (latvian scc c) = table20stem c := fun h ↦ by
  obtain ⟨A, hA, heA⟩ := Option.map_eq_some_iff.1
    ((h (nom, .sg, .masc)).trans (by decide : _ = some "pat"))
  obtain ⟨B, hB, heB⟩ := Option.map_eq_some_iff.1
    ((h (acc, .sg, .masc)).trans (by decide : _ = some "paš"))
  obtain ⟨B', hB', heB'⟩ := Option.map_eq_some_iff.1
    ((h (nom, .pl, .masc)).trans (by decide : _ = some "paš"))
  obtain rfl := hv (RuleSet.selectBy_mem hB') (RuleSet.selectBy_mem hB) (heB'.trans heB.symm)
  have hne : A ≠ B' := fun e ↦ absurd (heA.symm.trans ((congrArg exponent e).trans heB))
    (by decide)
  rw [show latvian scc (nom, .sg, .masc) = (scc nom, ({.sg}, {.masc})) from rfl] at hA
  rw [show latvian scc (acc, .sg, .masc) = (scc acc, ({.sg}, {.masc})) from rfl] at hB
  rw [show latvian scc (nom, .pl, .masc) = (scc nom, ({.pl}, {.masc})) from rfl] at hB'
  exact scc_prediction hA hB hne (RuleSet.selectBy_applies hB')

-- (4), p. 889: the disjunctive rule, written as two homophonous rules, derives Table 20 under SCC
theorem latvian_scc_of_disjunctive :
    ∀ c, RuleSet.realize
      [(⟨⊥, "pat"⟩ : SubsetRule LBundle String), ⟨({.k1}, ∅, ∅), "paš"⟩, ⟨(∅, {.pl}, ∅), "paš"⟩]
      card (latvian scc c) = table20stem c := by
  decide

-- the pattern "cuts across genders": neither rule references gender
theorem latvian_gender_blind (c n) :
    latvianRules.realize card (latvian wcc (c, n, .masc)) =
      latvianRules.realize card (latvian wcc (c, n, .fem)) := by
  revert c n; decide

-- fn. 26: dropping the singular overgenerates *pat-* into the nominative plural
theorem latvian_pat_needs_singular :
    RuleSet.realize [(⟨⊥, "paš"⟩ : SubsetRule LBundle String), ⟨({.k0}, ∅, ∅), "pat"⟩] card
      (latvian wcc (nom, .pl, .masc)) = some "pat" := by
  decide

-- fn. 8: a rule for the masculine beside one for k₀ singular has an incomparable specification, so
-- under the inclusion of contexts of (i) either may apply in the nominative singular masculine;
-- counting decides, and what it decides is one of them
theorem counting_decides_incomparable :
    let v : RuleSet (SubsetRule LBundle ℕ) := [⟨(∅, ∅, {.masc}), 0⟩, ⟨({.k0}, {.sg}, ∅), 1⟩]
    let c := latvian wcc (nom, .sg, .masc)
    v.Realizes applySet c 0 ∧ v.Realizes applySet c 1 ∧ v.realize card c = some 1 := by
  intro v c
  have h : v.realize card c = some 1 := by decide
  refine ⟨⟨⟨(∅, ∅, {.masc}), 0⟩, ⟨⟨by simp [v], by decide⟩, fun s hs hle ↦ ?_⟩, rfl⟩,
    SubsetRule.realize_realizes grade_strictMono h, h⟩
  simp only [v, List.mem_cons, List.not_mem_nil, or_false] at hs
  obtain ⟨rfl | rfl, -⟩ := hs
  · exact le_rfl
  · exact absurd (SubsetRule.applySet_subset_iff.1 hle) (by decide)

/-! ### Yiddish 1st person (fn. 25): why k₁ exists

*ix* (NOM.SG), *m-* (elsewhere: *m-ir, m-ix*), *undz* (ACC.PL and DAT.PL). The *undz* rule must
reference k₁: specified for plural alone it would also capture the nominative plural *m-ir*. This
ABB row with B more specific than the elsewhere is the evidence that WCC's k₁ is not eliminable. -/

/-- The Yiddish decomposition, crossing WCC with number. -/
def yiddish : Fin 3 × LNum → Finset K × Finset LNum :=
  Prod.map wcc singleton

/-- The three stem rules: *ix* a non-elsewhere nominative-singular stem, *undz* the k₁-plural stem,
*m-* the elsewhere. -/
def yiddishRules : RuleSet (SubsetRule (Finset K × Finset LNum) String) :=
  [⟨⊥, "m"⟩, ⟨({.k0}, {.sg}), "ix"⟩, ⟨({.k1}, {.pl}), "undz"⟩]

/-- The fn. 25 paradigm's stem distribution: *ix* / *m-ix* / *m-ir* in the singular, *m-ir* /
*undz* / *undz* in the plural. -/
def yiddishStem (c : Fin 3 × LNum) : String :=
  if c.1 = nom ∧ c.2 = .sg then "ix"
  else if c.1 ≠ nom ∧ c.2 = .pl then "undz"
  else "m"

-- fn. 25
theorem yiddish_stems :
    ∀ c, yiddishRules.realize card (yiddish c) = some (yiddishStem c) := by
  decide

-- fn. 25: specified for plural alone, *undz* wrongly beats *m-* in the nominative plural
theorem undz_needs_k1 :
    RuleSet.realize [(⟨⊥, "m"⟩ : SubsetRule (Finset K × Finset LNum) String),
        ⟨({.k0}, {.sg}), "ix"⟩, ⟨(∅, {.pl}), "undz"⟩] card (yiddish (nom, .pl)) = some "undz" := by
  decide

/-! ### The natural classes -/

/-- The natural classes of a decomposition. -/
def naturalClasses (D : Paradigm 3 (Finset K)) : Finset (Finset (Fin 3)) :=
  Finset.univ.filter (IsNaturalClass D)

theorem mem_naturalClasses {D : Paradigm 3 (Finset K)} {S : Finset (Fin 3)} :
    S ∈ naturalClasses D ↔ IsNaturalClass D S := by
  simp [naturalClasses]

/-- A closure system on the three cases: a family with all of them, closed under intersection. -/
def IsClosureSystem (F : Finset (Finset (Fin 3))) : Prop :=
  Finset.univ ∈ F ∧ ∀ S ∈ F, ∀ T ∈ F, S ∩ T ∈ F

instance : DecidablePred IsClosureSystem := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem isClosureSystem_naturalClasses (D : Paradigm 3 (Finset K)) :
    IsClosureSystem (naturalClasses D) :=
  ⟨mem_naturalClasses.2 (by simp [IsNaturalClass]), fun _ hS _ hT ↦ mem_naturalClasses.2 (by
    simpa [IsNaturalClass] using (mem_naturalClasses.1 hS).inter (mem_naturalClasses.1 hT))⟩

-- Tables 1, 24 and 2 by what their rules can pick out
theorem naturalClasses_values :
    naturalClasses scc = {∅, {dat}, {acc, dat}, Finset.univ} ∧
      naturalClasses wcc = {∅, {nom}, {dat}, {acc, dat}, Finset.univ} ∧
        naturalClasses ncc = {∅, {nom}, {acc}, {dat}, {nom, acc}, {acc, dat}, Finset.univ} := by
  decide +kernel

/-- The "midway" of p. 895 is literal: the natural classes of the three decompositions are
nested. -/
theorem naturalClasses_ssubset :
    naturalClasses scc ⊂ naturalClasses wcc ∧ naturalClasses wcc ⊂ naturalClasses ncc := by
  decide +kernel

private theorem subset_or_subset_of_not_mem :
    ∀ F : Finset (Finset (Fin 3)), IsClosureSystem F → {acc} ∉ F → {nom, dat} ∉ F →
      F ⊆ naturalClasses wcc ∨ F ⊆ naturalClasses (wcc ∘ Fin.rev) := by
  decide +kernel

/-- **Weak Case Containment is the most expressive decomposition that excludes ABA.** The natural
classes of any decomposition excluding ABA lie inside those of Weak Case Containment, or of its
mirror image, the accusative inside the nominative, which it attains. -/
theorem naturalClasses_subset_of_forall_isContiguous [Nontrivial F] {D : Paradigm 3 (Finset K)}
    (h : ∀ v : RuleSet (SubsetRule (Finset K) F), v.Antihomophonous →
      IsContiguous fun c ↦ v.realize card (D c)) :
    naturalClasses D ⊆ naturalClasses wcc ∨ naturalClasses D ⊆ naturalClasses (wcc ∘ Fin.rev) := by
  obtain ⟨h₁, h₂⟩ := forall_isContiguous_iff_not_isNaturalClass.1 h
  exact subset_or_subset_of_not_mem _ (isClosureSystem_naturalClasses D)
    (fun hm ↦ h₁ (mem_naturalClasses.1 hm)) fun hm ↦ h₂ (mem_naturalClasses.1 hm)

end ChristopoulosZompi2023
