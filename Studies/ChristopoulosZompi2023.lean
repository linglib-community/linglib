module

public import Linglib.Morphology.Exponence.SubsetRule
public import Linglib.Fragments.Latvian.Pronouns
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.List.Sections
public import Mathlib.Tactic.DeriveFintype

/-!
# Christopoulos and Zompì (2023): Weak Case Containment

Three featural decompositions of the nominative, accusative and dative are compared under the
Subset Principle. Strong Case Containment nests them in a chain. It excludes ABA, but
[a rule winning an accusative over another applies in no nominative](##scc_prediction), so it
[cannot derive](##latvian_not_scc) the Latvian stems that Weak Case Containment
[derives](##latvian_stems). No Case Containment makes them incomparable and
[derives ABA](##ncc_aba_generable). Excluding ABA while stating a nominative stem, a rule for
accusative and dative, and a rule for the dative alone is
[equivalent to the shape of Weak Case Containment](##isWeak_iff): the accusative properly inside the
dative, nominative and accusative incomparable, and nothing shared by nominative and dative outside
the accusative.

## Implementation notes

* Clause (1b) presupposes a unique rule with the greatest number of features. `realize` breaks ties
  by the order of the rule set; `derivations`, which enumerates the tables, excludes them.
* That the decomposition is forced is this file's reading: the paper argues that Weak Case
  Containment suffices. Rule sets are antihomophonous where fn. 9 says "barring accidental
  homophony"; a homophonous pair is the disjunctive rule (4), with which Strong Case Containment
  [does derive the stems](##latvian_scc_of_disjunctive).
* The tables' parenthesized features stand for two rules each, so a row is a list of alternatives.

## Errata

* Table 11, said on p. 885 to list "all the possible derivations", and the "nine ways of deriving
  ABC" of pp. 885-887, [omit four rows](##derivations_ncc), all with rule B for $\{k_1, k_3\}$;
  there are thirteen. The argument is unaffected, the omission understating the overgeneration.
* The reason p. 895 gives for excluding ABA under Weak Case Containment, the accusative's
  containment in the dative, excludes only a rule for the accusative alone. A rule for nominative
  and dative together is excluded because they share no feature, a separate condition
  (`acc_ssubset_dat_derives_aba`).

## TODO

* The surface containment predictions of Table 37, from hypothesis (10) (§6.2).
* The markedness features of [mcfadden-2018], rejected on Latvian and Tocharian (§3.3).

## References

* [bobaljik-2012]
* [caha-2009]
* [christopoulos-zompi-2023]
* [halle-1997]
* [mcfadden-2018]
* [smith-moskal-xu-kang-bobaljik-2019]
-/

@[expose] public section

namespace ChristopoulosZompi2023

open Morphology.Exponence
open SubsetRule (card)

/-- The privative features: k₀–k₃ across the three Case decompositions, plus number (s₀ singular,
p₀ plural) and gender features for the empirical paradigms, no property contained in its
category-mates (fn. 26). -/
inductive K | k0 | k1 | k2 | k3 | s0 | p0 | m0 | f0
  deriving DecidableEq, Fintype, Repr

/-- The case triplet, in the *ABA order NOM ≺ ACC ≺ DAT. -/
inductive Case3 | nom | acc | dat
  deriving DecidableEq, Fintype, Repr

/-- **Strong Case Containment** (Table 1): a chain ∅ ⊂ {k₁} ⊂ {k₁,k₂}. -/
def scc : Case3 → Finset K
  | .nom => ∅ | .acc => {.k1} | .dat => {.k1, .k2}

/-- **No Case Containment** (Table 2): pairwise incomparable feature sets; k₃ is the NOM/ACC feature
absent from DAT. -/
def ncc : Case3 → Finset K
  | .nom => {.k0, .k3} | .acc => {.k1, .k3} | .dat => {.k1, .k2}

/-- **Weak Case Containment** (Table 24): ACC ⊂ DAT as in SCC, but NOM carries its own k₀,
incomparable to ACC, and there is no k₃. -/
def wcc : Case3 → Finset K
  | .nom => {.k0} | .acc => {.k1} | .dat => {.k1, .k2}

variable {F : Type*}

/-! ### *ABA -/

/-- A decomposition excludes ABA when no antihomophonous rule set realizes one exponent at the
nominative and the dative and another at the accusative. -/
def ExcludesABA (F : Type*) (D : Case3 → Finset K) : Prop :=
  ∀ v : RuleSet (SubsetRule (Finset K) F), v.Antihomophonous →
    v.realize card (D .nom) = v.realize card (D .dat) →
      v.realize card (D .acc) = v.realize card (D .nom)

theorem excludesABA_iff [Nontrivial F] {D : Case3 → Finset K} :
    ExcludesABA F D ↔ D .nom ∩ D .dat ⊆ D .acc ∧ (D .acc ⊆ D .nom ∨ D .acc ⊆ D .dat) :=
  SubsetRule.forall_realize_eq_iff fun _ _ ↦ SubsetRule.card_lt_card

theorem excludesABA_scc : ExcludesABA F scc :=
  fun _ hv h ↦ SubsetRule.realize_eq_of_inf_le_of_le hv (by decide) (by decide) h

theorem excludesABA_wcc : ExcludesABA F wcc :=
  fun _ hv h ↦ SubsetRule.realize_eq_of_inf_le_of_le hv (by decide) (by decide) h

/-- Exponent labels for the derivation tables. -/
inductive Ex | A | B | C
  deriving DecidableEq, Repr

/-- A PATTERN-column value: the exponents surfacing at NOM, ACC, DAT. -/
def surface (n a d : Ex) : Case3 → Ex
  | .nom => n | .acc => a | .dat => d

-- Table 11, row 2: an elsewhere rule beside a rule for the accusative-specific set {k₁, k₃}
theorem ncc_aba_generable :
    ∀ c, RuleSet.realize [(⟨∅, Ex.A⟩ : SubsetRule (Finset K) Ex), ⟨{.k1, .k3}, .B⟩]
      card (ncc c) = some (surface .A .B .A c) := by
  decide

-- p. 895: a decomposition with ACC ⊂ DAT whose NOM and DAT share k₃ derives ABA by a rule for k₃
theorem acc_ssubset_dat_derives_aba :
    ({.k1} : Finset K) ⊂ {.k1, .k2, .k3} ∧
      ∀ c, RuleSet.realize [(⟨{.k3}, Ex.A⟩ : SubsetRule (Finset K) Ex), ⟨∅, .B⟩] card
        ((fun | .nom => {.k0, .k3} | .acc => {.k1} | .dat => {.k1, .k2, .k3} :
          Case3 → Finset K) c) = some (surface .A .B .A c) := by
  decide

/-! ### The derivation tables -/

/-- A row of a derivation table: the specifications of rules A, B and C, each listing the
alternatives the table writes with a parenthesized feature, and the PATTERN column. -/
abbrev Row := List (List (Finset K)) × (Case3 → Ex)

/-- The rule sets a row stands for. -/
def Row.ruleSets (r : Row) : List (RuleSet (SubsetRule (Finset K) Ex)) :=
  r.1.sections.map (List.zipWith SubsetRule.mk · [.A, .B, .C])

/-- The specification written $\{k_0 (, k_3)\}$. -/
def k0k3 : List (Finset K) := [{.k0}, {.k0, .k3}]

/-- The specification written $\{(k_1 ,) k_2\}$. -/
def k1k2 : List (Finset K) := [{.k2}, {.k1, .k2}]

/-- Table 8, under Strong Case Containment. -/
def table8 : List Row :=
  [([[∅]], surface .A .A .A),
   ([[∅], [{.k1}]], surface .A .B .B),
   ([[∅], k1k2], surface .A .A .B),
   ([[∅], [{.k1}], [{.k1, .k2}]], surface .A .B .C)]

/-- Table 25, under Weak Case Containment. -/
def table25 : List Row :=
  [([[∅]], surface .A .A .A),
   ([[{.k0}], [{.k1}]], surface .A .B .B),
   ([[{.k0}], [∅]], surface .A .B .B),
   ([[∅], [{.k1}]], surface .A .B .B),
   ([[∅], k1k2], surface .A .A .B),
   ([[∅], [{.k1}], [{.k1, .k2}]], surface .A .B .C),
   ([[{.k0}], [∅], k1k2], surface .A .B .C),
   ([[{.k0}], [{.k1}], [{.k1, .k2}]], surface .A .B .C)]

/-- Table 11, under No Case Containment. -/
def table11 : List Row :=
  [([[∅]], surface .A .A .A),
   ([[∅], [{.k1, .k3}]], surface .A .B .A),
   ([k0k3, [{.k1}]], surface .A .B .B),
   ([k0k3, [∅]], surface .A .B .B),
   ([[∅], [{.k1}]], surface .A .B .B),
   ([[{.k3}], k1k2], surface .A .A .B),
   ([[∅], k1k2], surface .A .A .B),
   ([[{.k3}], [∅]], surface .A .A .B),
   ([k0k3, [{.k1, .k3}], k1k2], surface .A .B .C),
   ([k0k3, [{.k1}], [{.k1, .k2}]], surface .A .B .C),
   ([[{.k0, .k3}], [{.k3}], k1k2], surface .A .B .C),
   ([[{.k3}], [{.k1, .k3}], [{.k1}]], surface .A .B .C),
   ([[∅], [{.k1}], [{.k1, .k2}]], surface .A .B .C),
   ([[∅], [{.k1, .k3}], [{.k1}]], surface .A .B .C),
   ([[{.k0, .k3}], [{.k3}], [∅]], surface .A .B .C),
   ([[{.k3}], [{.k1, .k3}], [∅]], surface .A .B .C),
   ([k0k3, [∅], k1k2], surface .A .B .C)]

/-- The derivations of ABC under No Case Containment that Table 11 omits. -/
def table11Omitted : List Row :=
  [([[∅], [{.k1, .k3}], k1k2], surface .A .B .C),
   ([k0k3, [{.k1, .k3}], [{.k1}]], surface .A .B .C),
   ([k0k3, [{.k1, .k3}], [∅]], surface .A .B .C),
   ([[{.k3}], [{.k1, .k3}], k1k2], surface .A .B .C)]

/-- Every rule set of every row realizes the row's PATTERN column. -/
abbrev Generates (D : Case3 → Finset K) (t : List Row) : Prop :=
  ∀ r ∈ t, ∀ v ∈ r.ruleSets, ∀ c, v.realize card (D c) = some (r.2 c)

theorem generates_table8 : Generates scc table8 := by decide

theorem generates_table25 : Generates wcc table25 := by decide

theorem generates_table11 : Generates ncc (table11 ++ table11Omitted) := by decide

/-- Among the specifications `i`, the rule for `r` wins at `c`: it applies, and has more features
than any other that does, clause (1b). -/
def Wins (i : List (Finset K)) (c r : Finset K) : Prop :=
  r ⊆ c ∧ ∀ s ∈ i, s ⊆ c → s ≠ r → s.card < r.card

instance (i : List (Finset K)) (c r : Finset K) : Decidable (Wins i c r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The specifications winning at the nominative, accusative and dative. -/
abbrev Winners := Finset K × Finset K × Finset K

/-- Three rules derive a pattern when each wins its case among the three, ties excluded. -/
abbrev IsDerivation (D : Case3 → Finset K) (w : Winners) : Prop :=
  Wins [w.1, w.2.1, w.2.2] (D .nom) w.1 ∧ Wins [w.1, w.2.1, w.2.2] (D .acc) w.2.1 ∧
    Wins [w.1, w.2.1, w.2.2] (D .dat) w.2.2

/-- The derivations under a decomposition, each given by its winners. -/
def derivations (D : Case3 → Finset K) : Finset Winners :=
  ((D .nom).powerset ×ˢ (D .acc).powerset ×ˢ (D .dat).powerset).filter fun w ↦ IsDerivation D w

/-- The position of an exponent label among a row's rules. -/
def Ex.index : Ex → ℕ
  | .A => 0 | .B => 1 | .C => 2

/-- The winners the rows of a table claim, reading each case's rule off the PATTERN column. -/
def winners (t : List Row) : Finset Winners :=
  (t.flatMap fun r ↦ r.1.sections.map fun l ↦
    (l.getD (r.2 .nom).index ∅, l.getD (r.2 .acc).index ∅, l.getD (r.2 .dat).index ∅)).toFinset

-- p. 883: "an exhaustive list of the derivations"
theorem derivations_scc : derivations scc = winners table8 := by decide +kernel

-- p. 895: "all the possible derivations"
theorem derivations_wcc : derivations wcc = winners table25 := by decide +kernel

/-- Table 11 omits four of the derivations under No Case Containment. -/
theorem derivations_ncc : derivations ncc = winners (table11 ++ table11Omitted) := by
  decide +kernel

/-! ### The argument against Strong Case Containment -/

/-- **Prediction (2).** Under Strong Case Containment, crossed with features `T o` of other
dimensions, a rule winning an accusative over a different nominative winner applies in no
nominative, under any version of the Subset Principle. -/
theorem scc_prediction {O E α : Type*} [LinearOrder α] {T : O → Finset K} (hT : ∀ o, K.k1 ∉ T o)
    {v : RuleSet (SubsetRule (Finset K) E)} {f : SubsetRule (Finset K) E → α}
    {A B : SubsetRule (Finset K) E} {o o' : O}
    (hA : v.selectBy f (scc .nom ∪ T o) = some A) (hB : v.selectBy f (scc .acc ∪ T o) = some B)
    (hne : A ≠ B) : ¬ Applies B (scc .nom ∪ T o') := fun h ↦
  hT o' <| by
    simpa [scc] using h <| SubsetRule.mem_features_of_selectBy_ne
      (Finset.union_subset_union_left (by decide)) (by simp [scc]) hA hB hne

-- (8) and (9): a rule winning a dative over a different accusative winner, rule B of an AAB or rule
-- C of an ABC, applies in no nominative or accusative
theorem wcc_prediction {O E α : Type*} [LinearOrder α] {T : O → Finset K} (hT : ∀ o, K.k2 ∉ T o)
    {v : RuleSet (SubsetRule (Finset K) E)} {f : SubsetRule (Finset K) E → α}
    {A C : SubsetRule (Finset K) E} {o o' : O}
    (hA : v.selectBy f (wcc .acc ∪ T o) = some A) (hC : v.selectBy f (wcc .dat ∪ T o) = some C)
    (hne : A ≠ C) {c : Case3} (hc : c ≠ .dat) : ¬ Applies C (wcc c ∪ T o') := fun h ↦ by
  have hk : K.k2 ∈ wcc c ∪ T o' := h <| SubsetRule.mem_features_of_selectBy_ne
    (Finset.union_subset_union_left (by decide))
    (by simp [wcc, Finset.insert_union, Finset.insert_comm]) hA hC hne
  cases c <;> simp_all [wcc]

/-! ### Latvian *pat-* ~ *paš-* (Table 20, rules (7))

The emphatic pronoun singles out nominative singular across both genders: *pat-s* / *pat-i* against
*paš-* everywhere else. Rules (7): *pat-* in k₀ singular contexts, *paš-* elsewhere. Number
decomposes with neither value contained in the other (fn. 26); gender features are carried by the
cells but referenced by no rule. -/

/-- Number. -/
inductive LNum | sg | pl
  deriving DecidableEq, Fintype, Repr

/-- Gender. -/
inductive LGen | masc | fem
  deriving DecidableEq, Fintype, Repr

/-- The Latvian case a member of the triplet is. -/
def Case3.toLatvian : Case3 → Latvian.Case
  | .nom => .nom | .acc => .acc | .dat => .dat

/-- The number a value of `LNum` is. -/
def LNum.toNumber : LNum → Number
  | .sg => .singular | .pl => .plural

/-- The gender tag of a value of `LGen`. -/
def LGen.toUD : LGen → UD.Gender
  | .masc => .Masc | .fem => .Fem

/-- The features of a number. -/
def LNum.features : LNum → Finset K
  | .sg => {.s0} | .pl => {.p0}

/-- The features of a gender. -/
def LGen.features : LGen → Finset K
  | .masc => {.m0} | .fem => {.f0}

/-- A Latvian cell: case, number, gender. -/
structure LCell where
  case : Case3
  num : LNum
  gen : LGen
  deriving DecidableEq, Fintype, Repr

/-- The Latvian decomposition over a decomposition of case. -/
def latvian (D : Case3 → Finset K) (c : LCell) : Finset K :=
  D c.case ∪ (c.num.features ∪ c.gen.features)

/-- Rules (7): *pat-* in k₀ singular contexts; *paš-* elsewhere. -/
def latvianRules : RuleSet (SubsetRule (Finset K) String) :=
  [⟨{.k0, .s0}, "pat"⟩, ⟨∅, "paš"⟩]

/-- The stem of Table 20 at a cell: the root of the form of *pats* in the cell's case, number and
gender. -/
def table20stem (c : LCell) : Option String :=
  (Latvian.Pronouns.pats c.case.toLatvian c.num.toNumber c.gen.toUD).bind
    fun ms ↦ (ms.find? (·.kind = .root)).map (·.form)

/-- Rules (7) generate Table 20's stem distribution under Weak Case Containment. -/
theorem latvian_stems :
    ∀ c, latvianRules.realize card (latvian wcc c) = table20stem c := by
  decide

/-- No antihomophonous rule set derives Table 20 under Strong Case Containment, whatever the score:
*paš-* wins the accusative singular over *pat-* and still appears in the nominative plural,
against prediction (2). -/
theorem latvian_not_scc {α : Type*} [LinearOrder α] {v : RuleSet (SubsetRule (Finset K) String)}
    {f : SubsetRule (Finset K) String → α} (hv : v.Antihomophonous) :
    ¬ ∀ c, v.realize f (latvian scc c) = table20stem c := fun h ↦ by
  obtain ⟨A, hA, heA⟩ := Option.map_eq_some_iff.1
    ((h ⟨.nom, .sg, .masc⟩).trans (by decide : _ = some "pat"))
  obtain ⟨B, hB, heB⟩ := Option.map_eq_some_iff.1
    ((h ⟨.acc, .sg, .masc⟩).trans (by decide : _ = some "paš"))
  obtain ⟨B', hB', heB'⟩ := Option.map_eq_some_iff.1
    ((h ⟨.nom, .pl, .masc⟩).trans (by decide : _ = some "paš"))
  obtain rfl := hv (RuleSet.selectBy_mem hB') (RuleSet.selectBy_mem hB) (heB'.trans heB.symm)
  have hne : A ≠ B' := fun e ↦ absurd (heA.symm.trans ((congrArg exponent e).trans heB))
    (by decide)
  exact scc_prediction (T := fun p : LNum × LGen ↦ p.1.features ∪ p.2.features)
    (by rintro ⟨_ | _, _ | _⟩ <;> decide) (o := (.sg, .masc)) (o' := (.pl, .masc)) hA hB hne
    (RuleSet.selectBy_applies hB')

-- (4), p. 889: the disjunctive rule, written as two homophonous rules, derives Table 20 under SCC
theorem latvian_scc_of_disjunctive :
    ∀ c, RuleSet.realize
      [(⟨{.k1}, "paš"⟩ : SubsetRule (Finset K) String), ⟨{.p0}, "paš"⟩, ⟨∅, "pat"⟩]
      card (latvian scc c) = table20stem c := by
  decide

-- the pattern "cuts across genders": neither rule references gender
theorem latvian_gender_blind (c n) :
    latvianRules.realize card (latvian wcc ⟨c, n, .masc⟩) =
      latvianRules.realize card (latvian wcc ⟨c, n, .fem⟩) := by
  revert c n; decide

-- fn. 26: dropping s₀ overgenerates *pat-* into the nominative plural
theorem latvian_pat_needs_singular :
    RuleSet.realize [(⟨{.k0}, "pat"⟩ : SubsetRule (Finset K) String), ⟨∅, "paš"⟩] card
      (latvian wcc ⟨.nom, .pl, .masc⟩) = some "pat" := by
  decide

/-! ### Yiddish 1st person (fn. 25): why k₁ exists

*ix* (NOM.SG), *m-* (elsewhere: *m-ir, m-ix*), *undz* (ACC.PL and DAT.PL). The *undz* rule must
reference k₁: specified for plural alone it would also capture the nominative plural *m-ir*. This
ABB row with B more specific than the elsewhere is the evidence that WCC's k₁ is not eliminable. -/

/-- A Yiddish cell: case and number. -/
structure YCell where
  case : Case3
  num : LNum
  deriving DecidableEq, Fintype, Repr

/-- The Yiddish decomposition: WCC for case, s₀/p₀ for number. -/
def yiddish (c : YCell) : Finset K :=
  wcc c.case ∪ c.num.features

/-- The three stem rules: *ix* a non-elsewhere nominative-singular stem, *undz* the k₁-plural stem,
*m-* the elsewhere. -/
def yiddishRules : RuleSet (SubsetRule (Finset K) String) :=
  [⟨{.k0, .s0}, "ix"⟩, ⟨{.k1, .p0}, "undz"⟩, ⟨∅, "m"⟩]

/-- The fn. 25 paradigm's stem distribution: *ix* / *m-ix* / *m-ir* in the singular, *m-ir* /
*undz* / *undz* in the plural. -/
def yiddishStem (c : YCell) : String :=
  if c.case = .nom ∧ c.num = .sg then "ix"
  else if c.case ≠ .nom ∧ c.num = .pl then "undz"
  else "m"

-- fn. 25
theorem yiddish_stems :
    ∀ c, yiddishRules.realize card (yiddish c) = some (yiddishStem c) := by
  decide

-- fn. 25: specified for plural alone, *undz* wrongly beats *m-* in the nominative plural
theorem undz_needs_k1 :
    RuleSet.realize [(⟨{.k0, .s0}, "ix"⟩ : SubsetRule (Finset K) String),
        ⟨{.p0}, "undz"⟩, ⟨∅, "m"⟩] card (yiddish ⟨.nom, .pl⟩) = some "undz" := by
  decide

/-! ### The shape the argument forces -/

/-- The cases `S` are a natural class of a decomposition when some specification applies in exactly
those cases. -/
def IsNaturalClass (D : Case3 → Finset K) (S : Set Case3) : Prop :=
  ∃ s : Finset K, ∀ c, s ⊆ D c ↔ c ∈ S

/-- The shape of Weak Case Containment: the accusative properly inside the dative, nominative and
accusative incomparable (p. 894), and nothing shared by nominative and dative outside the
accusative. -/
def IsWeak (D : Case3 → Finset K) : Prop :=
  D .acc ⊂ D .dat ∧ D .nom ∩ D .dat ⊆ D .acc ∧ ¬ D .nom ⊆ D .acc ∧ ¬ D .acc ⊆ D .nom

instance : DecidablePred IsWeak := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- **The demands fix the shape.** A decomposition excludes ABA and makes natural classes of the
nominative (a non-elsewhere nominative stem, p. 881), of accusative and dative (the *undz* rule of
fn. 25), and of the dative (rule C of an ABC, p. 901) exactly when it has the shape of Weak Case
Containment. Table 24 has that shape; Tables 1 and 2 do not. -/
theorem isWeak_iff [Nontrivial F] {D : Case3 → Finset K} :
    IsWeak D ↔ ExcludesABA F D ∧ IsNaturalClass D {.nom} ∧ IsNaturalClass D {.acc, .dat} ∧
      IsNaturalClass D {.dat} := by
  rw [excludesABA_iff]
  constructor
  · rintro ⟨hs, hi, hn, ha⟩
    have hnd : ¬ D .nom ⊆ D .dat := fun h ↦ hn fun _ hk ↦ hi (Finset.mem_inter.2 ⟨hk, h hk⟩)
    have hdn : ¬ D .dat ⊆ D .nom := fun h ↦ ha (hs.subset.trans h)
    refine ⟨⟨hi, .inr hs.subset⟩, ⟨D .nom, ?_⟩, ⟨D .acc, ?_⟩, ⟨D .dat, ?_⟩⟩ <;>
      rintro (_ | _ | _) <;> simp [hn, ha, hnd, hdn, hs.subset, hs.not_subset]
  · rintro ⟨⟨hi, hy⟩, ⟨s₁, h₁⟩, ⟨s₂, h₂⟩, ⟨s₃, h₃⟩⟩
    have hn₁ := (h₁ .nom).2 rfl
    have hn₂ := (h₂ .acc).2 (.inl rfl)
    have hd₃ := (h₃ .dat).2 rfl
    have ha₁ : ¬ s₁ ⊆ D .acc := fun h ↦ by simpa using (h₁ .acc).1 h
    have hn₂' : ¬ s₂ ⊆ D .nom := fun h ↦ by simpa using (h₂ .nom).1 h
    have ha₃ : ¬ s₃ ⊆ D .acc := fun h ↦ by simpa using (h₃ .acc).1 h
    have hsub : D .acc ⊆ D .dat := hy.resolve_left fun h ↦ hn₂' (hn₂.trans h)
    exact ⟨⟨hsub, fun h ↦ ha₃ (hd₃.trans h)⟩, hi, fun h ↦ ha₁ (hn₁.trans h),
      fun h ↦ hn₂' (hn₂.trans h)⟩

theorem isWeak_wcc : IsWeak wcc := by decide

theorem not_isWeak_scc : ¬ IsWeak scc := by decide

theorem not_isWeak_ncc : ¬ IsWeak ncc := by decide

end ChristopoulosZompi2023
