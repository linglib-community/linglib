module

public import Linglib.Morphology.Exponence.Decomposition
public import Linglib.Fragments.Latvian.Pronouns
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sigma

/-!
# Christopoulos & Zompì 2023: Weak Case Containment
[christopoulos-zompi-2023]

Three rival featural decompositions of NOM ≺ ACC ≺ DAT, run against two
discriminating predictions under Subset-Principle competition. **Strong Case
Containment** (Table 1; [caha-2009], [smith-moskal-xu-kang-bobaljik-2019])
nests the three cases in a chain; **No Case Containment** (Table 2) makes them
pairwise incomparable; the paper's **Weak Case Containment** (Table 24) keeps
ACC ⊂ DAT but gives NOM its own feature, incomparable to ACC. The predictions:

* ***ABA** ([bobaljik-2012]'s coinage): SCC and WCC exclude it structurally
  (`noABA`, discharged for both by their shared order-theoretic profile:
  ACC-appliers persist to DAT, and NOM∩DAT-appliers reach ACC); NCC derives it
  (`ncc_aba_generable`, via a rule referencing its accusative-specific feature
  set {k₁, k₃}).
* **Non-Elsewhere Nominative Stems**: SCC forces any NOM-applying rule to be
  the featureless elsewhere (`scc_nom_forces_empty`) — the Doric Greek *h-*
  stem (Table 3), Latvian *pat-*, and English feminine *sh-* against elsewhere
  *h-* (Table 14) refute this; WCC's k₀ writes them directly (Table 25 rows
  2–3; the Latvian rules (7) below). [mcfadden-2018]'s markedness rescue of
  SCC is refuted on Latvian/Tocharian Gender in the paper's §3.3 (not
  formalized here).

Table 25's eight derivation rows are reproduced by `decide`; the Latvian
emphatic pronoun (Table 20, rules (7)) and the Yiddish 1st person (fn. 25) are
run as full stem-distribution checks, including the paper's two minimality
points: *pat-* needs the singular feature alongside k₀ (fn. 26), and *undz*
needs k₁ (fn. 25). The Latvian stems are read off the segmented forms of
`Latvian.Pronouns.pats`.

## Main results

* `noABA_scc` / `noABA_wcc` — the generic `Decomposition.noABA` (*ABA excluded
  under any decomposition nesting the middle cell) discharged for SCC and WCC by
  `decide` on the order-theoretic hypotheses
* `ncc_aba_generable` — the two-rule NCC vocabulary generating A B A
* `scc_nom_forces_empty` — SCC has no non-elsewhere nominative rules
* `table25_generates` — each `table25` row's inventory generates its PATTERN
  column
* `latvian_stems` / `latvian_gender_blind` / `latvian_pat_needs_singular` —
  Table 20 under rules (7)
* `yiddish_stems` / `undz_needs_k1` — the fn. 25 paradigm and its k₁ argument

## References

* [bobaljik-2012]
* [caha-2009]
* [christopoulos-zompi-2023]
* [mcfadden-2018]
* [smith-moskal-xu-kang-bobaljik-2019]
-/

@[expose] public section

namespace ChristopoulosZompi2023

open Morphology Morphology.Exponence Morphology.Decomposition

/-- The privative features: k₀–k₃ across the three Case decompositions
(Tables 1, 2, 24), plus number (s₀ singular, p₀ plural) and gender features
for the empirical paradigms — no property contained in its category-mates
(fn. 26). -/
inductive K | k0 | k1 | k2 | k3 | s0 | p0 | m0 | f0
  deriving DecidableEq, Fintype, Repr

/-- The case triplet, in the *ABA order NOM ≺ ACC ≺ DAT. -/
inductive Case3 | nom | acc | dat
  deriving DecidableEq, Fintype, Repr

/-- **Strong Case Containment** (Table 1): a chain ∅ ⊂ {k₁} ⊂ {k₁,k₂}. -/
def scc : Case3 → Finset K
  | .nom => ∅ | .acc => {.k1} | .dat => {.k1, .k2}

/-- **No Case Containment** (Table 2): pairwise incomparable feature sets;
k₃ is the NOM/ACC feature absent from DAT. -/
def ncc : Case3 → Finset K
  | .nom => {.k0, .k3} | .acc => {.k1, .k3} | .dat => {.k1, .k2}

/-- **Weak Case Containment** (Table 24): ACC ⊂ DAT as in SCC, but NOM carries
its own k₀, incomparable to ACC — no k₃. -/
def wcc : Case3 → Finset K
  | .nom => {.k0} | .acc => {.k1} | .dat => {.k1, .k2}

variable {F : Type*}

/-! ### *ABA

The generic order-theoretic exclusion is `Decomposition.noABA`: whenever the
middle cell nests between the outer two, a rule winning both outer cells wins the
middle, so no distinct B can interrupt an A_A pattern. It discharges for the two
containment decompositions by `decide` on the hypotheses; NCC violates the
first (`ncc_aba_generable`). -/

/-- *ABA under Strong Case Containment ([caha-2009],
[smith-moskal-xu-kang-bobaljik-2019]). -/
theorem noABA_scc {v : RuleSet (Rule Case3 scc F)} {A B : Rule Case3 scc F}
    (hnom : IsWinner v .nom A) (hdat : IsWinner v .dat A)
    (hacc : IsWinner v .acc B) : B = A :=
  noABA (by decide) (by decide) hnom hdat hacc

/-- *ABA under Weak Case Containment: the paper's Table 24 decomposition keeps
SCC's exclusion. -/
theorem noABA_wcc {v : RuleSet (Rule Case3 wcc F)} {A B : Rule Case3 wcc F}
    (hnom : IsWinner v .nom A) (hdat : IsWinner v .dat A)
    (hacc : IsWinner v .acc B) : B = A :=
  noABA (by decide) (by decide) hnom hdat hacc

/-- Exponent labels for the derivation tables. -/
inductive Ex | A | B | C
  deriving DecidableEq, Repr

/-- A PATTERN-column value: the exponents surfacing at NOM, ACC, DAT. -/
def surface (n a d : Ex) : Case3 → Ex
  | .nom => n | .acc => a | .dat => d

/-- Under NCC, an elsewhere rule plus a rule for the accusative-specific set {k₁, k₃} yields ABA
(§2). -/
theorem ncc_aba_generable :
    ∀ c, pattern (D := ncc) [⟨∅, Ex.A⟩, ⟨{.k1, .k3}, Ex.B⟩] c
      = some (surface .A .B .A c) := by
  decide

/-! ### Non-Elsewhere Nominative Stems -/

/-- Under SCC, a rule applicable in the nominative is featureless, so SCC cannot state a
non-elsewhere nominative stem (§3). -/
theorem scc_nom_forces_empty {r : Rule Case3 scc F}
    (h : Exponence.Applies r .nom) : r.feats = ∅ :=
  Finset.subset_empty.mp h

/-! ### Table 25: derivations of AAA, ABB, AAB, ABC under WCC

Each row pairs its rule inventory with its PATTERN column. Rows 5 and 7 use
the minimal `{k₂}` variant of the table's `{(k₁,)k₂}`. Rows 2–3 are the NENS
derivations — rule A strictly or weakly outranks the elsewhere B. -/

/-- The eight rows of Table 25: rule inventory and PATTERN column. -/
def table25 : List (RuleSet (Rule Case3 wcc Ex) × (Case3 → Ex)) :=
  [([⟨∅, .A⟩], surface .A .A .A),
   ([⟨{.k0}, .A⟩, ⟨{.k1}, .B⟩], surface .A .B .B),
   ([⟨{.k0}, .A⟩, ⟨∅, .B⟩], surface .A .B .B),
   ([⟨∅, .A⟩, ⟨{.k1}, .B⟩], surface .A .B .B),
   ([⟨∅, .A⟩, ⟨{.k2}, .B⟩], surface .A .A .B),
   ([⟨∅, .A⟩, ⟨{.k1}, .B⟩, ⟨{.k1, .k2}, .C⟩], surface .A .B .C),
   ([⟨{.k0}, .A⟩, ⟨∅, .B⟩, ⟨{.k2}, .C⟩], surface .A .B .C),
   ([⟨{.k0}, .A⟩, ⟨{.k1}, .B⟩, ⟨{.k1, .k2}, .C⟩], surface .A .B .C)]

/-- Every Table 25 row's inventory generates its PATTERN column. -/
theorem table25_generates :
    ∀ p ∈ table25, ∀ c, pattern p.1 c = some (p.2 c) := by decide

/-! ### Latvian *pat-* ~ *paš-* (Table 20, rules (7))

The emphatic pronoun singles out nominative singular across both genders:
*pat-s* / *pat-i* against *paš-* everywhere else. Rules (7): *pat-* in k₀
singular contexts, *paš-* elsewhere. Number decomposes with neither value
contained in the other (fn. 26); gender features are carried by the cells but
referenced by no rule. -/

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

/-- A Latvian cell: case, number, gender. -/
structure LCell where
  case : Case3
  num : LNum
  gen : LGen
  deriving DecidableEq, Fintype, Repr

/-- The Latvian decomposition: WCC for case, s₀/p₀ for number, m₀/f₀ for
gender. -/
def latvian (c : LCell) : Finset K :=
  wcc c.case ∪ (match c.num with | .sg => {.s0} | .pl => {.p0})
    ∪ (match c.gen with | .masc => {.m0} | .fem => {.f0})

/-- Rules (7): *pat-* in k₀ singular contexts; *paš-* elsewhere. -/
def latvianRules : RuleSet (Rule LCell latvian String) :=
  [⟨{.k0, .s0}, "pat"⟩, ⟨∅, "paš"⟩]

/-- The stem of Table 20 at a cell: the root of the form of *pats* in the
cell's case, number and gender. -/
def table20stem (c : LCell) : Option String :=
  (Latvian.Pronouns.pats c.case.toLatvian c.num.toNumber c.gen.toUD).bind
    fun ms ↦ (ms.find? (·.kind = .root)).map (·.form)

/-- Rules (7) generate Table 20's stem distribution. -/
theorem latvian_stems : ∀ c, pattern latvianRules c = table20stem c := by
  decide

/-- The pattern "cuts across genders": neither rule references gender, so the
distribution is gender-blind. -/
theorem latvian_gender_blind (c n) :
    pattern latvianRules ⟨c, n, .masc⟩ = pattern latvianRules ⟨c, n, .fem⟩ := by
  revert c n; decide

/-- *pat-* must be specified for the singular alongside k₀ (fn. 26): dropping
s₀ overgenerates *pat-* into the nominative plural. -/
theorem latvian_pat_needs_singular :
    pattern [(⟨{.k0}, "pat"⟩ : Rule LCell latvian String), ⟨∅, "paš"⟩]
        ⟨.nom, .pl, .masc⟩ = some "pat" := by
  decide

/-! ### Yiddish 1st person (fn. 25): why k₁ exists

*ix* (NOM.SG), *m-* (elsewhere: *m-ir, m-ix*), *undz* (ACC.PL and DAT.PL).
The *undz* rule must reference k₁: specified for plural alone it would also
capture the nominative plural *m-ir*. This ABB row with B more specific than
the elsewhere is the evidence that WCC's k₁ is not eliminable. -/

/-- A Yiddish cell: case and number. -/
structure YCell where
  case : Case3
  num : LNum
  deriving DecidableEq, Fintype, Repr

/-- The Yiddish decomposition: WCC for case, s₀/p₀ for number. -/
def yiddish (c : YCell) : Finset K :=
  wcc c.case ∪ (match c.num with | .sg => {.s0} | .pl => {.p0})

/-- The three stem rules: *ix* a non-elsewhere nominative-singular stem,
*undz* the k₁-plural stem, *m-* the elsewhere. -/
def yiddishRules : RuleSet (Rule YCell yiddish String) :=
  [⟨{.k0, .s0}, "ix"⟩, ⟨{.k1, .p0}, "undz"⟩, ⟨∅, "m"⟩]

/-- The fn. 25 paradigm's stem distribution: *ix* / *m-ix* / *m-ir* in the
singular, *m-ir* / *undz* / *undz* in the plural. -/
def yiddishStem (c : YCell) : String :=
  if c.case = .nom ∧ c.num = .sg then "ix"
  else if c.case ≠ .nom ∧ c.num = .pl then "undz"
  else "m"

/-- The three rules generate the paradigm. -/
theorem yiddish_stems : ∀ c, pattern yiddishRules c = some (yiddishStem c) := by
  decide

/-- *undz* needs k₁ (fn. 25): specified for plural alone, it wrongly beats
*m-* in the nominative plural. -/
theorem undz_needs_k1 :
    pattern [(⟨{.k0, .s0}, "ix"⟩ : Rule YCell yiddish String),
        ⟨{.p0}, "undz"⟩, ⟨∅, "m"⟩] ⟨.nom, .pl⟩ = some "undz" := by
  decide

end ChristopoulosZompi2023
