module

public import Studies.McCarthy2005
import Mathlib.Tactic.FinCases

/-!
# Marco and Rasin (2026): Optimal Paradigms

This file formalizes the challenge to optimal paradigms of [marco-rasin-2026]. [mccarthy-2005]
derived the Moroccan Arabic noun–verb asymmetry in the position of schwa, verbs CCəC
regardless of sonority and nouns CəCC when the second consonant is more sonorous than the
third, from paradigm structure: most verbal suffixes are consonant-initial, so paradigm
uniformity draws the unsuffixed verb to CCəC by majority rule, while the one-member noun
paradigm is left to the sonority constraint. In Judeo-Tripolitanian Arabic verbs and nouns
pattern as in Moroccan, but adjectives are CCəC regardless of sonority while inflecting, like
nouns, with vowel-initial suffixes only, so under McCarthy's ranking optimal paradigms select
the levelled CəCC paradigm for them: for any root and any suffixes, the bare stem sides with
[the more numerous class of suffixes](##MarcoRasin2026.majority_rules); a category-specific
template for verbs and adjectives derives the pattern, against category-neutral phonology
([bobaljik-2008]).

## Implementation notes

* The paradigms, constraints, and ranking are those of the McCarthy 2005 study, run on the
  Judeo-Tripolitanian data; schwa is epenthetic, so the input is the bare root.
* The paper states OP-MAX-V over positions: a mark for each pair of members in which one has a
  vowel where the other has none. Here it is MAX-V on the relation between two stems that their
  input correspondences induce, in which epenthetic schwas at different sites do not correspond;
  the two [agree on the paper's counts](##MarcoRasin2026.opMaxV_counts).
* The templatic constraint is read at every member's stem, where the paper's tableau shows the
  bare form alone.

## References

* [marco-rasin-2026]
* [mccarthy-2005]
* [bobaljik-2008]
-/

@[expose] public section

namespace MarcoRasin2026

open OptimalityTheory McCarthy2005 McCarthy2005.Arabic

/-- The CCəC realisation of the root /C₁C₂C₃/ in a cell, the schwa epenthetic. -/
def schwaMedial (c₁ c₂ c₃ : Seg) (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, [c₁, c₂, .schwa, c₃], [(0, 0), (1, 1), (2, 3)]⟩

/-- The CəCC realisation. -/
def schwaInitial (c₁ c₂ c₃ : Seg) (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, [c₁, .schwa, c₂, c₃], [(0, 0), (1, 2), (2, 3)]⟩

/-- The candidate paradigms of a root over the bare cell, the C-initial and the V-initial
suffixes, as in tableau (9): the bare stem CCəC or CəCC with the suffixed stems fixed by the
phonotactics, or levelled to CCəC or to CəCC. -/
def paradigms (c₁ c₂ c₃ : Seg) (cInitial vInitial : List (List Seg)) :
    Cand → Paradigm Seg (List Seg)
  | .a => ⟨root, ([] :: cInitial).map medial ++ vInitial.map initial⟩
  | .b => ⟨root, initial [] :: cInitial.map medial ++ vInitial.map initial⟩
  | .c => ⟨root, ([] :: cInitial ++ vInitial).map medial⟩
  | _ => ⟨root, ([] :: cInitial ++ vInitial).map initial⟩
where
  root : List Seg := [c₁, c₂, c₃]
  medial := schwaMedial c₁ c₂ c₃
  initial := schwaInitial c₁ c₂ c₃

/-- The undominated markedness constraints (7a, b): \*ə]σ and \*CCC. -/
def phonotactics : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness fun suf s ↦ schwaOpen (s ++ suf), markedness fun suf s ↦ ccc (s ++ suf)]

/-- The constraints (7) in the ranking of tableau (9): \*ə]σ, \*CCC >> OP-MAX-V >> SONCON. -/
def ranking : List (Constraint (Paradigm Seg (List Seg))) :=
  phonotactics ++
    [opFaith (Correspondence.Diagram.maxViolOn IsVowel), markedness fun suf s ↦ sonCon (s ++ suf)]

/-! ### Moroccan Arabic (§2) -/

/-- The Moroccan perfective paradigm of /ʃrb/ 'drink', with the suffixes of tableau (9). -/
def moroccan : Cand → Paradigm Seg (List Seg) :=
  paradigms .sh .r .b [[.t], [.n, .a], [.t, .i], [.t, .u]] [[.schwa, .t], [.u]]

/-! ### Majority rules -/

/-- The input correspondence of a CCəC stem, read into positions. -/
private abbrev medialIO : Correspondence (Fin 3) (Fin 4) :=
  Correspondence.edgeOfPairs 3 4 [(0, 0), (1, 1), (2, 3)]

/-- The input correspondence of a CəCC stem, read into positions. -/
private abbrev initialIO : Correspondence (Fin 3) (Fin 4) :=
  Correspondence.edgeOfPairs 3 4 [(0, 0), (1, 2), (2, 3)]

private theorem image_fst_medial_medial :
    (medialIO.through medialIO).image Prod.fst = Finset.univ := by decide +kernel

private theorem image_fst_initial_initial :
    (initialIO.through initialIO).image Prod.fst = Finset.univ := by decide +kernel

private theorem image_fst_medial_initial :
    (medialIO.through initialIO).image Prod.fst = {0, 1, 3} := by decide +kernel

private theorem image_fst_initial_medial :
    (initialIO.through medialIO).image Prod.fst = {0, 2, 3} := by decide +kernel

variable (c₁ c₂ c₃ : Seg) (s s' : List Seg)

private theorem maxV_medial_medial :
    Correspondence.Diagram.maxViolOn IsVowel
      ((schwaMedial c₁ c₂ c₃ s).opCorr [c₁, c₂, c₃] (schwaMedial c₁ c₂ c₃ s')) .lhs .rhs = 0 := by
  show (Finset.univ.filter (fun i : Fin 4 ↦ IsVowel [c₁, c₂, Seg.schwa, c₃][i]) \
    (medialIO.through medialIO).image Prod.fst).card = 0
  rw [image_fst_medial_medial, Finset.sdiff_eq_empty_iff_subset.2 (Finset.subset_univ _),
    Finset.card_empty]

private theorem maxV_initial_initial :
    Correspondence.Diagram.maxViolOn IsVowel
      ((schwaInitial c₁ c₂ c₃ s).opCorr [c₁, c₂, c₃] (schwaInitial c₁ c₂ c₃ s')) .lhs .rhs = 0 := by
  show (Finset.univ.filter (fun i : Fin 4 ↦ IsVowel [c₁, Seg.schwa, c₂, c₃][i]) \
    (initialIO.through initialIO).image Prod.fst).card = 0
  rw [image_fst_initial_initial, Finset.sdiff_eq_empty_iff_subset.2 (Finset.subset_univ _),
    Finset.card_empty]

private theorem maxV_medial_initial :
    Correspondence.Diagram.maxViolOn IsVowel
      ((schwaMedial c₁ c₂ c₃ s).opCorr [c₁, c₂, c₃] (schwaInitial c₁ c₂ c₃ s')) .lhs .rhs = 1 := by
  show (Finset.univ.filter (fun i : Fin 4 ↦ IsVowel [c₁, c₂, Seg.schwa, c₃][i]) \
    (medialIO.through initialIO).image Prod.fst).card = 1
  rw [image_fst_medial_initial, Finset.card_eq_one]
  refine ⟨2, Finset.ext fun i ↦ ?_⟩
  fin_cases i <;> simp [IsVowel]

private theorem maxV_initial_medial :
    Correspondence.Diagram.maxViolOn IsVowel
      ((schwaInitial c₁ c₂ c₃ s).opCorr [c₁, c₂, c₃] (schwaMedial c₁ c₂ c₃ s')) .lhs .rhs = 1 := by
  show (Finset.univ.filter (fun i : Fin 4 ↦ IsVowel [c₁, Seg.schwa, c₂, c₃][i]) \
    (initialIO.through medialIO).image Prod.fst).card = 1
  rw [image_fst_initial_medial, Finset.card_eq_one]
  refine ⟨1, Finset.ext fun i ↦ ?_⟩
  fin_cases i <;> simp [IsVowel]

variable (cInitial vInitial : List (List Seg))

-- Each pair of a CCəC stem and a CəCC stem draws two OP-MAX-V marks, one in each direction.
theorem opMaxV_medial_append_initial :
    opFaith (Correspondence.Diagram.maxViolOn IsVowel)
      ⟨[c₁, c₂, c₃], cInitial.map (schwaMedial c₁ c₂ c₃) ++ vInitial.map (schwaInitial c₁ c₂ c₃)⟩ =
        2 * (cInitial.length * vInitial.length) := by
  rw [opFaith_append (k := 2), List.length_map, List.length_map, mul_comm]
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun s _ s' _ ↦ maxV_medial_medial c₁ c₂ c₃ s s'
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun s _ s' _ ↦ maxV_initial_initial c₁ c₂ c₃ s s'
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun s _ s' _ ↦ by rw [maxV_medial_initial, maxV_initial_medial]

theorem opMaxV_paradigms_a :
    opFaith (Correspondence.Diagram.maxViolOn IsVowel) (paradigms c₁ c₂ c₃ cInitial vInitial .a) =
      2 * ((cInitial.length + 1) * vInitial.length) :=
  opMaxV_medial_append_initial c₁ c₂ c₃ ([] :: cInitial) vInitial

theorem opMaxV_paradigms_b :
    opFaith (Correspondence.Diagram.maxViolOn IsVowel) (paradigms c₁ c₂ c₃ cInitial vInitial .b) =
      2 * (cInitial.length * (vInitial.length + 1)) :=
  (opFaith_perm _ List.perm_middle.symm).trans
    (opMaxV_medial_append_initial c₁ c₂ c₃ cInitial ([] :: vInitial))

/-- Majority rules: the paradigm whose bare stem is CCəC draws fewer OP-MAX-V marks than the
one whose bare stem is CəCC exactly when the C-initial suffixes outnumber the V-initial ones
(10). -/
theorem majority_rules :
    opFaith (Correspondence.Diagram.maxViolOn IsVowel) (paradigms c₁ c₂ c₃ cInitial vInitial .a) <
        opFaith (Correspondence.Diagram.maxViolOn IsVowel)
          (paradigms c₁ c₂ c₃ cInitial vInitial .b) ↔
      vInitial.length < cInitial.length := by
  rw [opMaxV_paradigms_a, opMaxV_paradigms_b, Nat.mul_lt_mul_left two_pos, Nat.add_mul,
    Nat.mul_add, one_mul, mul_one, Nat.add_lt_add_iff_left]

variable {c₁ c₂ c₃ cInitial vInitial} {labels : Finset Cand}

-- Where the phonotactics leave the two paradigms that differ in the bare stem, the winner is
-- the one whose bare stem sides with the more numerous suffixes.
theorem optimal_of_lt
    (h : (Tableau.ofLabels (paradigms c₁ c₂ c₃ cInitial vInitial) labels phonotactics).optimal =
      {.a, .b}) (hlt : vInitial.length < cInitial.length) :
    (Tableau.ofLabels (paradigms c₁ c₂ c₃ cInitial vInitial) labels ranking).optimal = {.a} := by
  rw [ranking, Tableau.optimal_ofLabels_append, h]
  refine Tableau.optimal_ofLabels_cons_eq_singleton (by simp) fun l hl hne ↦ ?_
  obtain rfl : l = .b := by simpa [hne] using hl
  exact (majority_rules c₁ c₂ c₃ cInitial vInitial).2 hlt

theorem optimal_of_gt
    (h : (Tableau.ofLabels (paradigms c₁ c₂ c₃ cInitial vInitial) labels phonotactics).optimal =
      {.a, .b}) (hlt : cInitial.length < vInitial.length) :
    (Tableau.ofLabels (paradigms c₁ c₂ c₃ cInitial vInitial) labels ranking).optimal = {.b} := by
  rw [ranking, Tableau.optimal_ofLabels_append, h]
  refine Tableau.optimal_ofLabels_cons_eq_singleton (by simp) fun l hl hne ↦ ?_
  obtain rfl : l = .a := by simpa [hne] using hl
  rw [opMaxV_paradigms_a, opMaxV_paradigms_b, Nat.mul_lt_mul_left two_pos, Nat.add_mul,
    Nat.mul_add, one_mul, mul_one, Nat.add_lt_add_iff_left]
  exact hlt

/-- In the Moroccan verb the bare stem is CCəC against sonority, as in tableau (9): the
phonotactics leave the two paradigms that differ in the bare stem, and four C-initial suffixes
outnumber two V-initial ones. -/
theorem moroccan_verb : (Tableau.ofLabels moroccan {.a, .b, .c, .d} ranking).optimal = {.a} :=
  optimal_of_lt (by decide +kernel) (by decide)

/-- The attested Moroccan paradigm, with four C-initial and two V-initial suffixes, draws 20
OP-MAX-V marks against 24 with the bare stem CəCC (9), and the attested adjectival paradigm,
with two V-initial suffixes alone, draws four (14). -/
theorem opMaxV_counts :
    opFaith (Correspondence.Diagram.maxViolOn IsVowel) (moroccan .a) = 20 ∧
      opFaith (Correspondence.Diagram.maxViolOn IsVowel) (moroccan .b) = 24 ∧
      opFaith (Correspondence.Diagram.maxViolOn IsVowel)
        (paradigms .t .r .sh [] [[.a], [.i, .n]] .a) = 4 :=
  ⟨opMaxV_paradigms_a .., opMaxV_paradigms_b .., opMaxV_paradigms_a ..⟩

-- (11)
theorem moroccan_noun :
    (Tableau.ofLabels (paradigms .sh .r .b [] []) {.a, .b} ranking).optimal = {.b} := by
  decide +kernel

/-! ### Judeo-Tripolitanian Arabic verbs and nouns (§3.1) -/

/-- The JTA perfect suffixes (Table 2): five C-initial, two V-initial. -/
def jtaVerb (c₁ c₂ c₃ : Seg) : Cand → Paradigm Seg (List Seg) :=
  paradigms c₁ c₂ c₃ [[.ch], [.n, .a], [.ch], [.ch, .i], [.ch, .u]] [[.schwa, .ch], [.u]]

-- Table 2
theorem jta_verbs :
    ∀ r ∈ [(Seg.sh, Seg.r, Seg.b), (.g, .d, .m), (.k, .ch, .b)],
      (Tableau.ofLabels (jtaVerb r.1 r.2.1 r.2.2) {.a, .b, .c, .d} ranking).optimal = {.a} := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨optimal_of_lt (by decide +kernel) (by decide),
    optimal_of_lt (by decide +kernel) (by decide), optimal_of_lt (by decide +kernel) (by decide)⟩

/-- The roots of the nouns (12): CəCC with C₂ more sonorous than C₃ — *kəlb, bəntʃ, wəld,
səms, məlħ, tʃəlʒ* — and CCəC otherwise — *xʃəm, ħbəq, lħəm, sdər, bsəl, fħəm*. -/
def nouns : List (Seg × Seg × Seg) × List (Seg × Seg × Seg) :=
  ([(.k, .l, .b), (.b, .n, .ch), (.w, .l, .d), (.s, .m, .s), (.m, .l, .hh), (.ch, .l, .zh)],
   [(.x, .sh, .m), (.hh, .b, .q), (.l, .hh, .m), (.s, .d, .r), (.b, .s, .l), (.f, .hh, .m)])

-- (12)
theorem jta_nouns :
    (∀ r ∈ nouns.1,
      (Tableau.ofLabels (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} ranking).optimal = {.b}) ∧
    ∀ r ∈ nouns.2,
      (Tableau.ofLabels (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} ranking).optimal = {.a} := by
  decide +kernel

/-! ### The challenge from adjectives (§3.2–3.3)

Adjectives with C₂ more sonorous than C₃ — *bjəd* 'white', *zrəq* 'blue', *trəʃ* 'deaf',
*ħwəl* 'cross-eyed' (13a), the comparatives *qrəb*, *zjən* (Table 3) — are CCəC like verbs, but
inflect with the V-initial suffixes *-a*, *-in* alone (Table 5). -/

/-- The adjectival paradigm of a root (Table 5): bare, feminine *-a*, plural *-in*. -/
def adjective (c₁ c₂ c₃ : Seg) : Cand → Paradigm Seg (List Seg) :=
  paradigms c₁ c₂ c₃ [] [[.a], [.i, .n]]

/-- The roots of the adjectives with C₂ more sonorous than C₃, (13a) and Table 3. -/
def adjectives : List (Seg × Seg × Seg) :=
  [(.b, .j, .d), (.z, .r, .q), (.t, .r, .sh), (.hh, .w, .l), (.q, .r, .b), (.z, .j, .n)]

/-- Optimal paradigms select the levelled CəCC paradigm for the adjectives, which surface as
CCəC (14). -/
theorem adjective_paradigm :
    ∀ r ∈ adjectives,
      (Tableau.ofLabels (adjective r.1 r.2.1 r.2.2) {.a, .b} ranking).optimal = {.b} := by
  have h : ∀ r ∈ adjectives, (Tableau.ofLabels (adjective r.1 r.2.1 r.2.2) {.a, .b}
      phonotactics).optimal = {.a, .b} := by decide +kernel
  exact fun r hr ↦ optimal_of_gt (h r hr) (by decide)

-- (15)
theorem adjective_bare :
    ∀ r ∈ adjectives,
      (Tableau.ofLabels (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} ranking).optimal = {.b} := by
  decide +kernel

/-! ### Category-specific templates (§3.3) -/

inductive Category
  | verb | adjective | noun
  deriving DecidableEq, Repr

/-- {CCəC}_{Verb, Adj} (17): the stem of a verb or an adjective surfaces as CCəC. -/
def template : Category → List Seg → ℕ
  | .noun, _ => 0
  | _, [_, .schwa, _, _] => 1
  | _, _ => 0

/-- The ranking of tableau (18): \*ə]σ, \*CCC >> {CCəC}_{Verb, Adj} >> SONCON. -/
def templateRanking (cat : Category) : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness fun suf s ↦ schwaOpen (s ++ suf), markedness fun suf s ↦ ccc (s ++ suf),
   markedness fun _ s ↦ template cat s, markedness fun suf s ↦ sonCon (s ++ suf)]

/-- A template for verbs and adjectives ranked above SONCON derives the adjectives' CCəC (18). -/
theorem template_adjective :
    ∀ r ∈ adjectives,
      (Tableau.ofLabels (adjective r.1 r.2.1 r.2.2) {.a, .b} (templateRanking .adjective)).optimal =
        {.a} := by
  decide +kernel

-- Table 2, (12)
theorem template_verb_noun :
    (∀ r ∈ [(Seg.sh, Seg.r, Seg.b), (.g, .d, .m), (.k, .ch, .b)],
      (Tableau.ofLabels (jtaVerb r.1 r.2.1 r.2.2) {.a, .b, .c, .d} (templateRanking .verb)).optimal
        = {.a}) ∧
    (∀ r ∈ nouns.1,
      (Tableau.ofLabels (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b}
        (templateRanking .noun)).optimal = {.b}) ∧
    ∀ r ∈ nouns.2,
      (Tableau.ofLabels (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b}
        (templateRanking .noun)).optimal = {.a} := by
  decide +kernel

end MarcoRasin2026
