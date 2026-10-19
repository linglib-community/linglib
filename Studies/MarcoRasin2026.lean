module

public import Studies.McCarthy2005

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
the levelled CəCC paradigm for them; a category-specific template for verbs and adjectives
derives the pattern, against category-neutral phonology ([bobaljik-2008]).

## Implementation notes

The paradigms, constraints, and ranking are those of the McCarthy 2005 study, run on the
Judeo-Tripolitanian data; schwa is epenthetic, so the input is the bare root.

## TODO

The paper is not on file; example numbers are transcribed from an earlier version of this
file and are UNVERIFIED.

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
suffixes (10): the bare stem CCəC or CəCC with the suffixed stems fixed by the phonotactics,
or levelled to CCəC or to CəCC. -/
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

/-- The constraints (8) in McCarthy's ranking: \*ə]σ, \*CCC >> OP-MAX-V >> SONCON. -/
def ranking : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness λ suf s => schwaOpen (s ++ suf), markedness λ suf s => ccc (s ++ suf),
   opFaith (Correspondence.maxViolOn IsVowel), markedness λ suf s => sonCon (s ++ suf)]

/-! ### Moroccan Arabic (§2) -/

/-- The Moroccan perfective suffixes (6). -/
def moroccan : Cand → Paradigm Seg (List Seg) :=
  paradigms .sh .r .b [[.t], [.n, .a], [.t, .i], [.t, .u]] [[.schwa, .t], [.u]]

/-- (10): majority rules — the unsuffixed *ʃrəb* joins the C-suffixed CCəC stems, twenty
OP-MAX-V marks against twenty-four. -/
theorem moroccan_verb : (tableau moroccan {.a, .b, .c, .d} ranking).optimal = {.a} := by
  decide

/-- (12): the one-member noun paradigm is left to SONCON, *ʃərb*. -/
theorem moroccan_noun : (tableau (paradigms .sh .r .b [] []) {.a, .b} ranking).optimal = {.b} := by
  decide

/-! ### Judeo-Tripolitanian Arabic verbs and nouns (§3.1) -/

/-- The JTA perfective suffixes (13): five C-initial, two V-initial. -/
def jtaVerb (c₁ c₂ c₃ : Seg) : Cand → Paradigm Seg (List Seg) :=
  paradigms c₁ c₂ c₃ [[.ch], [.n, .a], [.ch], [.ch, .i], [.ch, .u]] [[.schwa, .ch], [.u]]

/-- (13): the paradigms of *ʃrəb* 'drink', *gdəm* 'bite' and *ktʃəb* 'write' — CCəC in the
bare form and before C-initial suffixes, CəCC before V-initial ones, whatever the sonority
of the root — are OP's optima. -/
theorem jta_verbs :
    ∀ r ∈ [(Seg.sh, Seg.r, Seg.b), (.g, .d, .m), (.k, .ch, .b)],
      (tableau (jtaVerb r.1 r.2.1 r.2.2) {.a, .b, .c, .d} ranking).optimal = {.a} := by
  decide

/-- The roots of the nouns (14): CəCC with C₂ more sonorous than C₃ — *kəlb, bəntʃ, wəld,
səms, məlħ, tʃəlʒ* — and CCəC otherwise — *xʃəm, ħbəq, lħəm, sdər, bsəl, fħəm*. -/
def nouns : List (Seg × Seg × Seg) × List (Seg × Seg × Seg) :=
  ([(.k, .l, .b), (.b, .n, .ch), (.w, .l, .d), (.s, .m, .s), (.m, .l, .hh), (.ch, .l, .zh)],
   [(.x, .sh, .m), (.hh, .b, .q), (.l, .hh, .m), (.s, .d, .r), (.b, .s, .l), (.f, .hh, .m)])

/-- (14): the one-member noun paradigms follow SONCON. -/
theorem jta_nouns :
    (∀ r ∈ nouns.1, (tableau (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} ranking).optimal = {.b}) ∧
    ∀ r ∈ nouns.2, (tableau (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} ranking).optimal = {.a} := by
  decide

/-! ### The challenge from adjectives (§3.2–3.3)

Adjectives with C₂ more sonorous than C₃ — *bjəd* 'white', *zrəq* 'blue', *trəʃ* 'deaf',
*ħwəl* 'cross-eyed' (15), the comparatives *qrəb*, *zjən* (16) — are CCəC like verbs, but
inflect with the V-initial suffixes *-a*, *-in* alone (18). -/

/-- The adjectival paradigm of a root (18): bare, feminine *-a*, plural *-in*. -/
def adjective (c₁ c₂ c₃ : Seg) : Cand → Paradigm Seg (List Seg) :=
  paradigms c₁ c₂ c₃ [] [[.a], [.i, .n]]

/-- The roots of the adjectives with C₂ more sonorous than C₃, (15a) and (16). -/
def adjectives : List (Seg × Seg × Seg) :=
  [(.b, .j, .d), (.z, .r, .q), (.t, .r, .sh), (.hh, .w, .l), (.q, .r, .b), (.z, .j, .n)]

/-- (19): OP fails — the attested ⟨trəʃ, tərʃa, tərʃin⟩ draws four OP-MAX-V marks and one
of SONCON, and the levelled ⟨tərʃ, tərʃa, tərʃin⟩ none. -/
theorem adjective_paradigm :
    ∀ r ∈ adjectives, (tableau (adjective r.1 r.2.1 r.2.2) {.a, .b} ranking).optimal = {.b} := by
  decide

/-- (20): OP fails regardless of what constitutes a paradigm — as a paradigm of one, the
adjective is left to SONCON, *tərʃ*. -/
theorem adjective_bare :
    ∀ r ∈ adjectives,
      (tableau (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} ranking).optimal = {.b} := by
  decide

/-! ### Category-specific templates (§3.3) -/

inductive Category
  | verb | adjective | noun
  deriving DecidableEq, Repr

/-- {CCəC}_{Verb, Adj} (22): the stem of a verb or an adjective surfaces as CCəC. -/
def template : Category → List Seg → ℕ
  | .noun, _ => 0
  | _, [_, .schwa, _, _] => 1
  | _, _ => 0

/-- The ranking (23): \*ə]σ, \*CCC >> {CCəC}_{Verb, Adj} >> SONCON. -/
def templateRanking (cat : Category) : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness λ suf s => schwaOpen (s ++ suf), markedness λ suf s => ccc (s ++ suf),
   markedness λ _ s => template cat s, markedness λ suf s => sonCon (s ++ suf)]

/-- (23): the template selects the attested adjectival paradigms against SONCON. -/
theorem template_adjective :
    ∀ r ∈ adjectives,
      (tableau (adjective r.1 r.2.1 r.2.2) {.a, .b} (templateRanking .adjective)).optimal =
        {.a} := by
  decide

/-- The template leaves the verbs (13) and the nouns (14) as they are. -/
theorem template_verb_noun :
    (∀ r ∈ [(Seg.sh, Seg.r, Seg.b), (.g, .d, .m), (.k, .ch, .b)],
      (tableau (jtaVerb r.1 r.2.1 r.2.2) {.a, .b, .c, .d} (templateRanking .verb)).optimal
        = {.a}) ∧
    (∀ r ∈ nouns.1,
      (tableau (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} (templateRanking .noun)).optimal = {.b}) ∧
    ∀ r ∈ nouns.2,
      (tableau (paradigms r.1 r.2.1 r.2.2 [] []) {.a, .b} (templateRanking .noun)).optimal =
        {.a} := by
  decide

end MarcoRasin2026
