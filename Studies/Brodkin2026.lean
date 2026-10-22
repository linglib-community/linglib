module

public import Linglib.Phonology.Prosody.Word
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.Prosody.Match
public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.Command
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Data.Examples.Brodkin2026
public import Linglib.Data.Wordlist.Brodkin2026
public import Mathlib.Tactic.DeriveFintype

/-!
# Brodkin (2026): suppletion in global perspective

Seven Mandar heads take a monosyllabic allomorph inside a phonological phrase φ and a longer one
at its right edge, because Positional Minimality, Align-R(φ, (σ́σ)), outranks PRIORITY. Where
Syllable Lifting can draw an unfooted syllable from the next φ of the same maximal φ, the
suppletion is suspended, so Vocabulary Insertion reads prosody beyond the head.

## Main definitions

* `vocabulary`: the Vocabulary Items of the heads of (44), with (57a).
* `Constituency`, `candidates`, `tableau`: the syntax of the head and the next word, GEN over the
  allomorphs and the phrasings, and the ranking of (26c), (63), (64) and (80) over MAX-XP (23a),
  SUBCAT (29b), Positional Minimality (26a), PRIORITY (60a), Match(ω, X⁰) (75a) and
  Match(φ, XP) (23b).

## Main results

* `optimal_joined_iff`: whether the head ends its φ follows from the syntax.
* `optimal_exponent`: the calculus of top-down suppletion (88).
* `suppletion_not_optimal_without_maxXP`: MAX-XP, which the tableaux of §3–§4 omit, is what keeps
  a stranded head out of the next word's φ.
* `rows_optimal`: the grammar inserts the attested allomorph in every example.
* `optimal_item_eq_of_two_le`: only a monosyllabic unmarked allomorph suppletes.
* `winner?_eq_some_item_of_mem_optimal`: PRIORITY undominated selects the Subset Principle's
  winner.
* `forms_not_function_of_constituency`, `forms_not_function_of_footed`: neither the syntax nor it
  and the footing of the next syllable determine the attested allomorph, so no rule set reading
  only these inserts it (`not_realizes_of_constituency`, `not_realizes_of_footed`), nor does the
  Subset Principle over the heads' neighborhoods (`not_subsetPrinciple_eq_forms`).
* `forms_not_function_of_cCommanded`: nor do the words a head c-commands in the ditransitive
  clause (90), against insertion bounded by the c-command domain (92).

## Implementation notes

* The input is the syntax of the head and the next word: the phrases over the two words, each
  anchored at its head's stressed syllable, the extended projection of a noun or predicate one
  phrase anchored at the noun or predicate, and whether the next word is a second-position
  element. MAX-XP is
  `Prosody.syntaxProsodyMax`, the existential correspondence of Itô and Mester as their tableaux
  count it, which Brodkin adopts for (23a).
* The maximal φ is the paper's domain stipulation on Syllable Lifting (§4.3), stated in GEN; an
  example records it where the paper brackets it or the clause has at most three words (85). The
  maximal φ over both words answers to the clause in Match(φ, XP).
* The c-command argument reads a phrase-structure tree of the ditransitive clause (90), built
  from each example's words, with `RoseTree.CCommands`.
* A parse is built from the syllable count of the inserted form, its vowels in
  `Brodkin2026.Wordlist`, whose 'who' forms are the surface forms of (42); what follows the
  head is a word whose first syllable is footed or unfooted under penultimate stress (14), (15).

## TODO

* The segmental repairs of §2, Vʔ-epenthesis and blocked coalescence and gliding under DEP and
  ONSET, their suspension by Syllable Lifting ((71)–(73)), and the irreducible parallelism of
  (72b); the blocking of *a* 'maybe' (43b), which needs a null parse; prefixes in the parse, for
  *ya-do* (54)–(55).
* Mandar segments in a Fragment, for syllables counted on typed segments.

## References

* [brodkin-2026]
* [mascaro-2007]
* [bonet-lloret-mascaro-2007]
* [halle-marantz-1993]
* [selkirk-2011]
* [ito-mester-2019]
-/

@[expose] public section

namespace Brodkin2026

open Prosody OptimalityTheory DistributedMorphology Morphology.Exponence CLDF.Wordlist

/-! ### The vocabulary -/

/-- The seven heads of table (44). -/
inductive Head
  | thisInHand | this | that | neg | what | which | who
  deriving DecidableEq, Repr, Fintype

/-- The features the items mention: a head, and a categorizer, the v⁰ of *maŋ-*, *mi-* and *ti-*
among them. -/
inductive Feature
  | head (h : Head)
  | cat (c : Categorizer)
  deriving DecidableEq, Repr

namespace Head

/-- A head's unmarked allomorph, its φ-medial form in (44). -/
def short : Head → Form Wordlist.Cell
  | thisInHand => Wordlist.this_in_hand_short | this => Wordlist.this_short
  | that => Wordlist.that_short | neg => Wordlist.neg_short | what => Wordlist.what_short
  | which => Wordlist.which_short | who => Wordlist.who_short

/-- A head's marked allomorph, its φ-final form in (44). -/
def long : Head → Form Wordlist.Cell
  | thisInHand => Wordlist.this_in_hand_long | this => Wordlist.this_long
  | that => Wordlist.that_long | neg => Wordlist.neg_long | what => Wordlist.what_long
  | which => Wordlist.which_long | who => Wordlist.who_long

/-- The neighborhood of a head, with a v⁰ one terminal toward the clause or not. -/
def neighborhood (h : Head) (verbalized : Bool) : Neighborhood (Finset Feature) :=
  ⟨{.head h}, [], if verbalized then [{.cat .v}] else []⟩

end Head

/-- The pairs of the heads are the top-down suppletion relations of the forms table. -/
theorem relations_eq : Wordlist.relations.map (fun r ↦ (r.form, r.target)) =
    [.thisInHand, .this, .that, .neg, .what, .which, .who].map fun h : Head ↦ (h.short, h.long) :=
  rfl

/-- The syllables of a form of (44), one to each vowel. -/
def syllables (f : Form Wordlist.Cell) : ℕ := f.segments.countP (· ∈ ["a", "e", "i", "o", "u"])

/-- Each unmarked allomorph is a monosyllable and each marked one longer. -/
theorem syllables_short_long (h : Head) : syllables h.short = 1 ∧ 2 ≤ syllables h.long := by
  cases h <;> decide

/-- A Vocabulary Item inserts a form of (44). -/
abbrev Item := VocabularyItem Feature (Form Wordlist.Cell)

/-- The vocabulary in PRIORITY's order: (57a), √WHAT as *apa* under v⁰, then each head's
unconditioned unmarked item before its marked one. -/
def vocabulary : RuleSet Item :=
  ⟨{(0, .head .what), (1, .cat .v)}, Head.what.long⟩ ::
    [Head.thisInHand, .this, .that, .neg, .what, .which, .who].flatMap
      fun h ↦ [{Feature.head h} ⟷ h.short, {Feature.head h} ⟷ h.long]

/-- The vocabulary is listed by non-increasing specificity. -/
theorem vocabulary_pairwise : vocabulary.Pairwise fun i j ↦ j.specificity ≤ i.specificity := by
  decide

/-! ### Inputs and candidates -/

/-- The syntax of the head and the word after it: the phrases over the two words, in word units,
each with the word heading it, and whether the second word is a second-position element, which
subcategorizes for the minimal φ of the element before it (29). -/
structure Constituency where
  /-- The phrases over the two words, each as the words it spans and the word heading it. -/
  phrases : List ((ℕ × ℕ) × ℕ)
  /-- The second word is a second-position element. -/
  subcat : Bool
  deriving DecidableEq

namespace Constituency

/-- The head ends its phrase and the next word heads a sister phrase: a stranded head, or a
wh-phrase before the predicate. -/
def sisters : Constituency := ⟨[((0, 1), 0), ((1, 2), 1)], false⟩

/-- The next word heads a phrase inside the head's own, the deictic *e* or *o* after a stranded
demonstrative or negator ((33b), (36b)). -/
def adjunct : Constituency := ⟨[((0, 2), 0), ((1, 2), 1)], false⟩

/-- The next word heads the head's phrase, a noun or predicate whose extended projection the head
belongs to ((33a), (36a)), one phrase as [ito-mester-2019] count an extended projection. -/
def complement : Constituency := ⟨[((0, 2), 1)], false⟩

/-- The next word is a second-position element hosted by the head's phrase ((40a)–(42a)). -/
def host : Constituency := ⟨[((0, 1), 0)], true⟩

end Constituency

/-- The input at a head. -/
structure Input where
  /-- The head and its morphosyntactic neighbors. -/
  neighborhood : Neighborhood (Finset Feature)
  /-- The syntax of the head and the next word. -/
  constituency : Constituency
  /-- The first syllable after the head is footed. -/
  footed : Bool
  /-- The next word shares the head's maximal φ. -/
  sameMax : Bool
  deriving DecidableEq

/-- The prosodic word of `n` syllables with penultimate stress (14), a trochee over its last two
syllables and the earlier ones unfooted (15); a monosyllable is a degenerate foot. -/
def penultimate : ℕ → Tree
  | 0 => .om []
  | 1 => .om [.ft true [.σ 0 true]]
  | n + 2 => .om (List.replicate n .σ ++ [.ft true [.σ 0 true, .σ]])

/-- A disyllabic trochee is a well-formed foot with the head profile of `Foot.trochee`. -/
def IsTrochee (t : Tree) : Prop := IsFoot t ∧ Foot.childHeadFlags t = [true, false]

instance : DecidablePred IsTrochee := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A minimal φ dominates no φ. -/
def IsMinimalPhi (t : Tree) : Prop := t.value.level = .ph ∧ ∀ c ∈ t.children, c.value.level ≠ .ph

instance : DecidablePred IsMinimalPhi := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

section Penultimate

variable (n : ℕ)

@[simp] theorem level_value_penultimate (k : ℕ) : (penultimate k).value.level = .om := by
  rcases k with _ | _ | n <;> rfl

@[simp] theorem numLeaves_penultimate : (penultimate (n + 2)).numLeaves = n + 2 := by
  simp [penultimate]

theorem spans_penultimate_ph (k : ℕ) : (penultimate k).spans (·.value.level = .ph) = [] := by
  rcases k with _ | _ | n <;>
    simp [penultimate, RoseTree.spansList_append, RoseTree.spansList_replicate]

theorem spans_penultimate_isMinimalPhi (k : ℕ) : (penultimate k).spans IsMinimalPhi = [] := by
  rcases k with _ | _ | n <;>
    simp [penultimate, IsMinimalPhi, RoseTree.spansList_append, RoseTree.spansList_replicate]

theorem spans_penultimate_isTrochee : (penultimate (n + 2)).spans IsTrochee = [(n, n + 2)] := by
  simp [penultimate, RoseTree.spansList_append, RoseTree.spansList_replicate, IsTrochee,
    IsConstituent, Foot.childHeadFlags, RoseTree.licensed_node_iff, Constituent.Licenses,
    Constituent.isHead]

end Penultimate

/-- How a candidate phrases the head and the next word. -/
inductive Phrasing
  /-- Both in one φ. -/
  | joined
  /-- Each in a φ of its own. -/
  | separate
  /-- Each in a φ of its own, with the first syllable after the head lifted into the head's foot. -/
  | lifted
  deriving DecidableEq, Repr, Fintype

namespace Input

variable (x : Input)

/-- The syllables of the word standing for what follows the head: a disyllable when the first
syllable after the head is footed and a trisyllable when it is not, since only the footing of that
syllable bears on the constraints. -/
def next : ℕ := if x.footed then 2 else 3

/-- The parse of the input by a head of `k` syllables under a phrasing, the two φs grouped into one
maximal φ where the next word shares the head's. -/
def parse (k : ℕ) : Phrasing → Tree
  | .joined => .node .iota [Tree.ph [penultimate k, penultimate x.next]]
  | .separate => pair (penultimate k) (penultimate x.next)
  | .lifted => pair (penultimate (k + 1)) (penultimate (x.next - 1))
where
  /-- Two φs, under one maximal φ where the next word shares the head's. -/
  pair (h n : Tree) : Tree :=
    if x.sameMax then .node .iota [Tree.ph [Tree.ph [h], Tree.ph [n]]]
    else .node .iota [Tree.ph [h], Tree.ph [n]]

/-- The cut before word `w`, in syllables, for a head of `k` syllables. -/
def cut (k w : ℕ) : ℕ := ([k, x.next].take w).sum

/-- The stressed syllable of word `w`, its penult (14). -/
def stress (k w : ℕ) : ℕ := x.cut k w + ([k, x.next].getD w 0 - 2)

/-- The phrases in syllables, each with the stressed syllable of the word heading it. -/
def phrases (k : ℕ) : List ((ℕ × ℕ) × ℕ) :=
  x.constituency.phrases.map fun p ↦ ((x.cut k p.1.1, x.cut k p.1.2), x.stress k p.2)

/-- The spans of the morphosyntactic words, the head's `k` syllables and then the next word's. -/
def words (k : ℕ) : List (ℕ × ℕ) := [(0, k), (k, k + x.next)]

end Input

/-- A candidate of GEN. -/
structure Candidate where
  /-- The Vocabulary Item the candidate inserts at the head. -/
  item : Item
  /-- How the candidate phrases the head and the next word. -/
  phrasing : Phrasing
  deriving DecidableEq

section Tableau

variable (v : RuleSet Item) (x : Input)

/-- The parse a candidate gives the input. -/
def Candidate.tree (c : Candidate) : Tree := x.parse (syllables c.item.exponent) c.phrasing

/-- GEN offers each item of `v` applicable to the head in each phrasing, Syllable Lifting only where
the next word shares the head's maximal φ, the domain §4.3 gives it. -/
def candidates : Finset Candidate :=
  ((v.applicable x.neighborhood).flatMap fun i ↦
    ((if x.sameMax then [.joined, .separate, .lifted] else [.joined, .separate]).map
      (⟨i, ·⟩))).toFinset

/-- MAX-XP (23a), evaluated as [ito-mester-2019] evaluate it: one violation for each phrase left
without a φ of its own, a φ containing the phrase's head and no head from outside the phrase, and
answering to one phrase only. -/
def maxXP : Constraint Candidate := fun c ↦
  syntaxProsodyMax (x.phrases (syllables c.item.exponent)) .ph (c.tree x)

/-- SUBCAT (29b): a violation when a second-position element lies in no minimal φ together with the
element before it. -/
def subcat : Constraint Candidate :=
  (Constraint.align fun (w p : ℕ × ℕ) ↦ p.1 < w.1 ∧ w.2 ≤ p.2).comap fun c ↦
    let k := syllables c.item.exponent
    (if x.constituency.subcat then [(k, k + x.next)] else [], (c.tree x).spans IsMinimalPhi)

/-- Positional Minimality (26a), Align-R(φ, (σ́σ)): one violation for each φ whose right edge no
disyllabic trochee shares. -/
def positionalMinimality : Constraint Candidate :=
  Constraint.alignRight.comap fun c ↦ (levelSpans .ph (c.tree x), (c.tree x).spans IsTrochee)

/-- PRIORITY (60a), after [mascaro-2007]: as many violations as the inserted item stands below
the first item of `v` applicable to the head. -/
def priority : Constraint Candidate := fun c ↦ (v.applicable x.neighborhood).idxOf c.item

/-- Match(ω, X⁰) (75a): one violation for each ω that is not the span of a word. -/
def matchOmega : Constraint Candidate := fun c ↦
  prosodySyntaxMatch .om (x.words (syllables c.item.exponent)) (c.tree x)

/-- Match(φ, XP) (23b): one violation for each φ that is not the span of a phrase, the maximal φ
over both words answering to the clause. -/
def matchPhi : Constraint Candidate := fun c ↦
  let k := syllables c.item.exponent
  prosodySyntaxMatch .ph
    ((x.phrases k).map (·.1) ++ if x.sameMax then [(0, k + x.next)] else []) (c.tree x)

/-- The tableau of an input: MAX-XP and SUBCAT over Positional Minimality over PRIORITY over the
Match constraints, as in (26c), (63), (64) and (80). -/
def tableau : Tableau Candidate 6 :=
  Tableau.ofList (candidates v x)
    [maxXP x, subcat x, positionalMinimality x, priority v x, matchOmega x, matchPhi x]

end Tableau

/-! ### The examples -/

/-- An example. -/
structure Row where
  /-- The input at its head. -/
  input : Input
  /-- The allomorph the head takes. -/
  form : Form Wordlist.Cell

/-- The heads by the names the examples give them. -/
def headTable : List (String × Head) :=
  [("this_in_hand", .thisInHand), ("this", .this), ("that", .that), ("neg", .neg), ("what", .what),
    ("which", .which), ("who", .who)]

/-- The configurations by the names the examples give them. -/
def constituencyTable : List (String × Constituency) :=
  [("sisters", .sisters), ("adjunct", .adjunct), ("complement", .complement), ("host", .host)]

/-- The row of an example. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let h ← ex.parse? "head" headTable
  let long ← ex.parse? "allomorph" [("short", false), ("long", true)]
  let s ← ex.parse? "syntax" constituencyTable
  pure ⟨⟨h.neighborhood (ex.feature? "affix" = some "verbalizer"), s,
    ex.feature? "next" ≠ some "unfooted", ex.feature? "maxPhi" = some "same"⟩,
    if long then h.long else h.short⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The rows of the examples. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- **The grammar derives the examples**: in each the optimal candidates insert the attested
allomorph. -/
theorem rows_optimal :
    ∀ d ∈ rows, (tableau vocabulary d.input).optimal.image (·.item.exponent) = {d.form} := by
  decide

/-! ### Suppletion and its suspension -/

/-- **φ-finality follows from the syntax**: the optimal parses phrase the head together with the
next word exactly where the next word heads the head's phrase or is a second-position element it
hosts, and otherwise end the head's φ at the head, as MAX-XP and SUBCAT require ((24)–(26),
(29)). -/
theorem optimal_joined_iff (h : Head) (footed sameMax : Bool) :
    ∀ s ∈ [Constituency.sisters, .adjunct, .complement, .host],
      ∀ c ∈ (tableau vocabulary ⟨h.neighborhood false, s, footed, sameMax⟩).optimal,
        c.phrasing = .joined ↔ (s = .complement ∨ s = .host) := by
  decide +revert +kernel

/-- **The calculus of top-down suppletion** (88): a head takes its marked allomorph exactly where
it ends its φ and Syllable Lifting is unavailable, the next φ beginning with a footed syllable or
lying in another maximal φ. -/
theorem optimal_exponent (h : Head) (footed sameMax : Bool) :
    ∀ s ∈ [Constituency.sisters, .adjunct, .complement, .host],
      (tableau vocabulary ⟨h.neighborhood false, s, footed, sameMax⟩).optimal.image
        (·.item.exponent) = {if (s == .sisters || s == .adjunct) && (footed || !sameMax)
          then h.long else h.short} := by
  decide +revert +kernel

/-- **MAX-XP is load-bearing.** Without it, joining a stranded head's φ with the next word's,
which no tableau of the paper lists, does as well as suppletion on every other constraint and
better on PRIORITY, so under no ranking of the other constraints in which PRIORITY is active is
the suppleted head optimal, against (76a), (77a) and (78a). -/
theorem suppletion_not_optimal_without_maxXP (h : Head) (footed : Bool)
    {Fs : List (Constraint Candidate)}
    (hFs : ∀ F ∈ Fs, F ∈ (fun x ↦ [subcat x, positionalMinimality x, priority vocabulary x,
      matchOmega x, matchPhi x]) ⟨h.neighborhood false, .sisters, footed, true⟩)
    (hp : priority vocabulary ⟨h.neighborhood false, .sisters, footed, true⟩ ∈ Fs) :
    ⟨{Feature.head h} ⟷ h.long, .separate⟩ ∉ (Tableau.ofList
      (candidates vocabulary ⟨h.neighborhood false, .sisters, footed, true⟩) Fs).optimal := by
  set x : Input := ⟨h.neighborhood false, .sisters, footed, true⟩
  have hle : ∀ F ∈ (fun x ↦ [subcat x, positionalMinimality x, priority vocabulary x,
      matchOmega x, matchPhi x]) x,
      F ⟨{Feature.head h} ⟷ h.short, .joined⟩ ≤ F ⟨{Feature.head h} ⟷ h.long, .separate⟩ := by
    cases h <;> cases footed <;> decide
  have hlt : priority vocabulary x ⟨{Feature.head h} ⟷ h.short, .joined⟩ <
      priority vocabulary x ⟨{Feature.head h} ⟷ h.long, .separate⟩ := by
    cases h <;> cases footed <;> decide
  refine Tableau.notMem_optimal_of_lt (c := ⟨{Feature.head h} ⟷ h.short, .joined⟩)
    (by rw [Tableau.ofList_candidates]; cases h <;> cases footed <;> decide)
    (Pi.toLex_strictMono ?_)
  obtain ⟨p, hp⟩ := List.get_of_mem hp
  refine Pi.lt_def.2 ⟨fun q ↦ hle _ (hFs _ (List.get_mem _ _)), p, ?_⟩
  show Fs.get p _ < Fs.get p _
  rw [hp]
  exact hlt

section Priority

variable {v : RuleSet Item} {x : Input} {c : Candidate} {i : Item}

theorem mem_candidates : c ∈ candidates v x ↔
    c.item ∈ v.applicable x.neighborhood ∧ (c.phrasing = .lifted → x.sameMax) := by
  obtain ⟨i, _ | _ | _⟩ := c <;> obtain ⟨n, s, fo, _ | _⟩ := x <;> simp [candidates]

/-- A candidate satisfies PRIORITY exactly when it inserts the first applicable item. -/
theorem priority_eq_zero_iff (hi : (v.applicable x.neighborhood).head? = some i) :
    priority v x c = 0 ↔ c.item = i := by
  obtain ⟨l, hl⟩ := List.head?_eq_some_iff.1 hi
  by_cases h : i = c.item <;> simp [priority, hl, h, eq_comm]

section Configurations

attribute [local simp] maxXP subcat positionalMinimality Candidate.tree syntaxProsodyMax
  Constraint.align Constraint.deficiency List.matchingNumber Input.phrases Input.parse
  Input.parse.pair Input.cut Input.stress Input.next spans_penultimate_ph
  spans_penultimate_isTrochee spans_penultimate_isMinimalPhi IsTrochee IsConstituent
  Foot.childHeadFlags RoseTree.licensed_node_iff Constituent.Licenses IsMinimalPhi Corresponds
  Set.mem_Ico Finset.filter_insert Finset.filter_singleton Finset.sup_insert Finset.sup_singleton

private theorem eq_zero_sisters {a : ℕ} (n : Neighborhood (Finset Feature)) (fo sm : Bool)
    (ha : syllables i.exponent = a + 2) :
    let x : Input := ⟨n, .sisters, fo, sm⟩
    maxXP x ⟨i, .separate⟩ = 0 ∧ subcat x ⟨i, .separate⟩ = 0 ∧
      positionalMinimality x ⟨i, .separate⟩ = 0 := by
  cases fo <;> cases sm <;> simp +arith [ha, Constituency.sisters]

private theorem eq_zero_adjunct {a : ℕ} (n : Neighborhood (Finset Feature)) (fo sm : Bool)
    (ha : syllables i.exponent = a + 2) :
    let x : Input := ⟨n, .adjunct, fo, sm⟩
    maxXP x ⟨i, .separate⟩ = 0 ∧ subcat x ⟨i, .separate⟩ = 0 ∧
      positionalMinimality x ⟨i, .separate⟩ = 0 := by
  cases fo <;> cases sm <;> simp +arith [ha, Constituency.adjunct]

private theorem eq_zero_complement {a : ℕ} (n : Neighborhood (Finset Feature)) (fo sm : Bool)
    (ha : syllables i.exponent = a + 2) :
    let x : Input := ⟨n, .complement, fo, sm⟩
    maxXP x ⟨i, .joined⟩ = 0 ∧ subcat x ⟨i, .joined⟩ = 0 ∧
      positionalMinimality x ⟨i, .joined⟩ = 0 := by
  cases fo <;> cases sm <;> simp +arith [ha, Constituency.complement]

private theorem eq_zero_host {a : ℕ} (n : Neighborhood (Finset Feature)) (fo sm : Bool)
    (ha : syllables i.exponent = a + 2) :
    let x : Input := ⟨n, .host, fo, sm⟩
    maxXP x ⟨i, .joined⟩ = 0 ∧ subcat x ⟨i, .joined⟩ = 0 ∧
      positionalMinimality x ⟨i, .joined⟩ = 0 := by
  cases fo <;> cases sm <;> simp +arith [ha, Constituency.host]

end Configurations

/-- In each of the paper's configurations, a head of at least two syllables has a phrasing that
satisfies MAX-XP, SUBCAT and Positional Minimality: separate φs where the next word heads a phrase
of its own, one φ where it heads the head's phrase or is a second-position element. -/
theorem exists_phrasing_eq_zero
    (hs : x.constituency ∈ [Constituency.sisters, .adjunct, .complement, .host])
    (hk : 2 ≤ syllables i.exponent) :
    ∃ p ≠ Phrasing.lifted, maxXP x ⟨i, p⟩ = 0 ∧ subcat x ⟨i, p⟩ = 0 ∧
      positionalMinimality x ⟨i, p⟩ = 0 := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨n, s, fo, sm⟩ := x
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  exacts [⟨.separate, nofun, eq_zero_sisters n fo sm ha⟩,
    ⟨.separate, nofun, eq_zero_adjunct n fo sm ha⟩, ⟨.joined, nofun, eq_zero_complement n fo sm ha⟩,
    ⟨.joined, nofun, eq_zero_host n fo sm ha⟩]

/-- **Only monosyllables supplete** (§3.3): in each of the paper's configurations, where the first
item of `v` applicable to a head has at least two syllables, every optimal candidate inserts it. -/
theorem optimal_item_eq_of_two_le
    (hs : x.constituency ∈ [Constituency.sisters, .adjunct, .complement, .host])
    (hi : (v.applicable x.neighborhood).head? = some i) (hk : 2 ≤ syllables i.exponent)
    (hc : c ∈ (tableau v x).optimal) : c.item = i := by
  obtain ⟨p, hp, h₁, h₂, h₃⟩ := exists_phrasing_eq_zero hs hk
  have hd : (⟨i, p⟩ : Candidate) ∈ candidates v x :=
    mem_candidates.2 ⟨List.mem_of_mem_head? hi, fun h ↦ absurd h hp⟩
  have z {s : Finset Candidate} {F : Constraint Candidate} (hs : (⟨i, p⟩ : Candidate) ∈ s)
      (h0 : F ⟨i, p⟩ = 0) : (⟨i, p⟩ : Candidate) ∈ s.argmin F :=
    Finset.mem_argmin.2 ⟨hs, fun _ _ ↦ h0.trans_le (Nat.zero_le _)⟩
  rw [tableau, Tableau.optimal_ofList_cons, Tableau.optimal_ofList_cons,
    Tableau.optimal_ofList_cons, Tableau.optimal_ofList_cons] at hc
  obtain ⟨-, hmin⟩ := Finset.mem_argmin.1 (Tableau.optimal_subset hc)
  exact (priority_eq_zero_iff hi).1 (Nat.le_zero.1
    ((hmin _ (z (z (z hd h₁) h₂) h₃)).trans_eq ((priority_eq_zero_iff hi).2 rfl)))

/-- **PRIORITY undominated reduces to selection.** §5, after [bonet-lloret-mascaro-2007], derives
suppletion that is not output-optimizing from PRIORITY ranked over the output constraints. Where
PRIORITY outranks the other constraints and the vocabulary lists its items by non-increasing
specificity, so that PRIORITY's lexical order extends the Subset Principle's, every optimal
candidate inserts the Subset Principle's winner. -/
theorem winner?_eq_some_item_of_mem_optimal
    (hv : v.Pairwise fun i j ↦ j.specificity ≤ i.specificity) {Fs : List (Constraint Candidate)}
    (hc : c ∈ (Tableau.ofList (candidates v x) (priority v x :: Fs)).optimal) :
    winner? v x.neighborhood = some c.item := by
  rw [Tableau.optimal_ofList_cons] at hc
  obtain ⟨hcs, hmin⟩ := Finset.mem_argmin.1 (Tableau.optimal_subset hc)
  rw [winner?_eq_head?_applicable hv]
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1
    (List.isSome_head?.2 (List.ne_nil_of_mem (mem_candidates.1 hcs).1))
  have h0 := hmin _ ((mem_candidates (c := ⟨i, .joined⟩)).2 ⟨List.mem_of_mem_head? hi, by simp⟩)
  rw [(priority_eq_zero_iff (c := ⟨i, .joined⟩) hi).2 rfl, Nat.le_zero,
    priority_eq_zero_iff hi] at h0
  rw [hi, h0]

/-- The Mandar vocabulary under PRIORITY undominated inserts the Subset Principle's winner. -/
theorem winner?_vocabulary_eq_some_item_of_mem_optimal {Fs : List (Constraint Candidate)}
    (hc : c ∈ (Tableau.ofList (candidates vocabulary x) (priority vocabulary x :: Fs)).optimal) :
    winner? vocabulary x.neighborhood = some c.item :=
  winner?_eq_some_item_of_mem_optimal vocabulary_pairwise hc

end Priority

/-! ### Globality -/

section Globality

variable {V : Type*}

private theorem not_exists_of_rows {A : Input → V}
    (h : ∃ d ∈ rows, ∃ e ∈ rows, A d.input = A e.input ∧ d.form ≠ e.form) :
    ¬ ∃ f : V → Form Wordlist.Cell, ∀ d ∈ rows, f (A d.input) = d.form := by
  rintro ⟨f, hf⟩
  obtain ⟨d, hd, e, he, hA, hne⟩ := h
  exact hne ((hf d hd).symm.trans (by rw [hA]; exact hf e he))

/-- **The syntax does not determine the allomorph** ((76)–(78)): no function of a head's
neighborhood and of the syntax of the head and the next word gives the attested allomorphs, a
stranded head taking its marked allomorph before a footed syllable and its unmarked one before an
unfooted one, as in (76a) and (76b). -/
theorem forms_not_function_of_constituency :
    ¬ ∃ f : Neighborhood (Finset Feature) × Constituency → Form Wordlist.Cell,
      ∀ d ∈ rows, f (d.input.neighborhood, d.input.constituency) = d.form :=
  not_exists_of_rows (A := fun x ↦ (x.neighborhood, x.constituency)) (by decide)

/-- **Nor does the next syllable** ((84), (86)): no function of a head's neighborhood, of the syntax
of the head and the next word and of whether the next syllable is footed gives the attested
allomorphs, a stranded demonstrative taking its unmarked allomorph before an unfooted syllable of
its maximal φ and its marked one before an unfooted syllable of the next, as in (86a) and
(86b). -/
theorem forms_not_function_of_footed :
    ¬ ∃ f : Neighborhood (Finset Feature) × Constituency × Bool → Form Wordlist.Cell,
      ∀ d ∈ rows, f (d.input.neighborhood, d.input.constituency, d.input.footed) = d.form :=
  not_exists_of_rows (A := fun x ↦ (x.neighborhood, x.constituency, x.footed)) (by decide)

variable {R : Type*} [Rule R Input (Form Wordlist.Cell)] [DecidableRel (Applies : R → Input → Prop)]
  {κ : Type*} [Preorder κ] [DecidableRel (· < · : κ → κ → Prop)] (w : RuleSet R) (key : R → κ)

private theorem not_realizes_of_not_exists {A : Input → V}
    (h : ¬ ∃ f : V → Form Wordlist.Cell, ∀ d ∈ rows, f (A d.input) = d.form)
    (hw : ∀ r ∈ w, ∀ ⦃x y : Input⦄, A x = A y → (Applies r x ↔ Applies r y)) :
    ¬ ∀ d ∈ rows, w.realizeMinimal key d.input = some d.form := fun hr ↦
  h ⟨fun y ↦ (Function.extend A (w.realizeMinimal key) (fun _ ↦ none) y).getD Head.what.short,
    fun d hd ↦ by
      simp only [(RuleSet.realizeMinimal_factorsThrough hw).extend_apply, hr d hd,
        Option.getD_some]⟩

/-- **No serial Vocabulary Insertion**: no vocabulary inserts the attested allomorphs by the Subset
Principle over the heads' neighborhoods, since a head's neighborhood does not determine its
allomorph. -/
theorem not_subsetPrinciple_eq_forms :
    ¬ ∃ v : RuleSet Item, ∀ d ∈ rows, subsetPrinciple v d.input.neighborhood = some d.form :=
  fun ⟨v, hv⟩ ↦ forms_not_function_of_constituency
    ⟨fun y ↦ (subsetPrinciple v y.1).getD Head.what.short, fun d hd ↦ by simp [hv d hd]⟩

/-- **No selection by the syntax**: no rule set whose rules read of the input only the head's
neighborhood and the syntax of the head and the next word, as the selectional frame (65) reads the
right edge of the head's phrase, inserts the attested allomorphs. -/
theorem not_realizes_of_constituency
    (hw : ∀ r ∈ w, ∀ ⦃x y : Input⦄,
      (x.neighborhood, x.constituency) = (y.neighborhood, y.constituency) →
      (Applies r x ↔ Applies r y)) :
    ¬ ∀ d ∈ rows, w.realizeMinimal key d.input = some d.form :=
  not_realizes_of_not_exists w key (A := fun x ↦ (x.neighborhood, x.constituency))
    forms_not_function_of_constituency hw

/-- **No selection by the next syllable**: no rule set whose rules read of the input only the
head's neighborhood, the syntax of the head and the next word and whether the next syllable is
footed inserts the attested allomorphs. -/
theorem not_realizes_of_footed
    (hw : ∀ r ∈ w, ∀ ⦃x y : Input⦄,
      (x.neighborhood, x.constituency, x.footed) = (y.neighborhood, y.constituency, y.footed) →
      (Applies r x ↔ Applies r y)) :
    ¬ ∀ d ∈ rows, w.realizeMinimal key d.input = some d.form :=
  not_realizes_of_not_exists w key (A := fun x ↦ (x.neighborhood, x.constituency, x.footed))
    forms_not_function_of_footed hw

end Globality

/-! ### C-command -/

section CCommand

open PhraseStructure Core.Order

/-- The categories of the ditransitive clause (90). -/
inductive Cat
  | voice | v | appl | verb | det | noun
  deriving DecidableEq, Repr

/-- The ditransitive clause of (90), the verb raised to Voice over the internal argument, a
demonstrative whose noun phrase is elided, and the applied argument in a rightward specifier of
Appl above it ((89)). The traces of the raised verb and the elided noun phrase are silent leaves;
the silent external argument and the final deictic are left out. -/
def ditransitive (verb o d : String) : PhraseStructure.Tree Cat String :=
  Tree.node .voice [Tree.terminal .voice verb,
    Tree.node .v [Tree.trace 0 .v,
      Tree.node .appl [
        Tree.node .appl [Tree.trace 0 .appl,
          Tree.node .verb [Tree.trace 0 .verb,
            Tree.node .det [Tree.terminal .det o, Tree.trace 1 .noun]]],
        Tree.node .det [Tree.terminal .noun d]]]]

/-- The words of the terminals a position c-commands. -/
def cCommandedWords (t : PhraseStructure.Tree Cat String) (p : TreePath) : List String :=
  (t.positionedTerminals.filter fun x ↦ t.CCommands p x.1).map (·.2.2)

-- The raised verb c-commands both arguments, and the applied argument c-commands the internal
-- argument's demonstrative, which c-commands neither.
example : cCommandedWords (ditransitive "u-kiriŋ-aŋ" "do" "guru-u") ⟨[0]⟩ = ["do", "guru-u"] := by
  decide
example : cCommandedWords (ditransitive "u-kiriŋ-aŋ" "do" "guru-u") ⟨[1, 1, 1, 0]⟩ = ["do"] := by
  decide

/-- The words the head of a ditransitive example c-commands, the clause built from its verb, its
internal argument and its applied argument. -/
def cCommanded? (ex : Datum) : Option (List String) := do
  guard (ex.feature? "clause" = some "ditransitive")
  let verb ← ex.glossedTokens[0]?
  let o ← ex.glossedTokens[2]?
  let d ← ex.glossedTokens[3]?
  let t := ditransitive verb.1 o.1 d.1
  let p ← (t.positionedTerminals.find? (·.2.1 = .det)).map (·.1)
  pure (cCommandedWords t p)

/-- The ditransitive examples, (78a), (78b) and (92), each with the words its head c-commands. -/
def ditransitiveRows : List (Row × List String) :=
  Examples.all.filterMap fun ex ↦ do pure (← Row.ofDatum ex, ← cCommanded? ex)

/-- In the ditransitive examples the stranded demonstrative c-commands no overt word: the applied
argument lies outside its c-command domain. -/
theorem cCommanded_ditransitiveRows : ∀ x ∈ ditransitiveRows, x.2 = [] := by decide

/-- **No c-command-bounded insertion** ((92), §4.3): no function of a head's neighborhood and of
the words it c-commands gives the attested allomorphs, the stranded demonstrative in the internal
argument taking its marked allomorph before *guru* (78a) and its unmarked one before *guru-na*
(78b), the applied argument outside its c-command domain. Vocabulary Insertion that sees only a
head's c-command domain, inserting cyclically from the bottom up, cannot insert them. -/
theorem forms_not_function_of_cCommanded :
    ¬ ∃ f : Neighborhood (Finset Feature) × List String → Form Wordlist.Cell,
      ∀ x ∈ ditransitiveRows, f (x.1.input.neighborhood, x.2) = x.1.form := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hx, y, hy, he, hne⟩ : ∃ x ∈ ditransitiveRows, ∃ y ∈ ditransitiveRows,
      (x.1.input.neighborhood, x.2) = (y.1.input.neighborhood, y.2) ∧ x.1.form ≠ y.1.form := by
    decide
  exact hne ((hf x hx).symm.trans (he ▸ hf y hy))

end CCommand

end Brodkin2026
