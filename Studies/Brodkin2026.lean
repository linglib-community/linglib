module

public import Linglib.Phonology.Prosody.Word
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.OptimalityTheory.Constraint.Alignment
public import Linglib.Core.Data.RoseTree.Span
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Data.Examples.Brodkin2026
public import Linglib.Data.Forms.Brodkin2026
public import Mathlib.Tactic.DeriveFintype

/-!
# Brodkin (2026): suppletion in global perspective

Seven Mandar heads take a monosyllabic allomorph inside a phonological phrase φ and a longer one
at its right edge, because Positional Minimality, Align-R(φ, (σ́σ)), outranks PRIORITY. Where
Syllable Lifting can draw an unfooted syllable from the next φ of the same maximal φ, the
suppletion is suspended, so Vocabulary Insertion reads prosody beyond the head.

## Main definitions

* `vocabulary`: the Vocabulary Items of the heads of (44), with (57a).
* `candidates`, `tableau`: GEN, and the ranking of (64) and (80) over Positional Minimality (26a),
  PRIORITY (60a), Match(ω, X⁰) (75a) and Match(φ, XP) (23b).

## Main results

* `optimal_exponent`: the calculus of top-down suppletion (88).
* `rows_optimal`: the grammar inserts the attested allomorph in every example.
* `optimal_item_eq_of_two_le`: only a monosyllabic unmarked allomorph suppletes.
* `winner?_eq_some_item_of_mem_optimal`: PRIORITY undominated selects the Subset Principle's
  winner.
* `forms_not_function_of_final`, `forms_not_function_of_footed`: neither the φ-edge nor it and
  the footing of the next syllable determine the attested allomorph, so no rule set reading only
  these inserts it (`not_realizes_of_final`, `not_realizes_of_footed`), nor does the Subset
  Principle over the heads' neighborhoods (`not_subsetPrinciple_eq_forms`).

## Implementation notes

* The input stipulates what the paper derives from the syntax: whether the head ends its φ, and
  the phrases Match(φ, XP) reads, each word heading its own and the maximal φ answering to the
  clause. The maximal φ is the paper's domain stipulation on Syllable Lifting (§4.3), stated in
  GEN; an example records it where the paper brackets it or the clause has at most three words
  (85).
* A parse is built from the syllable count of the inserted form, its vowels in
  `Data.Forms.Brodkin2026`, whose 'who' forms are the surface forms of (42); what follows the head
  is a word whose first syllable is footed or unfooted under penultimate stress (14), (15).

## TODO

* Derive the φ-phrasing from a syntactic input under MAX-XP, HEADEDNESS and SUBCAT (§2.3–§2.4,
  (63)), and state the c-command argument of (92) over it.
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
-/

@[expose] public section

namespace Brodkin2026

open Prosody OptimalityTheory DistributedMorphology Morphology.Exponence Data.Forms

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
def short : Head → Form Forms.Cell
  | thisInHand => Forms.this_in_hand_short | this => Forms.this_short | that => Forms.that_short
  | neg => Forms.neg_short | what => Forms.what_short | which => Forms.which_short
  | who => Forms.who_short

/-- A head's marked allomorph, its φ-final form in (44). -/
def long : Head → Form Forms.Cell
  | thisInHand => Forms.this_in_hand_long | this => Forms.this_long | that => Forms.that_long
  | neg => Forms.neg_long | what => Forms.what_long | which => Forms.which_long
  | who => Forms.who_long

/-- The neighborhood of a head, with a v⁰ one terminal toward the clause or not. -/
def neighborhood (h : Head) (verbalized : Bool) : Neighborhood (Finset Feature) :=
  ⟨{.head h}, [], if verbalized then [{.cat .v}] else []⟩

end Head

/-- The pairs of the heads are the top-down suppletion relations of the forms table. -/
theorem relations_eq : Forms.relations.map (fun r ↦ (r.form, r.target)) =
    [.thisInHand, .this, .that, .neg, .what, .which, .who].map fun h : Head ↦ (h.short, h.long) :=
  rfl

/-- The syllables of a form of (44), one to each vowel. -/
def syllables (f : Form Forms.Cell) : ℕ := f.segments.countP (· ∈ ["a", "e", "i", "o", "u"])

/-- Each unmarked allomorph is a monosyllable and each marked one longer. -/
theorem syllables_short_long (h : Head) : syllables h.short = 1 ∧ 2 ≤ syllables h.long := by
  cases h <;> decide

/-- A Vocabulary Item inserts a form of (44). -/
abbrev Item := VocabularyItem Feature (Form Forms.Cell)

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

/-- The input at a head. -/
structure Input where
  /-- The head and its morphosyntactic neighbors. -/
  neighborhood : Neighborhood (Finset Feature)
  /-- The head ends its φ. -/
  final : Bool
  /-- The first syllable after the head is footed. -/
  footed : Bool
  /-- The next φ shares the head's maximal φ. -/
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

section Penultimate

variable (n : ℕ)

@[simp] theorem numLeaves_penultimate : (penultimate (n + 2)).numLeaves = n + 2 := by
  simp [penultimate]

theorem spans_penultimate_ph (k : ℕ) : (penultimate k).spans (·.value.level = .ph) = [] := by
  rcases k with _ | _ | n <;>
    simp [penultimate, RoseTree.spansList_append, RoseTree.spansList_replicate]

theorem spans_penultimate_isTrochee : (penultimate (n + 2)).spans IsTrochee = [(n, n + 2)] := by
  simp [penultimate, RoseTree.spansList_append, RoseTree.spansList_replicate, IsTrochee,
    IsConstituent, Foot.childHeadFlags, RoseTree.licensed_node_iff, Constituent.Licenses,
    Constituent.isHead]

end Penultimate

namespace Input

variable (x : Input)

/-- The syllables of the word standing for what follows the head: a disyllable when the first
syllable after the head is footed and a trisyllable when it is not, since only the footing of that
syllable bears on the constraints. -/
def next : ℕ := if x.footed then 2 else 3

/-- The parse of the input by a head of `k` syllables, with Syllable Lifting or without. -/
def parse (k : ℕ) (lift : Bool) : Tree :=
  if x.final then
    let h := if lift then penultimate (k + 1) else penultimate k
    let n := if lift then penultimate (x.next - 1) else penultimate x.next
    if x.sameMax then .node .iota [Tree.ph [Tree.ph [h], Tree.ph [n]]]
    else .node .iota [Tree.ph [h], Tree.ph [n]]
  else .node .iota [Tree.ph [penultimate k, penultimate x.next]]

/-- The spans of the morphosyntactic words, the head's `k` syllables and then the next word's. -/
def words (k : ℕ) : List (ℕ × ℕ) := [(0, k), (k, k + x.next)]

end Input

/-- A candidate of GEN. -/
structure Candidate where
  /-- The Vocabulary Item the candidate inserts at the head. -/
  item : Item
  /-- The candidate lifts the first syllable after the head into the head's foot. -/
  lift : Bool
  deriving DecidableEq

section Tableau

variable (v : RuleSet Item) (x : Input)

/-- The parse a candidate gives the input. -/
def Candidate.tree (c : Candidate) : Tree := x.parse (syllables c.item.exponent) c.lift

/-- GEN offers each item of `v` applicable to the head, with Syllable Lifting where the head ends
its φ and the next φ lies in its maximal φ, the domain §4.3 gives Syllable Lifting. -/
def candidates : Finset Candidate :=
  ((v.applicable x.neighborhood).flatMap fun i ↦
    (if x.final && x.sameMax then [false, true] else [false]).map (⟨i, ·⟩)).toFinset

/-- Positional Minimality (26a), Align-R(φ, (σ́σ)): one violation for each φ whose right edge no
disyllabic trochee shares. -/
def positionalMinimality : Constraint Candidate :=
  (Constraint.align fun a b : ℕ × ℕ ↦ a.2 = b.2).comap fun c ↦
    ((c.tree x).spans (·.value.level = .ph), (c.tree x).spans IsTrochee)

/-- PRIORITY (60a), after [mascaro-2007]: as many violations as the inserted item stands below
the first item of `v` applicable to the head. -/
def priority : Constraint Candidate := fun c ↦ (v.applicable x.neighborhood).idxOf c.item

/-- Match(ω, X⁰) (75a): one violation for each ω that is not the span of a word. -/
def matchOmega : Constraint Candidate :=
  (Constraint.align Eq).comap fun c ↦
    ((c.tree x).spans (·.value.level = .om), x.words (syllables c.item.exponent))

/-- Match(φ, XP) (23b): one violation for each φ that is not the span of a phrase, each word
heading its own and the maximal φ, where the two words share it, answering to the clause. -/
def matchPhi : Constraint Candidate :=
  (Constraint.align Eq).comap fun c ↦
    let k := syllables c.item.exponent
    ((c.tree x).spans (·.value.level = .ph),
      (if x.final && x.sameMax then [(0, k + x.next)] else []) ++ x.words k)

/-- The tableau of an input: Positional Minimality over PRIORITY over the Match constraints, as
in (64) and (80). -/
def tableau : Tableau Candidate 4 :=
  Tableau.ofList (candidates v x)
    [positionalMinimality x, priority v x, matchOmega x, matchPhi x]

end Tableau

/-! ### The examples -/

/-- An example. -/
structure Row where
  /-- The input at its head. -/
  input : Input
  /-- The allomorph the head takes. -/
  form : Form Forms.Cell

/-- The heads by the names the examples give them. -/
def headTable : List (String × Head) :=
  [("this_in_hand", .thisInHand), ("this", .this), ("that", .that), ("neg", .neg), ("what", .what),
    ("which", .which), ("who", .who)]

/-- The row of an example. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let h ← ex.parse? "head" headTable
  let long ← ex.parse? "allomorph" [("short", false), ("long", true)]
  let final ← ex.parse? "position" [("medial", false), ("final", true)]
  pure ⟨⟨h.neighborhood (ex.feature? "affix" = some "verbalizer"), final,
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

/-- **The calculus of top-down suppletion** (88): a head takes its marked allomorph exactly at the
right edge of its φ where Syllable Lifting is unavailable, the next φ beginning with a footed
syllable or lying in another maximal φ. -/
theorem optimal_exponent (h : Head) (final footed sameMax : Bool) :
    (tableau vocabulary ⟨h.neighborhood false, final, footed, sameMax⟩).optimal.image
      (·.item.exponent) = {if final && (footed || !sameMax) then h.long else h.short} := by
  decide +revert

section Priority

variable {v : RuleSet Item} {x : Input} {c : Candidate} {i : Item}

theorem mem_candidates :
    c ∈ candidates v x ↔ c.item ∈ v.applicable x.neighborhood ∧ (c.lift → x.final ∧ x.sameMax) := by
  obtain ⟨i, _ | _⟩ := c <;> obtain ⟨n, _ | _, fo, _ | _⟩ := x <;> simp [candidates]

/-- A candidate satisfies PRIORITY exactly when it inserts the first applicable item. -/
theorem priority_eq_zero_iff (hi : (v.applicable x.neighborhood).head? = some i) :
    priority v x c = 0 ↔ c.item = i := by
  obtain ⟨l, hl⟩ := List.head?_eq_some_iff.1 hi
  by_cases h : i = c.item <;> simp [priority, hl, h, eq_comm]

/-- An item of at least two syllables, inserted without lifting, satisfies Positional
Minimality. -/
theorem positionalMinimality_eq_zero_of_two_le (x : Input) (hk : 2 ≤ syllables i.exponent) :
    positionalMinimality x ⟨i, false⟩ = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨m, hm⟩ : ∃ m, x.next = m + 2 := by unfold Input.next; split; exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  simp only [positionalMinimality, Constraint.comap_apply, Candidate.tree, hn, Input.parse, hm,
    Constraint.align_eq_zero_iff]
  cases x.final <;> cases x.sameMax <;>
    simp [spans_penultimate_ph, spans_penultimate_isTrochee, IsTrochee, IsConstituent,
      Foot.childHeadFlags, RoseTree.licensed_node_iff, Constituent.Licenses] <;> omega

/-- **Only monosyllables supplete** (§3.3): where the first item of `v` applicable to a head has
at least two syllables, every optimal candidate under Positional Minimality over PRIORITY inserts
it, whatever the head's context and the constraints below. -/
theorem optimal_item_eq_of_two_le (hi : (v.applicable x.neighborhood).head? = some i)
    (hk : 2 ≤ syllables i.exponent) {Fs : List (Constraint Candidate)}
    (hc : c ∈ (Tableau.ofList (candidates v x)
      (positionalMinimality x :: priority v x :: Fs)).optimal) : c.item = i := by
  rw [Tableau.optimal_ofList_cons, Tableau.optimal_ofList_cons] at hc
  obtain ⟨-, hmin⟩ := Finset.mem_argmin.1 (Tableau.optimal_subset hc)
  have hd : (⟨i, false⟩ : Candidate) ∈ (candidates v x).argmin (positionalMinimality x) :=
    Finset.mem_argmin.2 ⟨(mem_candidates (c := ⟨i, false⟩)).2 ⟨List.mem_of_mem_head? hi, by simp⟩,
      fun _ _ ↦ (positionalMinimality_eq_zero_of_two_le x hk).trans_le (Nat.zero_le _)⟩
  exact (priority_eq_zero_iff hi).1
    (Nat.le_zero.1 ((hmin _ hd).trans_eq ((priority_eq_zero_iff hi).2 rfl)))

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
  have h0 := hmin _ ((mem_candidates (c := ⟨i, false⟩)).2 ⟨List.mem_of_mem_head? hi, by simp⟩)
  rw [(priority_eq_zero_iff (c := ⟨i, false⟩) hi).2 rfl, Nat.le_zero,
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
    ¬ ∃ f : V → Form Forms.Cell, ∀ d ∈ rows, f (A d.input) = d.form := by
  rintro ⟨f, hf⟩
  obtain ⟨d, hd, e, he, hA, hne⟩ := h
  exact hne ((hf d hd).symm.trans (by rw [hA]; exact hf e he))

/-- **The φ-edge does not determine the allomorph** ((76)–(78)): no function of a head's
neighborhood and of whether it ends its φ gives the attested allomorphs, a φ-final head taking its
marked allomorph before a footed syllable and its unmarked one before an unfooted one, as in (76a)
and (76b). -/
theorem forms_not_function_of_final :
    ¬ ∃ f : Neighborhood (Finset Feature) × Bool → Form Forms.Cell,
      ∀ d ∈ rows, f (d.input.neighborhood, d.input.final) = d.form :=
  not_exists_of_rows (A := fun x ↦ (x.neighborhood, x.final)) (by decide)

/-- **Nor does the next syllable** ((84), (86)): no function of a head's neighborhood, of whether
it ends its φ and of whether the next syllable is footed gives the attested allomorphs, a stranded
demonstrative taking its unmarked allomorph before an unfooted syllable of its maximal φ and its
marked one before an unfooted syllable of the next, as in (86a) and (86b). -/
theorem forms_not_function_of_footed :
    ¬ ∃ f : Neighborhood (Finset Feature) × Bool × Bool → Form Forms.Cell,
      ∀ d ∈ rows, f (d.input.neighborhood, d.input.final, d.input.footed) = d.form :=
  not_exists_of_rows (A := fun x ↦ (x.neighborhood, x.final, x.footed)) (by decide)

variable {R : Type*} [Rule R Input (Form Forms.Cell)] [Preorder R]
  [DecidableRel (Applies : R → Input → Prop)] [DecidableRel (· < · : R → R → Prop)]
  (w : RuleSet R)

private theorem not_realizes_of_not_exists {A : Input → V}
    (h : ¬ ∃ f : V → Form Forms.Cell, ∀ d ∈ rows, f (A d.input) = d.form)
    (hw : ∀ r ∈ w, ∀ ⦃x y : Input⦄, A x = A y → (Applies r x ↔ Applies r y)) :
    ¬ ∀ d ∈ rows, w.realizeMinimal d.input = some d.form := fun hr ↦
  h ⟨fun y ↦ (Function.extend A w.realizeMinimal (fun _ ↦ none) y).getD Head.what.short,
    fun d hd ↦ by
      simp only [(RuleSet.realizeMinimal_factorsThrough hw).extend_apply, hr d hd, Option.getD_some]⟩

/-- **No serial Vocabulary Insertion**: no vocabulary inserts the attested allomorphs by the Subset
Principle over the heads' neighborhoods, since a head's neighborhood does not determine its
allomorph. -/
theorem not_subsetPrinciple_eq_forms :
    ¬ ∃ v : RuleSet Item, ∀ d ∈ rows, subsetPrinciple v d.input.neighborhood = some d.form :=
  fun ⟨v, hv⟩ ↦ forms_not_function_of_final
    ⟨fun y ↦ (subsetPrinciple v y.1).getD Head.what.short, fun d hd ↦ by simp [hv d hd]⟩

/-- **No selection by the φ-edge**: no rule set whose rules read of the input only the head's
neighborhood and whether it ends its φ, as the selectional frame (65) does, inserts the attested
allomorphs. -/
theorem not_realizes_of_final
    (hw : ∀ r ∈ w, ∀ ⦃x y : Input⦄, (x.neighborhood, x.final) = (y.neighborhood, y.final) →
      (Applies r x ↔ Applies r y)) :
    ¬ ∀ d ∈ rows, w.realizeMinimal d.input = some d.form :=
  not_realizes_of_not_exists w (A := fun x ↦ (x.neighborhood, x.final))
    forms_not_function_of_final hw

/-- **No selection by the next syllable**: no rule set whose rules read of the input only the
head's neighborhood, whether it ends its φ and whether the next syllable is footed inserts the
attested allomorphs. -/
theorem not_realizes_of_footed
    (hw : ∀ r ∈ w, ∀ ⦃x y : Input⦄,
      (x.neighborhood, x.final, x.footed) = (y.neighborhood, y.final, y.footed) →
      (Applies r x ↔ Applies r y)) :
    ¬ ∀ d ∈ rows, w.realizeMinimal d.input = some d.form :=
  not_realizes_of_not_exists w (A := fun x ↦ (x.neighborhood, x.final, x.footed))
    forms_not_function_of_footed hw

end Globality

end Brodkin2026
