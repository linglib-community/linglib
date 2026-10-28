module

public import Linglib.Semantics.Tense.Reichenbach
public import Linglib.Syntax.Category.Verb.Tense
public import Linglib.Data.Examples.Reichenbach1947
public import Mathlib.Data.Fintype.Prod

/-!
# Reichenbach (1947): the tenses of verbs

[reichenbach-1947] analyses a tense by the order of three time points, the point of speech S, the
point of reference R and the point of the event E. The three points can be ordered in thirteen
ways. He groups the orders that agree on how R stands to S and how E stands to R into nine
fundamental forms, since the position of E relative to S is usually irrelevant: R is past, present
or future relative to S, and E is anterior, simple or posterior relative to R. A fundamental form
groups more than one order exactly when it is [retrogressive](##one_lt_card_comp_iff), the
direction from S to R opposite to the direction from R to E, as in the posterior past and the
anterior future.

An English tense form [takes the fundamental forms of Reichenbach's table](##readings): the
extended forms, whose lexical verb is a present participle, take those of the plain forms, the
simple future takes two, $S, R — E$ and $S — R, E$, and *would do* is the posterior past.

The point of reference carries the time position of a clause. A time determination, an adverb such
as *now* or a comparison of clauses by *when* or *before*, refers to the point of reference and not
to the event, and the clauses of a compound sentence keep one point of reference unless such a
comparison relates them otherwise. On dense time a sentence can be placed on the time line under
these rules [exactly when its fundamental forms are coherent](##realizable_iff), which under the
permanence of the reference point is [agreement on the position of R relative to
S](##coherent_iff_of_permanent). The paper's sentences are coherent [exactly when it accepts
them](##rows_coherent), and the permanence of the reference point [decides all but one of them
alike](##permanent_iff_except_five): *he was healthier when I saw him than he is now*, whose points
of reference differ, needs the more general positional use.

## Implementation notes

* The frames of the clauses are `ReichenbachFrame.root` frames, the perspective at the point of
  speech, and the extension of an event in the extended tenses is lost on points.
* A connective is the cell in which it places the point of reference of the first clause relative
  to that of the clause it introduces. *When* and *now that* are the identity, *before* is
  precedence, the complementizer *that* and the question word *which* join their clauses under the
  permanence of the reference point, and *than* in (5), comparing states, relates no times.
* The diagrams of the table of tenses are recorded in the dash notation of the table of
  fundamental forms.

## TODO

The future clause with a present or present perfect *when*-clause, in which Reichenbach takes the
point of speech of the second clause to be neglected, is not modelled. The rule accepts these
sentences only through the posterior-present reading of the future, which places the event of the
*when*-clause at the point of speech; Reichenbach's account needs that event to lie in the future.

## References

* [reichenbach-1947]
-/

@[expose] public section

namespace Reichenbach1947

open Tense
open scoped Denotes

/-! ### Orders and fundamental forms -/

/-- The fundamental form of the points `s`, `r` and `e`: how the point of reference stands to the
point of speech, and how the point of the event stands to the point of reference. -/
def fundamentalForm {T : Type*} [LinearOrder T] (s r e : T) : Ordering × Ordering :=
  ((ReichenbachFrame.root s r e).referencePosition, (ReichenbachFrame.root s r e).eventPosition)

@[simp] theorem fundamentalForm_eq {T : Type*} [LinearOrder T] (s r e : T) :
    fundamentalForm s r e = (compare r s, compare e r) := rfl

/-- An order of S, R and E is recorded as the comparisons of R with S, of E with R and of E with S,
the last one that the composition of the first two allows. -/
def structures : Finset (Ordering × Ordering × Ordering) :=
  Finset.univ.filter fun x ↦ x.2.2 ∈ x.2.1.comp x.1

theorem mem_structures {T : Type*} [LinearOrder T] (s r e : T) :
    ((fundamentalForm s r e).1, (fundamentalForm s r e).2, compare e s) ∈ structures :=
  Finset.mem_filter.2
    ⟨Finset.mem_univ _, (ReichenbachFrame.root s r e).compare_eventTime_perspectiveTime_mem⟩

theorem exists_points :
    ∀ x ∈ structures, ∃ s r e : Fin 3, (compare r s, compare e r, compare e s) = x := by
  decide

-- p. 296
theorem card_structures : structures.card = 13 := by decide

-- p. 296
theorem card_fundamentalForms : (structures.image fun x ↦ (x.1, x.2.1)).card = 9 := by decide

theorem card_filter_form (a b : Ordering) :
    (structures.filter fun x ↦ x.1 = a ∧ x.2.1 = b).card = (b.comp a).card := by
  revert a b; decide

/-- More than one order obtains only for the posterior past and the anterior future (p. 297). -/
theorem one_lt_card_comp_iff (a b : Ordering) :
    1 < (b.comp a).card ↔ (a = .lt ∧ b = .gt) ∨ (a = .gt ∧ b = .lt) := by
  revert a b; decide

/-! ### The tenses of English -/

/-- The fundamental forms of an English tense form: those of the table of tenses for the six tenses
and, the extension of the event aside, for their extended forms; the simple future also has the
form $S — R, E$; and *would do* is the posterior past. -/
def readings (f : Form) : Finset (Ordering × Ordering) :=
  match f.finite, f.nonfinite.filter (· != .presentParticiple) with
  | .past, [] => {(.lt, .eq)}
  | .past, [.pastParticiple] => {(.lt, .lt)}
  | .past, [.infinitive] => {(.lt, .gt)}
  | .present, [] => {(.eq, .eq)}
  | .present, [.pastParticiple] => {(.eq, .lt)}
  | .present, [.infinitive] => {(.eq, .gt), (.gt, .eq)}
  | .present, [.infinitive, .pastParticiple] => {(.gt, .lt)}
  | _, _ => ∅

theorem readings_extended (f : Form) :
    readings { f with nonfinite := f.nonfinite ++ [.presentParticiple] } = readings f := by
  simp [readings, List.filter_append]

/-- A tense form by Reichenbach's name for it, and the conditional *would do*. -/
def form? (name : String) : Option Form :=
  [("Past Perfect", Form.pastPerfect), ("Simple Past", .simplePast),
    ("Present Perfect", .presentPerfect), ("Present", .simplePresent), ("Simple Future", .future),
    ("Future Perfect", .futurePerfect), ("Conditional", Form.simplePast.under .infinitive),
    ("Past Perfect, Extended", Form.pastProgressive.perfect),
    ("Simple Past, Extended", .pastProgressive),
    ("Present Perfect, Extended", Form.presentProgressive.perfect),
    ("Present, Extended", .presentProgressive),
    ("Simple Future, Extended", Form.presentProgressive.under .infinitive),
    ("Future Perfect, Extended", Form.presentProgressive.perfect.under .infinitive)].lookup name

/-- The fundamental form of a structure written as `E—R—S` or `S, R—E`, a dash placing the points
after it later and a comma keeping them together. -/
def structure? (str : String) : Option (Ordering × Ordering) := do
  let step : ℕ × List (Char × ℕ) → Char → ℕ × List (Char × ℕ)
    | (g, l), '—' => (g + 1, l)
    | (g, l), c => if c = 'S' ∨ c = 'R' ∨ c = 'E' then (g, (c, g) :: l) else (g, l)
  let l := (str.toList.foldl step (0, [])).2
  guard (l.length = 3)
  return fundamentalForm (← l.lookup 'S') (← l.lookup 'R') (← l.lookup 'E')

/-! ### The positional use of the reference point -/

/-- A clause of a sentence: its tense form, the cell in which a time determination such as *now*
places its point of reference relative to the point of speech, and the cell in which its connective
places the point of reference of the first clause relative to its own. -/
structure Clause where
  /-- The tense form of the clause. -/
  form : Form
  /-- The positions its time determination allows its point of reference, every position when it
  has none. -/
  adverb : Finset Ordering := ⊤
  /-- The positions its connective allows the point of reference of the first clause, the identity
  under the permanence of the reference point. -/
  link : Finset Ordering := ⟦present⟧

namespace Clause

/-- The fundamental forms a clause may take: the readings of its form whose point of reference
stands where its time determination places it. -/
def positions (c : Clause) : Finset (Ordering × Ordering) :=
  (readings c.form).filter (·.1 ∈ c.adverb)

/-- The clause joined to the first under the permanence of the reference point. -/
def permanent (c : Clause) : Clause := { c with link := ⟦present⟧ }

end Clause

/-- A sentence of a first clause `c` and further clauses `cs` is realizable on the time line `T`
when its clauses can be placed at one point of speech, each in one of its fundamental forms, with
the point of reference of the first standing to each other's as their connective says. -/
def Realizable (T : Type*) [LinearOrder T] (c : Clause) (cs : List Clause) : Prop :=
  ∃ s r₀ e₀ : T, fundamentalForm s r₀ e₀ ∈ c.positions ∧
    ∀ d ∈ cs, ∃ r e : T, fundamentalForm s r e ∈ d.positions ∧ compare r₀ r ∈ d.link

/-- A sentence is coherent when the first clause has a fundamental form whose point of reference
reaches that of each other clause through its connective. -/
def Coherent (c : Clause) (cs : List Clause) : Prop :=
  ∃ x ∈ c.positions, ∀ d ∈ cs, ∃ y ∈ d.positions, x.1 ∈ comp d.link {y.1}

instance (c : Clause) (cs : List Clause) : Decidable (Coherent c cs) :=
  inferInstanceAs (Decidable (∃ x ∈ c.positions, ∀ d ∈ cs, _))

variable {T : Type*} [LinearOrder T] {c : Clause} {cs : List Clause}

theorem Realizable.coherent (h : Realizable T c cs) : Coherent c cs := by
  obtain ⟨s, r₀, e₀, h₀, h⟩ := h
  refine ⟨_, h₀, fun d hd ↦ ?_⟩
  obtain ⟨r, e, hf, hl⟩ := h d hd
  exact ⟨_, hf, compare_mem_comp hl (Finset.mem_singleton_self _)⟩

private theorem exists_compare_eq [NoMinOrder T] [NoMaxOrder T] (o : Ordering) (a : T) :
    ∃ b, compare b a = o := by
  cases o
  · exact (exists_lt a).imp fun _ ↦ compare_lt_iff_lt.2
  · exact ⟨a, compare_eq_iff_eq.2 rfl⟩
  · exact (exists_gt a).imp fun _ ↦ compare_gt_iff_gt.2

/-- On dense time without endpoints a sentence is realizable exactly when it is coherent: the
connectives and time determinations constrain the points of reference and nothing else. -/
theorem realizable_iff [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] [Nonempty T] :
    Realizable T c cs ↔ Coherent c cs := by
  refine ⟨Realizable.coherent, fun ⟨x, hx, h⟩ ↦ ?_⟩
  obtain ⟨s⟩ := ‹Nonempty T›
  obtain ⟨r₀, hr₀⟩ := exists_compare_eq x.1 s
  obtain ⟨e₀, he₀⟩ := exists_compare_eq x.2 r₀
  refine ⟨s, r₀, e₀, by simpa [hr₀, he₀] using hx, fun d hd ↦ ?_⟩
  obtain ⟨y, hy, hk⟩ := h d hd
  rw [← hr₀] at hk
  obtain ⟨r, hl, hr⟩ := compare_mem_comp_iff.1 hk
  obtain ⟨e, he⟩ := exists_compare_eq y.2 r
  exact ⟨r, e, by simpa [Finset.mem_singleton.1 hr, he] using hy, hl⟩

/-- Under the permanence of the reference point a sentence is coherent exactly when its clauses
can agree on how their point of reference stands to the point of speech. -/
theorem coherent_iff_of_permanent (h : ∀ d ∈ cs, d.link = ⟦present⟧) :
    Coherent c cs ↔ ∃ x ∈ c.positions, ∀ d ∈ cs, ∃ y ∈ d.positions, y.1 = x.1 := by
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ forall₂_congr fun d hd ↦ ?_
  simp only [h d hd, comp_present_left, Finset.mem_singleton]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦ eq_comm

/-! ### The sentences -/

/-- The cell in which an adverb places a point of reference relative to the point of speech. -/
def adverb? (w : String) : Option (Finset Ordering) :=
  [("now", ⟦present⟧), ("tomorrow", ⟦future⟧)].lookup w

/-- The cell in which a connective places the point of reference of the first clause relative to
that of the clause it introduces. -/
def link? (w : String) : Option (Finset Ordering) :=
  [("when", ⟦present⟧), ("now that", ⟦present⟧), ("which", ⟦present⟧), ("that", ⟦present⟧),
    ("before", ⟦past⟧), ("than", ⊤)].lookup w

/-- The clauses of a row: its tense forms in order, the first taking the row's adverb and the
others its connectives in order. Rows whose second clause neglects the point of speech are not
read. -/
def sentence? (row : Datum) : Option (Clause × List Clause) := do
  guard (row.feature? "pointOfSpeech" ≠ some "neglected")
  let f :: fs ← (row.features "form").mapM form? | none
  let ls ← (row.features "link").mapM link?
  guard (ls.length = fs.length)
  let a ← (row.feature? "adverb").elim (some ⊤) adverb?
  return (⟨f, a, ⟦present⟧⟩, fs.zipWith (fun g l ↦ ⟨g, ⊤, l⟩) ls)

/-- Every row is acceptable exactly when its sentence is coherent. -/
theorem rows_coherent :
    Datum.Checks sentence? (fun x ↦ .ofProp (Coherent x.1 x.2)) Examples.all 23 := by
  decide +kernel

/-- The clauses of the rows paired with the diagrams the paper prints for them. -/
def diagrams : List (Clause × String) :=
  Examples.all.flatMap fun row ↦
    (sentence? row).toList.flatMap fun x ↦ (x.1 :: x.2).zip (row.features "structure")

theorem diagrams_mem_positions :
    (∀ p ∈ diagrams, ∃ y ∈ structure? p.2, y ∈ p.1.positions) ∧ diagrams.length = 26 := by
  decide +kernel

/-- The permanence of the reference point decides every row as its positional use does, except
(5), which is coherent only by the positional use. -/
theorem permanent_iff_except_five :
    ∀ row ∈ Examples.all, ∀ x ∈ sentence? row,
      (Coherent x.1 (x.2.map Clause.permanent) ↔ Coherent x.1 x.2 ∧ row ≠ Examples.ex_5) := by
  decide +kernel

end Reichenbach1947
