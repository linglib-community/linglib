module

public import Linglib.Phonology.Hiatus.Elision
public import Linglib.Phonology.OptimalityTheory.PositionalFaithfulness
public import Linglib.Data.Hiatus.Casali1997

/-!
# Casali (1997): Vowel Elision in Hiatus Contexts: Which Vowel Goes?

Casali observes that elision of the first of two vowels in hiatus is possible everywhere, while
elision of the second is found only where a lexical word or root precedes a function word or
suffix. He derives this from MAX constraints that protect segments in prominent positions: the
beginning of a word, a lexical word or root, the beginning of a morpheme, and a morpheme of one
segment. An elision deletes one vowel, so it violates the constraints that protect the position of
that vowel, and an elision can be optimal exactly when the constraints it violates are not a
proper superset of those the other elision violates.

## Main definitions

* `con`: Casali's constraints, MAX restricted to each prominent position and general MAX, on the
  two elisions.
* `violations`: the constraints an elision violates, a row of the paper's table of violations.
* `tableau`: the tableau of the two elisions under a ranking.

## Main results

* `exists_mem_optimal_iff`: an elision is optimal under some ranking iff the constraints it
  violates are not a proper superset of those the other elision violates.
* `exists_mem_optimal_second_iff`: where the first vowel begins no morpheme, the second can
  elide iff the first morph is a root and the second is not.
* `survey_allowed`, `survey_second_iff`: every elision the survey of Section 2 reports is
  allowed, and the survey reports an elision of the second vowel at exactly the kinds of juncture
  where one is allowed.

## Implementation notes

* The constraints are indexed by `Option Prominence`: `some p` is MAX restricted to the position
  `p`, and `none` is general MAX (`con_none`). Every elision violates general MAX once, so it
  never decides between them, and the universal ranking of the positional constraints above it
  is not imposed.
* Lexical status and word boundaries are read off the kinds of the two morphs: roots are lexical,
  and affixes, clitics and free function words are not.
* A word-initial vowel is also morpheme-initial, so the second vowel violates the
  morpheme-initial constraint at a word boundary too, which the paper's table of violations
  leaves out and which changes no prediction.
* `schematic k` is the paper's schematic juncture `/CV₁ + V₂C/` at the survey's kind `k`, with
  `C` and `V` the natural classes [+consonantal] and [+syllabic]; it witnesses that every kind of
  juncture has a context.

## References

* [casali-1997]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace Casali1997

open Phonology Phonology.Hiatus OptimalityTheory Morphology
open Data.Hiatus (ElidedVowel)

variable (c : Context)

/-- `position c e` is the position of the vowel that `e` elides. -/
def position : ElidedVowel → ℕ
  | .first => c.v1Idx
  | .second => c.v2Idx

theorem position_lt_length_input (e : ElidedVowel) : position c e < c.input.length := by
  cases e
  exacts [c.v1Idx_lt_length_input, c.v2Idx_lt_length_input]

/-- `protects c i k` holds when the constraint `i` protects position `k`. General MAX (`none`)
protects every position, and MAX restricted to a prominent position (`some p`) the positions that
lie in it. -/
def protects : Option Prominence → ℕ → Prop
  | none, _ => True
  | some p, k => c.Protects p k

instance (i : Option Prominence) : DecidablePred (protects c i) := fun _ ↦ by
  cases i <;> unfold protects <;> infer_instance

/-- Casali's constraints on the two elisions, each of which deletes the position of the elided
vowel. -/
def con : ConstraintSet ElidedVowel (Option Prominence) :=
  positionalMax (protects c) fun e ↦ {position c e}

/-- `corr c e` is the correspondence between the unrepaired concatenation and the form that the
elision `e` gives. -/
def corr (e : ElidedVowel) : Correspondence BinaryRole Segment :=
  Correspondence.eraseIdx c.input (position c e)

/-- `resolve c e` is the form that the elision `e` gives. -/
def resolve (e : ElidedVowel) : List Segment := (corr c e).form .rhs

theorem resolve_first : resolve c .first = c.elideV1 := c.elideV1_eq_eraseIdx.symm

theorem resolve_second : resolve c .second = c.elideV2 := c.elideV2_eq_eraseIdx.symm

/-- Each constraint counts the input segments it protects that have no correspondent in the
output. -/
theorem con_eq_maxViolAt (i : Option Prominence) (e : ElidedVowel) :
    con c i e = (corr c e).maxViolAt (protects c i) .lhs .rhs :=
  maxAt_singleton_eq_maxViolAt _ (position_lt_length_input c e)

/-- General MAX counts the input segments that have no correspondent in the output. -/
theorem con_none (e : ElidedVowel) : con c none e = (corr c e).maxViol .lhs .rhs :=
  (con_eq_maxViolAt c none e).trans (Correspondence.maxViolAt_true _ _ _)

/-- `violations c e` is the set of constraints that the elision `e` violates, those protecting
the position of the elided vowel. It is a row of the paper's table of violations. -/
def violations (e : ElidedVowel) : Set (Option Prominence) := {i | protects c i (position c e)}

section Violations

variable {c}

@[simp] theorem none_mem_violations (e : ElidedVowel) : none ∈ violations c e := trivial

@[simp] theorem some_mem_violations_first {p : Prominence} :
    some p ∈ violations c .first ↔ c.Protects p c.v1Idx := Iff.rfl

@[simp] theorem some_mem_violations_second {p : Prominence} :
    some p ∈ violations c .second ↔ c.Protects p c.v2Idx := Iff.rfl

/-- The second vowel occupies a morph of one segment exactly when eliding it leaves the bare
stem, so that no segment of the second morph remains. -/
theorem soleSegment_mem_violations_second_iff :
    some .soleSegment ∈ violations c .second ↔ resolve c .second = c.stem := by
  rw [resolve_second, c.elideV2_eq_stem_iff]
  simp

end Violations

/-! ### Which vowel elides -/

/-- The tableau of the two elisions under the ranking `r`. -/
abbrev tableau (r : Ranking (Option Prominence) 5) : Tableau ElidedVowel 5 :=
  Tableau.ofRanking (con c) r {.first, .second}

private theorem card_option_prominence : Fintype.card (Option Prominence) = 5 := rfl

private theorem candidates_eq_pair {e e' : ElidedVowel} (hne : e ≠ e') :
    ({.first, .second} : Finset ElidedVowel) = {e, e'} := by
  cases e <;> cases e' <;> first | exact absurd rfl hne | decide

variable {c}

/-- An elision is optimal under some ranking exactly when the constraints it violates are not a
proper superset of those the other elision violates. -/
theorem exists_mem_optimal_iff {e e' : ElidedVowel} (hne : e ≠ e') :
    (∃ r, e ∈ (tableau c r).optimal) ↔ ¬ violations c e' ⊂ violations c e :=
  exists_mem_optimal_positionalMax_iff card_option_prominence (candidates_eq_pair hne) rfl rfl

/-- An elision is the sole optimum under some ranking exactly when the other elision violates a
constraint it does not. -/
theorem exists_optimal_eq_singleton_iff {e e' : ElidedVowel} (hne : e ≠ e') :
    (∃ r, (tableau c r).optimal = {e}) ↔ ¬ violations c e' ⊆ violations c e :=
  exists_optimal_eq_singleton_positionalMax_iff card_option_prominence (candidates_eq_pair hne)
    hne rfl rfl

/-- One elision is the sole optimum under a ranking exactly when some constraint violated only by
the other outranks every constraint violated only by it. -/
theorem optimal_eq_singleton_iff {e e' : ElidedVowel} (hne : e ≠ e') (r) :
    (tableau c r).optimal = {e} ↔ ∃ i ∈ violations c e', i ∉ violations c e ∧
      ∀ j ∈ violations c e, j ∉ violations c e' → r.Dominates i j :=
  optimal_eq_singleton_positionalMax_iff (candidates_eq_pair hne) hne rfl rfl r

/-- A constraint violated only by the other elision and ranked on top makes an elision the sole
optimum. -/
theorem optimal_eq_singleton_of_forall_dominates {e e' : ElidedVowel} (hne : e ≠ e')
    {r : Ranking (Option Prominence) 5} {i : Option Prominence} (hi : i ∉ violations c e)
    (hi' : i ∈ violations c e') (hr : ∀ j, j ≠ i → r.Dominates i j) :
    (tableau c r).optimal = {e} :=
  (optimal_eq_singleton_iff hne r).2 ⟨i, hi', hi, fun j hj _ ↦ hr j fun h ↦ hi (h ▸ hj)⟩

/-- The first vowel can elide alone in every context where it begins no morph. -/
theorem exists_optimal_eq_first (h : c.stemBody ≠ []) : ∃ r, (tableau c r).optimal = {.first} :=
  (exists_optimal_eq_singleton_iff (e' := .second) (by decide)).2 fun hs ↦ by
    simpa [h] using hs (show some .morphemeInitial ∈ violations c .second by simp)

private theorem forall_option_prominence {P : Option Prominence → Prop} :
    (∀ i, P i) ↔ P none ∧ P (some .wordInitial) ∧ P (some .lexical) ∧
      P (some .morphemeInitial) ∧ P (some .soleSegment) :=
  ⟨fun h ↦ ⟨h _, h _, h _, h _, h _⟩,
    by rintro ⟨h₀, h₁, h₂, h₃, h₄⟩ (_ | _ | _ | _ | _) <;> assumption⟩

/-- Where the first vowel begins no morph, the second vowel elides under some ranking exactly
when the first morph is a root and the second is not. This covers the boundary between two
lexical words, between a lexical and a function word in either order, between a prefix of more
than one segment and a root, between a root and a suffix, and between two affixes or clitics. -/
theorem exists_mem_optimal_second_iff (h : c.stemBody ≠ []) :
    (∃ r, .second ∈ (tableau c r).optimal) ↔ c.left = .root ∧ c.right ≠ .root := by
  rw [exists_mem_optimal_iff (e' := .first) (by decide), Set.ssubset_def, Set.subset_def,
    Set.subset_def, forall_option_prominence, forall_option_prominence]
  simp [h]

/-- After a prefix of one vowel, either vowel can elide alone, since only eliding the first
violates the constraint on morphs of one segment and only eliding the second violates the
constraint on lexical material, as in the paper's tableaux (15) and (16). -/
theorem exists_optimal_eq_of_vowelPrefix (h : c.stemBody = []) (hs : c.suffixBody ≠ [])
    (hl : c.left ≠ .root) (hr : c.right = .root) (e : ElidedVowel) :
    ∃ r, (tableau c r).optimal = {e} := by
  cases e
  · refine (exists_optimal_eq_singleton_iff (e' := .second) (by decide)).2 fun hsub ↦ ?_
    simpa [hl] using hsub ((some_mem_violations_second (p := .lexical)).2 (by simpa using hr))
  · refine (exists_optimal_eq_singleton_iff (e' := .first) (by decide)).2 fun hsub ↦ ?_
    simpa [hs] using hsub ((some_mem_violations_first (p := .soleSegment)).2 (by simpa using h))

/-! ### The kinds of juncture of the survey -/

/-- The kinds of the two morphs at a kind of juncture of the survey. A lexical word is a root,
and a function word is free and not a root. -/
def kinds : Data.Hiatus.Juncture → Morph.Kind × Morph.Kind
  | .lexicalLexical => (.root, .root)
  | .lexicalFunction => (.root, .free)
  | .prefixRoot => (.bound .before .affix, .root)
  | .rootSuffix => (.root, .bound .after .affix)
  | .suffixSuffix => (.bound .after .affix, .bound .after .affix)
  | .cliticClitic => (.bound .after .clitic, .bound .after .clitic)

/-- `IsOfKind c k` holds when the context `c` is a juncture of the survey's kind `k` at which the
first vowel begins no morph. -/
structure IsOfKind (c : Context) (k : Data.Hiatus.Juncture) : Prop where
  stemBody_ne_nil : c.stemBody ≠ []
  left : c.left = (kinds k).1
  right : c.right = (kinds k).2

/-- The paper's schematic consonant, the natural class [+consonantal]. -/
def C : Segment := .ofSpecs [(.consonantal, true)]

/-- The paper's schematic vowel, the natural class [+syllabic]. -/
def V : Segment := .ofSpecs [(.syllabic, true)]

/-- The paper's schematic juncture `/CV₁ + V₂C/` at the survey's kind `k`, at the start of an
utterance. -/
def schematic (k : Data.Hiatus.Juncture) : Context where
  stemBody := [C]
  v1 := V
  v2 := V
  suffixBody := [C]
  v1_isVowel := by decide
  v2_isVowel := by decide
  before := none
  left := (kinds k).1
  right := (kinds k).2

theorem isOfKind_schematic (k : Data.Hiatus.Juncture) : IsOfKind (schematic k) k :=
  ⟨List.cons_ne_nil _ _, rfl, rfl⟩

/-- At a juncture of the survey's kind `k`, the first vowel can always elide, and the second
exactly when the first morph is a root and the second is not. -/
theorem exists_mem_optimal_iff_of_isOfKind {k : Data.Hiatus.Juncture} (hc : IsOfKind c k)
    {e : ElidedVowel} : (∃ r, e ∈ (tableau c r).optimal) ↔
      e = .first ∨ (kinds k).1 = .root ∧ (kinds k).2 ≠ .root := by
  cases e
  · obtain ⟨r, hr⟩ := exists_optimal_eq_first hc.stemBody_ne_nil
    exact iff_of_true ⟨r, hr ▸ Finset.mem_singleton_self _⟩ (.inl rfl)
  · rw [exists_mem_optimal_second_iff hc.stemBody_ne_nil, hc.left, hc.right]
    simp

/-- At the paper's schematic juncture of two lexical words no ranking elides the second vowel, as
in its tableau (10), while before a function word some ranking does, as in its tableau (12). -/
theorem schematic_second :
    (¬ ∃ r, .second ∈ (tableau (schematic .lexicalLexical) r).optimal) ∧
      ∃ r, .second ∈ (tableau (schematic .lexicalFunction) r).optimal := by
  simp only [exists_mem_optimal_iff_of_isOfKind (isOfKind_schematic _)]
  decide

/-- With the constraint on lexical material on top, the first vowel elides after a prefix and
the second before a suffix of any length, the asymmetry within one language that the paper
reports for Chichewa. -/
theorem lexical_on_top {r : Ranking (Option Prominence) 5}
    (hr : ∀ j, j ≠ some .lexical → r.Dominates (some .lexical) j) {c c' : Context}
    (hc : IsOfKind c .prefixRoot) (hc' : IsOfKind c' .rootSuffix) :
    (tableau c r).optimal = {.first} ∧ (tableau c' r).optimal = {.second} :=
  ⟨optimal_eq_singleton_of_forall_dominates (e' := .second) (by decide)
      (by simp [hc.left, kinds]) (by simp [hc.right, kinds]) hr,
    optimal_eq_singleton_of_forall_dominates (e' := .first) (by decide)
      (by simp [hc'.right, kinds]) (by simp [hc'.left, kinds]) hr⟩

/-- With the constraint on morphs of one segment over the constraint on lexical material, and
that over the morpheme-initial constraint, the first vowel elides before a suffix of one segment
and the second before a longer one, as in the paper's tableaux (19) and (20). -/
theorem soleSegment_over_lexical {r : Ranking (Option Prominence) 5}
    (h₁ : r.Dominates (some .soleSegment) (some .lexical))
    (h₂ : r.Dominates (some .lexical) (some .morphemeInitial)) (hc : IsOfKind c .rootSuffix) :
    (tableau c r).optimal = {if c.suffixBody = [] then .first else .second} := by
  obtain ⟨hs, hl, hr⟩ := hc
  simp only [kinds] at hl hr
  split_ifs with hsuf
  · refine (optimal_eq_singleton_iff (e' := .second) (by decide) r).2
      ⟨some .soleSegment, by simpa using hsuf, by simpa using hs, ?_⟩
    rintro (_ | _ | _ | _ | _) hj hj' <;> simp_all
  · refine (optimal_eq_singleton_iff (e' := .first) (by decide) r).2
      ⟨some .lexical, by simpa using hl, by simp [hr], ?_⟩
    rintro (_ | _ | _ | _ | _) hj hj' <;> simp_all [Morph.Kind.JoinsAt]

/-! ### The survey -/

/-- Every elision the survey reports is one the analysis allows, in that some ranking elides the
reported vowel at a juncture of the reported kind. -/
theorem survey_allowed :
    ∀ row ∈ Data.Hiatus.Casali1997.rows, ∀ c : Context, IsOfKind c row.juncture →
      ∃ r, row.elided ∈ (tableau c r).optimal := by
  have key : ∀ row ∈ Data.Hiatus.Casali1997.rows, row.elided = .first ∨
      (kinds row.juncture).1 = .root ∧ (kinds row.juncture).2 ≠ .root := by
    decide
  exact fun row hrow _ hc ↦ (exists_mem_optimal_iff_of_isOfKind hc).2 (key row hrow)

/-- The survey reports an elision of the second vowel at exactly the kinds of juncture where the
analysis allows one, before a function word and before a suffix. -/
theorem survey_second_iff {k : Data.Hiatus.Juncture} (hc : IsOfKind c k) :
    (∃ row ∈ Data.Hiatus.Casali1997.rows, row.juncture = k ∧ row.elided = .second) ↔
      ∃ r, .second ∈ (tableau c r).optimal := by
  rw [exists_mem_optimal_iff_of_isOfKind hc]
  cases k <;> decide

end Casali1997
