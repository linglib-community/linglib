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

* `marks`: Casali's constraints, MAX restricted to each prominent position and general MAX, on the
  two elisions.
* `violations`: the constraints an elision violates, a row of the paper's table of violations.
* `optimal`: the optimal elisions under a ranking.

## Implementation notes

* The constraints are indexed by `Option Prominence`: `some p` is MAX restricted to the position
  `p`, and `none` is general MAX (`marks_none`). Every elision violates general MAX once, so it
  never decides between them, and the universal ranking of the positional constraints above it
  is not imposed.
* Lexical status and word boundaries are read off the kinds of the two morphs: roots are lexical,
  and affixes, clitics and free function words are not.
* A word-initial vowel is also morpheme-initial, so the second vowel violates the
  morpheme-initial constraint at a word boundary too, which the paper's table of violations
  leaves out and which changes no prediction.
* `schematic k` is the paper's schematic juncture `/CV₁ + V₂C/` at the survey's kind `k`, with
  `C` and `V` the natural classes [+consonantal] and [+syllabic, −consonantal]; it witnesses that
  every kind of juncture has a context.

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
def marks : ElidedVowel → Option Prominence → ℕ :=
  positionalMax (protects c) fun e ↦ {position c e}

/-- `corr c e` is the correspondence between the unrepaired concatenation and the form that the
elision `e` gives. -/
def corr (e : ElidedVowel) : Correspondence.Coindexation BinaryRole Segment :=
  Correspondence.Coindexation.eraseIdx c.input ⟨position c e, position_lt_length_input c e⟩

/-- `resolve c e` is the form that the elision `e` gives. -/
def resolve (e : ElidedVowel) : List Segment := (corr c e).string .rhs

theorem resolve_first : resolve c .first = c.elideV1 :=
  Correspondence.Coindexation.eraseIdx_string_rhs.trans c.elideV1_eq_eraseIdx.symm

theorem resolve_second : resolve c .second = c.elideV2 :=
  Correspondence.Coindexation.eraseIdx_string_rhs.trans c.elideV2_eq_eraseIdx.symm

theorem marks_eq_maxViolAt (i : Option Prominence) (e : ElidedVowel) :
    marks c e i = (corr c e).maxViolAt (protects c i) .lhs .rhs :=
  Constraint.maxAt_singleton_eq_maxViolAt _ ⟨position c e, position_lt_length_input c e⟩

theorem marks_none (e : ElidedVowel) : marks c e none = (corr c e).maxViol .lhs .rhs :=
  (marks_eq_maxViolAt c none e).trans (Correspondence.Coindexation.maxViolAt_true _ _ _)

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

theorem soleSegment_mem_violations_second_iff :
    some .soleSegment ∈ violations c .second ↔ resolve c .second = c.left := by
  rw [resolve_second, c.elideV2_eq_left_iff]
  simp

theorem violations_first_subset_second_iff :
    violations c .first ⊆ violations c .second ↔
      (c.leftKind = .root → c.rightKind = .root) ∧ (c.leftBody = [] → c.rightBody = [] ∧
        ((∀ b ∈ c.beforeKind, ¬ b.JoinsAt .clitic c.leftKind) →
          ¬ c.leftKind.JoinsAt .clitic c.rightKind)) := by
  simp only [Set.subset_def, Option.forall, Prominence.forall, none_mem_violations,
    some_mem_violations_first, some_mem_violations_second, Context.protects_v1Idx,
    Context.protects_v2Idx]
  tauto

theorem violations_second_subset_first_iff :
    violations c .second ⊆ violations c .first ↔
      c.leftBody = [] ∧ (c.rightKind = .root → c.leftKind = .root) ∧
        (¬ c.leftKind.JoinsAt .clitic c.rightKind →
          ∀ b ∈ c.beforeKind, ¬ b.JoinsAt .clitic c.leftKind) := by
  simp only [Set.subset_def, Option.forall, Prominence.forall, none_mem_violations,
    some_mem_violations_first, some_mem_violations_second, Context.protects_v1Idx,
    Context.protects_v2Idx]
  tauto

end Violations

/-! ### Which vowel elides -/

/-- The optimal elisions under the ranking `r`. -/
abbrev optimal (r : Ranking (Option Prominence)) : Finset ElidedVowel :=
  r.optimal (marks c) {.first, .secondPosition}

private theorem card_option_prominence : Fintype.card (Option Prominence) = 5 := rfl

private theorem candidates_eq_pair {e e' : ElidedVowel} (hne : e ≠ e') :
    ({.first, .secondPosition} : Finset ElidedVowel) = {e, e'} := by
  cases e <;> cases e' <;> first | exact absurd rfl hne | decide

variable {c}

theorem forall_elidedVowel {p : ElidedVowel → Prop} : (∀ e, p e) ↔ p .first ∧ p .second :=
  ⟨fun h ↦ ⟨h _, h _⟩, by rintro ⟨h₁, h₂⟩ (_ | _) <;> assumption⟩

/-- An elision is optimal under some ranking exactly when the constraints it violates are minimal:
if they include those the other elision violates, the two violate the same constraints. -/
theorem exists_mem_optimal_iff {e : ElidedVowel} :
    (∃ r, e ∈ optimal c r) ↔
      ∀ e', violations c e' ⊆ violations c e → violations c e ⊆ violations c e' :=
  (exists_mem_optimal_positionalMax_iff card_option_prominence).trans
    ⟨fun h e' ↦ h.2 (by cases e' <;> simp), fun h ↦ ⟨by cases e <;> simp, fun e' _ ↦ h e'⟩⟩

theorem exists_optimal_eq_singleton_iff {e e' : ElidedVowel} (hne : e ≠ e') :
    (∃ r, optimal c r = {e}) ↔ ¬ violations c e' ⊆ violations c e :=
  exists_optimal_eq_singleton_positionalMax_iff card_option_prominence (candidates_eq_pair hne)
    hne rfl rfl

theorem optimal_eq_singleton_iff {e e' : ElidedVowel} (hne : e ≠ e') (r) :
    optimal c r = {e} ↔ ∃ i ∈ violations c e', i ∉ violations c e ∧
      ∀ j ∈ violations c e, j ∉ violations c e' → r.Dominates i j :=
  optimal_eq_singleton_positionalMax_iff (candidates_eq_pair hne) hne rfl rfl r

theorem optimal_eq_singleton_of_ssubset {e e' : ElidedVowel} (hne : e ≠ e')
    (h : violations c e ⊂ violations c e') (r : Ranking (Option Prominence)) :
    optimal c r = {e} :=
  optimal_eq_singleton_positionalMax_of_ssubset (candidates_eq_pair hne) rfl rfl h r

theorem optimal_eq_pair_iff (r : Ranking (Option Prominence)) :
    optimal c r = {.first, .secondPosition} ↔ violations c .first = violations c .second :=
  optimal_eq_pair_positionalMax_iff (c := .first) (d := .second) (P := protects c)
    (del := fun e ↦ {position c e}) rfl rfl rfl r

theorem optimal_eq_singleton_of_forall_dominates {e e' : ElidedVowel} (hne : e ≠ e')
    {r : Ranking (Option Prominence)} {i : Option Prominence} (hi : i ∉ violations c e)
    (hi' : i ∈ violations c e') (hr : ∀ j, j ≠ i → r.Dominates i j) :
    optimal c r = {e} :=
  (optimal_eq_singleton_iff hne r).2 ⟨i, hi', hi, fun j hj _ ↦ hr j fun h ↦ hi (h ▸ hj)⟩

theorem exists_optimal_eq_first (h : c.leftBody ≠ []) : ∃ r, optimal c r = {.first} :=
  (exists_optimal_eq_singleton_iff (e' := .second) (by decide)).2 fun hs ↦ by
    simpa [h] using hs (show some .morphemeInitial ∈ violations c .second by simp)

/-- Where the first vowel begins no morph, the second vowel elides under some ranking exactly
when the first morph is a root and the second is not. This covers the boundary between two
lexical words, between a lexical and a function word in either order, between a prefix of more
than one segment and a root, between a root and a suffix, and between two affixes or clitics. -/
theorem exists_mem_optimal_second_iff (h : c.leftBody ≠ []) :
    (∃ r, .secondPosition ∈ optimal c r) ↔ c.leftKind = .root ∧ c.rightKind ≠ .root := by
  simp [exists_mem_optimal_iff, forall_elidedVowel, violations_first_subset_second_iff,
    violations_second_subset_first_iff, h]

-- (15), (16)
theorem exists_optimal_eq_of_vowelPrefix (h : c.leftBody = []) (hs : c.rightBody ≠ [])
    (hl : c.leftKind ≠ .root) (hr : c.rightKind = .root) (e : ElidedVowel) :
    ∃ r, optimal c r = {e} := by
  cases e
  · refine (exists_optimal_eq_singleton_iff (e' := .second) (by decide)).2 fun hsub ↦ ?_
    simpa [hl] using hsub ((some_mem_violations_second (p := .lexical)).2 (by simpa using hr))
  · refine (exists_optimal_eq_singleton_iff (e' := .first) (by decide)).2 fun hsub ↦ ?_
    simpa [hs] using hsub ((some_mem_violations_first (p := .soleSegment)).2 (by simpa using h))

/-! ### The kinds of juncture of the survey -/

/-- The kinds of the two morphs at a kind of juncture of the survey. A lexical word is a root,
and a function word is free and not a root. -/
def kinds : Data.Hiatus.JunctureKind → Morph.Kind × Morph.Kind
  | .lexicalLexical => (.root, .root)
  | .lexicalFunction => (.root, .free)
  | .prefixRoot => (.bound .before .affix, .root)
  | .rootSuffix => (.root, .bound .after .affix)
  | .suffixSuffix => (.bound .after .affix, .bound .after .affix)
  | .cliticClitic => (.bound .after .clitic, .bound .after .clitic)

/-- `IsOfKind c k` holds when the context `c` is a juncture of the survey's kind `k` at which the
first vowel begins no morph. -/
structure IsOfKind (c : Context) (k : Data.Hiatus.JunctureKind) : Prop where
  leftBody_ne_nil : c.leftBody ≠ []
  leftKind : c.leftKind = (kinds k).1
  rightKind : c.rightKind = (kinds k).2

/-- The paper's schematic consonant, the natural class [+consonantal]. -/
def C : Segment := [+consonantal]

/-- The paper's schematic vowel, the natural class [+syllabic, −consonantal]. -/
def V : Segment := [+syllabic, −consonantal]

/-- The paper's schematic juncture `/CV₁ + V₂C/` at the survey's kind `k`, at the start of an
utterance. -/
def schematic (k : Data.Hiatus.JunctureKind) : Context where
  leftBody := [C]
  v1 := V
  v2 := V
  rightBody := [C]
  v1_isVowel := by decide
  v2_isVowel := by decide
  beforeKind := none
  leftKind := (kinds k).1
  rightKind := (kinds k).2

theorem isOfKind_schematic (k : Data.Hiatus.JunctureKind) : IsOfKind (schematic k) k :=
  ⟨List.cons_ne_nil _ _, rfl, rfl⟩

theorem exists_mem_optimal_iff_of_isOfKind {k : Data.Hiatus.JunctureKind} (hc : IsOfKind c k)
    {e : ElidedVowel} : (∃ r, e ∈ optimal c r) ↔
      e = .first ∨ (kinds k).1 = .root ∧ (kinds k).2 ≠ .root := by
  cases e
  · obtain ⟨r, hr⟩ := exists_optimal_eq_first hc.leftBody_ne_nil
    exact iff_of_true ⟨r, hr ▸ Finset.mem_singleton_self _⟩ (.inl rfl)
  · rw [exists_mem_optimal_second_iff hc.leftBody_ne_nil, hc.leftKind, hc.rightKind]
    simp

-- (10), (12)
theorem schematic_second :
    (¬ ∃ r, .secondPosition ∈ optimal (schematic .lexicalLexical) r) ∧
      ∃ r, .secondPosition ∈ optimal (schematic .lexicalFunction) r := by
  simp only [exists_mem_optimal_iff_of_isOfKind (isOfKind_schematic _)]
  decide

theorem lexical_on_top {r : Ranking (Option Prominence)}
    (hr : ∀ j, j ≠ some .lexical → r.Dominates (some .lexical) j) {c c' : Context}
    (hc : IsOfKind c .prefixRoot) (hc' : IsOfKind c' .rootSuffix) :
    optimal c r = {.first} ∧ optimal c' r = {.secondPosition} :=
  ⟨optimal_eq_singleton_of_forall_dominates (e' := .second) (by decide)
      (by simp [hc.leftKind, kinds]) (by simp [hc.rightKind, kinds]) hr,
    optimal_eq_singleton_of_forall_dominates (e' := .first) (by decide)
      (by simp [hc'.rightKind, kinds]) (by simp [hc'.leftKind, kinds]) hr⟩

-- (19), (20)
theorem soleSegment_over_lexical {r : Ranking (Option Prominence)}
    (h₁ : r.Dominates (some .soleSegment) (some .lexical))
    (h₂ : r.Dominates (some .lexical) (some .morphemeInitial)) (hc : IsOfKind c .rootSuffix) :
    optimal c r = {if c.rightBody = [] then .first else .secondPosition} := by
  obtain ⟨hs, hl, hr⟩ := hc
  simp only [kinds] at hl hr
  split_ifs with hsuf
  · refine (optimal_eq_singleton_iff (e' := .second) (by decide) r).2
      ⟨some .soleSegment, by simpa using hsuf, by simpa using hs, ?_⟩
    simp_all [Option.forall, Prominence.forall]
  · refine (optimal_eq_singleton_iff (e' := .first) (by decide) r).2
      ⟨some .lexical, by simpa using hl, by simp [hr], ?_⟩
    simp_all [Option.forall, Prominence.forall, Morph.Kind.JoinsAt]

/-! ### The survey -/

/-- Every elision the survey reports is one the analysis allows, in that some ranking elides the
reported vowel at a juncture of the reported kind. -/
theorem survey_allowed :
    ∀ row ∈ Data.Hiatus.Casali1997.rows, ∀ c : Context, IsOfKind c row.juncture →
      ∃ r, row.elided ∈ optimal c r := by
  have key : ∀ row ∈ Data.Hiatus.Casali1997.rows, row.elided = .first ∨
      (kinds row.juncture).1 = .root ∧ (kinds row.juncture).2 ≠ .root := by
    decide
  exact fun row hrow _ hc ↦ (exists_mem_optimal_iff_of_isOfKind hc).2 (key row hrow)

/-- The survey reports an elision of the second vowel at exactly the kinds of juncture where the
analysis allows one, before a function word and before a suffix. -/
theorem survey_second_iff {k : Data.Hiatus.JunctureKind} (hc : IsOfKind c k) :
    (∃ row ∈ Data.Hiatus.Casali1997.rows, row.juncture = k ∧ row.elided = .second) ↔
      ∃ r, .secondPosition ∈ optimal c r := by
  rw [exists_mem_optimal_iff_of_isOfKind hc]
  cases k <;> decide

end Casali1997
