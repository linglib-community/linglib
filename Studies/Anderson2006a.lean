module

public import Linglib.Data.Examples.Anderson2006a
public import Mathlib.Data.Finset.Basic

/-!
# Anderson 2006: auxiliary verb constructions

An auxiliary verb construction pairs an auxiliary with a lexical verb that stays the semantic
head, and languages differ in which element hosts the inflection: the auxiliary (English *have
eaten*), the lexical verb (Pipil *weli ni-nehnemi*), both with the same categories (Gorum), the
two dividing the categories (Jakaltek, absolutive on the auxiliary and ergative on the lexical
verb), or dividing them with some doubled (Hemba, Doyayo, Pipil). The five macro-patterns are
distinguished by the inflectional head alone, and across the split/doubled languages the doubled
category is overwhelmingly the subject. Negative auxiliaries head constructions of four of the
five patterns: aux-headed in Udihe, split in Kokota, lex-headed in Kwerba, doubled in 'Iipay.
Doyayo, filed as
lex-headed although its auxiliary partially encodes subject person through tone, comes out split
by the inflectional-head criterion.

## Main definitions

* `InflectionPattern`: the five inflectional macro-patterns (13).
* `Category`: the inflectional categories the book's examples record.
* `InflectionalMarking`: which categories each element carries;
  `InflectionalMarking.pattern` reads the macro-pattern (13) off it.

## References

* [anderson-2006a]
-/

@[expose] public section

namespace Anderson2006a

/-! ### Where the inflection is marked -/

/-- The five inflectional patterns of auxiliary verb constructions, by which of the auxiliary
and the lexical verb carries the inflection. -/
inductive InflectionPattern where
  /-- The auxiliary hosts the inflection and the lexical verb is nonfinite: English *have
  eaten*, French *va manger*. -/
  | auxHeaded
  /-- The lexical verb hosts the inflection and the auxiliary is grammaticalized: Pipil *weli
  ni-nehnemi*. -/
  | lexHeaded
  /-- Both elements carry the same categories: Gorum *miŋ ne-gaʔ-ru ne-laʔ-ru*, subject and TAM
  on each. -/
  | doubled
  /-- The categories divide between the elements with no overlap: Jakaltek *šk-ach w-ila*,
  absolutive on the auxiliary and ergative on the lexical verb. -/
  | split
  /-- The categories divide, but some are carried by both elements, the patterns of ch. 5 §5.2. -/
  | splitDoubled
  deriving DecidableEq, Repr, Inhabited

/-- The inflectional categories the book's examples record on the auxiliary and the lexical
verb. Agreement is subject or object agreement, as the book files it: Jakaltek's ergative
marker is subject and its absolutive marker object agreement. -/
inductive Category where
  | subj
  | obj
  | tense
  | aspect
  | mood
  | negation
  /-- The Gorum category of affectedness (version). -/
  | affectedness
  deriving DecidableEq

/-- Which inflectional categories each element of an auxiliary verb construction carries. -/
structure InflectionalMarking where
  onAux : Finset Category
  onLex : Finset Category
  deriving DecidableEq

/-- The inflectional head fixes the macro-pattern (13): only the auxiliary marked, only the
lexical verb, both with the same categories, the two disjoint, or overlapping. -/
def InflectionalMarking.pattern (m : InflectionalMarking) : InflectionPattern :=
  if m.onLex = ∅ then .auxHeaded
  else if m.onAux = ∅ then .lexHeaded
  else if m.onAux = m.onLex then .doubled
  else if Disjoint m.onAux m.onLex then .split
  else .splitDoubled

/-- The categories doubled on both elements. -/
def InflectionalMarking.doubled (m : InflectionalMarking) : Finset Category :=
  m.onAux ∩ m.onLex

/-! ### The book's examples -/

/-- The category names used in the example rows. -/
def Category.ofString? : String → Option Category
  | "subj" => some .subj
  | "obj" => some .obj
  | "tense" => some .tense
  | "aspect" => some .aspect
  | "mood" => some .mood
  | "negation" => some .negation
  | "affectedness" => some .affectedness
  | _ => none

/-- The categories a row lists under a feature key. -/
def categories (r : Datum) (key : String) : Finset Category :=
  ((r.features key).filterMap Category.ofString?).toFinset

/-- The inflectional marking a row records, when it records one. -/
def InflectionalMarking.ofRow? (r : Datum) : Option InflectionalMarking :=
  if r.paperFeatures.any (fun kv => kv.1 = "on_aux" || kv.1 = "on_lex") then
    some ⟨categories r "on_aux", categories r "on_lex"⟩
  else none

def InflectionPattern.ofString? : String → Option InflectionPattern
  | "auxHeaded" => some .auxHeaded
  | "lexHeaded" => some .lexHeaded
  | "doubled" => some .doubled
  | "split" => some .split
  | "splitDoubled" => some .splitDoubled
  | _ => none

-- (13)
theorem rows_pattern :
    ∀ r ∈ Examples.all, r.feature? "aux_marking" = none →
      ∀ m ∈ (InflectionalMarking.ofRow? r).toList,
        ∀ p ∈ ((r.feature? "infl_pattern").bind InflectionPattern.ofString?).toList,
          m.pattern = p := by
  decide +kernel

-- (15a), (13)
theorem doyayo_split :
    ∀ m ∈ (InflectionalMarking.ofRow? Examples.doyayo_lexheaded).toList, m.pattern = .split := by
  decide +kernel

theorem all_patterns_attested (p : InflectionPattern) :
    ∃ r ∈ Examples.all, ∃ m ∈ (InflectionalMarking.ofRow? r).toList, m.pattern = p := by
  cases p <;> decide +kernel

theorem splitDoubled_doubles_subject :
    ∀ r ∈ Examples.all, ∀ m ∈ (InflectionalMarking.ofRow? r).toList,
      m.pattern = .splitDoubled → m.doubled = {.subj} := by
  decide +kernel

/-! ### Negative auxiliaries -/

-- (49), (52), §1.7.2
theorem negative_auxiliary_patterns :
    (∃ r ∈ Examples.all, r.feature? "strategy" = some "negVerb" ∧
      (r.feature? "infl_pattern").bind InflectionPattern.ofString? = some .auxHeaded) ∧
    ∃ r ∈ Examples.all, r.feature? "strategy" = some "negVerb" ∧
      (r.feature? "infl_pattern").bind InflectionPattern.ofString? = some .lexHeaded := by
  decide +kernel

end Anderson2006a
