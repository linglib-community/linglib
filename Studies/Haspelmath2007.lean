module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Haspelmath2007
public import Linglib.Syntax.Category.Coordinator
public import Linglib.Fragments.English.Coordination
public import Linglib.Fragments.Finnish.Coordination
public import Linglib.Fragments.German.Coordination
public import Linglib.Fragments.Hausa.Adpositions
public import Linglib.Fragments.Hausa.Coordination
public import Linglib.Fragments.Hungarian.Coordination
public import Linglib.Fragments.Irish.Coordination
public import Linglib.Fragments.Kannada.Coordination
public import Linglib.Fragments.Korean.Coordination
public import Linglib.Fragments.Lango.Adpositions
public import Linglib.Fragments.Lango.Coordination
public import Linglib.Fragments.Latin.Coordination
public import Linglib.Fragments.Tibetic.Classical.Case
public import Linglib.Fragments.Tibetic.Classical.Coordination
public import Linglib.Fragments.Turkish.Adpositions
public import Linglib.Fragments.Turkish.Coordination
public import Linglib.Fragments.Yoruba.Coordination
public import Linglib.Data.Examples.Readers

/-!
# Haspelmath (2007): Coordination

Haspelmath's chapter classifies coordinate constructions by where their coordinators go. A
binary pattern, (17), is the pair of the markings of the two coordinands. The two diachronic
sources of conjunction, §1.2, a comitative modifier 'A with B' and an additive focus particle
'A, also B', yield patterns from the order of their parts, and no source whose modifier order and
adposition order are harmonic yields co-A B, the pattern no language attests. Table 1.1 derives
the patterns of multiple coordination from the binary one.

The chapter's examples are the rows of `Data/Examples/Haspelmath2007.json`. Each construction is
analysed by its coordinators, one coordinator or a correlative pair. Of the binary examples, the
chapter calls emphatic exactly the correlative ones, and the bisyndetic ones that are not
correlative are postpositive, §1.3 and §2.1. The file also classifies the correlatives of (45) by
their forms and states Payne's implicational sequence of coordinand types, §3, with the
counterexample from Tinrin the chapter records.

## Implementation notes

* A binary pattern (17) is a `Coordinator.Pattern`, the side of each coordinand's coordinator,
  `none` for a bare coordinand.
* A construction's coordinators are its language's Fragment entries where they exist, and are
  written inline otherwise. A pair of coordinators is a `Coordinator.Correlative`; the single
  coordinator of a mixed pair, (27) and (28), is taken to be its second, as in (45b).
* The rows record emphasis only where the chapter states it. Keeping every coordinator of a
  multiple coordination is emphatic in European languages, p. 12, which is not emphasis by
  correlatives, so `emphatic_iff_correlative` is about binary coordination.
* Classical Tibetan *-daŋ* and Turkish *-le*, which the chapter says "come from a former
  case-marker" without naming the case, have no source in the rows; the Fragments record, after
  Beyer and after Göksel and Kerslake, that both are still comitative markers
  (`former_case_marker_isAlsoComitative`).
* The rows record §1.4 coordinator omission as a feature, all but the last coordinator kept,
  all but the first, or none; `omitted` is Table 1.1's omission column and `omittedFirst` the
  Classical Tibetan and Amharic alternative of (36).

## TODO

* The Somali rows (60b–c) and §4.2's natural conjunction, Yoruba *t-A-t-B* at p. 24, are not
  yet encoded.

## References

* [haspelmath-2007]
* [beyer-1992]
* [dryer-1992]
* [goksel-kerslake-2005]
* [greenberg-1963]
* [rowlands-1969]
* [stassen-2000]
-/

@[expose] public section

namespace Haspelmath2007

open Morphology (Morph)
open Coordinator (Pattern)

/-! ### Binary patterns, (17) -/

-- §1.2
theorem monosyndetic_bare {p : Pattern} (h : p.syndesis = 1) : p.1 = none ∨ p.2 = none := by
  rcases p with ⟨_ | _, _ | _⟩ <;> simp_all [Pattern.syndesis]

/-! ### Diachronic sources, §1.2 -/

/-- A conjunctive coordinator comes from a comitative modifier 'A with B', given by the side of
B its adposition goes on and the side of the noun the modifier goes on, or from an additive focus
particle 'A, also B', given by the side of B it goes on, §1.2 and §5.1. -/
inductive DiachronicSource where
  | comitative (adposition modifier : Morph.Side)
  | focusParticle (particle : Morph.Side)
  deriving DecidableEq, Repr

namespace DiachronicSource

/-- The binary pattern (17) of a source construction, §1.2. The comitative phrase is the first
coordinand when modifiers precede the noun and the second when they follow it, marked on the side
of its adposition, and the focus particle marks the second conjunct on its own side, so that
'A, B too' gives A B-co and 'A, also B' gives A co-B. -/
def pattern : DiachronicSource → Pattern
  | .comitative adposition .before => (some adposition, none)
  | .comitative adposition .after => (none, some adposition)
  | .focusParticle particle => (none, some particle)

/-- A comitative source is harmonic when modifiers precede the noun in a language with
postpositions or follow it in one with prepositions, the orders that go together
[greenberg-1963] [dryer-1992]; a focus particle is not a modifier. -/
def Harmonic : DiachronicSource → Prop
  | .comitative adposition modifier => adposition ≠ modifier
  | .focusParticle _ => True

instance : DecidablePred Harmonic
  | .comitative adposition modifier => inferInstanceAs (Decidable (adposition ≠ modifier))
  | .focusParticle _ => inferInstanceAs (Decidable True)

theorem pattern_eq_coAB_iff {s : DiachronicSource} :
    s.pattern = (some .before, none) ↔ s = .comitative .before .before := by
  rcases s with ⟨_ | _, _ | _⟩ | (_ | _) <;> decide

/-- No harmonic source has the pattern co-A B, which §1.2 offers as the explanation of its
absence from [stassen-2000]'s sample of 260 languages. -/
theorem coAB_unsourced {s : DiachronicSource} (h : s.Harmonic) :
    s.pattern ≠ (some .before, none) :=
  fun h' ↦ by rw [pattern_eq_coAB_iff.1 h'] at h; exact h rfl

end DiachronicSource

/-! ### Multiple coordination, Table 1.1 -/

/-- The full n-ary pattern of a binary one, §1.4. A bisyndetic pattern of one shape marks every
coordinand, and a monosyndetic pattern leaves bare the coordinand bare in the binary
construction and marks every other one as its marked coordinand is marked; the mixed patterns
have no full pattern in the chapter. -/
def full (p : Pattern) (n : ℕ) : Option (List (Option Morph.Side)) :=
  match p with
  | (none, s) => some (none :: List.replicate (n - 1) s)
  | (s, none) => some (List.replicate (n - 1) s ++ [none])
  | (s, t) => if s = t then some (List.replicate n s) else none

/-- Keep the first coordinator of a construction, eliminating the rest. -/
def keepFirst : List (Option Morph.Side) → List (Option Morph.Side)
  | [] => []
  | none :: l => none :: keepFirst l
  | s :: l => s :: l.map fun _ ↦ none

theorem keepFirst_countP (l : List (Option Morph.Side)) :
    (keepFirst l).countP Option.isSome ≤ 1 := by
  induction l with
  | nil => simp [keepFirst]
  | cons s l ih =>
    cases s <;> simp_all [keepFirst]

/-- Coordinator omission, §1.4, eliminates all but the last coordinator, the omission of
Table 1.1. -/
def omitted (p : Pattern) (n : ℕ) : Option (List (Option Morph.Side)) :=
  (full p n).map fun l ↦ (keepFirst l.reverse).reverse

/-- Omission eliminating all but the first coordinator, the Classical Tibetan and Amharic
alternative of (36), which p. 13 sets against Table 1.1. -/
def omittedFirst (p : Pattern) (n : ℕ) : Option (List (Option Morph.Side)) :=
  (full p n).map keepFirst

-- Table 1.1
theorem table_1_1 :
    full (none, some .before) 4 = some [none, some .before, some .before, some .before] ∧
      omitted (none, some .before) 4 = some [none, none, none, some .before] ∧
    full (some .after, none) 4 = some [some .after, some .after, some .after, none] ∧
      omitted (some .after, none) 4 = some [none, none, some .after, none] ∧
    full (some .after, some .after) 4 = some (.replicate 4 (some .after)) ∧
      omitted (some .after, some .after) 4 = some [none, none, none, some .after] ∧
    full (some .before, some .before) 4 = some (.replicate 4 (some .before)) ∧
      omitted (some .before, some .before) 4 = some [none, none, none, some .before] ∧
    full (none, some .after) 4 = some [none, some .after, some .after, some .after] ∧
      omitted (none, some .after) 4 = some [none, none, none, some .after] := by
  decide

/-! ### The chapter's examples -/

/-- The labels of the patterns in the rows, A co-B as `a_co_b`. -/
def patternLabels : List (String × Pattern) :=
  [("asyndetic", (none, none)), ("a_co_b", (none, some .before)), ("a'co_b", (some .after, none)),
    ("a_b'co", (none, some .after)), ("co'a_b", (some .before, none)),
    ("co'a_co'b", (some .before, some .before)), ("a'co_b'co", (some .after, some .after)),
    ("co'a_b'co", (some .before, some .after)), ("a'co_co'b", (some .after, some .before))]

/-- The binary pattern of a row, for a multiple coordination that of its binary construction. -/
def pattern? (d : Datum) : Option Pattern := d.parse? "pattern" patternLabels

/-- Whether the chapter presents a row as emphatic, where it says. -/
def emphatic? (d : Datum) : Option Bool := d.parse? "emphatic" [("yes", true), ("no", false)]

-- (17)
theorem pattern?_isSome :
    ∀ d ∈ Examples.all, (d.feature? "pattern").isSome → (pattern? d).isSome := by
  decide

theorem pattern?_ne_coAB : ∀ d ∈ Examples.all, pattern? d ≠ some (some .before, none) := by
  decide

-- §1.3 [stassen-2000]
theorem prepositive_bisyndetic_emphatic :
    ∀ d ∈ Examples.all, pattern? d = some (some .before, some .before) →
      emphatic? d = some true := by
  decide

-- (36), Table 1.1
theorem allButFirst_ne_omitted :
    ∀ d ∈ Examples.all, d.feature? "omission" = some "allButFirst" →
      ∀ p ∈ pattern? d, ∀ n ∈ d.nat? "coordinands",
        omittedFirst p n = some (some .after :: List.replicate (n - 1) none) ∧
          omittedFirst p n ≠ omitted p n := by
  decide

-- p. 14, Table 1.1 [rowlands-1969]
theorem deletion_omitted :
    ∃ p ∈ pattern? Examples.deletion, ∃ n ∈ Examples.deletion.nat? "coordinands",
      omitted p n = some [none, none, none, some .before] := by
  decide

-- (85b), §5.1, (81), (86)
theorem comitative_patterns : ∀ d ∈ Examples.all, d.feature? "source" = some "comitative" →
    ∀ p ∈ pattern? d,
      (∃ a m, (DiachronicSource.comitative a m).Harmonic ∧
        (DiachronicSource.comitative a m).pattern = p) ∨
      d.source.paperLabel = "(85b)" ∧ p = (some .after, some .after) ∨
      d.source.paperLabel ∈ ["(81)", "(86)"] ∧
        p = (DiachronicSource.comitative .after .after).pattern := by
  decide

/-! ### The coordinators of the constructions -/

/-- A construction has one coordinator, on each coordinand its pattern marks, or a pair of
correlative coordinators. -/
inductive Coordinators where
  | plain (c : Coordinator)
  | correlative (k : Coordinator.Correlative)
  deriving Repr

/-- The coordinators are a correlative pair. -/
def Coordinators.IsCorrelative : Coordinators → Prop
  | .plain _ => False
  | .correlative _ => True

instance : DecidablePred Coordinators.IsCorrelative
  | .plain _ => inferInstanceAs (Decidable False)
  | .correlative _ => inferInstanceAs (Decidable True)

/-- The forms on the coordinands a pattern marks, each with its marking. -/
def Coordinators.marking : Coordinators → Pattern → List (Option Morph.Side × Morph)
  | .plain c, (s, t) => [(s, c.morph), (t, c.morph)].filter (·.1.isSome)
  | .correlative k, (s, t) => k.first.map (s, ·) ++ k.second.map (t, ·)

/-- A coordinate construction the chapter cites, a row with its coordinators. -/
structure Attestation where
  datum : Datum
  coordinators : Coordinators

/-- A conjunctive coordinator with no Fragment entry. -/
def co (morph : Morph) : Coordinator := { morph, gloss := "and", role := .conjunctive }

/-- A disjunctive coordinator with no Fragment entry. -/
def dis (form : String) : Coordinator :=
  { morph := .free form, gloss := "or", role := .disjunctive }

open Examples in
/-- The constructions of the rows with a coordinator. -/
def attestations : List Attestation :=
  [ ⟨ex5, .plain Kannada.Coordination.uu⟩,
    ⟨ex6a, .correlative English.Coordination.bothAnd⟩,
    ⟨ex6b, .plain English.Coordination.and_⟩,
    ⟨ex7a, .correlative English.Coordination.neitherNor⟩,
    ⟨ex12b, .plain Hausa.Coordination.da⟩,
    ⟨ex20, .plain Lango.Coordination.kede⟩,
    ⟨ex21, .plain ClassicalTibetan.Coordination.dang⟩,
    ⟨ex22, .plain Latin.Coordination.que⟩,
    ⟨ex23, .plain Turkish.Coordination.de⟩,
    ⟨ex24a, .plain (co (.suff "a"))⟩,
    ⟨ex24b, .plain (dis "râ")⟩,
    ⟨ex25, .correlative Yoruba.Coordination.atiAti⟩,
    ⟨ex26, .plain (co (.suff "thurti"))⟩,
    ⟨ex27, .correlative ⟨[.encl "te"], [.free "kaì"], co (.free "kaì")⟩⟩,
    ⟨ex28, .correlative ⟨[Latin.Coordination.et.morph], [Latin.Coordination.que.morph],
      Latin.Coordination.que⟩⟩,
    ⟨ex29, .plain (co (.suff "ɣo"))⟩,
    ⟨ex30, .correlative ⟨[.free "ou"], [.free "ou"], dis "ou"⟩⟩,
    ⟨ex31, .plain (co (.free "i"))⟩,
    ⟨ex32, .plain (co (.suff "ni"))⟩,
    ⟨ex33, .plain (co (.encl "lu"))⟩,
    ⟨ex34, .plain (co (.encl "lu"))⟩,
    ⟨ex35, .plain (co (.suff "nna"))⟩,
    ⟨ex36a, .plain ClassicalTibetan.Coordination.dang⟩,
    ⟨ex36b, .plain (co (.suff "nna"))⟩,
    ⟨ex37, .plain (co (.free "oh"))⟩,
    ⟨deletion, .plain Yoruba.Coordination.ati⟩,
    ⟨ex43, .correlative English.Coordination.bothAnd⟩,
    ⟨ex57a, .plain Korean.Coordination.gwa⟩,
    ⟨ex58a, .plain Turkish.Coordination.ile⟩,
    ⟨ex59a, .plain Yoruba.Coordination.ati⟩,
    ⟨ex60a, .plain (co (.free "iyo"))⟩,
    ⟨ex62b, .plain (co (.free "di"))⟩,
    ⟨ex63b, .plain (co (.free "kɛ"))⟩,
    ⟨ex77b, .plain (co (.free "ma"))⟩,
    ⟨ex78b, .plain (co (.suff "ka"))⟩,
    ⟨ex79, .plain (co (.free "s"))⟩,
    ⟨ex81, .plain (co (.free "ca"))⟩,
    ⟨ex85b, .plain (co (.suff "sou"))⟩,
    ⟨ex86, .plain (co (.suff "wan"))⟩ ]

theorem attestations_label : attestations.map (·.datum.source.paperLabel) =
    (Examples.all.filter fun d ↦ (pattern? d).any (·.syndesis ≠ 0)).map
      (·.source.paperLabel) := by
  decide

theorem marking_agrees_with_side : ∀ a ∈ attestations, ∀ p ∈ pattern? a.datum,
    ∀ m ∈ a.coordinators.marking p, ∀ s ∈ m.2.kind.side?, m.1 = some s := by
  decide

/-- The chapter presents a binary coordination as emphatic exactly when its coordinators are
correlative, §2.1. -/
theorem emphatic_iff_correlative : ∀ a ∈ attestations, a.datum.nat? "coordinands" = none →
    ∀ e ∈ emphatic? a.datum, (e = true ↔ a.coordinators.IsCorrelative) := by
  decide

/-- Non-correlative bisyndesis is postpositive (§2.1, §1.3), so prepositive bisyndesis is emphatic,
as [stassen-2000] finds. -/
theorem normal_bisyndetic_postpositive : ∀ a ∈ attestations, ¬ a.coordinators.IsCorrelative →
    ∀ p ∈ pattern? a.datum, p.syndesis = 2 → p = (some .after, some .after) := by
  decide

theorem comitative_source_isAlsoComitative :
    Hausa.Coordination.da.IsAlsoComitative Hausa.Adpositions.da.morphs
        Hausa.Adpositions.da.functions ∧
      Lango.Coordination.kede.IsAlsoComitative Lango.Adpositions.kede.morphs
        Lango.Adpositions.kede.functions := by
  decide

-- (41)
theorem former_case_marker_isAlsoComitative :
    ClassicalTibetan.Coordination.dang.IsAlsoComitative
        (ClassicalTibetan.Case.exponents .accompaniment)
        (ClassicalTibetan.Case.functions .accompaniment) ∧
      Turkish.Coordination.ile.IsAlsoComitative Turkish.Adpositions.ile.morphs
        Turkish.Adpositions.ile.functions := by
  decide

/-! ### Emphatic correlatives, (45) -/

/-- A pair of correlative coordinators, (45), has both identical to the single coordinator, only
its second identical to it, its two identical to each other but not to it, or all three
different. -/
inductive CorrelativeShape where
  | bothSingle
  | secondSingle
  | sameNotSingle
  | allDifferent
  deriving DecidableEq, Repr

/-- The shape of a correlative pair, read off the forms. -/
def CorrelativeShape.classify (c : Coordinator.Correlative) : CorrelativeShape :=
  if c.first = [c.single.morph] ∧ c.second = [c.single.morph] then .bothSingle
  else if c.second = [c.single.morph] then .secondSingle
  else if c.first = c.second then .sameNotSingle
  else .allDifferent

/-- The rows of (45), each with its language and the letter the chapter files it under; Polish
*tak (i)* is recorded without its optional *i*. -/
def correlatives : List (String × Coordinator.Correlative × CorrelativeShape) :=
  [ ("Russian", ⟨[.free "i"], [.free "i"], co (.free "i")⟩, .bothSingle),
    ("Italian", ⟨[.free "e"], [.free "e"], co (.free "e")⟩, .bothSingle),
    ("Modern Greek", ⟨[.free "ke"], [.free "ke"], co (.free "ke")⟩, .bothSingle),
    ("Albanian", ⟨[.free "edhe"], [.free "edhe"], co (.free "edhe")⟩, .bothSingle),
    ("Polish", ⟨[.free "albo"], [.free "albo"], dis "albo"⟩, .bothSingle),
    ("Dutch", ⟨[.free "of"], [.free "of"], dis "of"⟩, .bothSingle),
    ("Basque", ⟨[.free "ala"], [.free "ala"], dis "ala"⟩, .bothSingle),
    ("Somali", ⟨[.free "ama"], [.free "ama"], dis "ama"⟩, .bothSingle),
    ("English", English.Coordination.bothAnd, .secondSingle),
    ("Irish", Irish.Coordination.idirAgus, .secondSingle),
    ("English", English.Coordination.eitherOr, .secondSingle),
    ("German", German.Coordination.entwederOder, .secondSingle),
    ("Finnish", Finnish.Coordination.jokoTai, .secondSingle),
    ("Hungarian", Hungarian.Coordination.mindMind, .sameNotSingle),
    ("Korean", Korean.Coordination.doDo, .sameNotSingle),
    ("Lezgian", ⟨[.free "ja"], [.free "ja"], dis "waja"⟩, .sameNotSingle),
    ("German", German.Coordination.sowohlAlsAuch, .allDifferent),
    ("Polish", ⟨[.free "jak"], [.free "tak"], co (.free "i")⟩, .allDifferent),
    ("Finnish", Finnish.Coordination.sekaEtta, .allDifferent),
    ("Indonesian", ⟨[.free "baik"], [.free "maupun"], co (.free "dan")⟩, .allDifferent) ]

-- (45)
theorem correlatives_classified :
    ∀ r ∈ correlatives, CorrelativeShape.classify r.2.1 = r.2.2 := by
  decide

-- (45)
theorem correlatives_conjunctive_or_disjunctive : ∀ r ∈ correlatives,
    r.2.1.single.role = .conjunctive ∨ r.2.1.single.role = .disjunctive := by
  decide

-- (45a)
theorem yoruba_bothSingle :
    CorrelativeShape.classify Yoruba.Coordination.atiAti = .bothSingle := by
  decide

/-! ### Types of coordinands, §3 -/

/-- Beyond the binary contrast of noun-phrase and event coordination, (57)–(58), Yoruba
distinguishes three coordinand types, (59): *àti* for noun phrases, *tí* for relative clauses
and *sì* for main clauses, each row with its coordinator. -/
def yorubaContrasts : List (Datum × Coordinator) :=
  [(Examples.ex59a, Yoruba.Coordination.ati), (Examples.ex59b, Yoruba.Coordination.ti),
    (Examples.ex59c, Yoruba.Coordination.si)]

-- (59)
theorem yorubaContrasts_distinct :
    (yorubaContrasts.map fun r ↦ r.1.feature? "coordinands").Nodup ∧
      (yorubaContrasts.map fun r ↦ r.2.morph).Nodup ∧
      ∀ r ∈ yorubaContrasts, r.2.role = .conjunctive := by
  decide

/-! ### Payne's implicational sequence, §3 -/

/-- The coordinand types of the sequence S – VP – AP – PP – NP. -/
inductive CoordinandType where
  | s
  | vp
  | ap
  | pp
  | np
  deriving DecidableEq, Fintype, Repr

/-- Position on the sequence. -/
def CoordinandType.rank : CoordinandType → ℕ
  | .s => 0
  | .vp => 1
  | .ap => 2
  | .pp => 3
  | .np => 4

/-- A coordinator's range is a contiguous stretch of the sequence. -/
def Contiguous (r : Finset CoordinandType) : Prop :=
  ∀ a ∈ r, ∀ b ∈ r, ∀ c, a.rank ≤ c.rank → c.rank ≤ b.rank → c ∈ r

instance : DecidablePred Contiguous := fun _ ↦ by unfold Contiguous; infer_instance

-- (57), (58)
theorem np_event_contiguous : Contiguous {.np} ∧ Contiguous {.vp, .s} := by decide

theorem tinrin_not_contiguous : ¬ Contiguous {.s, .np} := by decide

end Haspelmath2007
