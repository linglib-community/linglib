module

public import Mathlib.Tactic.FinCases
public import Linglib.Data.Wordlist.Svenonius2004
public import Linglib.Fragments.Slavic.Russian.Verbs
public import Linglib.Fragments.Slavic.Polish.Verbs
public import Linglib.Fragments.Slavic.Bulgarian.Verbs
public import Linglib.Morphology.Word.Tree

/-!
# Svenonius (2004): Slavic Prefixes Inside and Outside VP

Svenonius divides the Slavic verbal prefixes into two classes by their place in the decomposed
clause (2). A lexical prefix is the resultative R head inside the VP, like a Germanic particle in
den Dikken's analysis; a superlexical prefix is an Asp head above the VP, with an adverbial,
aspectual or quantificational meaning. The same prefix form serves either class, as Russian *za-*
does in (1).

## Main definitions

* `PrefixClass`, `SuperlexicalSubtype`: the class of a prefix in a word.
* `WellStacked`: no lexical prefix is outside a superlexical one, (4).
* `Structure`: the Asp heads, highest first, and the optional R head over a verb.
* `Analysis`: an attested form with its fragment verb and classified prefixes, outermost first.
* `Spells`: morphs spell out a written form.

## Implementation notes

The subtypes are the glosses of (57)–(58) together with Istratkova's terminative and
excessive, an open list. The secondary imperfective's scope (4.5), the argument-structure
effects of lexical prefixes (4.3), and the phrasal-movement alternative of section 5 are not
formalized; the classification of the examples is the paper's, and Romanova documents
mismatches among the diagnostics.

## References

* [svenonius-2004]
* [istratkova-2004]
* [dendikken-1995]
* [romanova-2004]
-/

@[expose] public section

namespace Svenonius2004

open Morphology (Morph)
open Morphology.Word (Tree)
open CLDF.Wordlist (Form)

/-- The aspectual subtypes of superlexical prefixes, the glosses of (57)–(58) with
[istratkova-2004]'s terminative and excessive. -/
inductive SuperlexicalSubtype
  | delimitative
  | cumulative
  | completive
  | repetitive
  | inceptive
  | distributive
  | attenuative
  | terminative
  | excessive
  deriving DecidableEq

/-- A prefix in a word is the R head or an Asp head with its subtype. -/
inductive PrefixClass
  | lexical
  | superlexical (subtype : SuperlexicalSubtype)
  deriving DecidableEq

namespace PrefixClass

/-- A superlexical class. -/
def IsSuperlexical : PrefixClass → Prop
  | .lexical => False
  | .superlexical _ => True

instance : DecidablePred IsSuperlexical
  | .lexical => isFalse id
  | .superlexical _ => isTrue trivial

theorem not_isSuperlexical_iff (c : PrefixClass) : ¬ c.IsSuperlexical ↔ c = .lexical := by
  cases c <;> simp [IsSuperlexical]

end PrefixClass

/-- A classified prefix sequence, outermost first, is well-stacked when no lexical prefix
appears outside a superlexical one (4). -/
def WellStacked (prefixes : List (Morph × PrefixClass)) : Prop :=
  prefixes.Pairwise fun outer inner ↦ inner.2.IsSuperlexical → outer.2.IsSuperlexical

instance : DecidablePred WellStacked := fun prefixes ↦
  inferInstanceAs (Decidable (prefixes.Pairwise fun outer inner ↦
    inner.2.IsSuperlexical → outer.2.IsSuperlexical))

/-- The lexical prefixes of a sequence. -/
def lexicals (prefixes : List (Morph × PrefixClass)) : List (Morph × PrefixClass) :=
  prefixes.filter (·.2 = PrefixClass.lexical)

/-! ### The structure (2) -/

/-- In the decomposed clause of (2) the superlexical prefixes are Asp heads above the VP, highest
first, and a lexical prefix is the resultative R head below V, of which a VP has one
position (4.4). -/
structure Structure where
  /-- The Asp heads, highest first. -/
  outer : List (Morph × SuperlexicalSubtype)
  /-- The R head. -/
  result : Option Morph
  /-- The verb. -/
  stem : Verb

namespace Structure

/-- A structure linearizes as the Asp heads, then the R head, before the stem. -/
def prefixes (s : Structure) : List (Morph × PrefixClass) :=
  s.outer.map (fun p ↦ (p.1, .superlexical p.2)) ++ (s.result.map (·, .lexical)).toList

-- (4)
theorem wellStacked_prefixes (s : Structure) : WellStacked s.prefixes := by
  rw [WellStacked, prefixes, List.pairwise_append]
  refine ⟨List.pairwise_map.2 (List.pairwise_of_forall fun _ _ _ ↦ trivial), ?_, ?_⟩
  · cases s.result <;> simp
  · intro a ha b hb _
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha
    trivial

-- (4.4)
theorem lexicals_length_le_one (s : Structure) : (lexicals s.prefixes).length ≤ 1 := by
  rw [lexicals, prefixes, List.filter_append, List.length_append]
  have h : (s.outer.map (fun p ↦ (p.1, PrefixClass.superlexical p.2))).filter
      (·.2 = PrefixClass.lexical) = [] :=
    List.filter_eq_nil_iff.2 fun a ha ↦ by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha
      simp
  rw [h, List.length_nil, zero_add]
  cases s.result <;> simp

/-- The linearizations of structures over a stem are exactly the well-stacked sequences with
at most one lexical prefix ((4.4)). -/
theorem exists_prefixes_eq_iff (ps : List (Morph × PrefixClass)) (st : Verb) :
    (∃ s : Structure, s.stem = st ∧ s.prefixes = ps) ↔
      WellStacked ps ∧ (lexicals ps).length ≤ 1 := by
  constructor
  · rintro ⟨s, _, rfl⟩
    exact ⟨s.wellStacked_prefixes, s.lexicals_length_le_one⟩
  · induction ps with
    | nil => exact fun _ ↦ ⟨⟨[], none, st⟩, rfl, rfl⟩
    | cons p ps ih =>
      rintro ⟨hw, hl⟩
      rw [WellStacked, List.pairwise_cons] at hw
      obtain ⟨⟨m, c⟩, rfl⟩ : ∃ q, q = p := ⟨p, rfl⟩
      cases c with
      | lexical =>
        have hps : ps = [] := by
          cases ps with
          | nil => rfl
          | cons a ps' =>
            have ha : a.2 = .lexical :=
              (PrefixClass.not_isSuperlexical_iff _).1 fun h ↦ hw.1 a (List.mem_cons_self ..) h
            simp [lexicals, ha] at hl
        exact ⟨⟨[], some m, st⟩, rfl, by simp [prefixes, hps]⟩
      | superlexical k =>
        obtain ⟨s, _, hps⟩ := ih ⟨hw.2, by simpa [lexicals] using hl⟩
        exact ⟨⟨(m, k) :: s.outer, s.result, st⟩, rfl, by simp [prefixes, ← hps]⟩

end Structure

/-- Morphs spell out a written form when their forms, joined, are that form. -/
def Spells (ms : List Morph) (w : String) : Prop := ms.foldr (·.form ++ ·) "" = w

instance (ms : List Morph) (w : String) : Decidable (Spells ms w) :=
  inferInstanceAs (Decidable (_ = _))

/-- An analysis of an attested form gives the fragment verb it is built on and its classified
prefix sequence, outermost first. -/
structure Analysis where
  /-- The attested form. -/
  form : Form UD.MorphFeatures
  /-- The fragment verb. -/
  stem : Verb
  /-- The classified fragment prefix morphs, outermost first. -/
  prefixes : List (Morph × PrefixClass)

namespace Analysis

/-- The morphs of the analysed word are the prefixes, outermost first, then the verb. -/
def morphs (a : Analysis) : List Morph := a.prefixes.map Prod.fst ++ a.stem.morphs

/-- The word-formation tree, the prefix morphs attached to the stem root innermost first. -/
def tree (a : Analysis) : Tree Morph :=
  .attachAll (Morph.root a.stem.form) (a.prefixes.reverse.map fun p ↦ (.before, p.1))

theorem tree_isConcatenative (a : Analysis) : a.tree.IsConcatenative :=
  Tree.isConcatenative_attachAll _ _

end Analysis

/-! ### The paper's analyses -/

section Russian
open Russian.Verbs

/-- (1a) *za-brosil* has lexical spatial *za-* on perfective *brositj*. -/
def a1a : Analysis := ⟨Wordlist.f_1a, brosit, [(za, .lexical)]⟩

/-- (1b) *za-brosil* 'gave up' has the same lexical *za-*, idiomatic. -/
def a1b : Analysis := ⟨Wordlist.f_1b, brosit, [(za, .lexical)]⟩

/-- (1c) *za-brosal* has superlexical inceptive *za-* on imperfective *brosatj*, the minimal pair
with (1a) on the same fragment morph. -/
def a1c : Analysis := ⟨Wordlist.f_1c, brosat, [(za, .superlexical .inceptive)]⟩

/-- (4a) *po-vy-brasyvatj* has superlexical distributive *po-* outside lexical *vy-* on the
secondary-imperfective stem. -/
def a4a : Analysis :=
  ⟨Wordlist.f_4a, brasyvat, [(po, .superlexical .distributive), (vy, .lexical)]⟩

/-- (58) *za-kuritj* has superlexical inceptive *za-*. -/
def a58za : Analysis := ⟨Wordlist.f_58za, kurit, [(za, .superlexical .inceptive)]⟩

/-- (58) *po-čitatj* has superlexical attenuative *po-*. -/
def a58po : Analysis := ⟨Wordlist.f_58po, chitat, [(po, .superlexical .attenuative)]⟩

/-- The Russian analyses. -/
def russianAnalyses : List Analysis := [a1a, a1b, a1c, a4a, a58za, a58po]

end Russian

section Polish
open Polish.Verbs

/-- (4c) *po-w-chodzili* has superlexical distributive *po-* outside lexical *w-*. -/
def a4c : Analysis :=
  ⟨Wordlist.f_4c, chodzic, [(po, .superlexical .distributive), (w, .lexical)]⟩

end Polish

section Bulgarian
open Bulgarian.Verbs

/-- (3a) *po-na-razkaža*, glossed DLMT-CMLT, on perfective *razkaža*. -/
def a3a : Analysis :=
  ⟨Wordlist.f_3a, razkazha,
    [(po, .superlexical .delimitative), (na, .superlexical .cumulative)]⟩

/-- (3e) *iz-po-na-pre-razkaža*, glossed CMPL-DSTR-CMLT-RPET, the deepest stack cited from
[istratkova-2004]. -/
def a3e : Analysis :=
  ⟨Wordlist.f_3e, razkazha,
    [(iz, .superlexical .completive), (po, .superlexical .distributive),
     (na, .superlexical .cumulative), (pre, .superlexical .repetitive)]⟩

end Bulgarian

/-- The analyses. -/
def analyses : List Analysis := [a1a, a1b, a1c, a4a, a58za, a58po, a4c, a3a, a3e]

/-- The starred reversals (4b) and (4d), with the classes of the prefixes in (4a) and (4c). -/
def starred : List Analysis :=
  [⟨Wordlist.f_4b, Russian.Verbs.brasyvat,
    [(Russian.Verbs.vy, .lexical), (Russian.Verbs.po, .superlexical .distributive)]⟩,
   ⟨Wordlist.f_4d, Polish.Verbs.chodzic,
    [(Polish.Verbs.w, .lexical), (Polish.Verbs.po, .superlexical .distributive)]⟩]

/-! ### Results -/

/-- Every analysis is well-stacked with at most one lexical prefix, so it is the linearization
of a structure over its stem. -/
theorem analyses_structured (a : Analysis) (ha : a ∈ analyses) :
    ∃ s : Structure, s.stem = a.stem ∧ s.prefixes = a.prefixes :=
  (Structure.exists_prefixes_eq_iff _ _).2 (by fin_cases ha <;> decide)

/-- The starred reversals (4b) and (4d) of the prefixes of (4a) and (4c) are not well-stacked, so no
structure linearizes to them. -/
theorem starred_not_structured (a : Analysis) (ha : a ∈ starred) :
    ¬ WellStacked a.prefixes ∧ ¬ ∃ s : Structure, s.stem = a.stem ∧ s.prefixes = a.prefixes := by
  have h : ¬ WellStacked a.prefixes := by fin_cases ha <;> decide
  exact ⟨h, fun h' ↦ h ((Structure.exists_prefixes_eq_iff _ _).1 h').1⟩

-- (4a), (4c)
theorem starred_prefixes : starred.map (·.prefixes) = [a4a, a4c].map (·.prefixes.reverse) := rfl

/-- Outside the past tense, as in (1) and (4c), every analysis spells out its attested form ((4a),
(4b), (58), (3)). -/
theorem analyses_spells : ∀ a ∈ analyses ++ starred,
    a.form.cell.tense ≠ ↑UD.Tense.Past → Spells a.morphs a.form.form := by
  decide

/-- Diagnostic (56c) holds of the Russian analyses: a superlexically prefixed verb is built on an
imperfective stem ((3)). -/
theorem superlexical_selects_imperfective (a : Analysis) (ha : a ∈ russianAnalyses)
    (hs : ∃ p ∈ a.prefixes, p.2.IsSuperlexical) :
    a.stem.perfectivity = some .imperfective := by
  fin_cases ha <;> first | rfl | exact absurd hs (by decide)

end Svenonius2004
