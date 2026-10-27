module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Linglib.Phonology.Harmony.System
public import Linglib.Fragments.Finnish.Phonology
public import Linglib.Fragments.Turkish.Phonology
public import Studies.Yang2016
public import Linglib.Data.Examples.Belth2026
public import Linglib.Morphology.Morph

/-!
# Belth (2026): A Learning-Based Account of Phonological Tiers

This file formalizes D2L, Belth's learner, and the paper's own runs of it. D2L
receives pairs of underlying and surface forms, an alternating class, and a feature, and
constructs the search-and-copy rule `Rel(A, F) / C __ ∘ proj(·, T)` (`Phonology.SearchCopy`) from
adjacent dependencies alone: starting from the whole alphabet as the tier, it builds the
left- and right-context rules whose contexts are the segments tier-adjacent to the targets,
counts the applications and correct applications of the more accurate one, accepts it under
Yang's Tolerance Principle (`Yang2016.tolerates`) with the Elsewhere default the
untouched targets show, and otherwise deletes from the tier the smallest natural class
containing the contexts that produced errors (`D2L.iterate`, `D2L.learn`). On the paper's toy
vocabulary (20) the learner runs exactly as its trace (21), (30), (32) and (33) says: three
iterations with the tiers Σ, [+cons] and [+sib], accuracies 1/8, 4/8 and 7/7, and the rule
`Agree({S}, {ant}) / [+sib] __ ∘ proj(·, [+sib])` with default [s] (`Toy.iterations`,
`Toy.learn`). The rules D2L converges to on natural language data are run on the paper's
examples: Latin liquid dissimilation (54) on (53), with the *lunaris* row it mispredicts
(`latin_rows`, `lunaris_mispredicted`); Finnish backness harmony (52), which is the
search-and-copy reading of the fragment's `Finnish.palatalHarmony`, on (51)
(`finnish_rows`); and Turkish vowel harmony (49a) on (46) and (47) through the fragment's
two harmonies (`turkish_rows`).

## Implementation notes

A target with no tier-adjacent segment on the rule's side is an underextension on either
side; the paper writes the right word boundary into the right-context set, which changes
only that rule's application count, never the choice between the two rules on the paper's
data. A context that is itself alternating is never added to the deletion set, since the
alternating segments must stay on the tier ((19), step 8); on this reading of (28) the
second iteration deletes exactly {n, k, g}. A trigger unspecified for the feature counts as
an incorrect application, as the paper counts it. Ties in accuracy go to the left-context
rule. Belth's Turkish rule (49a) transmits backness and rounding as one feature set; the
fragment factors it into the two harmonies of Göksel and Kerslake, applied in turn. The
predictions of section 4 need Finley's and McMullin and Hansson's full stimulus lists, which
the paper does not print, so the learned rules (40) and (44) are not run here.

## References

* [belth-2026]
* [yang-2016]
* [goksel-kerslake-2005]
-/

@[expose] public section

namespace Belth2026

open Phonology

/-! ### D2L -/

namespace D2L

variable {α : Type*} [DecidableEq α]

/-- A learning problem consists of the alphabet, the alternating segments `A`, the feature
`F` read and written on them, the natural classes a tier may lose, and the vocabulary of
underlying and surface forms. -/
structure Problem (α : Type*) [DecidableEq α] where
  alphabet : List α
  targets : List α
  value : α → Option Bool
  write : Bool → α → α
  value_write : ∀ v s, s ∈ targets → value (write v s) = some v
  write_value : ∀ v s, s ∈ targets → value s = some v → write v s = s
  classes : List (List α)
  vocabulary : List (List α × List α)

/-- The applications `n` and correct applications `c` of a rule over the vocabulary, the
contexts of its incorrect applications, and the surface segments of the targets it leaves
untouched. -/
structure Summary (α : Type*) where
  n : ℕ
  c : ℕ
  errors : List α
  untouched : List α
  deriving DecidableEq, Repr

/-- One iteration of D2L records the tier, the two context classes and summaries, the side
chosen, the default the chosen rule infers, and the deletion set. -/
structure Iteration (α : Type*) where
  tier : List α
  contextsL : List α
  contextsR : List α
  left : Summary α
  right : Summary α
  chosen : Edge
  default : Option (Option Bool)
  deletion : List α
  deriving DecidableEq, Repr

/-- The summary of the side an iteration chose. -/
def Iteration.summary (it : Iteration α) : Summary α :=
  match it.chosen with
  | .left => it.left
  | .right => it.right

/-- The contexts of the side an iteration chose. -/
def Iteration.contexts (it : Iteration α) : List α :=
  match it.chosen with
  | .left => it.contextsL
  | .right => it.contextsR

/-- Whether the left summary is at least as accurate as the right one. -/
def better (l r : Summary α) : Bool :=
  if l.n = 0 then r.c = 0 else if r.n = 0 then true else r.c * l.n ≤ l.c * r.n

/-- For each target on the tier of a form, read in the direction of `g`, the underlying
segment tier-adjacent to it if `g` applied, the segment `g` output, and the surface segment.
The rule applies when the output segment preceding the target on the tier is a trigger. -/
def trace (g : SearchCopy α) :
    List α → List α → Option α → Option α → List (Option α × α × α)
  | x :: xs, y :: ys, last, lastUR =>
    if g.tier x then
      let out := g.emit last x
      let ctx := if (last.filter fun c ↦ decide (g.IsSource c x)).isSome then lastUR else none
      (if g.IsTarget x then [(ctx, out, y)] else []) ++ trace g xs ys (some out) (some x)
    else trace g xs ys last lastUR
  | _, _, _, _ => []

/-- The trace of `g` over a pair of forms, in the direction of `g`. -/
def applications (g : SearchCopy α) (p : List α × List α) : List (Option α × α × α) :=
  trace g (g.direction.orient p.1) (g.direction.orient p.2) none none

namespace Problem

variable (P : Problem α)

/-- The segments tier-adjacent before the targets of a form on the tier `T`. -/
def precedingContexts (T : List α) : List α → Option α → List α
  | [], _ => []
  | x :: xs, last =>
    if x ∈ T then
      (if x ∈ P.targets then last.toList else []) ++ precedingContexts T xs (some x)
    else precedingContexts T xs last

/-- The context class `C` of the rule on side `d` over the tier `T`, every segment
tier-adjacent to a target on that side in some underlying form. -/
def contexts (T : List α) (d : Edge) : List α :=
  (P.vocabulary.flatMap fun p ↦
    P.precedingContexts T (d.orient p.1) none).dedup

/-- The candidate rule over the tier `T` with the contexts `C`. -/
def candidate (T C : List α) (rel : SearchCopy.Relation) (d : Edge)
    (default : Option Bool := none) : SearchCopy α where
  tier s := s ∈ T
  IsSource s _ := s ∈ C
  IsTarget s := s ∈ P.targets
  relation := rel
  value := P.value
  write := P.write
  value_write := P.value_write
  write_value := P.write_value
  default := default
  direction := d

/-- The summary of `g` over the vocabulary. -/
def summary (g : SearchCopy α) : Summary α :=
  let apps := P.vocabulary.flatMap (applications g)
  let applied := apps.filterMap fun t ↦ t.1.map fun c ↦ (c, decide (t.2.1 = t.2.2))
  { n := applied.length
    c := (applied.filter (·.2)).length
    errors := (((applied.filter fun a ↦ !a.2).map (·.1)).filter (· ∉ P.targets)).dedup
    untouched := apps.filterMap fun t ↦ if t.1.isNone then some t.2.2 else none }

/-- The Elsewhere default the untouched targets determine; `none` when their surface forms
disagree, which rejects the rule. -/
def inferDefault (untouched : List α) : Option (Option Bool) :=
  match (untouched.map P.value).dedup with
  | [] => some none
  | [v] => some v
  | _ => none

/-- The iteration over the tier `T` with the deletion set `D`. -/
def step (rel : SearchCopy.Relation) (T D : List α) : Iteration α :=
  let CL := P.contexts T .left
  let CR := P.contexts T .right
  let sL := P.summary (P.candidate T CL rel .left)
  let sR := P.summary (P.candidate T CR rel .right)
  let chosen : Edge := if better sL sR then .left else .right
  { tier := T, contextsL := CL, contextsR := CR, left := sL, right := sR, chosen := chosen
    default := P.inferDefault (match chosen with | .left => sL | .right => sR).untouched
    deletion := (D ++ sL.errors ++ sR.errors).dedup }

/-- The smallest natural class containing `D` and no target. -/
def deletionClass (D : List α) : Option (List α) :=
  (P.classes.filter fun N ↦ D.all (· ∈ N) && P.targets.all (· ∉ N)).foldl
    (fun acc N ↦ match acc with
      | none => some N
      | some M => if N.length < M.length then some N else some M) none

/-- The tier after deleting the class of `D`, or `D` itself when no class contains it. -/
def nextTier (T D : List α) : List α :=
  match P.deletionClass D with
  | some N => T.filter (· ∉ N)
  | none => T.filter (· ∉ D)

/-- The iterations of D2L from the tier `T` with the deletion set `D`, until the tier is
empty or stops shrinking. -/
def iterate (rel : SearchCopy.Relation) : ℕ → List α → List α → List (Iteration α)
  | 0, _, _ => []
  | fuel + 1, T, D =>
    if T = [] then [] else
    let it := P.step rel T D
    let T' : List α := P.nextTier T it.deletion
    it :: (if T'.length < T.length then iterate rel fuel T' it.deletion else [])

/-- The rule an iteration proposes, the chosen side's candidate with its inferred default. -/
def rule (rel : SearchCopy.Relation) (it : Iteration α) : Option (SearchCopy α) :=
  it.default.map fun d ↦ P.candidate it.tier it.contexts rel it.chosen d

/-- D2L returns the rule of the first iteration the criterion `sat` accepts on its
applications and exceptions. -/
def learn (rel : SearchCopy.Relation) (sat : ℕ → ℕ → Prop) [DecidableRel sat] :
    Option (SearchCopy α) :=
  ((P.iterate rel P.alphabet.length P.alphabet []).find? fun it ↦
    it.default.isSome && decide (sat it.summary.n (it.summary.n - it.summary.c))).bind (P.rule rel)

end Problem

end D2L

/-! ### The toy vocabulary (20) -/

namespace Toy

/-- The segments of the toy vocabulary, with `sh` for ʃ and `S` the sibilant unspecified for
anteriority. -/
inductive Seg where
  | sh | o | k | u | S | i | a | p | n | s | g | t
  deriving DecidableEq, Repr

/-- Consonantality. -/
def Seg.cons : Seg → Bool
  | .o | .u | .i | .a => false
  | _ => true

/-- Sibilance. -/
def Seg.sib : Seg → Bool
  | .sh | .S | .s => true
  | _ => false

/-- Anteriority, unspecified on `S` and on the vowels. -/
def Seg.ant : Seg → Option Bool
  | .s | .n | .p | .t => some true
  | .sh | .k | .g => some false
  | _ => none

def alphabet : List Seg := [.sh, .o, .k, .u, .S, .i, .a, .p, .n, .s, .g, .t]

/-- The natural classes describable by one feature. -/
def classes : List (List Seg) :=
  [alphabet.filter Seg.cons, alphabet.filter (!Seg.cons ·), alphabet.filter Seg.sib,
    alphabet.filter (!Seg.sib ·), alphabet.filter (·.ant = some true),
    alphabet.filter (·.ant = some false)]

/-- The pairs of (20a). -/
def vocabulary : List (List Seg × List Seg) :=
  [([.sh, .o, .k, .u, .S, .i, .S], [.sh, .o, .k, .u, .sh, .i, .sh]),
   ([.a, .p, .sh, .a, .S], [.a, .p, .sh, .a, .sh]),
   ([.sh, .u, .n, .i, .S], [.sh, .u, .n, .i, .sh]),
   ([.s, .o, .k, .i, .S], [.s, .o, .k, .i, .s]),
   ([.s, .i, .g, .o, .S, .i, .S], [.s, .i, .g, .o, .s, .i, .s]),
   ([.u, .t, .S], [.u, .t, .s])]

/-- The problem of (20), with `A = {S}` and `F = {ant}`. -/
def problem : D2L.Problem Seg where
  alphabet := alphabet
  targets := [.S]
  value := Seg.ant
  write v _ := if v then .s else .sh
  value_write := fun v _ _ ↦ by cases v <;> rfl
  write_value := fun _ seg h hv ↦ by
    simp only [List.mem_singleton] at h; subst h; simp [Seg.ant] at hv
  classes := classes
  vocabulary := vocabulary

/-- The consonant tier of the second iteration. -/
def consTier : List Seg := alphabet.filter Seg.cons

/-- The sibilant tier of the third iteration. -/
def sibTier : List Seg := alphabet.filter Seg.sib

/-- The surface sibilants the right-context rules leave untouched. -/
def rightUntouched : List Seg := [.sh, .sh, .sh, .s, .s, .s]

/-- The learner's trace (21), (30), (32), (33) takes three iterations, over the tiers Σ, [+cons] and
[+sib]. -/
theorem iterations : problem.iterate .agree problem.alphabet.length problem.alphabet [] =
    [{ tier := alphabet, contextsL := [.u, .a, .o, .i, .t], contextsR := [.i],
       left := ⟨8, 1, [.u, .a, .o, .i], []⟩, right := ⟨2, 0, [.i], rightUntouched⟩,
       chosen := .left, default := some none, deletion := [.u, .a, .o, .i] },
     { tier := consTier, contextsL := [.sh, .n, .k, .g, .S, .t], contextsR := [.S],
       left := ⟨8, 4, [.n, .k, .g], []⟩, right := ⟨2, 0, [], rightUntouched⟩,
       chosen := .left, default := some none, deletion := [.u, .a, .o, .i, .n, .k, .g] },
     { tier := sibTier, contextsL := [.sh, .s, .S], contextsR := [.S],
       left := ⟨7, 7, [], [.s]⟩, right := ⟨2, 0, [], rightUntouched⟩,
       chosen := .left, default := some (some true),
       deletion := [.u, .a, .o, .i, .n, .k, .g] }] := by
  decide

/-- Rule (33a) with its default, `Agree({S}, {ant}) / [+sib] __ ∘ proj(·, [+sib])` and [s]
elsewhere. -/
def rule33 : SearchCopy Seg := problem.candidate sibTier [.sh, .s, .S] .agree .left (some true)

theorem learn (sat : ℕ → ℕ → Prop) [DecidableRel sat] (h1 : ¬ sat 8 7) (h2 : ¬ sat 8 4)
    (h3 : sat 7 0) : problem.learn .agree sat = some rule33 := by
  simp [D2L.Problem.learn, iterations, D2L.Problem.rule, D2L.Iteration.summary,
    D2L.Iteration.contexts, h1, h2, h3, rule33]

theorem iterations_disagree :
    problem.iterate .disagree problem.alphabet.length problem.alphabet [] =
    [{ tier := alphabet, contextsL := [.u, .a, .o, .i, .t], contextsR := [.i],
       left := ⟨8, 0, [.u, .a, .o, .i, .t], []⟩, right := ⟨2, 0, [.i], rightUntouched⟩,
       chosen := .left, default := some none, deletion := [.u, .a, .o, .t, .i] },
     { tier := sibTier, contextsL := [.sh, .s, .S], contextsR := [.S],
       left := ⟨7, 2, [.sh, .s], [.s]⟩, right := ⟨2, 0, [], rightUntouched⟩,
       chosen := .left, default := some (some true),
       deletion := [.u, .a, .o, .t, .i, .sh, .s] },
     { tier := [.S], contextsL := [.S], contextsR := [.S],
       left := ⟨2, 0, [], rightUntouched⟩, right := ⟨2, 0, [], rightUntouched⟩,
       chosen := .left, default := none, deletion := [.u, .a, .o, .t, .i, .sh, .s] }] := by
  decide

theorem learn_disagree (sat : ℕ → ℕ → Prop) [DecidableRel sat] (h1 : ¬ sat 8 8)
    (h2 : ¬ sat 7 5) : problem.learn .disagree sat = none := by
  simp [D2L.Problem.learn, iterations_disagree, D2L.Iteration.summary, h1, h2]

end Toy

/-! ### Tolerance at the toy's iterations -/

theorem not_tolerates_8_7 : ¬ Yang2016.tolerates 8 7 := by
  unfold Yang2016.tolerates Yang2016.threshold
  have h8 : Real.log ((8 : ℕ) : ℝ) = 3 * Real.log 2 := by
    rw [show ((8 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h8, not_le, div_lt_iff₀ (by linarith [Real.log_two_gt_d9])]
  push_cast
  linarith [Real.log_two_gt_d9]

theorem not_tolerates_8_4 : ¬ Yang2016.tolerates 8 4 := by
  unfold Yang2016.tolerates Yang2016.threshold
  have h8 : Real.log ((8 : ℕ) : ℝ) = 3 * Real.log 2 := by
    rw [show ((8 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h8, not_le, div_lt_iff₀ (by linarith [Real.log_two_gt_d9])]
  push_cast
  linarith [Real.log_two_gt_d9]

-- (33a), (20)
theorem Toy.learn_tolerates :
    @D2L.Problem.learn _ _ Toy.problem .agree Yang2016.tolerates
      (fun _ _ ↦ Classical.propDecidable _) = some Toy.rule33 :=
  @Toy.learn Yang2016.tolerates (fun _ _ ↦ Classical.propDecidable _) not_tolerates_8_7
    not_tolerates_8_4 (Yang2016.tolerates_zero 7)

/-! ### Latin liquid dissimilation (54) -/

/-- The segments of the paper's Latin transcriptions; `L` is the affix liquid unspecified for
laterality, `v` the semivowel. -/
inductive LatSeg where
  | a | e | i | o | u
  | l | r | L
  | n | v | s | g | f | p | b
  deriving DecidableEq, Repr, Fintype

namespace LatSeg

/-- The `[+cons]` tier, every segment but the vowels, `L` included. -/
def IsCons : LatSeg → Prop
  | .a | .e | .i | .o | .u => False
  | _ => True

instance : DecidablePred IsCons := fun seg ↦ by cases seg <;> unfold IsCons <;> infer_instance

/-- Laterality, on which `l` alone is `[+lat]` and `L` is unspecified. -/
def isLat : LatSeg → Option Bool
  | .l => some true
  | .L => none
  | _ => some false

/-- A letter of the transcription. -/
def ofChar : Char → Option LatSeg
  | 'a' => some .a | 'e' => some .e | 'i' => some .i | 'o' => some .o | 'u' => some .u
  | 'l' => some .l | 'r' => some .r | 'L' => some .L
  | 'n' => some .n | 'v' => some .v | 's' => some .s | 'g' => some .g | 'f' => some .f
  | 'p' => some .p | 'b' => some .b
  | _ => none

end LatSeg

/-- The rule D2L learns under the `[+cons]` tier is rule (54),
`Disagree([?lat], {lat}) / [+cons] __ ∘ proj(·, [+cons])`, the liquid `L` taking the opposite
laterality of the tier-adjacent consonant. -/
def latinDissimRule : SearchCopy LatSeg where
  tier := LatSeg.IsCons
  IsSource seg _ := LatSeg.IsCons seg
  IsTarget seg := seg = .L
  relation := .disagree
  value := LatSeg.isLat
  write v _ := if v then .l else .r
  value_write := fun v _ _ ↦ by cases v <;> rfl
  write_value := fun _ seg h hv ↦ by subst h; simp [LatSeg.isLat] at hv

theorem latinDissimRule_isSubsequential : IsSubsequential .left latinDissimRule.apply :=
  latinDissimRule.apply_isSubsequential

/-- The segments of a transcription, the morpheme boundary dropped. -/
def latinSegments (s : String) : List LatSeg := s.toList.filterMap LatSeg.ofChar

/-- The stem of a transcription, before the morpheme boundary. -/
def stem (s : String) : List Char := s.toList.takeWhile (· ≠ '-')

/-- The underlying form of a row, its stem with the affix -aLis. -/
def latinUR (e : Datum) : List LatSeg :=
  (stem e.primaryText).filterMap LatSeg.ofChar ++ [.a, .L, .i, .s]

/-- The surface form of a row. -/
def latinSR (e : Datum) : List LatSeg := latinSegments e.primaryText

/-- The Latin rows, (53). -/
def latinRows : List Datum := Examples.all.filter (·.language = "lati1261")

/-- Rule (54) derives every form of (53) but *lunaris*, including dissimilation (53b) and its
blocking by `r` (53c) or a non-coronal (53d). -/
theorem latin_rows : ∀ e ∈ latinRows, e.id ≠ "belth2026_53b2" →
    latinDissimRule.apply (latinUR e) = latinSR e := by
  decide

theorem lunaris_mispredicted :
    latinDissimRule.apply (latinUR Examples.ex_53b2) ≠ latinSR Examples.ex_53b2 ∧
      latinDissimRule.apply (latinUR Examples.ex_53b2) = latinSegments "lunalis" := by
  decide

/-! ### Finnish backness harmony (52) -/

/-- The forms of a row listing several, its glossed tokens. -/
def forms (e : Datum) : List String := e.glossedTokens.map (·.1)

namespace Finnish

open _root_.Finnish Phonology

/-- `ofChar c` is the segment that the letter `c` of the paper's IPA transcription writes, which
is the Fragment's spelling but for the vowels `ɑ`, `æ` and `ø`. -/
def ofChar : Char → Option Segment
  | 'ɑ' => some a | 'æ' => some ä | 'ø' => some ö
  | c => _root_.Finnish.ofChar c

/-- The segments of a transcription, the morpheme boundary dropped. -/
def segments (cs : List Char) : List Segment := cs.filterMap ofChar

/-- The underlying form of a stem with the essive -nA. -/
def ur (form : String) : List Segment := segments (stem form) ++ [n, A]

-- (52), (51)
theorem rows : ∀ f ∈ forms Examples.ex_51,
    palatalHarmony.searchCopy.apply (ur f) = segments f.toList := by
  decide

end Finnish

/-! ### Turkish vowel harmony (49) -/

namespace Turkish

open _root_.Turkish.Phonology Phonology

/-- `ofChar c` is the segment that the letter `c` of the paper's IPA transcription writes, which
is the Fragment's spelling but for the vowels `ɑ`, `ɯ`, `y` and `ø` and the glide `j`. -/
def ofChar : Char → Option Segment
  | 'ɑ' => some a | 'ɯ' => some ı | 'y' => some ü | 'ø' => some ö | 'j' => some y
  | c => Turkish.Phonology.ofChar c

/-- A letter of an affix, its vowel the archiphoneme unspecified for the harmonic features. -/
def ofAffixChar : Char → Option Segment
  | 'ɑ' | 'e' => some A
  | 'ɯ' | 'i' | 'u' | 'y' => some I
  | c => ofChar c

/-- The segments of a form, the morpheme boundaries dropped. -/
def segments (s : String) : List Segment := s.toList.filterMap ofChar

/-- The underlying form of a stem with its affixes, whose vowels are archiphonemes. -/
def ur (form : String) : List Segment :=
  match (Morphology.Morph.wordsOf form).flatten with
  | [] => []
  | stem :: affixes => stem.filterMap ofChar ++ affixes.flatMap (·.filterMap ofAffixChar)

-- (49a), (46), (47)
theorem rows : ∀ e ∈ [Examples.ex_46, Examples.ex_47], ∀ f ∈ forms e,
    surface (ur f) = segments f := by
  decide +kernel

end Turkish

end Belth2026
