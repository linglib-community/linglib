module

public import Linglib.Data.Wordlist.Padgett2002
public import Linglib.Fragments.Turkish.Phonology
public import Linglib.Phonology.FeatureGeometry
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.Data.List.Iterate

/-!
# Padgett (2002): feature classes in phonology

Padgett argues that a constraint naming a feature class targets the features of the class
directly and individually, not through a class node. Classes are sets of features, the unions
(25), which carry over the classes of the geometry (3), and SPREAD(COLOR) (26) is violated once
for each segment an autosegment of [back] or [round] fails to reach, so it can be satisfied in
part. Turkish suffix harmony is then one Color harmony: under IDENT_Rt ≫ *[+rnd, −hi] ≫
SPREAD(COLOR) ≫ IDENT a nonhigh suffix vowel agrees with the root in [back] alone, while spreading
a Color node carries both features or neither.

## Main definitions

* `Node`, `node`: the geometry (3); `laryngeal`, `oral`, `vplace`, `height`, `color`: (25).
* `Tier`, `Tier.spread`: the autosegments of one feature over a word, and SPREAD (26).
* `tableau`: the Turkish grammar of (17)–(22), over every fully specified candidate.

## Main results

* `classes_eq_featureClass`: the classes (25) are those of the nodes of (3).
* `Tier.spread_eq_zero_iff`: SPREAD holds iff the feature has one autosegment.
* `predict_eq_attested`, `notMem_predict_marked`: the grammar derives the suffixed forms of
  (6), p. 85 and (21), and not the starred ones; `predict_suffix_mem_reduced`: only the suffix
  vowels of (13); `predictTotal_son_lAr`: the reverse ranking gives total Color harmony.
* `ne_colorSpreading`: no spreading of a Color node yields [son-lar] or [petrolʸ-ü] ((9), (23)).

## Implementation notes

Candidates are fully specified, as from (12) on. The segments are the vowels, as in (12)–(20),
and in (21)–(22) the root's last vowel, the palatal lateral, which shares its [round]
(footnote 6), and the suffix vowels, unspecified for color (§3.3): /I/ is the fragment's high
archiphoneme and /A/ the meet of the four nonhigh vowels. [pharyngeal] has no counterpart in the
inventory, so Place is left out of (25).

## TODO

* The paper marks four IDENT violations on (22b) and (22c), where counting by segment and
  feature, as in (17c) and (20d), gives three (`profile_22`); the winner is unaffected.
* HAVEPLACE, *PLACE and OCP(PLACE) ((27)–(29)), and the dissimilation of §5.

## References

* [J. Padgett, *Feature Classes in Phonology* (2002)][padgett-2002]
* [G. N. Clements and E. Sezer, *Vowel and consonant disharmony in Turkish*
  (1982)][clements-sezer-1982]
-/

@[expose] public section

namespace Padgett2002

open Phonology Phonology.FeatureGeometry OptimalityTheory Turkish.Phonology

/-! ### The geometry (3) and the classes (25) -/

/-- The class nodes of (3): Root over Laryngeal and Place, Place over Oral, Oral over VPlace,
and VPlace over Height and Color. -/
inductive Node where
  | root | laryngeal | place | oral | vplace | height | color
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node, the root fixed. -/
def pred : Node → Node
  | .root | .laryngeal | .place => .root
  | .oral => .place
  | .vplace => .oral
  | .height | .color => .vplace

/-- `a ≤ b` when `a` lies on the walk from `b` up to the root. -/
instance : PartialOrder Node where
  le a b := a ∈ List.iterate pred b (Fintype.card Node)
  le_refl := by decide
  le_trans := by decide +kernel
  le_antisymm := by decide

instance : DecidableLE Node := fun a b ↦ inferInstanceAs (Decidable (a ∈ List.iterate pred b _))

end Node

/-- The node each feature of (3) hangs from, with [aspirated] and [glottalized] read as [spread
glottis] and [constricted glottis]. -/
def node : Feature → Option Node
  | .spreadGlottis | .voice | .constrGlottis => some .laryngeal
  | .nasal => some .root
  | .labial | .coronal | .dorsal => some .oral
  | .low | .high => some .height
  | .back | .round => some .color
  | _ => none

/-- Laryngeal, the union of Aspirated, Voiced and Glottalized (25). -/
def laryngeal : Finset Feature := {.spreadGlottis} ∪ {.voice} ∪ {.constrGlottis}

/-- Color, the union of Back and Round (25). -/
def color : Finset Feature := {.back} ∪ {.round}

/-- Height, the union of Low and High (25). -/
def height : Finset Feature := {.low} ∪ {.high}

/-- VPlace, the union of Height and Color (25). -/
def vplace : Finset Feature := height ∪ color

/-- Oral, the union of Labial, Coronal, Dorsal and VPlace (25). -/
def oral : Finset Feature := {.labial} ∪ {.coronal} ∪ {.dorsal} ∪ vplace

/-- The classes (25) are the feature classes of the nodes of (3), which they carry over. -/
theorem classes_eq_featureClass :
    laryngeal = featureClass node .laryngeal ∧ oral = featureClass node .oral ∧
      vplace = featureClass node .vplace ∧ height = featureClass node .height ∧
      color = featureClass node .color := by
  decide

/-! ### SPREAD (26) -/

/-- The autosegments of one feature over a word of `n` segments, each linked to a run of
segments and every segment to one of them: `starts` are the segments at which an autosegment
begins, and `value j` is the value of the autosegment segment `j` is linked to. -/
structure Tier (n : ℕ) where
  /-- The segments at which an autosegment begins. -/
  starts : Finset (Fin n)
  /-- The value of each segment's autosegment. -/
  value : Fin n → Bool
  /-- An autosegment begins at the first segment. -/
  zero_mem : ∀ j : Fin n, j.val = 0 → j ∈ starts := by decide
  /-- A segment at which no autosegment begins shares the previous segment's. -/
  value_eq : ∀ j k : Fin n, k.val = j.val + 1 → k ∉ starts → value k = value j := by decide

namespace Tier

variable {n : ℕ}

/-- A tier is its starts and values, the conditions being propositions. -/
def equivSubtype : Tier n ≃ {p : Finset (Fin n) × (Fin n → Bool) //
    (∀ j : Fin n, j.val = 0 → j ∈ p.1) ∧
      ∀ j k : Fin n, k.val = j.val + 1 → k ∉ p.1 → p.2 k = p.2 j} where
  toFun t := ⟨(t.starts, t.value), t.zero_mem, t.value_eq⟩
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩

instance : DecidableEq (Tier n) := equivSubtype.decidableEq

instance : Fintype (Tier n) := .ofEquiv _ equivSubtype.symm

variable (t : Tier n)

/-- Segment `j` is linked to the autosegment beginning at `a`: `j` is at or after `a` and
before every later start. -/
def Linked (a j : Fin n) : Prop := a ≤ j ∧ ∀ b ∈ t.starts, a < b → j < b

instance (a j : Fin n) : Decidable (t.Linked a j) := inferInstanceAs (Decidable (_ ∧ _))

/-- The violations of SPREAD (26): each autosegment violates it once for every segment of the
word it is not linked to. -/
def spread : ℕ := ∑ a ∈ t.starts, (Finset.univ.filter (¬ t.Linked a ·)).card

/-- SPREAD holds of a tier iff it has at most one autosegment, every segment then sharing it. -/
theorem spread_eq_zero_iff : t.spread = 0 ↔ t.starts.card ≤ 1 := by
  simp only [spread, Finset.sum_eq_zero_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    not_not, Finset.mem_univ, true_implies, Finset.card_le_one]
  constructor
  · intro h a ha b hb
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact lt_irrefl b ((@h a ha b).2 b hb hlt)
    · exact lt_irrefl a ((@h b hb a).2 a ha hlt)
  · intro h a ha j
    refine ⟨?_, fun b hb hab ↦ absurd (h a ha b hb) hab.ne⟩
    by_contra hja
    have h0 : (⟨0, by omega⟩ : Fin n) ∈ t.starts := t.zero_mem _ rfl
    rcases Nat.eq_zero_or_pos a.val with ha0 | ha0
    · exact hja (Fin.le_def.2 (by omega))
    · exact absurd (h a ha _ h0) (fun he ↦ by simp [Fin.ext_iff] at he; omega)

end Tier

/-! ### Turkish -/

/-- A candidate gives a tier to each feature of Color. -/
abbrev Candidate (n : ℕ) := color → Tier n

/-- [back] as a feature of Color. -/
def back : color := ⟨.back, by decide⟩

/-- [round] as a feature of Color. -/
def round : color := ⟨.round, by decide⟩

variable {n : ℕ} (x : Fin n → Segment) (r : ℕ)

/-- The output of a candidate: each input segment with the values of its color autosegments. -/
def surface (c : Candidate n) (j : Fin n) : Segment :=
  ((x j).setFeature .back ((c back).value j)).setFeature .round ((c round).value j)

/-- IDENT_Rt (16), summed over Color: a segment of the root, the first `r`, keeps the input
value of each color feature. -/
def identRoot (c : Candidate n) : ℕ :=
  ∑ f, (Finset.univ.filter fun j : Fin n ↦ j.val < r ∧ ¬ (x j).HasValue f.1 ((c f).value j)).card

/-- *[+rnd, −hi]: a nonhigh segment is not round. -/
def noRoundNonhigh (c : Candidate n) : ℕ :=
  (Finset.univ.filter fun j ↦ (c round).value j = true ∧ (x j).HasValue .high false).card

/-- SPREAD(COLOR) (10, 26), summed over the features of Color. -/
def spreadColor (c : Candidate n) : ℕ := ∑ f, (c f).spread

/-- IDENT (11), summed over Color: a segment keeps the input value of each color feature,
unspecified counting as a value. -/
def ident (c : Candidate n) : ℕ :=
  ∑ f, (Finset.univ.filter fun j : Fin n ↦ ¬ (x j).HasValue f.1 ((c f).value j)).card

/-- IDENT_Rt ≫ *[+rnd, −hi] ≫ SPREAD(COLOR) ≫ IDENT, the ranking of (17)–(22), over every
candidate. -/
def tableau : Tableau (Candidate n) 4 :=
  .ofList Finset.univ [identRoot x r, noRoundNonhigh x, spreadColor, ident x]

/-- The reverse ranking of SPREAD(COLOR) and *[+rnd, −hi], total class spreading as in Kirghiz
(p. 93). -/
def tableauTotal : Tableau (Candidate n) 4 :=
  .ofList Finset.univ [identRoot x r, spreadColor, noRoundNonhigh x, ident x]

/-- The outputs of the winners of the grammar for the segments `w`, the first `r` of the root. -/
def predict (w : List Segment) (r : ℕ) : Finset (List Segment) :=
  (tableau (fun j : Fin w.length ↦ w[j]) r).optimal.image fun c ↦
    List.ofFn (surface (fun j : Fin w.length ↦ w[j]) c)

/-- The outputs of the winners under the reverse ranking. -/
def predictTotal (w : List Segment) (r : ℕ) : Finset (List Segment) :=
  (tableauTotal (fun j : Fin w.length ↦ w[j]) r).optimal.image fun c ↦
    List.ofFn (surface (fun j : Fin w.length ↦ w[j]) c)

/-! ### Inputs and forms -/

/-- /A/, the nonhigh suffix vowel unspecified for color: what the four nonhigh vowels share. -/
def A' : Segment := a ⊓ e ⊓ o ⊓ ö

/-- The segment a segment symbol of the paper's transcription contributes to harmony: a vowel,
with `ɨ` for `ı`, or the palatal lateral `lʸ`. -/
def harmonySegment (g : String) : Option Segment :=
  [("a", a), ("e", e), ("ɨ", ı), ("i", i), ("o", o), ("ö", ö), ("u", u), ("ü", ü),
    ("lʸ", l')].lookup g

/-- A root from its last vowel on, the segments after the vowel sharing its [round]
(footnote 6). -/
def shareRound : List Segment → List Segment
  | [] => []
  | v :: w => v :: w.map (Function.update · .round (v .round))

/-- The suffix vowels of a cell, in the order of the suffixes: /A/ of the plural -lAr, then /I/ of
the accusative -I or the genitive -In (§3.3). -/
def suffixVowels (cell : Wordlist.Cell) : List Segment :=
  (if cell.number = ↑UD.Number.Plur then [A'] else []) ++
    if cell.case = ↑UD.Case.Nom then [] else [I]

/-! ### The tableaux (14), (20) and (22) -/

/-- The candidate with tier `b` for [back] and tier `r` for [round]. -/
def cand (b r : Tier n) : Candidate n := fun f ↦ if f = back then b else r

/-- /son-lAr/ of (14) and (17). -/
def sonlAr : Fin 2 → Segment := ![o, A']

/-- (14a) {[son-lor]+B}+R, total Color harmony. -/
def cand14a : Candidate 2 :=
  cand { starts := {0}, value := ![true, true] } { starts := {0}, value := ![true, true] }

/-- (14b) [{son-}+R{lar}−R]+B, [back] harmony alone. -/
def cand14b : Candidate 2 :=
  cand { starts := {0}, value := ![true, true] } { starts := {0, 1}, value := ![true, false] }

/-- (14c) {[son-]+B[lör]−B}+R, [round] harmony alone. -/
def cand14c : Candidate 2 :=
  cand { starts := {0, 1}, value := ![true, false] } { starts := {0}, value := ![true, true] }

/-- (14d) [{son-}+R]+B[{lar}−R]+B, no harmony. -/
def cand14d : Candidate 2 :=
  cand { starts := {0, 1}, value := ![true, true] } { starts := {0, 1}, value := ![true, false] }

/-- The violations of (14) and (17a,b), IDENT_Rt first: partial class spreading (14b) violates
SPREAD(COLOR) twice, and no harmony (14d) four times. -/
theorem profile_14 :
    ofLex ((tableau sonlAr 1).profile cand14a) = ![0, 2, 0, 2] ∧
      ofLex ((tableau sonlAr 1).profile cand14b) = ![0, 1, 2, 2] ∧
      ofLex ((tableau sonlAr 1).profile cand14c) = ![0, 2, 2, 2] ∧
      ofLex ((tableau sonlAr 1).profile cand14d) = ![0, 1, 4, 2] := by
  decide

/-- Partial class spreading (14b) is the sole winner over every candidate. -/
theorem optimal_sonlAr : (tableau sonlAr 1).optimal = {cand14b} := by
  decide +kernel

/-- /pul-lAr-In/ of (20). -/
def pullArIn : Fin 3 → Segment := ![u, A', I]

/-- (20b) [{pul-}+R{lar-ɨn}−R]+B, the attested form. -/
def cand20b : Candidate 3 :=
  cand { starts := {0}, value := ![true, true, true] }
    { starts := {0, 1}, value := ![true, false, false] }

/-- (20c) [{pul-}+R{lar-}−R{un}+R]+B, with the final vowel round on its own. -/
def cand20c : Candidate 3 :=
  cand { starts := {0}, value := ![true, true, true] }
    { starts := {0, 1, 2}, value := ![true, false, true] }

/-- In (20) the attested form violates SPREAD(COLOR) three times and the transparent (20c) six. -/
theorem profile_20 :
    ofLex ((tableau pullArIn 1).profile cand20b) = ![0, 0, 3, 4] ∧
      ofLex ((tableau pullArIn 1).profile cand20c) = ![0, 0, 6, 4] := by
  decide

/-- /(petr)olʸ-I/ of (22), the lateral sharing the vowel's [+round]. -/
def petrolI : Fin 3 → Segment := ![o, Function.update l' .round (some true), I]

/-- (22a) {[o]+B[lʸ-ü]−B}+R, the attested form. -/
def cand22a : Candidate 3 :=
  cand { starts := {0, 1}, value := ![true, false, false] }
    { starts := {0}, value := ![true, true, true] }

/-- (22b) {[ölʸ-ü]−B}+R. -/
def cand22b : Candidate 3 :=
  cand { starts := {0}, value := ![false, false, false] }
    { starts := {0}, value := ![true, true, true] }

/-- (22c) {[ol-u]+B}+R. -/
def cand22c : Candidate 3 :=
  cand { starts := {0}, value := ![true, true, true] }
    { starts := {0}, value := ![true, true, true] }

/-- (22d) {[o]+B[lʸ]+R{-ɨ]−B}−R. -/
def cand22d : Candidate 3 :=
  cand { starts := {0, 1}, value := ![true, false, false] }
    { starts := {0, 2}, value := ![true, true, false] }

/-- The violations of (22), the lateral counted. The paper marks four IDENT violations on (22b)
and (22c), where counting by segment and feature gives three. -/
theorem profile_22 :
    ofLex ((tableau petrolI 2).profile cand22a) = ![0, 1, 3, 2] ∧
      ofLex ((tableau petrolI 2).profile cand22b) = ![1, 1, 0, 3] ∧
      ofLex ((tableau petrolI 2).profile cand22c) = ![1, 1, 0, 3] ∧
      ofLex ((tableau petrolI 2).profile cand22d) = ![0, 1, 6, 2] := by
  decide

/-- (22a) is the sole winner: [back] and [round] spread from different segments. -/
theorem optimal_petrolI : (tableau petrolI 2).optimal = {cand22a} := by
  decide +kernel

/-! ### The forms -/

/-- The segments a form contributes to harmony. -/
def harmony (w : CLDF.Wordlist.Form Wordlist.Cell) : List Segment :=
  w.segments.filterMap harmonySegment

/-- The position of the last vowel of a stem. -/
def lastVowel (s : List Segment) : ℕ := s.length - 1 - s.reverse.findIdx (· ∈ vowels)

variable (s : List Segment) (w : CLDF.Wordlist.Form Wordlist.Cell)

/-- The input of a form with stem `s`: the stem from its last vowel on, a following lateral
sharing the vowel's [round], and the suffix vowels of the form's cell. -/
def input : List Segment := shareRound (s.drop (lastVowel s)) ++ suffixVowels w.cell

/-- The vowels the grammar predicts for a form with stem `s`, the root being the stem from its
last vowel. -/
def predictedVowels : Finset (List Segment) :=
  (predict (input s w) (s.length - lastVowel s)).image (·.filter (· ∈ vowels))

/-- The vowels of a form with stem `s`, from the stem's last vowel on. -/
def attestedVowels : List Segment := ((harmony w).drop (lastVowel s)).filter (· ∈ vowels)

/-- The grammar derives the vowels of every suffixed form of (6), p. 85 and (21) from its stem,
the first form of its paradigm. -/
theorem predict_eq_attested : ∀ p ∈ Wordlist.paradigms, ∀ s ∈ p.forms.head?, ∀ w ∈ p.forms.tail,
    predictedVowels (harmony s) w = {attestedVowels (harmony s) w} := by
  decide +kernel

/-- The grammar derives neither starred form of p. 85, *[pul-lar-un] or *[yüz-ler-ün]. -/
theorem notMem_predict_marked : ∀ w ∈ Wordlist.marked, ∀ p ∈ Wordlist.paradigms,
    p.lexeme.id = w.lexeme.id → ∀ s ∈ p.forms.head?,
      attestedVowels (harmony s) w ∉ predictedVowels (harmony s) w := by
  decide +kernel

/-- Harmony yields only the vowels of (13) in a suffix, whatever the root vowel. -/
theorem predict_suffix_mem_reduced :
    ∀ v ∈ vowels, ∀ s ∈ [I, A'], ∀ w ∈ predict [v, s] 1, ∀ x ∈ w.drop 1,
      x ∈ ({i, ü, ı, u, e, a} : Finset Segment) := by
  decide +kernel

/-- Under the reverse ranking a nonhigh suffix vowel agrees in both features, [son-lor] and
[yüz-lör]. -/
theorem predictTotal_son_lAr : predictTotal [o, A'] 1 = {[o, o]} ∧
    predictTotal [ü, A'] 1 = {[ü, ö]} := by
  decide +kernel

/-! ### Class nodes -/

/-- Spreading the Color node of (3) from `src` onto `tgt`. -/
def colorSpreading (src tgt : Segment) : Segment := (featureClass node .color).piecewise src tgt

/-- Spreading a Color node is all or none: the target takes both features of Color. -/
theorem eqOn_colorSpreading (src tgt : Segment) :
    Set.EqOn (colorSpreading src tgt) src ↑color :=
  classes_eq_featureClass.2.2.2.2 ▸ eqOn_piecewise_of_le src tgt le_rfl

/-- No spreading or non-spreading of a Color node yields the suffix vowel of [son-lar] (9) or of
[petrolʸ-ü] (23). -/
theorem ne_colorSpreading : colorSpreading o A' ≠ a ∧ A' ≠ a ∧ colorSpreading o I ≠ ü ∧
    colorSpreading l' I ≠ ü ∧ I ≠ ü := by
  decide

end Padgett2002
