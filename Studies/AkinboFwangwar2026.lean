module

public import Linglib.Fragments.Mwaghavul.Basic
public import Linglib.Phonology.Autosegmental.Melody
public import Linglib.Phonology.OCP
public import Linglib.Core.Data.List.Forall2
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.Examples.AkinboFwangwar2026
public import Mathlib.Tactic.DeriveFintype

/-!
# Akinbo and Fwangwar (2026): Iconicity and expressiveness of grammatical tones targeting ideophones in Mwaghavul

Mwaghavul derives verbs from ideophones by a segmentally null verbaliser with two lexically
selected allomorphs, whose only exponents are the tunes M and M-H. A singular verb bears M on
every syllable, or M on every nonfinal syllable and H on the final one. A pluractional verb
doubles the ideophone and bears M on every syllable of the reduplicant and H on every syllable
of the base, so corresponding syllables never agree in tone, an iconic disharmony. The derived
verbs occur wherever underived verbs do and stay expressive, against the claimed inverse
relation between grammatical integration and expressiveness. The paper classifies the
verbaliser as replacive-dominant grammatical tone and derives its realisation in Optimality
Theory from constraints anchoring the verbaliser's tones to the edges of roots.

The printed verbs fit replacive dominance and no other dominance type, so the magnitude
iconicity the ideophones carry in their lexical tones is lost in their verbs. The three
tableaux, built from the dataset's ideophones under one constraint set, select the printed
verbs exactly under the rankings with R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Hᵥ and MAX-Tone below
both M anchors. Two dominations the paper states, L-ANCH-Mᵥ ≫ R-ANCH-Mᵥ and
L-ANCH-Hᵥ ≫ MAX-Tone, are not needed.

## Main statements

* `fits_iff`: replacive dominance is the only dominance type that derives every printed verb.
* `selectsWinners_iff`: the rankings under which the tableaux select the printed verbs.
* `exists_selectsWinners_rAnchorM_lAnchorM`: neither L-ANCH-Mᵥ ≫ R-ANCH-Mᵥ nor
  L-ANCH-Hᵥ ≫ MAX-Tone is needed.

## Implementation notes

* An input writes a root's lexical tones as the paper does, one tone for each run of identical
  tones, linked to every syllable of its run.
* The hosts of the verbaliser's tones are the roots, the morphemes sponsoring the syllables,
  since the verbaliser has no segments.

## TODO

* INTEGRITY-Mᵥ forbids an output with two correspondents of the verbaliser's M, and only the
  copying candidate of the first tableau violates it. A `Candidate` shares its input's tiers,
  so neither is represented. The copying candidate's printed row is harmonically bounded by the
  winner's, so leaving it out changes no optimum and no ranking condition.

## References

* [akinbo-fwangwar-2026]
* [rolle-2018]
* [finley-2009]
* [mccarthy-prince-1995]
* [dingemanse-akita-2017]
* [dingemanse-thompson-2020]
-/

@[expose] public section

namespace AkinboFwangwar2026

open Autosegmental OptimalityTheory Mwaghavul
open Tone (TRN TBU Tune Dominance)

/-! ### The verbaliser as replacive-dominant grammatical tone -/

/-- The two lexically selected allomorphs of the verbaliser, VBZ₁ with the tune M and VBZ₂ with
the tune M-H. -/
inductive Verbalizer where
  | m
  | mh
  deriving DecidableEq, Repr

/-- The tune of a verbaliser on a single host: M spreading over every syllable, or M-H anchored
at the right edge. -/
def Verbalizer.tune : Verbalizer → Tune
  | .m => ⟨[.M], .left⟩
  | .mh => ⟨[.M, .H], .right⟩

/-- The verbaliser an ideophone selects, read off its singular verb: VBZ₁ when the verb is level
M. -/
def verbalizer (i : Ideophone) : Option Verbalizer :=
  i.verb.map fun v ↦ if v = i.tones.map fun _ ↦ .M then .m else .mh

/-- The singular verb of a trigger of dominance type `d` with verbaliser `v`: the tune
applied to the ideophone's syllables. -/
def singular (d : Dominance) (v : Verbalizer) (i : Ideophone) : List TRN :=
  (d.apply v.tune i.syllables).map TBU.tone

/-- The pluractional verb of a trigger of dominance type `d`: VBZ₂ on the doubled ideophone,
each of its tones on its own root, M on the reduplicant and H on the base. -/
def pluractional (d : Dominance) (i : Ideophone) : List TRN :=
  (d.apply ⟨[.M], .left⟩ i.syllables ++ d.apply ⟨[.H], .left⟩ i.syllables).map TBU.tone

/-- The printed verbs fit replacive dominance and no other type of [rolle-2018]'s typology: the
singular verb is the selected verbaliser's tune applied to the ideophone, and the pluractional
verb VBZ₂ on the doubled ideophone. -/
theorem fits_iff (d : Dominance) :
    (∀ i ∈ ideophones, i.verb = (verbalizer i).map (singular d · i) ∧
      i.pluractional = pluractional d i) ↔ d = .replacive := by
  cases d <;> decide

/-- The verbaliser overwrites the magnitude iconicity of lexical tone: *wùlàʃ* ‘wide open’ and
*wúláʃ* ‘wide open of small thing’ differ only in tone and have the same verbs. -/
theorem magnitude_overwritten :
    wulash.syllables.map TBU.seg = wulashSmall.syllables.map TBU.seg ∧
      wulash.tones ≠ wulashSmall.tones ∧ wulash.verb = wulashSmall.verb ∧
      wulash.pluractional = wulashSmall.pluractional := by
  decide

/-! ### The descriptive generalisations -/

/-- Every singular verb has M on every syllable, or M on every nonfinal syllable and H on the
final one. -/
theorem verb_melodies :
    ∀ i ∈ ideophones, ∀ v ∈ i.verb,
      v = i.tones.map (fun _ ↦ .M) ∨ v = i.tones.dropLast.map (fun _ ↦ .M) ++ [.H] := by
  decide

/-- Which melody a singular verb has is lexical: *wùlàʃ* ‘wide open’ and *bɨ̀ʃɔ̀l* ‘shabbily
dressed’ have the same tones and select different verbalisers. -/
theorem verbalizer_lexical :
    wulash.tones = bishol.tones ∧ verbalizer wulash = some .m ∧ verbalizer bishol = some .mh := by
  decide

/-- Every pluractional verb has M on every syllable of the reduplicant and H on every syllable
of the base, whichever melody its singular verb has. -/
theorem pluractional_eq :
    ∀ i ∈ ideophones, i.pluractional = i.tones.map (fun _ ↦ .M) ++ i.tones.map (fun _ ↦ .H) := by
  decide

/-- Corresponding syllables of a pluractional verb's reduplicant and base never agree in tone,
the disharmony that depicts distinguishable identity. -/
theorem pluractional_disharmonic :
    ∀ i ∈ ideophones, List.Forall₂ (· ≠ ·) (i.pluractional.take i.tones.length)
      (i.pluractional.drop i.tones.length) := by
  decide

/-! ### Inputs and constraints -/

/-- The morphemes of a derived verb: the ideophonic root, doubled into a reduplicant and a base
in a pluractional verb, and the verbaliser. -/
inductive Morpheme where
  | root
  | red
  | base
  | vbz
  deriving DecidableEq, Repr

/-- A form with syllable TBUs, tones, and the sponsoring morphemes. -/
abbrev Form := Autosegmental.Form Syl TRN Morpheme

/-- The input of an ideophone as the root `m`: one lexical tone for each run of identical tones,
linked to every syllable of its run. -/
def rootInput (m : Morpheme) (i : Ideophone) : Form :=
  .melody m (OCP.collapse i.tones) (i.syllables.map TBU.seg)
    ((List.range i.syllables.length).map fun k ↦ (OCP.runIdx i.tones k, k)).toFinset

/-- The input of a verbaliser: its tones, floating. -/
def Verbalizer.input (v : Verbalizer) : Form := .melody .vbz v.tune.melody [] ∅

/-- The constraints of the analysis: LEFT-ANCHOR and RIGHT-ANCHOR for the verbaliser's M and H
((22)), and MAX-Tone ((23)). -/
inductive Con where
  | lAnchorM
  | rAnchorH
  | rAnchorM
  | lAnchorH
  | maxTone
  deriving DecidableEq, Fintype, Repr

variable {u : Form}

/-- The roots of a form, the morphemes sponsoring its syllables. -/
def roots (u : Form) : List Morpheme := (u.lower.map Sponsored.morpheme).dedup

/-- Syllable `i` bears the verbaliser's tone `t`. -/
def BearsTone (c : Candidate u) (t : TRN) (i : Fin u.lower.length) : Prop :=
  ∃ k ∈ c.linksTo i, u.upper[k].value = t ∧ u.upper[k].morpheme = .vbz

instance (c : Candidate u) (t : TRN) (i : Fin u.lower.length) : Decidable (BearsTone c t i) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- LEFT-ANCHOR-Tᵥ and RIGHT-ANCHOR-Tᵥ ([finley-2009]): the verbaliser's `t` corresponds to the
edge `e` of a root. One violation for each syllable between a root's edge and the nearest
syllable bearing `t`, on the root where they are fewest, and one for every syllable when no root
bears `t`. -/
def anchor (e : Edge) (t : TRN) : Constraint (Candidate u) := fun c ↦
  let fromEdge (l : List (Fin u.lower.length)) := match e with | .left => l | .right => l.reverse
  let distance (h : Morpheme) := (fromEdge (u.lowerOfMorpheme h)).findIdx? (BearsTone c t ·)
  ((roots u).filterMap distance).min?.getD u.lower.length

/-- The constraint set, MAX-Tone counting the deleted tones. -/
def con : ConstraintSet (Candidate u) Con
  | .lAnchorM => anchor .left .M
  | .rAnchorH => anchor .right .H
  | .rAnchorM => anchor .right .M
  | .lAnchorH => anchor .left .H
  | .maxTone => fun c ↦ c.deleted.card

/-- The tones on the syllables of a candidate, left to right. -/
def surface (c : Candidate u) : List TRN := (List.finRange u.lower.length).flatMap c.tierValues

/-- The columns of the printed tableaux: L-ANCH-Mᵥ, R-ANCH-Hᵥ, R-ANCH-Mᵥ, L-ANCH-Hᵥ, MAX-Tone. -/
private def columns : List Con := [.lAnchorM, .rAnchorH, .rAnchorM, .lAnchorH, .maxTone]

private theorem con_exists {p : Con → Prop} :
    (∃ i, p i) ↔ p .lAnchorM ∨ p .rAnchorH ∨ p .rAnchorM ∨ p .lAnchorH ∨ p .maxTone :=
  ⟨fun ⟨i, h⟩ ↦ by cases i <;> simp_all,
    fun h ↦ by rcases h with h | h | h | h | h <;> exact ⟨_, h⟩⟩

private theorem con_forall {p : Con → Prop} :
    (∀ i, p i) ↔ p .lAnchorM ∧ p .rAnchorH ∧ p .rAnchorM ∧ p .lAnchorH ∧ p .maxTone :=
  ⟨fun h ↦ ⟨h _, h _, h _, h _, h _⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ i ↦ by cases i <;> assumption⟩

/-! ### The M verbaliser and an unreduplicated ideophone -/

namespace Tableau24

/-- *wùlàʃ* ‘wide open’ with VBZ₁: one lexical L linked to both syllables, the verbaliser's M
floating. -/
def input : Form := rootInput .root wulash * Verbalizer.m.input

instance : NeZero input.upper.length := ⟨by decide⟩
instance : NeZero input.lower.length := ⟨by decide⟩

/-- The faithful candidate. -/
def cand : Candidate input := .input _

/-- The candidates (24a)–(24e): `(wùlàʃ)₁ M₂`, `(wùlàʃ)₁`, `(wù)₁(lāʃ)₂`, `(wū)₂(làʃ)₁`, and
`(wūlāʃ)₂`. -/
def candA : Candidate input := cand
def candB : Candidate input := cand.deleteTierElem 1
def candC : Candidate input := cand.deleteLink 0 1 |>.insertLink 1 1
def candD : Candidate input := cand.deleteLink 0 0 |>.insertLink 1 0
def candE : Candidate input := cand.deleteTierElem 0 |>.insertLink 1 0 |>.insertLink 1 1

def candidates : List (Candidate input) := [candA, candB, candC, candD, candE]

/-- The printed rows of (24); the input has no H, so every syllable violates the H anchors. -/
private theorem marks :
    candidates.map (fun c ↦ columns.map (con · c)) =
      [[2, 2, 2, 2, 0], [2, 2, 2, 2, 1], [1, 2, 0, 2, 0], [0, 2, 1, 2, 0], [0, 2, 0, 2, 1]] := by
  decide

/-- The tableau selects the spreading of M exactly when MAX-Tone is below both M anchors. It does
not rank L-ANCH-Mᵥ against R-ANCH-Mᵥ, which the paper reads off it. -/
theorem optimal_iff (r : Ranking Con 5) :
    (Tableau.ofRanking con r candidates.toFinset).optimal = {candE} ↔
      r.Dominates .lAnchorM .maxTone ∧ r.Dominates .rAnchorM .maxTone := by
  rw [Tableau.ofRanking_optimal_eq_singleton_iff, and_iff_right (by decide)]
  simp +decide only [candidates, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, ne_eq, false_imp_iff, true_and, and_true, false_and, false_or,
    true_implies, imp_false, con_exists, con_forall, Ranking.Dominates, Fin.lt_def]
  omega

end Tableau24

/-! ### The M-H verbaliser and an unreduplicated ideophone -/

namespace Tableau25

/-- *háŋláɣáp* ‘light-weighted’ with VBZ₂. -/
def input : Form := rootInput .root hanlaghap * Verbalizer.mh.input

instance : NeZero input.upper.length := ⟨by decide⟩
instance : NeZero input.lower.length := ⟨by decide⟩

/-- The faithful candidate. -/
def cand : Candidate input := .input _

/-- The candidates (25a)–(25g): `(háŋláɣáp)₁`, `(hāŋlā)₂(ɣáp)₁`, `(háŋláɣáp)₃`, `(hāŋlāɣāp)₂`,
`(hāŋlā)₂(ɣáp)₃`, `(hāŋ)₂(láɣáp)₃`, and `(hāŋ)₂(lá)₁(ɣáp)₃`. -/
def candA : Candidate input := cand.deleteTierElem 1 |>.deleteTierElem 2
def candB : Candidate input :=
  cand.deleteLink 0 0 |>.deleteLink 0 1 |>.insertLink 1 0 |>.insertLink 1 1 |>.deleteTierElem 2
def candC : Candidate input :=
  cand.deleteTierElem 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 2 1 |>.insertLink 2 2
def candD : Candidate input :=
  cand.deleteTierElem 0 |>.deleteTierElem 2 |>.insertLink 1 0 |>.insertLink 1 1 |>.insertLink 1 2
def candE : Candidate input :=
  cand.deleteTierElem 0 |>.insertLink 1 0 |>.insertLink 1 1 |>.insertLink 2 2
def candF : Candidate input :=
  cand.deleteTierElem 0 |>.insertLink 1 0 |>.insertLink 2 1 |>.insertLink 2 2
def candG : Candidate input :=
  cand.deleteLink 0 0 |>.deleteLink 0 2 |>.insertLink 1 0 |>.insertLink 2 2

def candidates : List (Candidate input) := [candA, candB, candC, candD, candE, candF, candG]

/-- The printed rows of (25). -/
private theorem marks :
    candidates.map (fun c ↦ columns.map (con · c)) =
      [[3, 3, 3, 3, 2], [0, 3, 1, 3, 1], [3, 0, 3, 0, 2], [0, 3, 0, 3, 2], [0, 0, 1, 2, 1],
        [0, 0, 2, 1, 1], [0, 0, 2, 2, 0]] := by
  decide

/-- The tableau selects M then H exactly under R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Hᵥ and
R-ANCH-Mᵥ ≫ MAX-Tone. It does not rank L-ANCH-Mᵥ against R-ANCH-Mᵥ either. -/
theorem optimal_iff (r : Ranking Con 5) :
    (Tableau.ofRanking con r candidates.toFinset).optimal = {candE} ↔
      r.Dominates .rAnchorH .rAnchorM ∧ r.Dominates .rAnchorM .lAnchorH ∧
        r.Dominates .rAnchorM .maxTone := by
  rw [Tableau.ofRanking_optimal_eq_singleton_iff, and_iff_right (by decide)]
  simp +decide only [candidates, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, ne_eq, false_imp_iff, true_and, and_true, false_and, false_or,
    true_implies, imp_false, con_exists, con_forall, Ranking.Dominates, Fin.lt_def]
  omega

end Tableau25

/-! ### The M-H verbaliser and a reduplicated ideophone -/

namespace Tableau26

/-- *jàlpàt* ‘hanging loose’ doubled into a reduplicant and a base, each with its own lexical L,
with VBZ₂. -/
def input : Form := rootInput .red jalpat * rootInput .base jalpat * Verbalizer.mh.input

instance : NeZero input.upper.length := ⟨by decide⟩
instance : NeZero input.lower.length := ⟨by decide⟩

/-- The faithful candidate. -/
def cand : Candidate input := .input _

/-- The candidates (26a)–(26g): `(jàlpàt)₁(jàlpàt)₂`, `(jàl)₁(pāt)₃(jàl)₂(pát)₄`,
`(jāl)₃(pàt)₁(jàl)₄(pàt)₂`, `(jālpāt)₃(jálpát)₄`, `(jāl)₃(pát)₄(jàlpàt)₂`, `(jālpāt jāl)₃(pát)₄`,
and `(jāl)₃(pàt jàl)₁(pát)₄`. -/
def candA : Candidate input := cand
def candB : Candidate input :=
  cand.deleteLink 0 1 |>.insertLink 2 1 |>.deleteLink 1 3 |>.insertLink 3 3
def candC : Candidate input :=
  cand.deleteLink 0 0 |>.insertLink 2 0 |>.deleteLink 1 2 |>.insertLink 3 2
def candD : Candidate input :=
  cand.deleteTierElem 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 2 1
    |>.insertLink 3 2 |>.insertLink 3 3
def candE : Candidate input := cand.deleteTierElem 0 |>.insertLink 2 0 |>.insertLink 3 1
def candF : Candidate input :=
  cand.deleteTierElem 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 2 1
    |>.insertLink 2 2 |>.insertLink 3 3
def candG : Candidate input :=
  cand.deleteLink 0 0 |>.deleteTierElem 1 |>.insertLink 2 0 |>.insertLink 0 2 |>.insertLink 3 3

def candidates : List (Candidate input) := [candA, candB, candC, candD, candE, candF, candG]

/-- The printed rows of (26): an anchor counts the root on which the tone comes closest to its
edge, and all four syllables when the tone is on neither root. -/
private theorem marks :
    candidates.map (fun c ↦ columns.map (con · c)) =
      [[4, 4, 4, 4, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 2], [0, 0, 1, 1, 1],
        [0, 0, 0, 1, 2], [0, 0, 1, 1, 1]] := by
  decide

/-- The tableau ranks no two constraints on its own: it selects M on the reduplicant and H on the
base exactly when MAX-Tone is below a left anchor, a right anchor, and one of R-ANCH-Mᵥ and
L-ANCH-Hᵥ. -/
theorem optimal_iff (r : Ranking Con 5) :
    (Tableau.ofRanking con r candidates.toFinset).optimal = {candD} ↔
      (r.Dominates .lAnchorM .maxTone ∨ r.Dominates .lAnchorH .maxTone) ∧
        (r.Dominates .rAnchorH .maxTone ∨ r.Dominates .rAnchorM .maxTone) ∧
        (r.Dominates .rAnchorM .maxTone ∨ r.Dominates .lAnchorH .maxTone) := by
  rw [Tableau.ofRanking_optimal_eq_singleton_iff, and_iff_right (by decide)]
  simp +decide only [candidates, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, ne_eq, false_imp_iff, true_and, and_true, false_and, false_or,
    true_implies, imp_false, con_exists, con_forall, Ranking.Dominates, Fin.lt_def]
  omega

end Tableau26

/-! ### The ranking -/

/-- A ranking selects the printed verbs: the spreading of M over the root in the first tableau,
M then H in the second, and M on the reduplicant with H on the base in the third. -/
def SelectsWinners (r : Ranking Con 5) : Prop :=
  (Tableau.ofRanking con r Tableau24.candidates.toFinset).optimal = {Tableau24.candE} ∧
    (Tableau.ofRanking con r Tableau25.candidates.toFinset).optimal = {Tableau25.candE} ∧
    (Tableau.ofRanking con r Tableau26.candidates.toFinset).optimal = {Tableau26.candD}

/-- The tableaux select the printed verbs exactly under the rankings with
R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Hᵥ and MAX-Tone below both M anchors. -/
theorem selectsWinners_iff (r : Ranking Con 5) :
    SelectsWinners r ↔ r.Dominates .rAnchorH .rAnchorM ∧ r.Dominates .rAnchorM .lAnchorH ∧
      r.Dominates .rAnchorM .maxTone ∧ r.Dominates .lAnchorM .maxTone := by
  rw [SelectsWinners, Tableau24.optimal_iff, Tableau25.optimal_iff, Tableau26.optimal_iff]
  simp only [Ranking.Dominates, Fin.lt_def]
  omega

/-- Neither L-ANCH-Mᵥ ≫ R-ANCH-Mᵥ nor L-ANCH-Hᵥ ≫ MAX-Tone, both of which the paper states, is
needed: the ranking R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Mᵥ ≫ MAX-Tone ≫ L-ANCH-Hᵥ reverses both and
selects the printed verbs. -/
theorem exists_selectsWinners_rAnchorM_lAnchorM :
    ∃ r : Ranking Con 5, SelectsWinners r ∧ r.Dominates .rAnchorM .lAnchorM ∧
      r.Dominates .maxTone .lAnchorH := by
  obtain ⟨r, hr⟩ := Ranking.exists_dominates_iff (n := 5)
    (fun | .rAnchorH => 0 | .rAnchorM => 1 | .lAnchorM => 2 | .maxTone => 3 | .lAnchorH => 4 :
      Con → ℕ) (by decide) rfl
  refine ⟨r, (selectsWinners_iff r).2 ?_, ?_⟩ <;> simp [hr]

/-- The paper's ranking, L-ANCH-Mᵥ and R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Hᵥ ≫ MAX-Tone, selects
the printed verbs. -/
theorem selectsWinners_of_dominates {r : Ranking Con 5}
    (h₁ : r.Dominates .lAnchorM .rAnchorM) (h₂ : r.Dominates .rAnchorH .rAnchorM)
    (h₃ : r.Dominates .rAnchorM .lAnchorH) (h₄ : r.Dominates .lAnchorH .maxTone) :
    SelectsWinners r :=
  (selectsWinners_iff r).2 ⟨h₂, h₃, _root_.trans h₃ h₄, _root_.trans h₁ (_root_.trans h₃ h₄)⟩

/-- The winners surface as the printed verbs *wūlāʃ*, *hāŋlāɣáp*, and *jālpāt-jálpát*. -/
theorem surface_winners :
    some (surface Tableau24.candE) = wulash.verb ∧ some (surface Tableau25.candE) = hanlaghap.verb ∧
      surface Tableau26.candD = jalpat.pluractional := by
  decide

/-! ### Morphosyntactic integration -/

open Examples in
/-- Every construction attested with the underived verb of (11) is attested with the derived
verb of (12): tense, focus, serial verbs, negation. -/
theorem derived_verbs_integrated :
    ∀ row ∈ Examples.all, row.feature? "verb" = some "underived" →
      ∃ row' ∈ Examples.all, row'.feature? "verb" = some "derived" ∧
        row'.feature? "construction" = row.feature? "construction" := by
  decide

end AkinboFwangwar2026
