module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
public import Linglib.Phonology.OptimalityTheory.HarmonicSerialism
public import Linglib.Phonology.Tone.Constraints
public import Linglib.Phonology.Tone.Grammatical
public import Linglib.Fragments.Poko.Tone
public import Linglib.Phonology.Autosegmental.Floating
public import Mathlib.Tactic.Linarith

/-!
# McPherson and Lamont (2026): Poko Postlexical Tone Requires Serial, Directional Evaluation

This file formalizes the argument of [mcpherson-lamont-2026] that Poko postlexical tone
resists global constraint evaluation. No ranking or weighting of the paper's four
faithfulness constraints derives both *nān + rī^H + nā* 'I ate a pig' and *kāk^H + rī^H*
'his pig': the ranking argument is an inconsistent set of elementary ranking conditions
derived from the candidates' violation profiles (`parallel_OT_inadequate`), and the
weighting argument a contradiction in which one constraint's weight must both exceed and
fall below a sum of others (`weighted_HG_inadequate`). Directional Harmonic Serialism after
[lamont-2022b], with the constraint against floating tones evaluated left to right,
converges on every attested form, whereas right-to-left evaluation converges on the wrong
form and a count-based constraint yields a divergent tie ([pruitt-2009]); the further
tableaux show the repair of falling contours, the blocking of crowding, and forced
tautomorphemic docking. Every step witness is decided.

## Implementation notes

The stems are those of `Fragments.Poko.Tone`, and an input is their product, each token
sponsored by its position in the phrase, as the source colours each stem; the tableaux,
rankings, and serial derivations are the substrate's harmonic-serialism and tableau
apparatus.

## References

* [mcpherson-lamont-2026]
* [lamont-2022b]
* [pruitt-2009]
-/

@[expose] public section

namespace McPhersonLamont2026

open OptimalityTheory
open OptimalityTheory Autosegmental Poko Tone

/-! ### Candidates (eqs. 57, 58) -/

/-- Winner/loser candidate pairs from [mcpherson-lamont-2026] eqs. 57 and 58. -/
inductive Cand
  /-- (57c) winner of `/nān + rī^H + nā/`: rī's H docks rightward onto nā. -/
  | nanWinner
  /-- In the (57b) loser, the floating H deletes instead. -/
  | nanLoser
  /-- (58c) winner of `/kāk^H + rī^H/`: both floating Hs delete. -/
  | kakWinner
  /-- In the unattested MAX(H)-dominant winner (58b), one H docks and one deletes. -/
  | kakLoser
  deriving DecidableEq

/-! ### Constraints (eq. 7, eq. 59 columns) -/

/-- `MAX(H)` (eq. 7c): one violation per H tone deleted by GEN. -/
def maxH : Constraint Cand :=
  fun
    | .nanWinner => 0   -- H docks rightward (preserved)
    | .nanLoser  => 1   -- H deleted
    | .kakWinner => 2   -- both Hs deleted
    | .kakLoser  => 1   -- one H docks, one deletes

/-- `DEP(link)/H` (eq. 7a): one violation per inserted H-associated link. -/
def depLinkH : Constraint Cand :=
  fun
    | .nanWinner => 1   -- new H link inserted (docking)
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- `MAX(M)` (eq. 7c analogue): one violation per M tone deleted. -/
def maxM : Constraint Cand :=
  fun
    | .nanWinner => 1   -- M overwritten by docking H
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- `MAX(link)/M` (eq. 7b analogue): one violation per deleted M-tone link. -/
def maxLinkM : Constraint Cand :=
  fun
    | .nanWinner => 1
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- The eq. 59 columns; `*FLOAT` factored out per the paper's candidate restriction. -/
def ranking : List (Constraint Cand) := [maxH, depLinkH, maxM, maxLinkM]

abbrev numConstraints : Nat := 4

example : ranking.length = numConstraints := rfl

/-- Constraint indices in `ranking`. -/
abbrev maxHIdx       : Fin numConstraints := 0
abbrev depLinkHIdx   : Fin numConstraints := 1
abbrev maxMIdx       : Fin numConstraints := 2
abbrev maxLinkMIdx   : Fin numConstraints := 3

/-! ### Derived ERCs -/

/-- ERC of a winner/loser pair via `ercOfProfiles` ([prince-2002]). -/
def ercFor (winner loser : Cand) : ERC (Fin numConstraints) :=
  ercOfProfiles (toLex (ranking.get · winner))
    (toLex (ranking.get · loser))

/-- ERC for the `/nān + rī^H + nā/` winner-loser pair. -/
def ercA : ERC (Fin numConstraints) := ercFor .nanWinner .nanLoser

/-- ERC for the `/kāk^H + rī^H/` winner-loser pair. -/
def ercB : ERC (Fin numConstraints) := ercFor .kakWinner .kakLoser

/-- The ranking-paradox support. -/
def pokoSupport : Finset (ERC (Fin numConstraints)) := {ercA, ercB}

/-- The derived `ercA` matches eq. 59 row a: `[W, L, L, L]`. -/
example : ercA maxHIdx = .W ∧ ercA depLinkHIdx = .L ∧
          ercA maxMIdx = .L ∧ ercA maxLinkMIdx = .L := by decide

/-- The derived `ercB` matches eq. 59 row b: `[L, W, W, W]`. -/
example : ercB maxHIdx = .L ∧ ercB depLinkHIdx = .W ∧
          ercB maxMIdx = .W ∧ ercB maxLinkMIdx = .W := by decide

/-! ### The ranking paradox (eq. 59) -/

/-- **Parallel OT cannot model Poko** (eq. 59): the derived support is ERC-inconsistent, since no
ranking of the four constraints satisfies both of its ERCs. -/
theorem parallel_OT_inadequate : ¬ (ERC.linearExtensions pokoSupport).Nonempty := by
  decide +kernel

/-! ### Weighted HG inadequacy -/

/-- Weighted HG cannot model Poko, since `MAX(H)` must both exceed and undercut the other
    three weights' sum (paper p. 32) and no ℚ-weighting satisfies both. -/
theorem weighted_HG_inadequate :
    ¬ ∃ w : Fin numConstraints → ℚ,
        w maxHIdx > w depLinkHIdx + w maxMIdx + w maxLinkMIdx ∧
        w depLinkHIdx + w maxMIdx + w maxLinkMIdx > w maxHIdx := by
  rintro ⟨_, h₁, h₂⟩
  linarith

/-! ### Shared fig. 2 ranking -/

/-- Non-float tail of the fig. 2 ranking, in (60) column order. -/
def rankingTail {u : Form ℕ} : List (Constraint (Candidate u)) :=
  [ starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

/-- The fig. 2 ranking (fig. 3 subset); only `*FLOAT^→` is directional. -/
def stdRanking {u : Form ℕ} : List (Constraint (Candidate u)) :=
  haveTone :: starFloatBlock ++ rankingTail

/-- Left-to-right directional HS over `stdRanking` — the paper's positive analysis. -/
def lrDerivation (input : Form ℕ) : HSDerivation (Candidate input) where
  gen := Candidate.gen
  ranking := stdRanking

/-! ### Fig. 3: LR vs RL over `/kāk^H + rī^H + dō^H/` -/

namespace Fig3

/-- Fig. 3 input `/kāk^H + rī^H + dō^H/`: each M linked, each H floating. -/
def fig3Input : Form ℕ := kak 0 * ri 1 * «do» 2

instance : NeZero fig3Input.upper.length := ⟨by decide⟩
instance : NeZero fig3Input.lower.length := ⟨by decide⟩

/-- The faithful candidate of the input. -/
def fig3 : Candidate fig3Input := .input _

/-- Directional-LR derivation (`*FLOAT^→`). -/
def derivationLR : HSDerivation (Candidate fig3Input) := lrDerivation fig3Input

/-- Mirror under `*FLOAT^←` (`starFloatBlockRev`) — the wrong-form counterexample. -/
def derivationRL : HSDerivation (Candidate fig3Input) where
  gen := Candidate.gen
  ranking := haveTone :: starFloatBlockRev ++ rankingTail

/-- The LR final form `[kāk rī dō]`: all floating Hs deleted (fig. 3 thick line). -/
def attestedForm : Candidate fig3Input :=
  fig3
    |>.deleteTierElem 1   -- delete H-kak
    |>.deleteTierElem 3   -- delete H-ri
    |>.deleteTierElem 5   -- delete H-do

/-- The RL final form `*[kāk rī dó]` (fig. 3; RL evaluation as in the two-stem eq. 61). -/
def starredForm : Candidate fig3Input :=
  fig3
    |>.deleteTierElem 5    -- step 1: delete H-do
    |>.insertLink 3 2  -- step 2: dock H-ri to do (TBU 2)
    |>.deleteTierElem 1    -- step 3: delete H-kak
    |>.deleteTierElem 4    -- step 4: delete M-do (repair *FALL contour)

/-! ### Step witnesses -/

-- (60b)
theorem fig3_LR_step1 :
    derivationLR.stepOptimum fig3 = {fig3.deleteTierElem 1} := by decide

theorem fig3_LR_step2 :
    derivationLR.stepOptimum (fig3.deleteTierElem 1) =
      {(fig3.deleteTierElem 1).deleteTierElem 3} := by decide

theorem fig3_LR_step3 :
    derivationLR.stepOptimum ((fig3.deleteTierElem 1).deleteTierElem 3) =
      {((fig3.deleteTierElem 1).deleteTierElem 3).deleteTierElem 5} := by decide

theorem fig3_LR_converged : derivationLR.Converged attestedForm := by decide

theorem fig3_RL_step1 :
    derivationRL.stepOptimum fig3 = {fig3.deleteTierElem 5} := by decide +kernel

theorem fig3_RL_step2 :
    derivationRL.stepOptimum (fig3.deleteTierElem 5) =
      {(fig3.deleteTierElem 5).insertLink 3 2} := by decide +kernel

theorem fig3_RL_step3 :
    derivationRL.stepOptimum ((fig3.deleteTierElem 5).insertLink 3 2) =
      {((fig3.deleteTierElem 5).insertLink 3 2).deleteTierElem 1} := by decide

theorem fig3_RL_step4 :
    derivationRL.stepOptimum (((fig3.deleteTierElem 5).insertLink 3 2).deleteTierElem 1) =
      {(((fig3.deleteTierElem 5).insertLink 3 2).deleteTierElem 1).deleteTierElem 4} := by
  decide

theorem fig3_RL_converged : derivationRL.Converged starredForm := by decide

theorem fig3_attested_neq_starred : attestedForm ≠ starredForm := by
  intro h
  exact absurd (congrArg Candidate.deleted h) (by decide)

/-! ### Regular HS: the divergent tie (eq. 62) -/

/-- The regular-HS derivation uses the same ranking with the count-based `starFloatCount` for
    `*FLOAT`. -/
def derivationParallel : HSDerivation (Candidate fig3Input) where
  gen := Candidate.gen
  ranking := haveTone :: starFloatCount :: rankingTail

theorem parallel_optimum_three_way_tie :
    derivationParallel.stepOptimum fig3 =
      {fig3.deleteTierElem 1, fig3.deleteTierElem 3, fig3.deleteTierElem 5} := by
  decide

theorem parallel_optimum_card_three :
    (derivationParallel.stepOptimum fig3).card = 3 := by decide

theorem directional_LR_optimum_card_one :
    (derivationLR.stepOptimum fig3).card = 1 := by decide

theorem only_directional_disambiguates_fig3 :
    (derivationLR.stepOptimum fig3).card <
      (derivationParallel.stepOptimum fig3).card := by decide +kernel

end Fig3

/-! ### Eq. (24): LR with *FALL repair -/

namespace Eq24

/-- Eq. (24) input `/nān + rī^H + nā/`; H-rī is the only floating tone. -/
def eq24Input : Form ℕ := nan 0 * ri 1 * na 2

instance : NeZero eq24Input.upper.length := ⟨by decide⟩
instance : NeZero eq24Input.lower.length := ⟨by decide⟩

/-- The faithful candidate of the input. -/
def eq24 : Candidate eq24Input := .input _

/-- Directional-LR derivation over `stdRanking`. -/
def derivationLR : HSDerivation (Candidate eq24Input) := lrDerivation eq24Input

/-- Attested `[nān rī ná]`: H-rī docks onto nā, then *FALL repair deletes M-nā. -/
def attestedForm : Candidate eq24Input :=
  eq24
    |>.insertLink 2 2      -- dock H-rī rightward to nā
    |>.deleteTierElem 3    -- delete M-nā (repair HM contour)

-- (24d)
theorem eq24_step1 :
    derivationLR.stepOptimum eq24 = {eq24.insertLink 2 2} := by decide

-- (24g)
theorem eq24_step2 :
    derivationLR.stepOptimum (eq24.insertLink 2 2) =
      {(eq24.insertLink 2 2).deleteTierElem 3} := by decide

theorem eq24_converged : derivationLR.Converged attestedForm := by decide

end Eq24

/-! ### Eq. (21): phrase-final floating-H deletion -/

namespace Eq21

/-- Eq. (21) input `/nān + rī^H/` (phrase-final): no rightward landing site. -/
def eq21Input : Form ℕ := nan 0 * ri 1

instance : NeZero eq21Input.upper.length := ⟨by decide⟩
instance : NeZero eq21Input.lower.length := ⟨by decide⟩

/-- The faithful candidate of the input. -/
def eq21 : Candidate eq21Input := .input _

/-- Directional-LR derivation; eq. (20)'s `*FLOAT, *TAUTDOCK ≫ MAX(H)` is a sub-ranking. -/
def derivationLR : HSDerivation (Candidate eq21Input) := lrDerivation eq21Input

/-- Attested `[nān rī]`: the floating H deletes. -/
def attestedForm : Candidate eq21Input := eq21.deleteTierElem 2

-- (21b)
theorem eq21_step1 :
    derivationLR.stepOptimum eq21 = {eq21.deleteTierElem 2} := by decide

-- (21d)
theorem eq21_converged : derivationLR.Converged attestedForm := by decide

end Eq21

/-! ### Eq. (27): *CROWD blocks docking onto an MH stem -/

namespace Eq27

/-- Eq. (27) input `/kāk^H + kǎ/`; kǎ carries a linked MH contour. -/
def eq27Input : Form ℕ := kak 0 * ka 1

instance : NeZero eq27Input.upper.length := ⟨by decide⟩
instance : NeZero eq27Input.lower.length := ⟨by decide⟩

/-- The faithful candidate of the input. -/
def eq27 : Candidate eq27Input := .input _

/-- Directional-LR derivation over `stdRanking`. -/
def derivationLR : HSDerivation (Candidate eq27Input) := lrDerivation eq27Input

/-- Attested `[kāk kǎ]`: H-kāk deletes; the MH contour survives. -/
def attestedForm : Candidate eq27Input := eq27.deleteTierElem 1

-- (27b)
theorem eq27_step1 :
    derivationLR.stepOptimum eq27 = {eq27.deleteTierElem 1} := by decide

-- (27e)
theorem eq27_converged : derivationLR.Converged attestedForm := by decide

end Eq27

/-! ### Eq. (30): *M◁L forces tautomorphemic docking -/

namespace Eq30

/-- Eq. (30) input `/kāk^H + ìlí/`; ìlí has L on its first syllable and H on its second
    (L% omitted). -/
def eq30Input : Form ℕ := kak 0 * ili 1

instance : NeZero eq30Input.upper.length := ⟨by decide⟩
instance : NeZero eq30Input.lower.length := ⟨by decide⟩

/-- The faithful candidate of the input. -/
def eq30 : Candidate eq30Input := .input _

/-- Eq. (30) ranking: `stdRanking` plus `*M◁L` above *TAUTDOCK — the inversion that
    licenses tautomorphemic docking (30c). -/
def eq30Ranking : List (Constraint (Candidate eq30Input)) :=
  haveTone :: starMlessL :: starFloatBlock ++
    [ starCrowd 2, starTautDock,
      maxTone TRN.H, starFall, depLinkTone TRN.H,
      maxTone TRN.M, maxTone TRN.L, maxLinkTone TRN.M ]

def derivationLR : HSDerivation (Candidate eq30Input) where
  gen := Candidate.gen
  ranking := eq30Ranking

/-- Attested `[kǎk ìlí]`: H-kāk docks onto its own TBU, making an MH contour. -/
def attestedForm : Candidate eq30Input := eq30.insertLink 1 0

-- (30c)
theorem eq30_step1 :
    derivationLR.stepOptimum eq30 = {eq30.insertLink 1 0} := by decide

-- (30e)
theorem eq30_converged : derivationLR.Converged attestedForm := by decide

end Eq30

/-! ### Eq. (22): HAVETONE drives docking onto a toneless stem -/

namespace Eq22

/-- Eq. (22a) input `/nān + rī^H + ne/`; ne is toneless. -/
def eq22Input : Form ℕ := nan 0 * ri 1 * ne 2

instance : NeZero eq22Input.upper.length := ⟨by decide⟩
instance : NeZero eq22Input.lower.length := ⟨by decide⟩

/-- The faithful candidate of the input. -/
def eq22 : Candidate eq22Input := .input _

/-- Directional-LR derivation over `stdRanking`. -/
def derivationLR : HSDerivation (Candidate eq22Input) := lrDerivation eq22Input

/-- Attested `[nān rī né]`: H-rī docks onto toneless ne. -/
def attestedForm : Candidate eq22Input := eq22.insertLink 2 2

theorem eq22_step1 :
    derivationLR.stepOptimum eq22 = {eq22.insertLink 2 2} := by decide

theorem eq22_converged : derivationLR.Converged attestedForm := by decide

end Eq22

/-! ### Deferred: GEN shift and insert-and-associate ops, L% boundary tone, §§3.3–3.4 tableaux -/

end McPhersonLamont2026

/-! ### `Candidate` strictly extends the [rolle-2018] overwrite encoding -/

namespace Autosegmental

open Tone (TBU TRN)

variable {S M : Type*}

/-- Embed a `Tone.overwrite` output as a form with one morpheme `m` and links `(i, i)`. -/
def Form.ofTBUList (host : List (TBU S)) (m : M) : Form S TRN M :=
  .melody m (host.map TBU.tone) (host.map TBU.seg)
    ((List.range host.length).map fun i ↦ (i, i)).toFinset

theorem Form.ofTBUList_linksTo_subsingleton (host : List (TBU S)) (m : M)
    (i : Fin (Form.ofTBUList host m).lower.length) :
    ((Candidate.input (Form.ofTBUList host m)).linksTo i).length ≤ 1 := by
  have h_all : ∀ n ∈ ((Candidate.input (Form.ofTBUList host m)).linksTo i).map Fin.val,
      n = i.val := fun n hn ↦ by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
    have := Candidate.mem_linksTo.1 hk
    rw [Candidate.input_links] at this
    obtain ⟨a, -, ha⟩ := List.mem_map.1 (List.mem_toFinset.1 (Form.mem_links_melody.1 this))
    simp only [Prod.mk.injEq] at ha
    omega
  have h_count := List.count_eq_length.mpr fun b hb ↦ (h_all b hb).symm
  have := List.nodup_iff_count_le_one.mp
    (((Candidate.input (Form.ofTBUList host m)).nodup_linksTo i).map Fin.val_injective) i.val
  rw [List.length_map] at h_count
  omega

theorem Candidate.exists_multi_tone_TBU :
    ∃ u : Form Unit TRN Unit, ∃ c : Candidate u, ∃ i, 2 ≤ (c.linksTo i).length :=
  ⟨.melody () [.H, .L] [()] ∅,
    (Candidate.input _).insertLink ⟨0, by decide⟩ ⟨0, by decide⟩
      |>.insertLink ⟨1, by decide⟩ ⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩

end Autosegmental
