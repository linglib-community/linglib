module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
public import Linglib.Phonology.OptimalityTheory.HarmonicSerialism
public import Linglib.Phonology.Tone.Constraints
public import Linglib.Phonology.Tone.Grammatical
public import Linglib.Fragments.Poko.Tone
public import Linglib.Phonology.Autosegmental.Floating
public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Mathlib.Tactic.Linarith

/-!
# McPherson and Lamont (2026): Poko Postlexical Tone Requires Serial, Directional Evaluation

This file formalizes the argument of [mcpherson-lamont-2026] that Poko postlexical tone
resists global constraint evaluation. No ranking or weighting of the paper's four
faithfulness constraints derives both *nān + rī^H + nā* 'I ate a pig' and *kāk^H + rī^H*
'his pig'. The violation profiles of the attested forms and their rivals give [antithetical
elementary ranking conditions, which no ranking satisfies](##parallel_OT_inadequate), and
[no weighting makes both attested forms the more harmonic](##weighted_HG_inadequate), since
the weight of MAX(H) would have to exceed the sum of the other three and fall below it.
Directional Harmonic Serialism after [lamont-2022b], with the constraint against floating tones
evaluated left to right, converges on every attested form, whereas right-to-left evaluation
converges on the wrong form and a count-based constraint yields a divergent tie
([pruitt-2009]); the further tableaux show the repair of falling contours, the blocking of
crowding, and forced tautomorphemic docking. Every step witness is decided.

## Implementation notes

The stems are those of `Fragments.Poko.Tone`, and an input is their product, each token
sponsored by its position in the phrase, as the source colours each stem; the tableaux,
rankings, and serial derivations are the substrate's harmonic-serialism and tableau
apparatus.

## Errata

* For `/kāk^H + rī^H/` the paragraph introducing the support (59) requires the weight of MAX(H)
  to be less than half the sum of the other three weights. The violation profiles of (58b) and
  (58c) require only that it be less than the sum, since (58b) also deletes an H; that no
  weighting fits both inputs is unaffected.
* Row (59a) writes the loser (57b) before the winner (57c), the reverse of row (59b), though its
  W and L are read with (57c) as the winner.

## References

* [mcpherson-lamont-2026]
* [lamont-2022b]
* [pruitt-2009]
* [prince-2002]
-/

@[expose] public section

namespace McPhersonLamont2026

open OptimalityTheory
open OptimalityTheory Autosegmental HarmonicGrammar Poko Tone

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

/-! ### Eqs. (57)–(59): parallel evaluation -/

/-- The four faithfulness constraints of the parallel tableaux (57) and (58), in their column
    order. `*FLOAT` is left out, since every candidate the support (59) compares satisfies it. -/
def faithfulness {u : Form ℕ} : ConstraintSet (Candidate u) (Fin 4) :=
  ![maxTone TRN.H, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M]

/-- The ERC of a winner over a loser on `faithfulness` ([prince-2002]). -/
def ercFor {u : Form ℕ} (winner loser : Candidate u) : ERC (Fin 4) :=
  ercOfProfiles (faithfulness · winner) (faithfulness · loser)

namespace Eq57

/-- (57b), the rival of the attested `Eq24.attestedForm` (57c): the floating H of rī deletes. -/
def loser : Candidate Eq24.eq24Input := Eq24.eq24.deleteTierElem 2

-- (57c)
theorem faithfulness_attestedForm (i : Fin 4) :
    faithfulness i Eq24.attestedForm = ![0, 1, 1, 1] i := by
  revert i; decide

-- (57b)
theorem faithfulness_loser (i : Fin 4) : faithfulness i loser = ![1, 0, 0, 0] i := by
  revert i; decide

end Eq57

namespace Eq58

/-- Eq. (58) input `/kāk^H + rī^H/`: each M linked, each H floating. -/
def eq58Input : Form ℕ := kak 0 * ri 1

instance : NeZero eq58Input.upper.length := ⟨by decide⟩
instance : NeZero eq58Input.lower.length := ⟨by decide⟩

/-- The faithful candidate of the input. -/
def eq58 : Candidate eq58Input := .input _

/-- (58c), attested `[kāk rī]`: both floating Hs delete. -/
def attestedForm : Candidate eq58Input := (eq58.deleteTierElem 1).deleteTierElem 3

/-- (58b): the H of kāk docks onto rī, whose M and H both delete. -/
def loser : Candidate eq58Input := ((eq58.insertLink 1 1).deleteTierElem 2).deleteTierElem 3

-- (58c)
theorem faithfulness_attestedForm (i : Fin 4) :
    faithfulness i attestedForm = ![2, 0, 0, 0] i := by
  revert i; decide

-- (58b)
theorem faithfulness_loser (i : Fin 4) : faithfulness i loser = ![1, 1, 1, 1] i := by
  revert i; decide

end Eq58

-- the candidates the support (59) compares satisfy *FLOAT
example : starFloatCount Eq24.attestedForm = 0 ∧ starFloatCount Eq57.loser = 0 ∧
    starFloatCount Eq58.attestedForm = 0 ∧ starFloatCount Eq58.loser = 0 := by
  decide

/-- Row (59a): the attested form of `/nān + rī^H + nā/` over its rival (57b). -/
def ercA : ERC (Fin 4) := ercFor Eq24.attestedForm Eq57.loser

/-- Row (59b): the attested form of `/kāk^H + rī^H/` over its rival (58b). -/
def ercB : ERC (Fin 4) := ercFor Eq58.attestedForm Eq58.loser

-- (59a)
theorem ercA_eq : ercA = ![.W, .L, .L, .L] := by
  funext i
  simp only [ercA, ercFor, Eq57.faithfulness_attestedForm, Eq57.faithfulness_loser]
  revert i; decide

-- (59b)
theorem ercB_eq_neg : ercB = -ercA := by
  rw [ercA_eq]
  funext i
  simp only [ercB, ercFor, Eq58.faithfulness_attestedForm, Eq58.faithfulness_loser]
  revert i; decide

/-- **Parallel OT cannot model Poko**: the two rows of the support (59) are antithetical, so no
ranking of the four faithfulness constraints derives both attested forms. -/
theorem parallel_OT_inadequate : ¬ (ERC.linearExtensions {ercA, ercB}).Nonempty := by
  rintro ⟨r, hr⟩
  rw [ERC.mem_linearExtensions] at hr
  refine ERC.not_satisfiedBy_neg ⟨0, by rw [ercA_eq]; decide⟩
    (hr ercA (Finset.mem_insert_self _ _)) ?_
  rw [← ercB_eq_neg]
  exact hr ercB (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- **Harmonic Grammar cannot model Poko**: no weighting of the four faithfulness constraints
makes both attested forms more harmonic than their rivals in (57) and (58), since MAX(H) would
have to outweigh the other three together for `/nān + rī^H + nā/` and weigh less than them for
`/kāk^H + rī^H/`. -/
theorem weighted_HG_inadequate :
    ¬ ∃ w : Fin 4 → ℝ, harmonyDominates faithfulness w Eq24.attestedForm Eq57.loser ∧
      harmonyDominates faithfulness w Eq58.attestedForm Eq58.loser := by
  rintro ⟨w, h₁, h₂⟩
  simp only [harmonyDominates_iff, harmonyScore_eq_neg_sum, Fin.sum_univ_four,
    Eq57.faithfulness_attestedForm, Eq57.faithfulness_loser, Eq58.faithfulness_attestedForm,
    Eq58.faithfulness_loser] at h₁ h₂
  norm_num at h₁ h₂
  linarith

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
