module

public import Linglib.Data.Statistics.Schema

/-!
# Khoo2015: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Khoo2015.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The experiment of section II: participants read a control vignette with a non-modal assertion and a
modal vignette in which Smith says 'Fat Tony might be dead' while the participant knows him to be
alive, and rated on a seven-point scale either whether what the speaker said is false or whether
they would reject it with 'No, ...'. Footnote 13 prints the mean and standard deviation of each
cell. The released survey has 31 participants in the False condition and 30 in the Rejection
condition, 61 against the paper's sixty, which the t-tests' degrees of freedom (59 between the
conditions, 30 within the False one) agree with.

## Raw data

* <https://semanticsarchive.net/Archive/Tc0NmIzY/>: the survey export datamd.xlsx and the vignettes;
  footnote 13 is recomputed from its columns C1 false, C1 no, M false and M no

## References

* [khoo-2015]
-/

@[expose] public section

namespace Khoo2015

open Data.Statistics

/-- The vignette. -/
inductive Sentence where
  /-- Control: the non-modal assertion 'Jim is at home right now' -/
  | control
  /-- Modal: the might-claim 'Fat Tony might be dead' -/
  | modal
  deriving DecidableEq, Repr, Fintype

/-- The question the participant answered. -/
inductive Response where
  /-- False: whether they agree that what the speaker said is false -/
  | judgedFalse
  /-- Rejection: whether they would respond 'No, ...' -/
  | rejection
  deriving DecidableEq, Repr, Fintype

/-- The midpoint of the seven-point scale, labelled 'in between'. (section II.i, p. 519; checked
against the PDF text layer only.) -/
def midpoint : ℕ := 4

/-- A row of footnote 13, p. 520: the mean rating of a vignette under a question. -/
structure Rating where
  /-- The mean rating on the seven-point scale. -/
  mean : Decimal
  /-- The standard deviation. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The cells of footnote 13, p. 520, by sentence and response; from an experiment; recomputed
from the authors' released data by `scripts/check_statistics.py`. -/
def ratings : Sentence → Response → Rating
  | .control, .judgedFalse => ⟨⟨610, 2⟩, ⟨135, 2⟩⟩
  | .control, .rejection => ⟨⟨560, 2⟩, ⟨113, 2⟩⟩
  | .modal, .judgedFalse => ⟨⟨242, 2⟩, ⟨161, 2⟩⟩
  | .modal, .rejection => ⟨⟨503, 2⟩, ⟨177, 2⟩⟩

end Khoo2015
