module

public import Linglib.Data.Statistics.Schema

/-!
# Bell1984: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Bell1984.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The tables Bell assembles from earlier studies: the standard fricatives of one subject in Mahl's
monitoring experiment, and the percentage a speaker's variables shift when an outsider is an
auditor, when he is the addressee, and when the topic changes.

## References

* [bell-1984]
-/

@[expose] public section

namespace Bell1984

open Data.Statistics

/-- Whether white noise through earphones masks the subject's own voice. -/
inductive Noise where
  /-- No noise: the subject hears himself speak -/
  | quiet
  /-- Noise: white noise prevents the subject hearing himself -/
  | noise
  deriving DecidableEq, Repr, Fintype

/-- Whether the subject faces the interviewer. -/
inductive Facing where
  /-- Facing interviewer: the subject sees the interviewer -/
  | facing
  /-- Not facing: the subject is turned away from the interviewer -/
  | notFacing
  deriving DecidableEq, Repr, Fintype

/-- The three variables of Table 4, on the continuum from Hawaiian creole to standard English. -/
inductive CreoleVariable where
  /-- bin/wen past marker: *bin* or *wen* as the past marker -/
  | binWen
  /-- wan indefinite article: *wan* as the indefinite article -/
  | wan
  /-- Negation with no: negation with *no* -/
  | no
  deriving DecidableEq, Repr, Fintype

/-- The two speakers of Table 5, recorded together with the English outsider. -/
inductive IrishSpeaker where
  /-- Speaker C: speaker C -/
  | c
  /-- Speaker E: speaker E -/
  | e
  deriving DecidableEq, Repr, Fintype

/-- The three variables of Table 5, from Northern Irish to standard English. -/
inductive IrishVariable where
  /-- (ng): the variable (ng) -/
  | ng
  /-- (ai): the variable (ai) -/
  | ai
  /-- (au): the variable printed with a barred u, (aʉ) -/
  | au
  deriving DecidableEq, Repr, Fintype

/-- The four variables of Table 6 in the travel assistant's speech. -/
inductive TravelVariable where
  /-- (h) dropping: dropping of (h) -/
  | hDropping
  /-- (r) flap vs. continuant: flapped against continuant (r) -/
  | rFlap
  /-- Consonant cluster reduction: reduction of consonant clusters -/
  | clusterReduction
  /-- Intervocalic (t) voicing: voicing of intervocalic (t) -/
  | tVoicing
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 1, p. 148: the percentage of the (dh) variable the subject realizes as the
standard fricative. -/
structure DhCell where
  /-- The percentage of standard fricatives. -/
  percent : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 148, by noise and facing; from an experiment; checked against the
page images. -/
def dhStandard : Noise → Facing → DhCell
  | .quiet, .facing => ⟨82⟩
  | .quiet, .notFacing => ⟨78⟩
  | .noise, .facing => ⟨69⟩
  | .noise, .notFacing => ⟨65⟩

/-- A row of Table 2, p. 149: the percentage of the (th) variable the subject realizes as the
standard fricative, printed in parentheses as an estimate from the published figures for (dh)
and for the two variables combined. -/
structure ThCell where
  /-- The estimated percentage of standard fricatives. -/
  percent : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 149, by noise and facing; from an experiment; checked against the
page images. -/
def thStandard : Noise → Facing → ThCell
  | .quiet, .facing => ⟨96⟩
  | .quiet, .notFacing => ⟨72⟩
  | .noise, .facing => ⟨86⟩
  | .noise, .notFacing => ⟨77⟩

/-- A row of Table 4, p. 173: the percentage Sailor shifts a variable toward standard English
with the investigator in the audience. -/
structure SailorShift where
  /-- The shift from the peer group to the peer group with the investigator. -/
  auditor : ℕ
  /-- The shift from the dyad with a friend to the interview with the investigator. -/
  addressee : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 4, p. 173, by variable; from a sociolinguistic survey; checked against the
page images. -/
def sailorShift : CreoleVariable → SailorShift
  | .binWen => ⟨27, 59⟩
  | .wan => ⟨20, 65⟩
  | .no => ⟨39, 60⟩

/-- A row of Table 5, p. 174: the percentage a speaker shifts a variable toward standard English
from talk with a peer, all variables normalized to a base of 100%. -/
structure OutsiderShift where
  /-- The shift with the English outsider as auditor. -/
  auditor : ℕ
  /-- The shift with the English outsider as addressee. -/
  addressee : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 5, p. 174, by speaker and variable; from a sociolinguistic survey; checked
against the page images. -/
def outsiderShift : IrishSpeaker → IrishVariable → OutsiderShift
  | .c, .ng => ⟨18, 22⟩
  | .c, .ai => ⟨1, 15⟩
  | .c, .au => ⟨2, 18⟩
  | .e, .ng => ⟨37, 61⟩
  | .e, .ai => ⟨0, 26⟩
  | .e, .au => ⟨6, 32⟩

/-- A row of Table 6, p. 179: the percentage the travel assistant shifts a variable. -/
structure TravelShift where
  /-- The shift from work to nonwork topics with the same addressees. -/
  topic : ℕ
  /-- The shift from the highest to the lowest class of addressee. -/
  addressee : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 6, p. 179, by variable; from a sociolinguistic survey; checked against the
page images. -/
def travelShift : TravelVariable → TravelShift
  | .hDropping => ⟨25, 32⟩
  | .rFlap => ⟨4, 28⟩
  | .clusterReduction => ⟨25, 37⟩
  | .tVoicing => ⟨31, 55⟩

end Bell1984
