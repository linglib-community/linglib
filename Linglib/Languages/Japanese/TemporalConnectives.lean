module

public import Linglib.Semantics.Tense.Connective

/-!
# Japanese temporal connectives

Lexical entries for the Japanese temporal connectives *mae* 'before', *ato* 'after' and *toki*
'when'. A *mae*-clause takes the present, the non-past in *-(r)u*, even under a past matrix, and
an *ato*-clause the past in *-ta*, while a *toki*-clause takes either. The relative-tense account
that Arregui and Kusumoto attribute to Ogihara and their own account, on which *mae* and *ato*
select a tensed clause, both derive the asymmetry. Ogihara and Steinert-Threlkeld use the
non-past of *mae* for a past *before*-sentence free of the veridical implicature of an English
past *before*-clause.

## References

* [ogihara-1996]
* [arregui-kusumoto-1998]
* [ogihara-steinert-threlkeld-2024]
-/

@[expose] public section

namespace Japanese.TemporalConnectives

open Tense

/-- *mae* 前 'before' takes a present complement under a past, as in *Junko-ga kuru mae-ni
Satoshi-wa kaetta* 'Satoshi left before Junko came'. -/
def mae : Connective where
  form := "mae"
  relation := .before
  tense := some .present

/-- *ato* 後 'after' takes a past complement, as in *Junko-ga kita ato-ni Satoshi-wa kaetta*
'Satoshi left after Junko came'. -/
def ato : Connective where
  form := "ato"
  relation := .after
  tense := some .past

/-- *toki* 時 'when' takes a past or a present complement, as in *Satoshi-ga kita toki Junko-wa
heya-ni ita* 'Junko was in her room when Satoshi came'. -/
def toki : Connective := { form := "toki", relation := .when_ }

end Japanese.TemporalConnectives
