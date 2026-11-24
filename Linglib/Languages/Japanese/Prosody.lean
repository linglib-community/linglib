module

public import Mathlib.Data.Nat.Notation

/-!
# Japanese prosody

Tokyo Japanese has a lexical pitch accent, at most one per word, on a mora: *ame* 'candy'
is unaccented and *a'me* 'rain' accented on its first mora, *uma'i* 'delicious' accented and
*amai* 'sweet' not. The entries are the minimal pairs and accentual-phrase materials of
Kawahara and of Beckman and Pierrehumbert.

## Main definitions

* `Japanese.Prosody.ProsodicEntry` — a word with its mora count and accent position

## References

* [beckman-pierrehumbert-1986]
* [kawahara-2015]
-/

@[expose] public section

namespace Japanese.Prosody

/-- A Japanese lexical entry with its prosodic specification. The accent is
    the 0-indexed mora position of the linked H tone, and unaccented words
    have `accentMora = none` ([beckman-pierrehumbert-1986]). -/
structure ProsodicEntry where
  /-- Surface form (romanized) -/
  form : String
  /-- Gloss -/
  gloss : String
  /-- Mora position of the accent (`none` = unaccented) -/
  accentMora : Option ℕ
  /-- Number of morae in the word -/
  nMorae : ℕ
  deriving Repr

/-- The entry bears an accent. -/
def ProsodicEntry.Accented (e : ProsodicEntry) : Prop := e.accentMora.isSome

instance (e : ProsodicEntry) : Decidable e.Accented := inferInstanceAs (Decidable (_ = true))

/-! ### Sample entries

The presence-vs-absence minimal pair *ame* ~ *a'me* of [kawahara-2015] (1a–b),
and the adjective and noun materials of [beckman-pierrehumbert-1986]'s
accentual-phrase experiments (Figs. 6–13), also cited as [kawahara-2015] (28). -/

/-- *ame* 'candy' — unaccented ([kawahara-2015] (1a); the unaccented noun of
    [beckman-pierrehumbert-1986] Fig. 6). -/
def ameCandy : ProsodicEntry :=
  { form := "ame", gloss := "candy", accentMora := none, nMorae := 2 }

/-- *a'me* 'rain' — initial accent, minimal with `ameCandy`
    ([kawahara-2015] (1b)). -/
def ameRain : ProsodicEntry :=
  { form := "ame", gloss := "rain", accentMora := some 0, nMorae := 2 }

/-- *uma'i* 'delicious' — accented adjective ([kawahara-2015] (28a);
    [beckman-pierrehumbert-1986] Figs. 6, 9). -/
def umai : ProsodicEntry :=
  { form := "umai", gloss := "delicious", accentMora := some 1, nMorae := 3 }

/-- *amai* 'sweet' — unaccented adjective, minimal with `umai`
    ([kawahara-2015] (28b); [beckman-pierrehumbert-1986] Fig. 8). -/
def amai : ProsodicEntry :=
  { form := "amai", gloss := "sweet", accentMora := none, nMorae := 3 }

/-- *mame'* 'beans' — final accent ([beckman-pierrehumbert-1986] Fig. 6,
    where AP-grouping with *uma'i* deletes this accent). -/
def mame : ProsodicEntry :=
  { form := "mame", gloss := "beans", accentMora := some 1, nMorae := 2 }

end Japanese.Prosody
