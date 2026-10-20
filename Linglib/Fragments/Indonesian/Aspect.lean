/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Aspect.Marker

/-!
# Indonesian aspect markers

The Indonesian verb does not change to indicate tense or aspect. Time is left to context, to a
time adjunct, or to one of the temporal markers of Sneddon's grammar, words within the predicate
indicating that the action has occurred, is occurring or is yet to occur in relation to a point
of reference, the moment of utterance or another event: *Ketika saya sampai di rumahnya Tom sudah
bangun* 'When I arrived at his house Tom had already got up'. The three relations are the perfect,
imperfective and prospective viewpoints, the point of reference being the topic time.

Sneddon classes *sempat* 'have the opportunity' with the modals and *belum* 'not yet' with the
negatives, so neither is entered; the preverbal *lagi* 'in the process of' is a different word
from *lagi* 'again', which follows the predicate.

## References

* [sneddon-1996]
-/

@[expose] public section

namespace Indonesian.Aspect

/-- *Sudah* indicates that an action has occurred or that a state has been achieved, *Ali sudah
bangun* 'Ali has woken up' (§2.143). With a state verb it usually refers both to the action that
begins the state and to its continuation, *Dia sudah tidur* 'He has gone to bed, he is asleep',
and with a non-verbal predicate it is translated 'already', *Dia sudah tinggi* 'He is already
tall'. -/
def sudah : Aspect.Marker :=
  { morphs := [.free "sudah"], gloss := "PERF", viewpoint := .perfect }

/-- *Telah* has the meaning of *sudah* and is almost entirely confined to writing and very formal
speech, *Dia telah pergi* 'He has gone' (§2.144). -/
def telah : Aspect.Marker :=
  { morphs := [.free "telah"], gloss := "PERF", viewpoint := .perfect, register := .formal }

/-- *Sedang* indicates that an action is in progress, *Mereka sedang makan* 'They are eating'
(§2.145). -/
def sedang : Aspect.Marker :=
  { morphs := [.free "sedang"], gloss := "PROG", viewpoint := .imperfective }

/-- *Lagi* can replace *sedang*, though it is less frequent and not used by all speakers, *Mereka
lagi makan* 'They are eating' (§2.146). -/
def lagi : Aspect.Marker :=
  { morphs := [.free "lagi"], gloss := "PROG", viewpoint := .imperfective }

/-- *Tengah* can replace *sedang*, though it is less frequent and not used by all speakers,
*Apartment Citraland kini tengah dibangun* 'The Citraland apartments are in the process of being
built' (§2.146). -/
def tengah : Aspect.Marker :=
  { morphs := [.free "tengah"], gloss := "PROG", viewpoint := .imperfective }

/-- *Masih* indicates that an action is still occurring, *Dia masih makan* 'She is still eating',
and occurs with non-verbal predicates, *Dia masih muda* 'She is still young' (§2.147). -/
def masih : Aspect.Marker :=
  { morphs := [.free "masih"], gloss := "still", viewpoint := .imperfective }

/-- *Akan* indicates a future event or state, *Tugasnya akan berat* 'His task will be heavy'
(§2.148); from a past point of reference it is 'would, was going to', *Dia berjanji akan datang*
'He promised he would come' (§2.152). -/
def akan : Aspect.Marker :=
  { morphs := [.free "akan"], gloss := "FUT", viewpoint := .prospective }

/-- *Bakal* indicates an event a considerable time in the future and occurs with verbal
predicates only, *Dia bakal menjadi presiden* 'He will become president' (§2.149). -/
def bakal : Aspect.Marker :=
  { morphs := [.free "bakal"], gloss := "FUT", viewpoint := .prospective }

/-- *Baru* indicates that an action or state has just occurred, *Dia baru tiba* 'He has just
arrived' (§2.150). -/
def baru : Aspect.Marker :=
  { morphs := [.free "baru"], gloss := "just", viewpoint := .perfect }

/-- *Pernah* indicates that an action occurred in the far past, never a recent one, and
corresponds to 'ever' or 'once', *Dia pernah belajar di Paris* 'She once studied in Paris'
(§2.151). -/
def pernah : Aspect.Marker :=
  { morphs := [.free "pernah"], gloss := "ever", viewpoint := .perfect }

/-- The temporal markers, in Sneddon's order of presentation. -/
def markers : List Aspect.Marker :=
  [sudah, telah, sedang, lagi, tengah, masih, akan, bakal, baru, pernah]

/-- *Telah* has the meaning of *sudah* and differs from it in register alone (§2.144). -/
theorem telah_eq_sudah :
    { telah with morphs := sudah.morphs, register := sudah.register } = sudah :=
  rfl

theorem register_sudah_lt_telah : sudah.register < telah.register := by decide

/-- *Lagi* can replace *sedang* (§2.146). -/
theorem lagi_eq_sedang : { lagi with morphs := sedang.morphs } = sedang := rfl

/-- *Tengah* can replace *sedang* (§2.146). -/
theorem tengah_eq_sedang : { tengah with morphs := sedang.morphs } = sedang := rfl

end Indonesian.Aspect
