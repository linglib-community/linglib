module

public import Linglib.Semantics.Tense.Embedding
public import Linglib.Semantics.Tense.Pronoun
public import Linglib.Semantics.Tense.Reichenbach
public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Ogihara1996

/-!
# Ogihara (1996): Tense, Attitudes, and Scope

Ogihara, developing his dissertation, takes an embedded past tense to be ambiguous between a genuine
past, contributing temporal precedence, and a zero tense, a bound variable that receives the matrix
event time. The simultaneous reading is the zero-tense reading (`zeroTense_simultaneous`) and the
shifted reading the genuine-past reading (`genuinePast_shifted`). Japanese is a pure relative-tense
language, every tense being interpreted in the scope of the structurally higher tenses, so an
embedded past is anterior to the matrix event and *Taroo-wa Hanako-ga byookidat-ta to it-ta* has
only the shifted reading (`embeddedByookiDatta`, `byookiDatta_shifted`), a reading of a language
without the Sequence of Tense rule (`byookiDatta_mem`), the simultaneous reading requiring the
embedded present. The English past perfect under a past matrix is built against the same matrix
frame (`pluperfectShifted`, `pluperfect_is_past`).

## Implementation notes

The frames are Reichenbach frames over the integers, with the embedded perspective time
set to the matrix event time. The Japanese example with an embedded present under a past
matrix, whose simultaneous reading places the event at the matrix event time while the
morphology says present, is not encoded, since a single reference and event time cannot
carry both the morphological tense and the divergent event location.

## References

* [ogihara-1996]
* [ogihara-1989]
-/

@[expose] public section

namespace Ogihara1996

open Tense
open scoped Denotes
open Montague

/-- The frame of a clause embedded under an attitude verb takes the matrix event time as its
perspective time, so the embedded tense locates its reference time against the attitude holder's
now. -/
@[simps] def embeddedFrame {T : Type*} (matrixFrame : ReichenbachFrame T)
    (embeddedR embeddedE : T) : ReichenbachFrame T :=
  ⟨matrixFrame.speechTime, matrixFrame.eventTime, embeddedR, embeddedE⟩

theorem zeroTense_simultaneous {W T : Type*} [LT T] (g : Assignment T) (n : ℕ) (now : T)
    (w : W) : (pronoun ⊤ n 0).selector (Function.update g n now) w = some now := by
  simp

theorem genuinePast_shifted {W T : Type*} [LinearOrder T] {k j : ℕ} {g : Assignment T} {w : W}
    (h : (pronoun ⟦past⟧ k j).presup g w) : compare (g k) (g j) = .lt := by
  simpa [compare_lt_iff_lt] using h

/-- The matrix frame *Taroo-wa … to it-ta* is past and perfective, with the speech and
perspective times at the origin and the reference and event times two units earlier. -/
def matrixItta : ReichenbachFrame ℤ := .root 0 (-2) (-2)

/-- The embedded *Hanako-ga byookidat-ta* is a past under a past, interpreted relative to the
matrix event, so its perspective time is the matrix event time and its reference time lies
before it. -/
def embeddedByookiDatta : ReichenbachFrame ℤ := embeddedFrame matrixItta (-5) (-5)

/-- The English past perfect under a past matrix, *he said that Mary had been reading books
yesterday*, is past relative to the embedded perspective, and perfect. -/
def pluperfectShifted : ReichenbachFrame ℤ := embeddedFrame matrixItta (-4) (-5)

theorem japanese_relative_perspective :
    embeddedByookiDatta.perspectiveTime = matrixItta.eventTime := rfl

theorem byookiDatta_shifted : embeddedByookiDatta.referencePosition = .lt := by decide

theorem byookiDatta_mem : embeddedByookiDatta.referencePosition ∈ pastUnderPast False := by
  decide

theorem pluperfect_is_perfect : pluperfectShifted.eventPosition = .lt := by decide

theorem pluperfect_is_past : pluperfectShifted.referencePosition = .lt := by decide

end Ogihara1996
