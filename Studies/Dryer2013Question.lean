module

public import Linglib.Data.WALS.Features.F116A
public import Linglib.Fragments.HindiUrdu.Particles
public import Linglib.Fragments.Japanese.Particles
public import Linglib.Fragments.Mandarin.QuestionParticles
public import Linglib.Fragments.Slavic.Bulgarian.QuestionParticles
public import Linglib.Fragments.Slavic.Polish.QuestionParticles
public import Linglib.Fragments.Slavic.Russian.QuestionParticles
public import Linglib.Fragments.Slavic.Serbian.QuestionParticles
public import Linglib.Fragments.Slavic.Ukrainian.QuestionParticles
public import Linglib.Fragments.Turkish.QuestionParticles

/-!
# Dryer (2013): Polar questions and the position of polar question particles

The atlas codes a language for how it marks a neutral polar question, by a question particle, by
interrogative morphology on the verb, by word order, by intonation alone or not at all, and, where
it has a question particle, for where the particle stands in the sentence: at the beginning, at
the end, in second position, elsewhere, or in either of two positions. This file reads the second
value off the polar question particles of the fragments, `Clause.Marker.questionParticlePosition`,
and compares it with the atlas's coding of the language.

## Implementation notes

* The particles of a language are the ones its fragment gives for a neutral polar question;
  mirative and biased particles are left out, since the atlas codes neutral questions.
* A particle the fragment places by the focus has no position in the atlas's terms, so the
  comparison says nothing about it.

## References

* [dryer-2013-wals]
-/

@[expose] public section

namespace Dryer2013Question

open Data.WALS Clause

/-- The neutral polar question particles of each fragment, under the atlas's code for the
language. -/
def particles : List (String × List Clause.Marker) :=
  [("rus", [Russian.QuestionParticles.li]),
   ("jpn", [Japanese.Particles.ka]),
   ("mnd", [Mandarin.QuestionParticles.ma]),
   ("pol", [Polish.QuestionParticles.czy]),
   ("ukr", [Ukrainian.QuestionParticles.cy]),
   ("scr", [Serbian.QuestionParticles.li, Serbian.QuestionParticles.daLi]),
   ("bul", [Bulgarian.QuestionParticles.li]),
   ("tur", [Turkish.QuestionParticles.mi]),
   ("hin", [HindiUrdu.Particles.kya])]

/-- Each of these languages marks polar questions with a question particle in the atlas. -/
theorem questionParticle :
    ∀ x ∈ particles, F116A.allData.lookup x.1 = some .questionParticle := by
  decide +kernel

/-- Where the particles of a fragment have a position in the clause, it is the position the atlas
codes for the language, Hindi apart: second position in Russian, final in Japanese and Mandarin,
initial in Polish and Ukrainian, and either of two positions in Serbian-Croatian. -/
theorem questionParticlePosition_eq :
    ∀ x ∈ particles, x.1 ≠ "hin" → ∀ v ∈ Marker.questionParticlePosition x.2,
      F92A.allData.lookup x.1 = some v := by
  decide +kernel

theorem questionParticlePosition_isSome :
    (particles.filter fun x ↦ (Marker.questionParticlePosition x.2).isSome).map (·.1) =
      ["rus", "jpn", "mnd", "pol", "ukr", "scr", "hin"] := by
  decide +kernel

end Dryer2013Question
