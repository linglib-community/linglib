module

public import Linglib.Syntax.Clause.Marker

/-!
# Dutch polarity particles

Dutch marks a switch from negative to positive polarity with the sentence-internal affirmative
particle *wel*, accented in that use, the counterpart of the negation *niet*, [sudhoff-2012],
[hogeweg-2009]. In the production study of [turco-braun-dimroth-2014] it is the dominant
strategy in polarity contrast and in polarity correction, where German uses Verum focus.

## References

* [G. Turco, B. Braun and C. Dimroth, *When Contrasting Polarity, the Dutch Use Particles,
  Germans Intonation* (2014)][turco-braun-dimroth-2014]
* [S. Sudhoff, *Negation der Negation. Verum-Fokus und die niederländische Partikel wel*
  (2012)][sudhoff-2012]
* [L. Hogeweg, *The Meaning and Interpretation of the Dutch Particle wel* (2009)][hogeweg-2009]
-/

@[expose] public section

namespace Dutch.Particles

/-- *wel*, the affirmative polarity particle, in the middle field where the negation *niet*
stands. -/
def wel : Clause.Marker where
  morphs := [.free "wel"]
  anchor := .clause {.medial}

end Dutch.Particles
