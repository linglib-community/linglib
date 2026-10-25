module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Romanian polarity particles

Romanian has three polarity particles (`Romanian.PolarityParticles`): the positive *da*, the
negative *nu*, and *ba*, which contradicts what it responds to and does not stand alone, being
followed by *da*, *nu* or a clause: *Ana nu a plecat. — Ba da, a plecat* 'Ana didn't leave. —
You are wrong, she did', in Farkas and Bruce's examples. What each particle marks is analysed in
`FarkasBruce2010`.

## References

* [farkas-bruce-2010]
-/

@[expose] public section

namespace Romanian.PolarityParticles

/-- *da* 'yes': *Ana a plecat.* 'Ana left.' — *Da.* -/
def da : Particle where
  form := "da"

/-- *nu* 'no': *Ana nu a plecat.* 'Ana didn't leave.' — *Nu, n-a plecat.* -/
def nu : Particle where
  form := "nu"

/-- *ba*, contradicting: *Ana a plecat.* — *Ba nu, n-a plecat.* 'No, she didn't.' -/
def ba : Particle where
  form := "ba"

/-- The polarity particles. -/
def all : List Particle := [da, nu, ba]

end Romanian.PolarityParticles
