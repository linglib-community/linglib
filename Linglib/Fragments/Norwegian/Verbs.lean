module

public import Linglib.Fragments.Norwegian.Conjugation
public import Linglib.Syntax.Category.Verb.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Norwegian verbs

This file defines the Bokmål verb as a lexical entry, the root `Verb` with its stem and its
formation, simplex or a verb phrase with a verbal particle. Faarlund, Lie and Vannebo's reference
grammar calls a preposition without a complement that goes with a verb a verbal particle, *kaste
bort* 'throw away', and describes the relation of such a verb phrase to the compound verb with
the same particle as its first member, *bortkaste*. The past participle takes the compound form
more readily than the other forms, and where the verb is otherwise a verb phrase the compound
participle is used attributively, *en oppgjort sak*, and after *være* and *bli*, *Saka er
oppgjort* 'the matter is settled', while after *ha* and *få* the participle stays a verb phrase,
*Vi har gjort opp saka* 'we have settled the matter'. The entries are the particle verbs whose
participles the grammar lists and those of den Dikken's Norwegian examples, with the simplex
verbs they are formed on, conjugated by the grammar's classes.

## Main definitions

* `Norwegian.Verb`: the entry, the root `Verb` with its stem and its formation.
* `Norwegian.ParticipleContext`, `Norwegian.ParticipleContext.IsCompound`: where a participle
  stands, and the contexts that take the compound form.
* `Norwegian.Verb.phraseParticiple`, `Norwegian.Verb.compoundParticiple`,
  `Norwegian.Verb.participle`: the participle of the verb phrase, the compound participle, and
  the one a context takes.
* `Norwegian.Verb.transitive`, `Norwegian.Verb.withParticle`: the transitive entry of a stem,
  and the verb phrase formed on an entry with a verbal particle.
* `Norwegian.Verbs.allVerbs`, `Norwegian.Verbs.Nynorsk.sparkeUt`: the Bokmål entries and the
  Nynorsk one.

## Main results

* `Norwegian.Verb.participle_eq_compoundParticiple`, `participle_of_simplex`: the contexts that
  take the compound participle, and a simplex verb's one participle.
* `Norwegian.Verbs.grammar_compound_participles`, `Norwegian.Verbs.gjoereOpp_participle`: the
  compound participles the grammar lists come out of the rule, and *gjøre opp* has the grammar's
  two participles.

## Implementation notes

The entries are Bokmål with the *-et* forms of the first weak class, and Nynorsk *sparke* for
Åfarli's rows in den Dikken's study. His other Nynorsk verbs have no entry: the grammar's lists
do not place *klippe*, and his *kjørt* is the Bokmål spelling of Nynorsk *køyrt*. Which verb
phrases also exist as compound verbs in all their forms, the grammar's three groups, is not
recorded.

## References

* [faarlund-lie-vannebo-1997]
* [dendikken-1995]
-/

@[expose] public section

namespace Norwegian

open ArgumentStructure Conjugation

/-- A verb is simplex or a verb phrase formed on a simplex verb with a verbal particle. -/
inductive Formation where
  | simplex
  | particle (form : String)
  deriving DecidableEq, Repr

/-- Where a participle stands: after the perfect auxiliaries *ha* and *få*, after *være* and
*bli*, or attributively. -/
inductive ParticipleContext where
  | perfect
  | copular
  | attributive
  deriving DecidableEq, Repr, Fintype

/-- A context takes the compound participle of a verb phrase when it is attributive or after
*være* and *bli*; after *ha* and *få* the participle stays a verb phrase. -/
def ParticipleContext.IsCompound (c : ParticipleContext) : Prop := c ≠ .perfect

instance : DecidablePred ParticipleContext.IsCompound :=
  fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- A Norwegian verb is the root entry with its stem and its formation. -/
structure Verb extends _root_.Verb where
  /-- The stem of the simplex verb. -/
  stem : Stem
  /-- The formation. -/
  formation : Formation := .simplex
  deriving BEq

namespace Verb

variable (v : Verb)

/-- The participle of the verb phrase, the simplex participle followed by its particle, *gjort
opp*. -/
def phraseParticiple : String :=
  match v.formation with
  | .simplex => v.stem.participle
  | .particle p => v.stem.participle ++ " " ++ p

/-- The compound participle, the particle prefixed to the simplex participle, *oppgjort*. -/
def compoundParticiple : String :=
  match v.formation with
  | .simplex => v.stem.participle
  | .particle p => p ++ v.stem.participle

/-- The participle a context takes: the compound one attributively and after *være* and *bli*,
the verb phrase after *ha* and *få*. -/
def participle : ParticipleContext → String
  | .perfect => v.phraseParticiple
  | .copular | .attributive => v.compoundParticiple

variable {v}

theorem participle_perfect : v.participle .perfect = v.phraseParticiple := rfl

theorem participle_eq_compoundParticiple {c : ParticipleContext} (h : c.IsCompound) :
    v.participle c = v.compoundParticiple := by
  cases c <;> first | exact absurd rfl h | rfl

/-- A simplex verb has one participle in every context. -/
theorem participle_of_simplex (h : v.formation = .simplex) (c : ParticipleContext) :
    v.participle c = v.stem.participle := by
  cases c <;> simp [participle, phraseParticiple, compoundParticiple, h]

/-- `transitive s` is the transitive entry with the stem `s`. -/
def transitive (s : Stem) : Verb :=
  { morphs := [.root s.infinitive], valency := .ofFrame ArgumentFrame.np, stem := s }

/-- `v.withParticle p` is the verb phrase formed on `v` with the verbal particle `p`. -/
def withParticle (v : Verb) (p : String) : Verb :=
  { v with morphs := v.morphs ++ [.free p], formation := .particle p }

theorem compoundParticiple_withParticle (v : Verb) (p : String) :
    (v.withParticle p).compoundParticiple = p ++ v.stem.participle := rfl

theorem phraseParticiple_withParticle (v : Verb) (p : String) :
    (v.withParticle p).phraseParticiple = v.stem.participle ++ " " ++ p := rfl

end Verb

namespace Verbs

/-! ### Simplex verbs -/

/-- *kaste* 'throw', the paradigm verb of the first weak class. -/
def kaste : Verb := .transitive (weak1 .bokmaal "kaste")

/-- *sparke* 'kick', of the first weak class like the other stems in *-rk*. -/
def sparke : Verb := .transitive (weak1 .bokmaal "sparke")

/-- *klippe* 'cut', of the first weak class like the other stems in *-pp*. -/
def klippe : Verb := .transitive (weak1 .bokmaal "klippe")

/-- *kjøre* 'drive', of the second weak class with *-te*, a stem in a long vowel and a single
consonant. -/
def kjoere : Verb := .transitive (weak2a "kjøre")

/-- *sende* 'send', of the second weak class with *-te*, a stem in *-nd*. -/
def sende : Verb := .transitive (weak2a "sende")

/-- *sette* 'set', of the second weak class with *-te* and a vowel change, *satte*, *satt*. -/
def sette : Verb := .transitive ⟨"sette", "setter", "satte", "satt"⟩

/-- *gjøre* 'do', of the second weak class with *-de* and a vowel change, *gjør*, *gjorde*,
*gjort*. -/
def gjoere : Verb := .transitive ⟨"gjøre", "gjør", "gjorde", "gjort"⟩

/-- *bygge* 'build', of the second weak class with *-de*, a stem in *-gg*. -/
def bygge : Verb := .transitive (weak2b "bygge")

/-- *leie* 'rent', of the second weak class with *-de*, a stem in *-ei*. -/
def leie : Verb := .transitive (weak2b "leie")

/-- *kle* 'dress', of the second weak class with *-dde*, a stem in a single vowel. -/
def kle : Verb := .transitive (weak2c "kle")

/-! ### Verb phrases with a verbal particle -/

/-- *kaste bort* 'throw away', *bortkastet*. -/
def kasteBort : Verb := kaste.withParticle "bort"

/-- *sparke ut* 'kick out', *utsparket*. -/
def sparkeUt : Verb := sparke.withParticle "ut"

/-- *klippe av* 'cut off', *avklippet*. -/
def klippeAv : Verb := klippe.withParticle "av"

/-- *kjøre bort* 'drive away', *bortkjørt*. -/
def kjoereBort : Verb := kjoere.withParticle "bort"

/-- *sende ut* 'send out', *utsendt*. -/
def sendeUt : Verb := sende.withParticle "ut"

/-- *sette ned* 'set down', *nedsatt*. -/
def setteNed : Verb := sette.withParticle "ned"

/-- *sette sammen* 'put together', *sammensatt*. -/
def setteSammen : Verb := sette.withParticle "sammen"

/-- *gjøre opp* 'settle', *oppgjort*. -/
def gjoereOpp : Verb := gjoere.withParticle "opp"

/-- *bygge ut* 'expand', *utbygd*. -/
def byggeUt : Verb := bygge.withParticle "ut"

/-- *leie ut* 'rent out', *utleid*. -/
def leieUt : Verb := leie.withParticle "ut"

/-- *kle på* 'dress', *påkledd*. -/
def klePaa : Verb := kle.withParticle "på"

/-- The entries. -/
def allVerbs : List Verb :=
  [kaste, sparke, klippe, kjoere, sende, sette, gjoere, bygge, leie, kle, kasteBort, sparkeUt,
    klippeAv, kjoereBort, sendeUt, setteNed, setteSammen, gjoereOpp, byggeUt, leieUt, klePaa]

/-- The compound participles the grammar lists for *gjøre opp*, *kle på*, *sette sammen*,
*bygge ut*, *leie ut* and *kaste bort* come out of the rule, the last in the *-et* form of the
grammar's *en bortkastet dag*. -/
theorem grammar_compound_participles :
    [gjoereOpp, klePaa, setteSammen, byggeUt, leieUt, kasteBort].map Verb.compoundParticiple =
      ["oppgjort", "påkledd", "sammensatt", "utbygd", "utleid", "bortkastet"] := by
  decide

/-- *gjøre opp* has the grammar's two participles, *Vi har gjort opp saka* after *ha* and *Saka
er oppgjort* after *være*. -/
theorem gjoereOpp_participle :
    gjoereOpp.participle .perfect = "gjort opp" ∧ gjoereOpp.participle .copular = "oppgjort" := by
  decide

/-! ### Nynorsk -/

namespace Nynorsk

/-- Nynorsk *sparke* 'kick', of the first weak class, *sparka*, as in the grammar's *Han vart
sparka*. -/
def sparke : Verb := .transitive (weak1 .nynorsk "sparke")

/-- Nynorsk *sparke ut* 'kick out', Åfarli's *sparka ut* and *utsparka*. -/
def sparkeUt : Verb := sparke.withParticle "ut"

end Nynorsk

end Verbs

end Norwegian
