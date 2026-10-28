module

public import Linglib.Fragments.Norwegian.Conjugation
public import Linglib.Syntax.Category.Verb.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Norwegian verbs

This file defines the Norwegian verb as a lexical entry, the root `Verb` with its stem, and the
verb phrase formed on a verb with a *verbal particle*, a preposition without a complement, as in
*kaste bort* 'throw away'. The past participle of such a verb phrase is that of the verb phrase,
*gjort opp*, or the compound with the particle prefixed, *oppgjort*. [The compound stands only
attributively and after *være* and *bli*, and the participle of the verb phrase everywhere but
attributively](##Norwegian.ParticipleContext.Admits): *en oppgjort sak*, *Saka er oppgjort* 'the
matter is settled', but only *Vi har gjort opp saka* 'we have settled the matter' after *ha*.

## Implementation notes

* A verb phrase is cited with its particle, the free morph its citation form ends in, and the
  particle is read off the citation form rather than stored beside it.
* The grammar calls the compound participle after *ha* and *få* unusual and the factors that
  favour the compound tendencies; the entries take the rule as categorical, as den Dikken's data
  do. That an attributive participle is never that of the verb phrase is read off the grammar's
  attributive examples, all of them compound.
* A particle can change the valency of its verb, *blåse av kampen* 'call off the match' beside
  intransitive *blåse*; `Norwegian.Verb.withParticle` keeps the valency of the simplex verb, which
  every verb phrase here shares.
* The entries are Bokmål, with the *-et* forms of the first weak class, and Åfarli's Nynorsk
  *sparke ut* of den Dikken's study. The comments locate the forms and classes in Faarlund, Lie
  and Vannebo (FLV) by page.

## TODO

* The grammar's three groups of verb phrases with a particle, those that exist only as a
  compound, only as a verb phrase, and as both (FLV pp. 83–84).
* The present participle, whose compound form is obligatory, *tilskyende* (FLV p. 85).
* The contexts keyed by the auxiliaries, whose split between *ha*, *få* and *være*, *bli*,
  *verte* also governs the agreement of a Nynorsk participle (FLV p. 518).
* The two participles as word structures, the compound a `Morphology.Word.Tree.compound`, once a
  compound spells out as one word.

## References

* [faarlund-lie-vannebo-1997]
* [dendikken-1995]
-/

@[expose] public section

namespace Norwegian

open ArgumentStructure Conjugation

/-- Where a past participle stands. -/
inductive ParticipleContext where
  /-- After *ha* or *få*. -/
  | haFaa
  /-- After *være* or *bli*, in Nynorsk also *verte*. -/
  | vaereBli
  /-- Attributively. -/
  | attributive
  deriving DecidableEq, Repr, Fintype

/-- The past participle of a verb phrase with a particle is that of the verb phrase, the particle
following it, *gjort opp*, or the compound, the particle prefixed, *oppgjort*. -/
inductive ParticipleForm where
  | phrase
  | compound
  deriving DecidableEq, Repr, Fintype

namespace ParticipleContext

/-- A context admits the participle of the verb phrase unless it is attributive, and the compound
unless it follows *ha* or *få*. -/
def Admits (c : ParticipleContext) : ParticipleForm → Prop  -- FLV p. 86, den Dikken (134), (135)
  | .phrase => c ≠ .attributive
  | .compound => c ≠ .haFaa

instance (c : ParticipleContext) : DecidablePred c.Admits
  | .phrase => inferInstanceAs (Decidable (c ≠ _))
  | .compound => inferInstanceAs (Decidable (c ≠ _))

variable {f : ParticipleForm}

@[simp] theorem admits_haFaa_iff : haFaa.Admits f ↔ f = .phrase := by cases f <;> decide

@[simp] theorem admits_vaereBli : vaereBli.Admits f := by cases f <;> decide

@[simp] theorem admits_attributive_iff : attributive.Admits f ↔ f = .compound := by
  cases f <;> decide

end ParticipleContext

/-- A Norwegian verb is the root entry with its stem. -/
structure Verb extends _root_.Verb where
  /-- The stem of the simplex verb. -/
  stem : Stem
  deriving BEq

namespace Verb

variable (v : Verb) (p : String)

/-- The particle of a verb phrase is the free morph its citation form ends in; a simplex verb has
none. -/
def particle? : Option String :=
  match v.morphs.getLast? with
  | some ⟨.free, p⟩ => some p
  | _ => none

/-- The past participle of the form `f`, the simplex participle followed by the particle or
prefixed with it; a simplex verb has one participle. -/
def participle (f : ParticipleForm) : String :=
  match v.particle?, f with
  | none, _ => v.stem.participle
  | some p, .phrase => v.stem.participle ++ " " ++ p
  | some p, .compound => p ++ v.stem.participle

/-- `transitive s` is the transitive simplex verb with the stem `s`. -/
def transitive (s : Stem) : Verb :=
  { morphs := [.root s.infinitive], valency := .ofFrame ArgumentFrame.np, stem := s }

/-- `v.withParticle p` is the verb phrase formed on `v` with the particle `p`, with the valency of
`v`. -/
def withParticle : Verb := { v with morphs := v.morphs ++ [.free p] }

@[simp] theorem particle?_transitive (s : Stem) : (transitive s).particle? = none := rfl

@[simp] theorem particle?_withParticle : (v.withParticle p).particle? = some p := by
  simp [particle?, withParticle, Morphology.Morph.free]

@[simp] theorem stem_withParticle : (v.withParticle p).stem = v.stem := rfl

variable {v}

theorem participle_of_particle?_eq_none (h : v.particle? = none) (f : ParticipleForm) :
    v.participle f = v.stem.participle := by
  simp [participle, h]

@[simp] theorem participle_withParticle_phrase :
    (v.withParticle p).participle .phrase = v.stem.participle ++ " " ++ p := by
  simp [participle]

@[simp] theorem participle_withParticle_compound :
    (v.withParticle p).participle .compound = p ++ v.stem.participle := by
  simp [participle]

theorem participle_phrase_ne_compound :
    (v.withParticle p).participle .phrase ≠ (v.withParticle p).participle .compound := by
  intro h
  have := congrArg String.length h
  simp only [participle_withParticle_phrase, participle_withParticle_compound,
    String.length_append] at this
  have : " ".length = 1 := rfl
  omega

end Verb

namespace Verbs

/-! ### Simplex verbs -/

/-- *kaste* 'throw', the paradigm verb of the first weak class. -/
def kaste : Verb := .transitive (weak1 .bokmaal "kaste")  -- FLV p. 483

/-- *sparke* 'kick', of the first weak class like the other stems in *-rk*. -/
def sparke : Verb := .transitive (weak1 .bokmaal "sparke")  -- FLV p. 482

/-- *klippe* 'cut', of the first weak class, as stems in *-pp* often are. -/
def klippe : Verb := .transitive (weak1 .bokmaal "klippe")  -- FLV p. 483

/-- *kjøre* 'drive', of the second weak class with *-te*, a stem in a long vowel and a single
consonant. -/
def kjoere : Verb := .transitive (weak2a "kjøre")  -- FLV p. 484

/-- *sende* 'send', of the second weak class with *-te*, a stem in *-nd*. -/
def sende : Verb := .transitive (weak2a "sende")  -- FLV p. 484

/-- *sette* 'set', of the second weak class with *-te* and a vowel change, *satte*, *satt*. -/
def sette : Verb := .transitive ⟨"sette", "setter", "satte", "satt"⟩  -- FLV p. 484

/-- *gjøre* 'do', of the second weak class with *-de* and a vowel change, *gjør*, *gjorde*,
*gjort*. -/
def gjoere : Verb := .transitive ⟨"gjøre", "gjør", "gjorde", "gjort"⟩  -- FLV p. 485

/-- *bygge* 'build', of the second weak class with *-de*, a stem in *-gg*. -/
def bygge : Verb := .transitive (weak2b "bygge")  -- FLV p. 485

/-- *leie* 'rent', of the second weak class with *-de*, a stem in *-ei*. -/
def leie : Verb := .transitive (weak2b "leie")  -- FLV p. 485

/-- *kle* 'dress', of the second weak class with *-dde*, a stem in a single vowel. -/
def kle : Verb := .transitive (weak2c "kle")  -- FLV p. 485

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

/-- The compound participles the grammar lists come out of the rule, *bortkastet* in the *-et*
form of its *en bortkastet dag*. -/
theorem grammar_compound_participles :  -- FLV pp. 85–86
    [gjoereOpp, klePaa, setteSammen, byggeUt, leieUt, kasteBort].map (·.participle .compound) =
      ["oppgjort", "påkledd", "sammensatt", "utbygd", "utleid", "bortkastet"] := by
  decide

/-- *gjøre opp* has the two participles of the grammar's *Vi har gjort opp saka* and *Saka er
oppgjort*. -/
theorem gjoereOpp_participle :  -- FLV p. 86
    gjoereOpp.participle .phrase = "gjort opp" ∧ gjoereOpp.participle .compound = "oppgjort" := by
  decide

/-! ### Nynorsk -/

namespace Nynorsk

/-- Nynorsk *sparke* 'kick', of the first weak class, *sparka*. -/
def sparke : Verb := .transitive (weak1 .nynorsk "sparke")  -- FLV p. 493

/-- Nynorsk *sparke ut* 'kick out', Åfarli's *sparka ut* and *utsparka*. -/
def sparkeUt : Verb := sparke.withParticle "ut"

end Nynorsk

end Verbs

end Norwegian
