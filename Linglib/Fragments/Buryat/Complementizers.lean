module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Buryat Complementizers and Clause-Embedding Verbs
[bondarenko-2022] [bondarenko-2020] [bondarenko-2019]

This file records the clause-typing morphemes of Barguzin Buryat
(Mongolic) embedded clauses and the matrix verbs that select them.
Embedded clauses show three surface shapes ([bondarenko-2022] §4.3.1
ex. 30–32): bare `[… V-TENSE gɘ-žɘ]`, nominalized `[… V-PART-CASE]`,
and nominalized with the say-root `[… V-TENSE g-ɘːš-CASE]`.

## Main definitions

- `Buryat.ge`, `Buryat.aasha`, `Buryat.zha` — the say-root *gɘ*, the
  agentive participle *-Aːša*, and the imperfective converb *-žA*
  ([skribnik-2003]), as root `Complementizer` entries; the closed
  inventory is `Buryat.complementizers`
- `Buryat.hanaxa`, `Buryat.medexe`, `Buryat.xelexe`, `Buryat.duulaxa` —
  clause-embedding verbs; all four alternate between the finite-CP and
  nominalized frames (ex. 35–36, 50–51). *hanaxa*'s frame-conditioned
  think~remember readings ride on `Verb.Reading` rows keyed to
  `Buryat.nominalizedFrame`

## Implementation notes

Bondarenko's head assignment (*gɘ* expones Cont, the suffixes are Comp
allomorphs) is paper-specific and lives in `Studies/Bondarenko2022.lean`;
rival carvings of Mongolic say-complementizers: [knyazev-2016],
[matic-pakendorf-2013]. Bare `§`-references are to [bondarenko-2022],
bare `ex.`/`fn.` references to [bondarenko-2020]. Identifiers are ASCII
romanizations (ɘ → e, ː → doubling, ž → zh, š → sh); `form` fields carry
the faithful transliterations, with capitals marking vowel-harmony
archiphonemes.
-/

@[expose] public section

namespace Buryat

/-- *gɘ* — grammaticalized root of *gɘxɘ* 'say' (fn. 21: no speech act
entailed under 'hear' or 'see'). Never surfaces unsuffixed (gɘ-žɘ,
g-ɘːšɘ), so it is recorded as a bound root. -/
def ge : Complementizer where
  morphs := [.root "gɘ"]

/-- *-Aːša* — past-oriented participle ([bondarenko-2020] ex. 36;
[skribnik-2003]); appears next to nominal projections. The complement it types is Noonan-nominalized
(case-marked, genitive subject) while the morpheme itself is a
participle — two axes, two fields. -/
def aasha : Complementizer where
  morphs := [.suff "Aːša"]
  coding := some .nominalized
  verbForm := some .Part
  licenser := some .nominal

/-- *-žA* — imperfective converb ([skribnik-2003]); appears next to
verbs, also in analytical verb forms and sentential adjuncts (ex. 30). -/
def zha : Complementizer where
  morphs := [.suff "žA"]
  coding := some .indicative
  verbForm := some .Conv
  licenser := some .verbal

/-- The clause-typing inventory — closed per §4.3.1 ex. 30–32. -/
def complementizers : List Complementizer := [ge, aasha, zha]

/-! ### Clause-embedding verbs

Vendler class stays unset (`Verb.Aspect.vendlerClass` convention for
clause-embedding verbs). -/

/-- The nominalized complement frame of the ex. 35–36 alternation:
[noonan-2007]-nominalized coding with an overt genitive embedded subject
(§4.3.1). Richer than the bare `ArgumentFrame.gerund` cell: it records the
embedded-subject case. -/
def nominalizedFrame : ArgumentFrame :=
  { complements := [.clausal (coding := some .nominalized)
      (embeddedSubject := some (.overt (some .gen)))] }

/-- *hanaxa* 'think', translated 'remember' with a nominalized complement (§4.4.3): one verb,
whose nominalized complement carries a presupposition that the event it describes started
before the thinking ([bondarenko-2020] (2), (21)). The `readings` rows record the alternation,
nonveridical and opaque on the bare CP, veridical and transparent on the nominalized frame. -/
def hanaxa : Verb where
  morphs := [.root "hanaxa"]
  valency := .ofFrames [ArgumentFrame.finiteClause, nominalizedFrame]
  readings := [
    { frame := ArgumentFrame.finiteClause, attitude := some (.doxastic .nonVeridical),
      opaqueContext := some true },
    { frame := nominalizedFrame, attitude := some (.doxastic .veridical),
      opaqueContext := some false }]

/-- *mɘdɘxɘ* 'know' — factive in both frames (ex. 36); embeds polar
questions (ex. 3). -/
def medexe : Verb where
  morphs := [.root "mɘdɘxɘ"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.gerund, ArgumentFrame.question]
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *xɘlɘxɘ* 'say' — non-factive with bare CPs; nominalized complements
are existence-entailing (ex. 51; speaker variation per fn. 30). -/
def xelexe : Verb where
  morphs := [.root "xɘlɘxɘ"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.gerund]
  speechActVerb := true

/-- *duːlaxa* 'hear' — non-factive with bare CPs, existence-entailing
with nominalized complements (ex. 50). -/
def duulaxa : Verb where
  morphs := [.root "duːlaxa"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.gerund]

end Buryat
