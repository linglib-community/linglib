module

public import Linglib.Syntax.Category.Particle.Basic
public import Linglib.Fragments.Slavic.Czech.Particles
public import Studies.StankovaSimik2025
public import Studies.Simik2024
public import Linglib.Semantics.Questions.Bias
public import Linglib.Data.Examples.Stankova2026
public import Linglib.Data.Examples.StankovaSimik2025

/-!
# Staňková (2026): A Three-Way Distinction of Negation Interpretation in Czech

Staňková proposes that negation in Czech polar questions occupies one of three LF positions,
outer (PolP), medial (ModP) or inner (TP), and that the polarity items and the particles
*náhodou*, *ještě* and *fakt* fingerprint them (her Table 1, `licensed`). The positions refine
Šimík's two readings of negation (`Position.ofReading`): medial negation is the paper's addition,
low like inner negation but non-propositional like FALSUM.

## References

* [stankova-2026]
* [stankova-simik-2025]
* [stankova-2023]
* [zeijlstra-2004]
* [romero-2024]
* [simik-2024]
* [gartner-gyuris-2017]
-/

@[expose] public section

namespace Stankova2026

open Question Simik2024
open StankovaSimik2025 (LicensedAt)

/-! ### The three positions -/

/-- Negation in a Czech polar question takes one of three LF positions, listed by scope width.
Inner negation in TP is propositional negation, medial negation in ModP scopes over the
evidential modal, and outer negation in PolP is the commitment operator FALSUM (the paper's
(16)). -/
inductive Position where
  /-- Inner negation is propositional ¬p in TP, which licenses negative concord items by Agree
  ([zeijlstra-2004]). -/
  | inner
  /-- Medial negation scopes over the evidential modal in ModP, in the bias presupposition. -/
  | medial
  /-- Outer negation is FALSUM in PolP, high negation with obligatory focus. -/
  | outer
  deriving DecidableEq, Repr, Fintype

/-- Each reading of [simik-2024] is a position. The inner reading, double-checking the negation
of the prejacent (`.negative`), is inner negation, and the outer reading, double-checking the
prejacent (`.positive`), is outer negation. -/
def Position.ofReading : Polarity → Position
  | .negative => .inner
  | .positive => .outer

/-- The evidential bias strength of a negation position (the paper's §3.1). Inner negation
presupposes evidence for ¬p, medial negation only the absence of evidence for p, and FALSUM
conveys epistemic rather than evidential bias. -/
inductive BiasStrength where
  | strong
  | weak
  | none_
  deriving DecidableEq, Repr

/-- The evidential bias strength of each position. -/
def Position.biasStrength : Position → BiasStrength
  | .inner => .strong
  | .medial => .weak
  | .outer => .none_

/-! ### Table 1 -/

/-- The Table 1 diagnostics of a negation position. -/
inductive Diagnostic where
  /-- The negation admits a positive polarity item like *nějaký* 'some' in its scope. -/
  | ppiOutscoping
  /-- The negation licenses a negative concord item like *žádný* 'no'. -/
  | nciLicensed
  /-- The particle *náhodou* 'by chance' is compatible. -/
  | nahodou
  /-- The particle *ještě* 'yet, still' is compatible. -/
  | jeste
  /-- The particle *fakt* 'really' is compatible. -/
  | fakt
  deriving DecidableEq, Repr, Fintype

/-- The diagnostics each negation position licenses, Table 1. -/
def licensed : Position → Finset Diagnostic
  | .inner => {.nciLicensed, .jeste, .fakt}
  | .medial => {.ppiOutscoping, .fakt}
  | .outer => {.ppiOutscoping, .nahodou}

/-- The position licenses the diagnostic, a cell of Table 1. -/
abbrev Licenses (pos : Position) (d : Diagnostic) : Prop := d ∈ licensed pos

/-- Table 1 fingerprints the positions, since no two license the same diagnostics. -/
theorem licensed_injective : Function.Injective licensed := by decide

variable {pos : Position}

theorem licenses_nciLicensed_iff : Licenses pos .nciLicensed ↔ pos = .inner := by
  cases pos <;> decide

theorem licenses_ppiOutscoping_iff : Licenses pos .ppiOutscoping ↔ pos ≠ .inner := by
  cases pos <;> decide

theorem licenses_nahodou_iff : Licenses pos .nahodou ↔ pos = .outer := by
  cases pos <;> decide

theorem licenses_jeste_iff : Licenses pos .jeste ↔ pos = .inner := by
  cases pos <;> decide

theorem licenses_fakt_iff : Licenses pos .fakt ↔ pos ≠ .outer := by
  cases pos <;> decide

/-- On the two readings of [simik-2024], the concord column of Table 1 is
[stankova-simik-2025]'s licensing of *žádný*. -/
theorem licenses_nciLicensed_iff_licensedAt (n : Polarity) :
    Licenses (.ofReading n) .nciLicensed ↔ LicensedAt StankovaSimik2025.Indefinite.nci.entry n := by
  cases n <;> decide

/-- On the two readings of [simik-2024], the polarity column of Table 1 is
[stankova-simik-2025]'s licensing of *nějaký*. -/
theorem licenses_ppiOutscoping_iff_licensedAt (n : Polarity) :
    Licenses (.ofReading n) .ppiOutscoping ↔
      LicensedAt StankovaSimik2025.Indefinite.ppi.entry n := by
  cases n <;> decide

/-! ### The diagnostic particles ([stankova-2026] §2.2, Table 1)

Entries live in `Czech.Particles`; this paper contributes the §2.2
licensing profiles — *ještě* felicitous in PQs only under inner
negation (§2.2.2, (14); with telic predicates it requires negation,
(13)), *fakt* licensed by inner and medial but repelled by outer on its
canonical reading (§2.2.3, (15), fn. 8), *vůbec* an NPI licensed by
inner only ((9)-(10)) — plus the Table 1 assignments and the
fingerprint results. -/

open Czech.Particles (nahodou jeste fakt copak)

/-- [stankova-2026]'s Table 1: which diagnostic each particle
realizes. -/
def table1 : List (Particle × Diagnostic) :=
  [(nahodou, .nahodou), (jeste, .jeste), (fakt, .fakt)]

/-- The Table 1 diagnostic realized by `p`, if any. -/
def diagnostic? (p : Particle) : Option Diagnostic :=
  table1.lookup p

/-- A particle is compatible with a negation position when the position licenses the
particle's Table 1 diagnostic, vacuously for a particle outside the table. -/
def Compatible (p : Particle) (pos : Position) : Prop :=
  ∀ d ∈ diagnostic? p, Licenses pos d

instance (p : Particle) (pos : Position) : Decidable (Compatible p pos) := by
  unfold Compatible; infer_instance

theorem nahodou_identifies_outer (pos : Position) : Compatible nahodou pos → pos = .outer := by
  cases pos <;> decide

theorem jeste_identifies_inner (pos : Position) : Compatible jeste pos → pos = .inner := by
  cases pos <;> decide

theorem fakt_plus_no_jeste_identifies_medial (pos : Position) :
    Compatible fakt pos ∧ ¬ Compatible jeste pos → pos = .medial := by
  cases pos <;> decide

/-- The three Table 1 particles jointly fingerprint the three negation
positions. -/
theorem particle_signatures_distinct (pos pos' : Position)
    (h : ∀ p ∈ [nahodou, jeste, fakt], Compatible p pos ↔ Compatible p pos') : pos = pos' := by
  have h1 := h nahodou (by simp)
  have h2 := h jeste (by simp [jeste])
  have h3 := h fakt (by simp [fakt])
  revert h1 h2 h3
  cases pos <;> cases pos' <;> decide

-- Table 1
theorem copak_no_diagnostic : diagnostic? copak = none := by decide

/-! ### Word order and PQ-form typology

Czech PQs come in V1 (interrogative) and nonV1 (declarative) word
orders; since *ne-* is inseparable from the finite verb, verb position
determines the syntactic position of negation ([stankova-simik-2025] §2,
[stankova-2026] §1). Crossing word order with polarity gives [simik-2024]'s 2×2 grid of PQ
forms (`Simik2024.CzechPQForm`), which maps onto [romero-2024]'s PosQ/LoNQ/HiNQ typology; the
readings of negation available at each verb position are in `StankovaSimik2025`. -/

/-- Outer negation has the verb clause-initial, inner and medial negation in situ. -/
def Position.toVerbPosition : Position → VerbPosition
  | .inner | .medial => .nonV1
  | .outer => .v1

/-- Outer negation preposes the negated verb, giving the high negation form (HiNQ) of
[romero-2024], and inner and medial negation leave it in situ, giving the low negation form
(LoNQ). -/
def Position.negationPosition (pos : Position) : Negation.Position :=
  pos.toVerbPosition.negationPosition

/-- Only outer negation (FALSUM) is obligatorily focused
([stankova-2026] §3.2). -/
def Position.RequiresFocus : Position → Prop
  | .outer => True
  | .medial | .inner => False

instance : DecidablePred Position.RequiresFocus := fun pos ↦ by
  cases pos <;> unfold Position.RequiresFocus <;> infer_instance

/-- In the grid of [simik-2024], outer negation gives an interrogative negative question
(InterNPQ), and inner and medial negation a declarative one (DeclNPQ). -/
def Position.toCzechPQForm (pos : Position) : CzechPQForm := ⟨pos.toVerbPosition, .negative⟩

theorem czechPQForm_negation (pos : Position) :
    pos.toCzechPQForm.negation = some pos.negationPosition :=
  rfl

/-- Czech refines [romero-2024]'s LoNQ: inner and medial share the LoNQ
form but differ in evidential bias strength and in Table 1
signatures. -/
theorem czech_refines_nonPreposed :
    Position.inner.negationPosition = Position.medial.negationPosition ∧
    Position.inner.biasStrength ≠ Position.medial.biasStrength ∧
    licensed .inner ≠ licensed .medial :=
  ⟨rfl, by decide, by decide⟩

-- §3.2 [stankova-2026]
theorem only_outer_requires_focus (p : Position) : p.RequiresFocus → p = .outer := by
  cases p <;> simp [Position.RequiresFocus]

/-! ### Verb position and context sensitivity

The verb-position API (`availableReadings`, `defaultReading`) is
[stankova-simik-2025]'s and lives in `StankovaSimik2025`; this paper adds
the link to evidential bias strength. -/

theorem context_tracks_bias_strength :
    (Position.ofReading VerbPosition.v1.defaultReading).biasStrength = .none_ ∧
    (Position.ofReading VerbPosition.nonV1.defaultReading).biasStrength = .strong :=
  ⟨rfl, rfl⟩

/-! ### The paper's examples

Typed stimuli live in `Data.Examples.Stankova2026`; each is paired here
with the negation reading and Table 1 diagnostic the paper assigns. -/


/-- The paper's polarity/particle examples with their negation reading
and tested diagnostic. -/
def analyzedExamples : List (Datum × Position × Diagnostic) :=
  [ (Examples.ex6a,  .inner,  .nciLicensed)
  , (Examples.ex6b,  .outer,  .nciLicensed)
  , (Examples.ex7a,  .medial, .ppiOutscoping)
  , (Examples.ex7b,  .outer,  .ppiOutscoping)
  , (Examples.ex11,  .outer,  .nahodou)
  , (Examples.ex15a, .inner,  .fakt)
  , (Examples.ex15d, .outer,  .fakt) ]

/-- Table 1 predicts each example's judgment, the diagnostic being
licensed at the example's negation position iff the example is
acceptable. -/
theorem examples_match_table1 :
    ∀ x ∈ analyzedExamples, x.1.judgment = .acceptable ↔ Licenses x.2.1 x.2.2 := by decide

/-- The positive-evidence stimulus of [stankova-simik-2025], their (14), a negative question
with a clause-initial verb after evidence for p, with the bias-profile cell it occupies. -/
def biasCheckedExamples :
    List (Datum × SignType × SignType × CzechPQForm) :=
  [ (StankovaSimik2025.Examples.ex14, 1, 0, .interNPQ) ]

theorem bias_examples_match_profile :
    ∀ x ∈ biasCheckedExamples,
      x.1.judgment = .acceptable ↔ x.2.2.2 ∈ czechBiasProfile x.2.1 x.2.2.1 := by
  decide

end Stankova2026
