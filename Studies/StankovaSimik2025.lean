module

public import Linglib.Fragments.Slavic.Czech.Particles
public import Linglib.Fragments.Slavic.Czech.PolarityItems
public import Linglib.Logic.Modal.Defs
public import Studies.Simik2024

/-!
# Staňková and Šimík (2025): Negation in Czech Polar Questions

Staňková and Šimík analyse negation in Czech polar questions. The negative prefix moves with the
finite verb, so verb position fixes the position of negation: a clause-initial verb sits above
the canonical negation operator and is licensed only by Repp's commitment operator FALSUM
(`Simik2024.falsumCz_eq_one_of_falsum`), while a verb in situ is licensed by either
(`mem_availableReadings_iff`). Following Zeijlstra, the concord item *žádný* and the prefix carry
an uninterpretable negative feature and contribute no negation of their own, so of the readings
the determiner fragment lists for *žádný* only the indefinite one yields 'no' under the canonical
operator (`compl_eq_no_iff`). The canonical operator licenses concord items and needs negative
contextual evidence; FALSUM licenses positive polarity items and is indifferent to evidence; and
declarative word order needs evidence. Felicity in a context follows from these three sources
(`Felicitous`), which yields the predictions the paper's naturalness study tests: in
interrogative questions the polarity item is felicitous in every context and the concord item in
none (`v1_ppi_any_context`, `v1_nci_never`), and declarative questions need evidence, the concord
item negative evidence (`nonV1_nci_iff`, `nonV1_ppi_iff`). The particle *náhodou* is licensed by
FALSUM alone, so it excludes concord items whatever the word order (`nahodou_excludes_nci`), and
*copak* needs evidence matching the question's polarity, against the speaker's prior belief
(`copak_requires_bias`, `copak_prior_ne_evidence`).

## Implementation notes

The readings of negation are Šimík's inner and outer negation. The main experiment (seventy-five
speakers, a fully crossed design of verb position, indefinite and context, cumulative link mixed
models) found a main effect of the indefinite in interrogative questions, no effect of context
there, a preference for negative contexts and for concord items in declarative questions, high
naturalness of interrogative questions under positive evidence, a main effect of the indefinite
for *náhodou* questions, and a main effect of context for *copak* questions; these results are
stated in prose only.

## References

* [stankova-simik-2025]
* [repp-2013]
* [zeijlstra-2004]
* [gunlogson-2002]
* [sudo-2013]
* [buring-gunlogson-2000]
* [nekula-1996]
* [simik-2024]
-/

@[expose] public section

namespace StankovaSimik2025

open Czech.Particles (nahodou copak)
open Question Quantifier
open Simik2024
open scoped Denotes

/-! ### Verb position and the readings of negation -/

/-- The readings of negation available at a verb position, each given as the polarity of the
proposition the question double-checks, `.positive` for FALSUM, the outer reading, and
`.negative` for the canonical operator, the inner reading. The clause-initial verb raises above
the canonical operator and is licensed by FALSUM alone, the verb in situ by FALSUM or by the
canonical operator (the paper's (11) and (12)). -/
def _root_.Simik2024.VerbPosition.availableReadings : VerbPosition → List Polarity
  | .v1 => [.positive]
  | .nonV1 => [.negative, .positive]

theorem mem_availableReadings_iff (wp : VerbPosition) (n : Polarity) :
    n ∈ wp.availableReadings ↔ n = .positive ∨ wp = .nonV1 := by
  cases wp <;> cases n <;> decide

/-- The unmarked reading at a verb position is that of the lowest available operator. -/
def _root_.Simik2024.VerbPosition.defaultReading : VerbPosition → Polarity
  | .v1 => .positive
  | .nonV1 => .negative

theorem defaultReading_mem (wp : VerbPosition) : wp.defaultReading ∈ wp.availableReadings := by
  cases wp <;> decide

/-! ### Indefinites as proxies for the readings -/

/-- The experiment manipulates the indefinite, the negative concord item *žádný* as a proxy for
inner negation or the positive polarity item *nějaký* as a proxy for FALSUM. -/
inductive Indefinite
  | nci
  | ppi
  deriving DecidableEq, Repr, Fintype

/-- The determiner realizing each indefinite. -/
def Indefinite.word : Indefinite → Czech.Determiners.QuantityWord
  | .nci => .zadny
  | .ppi => .nejaky

/-- The polarity entry of each indefinite. -/
def Indefinite.entry : Indefinite → PolarityItem
  | .nci => Czech.PolarityItems.zadny
  | .ppi => Czech.PolarityItems.nejaky

/-- Of the readings of *žádný*, exactly the indefinite one yields *no* under the one negation of the
clause (p. 5). -/
theorem compl_eq_no_iff {d : GQ.Family} (hd : d ∈ ⟦Indefinite.nci.word⟧) :
    dᶜ = GQ.Family.no ↔ d = GQ.Family.some := by
  rcases hd with rfl | rfl <;> simp [GQ.Family.some_ne_no, GQ.Family.some_ne_no.symm]

/-- A polarity item is licensed at a reading of negation when a positive polarity item
falls under FALSUM and a negative one under the canonical operator (the paper's (11) and
(12)). -/
def LicensedAt (e : PolarityItem) (n : Polarity) : Prop :=
  (e.IsPPI → n = .positive) ∧ (e.IsNPI → n = .negative)

instance (e : PolarityItem) (n : Polarity) : Decidable (LicensedAt e n) := by
  unfold LicensedAt; infer_instance

theorem licensedAt_ppi_iff_not_nci (n : Polarity) :
    LicensedAt Indefinite.ppi.entry n ↔ ¬ LicensedAt Indefinite.nci.entry n := by
  cases n <;> decide

/-! ### Bias and felicity -/

/-- The canonical operator requires negative contextual evidence, as in the evidentially biased
contexts of [gunlogson-2002] and [sudo-2013], while FALSUM, conveying epistemic rather than
evidential bias, requires none. -/
def ReadingAdmits : Polarity → SignType → Prop
  | .negative, ctx => ctx = -1
  | .positive, _ => True

instance (n : Polarity) (ctx : SignType) : Decidable (ReadingAdmits n ctx) := by
  cases n <;> unfold ReadingAdmits <;> infer_instance

/-- Declarative word order requires contextual evidence ([gunlogson-2002]); interrogative
word order requires none. -/
def WordOrderAdmits : VerbPosition → SignType → Prop
  | .v1, _ => True
  | .nonV1, ctx => ctx ≠ 0

instance (wp : VerbPosition) (ctx : SignType) :
    Decidable (WordOrderAdmits wp ctx) := by
  cases wp <;> unfold WordOrderAdmits <;> infer_instance

/-- A negative polar question with an indefinite is felicitous in a context when some reading
available at its verb position licenses the indefinite and admits the context's evidence, and
the word order admits the evidence. -/
def Felicitous (wp : VerbPosition) (ind : Indefinite) (ctx : SignType) : Prop :=
  (∃ n ∈ wp.availableReadings, LicensedAt ind.entry n ∧ ReadingAdmits n ctx) ∧
    WordOrderAdmits wp ctx

instance (wp : VerbPosition) (ind : Indefinite) (ctx : SignType) :
    Decidable (Felicitous wp ind ctx) := by
  unfold Felicitous; infer_instance

theorem v1_ppi_any_context (ctx : SignType) : Felicitous .v1 .ppi ctx := by
  decide +revert

theorem v1_nci_never (ctx : SignType) : ¬ Felicitous .v1 .nci ctx := by
  decide +revert

theorem v1_context_invariant (ind : Indefinite) (ctx ctx' : SignType) :
    Felicitous .v1 ind ctx ↔ Felicitous .v1 ind ctx' := by
  decide +revert

theorem nonV1_nci_iff (ctx : SignType) :
    Felicitous .nonV1 .nci ctx ↔ ctx = -1 := by
  decide +revert

theorem nonV1_ppi_iff (ctx : SignType) :
    Felicitous .nonV1 .ppi ctx ↔ ctx ≠ 0 := by
  decide +revert

theorem nonV1_neutral_infelicitous (ind : Indefinite) : ¬ Felicitous .nonV1 ind 0 := by
  cases ind <;> decide

-- (14) [buring-gunlogson-2000]
theorem falsum_broader_than_english_outer :
    ¬ BuringGunlogson2000.Felicitous (some .positive) 1 ∧
      Felicitous .v1 .ppi 1 :=
  ⟨by decide, v1_ppi_any_context _⟩

/-! ### The particles -/

/-- *Náhodou* excludes the concord item at either verb position, since the item needs inner
negation and the particle needs FALSUM (the paper's (17) and (18)). -/
theorem nahodou_excludes_nci (wp : VerbPosition) :
    ¬ ∃ n ∈ wp.availableReadings,
      LicensedAt Indefinite.nci.entry n ∧ NahodouLicensed .negative n := by
  cases wp <;> decide

theorem nahodou_ppi (wp : VerbPosition) :
    ∃ n ∈ wp.availableReadings,
      LicensedAt Indefinite.ppi.entry n ∧ NahodouLicensed .negative n := by
  cases wp <;> decide

/-- *Copak* is felicitous exactly when the context's evidence matches the question's
polarity. -/
def CopakLicensed (pol : Polarity) (ctx : SignType) : Prop := ctx = evidence pol

instance (pol : Polarity) (ctx : SignType) : Decidable (CopakLicensed pol ctx) := by
  unfold CopakLicensed; infer_instance

theorem copak_requires_bias (pol : Polarity) : ¬ CopakLicensed pol 0 := by
  cases pol <;> decide

theorem copak_prior_ne_evidence (pol : Polarity) :
    (prior pol = 1 ↔ evidence pol = -1) ∧
      (prior pol = -1 ↔ evidence pol = 1) := by
  cases pol <;> decide

theorem nahodou_copak_opposite (ctx : SignType) :
    NahodouLicensed .negative .positive ∧ (CopakLicensed .negative ctx → ctx ≠ 0) := by
  decide +revert

end StankovaSimik2025
