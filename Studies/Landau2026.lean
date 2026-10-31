module

public import Linglib.Syntax.Anaphora.Basic
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Data.Examples.Landau2026
public import Mathlib.Data.Finset.Disjoint
public import Linglib.Data.Examples.Readers

/-!
# Landau (2026): Silent Resumption: A New Test for Ellipsis

This file formalizes the ellipsis-internal resumption test of [landau-2026]. By the ban on vacuous
quantification ([chomsky-1982]) an Ā-operator binds into a null site only if the site has structure
at LF to host a resumptive variable, so a resumptive dependency into a null site diagnoses a surface
anaphor in the sense of [hankamer-sag-1976]. A failed extraction has two possible sources, the
paper's two reasons for the star: the site is a deep anaphor with no structure to host the
dependency, or it is a surface anaphor and ellipsis applied in the derivation bled the dependency.
An island around the site blocks extraction for a further reason, independent of ellipsis. Movement
is exposed to both of these confounds and agreement to the first; a resumptive dependency is formed
at LF and is exposed to neither. A test decides depth when the depth of a site factors through its
outcome, and a dependency decides depth exactly when it is exposed to no confound
(`Dependency.decides_iff`), so of the three only resumption does
(`Dependency.decides_iff_eq_resumption`). The paper's Hebrew nominal and prepositional ellipses,
whose domains are all islands, and its cross-linguistic mixed anaphors are rows of
`Data/Examples/Landau2026.json`. The resumption judgments are the test's predictions
(`eir_matches`), extraction fails on every Hebrew row (`hebrew_extraction_fails`), and the judgments
alone fix a deep anaphor and an ellipsis in each Hebrew domain (`hebrew_domains`) and the deep
status of the mixed anaphors (`mixed_anaphors_deep`).

## Implementation notes

A site is modelled by its depth and the confounds present at it, and a test by the dependency it
forms into the site. The paper does not say whether islands block agreement, and nothing below
depends on it: agreement fails to decide depth on the timing confound alone. The rows' texts and
judgments agree with the August 2025 preprint of the paper; the example numbers the rows carry run
two below the preprint's throughout and have not been checked against the published version. The
domain of a null site is the category of its head, `Minimalist.Cat`.

## References

* [landau-2026]
* [hankamer-sag-1976]
* [chomsky-1982]
-/

@[expose] public section

namespace Landau2026

open Anaphor (Depth)

/-! ### Sites and dependencies -/

/-- What can block a dependency into a surface site: ellipsis applied in the derivation before
the dependency was formed, bleeding it, or an island around the site. -/
inductive Confound where
  | timing
  | island
  deriving DecidableEq, Repr

/-- A null site, given by the depth of its anaphor and the confounds present at it. -/
structure Site where
  /-- The depth of the anaphor at the site. -/
  depth : Depth
  /-- The confounds present at the site. -/
  confounds : Finset Confound

/-- The dependency a test forms into a null site: extraction moves an operator out of it,
agreement probes into it, and the EIR test binds a resumptive pronoun inside it. -/
inductive Dependency where
  | movement
  | agreement
  | resumption
  deriving DecidableEq, Repr

/-- The confounds a dependency is exposed to. Movement is formed in the derivation and is
constrained by islands; agreement is formed in the derivation, so ellipsis can bleed it; a
resumptive dependency is formed at LF and is indifferent to islands. -/
def Dependency.exposure : Dependency → Finset Confound
  | .movement => {.timing, .island}
  | .agreement => {.timing}
  | .resumption => ∅

/-- A site hosts a dependency when it has internal structure for the dependency to end in and no
confound the dependency is exposed to is present. -/
def Site.Hosts (s : Site) (d : Dependency) : Prop :=
  s.depth.HasInternalStructure ∧ Disjoint d.exposure s.confounds

instance (s : Site) (d : Dependency) : Decidable (s.Hosts d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A test decides depth when the depth of a site is determined by whether the site hosts the
test's dependency. -/
def Dependency.Decides (d : Dependency) : Prop :=
  Function.FactorsThrough Site.depth (·.Hosts d)

variable {s : Site} {d d' : Dependency}

theorem Site.Hosts.depth_eq_surface (h : s.Hosts d) : s.depth = .surface := h.1

theorem Site.Hosts.mono (h : s.Hosts d) (hle : d'.exposure ⊆ d.exposure) : s.Hosts d' :=
  ⟨h.1, h.2.mono_left hle⟩

theorem Site.Hosts.resumption (h : s.Hosts d) : s.Hosts .resumption :=
  h.mono (Finset.empty_subset _)

theorem Site.hosts_resumption_iff : s.Hosts .resumption ↔ s.depth = .surface := by
  simp [Site.Hosts, Dependency.exposure, Depth.HasInternalStructure]

theorem Site.depth_eq_of_iff_hosts_resumption {p : Prop} [Decidable p]
    (h : p ↔ s.Hosts .resumption) : s.depth = if p then .surface else .deep := by
  rw [Site.hosts_resumption_iff] at h
  cases hd : s.depth <;> simp_all

theorem Dependency.decides_iff : d.Decides ↔ d.exposure = ∅ := by
  refine ⟨fun h ↦ ?_, fun h a b hab ↦ ?_⟩
  · by_contra hne
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have := @h ⟨.deep, ∅⟩ ⟨.surface, {k}⟩ (by simp [Site.Hosts, Depth.HasInternalStructure, hk])
    exact Depth.noConfusion this
  · rcases a with ⟨_ | _, _⟩ <;> rcases b with ⟨_ | _, _⟩ <;>
      simp_all [Site.Hosts, Depth.HasInternalStructure]

theorem Dependency.decides_iff_eq_resumption : d.Decides ↔ d = .resumption := by
  cases d <;> simp [decides_iff, exposure]

theorem exists_hosts_resumption_not_movement :
    ∃ s : Site, s.Hosts .resumption ∧ ¬ s.Hosts .movement :=
  ⟨⟨.surface, {.timing}⟩, by decide⟩

/-! ### The paper's examples

Every row is a resumptive dependency into a null site, and its judgment is the outcome of the EIR
test. The depth of the site, its domain, and whether the domain is an island are read from the
row's paper features. -/

-- UNVERIFIED: the rows' example numbers against the published version; they run two below the
-- August 2025 preprint's.

def depths : List (String × Depth) := [("deep", .deep), ("surface", .surface)]

def domains : List (String × Minimalist.Cat) := [("nP", .n), ("DP", .D), ("PP", .P), ("VP", .V)]

/-- The confounds a row's `extractionAvailable` feature records: a domain out of which extraction
is unavailable is an island. -/
def barriers : List (String × Finset Confound) := [("true", ∅), ("false", {.island})]

/-- The site of a row: its recorded depth, and the island confound when extraction out of its
domain is unavailable. -/
def site? (e : Datum) : Option Site := do
  pure ⟨← e.parse? "depth" depths, ← e.parse? "extractionAvailable" barriers⟩

def hebrewData : List Datum :=
  [Examples.hebrewEN, Examples.hebrewENP, Examples.hebrewNCA_DP, Examples.hebrewAE,
    Examples.hebrewNCA_PP, Examples.hebrewPPE]

def mixedAnaphorData : List Datum :=
  [Examples.englishDoSo, Examples.dutchDatDoen, Examples.danishDet, Examples.koreanNullObj]

theorem site?_isSome : ∀ e ∈ Examples.all, (site? e).isSome := by decide +kernel

theorem eir_matches : ∀ e ∈ Examples.all, ∀ s, site? e = some s →
    (e.judgment = .acceptable ↔ s.Hosts .resumption) := by
  decide +kernel

theorem hebrew_extraction_fails :
    ∀ e ∈ hebrewData, ∀ s, site? e = some s → ¬ s.Hosts .movement := by
  decide +kernel

theorem hebrew_domains : ∀ c ∈ [Minimalist.Cat.n, .D, .P], ∀ δ : Depth, ∃ e ∈ hebrewData,
    e.parse? "domain" domains = some c ∧
      ∀ s : Site, (e.judgment = .acceptable ↔ s.Hosts .resumption) → s.depth = δ := by
  intro c hc δ
  obtain ⟨e, he, hd, hj⟩ : ∃ e ∈ hebrewData, e.parse? "domain" domains = some c ∧
      (if e.judgment = .acceptable then .surface else .deep) = δ := by
    revert c δ; decide +kernel
  exact ⟨e, he, hd, fun s h ↦ (Site.depth_eq_of_iff_hosts_resumption h).trans hj⟩

theorem mixed_anaphors_deep : ∀ e ∈ mixedAnaphorData, ∀ s : Site,
    (e.judgment = .acceptable ↔ s.Hosts .resumption) → s.depth = .deep := by
  intro e he s h
  have hj : ∀ e ∈ mixedAnaphorData, e.judgment ≠ .acceptable := by decide
  simpa [hj e he] using Site.depth_eq_of_iff_hosts_resumption h

end Landau2026
