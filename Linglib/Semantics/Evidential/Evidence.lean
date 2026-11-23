module

public import Linglib.Semantics.Evidential.Paradigm

/-!
# Evidence

An evidence relation `ev : Parameter → Set W → Set W` gives, for each information source `π` and
proposition `p`, the set `ev π p` of worlds in which the speaker has evidence from `π` for `p`.
The sources at hand for `p` at a world `w` are `sources ev p w = {π | w ∈ ev π p}`. The
evidential proposition of a term `e` is that the speaker has evidence for `p` from a source it
covers,

`e.evidence ev p = {w | ∃ π ∈ e.covers, w ∈ ev π p}`,

which holds at `w` exactly when the coverage of `e` meets the sources at hand
(`Evidential.mem_evidence_iff_not_disjoint`). The term an inventory prefers for the sources at
hand therefore has a true evidential proposition
(`Evidential.mem_evidence_of_preferred_eq_some`), and where it prefers none, no term has
(`Evidential.notMem_evidence_of_preferred_eq_none`).

An account that distinguishes evidence only by its type gives an evidence relation that
factors through `Parameter.evidenceType`. A term of a type of evidence then has the evidence of
that type as its evidential proposition (`Evidential.IsOfType.evidence_comp`), and in general a
term whose parameters all fall in one class of a classification has the evidence of that class
(`Evidential.evidence_comp_of_forall_eq`).

## Implementation notes

The relation is a bare function and the speaker is not an argument: an account with several
agents supplies one relation for each. Nothing is assumed of `ev`, since accounts differ on
whether evidence for `p` is closed under entailment and on whether direct evidence for `p`
excludes indirect evidence for it.

## TODO

* The evidence of a report is the content of a speech event; the content function of
  attitude reports is not yet related to `ev` at the hearsay and quotative parameters.
* The time at which evidence is acquired (`Tense.EvidentialFrame`) is not an argument of `ev`.
* The presupposition of indirect evidence in [izvorski-1997] and the information sources of the
  St'át'imcets modals in [matthewson-2016] are stated in their studies on Kratzer backgrounds,
  not on an evidence relation.

## References

* [aikhenvald-2004]
* [martinez-vera-2026]
* [von-fintel-gillies-2010]
-/

@[expose] public section

namespace Evidential

variable {W ι : Type*} {ev : Parameter → Set W → Set W} {e e' : Evidential} {es : List Evidential}
  {p : Set W} {w : W} {S : Finset Parameter}

/-- The sources at hand for a proposition at a world: those from which the speaker has evidence
for it there. -/
def sources (ev : Parameter → Set W → Set W) (p : Set W) (w : W) : Set Parameter :=
  {π | w ∈ ev π p}

@[simp] theorem mem_sources {π : Parameter} : π ∈ sources ev p w ↔ w ∈ ev π p := Iff.rfl

/-- The evidential proposition of a term: the speaker has evidence for `p` from a source the
term covers. -/
def evidence (e : Evidential) (ev : Parameter → Set W → Set W) (p : Set W) : Set W :=
  {w | ∃ π ∈ e.covers, w ∈ ev π p}

@[simp] theorem mem_evidence : w ∈ e.evidence ev p ↔ ∃ π ∈ e.covers, w ∈ ev π p := Iff.rfl

/-- The evidential proposition of a term holds where its coverage meets the sources at hand. -/
theorem mem_evidence_iff_not_disjoint :
    w ∈ e.evidence ev p ↔ ¬ Disjoint (e.covers : Set Parameter) (sources ev p w) := by
  simp [Set.not_disjoint_iff]

theorem evidence_mono (h : e.covers ⊆ e'.covers) : e.evidence ev p ⊆ e'.evidence ev p :=
  fun _ ⟨π, hπ, hw⟩ ↦ ⟨π, h hπ, hw⟩

/-- A term whose parameters all fall in one class of a classification has, under an evidence
relation that depends on the class alone, the evidence of that class. -/
theorem evidence_comp_of_forall_eq {c : Parameter → ι} {i : ι} (ev : ι → Set W → Set W)
    (hne : e.covers.Nonempty) (h : ∀ π ∈ e.covers, c π = i) :
    e.evidence (fun π ↦ ev (c π)) p = ev i p := by
  obtain ⟨π₀, hπ₀⟩ := hne
  ext w
  refine ⟨fun ⟨π, hπ, hw⟩ ↦ ?_, fun hw ↦ ⟨π₀, hπ₀, ?_⟩⟩
  · rwa [← h π hπ]
  · rwa [← h π₀ hπ₀] at hw

/-- The evidential proposition of a term of a type of evidence, under an evidence relation that
depends on the type alone, is the evidence of that type. -/
theorem IsOfType.evidence_comp {t : EvidenceType} (h : e.IsOfType t)
    (ev : EvidenceType → Set W → Set W) :
    e.evidence (fun π ↦ ev π.evidenceType) p = ev t p :=
  evidence_comp_of_forall_eq ev h.nonempty fun _ hπ ↦ EvidenceType.mem_block.1 (h.subset hπ)

/-- The term an inventory prefers for the sources at hand has a true evidential proposition. -/
theorem mem_evidence_of_preferred_eq_some (hS : (S : Set Parameter) = sources ev p w)
    (h : preferred es S = some e) : w ∈ e.evidence ev p :=
  mem_evidence_iff_not_disjoint.2 <| hS ▸ by
    simpa using not_disjoint_of_preferred_eq_some h

/-- Where an inventory prefers no term for the sources at hand, no term of it has a true
evidential proposition. -/
theorem notMem_evidence_of_preferred_eq_none (hS : (S : Set Parameter) = sources ev p w)
    (h : preferred es S = none) (he : e ∈ es) : w ∉ e.evidence ev p := by
  rw [mem_evidence_iff_not_disjoint, not_not, ← hS, Finset.disjoint_coe]
  exact (preferred_eq_none.1 h).mono_left fun π hπ ↦ mem_expressed.2 ⟨e, he, hπ⟩

end Evidential
