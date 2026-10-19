module

public import Linglib.Phonology.Tone.Grammatical
public import Linglib.Phonology.OptimalityTheory.Correspondence
public import Linglib.Phonology.OptimalityTheory.Cophonology

/-!
# Rolle (2018): Grammatical tone: typology and theory

This file formalizes the dissertation's account of dominant grammatical tone, the replacement
of a target's underlying tones by a trigger's grammatical tune, through its two mechanisms.
Cophonology-scope answers the scope problem: hierarchy exchange lays the vocabulary items of
a specifier–head–complement configuration out from outermost to innermost, `Position`, and an
item's cophonology scopes over everything located inwardly, `ScopesOver`, so the dominant
trigger is the outer item. The dominant-tone asymmetry, that triggers are dependents and
lexical heads never impose dominance outward, is read off the order, and the typology table
of trigger–target pairs is reproduced once objects sit in specifier position,
`Row.dominant_iff`. Matrix–basemap correspondence answers the erasure problem: a dominant
trigger's subranking promotes faithfulness to the output of a basemap derivation whose input
is the induced projection of the target with its tones unvalued, `basemapOutput`, and
cophonological evaluation under that subranking selects exactly the candidates whose tonal
tier matches the basemap's, `coph_selects_basemap_faithful`; the same constraint referring to
the stem itself yields the recessive pattern, in which the tune does not apply to a valued
target.

## Implementation notes

Positions are the three of one specifier–head–complement configuration; a trigger–target pair
on a larger spine is read at the configuration containing both, which is how the typology
table's rows are placed. Basemap induction is represented by unvaluing the target's tones, the
basemap derivation by the overwrite that docks the tune, and matrix–basemap correspondence by
identity on the tonal tier, the substrate's `Correspondence.identViol`. The Izon and Hausa
case studies and the treatment of apparent outward dominance are not formalized.

## References

* [N. R. Rolle, *Grammatical tone: typology and theory* (2018)][rolle-2018]
* [L. Benua, *Transderivational identity: phonological relations between words*
  (1997)][benua-1997]
* [J. J. McCarthy, A. Prince, *Faithfulness and reduplicative identity*
  (1995)][mccarthy-prince-1995]
* [S. Inkelas, C. Zoll, *Is grammar dependence real? A comparison between cophonological and
  indexed constraint approaches to morphologically conditioned phonology*
  (2007)][inkelas-zoll-2007]
* [H. Sande, P. Jenks, *Cophonologies by phase* (2017)][sande-jenks-2017]
* [G. Ó. Hansson, *(Dis)agreement by (non)correspondence: inspecting the foundations*
  (2014)][hansson-2014]
* [R. S. Kayne, *The antisymmetry of syntax* (1994)][kayne-1994]
-/

@[expose] public section

namespace Rolle2018

open Tone OptimalityTheory

/-! ### Cophonology-scope -/

/-- The positions of a specifier–head–complement configuration, ordered from innermost to
outermost as hierarchy exchange lays their vocabulary items out in the morpho-phonological
tree: the head is outer to its complement and the specifier outer to the head. -/
inductive Position
  | complement
  | head
  | spec
  deriving DecidableEq, Fintype

namespace Position

def toFin : Position → Fin 3
  | .complement => 0
  | .head => 1
  | .spec => 2

theorem toFin_injective : Function.Injective toFin := by
  intro a b h; cases a <;> cases b <;> simp_all [toFin]

noncomputable instance : LinearOrder Position := LinearOrder.lift' toFin toFin_injective

/-- A dependent position: any position but the head. -/
def IsDependent (p : Position) : Prop := p ≠ .head

instance : DecidablePred IsDependent := fun p ↦ inferInstanceAs (Decidable (p ≠ .head))

end Position

/-- Cophonology-scope: the vocabulary item at `p` scopes over the item at `q` when `q` is
located inwardly, so that `p`'s subranking governs the constituent containing both. -/
def ScopesOver (p q : Position) : Prop := q < p

noncomputable instance : DecidableRel ScopesOver := fun p q ↦ inferInstanceAs (Decidable (q < p))

/-- Only the specifier's item scopes over the head: a dominant trigger targeting a lexical head
is a dependent, and an object imposes dominant tone on its verb because it sits in specifier
position. -/
theorem scopesOver_head_iff (p : Position) : ScopesOver p .head ↔ p = .spec := by
  cases p <;> decide

/-- No item scopes over the specifier's: a lexical head never imposes dominance outward. -/
theorem not_scopesOver_spec (p : Position) : ¬ ScopesOver p .spec := by
  cases p <;> decide

/-- The complement's item scopes over nothing. -/
theorem not_scopesOver_of_complement (q : Position) : ¬ ScopesOver .complement q := by
  cases q <;> decide

/-- A trigger that scopes over another item is a dependent or the head over its complement. -/
theorem isDependent_of_scopesOver_head {p : Position} (h : ScopesOver p .head) :
    p.IsDependent := by
  rw [scopesOver_head_iff] at h
  subst h
  decide

/-- The trigger–target pairs of the dominant-tone asymmetry table, with the positions the
dissertation assigns them: an affix is a head taking the root, or the inner stem, as its
complement; modifiers and objects are specifiers; an inner item stands to an outer one as the
complement of the outer configuration. -/
inductive Row
  | affixRoot
  | outerAffixStem
  | modifierNoun
  | outerModifierNoun
  | objectVerb
  | rootAffix
  | innerAffixOuter
  | nounModifier
  | innerModifierOuter
  | verbObject
  deriving DecidableEq, Fintype

/-- The trigger's position. -/
def Row.trigger : Row → Position
  | .affixRoot | .outerAffixStem | .nounModifier | .verbObject => .head
  | .modifierNoun | .outerModifierNoun | .objectVerb => .spec
  | .rootAffix | .innerAffixOuter | .innerModifierOuter => .complement

/-- The target's position. -/
def Row.target : Row → Position
  | .affixRoot | .outerAffixStem => .complement
  | .modifierNoun | .outerModifierNoun | .objectVerb | .rootAffix | .innerAffixOuter => .head
  | .nounModifier | .innerModifierOuter | .verbObject => .spec

/-- The table's dominant column: dominant tone from a dependent onto a lexical head or an
inner item is attested, dominant tone outward from a head or from an inner item is not. -/
def Row.DominantAttested : Row → Prop
  | .affixRoot | .outerAffixStem | .modifierNoun | .outerModifierNoun | .objectVerb => True
  | .rootAffix | .innerAffixOuter | .nounModifier | .innerModifierOuter | .verbObject => False

instance : DecidablePred Row.DominantAttested := fun r ↦ by
  cases r <;> unfold Row.DominantAttested <;> infer_instance

/-- The typology table falls out of cophonology-scope: dominant tone is attested for a
trigger–target pair exactly when the trigger's item scopes over the target's. -/
theorem Row.dominant_iff (r : Row) : r.DominantAttested ↔ ScopesOver r.trigger r.target := by
  cases r <;> decide

/-! ### Matrix–basemap correspondence -/

variable {S : Type}

/-- The tonal tier, the tone of each tone-bearing unit, along which matrix and basemap outputs are
compared. -/
def tonalTier (tbus : List (TBU S)) : List TRN := tbus.map TBU.tone

@[simp] theorem tonalTier_eq_map (tbus : List (TBU S)) : tonalTier tbus = tbus.map TBU.tone :=
  rfl

/-- Matrix–basemap correspondence on the tonal tier: the identity violations between two
tiers, the substrate's output–output identity restricted to tone. -/
def basemapViolations (tier₁ tier₂ : List TRN) : ℕ :=
  (Correspondence.parallel tier₁ tier₂).identViol .lhs .rhs

theorem basemapViolations_self (t : List TRN) : basemapViolations t t = 0 :=
  Correspondence.identViol_identity t

/-- Tiers of equal length with no identity violation are equal. -/
theorem eq_of_basemapViolations_eq_zero {t₁ t₂ : List TRN} (hLen : t₁.length = t₂.length)
    (h : basemapViolations t₁ t₂ = 0) : t₁ = t₂ := by
  unfold basemapViolations Correspondence.identViol at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  apply List.ext_getElem hLen
  intro n hn₁ hn₂
  have hmem : ((⟨n, hn₁⟩ : Fin t₁.length), (⟨n, hn₂⟩ : Fin t₂.length)) ∈
      (Correspondence.parallel t₁ t₂).edge .lhs .rhs := by
    rw [Correspondence.parallel_edge_lhs_rhs]
    exact (Correspondence.mem_diagonal _ _).mpr rfl
  have hne := h hmem
  simp only [Correspondence.parallel_form_lhs, Correspondence.parallel_form_rhs, not_not] at hne
  simpa using hne

/-- The matrix–basemap constraint of a trigger's subranking: a candidate's tonal tier against
the basemap output's. -/
def mxbm {C : Type} (basemapTier : List TRN) (extractTier : C → List TRN) : Constraint C :=
  fun c ↦ basemapViolations (extractTier c) basemapTier

open OptimalityTheory.Cophonology (cophonologicalEval mergeRanking)

variable {L C : Type} [DecidableEq L] (extractTier : C → List TRN) (l : L)
  (defaultRanking : List (L × Constraint C)) (candidates : Finset C)

/-- Promoting matrix–basemap faithfulness in a cophonology selects exactly the basemap-faithful
candidates: with a faithful candidate available, every optimal candidate's tonal tier is the
basemap's. -/
theorem coph_selects_basemap_faithful (basemapTier : List TRN)
    (hLen : ∀ c ∈ candidates, (extractTier c).length = basemapTier.length)
    (hFaithful : ∃ c ∈ candidates, extractTier c = basemapTier) :
    ∀ c ∈ cophonologicalEval defaultRanking [(l, mxbm basemapTier extractTier)] candidates,
      extractTier c = basemapTier := by
  intro c hc
  simp only [cophonologicalEval, mergeRanking] at hc
  obtain ⟨c₀, hc₀, he⟩ := hFaithful
  have hZero : mxbm basemapTier extractTier c = 0 :=
    Nat.le_zero.1 <| (Tableau.constraints_zero_le_of_mem_optimal hc hc₀).trans_eq
      (by simp [mxbm, he, basemapViolations_self])
  exact eq_of_basemapViolations_eq_zero (hLen c (Tableau.optimal_subset hc)) hZero

/-- Recessive grammatical tone: under a subranking promoting faithfulness to the stem itself,
every optimal candidate keeps the target's own tones, so the tune does not apply to a valued
target. -/
theorem recessive (host : List (TBU S))
    (hLen : ∀ c ∈ candidates, (extractTier c).length = host.length)
    (hFaithful : ∃ c ∈ candidates, extractTier c = tonalTier host) :
    ∀ c ∈ cophonologicalEval defaultRanking [(l, mxbm (tonalTier host) extractTier)] candidates,
      extractTier c = tonalTier host :=
  coph_selects_basemap_faithful extractTier l defaultRanking candidates _
    (by simpa using hLen) hFaithful

/-- The basemap output: the trigger's tune docked onto the target's deficient projection, the
target with its tones unvalued, which is the structure common to the vocabulary items that the
constraint's similarity condition picks out. -/
def basemapOutput (host : List (TBU S)) (u : Tune) : List (TBU S) :=
  overwrite (unvalue host) u

/-- For a one-tone tune the basemap output carries the tune on every unit, whatever the
target's own tones: the locus of erasure. -/
theorem tonalTier_basemapOutput_singleton (host : List (TBU S)) (t : TRN) :
    tonalTier (basemapOutput host ⟨[t], .left⟩) = host.map fun _ ↦ t := by
  rw [tonalTier_eq_map, basemapOutput, overwrite_unvalue, map_tone_overwrite_singleton]

/-- Dominant grammatical tone: under a subranking promoting faithfulness to the induced
basemap, every optimal candidate carries the trigger's whole-word tune, whatever the target's
underlying tones were. -/
theorem dominant (host : List (TBU S)) (t : TRN)
    (hLen : ∀ c ∈ candidates, (extractTier c).length = host.length)
    (hFaithful : ∃ c ∈ candidates, extractTier c = host.map fun _ ↦ t) :
    ∀ c ∈ cophonologicalEval defaultRanking
        [(l, mxbm (tonalTier (basemapOutput host ⟨[t], .left⟩)) extractTier)] candidates,
      extractTier c = host.map fun _ ↦ t := by
  rw [tonalTier_basemapOutput_singleton]
  exact coph_selects_basemap_faithful extractTier l defaultRanking candidates _
    (by simpa using hLen) hFaithful

end Rolle2018
