module

public import Linglib.Phonology.Tone.Grammatical
public import Linglib.Phonology.OptimalityTheory.Cophonology

/-!
# Rolle (2018): Grammatical tone: typology and theory

Hierarchy exchange lays the vocabulary items of a specifier–head–complement configuration out
from outermost to innermost, and an item's cophonology scopes over those located inwardly of it,
so that [a trigger–target pair is attested with dominant tone exactly when the trigger scopes
over the target](##Row.dominant_iff). Matrix–basemap correspondence requires the tones of one
output to be present in another's. Ranked first towards a basemap induced from the target with
its tones unvalued, the matrix-to-basemap direction [bounds the winner by the trigger's tune,
whatever the target's tones](##dominant), and [erases them where there is no tune](##subtractive).
Ranked first towards the stem, the basemap-to-matrix direction [keeps a valued target as it
is](##recessive) in a privative culminative system and [is vacuous on an unvalued
one](##recessive_unvalued), [where the other direction would block the
tune](##omxobm_stem_unvalued).

## Implementation notes

* Candidates are read through `tier`, the tones of the target's units, compared unit by unit
  under the subsumption order on root nodes; a target tone that coincides with the tune's on the
  same unit is therefore not told apart from it, as Rolle's autosegmental correspondence does.
* IO(T) and the docking constraint are not modelled, so `dominant` bounds the winner's tones by
  the tune's rather than fixing them.
* Positions are the three of one configuration; a trigger–target pair on a larger spine is read
  at the configuration containing both.

## TODO

* The Izon and Hausa case studies and the treatment of apparent outward dominance.

## References

* [rolle-2018]
* [inkelas-zoll-2007]
* [benua-1997]
-/

@[expose] public section

namespace Rolle2018

open Tone OptimalityTheory OptimalityTheory.Cophonology

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

/-- The depth of a position, innermost first. -/
def toFin : Position → Fin 3
  | .complement => 0
  | .head => 1
  | .spec => 2

theorem toFin_injective : Function.Injective toFin := by decide

instance : LinearOrder Position := LinearOrder.lift' toFin toFin_injective

end Position

/-- Cophonology-scope, extending the stem scope of [inkelas-zoll-2007]: the vocabulary item at
`p` scopes over the item at `q` when `q` is located inwardly, so that `p`'s subranking governs
the constituent containing both. -/
def ScopesOver (p q : Position) : Prop := q < p

instance : DecidableRel ScopesOver := fun p q ↦ inferInstanceAs (Decidable (q < p))

/-- The trigger–target pairs of the table summarizing the dominant-tone asymmetry. -/
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

/-- The trigger's position. An affix is a head taking the root, or the inner stem, as its
complement; modifiers and objects are specifiers, the object that of vP; an inner item stands to
an outer one as the complement of the outer configuration. -/
def Row.trigger : Row → Position
  | .affixRoot | .outerAffixStem | .nounModifier | .verbObject => .head
  | .modifierNoun | .outerModifierNoun | .objectVerb => .spec
  | .rootAffix | .innerAffixOuter | .innerModifierOuter => .complement

/-- The target's position. -/
def Row.target : Row → Position
  | .affixRoot | .outerAffixStem | .outerModifierNoun => .complement
  | .modifierNoun | .objectVerb | .rootAffix | .innerAffixOuter => .head
  | .nounModifier | .innerModifierOuter | .verbObject => .spec

/-- The rows the table marks attested with dominant tone, from a dependent onto a lexical head
or onto an inner item. -/
def Row.DominantAttested (r : Row) : Prop :=
  r = .affixRoot ∨ r = .outerAffixStem ∨ r = .modifierNoun ∨ r = .outerModifierNoun ∨
    r = .objectVerb

instance : DecidablePred Row.DominantAttested := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A trigger–target pair is attested with dominant tone exactly when the trigger scopes over the
target (ch. 6, Table 3, from the CoP-scope hierarchy (12) and the object in the specifier of vP,
Figure 15). -/
theorem Row.dominant_iff (r : Row) : r.DominantAttested ↔ ScopesOver r.trigger r.target := by
  cases r <;> decide

/-! ### Matrix–basemap correspondence -/

variable {S C L : Type*} [DecidableEq L] {n : ℕ} {candidates : Finset C}
  {default sub : List (L × Constraint C)} {l l' : L}

/-- The tonal tier of a string, the tone of each of its units. -/
def tonalTier (w : List (TBU S)) (i : Fin w.length) : TRN := w[i].tone

theorem tonalTier_eq_bot_iff {w : List (TBU S)} : tonalTier w = ⊥ ↔ ∀ τ ∈ w, ¬ τ.IsValued := by
  simp [funext_iff, tonalTier, TBU.IsValued, TRN.bot_eq_empty, List.forall_mem_iff_getElem,
    Fin.forall_iff]

/-- The units at which a tone of the tier `X` is not present in the tier `Y`. -/
def absentViol (X Y : Fin n → TRN) : ℕ := (Finset.univ.filter fun i ↦ ¬ X i ≤ Y i).card

theorem absentViol_eq_zero_iff {X Y : Fin n → TRN} : absentViol X Y = 0 ↔ X ≤ Y := by
  simp [absentViol, Finset.filter_eq_empty_iff, Pi.le_def]

/-- OMxOBM(T), an output–output correspondence constraint in the sense of [benua-1997] directed
from the matrix output to the basemap output: all tone of the matrix must be present in the
basemap. -/
def omxobm (tier : C → Fin n → TRN) (basemap : Fin n → TRN) : Constraint C :=
  fun c ↦ absentViol (tier c) basemap

/-- OBMOMx(T), directed from the basemap output to the matrix output: all tone of the basemap
must be present in the matrix. -/
def obmomx (tier : C → Fin n → TRN) (basemap : Fin n → TRN) : Constraint C :=
  fun c ↦ absentViol basemap (tier c)

/-- CULMINATIVITY for the toneme `t`: a candidate violates it at each occurrence of `t` beyond
the first. -/
def culmin (tier : C → Fin n → TRN) (t : TRN) : Constraint C :=
  fun c ↦ (Finset.univ.filter (tier c · = t)).card - 1

theorem le_of_mem_optimal_omxobm {tier : C → Fin n → TRN} {B : Fin n → TRN}
    (hB : ∃ c ∈ candidates, tier c ≤ B) :
    ∀ c ∈ Cophonology.optimal default ((l, omxobm tier B) :: sub) candidates, tier c ≤ B :=
  fun c hc ↦ by
    obtain ⟨d, hd, hdB⟩ := hB
    simpa [omxobm, absentViol_eq_zero_iff] using
      eq_zero_of_mem_optimal (pre := [(l, omxobm tier B)]) hc hd
        (by simpa [omxobm, absentViol_eq_zero_iff])

/-- The basemap output: the trigger's tune docked onto the target's deficient projection, the
target with its tones unvalued. -/
def basemapOutput (host : List (TBU S)) (u : Tune) : List (TBU S) :=
  overwrite (unvalue host) u

theorem basemapOutput_eq_apply (host : List (TBU S)) (u : Tune) :
    basemapOutput host u = Dominance.replacive.apply u host :=
  overwrite_unvalue host u

@[simp] theorem map_tone_basemapOutput (host : List (TBU S)) (u : Tune) :
    (basemapOutput host u).map TBU.tone = u.realize host.length := by
  simp [basemapOutput_eq_apply]

@[simp] theorem length_basemapOutput (host : List (TBU S)) (u : Tune) :
    (basemapOutput host u).length = host.length := by
  simp [basemapOutput_eq_apply]

/-- The basemap output's tonal tier, unit by unit of the target. -/
def basemapTier (host : List (TBU S)) (u : Tune) : Fin host.length → TRN :=
  tonalTier (basemapOutput host u) ∘ Fin.cast (length_basemapOutput host u).symm

theorem basemapTier_apply (host : List (TBU S)) (u : Tune) (i : Fin host.length) :
    basemapTier host u i = (u.realize host.length)[i.1]'(by simp) := by
  simp [basemapTier, tonalTier, ← List.getElem_map TBU.tone]

/-- Under a trigger whose subranking puts OMxOBM(T) towards the induced basemap first, every
winner bears at each unit of the target nothing or the tone the tune puts there, whatever the
target's own tones (ch. 5, (22) and Tableau 5). -/
theorem dominant (host : List (TBU S)) (u : Tune) (tier : C → Fin host.length → TRN)
    (hu : ∃ c ∈ candidates, tier c = basemapTier host u) :
    ∀ c ∈ Cophonology.optimal default ((l, omxobm tier (basemapTier host u)) :: sub) candidates,
      ∀ i, tier c i ≤ (u.realize host.length)[i.1]'(by simp) := fun c hc i ↦
  basemapTier_apply host u i ▸ le_of_mem_optimal_omxobm
    (hu.imp fun _ ↦ .imp_right le_of_eq) c hc i

/-- A trigger with no tune is subtractive: under OMxOBM(T) towards the basemap induced from the
target, every winner leaves the target unvalued (ch. 5, §5.3.3). -/
theorem subtractive (host : List (TBU S)) (e : Edge) (tier : C → Fin host.length → TRN)
    (hu : ∃ c ∈ candidates, tier c = ⊥) :
    ∀ c ∈ Cophonology.optimal default
        ((l, omxobm tier (basemapTier host ⟨[], e⟩)) :: sub) candidates, tier c = ⊥ := by
  have hB : basemapTier host ⟨[], e⟩ = ⊥ := funext fun i ↦ by
    simp [basemapTier_apply, TRN.bot_eq_empty]
  rw [hB]
  exact fun c hc ↦ le_bot_iff.1 <|
    le_of_mem_optimal_omxobm (hu.imp fun _ ↦ .imp_right le_of_eq) c hc

theorem omxobm_stem_unvalued (host : List (TBU S)) (tier : C → Fin host.length → TRN)
    (h : ∀ τ ∈ host, ¬ τ.IsValued) (hu : ∃ c ∈ candidates, tier c = ⊥) :
    ∀ c ∈ Cophonology.optimal default ((l, omxobm tier (tonalTier host)) :: sub) candidates,
      tier c = ⊥ := by
  rw [tonalTier_eq_bot_iff.2 h]
  exact fun c hc ↦ le_bot_iff.1 <|
    le_of_mem_optimal_omxobm (hu.imp fun _ ↦ .imp_right le_of_eq) c hc

/-- In a privative culminative system with the toneme `t`, a trigger whose subranking puts
OBMOMx(T) towards the stem and CULMINATIVITY first leaves a target bearing `t` once as it is:
the tune does not apply (ch. 5, (32) and Tableau 8). -/
theorem recessive (host : List (TBU S)) (tier : C → Fin host.length → TRN) {t : TRN}
    (hhost : (Finset.univ.filter (tonalTier host · = t)).card = 1)
    (hpriv : ∀ c ∈ candidates, ∀ i, tier c i = ⊥ ∨ tier c i = t)
    (hu : ∃ c ∈ candidates, tier c = tonalTier host) :
    ∀ c ∈ Cophonology.optimal default
        ((l, obmomx tier (tonalTier host)) :: (l', culmin tier t) :: sub) candidates,
      tier c = tonalTier host := fun c hc ↦ by
  obtain ⟨d, hd, hdt⟩ := hu
  have h0 := eq_zero_of_mem_optimal
    (pre := [(l, obmomx tier (tonalTier host)), (l', culmin tier t)]) hc hd <| by
      simp [obmomx, culmin, absentViol_eq_zero_iff, hdt, hhost]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, obmomx,
    culmin, absentViol_eq_zero_iff] at h0
  have hT := hpriv c (Tableau.optimal_subset hc)
  have hH := hdt ▸ hpriv d hd
  -- Every unit bearing `t` in the target bears it in the winner, and the winner bears it once.
  have hsub : Finset.univ.filter (tonalTier host · = t) ⊆ Finset.univ.filter (tier c · = t) :=
    fun i hi ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (hT i).elim (fun h ↦ by rw [h, ← le_bot_iff.1 (h ▸ hi ▸ h0.1 i)]) id
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  funext i
  have hi : tier c i = t ↔ tonalTier host i = t := by
    simpa using congrArg (i ∈ ·) heq.symm
  rcases hT i with h | h
  · rcases hH i with h' | h'
    · rw [h, h']
    · rw [h, h']; exact h.symm.trans (hi.2 h')
  · rw [h, hi.1 h]

/-- On an unvalued target, OBMOMx(T) towards the stem rates every candidate alike, so it leaves
the tune's docking to the rest of the ranking (ch. 5, Tableau 9). -/
theorem recessive_unvalued (host : List (TBU S)) (tier : C → Fin host.length → TRN)
    (h : ∀ τ ∈ host, ¬ τ.IsValued) :
    Cophonology.optimal default ((l, obmomx tier (tonalTier host)) :: sub) candidates =
      Cophonology.optimal (default.filter (·.1 ≠ l)) sub candidates :=
  optimal_cons_of_forall_eq fun c _ d _ ↦ by
    simp [obmomx, tonalTier_eq_bot_iff.2 h, absentViol_eq_zero_iff.2 bot_le]

/-! ### Tableaux on the target's tier

The candidates of Tableaux 5, 8 and 9 of ch. 5, read through the tones of the target. -/

-- Kalabari *mí* 'this' with *námá* 'meat': OMxOBM(T) keeps the tune's L H and the toneless
-- target and rejects the target's own H H, leaving the choice to IO(T).
example : Cophonology.optimal ([] : List (ℕ × Constraint (Fin 2 → TRN)))
    [(0, omxobm id (basemapTier [⟨(), TRN.H⟩, ⟨(), TRN.H⟩] ⟨[.L, .H], .left⟩))]
    {![.L, .H], ![.H, .H], ⊥} = {![.L, .H], ⊥} := by
  decide

-- Japanese *múraki* with *-si* 'Mr.': the recessive ranking keeps the target as it is.
example : Cophonology.optimal ([] : List (ℕ × Constraint (Fin 3 → TRN)))
    [(0, obmomx id ![.H, ⊥, ⊥]), (1, culmin id .H)]
    {![.H, ⊥, ⊥], ![.H, ⊥, .H], ![⊥, ⊥, .H], ⊥} = {![.H, ⊥, ⊥]} := by
  decide

-- Japanese *yosida* with *-si*: the same ranking lets the tune dock, while OMxOBM(T) towards the
-- stem would not.
example : Cophonology.optimal ([] : List (ℕ × Constraint (Fin 3 → TRN)))
    [(0, obmomx id ⊥), (1, culmin id .H)] {![⊥, ⊥, .H], ⊥} = {![⊥, ⊥, .H], ⊥} := by
  decide

example : Cophonology.optimal ([] : List (ℕ × Constraint (Fin 3 → TRN)))
    [(0, omxobm id ⊥)] {![⊥, ⊥, .H], ⊥} = {⊥} := by
  decide

end Rolle2018
