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

## Errata

* The discussion of the table summarizing the dominant-tone asymmetry calls the reverse of its
  row a. "row b."; it is row f.

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

variable {S C L : Type*} [DecidableEq L] (tier : C → List TRN) {candidates : Finset C}
  {default sub : List (L × Constraint C)} {l l' : L}

/-- OMxOBM(T), an output–output correspondence constraint in the sense of [benua-1997] directed
from the matrix output to the basemap output: a candidate violates it at each unit whose tone in
the matrix is not present in the basemap. -/
def omxobm (basemap : List TRN) : Constraint C :=
  fun c ↦ ((tier c).zip basemap).countP fun p ↦ ¬ p.1 ≤ p.2

/-- OBMOMx(T), directed from the basemap output to the matrix output: a candidate violates it at
each unit whose tone in the basemap is not present in the matrix. -/
def obmomx (basemap : List TRN) : Constraint C :=
  fun c ↦ (basemap.zip (tier c)).countP fun p ↦ ¬ p.1 ≤ p.2

/-- CULMINATIVITY for the toneme `t`: a candidate violates it at each occurrence of `t` beyond
the first. -/
def culmin (t : TRN) : Constraint C := fun c ↦ (tier c).count t - 1

private theorem countP_zip_eq_zero_iff {t₁ t₂ : List TRN} (h : t₁.length = t₂.length) :
    (t₁.zip t₂).countP (fun p ↦ ¬ p.1 ≤ p.2) = 0 ↔ List.Forall₂ (· ≤ ·) t₁ t₂ := by
  simp [List.countP_eq_zero, List.forall₂_iff_zip, h]

variable {tier} in
theorem omxobm_eq_zero_iff {B : List TRN} {c : C} (h : (tier c).length = B.length) :
    omxobm tier B c = 0 ↔ List.Forall₂ (· ≤ ·) (tier c) B :=
  countP_zip_eq_zero_iff h

variable {tier} in
theorem obmomx_eq_zero_iff {B : List TRN} {c : C} (h : (tier c).length = B.length) :
    obmomx tier B c = 0 ↔ List.Forall₂ (· ≤ ·) B (tier c) :=
  countP_zip_eq_zero_iff h.symm

theorem forall₂_le_of_mem_cophonologicalEval {B : List TRN}
    (hLen : ∀ c ∈ candidates, (tier c).length = B.length) (hB : ∃ c ∈ candidates, tier c = B) :
    ∀ c ∈ cophonologicalEval default ((l, omxobm tier B) :: sub) candidates,
      List.Forall₂ (· ≤ ·) (tier c) B := fun c hc ↦ by
  obtain ⟨d, hd, rfl⟩ := hB
  have h0 := eq_zero_of_mem_cophonologicalEval (pre := [(l, omxobm tier (tier d))]) hc hd <| by
    simp [(omxobm_eq_zero_iff rfl).2 (List.forall₂_refl _)]
  exact (omxobm_eq_zero_iff (hLen c (Tableau.optimal_subset hc))).1 (by simpa using h0)

private theorem eq_replicate_of_forall₂ {T : List TRN} {n : ℕ}
    (h : List.Forall₂ (· ≤ ·) T (List.replicate n ⊥)) : T = List.replicate n ⊥ := by
  induction n generalizing T with
  | zero => simpa using h
  | succ n ih =>
    obtain ⟨a, T, ha, hT, rfl⟩ := List.forall₂_cons_right_iff.1 h
    rw [le_bot_iff.1 ha, ih hT, List.replicate_succ]

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

/-- Under a trigger whose subranking puts OMxOBM(T) towards the induced basemap first, every
winner bears at each unit of the target nothing or the tone the tune puts there, whatever the
target's own tones (ch. 5, (22) and Tableau 5). -/
theorem dominant (host : List (TBU S)) (u : Tune)
    (hLen : ∀ c ∈ candidates, (tier c).length = host.length)
    (hu : ∃ c ∈ candidates, tier c = u.realize host.length) :
    ∀ c ∈ cophonologicalEval default
        ((l, omxobm tier ((basemapOutput host u).map TBU.tone)) :: sub) candidates,
      List.Forall₂ (· ≤ ·) (tier c) (u.realize host.length) := by
  rw [map_tone_basemapOutput]
  exact forall₂_le_of_mem_cophonologicalEval tier (by simpa using hLen) hu

/-- A trigger with no tune is subtractive: under OMxOBM(T) towards the basemap induced from the
target, every winner leaves the target unvalued (ch. 5, §5.3.3). -/
theorem subtractive (host : List (TBU S)) (e : Edge)
    (hLen : ∀ c ∈ candidates, (tier c).length = host.length)
    (hu : ∃ c ∈ candidates, tier c = (Dominance.subtractive.apply ⟨[], e⟩ host).map TBU.tone) :
    ∀ c ∈ cophonologicalEval default
        ((l, omxobm tier ((basemapOutput host ⟨[], e⟩).map TBU.tone)) :: sub) candidates,
      tier c = (Dominance.subtractive.apply ⟨[], e⟩ host).map TBU.tone := fun c hc ↦ by
  have hB : (Dominance.subtractive.apply ⟨[], e⟩ host).map TBU.tone =
      List.replicate host.length ⊥ := by
    simp [unvalue, TRN.bot_eq_empty, Function.comp_def, List.map_const']
  have hR : Tune.realize ⟨[], e⟩ host.length = List.replicate host.length ⊥ := by
    simp [TRN.bot_eq_empty]
  rw [hB] at hu ⊢
  have := dominant tier host ⟨[], e⟩ hLen (by rwa [hR]) c hc
  rw [hR] at this
  exact eq_replicate_of_forall₂ this

theorem omxobm_stem_unvalued (host : List (TBU S)) (h : ∀ τ ∈ host, ¬ τ.IsValued)
    (hLen : ∀ c ∈ candidates, (tier c).length = host.length)
    (hu : ∃ c ∈ candidates, tier c = host.map TBU.tone) :
    ∀ c ∈ cophonologicalEval default ((l, omxobm tier (host.map TBU.tone)) :: sub) candidates,
      tier c = host.map TBU.tone := by
  have hB : host.map TBU.tone = List.replicate host.length ⊥ :=
    List.eq_replicate_iff.2 ⟨by simp, by simpa [TBU.IsValued, TRN.bot_eq_empty] using h⟩
  rw [hB] at hu ⊢
  exact fun c hc ↦ eq_replicate_of_forall₂ <|
    forall₂_le_of_mem_cophonologicalEval tier (by simpa using hLen) hu c hc

private theorem count_le_of_forall₂ {t : TRN} :
    ∀ {H T : List TRN}, List.Forall₂ (· ≤ ·) H T → (∀ x ∈ T, x = ⊥ ∨ x = t) →
      H.count t ≤ T.count t
  | [], [], .nil, _ => le_rfl
  | a :: H, b :: T, .cons hab hHT, hT => by
    rw [List.forall_mem_cons] at hT
    have ih := count_le_of_forall₂ hHT hT.2
    have hbt : a = t → b = t := fun ha ↦
      hT.1.elim (fun hb ↦ by rw [hb, ← le_bot_iff.1 (hb ▸ hab), ha]) id
    by_cases ha : a = t
    · simp [ha, hbt ha]; omega
    · simp only [List.count_cons, beq_iff_eq, ha, ite_false]; split_ifs <;> omega

private theorem eq_of_forall₂_of_count_le {t : TRN} :
    ∀ {H T : List TRN}, List.Forall₂ (· ≤ ·) H T → (∀ x ∈ H, x = ⊥ ∨ x = t) →
      (∀ x ∈ T, x = ⊥ ∨ x = t) → T.count t ≤ H.count t → T = H
  | [], [], .nil, _, _, _ => rfl
  | a :: H, b :: T, .cons hab hHT, hH, hT, hc => by
    rw [List.forall_mem_cons] at hH hT
    have hmono := count_le_of_forall₂ hHT hT.2
    obtain rfl | hne := eq_or_ne a b
    · simp only [List.count_cons] at hc
      rw [eq_of_forall₂_of_count_le hHT hH.2 hT.2 (by omega)]
    · have hb : b = t := hT.1.resolve_left fun hb ↦ hne ((le_bot_iff.1 (hb ▸ hab)).trans hb.symm)
      have ha : a ≠ t := fun ha ↦ hne (ha.trans hb.symm)
      simp [ha, hb] at hc
      omega

/-- In a privative culminative system with the toneme `t`, a trigger whose subranking puts
OBMOMx(T) towards the stem and CULMINATIVITY first leaves a target bearing `t` once as it is:
the tune does not apply (ch. 5, (32) and Tableau 8). -/
theorem recessive (host : List (TBU S)) {t : TRN} (hhost : (host.map TBU.tone).count t = 1)
    (hpriv : ∀ c ∈ candidates, ∀ x ∈ tier c, x = ⊥ ∨ x = t)
    (hLen : ∀ c ∈ candidates, (tier c).length = host.length)
    (hu : ∃ c ∈ candidates, tier c = host.map TBU.tone) :
    ∀ c ∈ cophonologicalEval default
        ((l, obmomx tier (host.map TBU.tone)) :: (l', culmin tier t) :: sub) candidates,
      tier c = host.map TBU.tone := fun c hc ↦ by
  obtain ⟨d, hd, hdt⟩ := hu
  have hd₀ : obmomx tier (host.map TBU.tone) d = 0 :=
    (obmomx_eq_zero_iff (by rw [hdt])).2 (by rw [hdt]; exact List.forall₂_refl _)
  have hd₁ : culmin tier t d = 0 := by simp [culmin, hdt, hhost]
  have h0 := eq_zero_of_mem_cophonologicalEval
    (pre := [(l, obmomx tier (host.map TBU.tone)), (l', culmin tier t)]) hc hd <| by
      simp [hd₀, hd₁]
  have hc' := Tableau.optimal_subset hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h0
  refine eq_of_forall₂_of_count_le ((obmomx_eq_zero_iff (by simpa using hLen c hc')).1 h0.1)
    (hdt ▸ hpriv d hd) (hpriv c hc') ?_
  simp only [culmin] at h0
  omega

/-- On an unvalued target, OBMOMx(T) towards the stem rates every candidate alike, so it leaves
the tune's docking to the rest of the ranking (ch. 5, Tableau 9). -/
theorem recessive_unvalued (host : List (TBU S)) (h : ∀ τ ∈ host, ¬ τ.IsValued) :
    cophonologicalEval default ((l, obmomx tier (host.map TBU.tone)) :: sub) candidates =
      cophonologicalEval (default.filter (·.1 ≠ l)) sub candidates := by
  have h0 : ∀ c, obmomx tier (host.map TBU.tone) c = 0 := fun c ↦ by
    refine List.countP_eq_zero.2 fun p hp ↦ ?_
    obtain ⟨τ, hτ, hp⟩ := List.mem_map.1 (List.of_mem_zip hp).1
    have : p.1 = ⊥ := by simpa [TBU.IsValued, TRN.bot_eq_empty, hp] using h τ hτ
    simp [this]
  exact cophonologicalEval_cons_of_forall_eq fun c _ d _ ↦ (h0 c).trans (h0 d).symm

/-! ### Tableaux on the target's tier

The candidates of Tableaux 5, 8 and 9 of ch. 5, read through the tones of the target. -/

-- Kalabari *mí* 'this' with *námá* 'meat': OMxOBM(T) keeps the tune's L H and the toneless
-- target and rejects the target's own H H, leaving the choice to IO(T).
example : cophonologicalEval ([] : List (ℕ × Constraint (List TRN)))
    [(0, omxobm id ((basemapOutput [⟨(), TRN.H⟩, ⟨(), TRN.H⟩] ⟨[.L, .H], .left⟩).map TBU.tone))]
    {[.L, .H], [.H, .H], [⊥, ⊥]} = {[.L, .H], [⊥, ⊥]} := by
  decide

-- Japanese *múraki* with *-si* 'Mr.': the recessive ranking keeps the target as it is.
example : cophonologicalEval ([] : List (ℕ × Constraint (List TRN)))
    [(0, obmomx id [.H, ⊥, ⊥]), (1, culmin id .H)]
    {[.H, ⊥, ⊥], [.H, ⊥, .H], [⊥, ⊥, .H], [⊥, ⊥, ⊥]} = {[.H, ⊥, ⊥]} := by
  decide

-- Japanese *yosida* with *-si*: the same ranking lets the tune dock, while OMxOBM(T) towards the
-- stem would not.
example : cophonologicalEval ([] : List (ℕ × Constraint (List TRN)))
    [(0, obmomx id [⊥, ⊥, ⊥]), (1, culmin id .H)]
    {[⊥, ⊥, .H], [⊥, ⊥, ⊥]} = {[⊥, ⊥, .H], [⊥, ⊥, ⊥]} := by
  decide

example : cophonologicalEval ([] : List (ℕ × Constraint (List TRN)))
    [(0, omxobm id [⊥, ⊥, ⊥])] {[⊥, ⊥, .H], [⊥, ⊥, ⊥]} = {[⊥, ⊥, ⊥]} := by
  decide

end Rolle2018
