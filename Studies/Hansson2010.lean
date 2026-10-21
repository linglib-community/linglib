module

public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Subregular.Agree
public import Linglib.Phonology.Subregular.Multitier
public import Linglib.Phonology.Harmony.System
public import Linglib.Data.Examples.Hansson2010

/-!
# Hansson (2010): Consonant Harmony: Long-Distance Interaction in Phonology

This file formalizes the Navajo sibilant harmony with which Hansson opens his survey of
consonant harmony (section 1.1, and the case study of section 2.4.1.1). The alveolar and
postalveolar sibilant series cannot co-occur, and when morpheme concatenation juxtaposes them
the rightmost sibilant determines the anteriority of every sibilant before it, across any
vowels and non-sibilant consonants in between (3), (4), (6). The sibilants are the [+strident]
segments, and the harmony is agreement in [anterior] on their tier, a tier-based strictly
2-local language. The map `anticipatory` writes the rightmost sibilant's [anterior] value into
every sibilant, and its fixed points are exactly the words of that language,
`mem_language_iff_anticipatory_eq`. It leaves the trigger and everything off the tier in place
and neutralizes the contrast in the sibilants it targets, the three characteristics the book
draws from (4). It is the search-and-copy run, from the right, of the substrate's harmony
`System` over segments with [anterior] as its feature, the decomposition Rose and Walker share
with the vowel harmonies of the fragments, `anticipatory_eq_apply`. The book's own
qualification (section 3.1.2) is the perseveratory assimilation of the first-person subject
prefix after the s-perfective and s-destruct prefixes (12), (14), which the anticipatory map
mispredicts, `perseveratory_rows`, while harmony from the root still overrides it (15).

## Implementation notes

A segment's class on the tier, `sibilantClass`, is its [anterior] value, and the book's claims
about the examples concern the classes on the tier, so the rows of `Data.Examples.Hansson2010`
are read for their sibilants and compared class by class. Voicing, which the s-perfective
changes in (4b) and (4c) under a condition the book sets aside, and the glottalization of
affricates are not compared. The Navajo sibilants are the chart's without [distributed], on which
the chart's alveolar and postalveolar series also differ, so that anteriority is the whole of
the contrast the harmony changes. The book's correspondence-theoretic analysis (chapters 4 and 5),
its typological survey (chapter 2), and its speech-error account (chapter 6) are not formalized;
Rose and Walker's Agreement by Correspondence is in `Studies/RoseWalker2004.lean`.

## References

* [hansson-2010]
* [rose-walker-2011]
* [rose-walker-2004]
* [mcdonough-1991]
* [sapir-hoijer-1967]
-/

@[expose] public section

namespace Hansson2010

open Subregular Phonology Phonology.Harmony Data.PHOIBLE
open Subregular.TierStrictlyLocalGrammar (map_mem_ofForbiddenPairs_language_iff
  mem_ofForbiddenPairs_language_iff ofForbiddenPairs_language_congr)

/-! ### The harmony tier -/

/-- The class of a sibilant is its [anterior] value, `true` for the alveolar series and `false`
for the postalveolar, and a segment that is not a sibilant has none. -/
def sibilantClass (x : Segment) : Option Bool := if x.IsSibilant then x .anterior else none

/-- A segment is on the harmony tier when it has a class. -/
def OnTier (x : Segment) : Prop := (sibilantClass x).isSome

instance : DecidablePred OnTier := fun _ ↦ inferInstanceAs (Decidable (_ = true))

theorem isSibilant_of_onTier {x : Segment} (h : OnTier x) : x.IsSibilant := by
  by_contra hs
  simp [OnTier, sibilantClass, hs] at h

theorem sibilantClass_of_onTier {x : Segment} (h : OnTier x) : sibilantClass x = x .anterior :=
  ite_eq_left (isSibilant_of_onTier h)

theorem setFeature_anterior_isSibilant (x : Segment) (v : Bool) :
    (x.setFeature .anterior v).IsSibilant ↔ x.IsSibilant := by
  simp [Segment.IsSibilant, Segment.HasValue]

theorem sibilantClass_setFeature {x : Segment} (h : OnTier x) (v : Bool) :
    sibilantClass (x.setFeature .anterior v) = some v := by
  rw [sibilantClass, ite_eq_left ((setFeature_anterior_isSibilant x v).2 (isSibilant_of_onTier h))]
  exact Segment.setFeature_hasValue x .anterior v

theorem onTier_setFeature {x : Segment} (h : OnTier x) (v : Bool) :
    OnTier (x.setFeature .anterior v) := by
  simp [OnTier, sibilantClass_setFeature h v]

/-! ### Navajo sibilants and the transcriptions -/

/-- A Navajo sibilant is its chart entry's segment without [distributed]. -/
def sibilant (m : FeatureMatrix) : Segment := .ofChart m ⊥ {.distributed}ᶜ

/-- The alveolar fricative /s/. -/
def s : Segment := sibilant .«s»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := sibilant .«z»

/-- The postalveolar fricative /ʃ/. -/
def esh : Segment := sibilant .«ʃ»

/-- The voiced postalveolar fricative /ʒ/. -/
def ezh : Segment := sibilant .«ʒ»

/-- The alveolar affricate /ts/. -/
def ts : Segment := sibilant .«ts»

/-- The voiced alveolar affricate /dz/. -/
def dz : Segment := sibilant .«dz»

/-- The postalveolar affricate /tʃ/. -/
def tesh : Segment := sibilant .«t̠ʃ»

/-- The voiced postalveolar affricate /dʒ/. -/
def dezh : Segment := sibilant .«d̠ʒ»

/-- The two series differ in [anterior] alone, pair by pair. -/
theorem eqOn_anterior_compl :
    ∀ p ∈ [(s, esh), (z, ezh), (ts, tesh), (dz, dezh)], ∀ f ≠ .anterior, p.1 f = p.2 f := by
  decide

/-- The sibilants of a transcription, in order, an affricate being written with two
letters. -/
def sibilantsOf : List Char → List Segment
  | 't' :: 's' :: cs => ts :: sibilantsOf cs
  | 't' :: 'ʃ' :: cs => tesh :: sibilantsOf cs
  | 'd' :: 'z' :: cs => dz :: sibilantsOf cs
  | 'd' :: 'ʒ' :: cs => dezh :: sibilantsOf cs
  | 's' :: cs => s :: sibilantsOf cs
  | 'z' :: cs => z :: sibilantsOf cs
  | 'ʃ' :: cs => esh :: sibilantsOf cs
  | 'ʒ' :: cs => ezh :: sibilantsOf cs
  | _ :: cs => sibilantsOf cs
  | [] => []

/-- The underlying sibilants of a row, from its `underlying` feature. -/
def ur (e : Datum) : List Segment := sibilantsOf ((e.feature? "underlying").getD "").toList

/-- The surface sibilants of a row. -/
def sr (e : Datum) : List Segment := sibilantsOf e.primaryText.toList

/-- The sibilants of a word, in order. -/
abbrev sibilants (w : List Segment) : List Segment := w.filter (OnTier ·)

theorem onTier_of_mem_sibilants {w : List Segment} {x : Segment} (h : x ∈ sibilants w) :
    OnTier x :=
  of_decide_eq_true (List.mem_filter.mp h).2

/-! ### The surface language -/

/-- The surface phonotactic of section 2.4.1.1 requires adjacent sibilants on the tier to agree
in [anterior]. -/
abbrev navajoSibilantHarmony : TierStrictlyLocalGrammar 2 Segment :=
  TierStrictlyLocalGrammar.ofForbiddenPairs (fun x y ↦ x .anterior ≠ y .anterior) OnTier

theorem isTierStrictlyLocal : Language.IsTierStrictlyLocal 2 navajoSibilantHarmony.language :=
  ⟨_, rfl⟩

theorem isBTSL : Language.IsBTSL 2 navajoSibilantHarmony.language :=
  isTierStrictlyLocal.toIsBTSL

/-- A word is harmonic iff its sibilants agree in [anterior], however far apart. -/
theorem mem_language_iff (w : List Segment) :
    w ∈ navajoSibilantHarmony.language ↔
      ∀ x ∈ sibilants w, ∀ y ∈ sibilants w, x .anterior = y .anterior := by
  have : IsTrans Segment (fun x y ↦ x .anterior = y .anterior) := ⟨fun _ _ _ ↦ Eq.trans⟩
  have : Std.Symm (fun x y : Segment ↦ x .anterior = y .anterior) := ⟨fun _ _ ↦ Eq.symm⟩
  rw [mem_ofForbiddenPairs_language_iff]
  simp only [ne_eq, not_not]
  exact ⟨fun h ↦ h.pairwise.forall_of_forall fun _ _ ↦ rfl,
    fun h ↦ (List.pairwise_of_forall_mem_list h).isChain⟩

/-- The language is the inverse image, under the sibilant class, of agreement among the
classes. -/
theorem language_eq_preimage : navajoSibilantHarmony.language =
    List.map sibilantClass ⁻¹' (TierStrictlyLocalGrammar.agree (·.isSome)).language := by
  ext w
  show _ ↔ w.map sibilantClass ∈ (TierStrictlyLocalGrammar.agree (·.isSome)).language
  rw [TierStrictlyLocalGrammar.agree, map_mem_ofForbiddenPairs_language_iff]
  exact Eq.to_iff (congrArg (w ∈ ·) (ofForbiddenPairs_language_congr (fun _ ↦ Iff.rfl)
    fun x y hx hy ↦ by rw [sibilantClass_of_onTier hx, sibilantClass_of_onTier hy]))

/-! ### Anticipatory harmony, section 1.1 -/

/-- The trigger is the class of the rightmost sibilant of a word. -/
def trigger (w : List Segment) : Option Bool := (sibilants w).getLast?.bind sibilantClass

/-- A sibilant takes the trigger's [anterior] value, and anything off the tier is
untouched. -/
def harmonize (t : Option Bool) (x : Segment) : Segment :=
  if OnTier x then t.elim x (x.setFeature .anterior) else x

/-- Anticipatory sibilant harmony gives every sibilant the class of the rightmost one. -/
def anticipatory (w : List Segment) : List Segment := w.map (harmonize (trigger w))

theorem harmonize_of_not_onTier {t : Option Bool} {x : Segment} (h : ¬ OnTier x) :
    harmonize t x = x :=
  ite_eq_right h

theorem harmonize_none (x : Segment) : harmonize none x = x := by
  unfold harmonize; split_ifs <;> rfl

theorem harmonize_some {x : Segment} (h : OnTier x) (v : Bool) :
    harmonize (some v) x = x.setFeature .anterior v :=
  ite_eq_left h

theorem onTier_harmonize (t : Option Bool) (x : Segment) : OnTier (harmonize t x) ↔ OnTier x := by
  by_cases h : OnTier x
  · cases t with
    | none => rw [harmonize_none]
    | some v => exact iff_of_true (harmonize_some h v ▸ onTier_setFeature h v) h
  · rw [harmonize_of_not_onTier h]

theorem sibilants_map_harmonize (t : Option Bool) (w : List Segment) :
    sibilants (w.map (harmonize t)) = (sibilants w).map (harmonize t) := by
  simp only [sibilants, List.filter_map]
  exact congrArg _ (List.filter_congr fun x _ ↦ by simp [onTier_harmonize])

/-- A word has a trigger exactly when it has a sibilant. -/
theorem trigger_eq_none_iff (w : List Segment) : trigger w = none ↔ sibilants w = [] := by
  rw [trigger]
  rcases hl : (sibilants w).getLast? with _ | x
  · simpa using hl
  · have hx := onTier_of_mem_sibilants (List.mem_of_getLast? hl)
    simp only [Option.bind_some, ← List.getLast?_eq_none_iff, hl, reduceCtorEq, iff_false]
    exact Option.ne_none_iff_isSome.2 hx

/-- The harmony leaves the trigger in place, so the rightmost sibilant determines the rest. -/
theorem trigger_anticipatory (w : List Segment) : trigger (anticipatory w) = trigger w := by
  rw [anticipatory]
  rcases ht : trigger w with _ | v
  · rw [show harmonize none = id from funext harmonize_none, List.map_id, ht]
  · rw [trigger] at ht
    rcases hl : (sibilants w).getLast? with _ | x
    · simp [hl] at ht
    · have hx := onTier_of_mem_sibilants (List.mem_of_getLast? hl)
      rw [trigger, sibilants_map_harmonize, List.getLast?_map, hl, Option.map_some,
        Option.bind_some, harmonize_some hx, sibilantClass_setFeature hx]

/-- The harmonized word is harmonic. -/
theorem anticipatory_mem_language (w : List Segment) :
    anticipatory w ∈ navajoSibilantHarmony.language := by
  rw [mem_language_iff, anticipatory, sibilants_map_harmonize]
  rcases ht : trigger w with _ | v
  · simp [(trigger_eq_none_iff w).1 ht]
  · simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [harmonize_some (onTier_of_mem_sibilants hx), harmonize_some (onTier_of_mem_sibilants hy)]
    simp [Segment.setFeature]

/-- A harmonic word is a fixed point of the harmony. -/
theorem anticipatory_eq_self_of_mem {w : List Segment}
    (h : w ∈ navajoSibilantHarmony.language) : anticipatory w = w := by
  rw [mem_language_iff] at h
  refine (List.map_congr_left fun x hx ↦ ?_).trans (List.map_id w)
  by_cases hon : OnTier x
  · have hxs : x ∈ sibilants w := List.mem_filter.mpr ⟨hx, decide_eq_true hon⟩
    obtain ⟨y, hy⟩ :=
      Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr (List.ne_nil_of_mem hxs))
    have hys := List.mem_of_getLast? hy
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (onTier_of_mem_sibilants hys)
    have htr : trigger w = some v := by rw [trigger, hy, Option.bind_some, hv]
    have hxv : x .anterior = some v := by
      rw [h x hxs y hys, ← sibilantClass_of_onTier (onTier_of_mem_sibilants hys), hv]
    rw [htr, harmonize_some hon, id]
    exact Function.update_eq_self_iff.mpr hxv.symm
  · exact harmonize_of_not_onTier hon

/-- The surface language is exactly the set of fixed points of anticipatory harmony, so the
stringset the tier-based grammar recognizes and the map the harmony computes are one object. -/
theorem mem_language_iff_anticipatory_eq (w : List Segment) :
    w ∈ navajoSibilantHarmony.language ↔ anticipatory w = w :=
  ⟨anticipatory_eq_self_of_mem, fun h ↦ h ▸ anticipatory_mem_language w⟩

/-- In the neutralization of (4), prefixes whose sibilants differ only in [anterior] surface
alike once a sibilant follows. -/
theorem anticipatory_cons_eq {a b : Segment} {w : List Segment} (ha : OnTier a) (hb : OnTier b)
    (hab : ∀ f ≠ .anterior, a f = b f) (hw : sibilants w ≠ []) :
    anticipatory (a :: w) = anticipatory (b :: w) := by
  have htr : ∀ c, OnTier c → trigger (c :: w) = trigger w := fun c hc ↦ by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hw)
    simp only [trigger, sibilants] at hy ⊢
    rw [List.filter_cons_of_pos (p := fun x ↦ decide (OnTier x)) (decide_eq_true hc),
      List.getLast?_cons, hy]
    rfl
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((trigger_eq_none_iff w).not.mpr hw)
  simp only [anticipatory, List.map_cons, htr a ha, htr b hb, hv, harmonize_some ha,
    harmonize_some hb]
  refine congrArg₂ _ (funext fun f ↦ ?_) rfl
  obtain rfl | hf := eq_or_ne f .anterior
  · simp [Segment.setFeature]
  · simp [Segment.setFeature, Function.update_of_ne hf, hab f hf]

/-- The alveolar and postalveolar fricatives neutralize before a sibilant. -/
example (w : List Segment) (hw : sibilants w ≠ []) :
    anticipatory (s :: w) = anticipatory (esh :: w) :=
  anticipatory_cons_eq (by decide) (by decide) (eqOn_anterior_compl (s, esh) (by simp)) hw

/-! ### The examples -/

/-- On the anticipatory examples of (3), (4), (6), (11), (13), and (15) the map takes each
underlying form to the classes of its surface sibilants. -/
theorem anticipatory_rows :
    ∀ e ∈ Examples.all, e.feature? "directionality" = some "anticipatory" →
      (anticipatory (ur e)).map sibilantClass = (sr e).map sibilantClass := by
  decide

/-- The book qualifies the account in section 3.1.2. The s-perfective (12) and s-destruct (14)
prefixes assimilate the following first-person prefix perseveratively, which the anticipatory
map mispredicts. -/
theorem perseveratory_rows :
    ∀ e ∈ Examples.all, e.feature? "directionality" = some "perseveratory" →
      (anticipatory (ur e)).map sibilantClass ≠ (sr e).map sibilantClass := by
  decide

/-- The underlying form of (6a) is disharmonic. -/
theorem ur_ex6a_ii_violates : ur Examples.ex6a_ii ∉ navajoSibilantHarmony.language := by
  rw [mem_language_iff_anticipatory_eq]
  decide

/-- Its surface form is harmonic. -/
theorem sr_ex6a_ii_legal : sr Examples.ex6a_ii ∈ navajoSibilantHarmony.language := by
  rw [mem_language_iff_anticipatory_eq]
  decide

/-! ### The harmony system -/

/-- Navajo sibilant harmony is the harmony `System` over segments with [anterior] as its
feature, in which the sibilants are targets, all else is transparent, nothing blocks, and the
direction is leftward. -/
def navajo : System Segment := System.mk' .anterior OnTier (¬ OnTier ·) .leftward

theorem pattern_onTier_iff (x : Segment) : navajo.pattern.OnTier x ↔ OnTier x := by
  by_cases h : OnTier x <;> simp [navajo, System.mk', Pattern.OnTier, h]

theorem pattern_tier (w : List Segment) : navajo.pattern.tier w = sibilants w :=
  List.filter_congr fun x _ ↦ by simp [pattern_onTier_iff]

/-- Every sibilant is a participating target with a value. -/
theorem saturated : navajo.Saturated := fun x hx ↦ by
  rw [pattern_onTier_iff] at hx
  refine ⟨hx, by simp [navajo, System.mk', hx], ?_⟩
  show (x .anterior).isSome
  rw [← sibilantClass_of_onTier hx]
  exact hx

theorem preservesTier : navajo.searchCopy.PreservesTier := fun v x hx ↦ by
  rw [System.searchCopy_tier, pattern_onTier_iff, pattern_onTier_iff]
  exact iff_of_true (onTier_setFeature ((pattern_onTier_iff x).1 hx.2) v)
    ((pattern_onTier_iff x).1 hx.2)

/-- The sibilant class is the system's tier projection. -/
theorem pattern_project : navajo.pattern.project = sibilantClass := by
  funext x
  by_cases h : OnTier x
  · rw [Pattern.project, ite_eq_left ((pattern_onTier_iff x).2 h), sibilantClass_of_onTier h]
    rfl
  · rw [Pattern.project, ite_eq_right (mt (pattern_onTier_iff x).1 h)]
    exact (Option.not_isSome_iff_eq_none.mp h).symm

/-- The system's surface harmonicity is the tier-based language. -/
theorem harmonic_iff_mem_language (w : List Segment) :
    navajo.pattern.Harmonic w ↔ w ∈ navajoSibilantHarmony.language := by
  rw [navajo.pattern.harmonic_iff_map_project_mem (fun x hx ↦ (saturated x hx).2) w,
    pattern_project, language_eq_preimage]
  rfl

/-- Anticipatory harmony is the search-and-copy run of the system in its direction. -/
theorem anticipatory_eq_apply (w : List Segment) :
    anticipatory w = navajo.searchCopy.apply w := by
  rw [navajo.apply_eq_map saturated preservesTier rfl, anticipatory]
  refine List.map_congr_left fun x _ ↦ ?_
  have htrigger : (navajo.pattern.tier (navajo.pattern.direction.scanEdge.orient w)).head?.bind
      navajo.pattern.value = trigger w := by
    rw [show navajo.pattern.direction.scanEdge = .right from rfl, Edge.orient_right,
      navajo.pattern.tier_reverse, pattern_tier, List.head?_reverse]
    rcases hl : (sibilants w).getLast? with _ | y
    · simp [trigger, hl]
    · simp [trigger, hl, navajo, System.mk',
        sibilantClass_of_onTier (onTier_of_mem_sibilants (List.mem_of_getLast? hl))]
  rw [htrigger, harmonize]
  simp only [pattern_onTier_iff]
  rfl

end Hansson2010
