module

public import Linglib.Data.Examples.GokselKerslake2005
public import Linglib.Fragments.Turkish.Clause
public import Linglib.Fragments.Turkish.Possession
public import Linglib.Fragments.Turkish.QuestionParticles
public import Linglib.Fragments.Turkish.Verbs
public import Linglib.Morphology.Morphotactics.Concatenation

/-!
# Göksel and Kerslake (2005): Turkish suffixation

This file checks the account of the form and order of Turkish suffixes in the reference
grammar of Göksel and Kerslake against the Turkish Fragment.

The example words of Chapters 3, 6 and 8 are rows of the data, each naming its stem and its
suffixes, and every one of them is written as the surface form of that stem with those
suffixes (`printed`). A person marker is read as one of group 1 or of group 2 by the suffix
before it (§8.4), and a possessive by the suffix after it (§8.1.2).

The vowel harmony of Chapter 3 is derived by the surface forms of `Turkish.Phonology` from the
exponent forms of `Turkish.Morphotactics`. Harmony and the voicing of a suffix-initial stop fill
features in and change none, so each harmonized segment is at least its underlying segment in
the order of `Phonology.Segment` (`forall₂_le_harmonize`). The Fragment states them in terms
of features alone, as the grammar does: `Turkish.Phonology.fill w x` is the segment `x` after
the harmonized string `w`, and the harmonized form of `w ++ [x]` is that of `w` followed by
`fill` of it and `x`. The search-and-copy rules of the three harmony systems, run in turn,
compute the same form for every word (`harmonize_eq_searchCopy`). The underlying form of a
word attaches its suffixes one at a time, and before raising the harmonized word is stepwise and
concatenative in the sense of `Morphology.Morphotactics`: a suffix sees only the harmonized word
it attaches to and leaves it in place (`isStepwise_harmonize_underlying`,
`isConcatenative_harmonize_underlying`). Raising before -(I)yor alters the stem, so surface
forms are not concatenative (`not_isConcatenative_realize`). The alternants that the
grammar lists for `A`, `I` and `D` are the values of `fill` (`fill_A`, `fill_I`, `fill_D`), and
two stems of phonemes that end alike take their suffixes alike
(`exists_harmonize_append_eq`). The permissible vowel sequences of §3.1 are the
surface forms of the two suffix vowels. The last vowel of a disharmonic loan decides
(*otobüs-ler*), an invariant suffix vowel is skipped and triggers what follows (*görüyorum*,
§3.4), and the palatal l of *gol* fronts its suffix (§3.4). The bracketed segments of Chapter 6
appear where they keep vowels and consonants apart (§6.1.3), and a stem-final `a` or `e`,
the vowel of the negative included, is raised before -(I)yor (§8.2.3.3).

The suffix order of Chapter 8 is licensing by the templates of the finite verb and the nominal,
the person marker of the verb moving where §8.4 allows and nowhere else.
The grammar's example words are licensed with their stacked voice suffixes, reversed orders are
not, and the rule that markers of one position cannot co-occur (§8.2.3) holds because the
template does not repeat the position.

The question clitic *mI* stands before the first clitic among the markers of a predicate and
after the other markers (§11.1.1.5), as `Turkish.QuestionParticles.mi.insert` places it, so the
grammar's examples are its surface forms, the markers after it attached to it.

The converbs of §8.5.2.2 are those of `Turkish.Converb` on the grammar's verbs, and
*-(y)Ip* and *-(y)ArAk* follow every slot before the position-3 marker and none after it
(§28.2).

The possessive and locative existential sentences of §12.1.1.2 are those of
`Turkish.Possession`, with the possessive suffix on the possessee obligatory (§14.4).

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

@[expose] public section

namespace GokselKerslake2005

open Turkish Phonology Phonology.Harmony Verb.Exponent Nominal.Exponent QuestionParticles

/-! ### Vowel harmony (Chapter 3) -/

/-- `followers v` lists the vowels that may follow `v` in a suffix, the surface forms of `A`
and of `I` after it. -/
def followers (v : Segment) : List Segment :=
  [A, I].map fun x ↦ (surface [v, x]).getLastD x

/-- The permissible vowel sequences are those the grammar tabulates (§3.1). -/
theorem followers_table :
    followers a = [a, ı] ∧ followers ı = [a, ı] ∧ followers o = [a, u] ∧ followers u = [a, u] ∧
    followers e = [e, i] ∧ followers i = [e, i] ∧ followers ö = [e, ü] ∧ followers ü = [e, ü] := by
  decide

/-! ### The grammar's words -/

/-- The segments of the stem that a lexeme of the data is, the loans *gol* and *hal* ending in
the palatal lateral (§3.4 (iv)). -/
def Examples.Lexeme.stem : Examples.Lexeme → List Segment
  | .kiz => [k, ı, z]
  | .el => [e, l]
  | .kol => [k, o, l]
  | .goz => [g, ö, z]
  | .otobus => [o, t, o, b, ü, s]
  | .uz => [ü, z]
  | .gor => [g, ö, r]
  | .bak => [b, a, k]
  | .gol => [g, o, l']
  | .hal => [h, a, l']
  | .kal => [k, a, l]
  | .dus => [d, ü, ş]
  | .pul => [p, u, l]
  | .ev => [e, v]
  | .araba => [a, r, a, b, a]
  | .ara => [a, r, a]
  | .sor => [s, o, r]
  | .atla => [a, t, l, a]
  | .suna => [s, u, n, a]
  | .betul => [b, e, t, ü, l]
  | .emine => [e, m, i, n, e]
  | .elbise => [e, l, b, i, s, e]
  | .tepe => [t, e, p, e]
  | .yuz => [y, ü, z]
  | .oda => [o, d, a]
  | .masa => [m, a, s, a]
  | .okul => [o, k, u, l]
  | .hasta => [h, a, s, t, a]
  | .kat => [k, a, t]
  | .anla => [a, n, l, a]
  | .oksa => [o, k, ş, a]
  | .bekle => [b, e, k, l, e]
  | .ozle => [ö, z, l, e]
  | .eri => [e, r, i]
  | .kuru => [k, u, r, u]
  | .sakla => [s, a, k, l, a]
  | .soyle => [s, ö, y, l, e]
  | .yap => [y, a, p]
  | .koy => [k, o, y]
  | .ol => [ö, l]
  | .dol => [d, o, l]

/-- The exponent of the nominal that a gloss of the data names, if it names one. -/
def Examples.Suffix.nominal? : Examples.Suffix → Option (Σ σ, Nominal.Exponent σ)
  | .pl => some ⟨_, plural⟩
  | .poss1sg => some ⟨_, possessive (.personNumber .first .singular)⟩
  | .poss2sg => some ⟨_, possessive (.personNumber .second .singular)⟩
  | .poss3sg => some ⟨_, possessive (.personNumber .third .singular)⟩
  | .poss1pl => some ⟨_, possessive (.personNumber .first .plural)⟩
  | .poss2pl => some ⟨_, possessive (.personNumber .second .plural)⟩
  | .poss3pl => some ⟨_, possessive (.personNumber .third .plural)⟩
  | .gen => some ⟨_, genitive⟩
  | .dat => some ⟨_, dative⟩
  | .loc => some ⟨_, locative⟩
  | _ => none

/-- The group of a person marker after the suffix `prev`: group 1 after -DI, -sA and the
copular markers -(y)DI and -(y)sA, and group 2 otherwise (§8.4). -/
def groupAfter (prev : Option Examples.Suffix) : Verb.PersonGroup :=
  if prev ∈ [some .pf, some .cond, some .pCop, some .condCop] then .one else .two

/-- The forms of the verbal or predicate suffix that a gloss of the data names, after the
suffix `prev`. -/
def Examples.Suffix.verbal (prev : Option Examples.Suffix) :
    Examples.Suffix → List Turkish.Suffix
  | .pass => [passive.form]
  | .caus => [causative.form]
  | .neg => [negative.form]
  | .pf => [di.form]
  | .evPf => [miş.form]
  | .impf => [iyor.form]
  | .aor => [aorist.form]
  | .fut => [acak.form]
  | .cond => [sa.form]
  | .pCop => [pastCopula.form]
  | .evCop => [evidentialCopula.form]
  | .condCop => [conditionalCopula.form]
  | .cv => Converb.ken.form
  | .p1sg => [(person (groupAfter prev) (.personNumber .first .singular)).form]
  | .p1pl => [(person (groupAfter prev) (.personNumber .first .plural)).form]
  | .p2pl => [(person (groupAfter prev) (.personNumber .second .plural)).form]
  | .p3pl => [(person (groupAfter prev) (.personNumber .third .plural)).form]
  | _ => []

/-- The forms of a string of glosses. A nominal exponent takes its form before the one after
it, as `Nominal.forms` gives it, and a verbal one after the gloss before it. -/
def suffixForms : Option Examples.Suffix → List Examples.Suffix → List Suffix
  | _, [] => []
  | prev, x :: xs =>
    (match x.nominal? with
      | some e => (Nominal.forms (e :: (xs.head?.bind (·.nominal?)).toList)).take 1
      | none => x.verbal prev) ++ suffixForms (some x) xs

/-- The segments that a string of letters writes, capitals as small letters and without the
morpheme boundaries and the full stop. -/
def segments? (cs : List Char) : Option (List Segment) :=
  ((cs.filter fun c ↦ c ≠ '-' ∧ c ≠ '.').map Char.toLower).mapM ofChar

/-- A surface form as the alphabet writes it, the palatal lateral as the plain one and the
final consonant of -(y)AcAK as `k`. -/
def written (w : List Segment) : List Segment :=
  w.map fun x ↦ if x = l' then l else if x = K then k else x

/-- Every example word of the grammar is written as the surface form of its stem with its
suffixes. -/
theorem printed : ∀ x : Examples.Example, ∃ st ∈ (x.lexemes .stem).head?,
    ∃ w ∈ x.datum.glossedWords.head?,
      segments? w.word = some (written (realize st.stem (suffixForms none x.suffixes))) := by
  decide

-- where the grammar segments a word, its first morph writes the stem
theorem stem_printed : ∀ x : Examples.Example, ∀ st ∈ (x.lexemes .stem).head?,
    ∀ w ∈ x.datum.glossedWords.head?, ∀ m ∈ w.glossedMorphemes.head?,
      1 < w.glossedMorphemes.length → segments? m.morpheme = some (written st.stem) := by
  decide

/-- The juncture of *araba* 'car' and the vowel of -(I)m. -/
def arabaIm : Hiatus.Juncture := ⟨[a, r, a, b], a, I, [m], by decide, by decide⟩

/-- The juncture of *masa* 'table' and the vowel of -(y)A. -/
def masaA : Hiatus.Juncture := ⟨[m, a, s], a, A, [], by decide, by decide⟩

/-- Bracketed vowels and consonants are the two repairs of hiatus, elision in *araba-m* and
epenthesis in *masa-ya* (§6.1.3, §8.1.2, §8.1.3). -/
theorem hiatus_repairs :
    (possessive (.personNumber .first .singular)).form.attach arabaIm.left = arabaIm.elideV2 ∧
    dative.form.attach masaA.left = masaA.epenthesize y :=
  ⟨Suffix.attach_eq_elideV2 arabaIm rfl rfl,
    Suffix.attach_eq_epenthesize masaA rfl (by decide) rfl⟩

/-- The spelled stem of every verb of the Fragment writes the surface form of its root and
voice suffixes, the causatives *öldür-* and *yaptır-* among them. -/
theorem spelled_stems : ∀ v ∈ verbs, ofString? v.form = some (v.inflect []) := by
  decide

/-! ### The search-and-copy rules compute the harmonized form -/

private theorem not_isTarget : ∀ x ∈ vowels ∪ consonants, ¬ fronting.searchCopy.IsTarget x ∧
    ¬ rounding.searchCopy.IsTarget x ∧ ¬ voicing.searchCopy.IsTarget x := by decide

private theorem fronting_preservesTier : fronting.searchCopy.PreservesTier := by
  intro v s h
  simp [fronting, System.mk', System.searchCopy, Pattern.OnTier] at h ⊢
  exact fun _ ↦ h.1.1

private theorem rounding_preservesTier : rounding.searchCopy.PreservesTier := by
  intro v s h
  simp [rounding, System.mk', System.searchCopy, Pattern.OnTier] at h ⊢

private theorem voicing_preservesTier : voicing.searchCopy.PreservesTier := by
  intro v s h
  simp [voicing, System.mk', System.searchCopy, Pattern.OnTier] at h ⊢

private theorem fronting_participating {b : Segment} (h : fronting.pattern.OnTier b) :
    fronting.pattern.participation b = .participating := by
  simpa [fronting, System.mk', Pattern.OnTier] using h

private theorem rounding_participating {b : Segment} (h : rounding.pattern.OnTier b) :
    rounding.pattern.participation b = .participating := by
  simpa [rounding, System.mk', Pattern.OnTier] using h

private theorem fronting_tier_iff (s : Segment) :
    fronting.searchCopy.tier s ↔ s.IsSyllabic ∨ s .back ≠ none := by
  simp [fronting, System.mk', System.searchCopy, Pattern.OnTier, Segment.IsSyllabic]; tauto

private theorem rounding_tier_iff (s : Segment) : rounding.searchCopy.tier s ↔ s.IsSyllabic := by
  simp [rounding, System.mk', System.searchCopy, Pattern.OnTier, Segment.IsSyllabic]

private theorem filter_fronting_tier (w : List Segment) :
    w.filter (fronting.searchCopy.tier ·) = w.filter fun s ↦ s.IsSyllabic ∨ s .back ≠ none :=
  List.filter_congr fun s _ ↦ decide_eq_decide.2 (fronting_tier_iff s)

private theorem filter_rounding_tier (w : List Segment) :
    w.filter (rounding.searchCopy.tier ·) = w.filter (·.IsSyllabic) :=
  List.filter_congr fun s _ ↦ decide_eq_decide.2 (rounding_tier_iff s)

private theorem fronting_emit (w : List Segment) (x : Segment) :
    fronting.searchCopy.emit (w.filter (fronting.searchCopy.tier ·)).getLast? x =
      if x.IsSyllabic ∧ x .back = none then
        x.copy .back (w.filter fun s ↦ s.IsSyllabic ∨ s .back ≠ none).getLast? else x := by
  have ht := fronting_tier_iff
  have hx : fronting.IsTarget x ∧ fronting.pattern.OnTier x ↔ x.IsSyllabic ∧ x .back = none :=
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, (ht x).2 (.inl h.1)⟩⟩
  rw [fronting.emit_eq_of_participating rfl fun c hc ↦ by
    have := of_decide_eq_true (List.mem_filter.1 (List.mem_of_getLast? hc)).2
    simpa [fronting, System.mk', Pattern.OnTier] using this,
    List.filter_congr fun s _ ↦ decide_eq_decide.2 (ht s)]
  simp only [hx]
  rfl

private theorem rounding_emit (w : List Segment) (x : Segment) :
    rounding.searchCopy.emit (w.filter (rounding.searchCopy.tier ·)).getLast? x =
      if x.IsSyllabic ∧ x .high = true ∧ x .round = none then
        x.copy .round (w.filter (·.IsSyllabic)).getLast? else x := by
  have ht := rounding_tier_iff
  have hx : rounding.IsTarget x ∧ rounding.pattern.OnTier x ↔
      x.IsSyllabic ∧ x .high = true ∧ x .round = none :=
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, (ht x).2 h.1⟩⟩
  rw [rounding.emit_eq_of_participating rfl fun c hc ↦ by
    have := of_decide_eq_true (List.mem_filter.1 (List.mem_of_getLast? hc)).2
    simpa [rounding, System.mk', Pattern.OnTier] using this,
    List.filter_congr fun s _ ↦ decide_eq_decide.2 (ht s)]
  simp only [hx]
  rfl

private theorem voicing_emit (w : List Segment) (x : Segment) :
    voicing.searchCopy.emit w.getLast? x =
      if x .voice = none then x.copy .voice w.getLast? else x := by
  have hx : voicing.IsTarget x ∧ voicing.pattern.OnTier x ↔ x .voice = none :=
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, by simp [voicing, System.mk', Pattern.OnTier]⟩⟩
  rw [voicing.emit_eq_of_participating rfl fun c _ ↦ by simp [voicing, System.mk']]
  simp only [hx]
  rfl

private theorem emit_eq_fill (w : List Segment) (x : Segment) :
    voicing.searchCopy.emit w.getLast?
      (rounding.searchCopy.emit (w.filter (rounding.searchCopy.tier ·)).getLast?
        (fronting.searchCopy.emit (w.filter (fronting.searchCopy.tier ·)).getLast? x)) =
      fill w x := by
  rw [fronting_emit, rounding_emit, voicing_emit]
  rfl

private theorem scans_concat (w : List Segment) (x : Segment) :
    voicing.searchCopy.scan (rounding.searchCopy.scan (fronting.searchCopy.scan (w ++ [x]))) =
      voicing.searchCopy.scan (rounding.searchCopy.scan (fronting.searchCopy.scan w)) ++
        [fill (voicing.searchCopy.scan (rounding.searchCopy.scan (fronting.searchCopy.scan w)))
          x] := by
  rw [fronting.searchCopy.scan_concat fronting_preservesTier,
    rounding.searchCopy.scan_concat rounding_preservesTier,
    voicing.searchCopy.scan_concat voicing_preservesTier]
  generalize fronting.searchCopy.scan w = F
  generalize hR : rounding.searchCopy.scan F = R
  generalize hV : voicing.searchCopy.scan R = V
  have ev : ∀ g : Phonology.Feature, g ≠ .voice → ∀ q s, (voicing.searchCopy.emit q s) g = s g :=
    fun g hg ↦ SearchCopy.emit_apply_of_ne (fun _ _ ↦ rfl) (Ne.symm hg)
  have er : ∀ g : Phonology.Feature, g ≠ .round → ∀ q s, (rounding.searchCopy.emit q s) g = s g :=
    fun g hg ↦ SearchCopy.emit_apply_of_ne (fun _ _ ↦ rfl) (Ne.symm hg)
  have mV : ∀ {γ : Type} (π : Segment → γ), (∀ q s, π (voicing.searchCopy.emit q s) = π s) →
      V.map π = R.map π := fun π h ↦ by
    rw [← hV]; exact voicing.searchCopy.toMealy.map_run R h
  have mR : ∀ {γ : Type} (π : Segment → γ), (∀ q s, π (rounding.searchCopy.emit q s) = π s) →
      R.map π = F.map π := fun π h ↦ by
    rw [← hR]; exact rounding.searchCopy.toMealy.map_run F h
  have hVR : V.map (fun c ↦ (c .round, c .syllabic)) = R.map fun c ↦ (c .round, c .syllabic) :=
    mV _ fun q s ↦ Prod.ext (ev .round (by decide) q s) (ev .syllabic (by decide) q s)
  have hVF : V.map (fun c ↦ (c .back, c .syllabic)) = F.map fun c ↦ (c .back, c .syllabic) :=
    (mV _ fun q s ↦ Prod.ext (ev .back (by decide) q s) (ev .syllabic (by decide) q s)).trans
      (mR _ fun q s ↦ Prod.ext (er .back (by decide) q s) (er .syllabic (by decide) q s))
  have h₁ : V.filter (voicing.searchCopy.tier ·) = V :=
    List.filter_eq_self.2 fun a _ ↦ by simp [voicing, System.mk', System.searchCopy, Pattern.OnTier]
  have h₂ : ∀ y, rounding.searchCopy.emit (R.filter (rounding.searchCopy.tier ·)).getLast? y =
      rounding.searchCopy.emit (V.filter (rounding.searchCopy.tier ·)).getLast? y :=
    rounding.searchCopy.emit_getLast?_filter_congr
      (fun c c' h ↦ by
        obtain ⟨-, h⟩ := Prod.mk.inj h
        simp_all [rounding, System.mk', System.searchCopy, Pattern.OnTier])
      (fun c c' t h ↦ by
        obtain ⟨h, h'⟩ := Prod.mk.inj h
        simp_all [rounding, System.mk', System.searchCopy, Pattern.OnTier]) hVR.symm
  have h₃ : fronting.searchCopy.emit (F.filter (fronting.searchCopy.tier ·)).getLast? x =
      fronting.searchCopy.emit (V.filter (fronting.searchCopy.tier ·)).getLast? x :=
    fronting.searchCopy.emit_getLast?_filter_congr
      (fun c c' h ↦ by
        obtain ⟨h, h'⟩ := Prod.mk.inj h
        simp_all [fronting, System.mk', System.searchCopy, Pattern.OnTier])
      (fun c c' t h ↦ by
        obtain ⟨h, h'⟩ := Prod.mk.inj h
        simp_all [fronting, System.mk', System.searchCopy, Pattern.OnTier]) hVF.symm x
  rw [h₁, h₂, h₃, emit_eq_fill]

private theorem harmonize_eq_scan (w : List Segment) : harmonize w =
    voicing.searchCopy.scan (rounding.searchCopy.scan (fronting.searchCopy.scan w)) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih => rw [harmonize_concat, scans_concat, ih]

/-- The search-and-copy rules of fronting, rounding and voicing, run in turn, compute the
harmonized form of every word. -/
theorem harmonize_eq_searchCopy (w : List Segment) : harmonize w =
    voicing.searchCopy.apply (rounding.searchCopy.apply (fronting.searchCopy.apply w)) := by
  rw [harmonize_eq_scan, voicing.searchCopy.apply_eq_scan rfl,
    rounding.searchCopy.apply_eq_scan rfl, fronting.searchCopy.apply_eq_scan rfl]

/-! ### Harmony fills features in (Chapter 3) -/

/-- Harmony and voicing fill features in and change none: each segment of `harmonize w` has
every feature value of the segment of `w` it comes from. -/
theorem forall₂_le_harmonize (w : List Segment) : List.Forall₂ (· ≤ ·) w (harmonize w) := by
  rw [harmonize_eq_scan]
  simpa only [Mealy.run_comp, Function.comp_apply, SearchCopy.scan] using
    (voicing.searchCopy.toMealy.comp (rounding.searchCopy.toMealy.comp
      fronting.searchCopy.toMealy)).forall₂_run w fun q s ↦
    ((fronting.searchCopy.le_emit (fun v s h ↦ Segment.le_setFeature h.1.2 v) _ s).trans
      (rounding.searchCopy.le_emit (fun v s h ↦ Segment.le_setFeature h.1.2.2 v) _ _)).trans
      (voicing.searchCopy.le_emit (fun v s h ↦ Segment.le_setFeature h.1 v) _ _)

/-- Raising is the one rule of the surface form that changes a feature value. -/
theorem forall₂_le_surface (w : List Segment) :
    List.Forall₂ (· ≤ ·) (raising.apply w) (surface w) :=
  forall₂_le_harmonize _

/-- A string of phonemes is harmonized already. -/
theorem harmonize_eq_self {w : List Segment} (hw : ∀ x ∈ w, x ∈ vowels ∪ consonants) :
    harmonize w = w := by
  rw [harmonize_eq_scan, fronting.searchCopy.scan_eq_self fun s hs ↦ (not_isTarget s (hw s hs)).1,
    rounding.searchCopy.scan_eq_self fun s hs ↦ (not_isTarget s (hw s hs)).2.1,
    voicing.searchCopy.scan_eq_self fun s hs ↦ (not_isTarget s (hw s hs)).2.2]

/-- Adding segments to a word leaves the harmonized form of the word in place. -/
theorem harmonize_isPrefix_append (w s : List Segment) :
    harmonize w <+: harmonize (w ++ s) := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s x ih =>
    rw [← List.append_assoc, harmonize_concat]
    exact ih.trans (List.prefix_append _ _)

/-- Stems that end alike take their suffixes alike: two strings of phonemes with the same last
segment, the same last vowel and the same last vowel or palatal lateral are followed by the same
harmonized segments, whatever is added, so that a loan such as *otobüs* takes the suffixes of a
native stem in `ü` (Chapter 3). -/
theorem exists_harmonize_append_eq {w w' : List Segment}
    (hw : ∀ x ∈ w, x ∈ vowels ∪ consonants) (hw' : ∀ x ∈ w', x ∈ vowels ∪ consonants)
    (hl : w.getLast? = w'.getLast?)
    (hv : (w.filter (·.IsSyllabic)).getLast? = (w'.filter (·.IsSyllabic)).getLast?)
    (hb : (w.filter fun s ↦ s.IsSyllabic ∨ s .back ≠ none).getLast? =
      (w'.filter fun s ↦ s.IsSyllabic ∨ s .back ≠ none).getLast?)
    (s : List Segment) : ∃ t, harmonize (w ++ s) = w ++ t ∧ harmonize (w' ++ s) = w' ++ t := by
  induction s using List.reverseRecOn with
  | nil => exact ⟨[], by simp [harmonize_eq_self hw], by simp [harmonize_eq_self hw']⟩
  | append_singleton s x ih =>
    obtain ⟨t, h, h'⟩ := ih
    have hf : fill (w' ++ t) x = fill (w ++ t) x := by
      simp only [fill, List.filter_append, List.getLast?_append, hl, hv, hb]
    exact ⟨t ++ [fill (w ++ t) x],
      by rw [← List.append_assoc, harmonize_concat, h, List.append_assoc],
      by rw [← List.append_assoc, harmonize_concat, h', hf, List.append_assoc]⟩

/-! ### The alternants of an archiphoneme (§3.2, §6.1.2) -/

/-- After a string whose last segment that is syllabic or bears [back] has the value `β` for
[back], `A` is `a` or `e` accordingly (§3.2.2). -/
theorem fill_A {w : List Segment} {b : Segment} {β : Bool}
    (hb : (w.filter fun s ↦ s.IsSyllabic ∨ s .back ≠ none).getLast? = some b)
    (hβ : b .back = some β) : fill w A = A.setFeature .back β := by
  rw [← filter_fronting_tier] at hb
  have hbt : fronting.pattern.OnTier b :=
    of_decide_eq_true (List.mem_filter.1 (List.mem_of_getLast? hb)).2
  have h₁ : fronting.searchCopy.emit (some b) A = A.setFeature .back β :=
    fronting.emit_eq_write_of_found_eq_some (by decide) (by decide)
      ((fronting.found_some_of_participating (fronting_participating hbt) A).trans hβ)
  rw [← emit_eq_fill, hb, h₁]
  cases β <;>
    rw [rounding.searchCopy.emit_of_not_isTarget (by decide),
      voicing.searchCopy.emit_of_not_isTarget (by decide)]

/-- After a string whose last segment that is syllabic or bears [back] has the value `β` for
[back] and whose last syllabic segment has the value `ρ` for [round], `I` is the high vowel
with those values (§3.2.1). -/
theorem fill_I {w : List Segment} {b v : Segment} {β ρ : Bool}
    (hb : (w.filter fun s ↦ s.IsSyllabic ∨ s .back ≠ none).getLast? = some b)
    (hβ : b .back = some β) (hv : (w.filter (·.IsSyllabic)).getLast? = some v)
    (hρ : v .round = some ρ) : fill w I = (I.setFeature .back β).setFeature .round ρ := by
  rw [← filter_fronting_tier] at hb
  rw [← filter_rounding_tier] at hv
  have hbt : fronting.pattern.OnTier b :=
    of_decide_eq_true (List.mem_filter.1 (List.mem_of_getLast? hb)).2
  have hvt : rounding.pattern.OnTier v :=
    of_decide_eq_true (List.mem_filter.1 (List.mem_of_getLast? hv)).2
  have h₁ : fronting.searchCopy.emit (some b) I = I.setFeature .back β :=
    fronting.emit_eq_write_of_found_eq_some (by decide) (by decide)
      ((fronting.found_some_of_participating (fronting_participating hbt) I).trans hβ)
  have h₂ : rounding.searchCopy.emit (some v) (I.setFeature .back β) =
      (I.setFeature .back β).setFeature .round ρ :=
    rounding.emit_eq_write_of_found_eq_some (by cases β <;> decide) (by cases β <;> decide)
      ((rounding.found_some_of_participating (rounding_participating hvt) _).trans hρ)
  rw [← emit_eq_fill, hb, hv, h₁, h₂]
  cases β <;> cases ρ <;> exact voicing.searchCopy.emit_of_not_isTarget (by decide) _

/-- After a string whose last segment has the value `ν` for [voice], `D` is `d` or `t`
accordingly (§6.1.2). -/
theorem fill_D {w : List Segment} {x : Segment} {ν : Bool}
    (hx : w.getLast? = some x) (hν : x .voice = some ν) :
    fill w D = D.setFeature .voice ν := by
  rw [← emit_eq_fill, fronting.searchCopy.emit_of_not_isTarget (by decide),
    rounding.searchCopy.emit_of_not_isTarget (by decide), hx]
  exact voicing.emit_eq_write_of_found_eq_some (by decide) (by decide)
    ((voicing.found_some_of_participating (by simp [voicing, System.mk']) D).trans hν)

/-- A phoneme stands unchanged wherever it occurs, so the vowel of a disharmonic stem or an
invariable suffix decides for what follows it (§3.4). -/
theorem fill_of_mem {x : Segment} (hx : x ∈ vowels ∪ consonants) (w : List Segment) :
    fill w x = x := by
  obtain ⟨h₁, h₂, h₃⟩ := not_isTarget x hx
  rw [← emit_eq_fill, fronting.searchCopy.emit_of_not_isTarget h₁,
    rounding.searchCopy.emit_of_not_isTarget h₂, voicing.searchCopy.emit_of_not_isTarget h₃]

/-! ### Suffixes one at a time -/

theorem underlying_eq_ofStep (w : List Segment) (sfxs : List Suffix) :
    underlying w sfxs = Morphology.Morphotactics.ofStep id Suffix.attach w sfxs :=
  rfl

/-- Before raising, a further suffix leaves the word before it in place. -/
theorem isConcatenative_harmonize_underlying :
    Morphology.Morphotactics.IsConcatenative fun w sfxs ↦ harmonize (underlying w sfxs) :=
  fun w sfxs s ↦ by
    change harmonize (underlying w sfxs) <+: harmonize (underlying w (sfxs ++ [s]))
    rw [underlying_append, underlying_cons, underlying_nil, Suffix.attach, List.append_assoc]
    exact harmonize_isPrefix_append _ _

/-- Raising before -(I)yor alters the stem, so surface forms are not concatenative: *anla* is
no prefix of *anlıyor* (§8.2.3.3). -/
theorem not_isConcatenative_realize : ¬ Morphology.Morphotactics.IsConcatenative realize :=
  fun h ↦ absurd (h [a, n, l, a] [] iyor.form) (by decide)

private theorem isVowel_fill (w : List Segment) (x : Segment) :
    (fill w x).IsVowel ↔ x.IsVowel := by
  simp only [fill]
  split_ifs <;>
    simp [Segment.IsVowel, Segment.IsSyllabic, Segment.copy_apply_of_ne]

private theorem initial_harmonize (s : Suffix) (u : List Segment) :
    s.initial (harmonize u) = s.initial u := by
  cases hb : s.bracketed with
  | none => rw [Suffix.initial_of_bracketed_eq_none hb, Suffix.initial_of_bracketed_eq_none hb]
  | some b =>
    induction u using List.reverseRecOn with
    | nil => rfl
    | append_singleton u x _ =>
      rw [harmonize_concat, Suffix.initial_concat hb, Suffix.initial_concat hb]
      simp only [isVowel_fill]

/-- Before raising, a suffix sees only the harmonized word it attaches to: two words that are
harmonized alike are harmonized alike with one more suffix. -/
theorem isStepwise_harmonize_underlying :
    Morphology.Morphotactics.IsStepwise fun w sfxs ↦ harmonize (underlying w sfxs) :=
  fun w w' sfxs sfxs' s h ↦ by
    replace h : harmonize (underlying w sfxs) = harmonize (underlying w' sfxs') := h
    simp only [underlying_append, underlying_cons, underlying_nil, Suffix.attach,
      List.append_assoc, harmonize_append]
    rw [← initial_harmonize s (underlying w sfxs), ← initial_harmonize s (underlying w' sfxs'), h]

/-! ### The order of suffixes (Chapter 8) -/

-- §8.1, (1)
theorem nominal :
    Nominal.template.Licensed (E := Nominal.Exponent)
      [⟨_, .plural⟩, ⟨_, .possessive (.personNumber .second .singular)⟩, ⟨_, .dative⟩] := by
  decide

/-- *Döğ-üş-tür-t-ül-me-yebil-iyor-muş-sunuz-dur* fills every slot of the finite verb, the
voice slot with four stacked suffixes (§8.2 (7)). -/
theorem finite_verb :
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .reciprocal⟩, ⟨_, .causative⟩, ⟨_, .causative⟩, ⟨_, .passive⟩, ⟨_, .negative⟩,
        ⟨_, .abil⟩, ⟨_, .iyor⟩, ⟨_, .evidentialCopula⟩,
        ⟨_, .person .two (.personNumber .second .plural)⟩,
        ⟨_, .dir⟩] := by
  decide

-- §8.2.3, (11), (12), §8.2.3.3
theorem tam_positions :
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .possibility⟩, ⟨_, .negative⟩, ⟨_, .miş⟩, ⟨_, .dir⟩] ∧
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .abil⟩, ⟨_, .acak⟩, ⟨_, .evidentialCopula⟩] ∧
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .di⟩, ⟨_, .pastCopula⟩, ⟨_, .person .one (.personNumber .second .singular)⟩] := by
  decide

-- §8.2.2, §8.2.3
theorem reversed_orders :
    ¬ Verb.template.Licensed (E := Verb.Exponent) [⟨_, .negative⟩, ⟨_, .causative⟩] ∧
    ¬ Verb.template.Licensed (E := Verb.Exponent) [⟨_, .di⟩, ⟨_, .negative⟩] ∧
    ¬ Verb.template.Licensed (E := Verb.Exponent) [⟨_, .pastCopula⟩, ⟨_, .di⟩] := by
  decide

/-- Markers of position 3 cannot co-occur, since the template does not repeat the position
(§8.2.3 (i)). -/
theorem same_position_excluded (m₁ m₂ : Verb.Exponent .tam) :
    ¬ Verb.template.Licensed [⟨_, m₁⟩, ⟨_, m₂⟩] :=
  show [Verb.Slot.tam, .tam] ∉ Verb.template.language by decide

/-- On a verb a person marker precedes the copular marker when it is a group-1 marker after
-DI, as in *gittimdi*, *geldinizse* and *baktıktı*, or the third-person plural, as in
*kat-sa-lar-dı*, and the third-person plural may also follow -DIr, as in *gid-iyor-dur-lar*,
beside the orders of the template (§8.3.2, §8.3.3, §8.4). -/
theorem person_mobility : ∀ w ∈ ([
      ([g, i, t], [⟨_, di⟩, ⟨_, person .one (.personNumber .first .singular)⟩, ⟨_, pastCopula⟩],
        "gittimdi"),
      ([g, i, t], [⟨_, di⟩, ⟨_, pastCopula⟩, ⟨_, person .one (.personNumber .first .singular)⟩],
        "gittiydim"),
      ([g, e, l], [⟨_, di⟩, ⟨_, person .one (.personNumber .second .plural)⟩,
        ⟨_, conditionalCopula⟩], "geldinizse"),
      ([g, e, l], [⟨_, di⟩, ⟨_, conditionalCopula⟩,
        ⟨_, person .one (.personNumber .second .plural)⟩], "geldiyseniz"),
      ([b, a, k], [⟨_, di⟩, ⟨_, person .one (.personNumber .first .plural)⟩, ⟨_, pastCopula⟩],
        "baktıktı"),
      ([k, a, t], [⟨_, sa⟩, ⟨_, person .one (.personNumber .third .plural)⟩, ⟨_, pastCopula⟩],
        "kat-sa-lar-dı"),
      ([g, i, d], [⟨_, iyor⟩, ⟨_, person .two (.personNumber .third .plural)⟩, ⟨_, dir⟩],
        "gid-iyor-lar-dır"),
      ([g, i, d], [⟨_, iyor⟩, ⟨_, dir⟩, ⟨_, person .two (.personNumber .third .plural)⟩],
        "gid-iyor-dur-lar")] :
      List (List Segment × List (Σ σ, Verb.Exponent σ) × String)),
    Verb.Licensed w.2.1 ∧
      ofSegmented? w.2.2 = some (realize w.1 (Verb.forms w.2.1)) := by
  decide

/-- No other person marker leaves its place: a group-2 marker does not precede a copular
marker or follow -DIr, and a group-1 marker after -sA does not precede a copular marker
(§8.3.3, §8.4). -/
theorem person_fixed :
    ¬ Verb.Licensed [⟨_, iyor⟩, ⟨_, person .two (.personNumber .first .singular)⟩,
      ⟨_, pastCopula⟩] ∧
    ¬ Verb.Licensed [⟨_, iyor⟩, ⟨_, dir⟩, ⟨_, person .two (.personNumber .first .singular)⟩] ∧
    ¬ Verb.Licensed [⟨_, sa⟩, ⟨_, person .one (.personNumber .first .singular)⟩,
      ⟨_, pastCopula⟩] := by
  decide

/-! ### The question clitic (§11.1.1.5) -/

/-- *mI* precedes the copular markers -(y)DI and -(y)mIş, as in *Gitse miydik?*, *Başlamış
mıydınız?* and *Burada mıymış?*, the group-2 person markers but the third-person plural, as in
*Gidiyor musun?*, *İster miyiz?* and *Hazır mısınız?*, and -DIr, as in *Unutmuş mudurlar?*,
*Evde midir?* and *geçmiş miyimdir?*, and the markers after it attach to it. -/
theorem mi_precedes_clitics : ∀ w ∈ ([
      ([g, i, t], [⟨_, sa⟩, ⟨_, pastCopula⟩, ⟨_, person .one (.personNumber .first .plural)⟩],
        ["gitse", "miydik"]),
      ([b, a, ş, l, a],
        [⟨_, miş⟩, ⟨_, pastCopula⟩, ⟨_, person .one (.personNumber .second .plural)⟩],
        ["başlamış", "mıydınız"]),
      ([b, u, r, a, d, a], [⟨_, evidentialCopula⟩], ["burada", "mıymış"]),
      ([g, i, d], [⟨_, iyor⟩, ⟨_, person .two (.personNumber .second .singular)⟩],
        ["gidiyor", "musun"]),
      ([i, s, t, e], [⟨_, aorist⟩, ⟨_, person .two (.personNumber .first .plural)⟩],
        ["ister", "miyiz"]),
      ([h, a, z, ı, r], [⟨_, person .two (.personNumber .second .plural)⟩], ["hazır", "mısınız"]),
      ([u, n, u, t], [⟨_, miş⟩, ⟨_, dir⟩, ⟨_, person .two (.personNumber .third .plural)⟩],
        ["unutmuş", "mudurlar"]),
      ([e, v, d, e], [⟨_, dir⟩], ["evde", "midir"]),
      ([g, e, ç], [⟨_, miş⟩, ⟨_, person .two (.personNumber .first .singular)⟩, ⟨_, dir⟩],
        ["geçmiş", "miyimdir"])] :
      List (List Segment × List (Σ σ, Verb.Exponent σ) × List String)),
    Verb.Licensed w.2.1 ∧
      (w.2.2.mapM ofString?).map List.flatten = some (realize w.1 (mi.insert w.2.1)) := by
  decide

/-- *mI* follows the group-1 person markers, as in *Gördün mü?*, *Gitsek mi?* and *Yürüdünüz
mü?*, those of group 3 in the first and third persons, as in *Kalayım mı?* and *Başlasın mı?*,
the third-person plural, as in
*Gittiler mi?*, *Uyanırlar mı?* and *Okuldalar mı?*, and a subject complement without markers,
as in *Akıllı mı?* and *Benimki mi?*. -/
theorem mi_follows : ∀ w ∈ ([
      ([g, ö, r], [⟨_, di⟩, ⟨_, person .one (.personNumber .second .singular)⟩], ["gördün", "mü"]),
      ([g, i, t], [⟨_, sa⟩, ⟨_, person .one (.personNumber .first .plural)⟩], ["gitsek", "mi"]),
      ([y, ü, r, ü], [⟨_, di⟩, ⟨_, person .one (.personNumber .second .plural)⟩],
        ["yürüdünüz", "mü"]),
      ([k, a, l], [⟨_, optative⟩, ⟨_, person .three (.personNumber .first .singular)⟩],
        ["kalayım", "mı"]),
      ([b, a, ş, l, a], [⟨_, person .three (.personNumber .third .singular)⟩], ["başlasın", "mı"]),
      ([g, i, t], [⟨_, di⟩, ⟨_, person .one (.personNumber .third .plural)⟩], ["gittiler", "mi"]),
      ([u, y, a, n], [⟨_, aorist⟩, ⟨_, person .two (.personNumber .third .plural)⟩],
        ["uyanırlar", "mı"]),
      ([o, k, u, l, d, a], [⟨_, person .two (.personNumber .third .plural)⟩], ["okuldalar", "mı"]),
      ([a, k, ı, l, l, ı], [], ["akıllı", "mı"]),
      ([b, e, n, i, m, k, i], [], ["benimki", "mi"])] :
      List (List Segment × List (Σ σ, Verb.Exponent σ) × List String)),
    Verb.Licensed w.2.1 ∧
      (w.2.2.mapM ofString?).map List.flatten = some (realize w.1 (mi.insert w.2.1)) := by
  decide

/-! ### Converbs (§8.5.2.2) -/

/-- The converbs on the grammar's verbs: on the stem, as in *koşup*, *kalkmayınca*,
*yıkılmadan* and *koştukça*, -(y)ken on a position-3 marker or a nominal, as in
*çalış-ır-ken* and *sokaktayken*, and -cAsInA on -mIş and a person marker, as in
*duymamışçasına* and *konuşuyormuşumcasına* (§8.5.1.1, §8.5.2.2, §26.2.3 (40),
§26.3.8 (69), (73)). -/
theorem converbs : ∀ w ∈ [("koşup", [k, o, ş], Converb.ip.form),
      ("girip", [g, i, r], Converb.ip.form),
      ("yüzünce", [y, ü, z], Converb.inca.form),
      ("kalkmayınca", [k, a, l, k], negative.form :: Converb.inca.form),
      ("koşarak", [k, o, ş], Converb.arak.form),
      ("büyüyerek", [b, ü, y, ü], Converb.arak.form),
      ("çalışarak", [ç, a, l, ı, ş], Converb.arak.form),
      ("düşüneli", [d, ü, ş, ü, n], Converb.ali.form),
      ("geleli", [g, e, l], Converb.ali.form),
      ("yıkılmadan", [y, ı, k], passive.form :: Converb.madan.form),
      ("seyretmeden", [s, e, y, r, e, t], Converb.madan.form),
      ("koştukça", [k, o, ş], Converb.dikca.form),
      ("çalış-ır-ken", [ç, a, l, ı, ş], aorist.form :: Converb.ken.form),
      ("çocukken", [ç, o, c, u, k], Converb.ken.form),
      ("sokaktayken", [s, o, k, a, k], locative.form :: Converb.ken.form),
      ("duymamışçasına", [d, u, y], negative.form :: miş.form :: Converb.casina.form),
      ("konuşuyormuşumcasına", [k, o, n, u, ş], iyor.form :: evidentialCopula.form ::
        (person .two (.personNumber .first .singular)).form :: Converb.casina.form)],
    ofSegmented? w.1 = some (realize w.2.1 w.2.2) := by
  decide

/-- The converbs on two verbs, as in *baka baka*, *duy-du-m duy-alı* and *ye-r ye-mez*
(§8.5.2.2). -/
theorem doubled_converbs :
    ofString? "baka" = some (realize [b, a, k] DoubledConverb.aA.forms.1) ∧
    ofString? "baka" = some (realize [b, a, k] DoubledConverb.aA.forms.2) ∧
    ofString? "duydum" = some (realize [d, u, y]
      (DoubledConverb.diAli.forms.1 ++ [(person .one (.personNumber .first .singular)).form])) ∧
    ofString? "duyalı" = some (realize [d, u, y] DoubledConverb.diAli.forms.2) ∧
    ofString? "yer" = some (realize [y, e] DoubledConverb.arMaz.forms.1) ∧
    ofString? "yemez" = some (realize [y, e] DoubledConverb.arMaz.forms.2) := by
  decide

/-- -(y)Ip and -(y)ArAk stand in place of the position-3 marker and all the suffixes after it,
so they follow exactly the slots before it (§28.2). -/
theorem conjunctive_converbs :
    ∀ c ∈ [Converb.ip, .arak], ∀ s : Verb.Slot, s ≤ c.follows ↔ s < .tam := by
  decide

/-! ### Existential sentences (§12.1.1.2) -/

/-- The existentials (21), (22) and (26), such as *Murat'ın yatı var* 'Murat has a yacht', are
possessive. -/
theorem possessive_existential :
    Possession.IsPossessive [[a, y, t, e, n]] [realize [i, s, t, a, n, b, u, l] [locative.form]]
        [[i, k, i], [a, r, k, a, d, a, ş]] (.personNumber .third .singular) Possession.var
        [[a, y, t, e, n, i, n], [i, s, t, a, n, b, u, l, d, a], [i, k, i],
          [a, r, k, a, d, a, ş, ı], [v, a, r]] ∧
    Possession.IsPossessive [[a, y, t, e, n]] [realize [i, s, t, a, n, b, u, l] [locative.form]]
        [[i, k, i], [a, r, k, a, d, a, ş]] (.personNumber .third .singular) Possession.var
        [[i, s, t, a, n, b, u, l, d, a], [a, y, t, e, n, i, n], [i, k, i],
          [a, r, k, a, d, a, ş, ı], [v, a, r]] ∧
    Possession.IsPossessive [] [[o], [g, ü, n]] [[p, a, r, a]] (.personNumber .first .plural)
        (Possession.predicate Possession.yok (some pastCopula))
        [[o], [g, ü, n], [p, a, r, a, m, ı, z], [y, o, k, t, u]] ∧
    Possession.IsPossessive [[m, u, r, a, t]] [] [[y, a, t]] (.personNumber .third .singular)
        Possession.var [[m, u, r, a, t, ı, n], [y, a, t, ı], [v, a, r]] := by
  decide

/-- The locative existential sentence (17), *Ben-de bir kitap var* 'I have a book'. -/
theorem locative_existential :
    Possession.locative [[b, e, n]] [[b, i, r], [k, i, t, a, p]] Possession.var =
      [[b, e, n, d, e], [b, i, r], [k, i, t, a, p], [v, a, r]] := by
  decide

/-- The possessive suffix on *araba* in (117), *Sizin arabanız var mı?*, is obligatory: the
sentence before its question clitic is possessive, and no person-number cell gives it with the
bare *araba* (§14.4). -/
theorem possessive_obligatory :
    Possession.IsPossessive [[s, i, z]] [] [[a, r, a, b, a]] (.personNumber .second .plural)
        Possession.var [[s, i, z, i, n], [a, r, a, b, a, n, ı, z], [v, a, r]] ∧
      ∀ c ∈ Agreement.Bundle.personNumberCells, ¬ Possession.IsPossessive [[s, i, z]] []
        [[a, r, a, b, a]] c Possession.var [[s, i, z, i, n], [a, r, a, b, a], [v, a, r]] :=
  ⟨by decide, fun _ hc h ↦ h.ne_bare (np := []) hc [[s, i, z, i, n]] rfl⟩

end GokselKerslake2005
