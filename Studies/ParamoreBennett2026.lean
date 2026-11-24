module

public import Linglib.Data.Statistics.ParamoreBennett2026
public import Linglib.Data.Wordlist.ParamoreBennett2026
public import Linglib.Languages.Punjabi.Phonology
public import Linglib.Phonology.OptimalityTheory.Correspondence.Transderivational
public import Linglib.Phonology.RuleInteraction
public import Linglib.Phonology.Harmony.Nasal
public import Linglib.Phonology.Subregular.ForbiddenPairs
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Paramore and Bennett (2026): Covert URs: Evidence from nasalization in Panjabi

In Pakistani Panjabi long vowels contrast in nasality, a vowel before a nasal consonant is
nasal, and nasality spreads leftward from a nasal vowel through vowels and glides. This file
formalizes the analysis of that pattern by two ordered rules in the notation of
[chomsky-halle-1968]. Harmony gives [+nasal] to a segment that is [−consonantal] when only such
segments stand between it and a following nasal vowel; assimilation gives [+nasal] to a vowel
before a nasal consonant. Harmony applies first, so the surface form of an underlying form `u`
is `surface u = assimilation (harmony u)`, and a vowel that assimilation nasalizes triggers no
harmony: assimilation counterfeeds harmony, in the sense of [bakovic-blumenfeld-2024]. An
underlying form is covert when one of its segments surfaces unaltered in no context.

A word is its own surface form exactly when neither rule applies in it, a condition on adjacent
segments, and an underlying form is covert exactly when it is not its own surface form. An
underlying form with an oral vowel before a nasal consonant is covert whether or not harmony
applies, and one that harmony alone changes is covert only if harmony applies. Over the
phonemes, the underlying forms of [ɑɑʋɑ̃ɑ̃m] 'general public' are /ɑɑʋɑɑm/ alone. Among the
stimuli of the paper's second experiment, the surface form taken as an underlying form surfaces
unchanged except in the pre-N condition.

The morphemes are taken to be the words over the phonemes with no nasal vowel before a nasal
consonant. Their surface forms have no nasal glide, nasal vowel and nasal consonant in sequence,
and they are not a strictly 2-local language, while the words that are their own surface forms
are one. The stimuli with a postposition that begins in a nasal consonant have that sequence
across the boundary.

In Berbice Dutch Creole, identity to the base [nimi] keeps the nasal of [nim-tɛ] from
assimilating in place, and the same strings without a base assimilate. The paper's forms and
stimuli are read from its data, and the intervals of its nasalance models are compared with its
regions of practical equivalence.

## Implementation notes

* Harmony is `Phonology.Harmony.nasalSpread`, a search-and-copy rule: a target takes [+nasal]
  from the output of the segment to its right when that is a nasal vowel or glide, and every
  other segment halts its search. Scanning from the right, it applies the paper's rule
  iteratively. The two differ on a nasal glide in the input, which triggers here; the phonemes
  have none.
* The rules are those the paper prints. The targets of the printed rule are the segments that are
  [−consonantal]. Among the phonemes these are the targets of the cut at the glides on the
  nasalization hierarchy of [walker-2000], the vowels, the glides and [h], where the paper's prose
  names the vowels and the two glides. Its prose restricts assimilation to a vowel before a nasal
  consonant of its own syllable; the printed rule, and `assimilation`, have no such condition, so a
  vowel is nasalized before a nasal consonant that begins a postposition. The paper's oral and
  pre-N stimuli have no such postposition.
* The paper finds harmony optional before a contrastive nasal vowel and sets that aside in its
  analysis. `surface` applies harmony, and `assimilation.apply` is the derivation in which it
  does not apply; `Covert` takes the map as an argument, and is stated of both.
* `Covert` reads no boundary, since neither rule does.
* The glide of /sɑɑ-ɑ̃ɑ̃/ 'breath-PL', which breaks hiatus, and the [x] of [ʃɑɑxɑ̃ɑ̃] 'branch-PL'
  are not derived. The stimuli are written with their glides, as the paper writes them, and
  'branch-PL' is compared with its underlying form in nasality.
* The paper states the constraint against a nasal glide, a nasal vowel and a nasal consonant
  without a boundary, and considers a restriction of underlying forms to those without a nasal
  vowel before a nasal consonant. Here the restriction is on morphemes and the constraint is
  proved of morphemes standing alone.
* The tableau of Berbice Dutch Creole is run on the transderivational correspondence of
  [benua-1997], with the forms of [dow-2014] as the paper gives them, in chart segments. The
  identity constraint counts the corresponding segments that differ in place, where the paper's
  counts the words that have one. A word without a base is evaluated by the base's copy of the
  hierarchy. As in the paper, the optionality of assimilation in [nim-tɛ] is set aside.
* Not entered: the items of the first experiment; the models of the final vowel and of the two
  postpositions in the second, and the two speakers set aside there; the suffixed and the nonce
  forms of the discussion; the comparison of [mətʃii-ʋɑɑ] 'fisherman' with 'fish-PL'; the
  Máíhɨ̃ki pattern; and the corpus counts.

## References

* [J. C. Paramore and R. Bennett, *Covert URs: Evidence from nasalization in Panjabi*
  (2026)][paramore-bennett-2026]
* [N. Chomsky and M. Halle, *The Sound Pattern of English* (1968)][chomsky-halle-1968]
* [E. Baković and L. Blumenfeld, *A formal typology of process interactions*
  (2024)][bakovic-blumenfeld-2024]
* [R. Walker, *Nasalization, Neutral Segments, and Opacity Effects* (2000)][walker-2000]
* [L. Benua, *Transderivational Identity* (1997)][benua-1997]
* [M. Dow, *Hybrid opacity in Berbice Dutch Creole* (2014)][dow-2014]
-/

@[expose] public section

namespace ParamoreBennett2026

open Function Phonology Subregular.LocalRewrite OptimalityTheory Data.PHOIBLE Data.Statistics

/-! ### The rules -/

/-- The targets of harmony, the segments that are [−consonantal]. -/
def vocoid : Segment := [−consonantal]

/-- The nasal vowels and glides. -/
def nasalVocoid : Segment := [−consonantal, +nasal]

/-- The nasal consonants. -/
def nasalConsonant : Segment := [+consonantal, +nasal]

/-- The vowels. -/
def vowel : Segment := [+syllabic, −consonantal]

section Classes

variable {s : Segment}

theorem vocoid_le_iff : vocoid ≤ s ↔ s .consonantal = false := by
  rw [vocoid, Segment.setFeature_le_iff rfl]; simp

theorem nasalVocoid_le_iff : nasalVocoid ≤ s ↔ s .consonantal = false ∧ s .nasal = true := by
  rw [nasalVocoid, Segment.setFeature_le_iff (by decide), Segment.setFeature_le_iff rfl]; simp

theorem nasalConsonant_le_iff :
    nasalConsonant ≤ s ↔ s .consonantal = true ∧ s .nasal = true := by
  rw [nasalConsonant, Segment.setFeature_le_iff (by decide), Segment.setFeature_le_iff rfl]; simp

theorem vowel_le_iff : vowel ≤ s ↔ s.IsVowel := by
  rw [vowel, Segment.setFeature_le_iff (by decide), Segment.setFeature_le_iff rfl]
  simp [Segment.IsVowel, Segment.IsSyllabic]

theorem not_vocoid_le_of_nasalConsonant_le (h : nasalConsonant ≤ s) : ¬ vocoid ≤ s := fun hv ↦
  absurd ((vocoid_le_iff.1 hv).symm.trans (nasalConsonant_le_iff.1 h).1) (by decide)

theorem vocoid_le_of_nasalVocoid_le (h : nasalVocoid ≤ s) : vocoid ≤ s :=
  vocoid_le_iff.2 (nasalVocoid_le_iff.1 h).1

end Classes

/-- (5): nasal harmony, `[−cons] → [+nas] / __ [−cons]₀ V[+nas]`: the nasal harmony that
vowels trigger, with the [−consonantal] segments as targets, scanning from the right. -/
def harmony : SearchCopy Segment := Harmony.nasalSpread (·.IsVowel) (vocoid ≤ ·) .right

/-- (5): nasal assimilation, `V → [+nas] / __ C[+nas]`. -/
def assimilation : Rule where
  target := vowel
  effect := .changeFeatures [+nasal]
  rightContext := [.seg nasalConsonant]

/-- The surface form of an underlying form: harmony, then assimilation. -/
def surface (u : List Segment) : List Segment := assimilation.apply (harmony.apply u)

-- among the phonemes the targets are those of the cut at the glides on the nasalization hierarchy
theorem isTarget_glide_iff : ∀ s ∈ Punjabi.Phonology.phonemes,
    NasalCompatibility.glide.IsTarget s ↔ vocoid ≤ s := by
  decide +kernel

-- the segments that pass nasality on are the nasal vowels and glides
theorem isNasalSource_iff {s : Segment} :
    Harmony.IsNasalSource (·.IsVowel) (vocoid ≤ ·) s ↔ nasalVocoid ≤ s := by
  rw [Harmony.IsNasalSource, vocoid_le_iff, nasalVocoid_le_iff]
  exact ⟨fun ⟨hn, h⟩ ↦ ⟨h.elim (·.2) id, hn⟩, fun ⟨hc, hn⟩ ↦ ⟨hn, .inr hc⟩⟩

theorem harmony_emit (q : Option Segment) (s : Segment) :
    harmony.emit q s =
      if vocoid ≤ s ∧ ∃ c ∈ q, nasalVocoid ≤ c then s.setFeature .nasal true else s := by
  rw [harmony, Harmony.nasalSpread_emit]
  simp only [isNasalSource_iff]

theorem harmony_apply_cons (s : Segment) (w : List Segment) :
    harmony.apply (s :: w) =
      (if vocoid ≤ s ∧ ∃ c ∈ (harmony.apply w).head?, nasalVocoid ≤ c then
        s.setFeature .nasal true else s) :: harmony.apply w := by
  rw [harmony, Harmony.nasalSpread_apply_cons]
  simp only [isNasalSource_iff]

theorem assimilation_verdict (w : List Segment) (s : Segment) (d : List Segment) :
    assimilation.verdict w s d =
      [if vowel ≤ s ∧ ∃ c ∈ d.head?, nasalConsonant ≤ c then s.setFeature .nasal true else s] := by
  have hr : MatchesRight assimilation.rightContext d ↔ ∃ c ∈ d.head?, nasalConsonant ≤ c := by
    cases d <;> simp [assimilation, MatchesRight]
  have hl : MatchesLeft assimilation.leftContext w := trivial
  simp only [Rule.verdict, hr, hl, true_and, show assimilation.target = vowel from rfl]
  split_ifs <;> simp [assimilation, Effect.apply, Segment.setFeature_bot_or]

theorem assimilation_apply_cons (s : Segment) (w : List Segment) :
    assimilation.apply (s :: w) =
      (if vowel ≤ s ∧ ∃ c ∈ w.head?, nasalConsonant ≤ c then s.setFeature .nasal true else s) ::
        assimilation.apply w := by
  rw [Rule.apply_cons_of_leftReach_eq_zero (by decide), assimilation_verdict,
    List.singleton_append]

theorem assimilation_apply_drop (n : ℕ) (u : List Segment) :
    assimilation.apply (u.drop n) = (assimilation.apply u).drop n :=
  Rule.apply_drop (by decide) (by simp [assimilation]) n u

@[simp] theorem surface_nil : surface [] = [] := by simp [surface]

theorem surface_drop (n : ℕ) (u : List Segment) : surface (u.drop n) = (surface u).drop n := by
  rw [surface, harmony.apply_drop rfl, assimilation_apply_drop, surface]

/-- A segment without its value for [nasal]. -/
abbrev denasal : Segment → Segment := Segment.restrict {.nasal}ᶜ

theorem denasal_setFeature (s : Segment) (v : Bool) :
    denasal (s.setFeature .nasal v) = denasal s :=
  Segment.restrict_eq_restrict_iff.2 fun _ hg ↦
    Segment.setFeature_apply_of_ne (by rintro rfl; simp at hg) s v

theorem apply_eq_of_denasal_eq {a b : Segment} (h : denasal a = denasal b)
    {f : Phonology.Feature} (hf : f ≠ .nasal) : a f = b f :=
  Segment.restrict_eq_restrict_iff.1 h (by simpa using hf)

-- the rules change nasality alone
theorem map_denasal_surface (u : List Segment) : (surface u).map denasal = u.map denasal := by
  rw [surface, Rule.map_apply, harmony, Harmony.map_restrict_nasalSpread]
  intro w s d
  rw [assimilation_verdict]
  split_ifs <;> simp [denasal_setFeature]

/-! ### Fixed points -/

/-- Harmony applies to a [−consonantal] segment that is not nasal before a nasal vowel or
glide. -/
def Harmonizes (a b : Segment) : Prop := vocoid ≤ a ∧ a .nasal ≠ some true ∧ nasalVocoid ≤ b

/-- Assimilation applies to a vowel that is not nasal before a nasal consonant. -/
def Assimilates (a b : Segment) : Prop := vowel ≤ a ∧ a .nasal ≠ some true ∧ nasalConsonant ≤ b

instance : DecidableRel Harmonizes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : DecidableRel Assimilates := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem ite_setFeature_eq_self_iff {s : Segment} {p : Prop} {q : Segment → Prop}
    {o : Option Segment} [Decidable (p ∧ ∃ c ∈ o, q c)] :
    (if p ∧ ∃ c ∈ o, q c then s.setFeature .nasal true else s) = s ↔
      ∀ y ∈ o, ¬ (p ∧ s .nasal ≠ some true ∧ q y) := by
  split_ifs with h
  · obtain ⟨hp, y, hy, hq⟩ := h
    rw [Segment.setFeature_eq_self_iff]
    exact ⟨fun hs z hz hz' ↦ hz'.2.1 hs, fun hs ↦ by_contra fun hn ↦ hs y hy ⟨hp, hn, hq⟩⟩
  · exact iff_of_true rfl fun y hy hy' ↦ h ⟨hy'.1, y, hy, hy'.2.2⟩

-- harmony changes a word exactly where it applies
theorem harmony_apply_eq_self_iff {w : List Segment} :
    harmony.apply w = w ↔ w.IsChain fun a b ↦ ¬ Harmonizes a b := by
  rw [harmony, Harmony.nasalSpread_apply_eq_self_iff, Edge.orient_right, List.isChain_reverse]
  refine List.IsChain.iff fun a b ↦ ?_
  simp only [isNasalSource_iff, Harmonizes]
  tauto

-- assimilation changes a word exactly where it applies
theorem assimilation_apply_eq_self_iff {w : List Segment} :
    assimilation.apply w = w ↔ w.IsChain fun a b ↦ ¬ Assimilates a b := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [assimilation_apply_cons, List.cons.injEq, List.isChain_cons, ← ih]
    exact and_congr_left fun _ ↦ ite_setFeature_eq_self_iff

-- harmony changes no word without an underlying nasal vowel or glide
theorem harmony_apply_eq_self {u : List Segment} (h : ∀ s ∈ u, ¬ nasalVocoid ≤ s) :
    harmony.apply u = u :=
  harmony_apply_eq_self_iff.2 <| List.isChain_iff_forall_rel_of_append_cons_cons.2
    fun _ b _ _ hu hab ↦ h b (by simp [hu]) hab.2.2

-- a vowel before a nasal consonant comes out of assimilation nasal
theorem getElem?_assimilation_apply {l₁ l₂ : List Segment} {a b : Segment} (ha : vowel ≤ a)
    (hb : nasalConsonant ≤ b) :
    (assimilation.apply (l₁ ++ a :: b :: l₂))[l₁.length]? = some (a.setFeature .nasal true) := by
  rw [← List.head?_drop, ← assimilation_apply_drop, List.drop_left, assimilation_apply_cons,
    ite_eq_left ⟨ha, b, rfl, hb⟩, List.head?_cons]

-- a segment in which a rule applies surfaces nasal
theorem nasal_getElem?_surface {l₁ l₂ : List Segment} {a b : Segment}
    (h : Harmonizes a b ∨ Assimilates a b) :
    ((surface (l₁ ++ a :: b :: l₂))[l₁.length]?).bind (· .nasal) = some true := by
  rw [← List.head?_drop, ← surface_drop, List.drop_left, surface, harmony_apply_cons a]
  rcases h with ⟨ha, -, hb⟩ | ⟨ha, -, hb⟩
  · have hb' : ∃ c ∈ (harmony.apply (b :: l₂)).head?, nasalVocoid ≤ c := by
      rw [harmony_apply_cons]
      refine ⟨_, rfl, ?_⟩
      split_ifs
      · exact nasalVocoid_le_iff.2 ⟨(Segment.setFeature_apply_of_ne (by decide) ..).trans
          (nasalVocoid_le_iff.1 hb).1, Segment.setFeature_apply_self ..⟩
      · exact hb
    rw [ite_eq_left ⟨ha, hb'⟩, assimilation_apply_cons]
    split_ifs <;> simp
  · have hb1 : ¬ vocoid ≤ b := not_vocoid_le_of_nasalConsonant_le hb
    have hHb : harmony.apply (b :: l₂) = b :: harmony.apply l₂ := by
      rw [harmony_apply_cons, ite_eq_right fun h ↦ hb1 h.1]
    rw [hHb, ite_eq_right (fun h ↦ by
      obtain ⟨-, c, hc, hN⟩ := h
      obtain rfl : b = c := by simpa using hc
      exact hb1 (vocoid_le_of_nasalVocoid_le hN)), assimilation_apply_cons,
      ite_eq_left ⟨ha, b, rfl, hb⟩]
    simp

-- assimilation leaves no oral vowel before a nasal consonant
theorem isChain_assimilation_apply (w : List Segment) :
    (assimilation.apply w).IsChain fun a b ↦ ¬ Assimilates a b := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [assimilation_apply_cons]
    cases w with
    | nil => simp
    | cons y l =>
      rw [assimilation_apply_cons] at ih ⊢
      refine List.IsChain.cons_cons ?_ ih
      rintro ⟨hv, hn, hc⟩
      have hy : nasalConsonant ≤ y := by
        split_ifs at hc with h
        · have h1 := (nasalConsonant_le_iff.1 hc).1
          rw [Segment.setFeature_apply_of_ne (by decide)] at h1
          exact absurd ((vowel_le_iff.1 h.1).2.symm.trans h1) (by decide)
        · exact hc
      by_cases hx : vowel ≤ x
      · rw [ite_eq_left ⟨hx, y, rfl, hy⟩] at hn
        exact hn (Segment.setFeature_apply_self ..)
      · rw [ite_eq_right fun h ↦ hx h.1] at hv
        exact hx hv

-- no surface form has an oral vowel before a nasal consonant
theorem isChain_surface (u : List Segment) : (surface u).IsChain fun a b ↦ ¬ Assimilates a b :=
  isChain_assimilation_apply _

/-- A word is its own surface form exactly when neither rule applies in it: no [−consonantal]
segment that is not nasal stands before a nasal vowel or glide, and no oral vowel before a
nasal consonant. -/
theorem surface_eq_self_iff {w : List Segment} :
    surface w = w ↔ w.IsChain fun a b ↦ ¬ (Harmonizes a b ∨ Assimilates a b) := by
  refine ⟨fun h ↦ List.isChain_iff_forall_rel_of_append_cons_cons.2 fun a b l₁ l₂ hl hab ↦ ?_,
    fun h ↦ ?_⟩
  · have hn := nasal_getElem?_surface (l₁ := l₁) (l₂ := l₂) hab
    rw [← hl, h, hl] at hn
    exact hab.elim (·.2.1) (·.2.1) (by simpa using hn)
  · simp only [not_or, List.isChain_and_iff] at h
    rw [surface, harmony_apply_eq_self_iff.2 h.1, assimilation_apply_eq_self_iff.2 h.2]

open TierStrictlyLocalGrammar in
-- the words that are their own surface forms are a strictly 2-local language
theorem isStrictlyLocal_fixedPoints : Language.IsStrictlyLocal (fixedPoints surface) 2 := by
  refine ⟨(Subregular.forbiddenPairs fun a b ↦ Harmonizes a b ∨ Assimilates a b)ᶜ,
    Set.ext fun w ↦ ?_⟩
  have h := mem_ofForbiddenPairs_language_iff (R := fun a b ↦ Harmonizes a b ∨ Assimilates a b)
    (p := fun _ ↦ True) (w := w)
  simp only [mem_language, ofForbiddenPairs, decide_true, List.filter_true] at h
  exact h.trans surface_eq_self_iff.symm

/-! ### Covert underlying forms -/

section Covert

variable {α : Type*}

/-- An underlying form is covert under the map `G` when one of its segments surfaces unaltered
in no context. -/
def Covert (G : List α → List α) (u : List α) : Prop :=
  ∃ i < u.length, ∀ pre post, (G (pre ++ u ++ post))[pre.length + i]? ≠ u[i]?

-- where the fixed points of a map are the words meeting a condition on adjacent segments, and a
-- segment that breaks the condition is changed whatever surrounds it, the covert underlying
-- forms are those the map changes
theorem covert_iff_ne_self {G : List α → List α} {R : α → α → Prop}
    (hfix : ∀ w, G w = w ↔ w.IsChain R)
    (hloc : ∀ l₁ l₂ a b, ¬ R a b → (G (l₁ ++ a :: b :: l₂))[l₁.length]? ≠ some a)
    {u : List α} : Covert G u ↔ G u ≠ u := by
  refine ⟨fun ⟨i, _, h⟩ he ↦ h [] [] (by simp [he]), fun h ↦ ?_⟩
  rw [Ne, hfix, List.isChain_iff_forall_rel_of_append_cons_cons] at h
  push Not at h
  obtain ⟨a, b, l₁, l₂, rfl, hab⟩ := h
  refine ⟨l₁.length, by simp, fun pre post he ↦ hloc (pre ++ l₁) (l₂ ++ post) a b hab ?_⟩
  simpa using he

end Covert

/-- An underlying form is covert exactly when it is not its own surface form. -/
theorem covert_surface_iff {u : List Segment} : Covert surface u ↔ surface u ≠ u :=
  covert_iff_ne_self (fun _ ↦ surface_eq_self_iff) fun l₁ l₂ a b hab he ↦ by
    have hn := nasal_getElem?_surface (l₁ := l₁) (l₂ := l₂) (not_not.1 hab)
    rw [he] at hn
    exact (not_not.1 hab).elim (·.2.1) (·.2.1) (by simpa using hn)

-- without harmony, an underlying form is covert exactly when assimilation changes it
theorem covert_assimilation_iff {u : List Segment} :
    Covert assimilation.apply u ↔ assimilation.apply u ≠ u :=
  covert_iff_ne_self (fun _ ↦ assimilation_apply_eq_self_iff) fun l₁ l₂ a b hab he ↦ by
    obtain ⟨ha, hn, hb⟩ := not_not.1 hab
    rw [getElem?_assimilation_apply ha hb, Option.some.injEq,
      Segment.setFeature_eq_self_iff] at he
    exact hn he

-- an underlying form with an oral vowel before a nasal consonant is covert, whether or not
-- harmony applies
theorem covert_of_infix {u : List Segment} {a b : Segment} (h : [a, b] <:+: u)
    (hab : Assimilates a b) : Covert surface u ∧ Covert assimilation.apply u :=
  ⟨covert_surface_iff.2 fun he ↦ List.isChain_pair.1 ((surface_eq_self_iff.1 he).infix h)
      (.inr hab),
    covert_assimilation_iff.2 fun he ↦
      List.isChain_pair.1 ((assimilation_apply_eq_self_iff.1 he).infix h) hab⟩

-- a word with a surface form of four segments differs from it in nasality alone
theorem exists_of_surface_eq {u : List Segment} {a b c d : Segment}
    (h : surface u = [a, b, c, d]) :
    ∃ a' b' c' d', u = [a', b', c', d'] ∧ denasal a' = denasal a ∧ denasal b' = denasal b ∧
      denasal c' = denasal c ∧ denasal d' = denasal d := by
  have hd := (map_denasal_surface u).symm
  rw [h] at hd
  obtain ⟨a', b', c', d', rfl⟩ : ∃ a' b' c' d', u = [a', b', c', d'] := by
    have hl := congrArg List.length hd
    simp only [List.length_map, List.length_cons, List.length_nil] at hl
    match u, hl with
    | [a', b', c', d'], _ => exact ⟨a', b', c', d', rfl⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hd
  exact ⟨a', b', c', d', rfl, hd⟩

/-! ### The derivation of (5) -/

section Panjabi

open Punjabi.Phonology (phonemes «ɑɑ» «ɑ̃ɑ̃» «ʋ» «ẽẽ» «tʃ» «kʰ» «ɳ» m)

/-- The nasalized labial semivowel [ʋ̃]. -/
def «ʋ̃» : Segment := «ʋ».setFeature .nasal true

-- (5a): harmony applies in /tʃɑɑʋẽẽ/ 'pumicestone'
theorem surface_pumicestone :
    surface [«tʃ», «ɑɑ», «ʋ», «ẽẽ»] = [«tʃ», «ɑ̃ɑ̃», «ʋ̃», «ẽẽ»] := by
  decide +kernel

-- (5b): assimilation alone applies in /ɑɑʋɑɑm/ 'general public'
theorem surface_generalPublic : surface [«ɑɑ», «ʋ», «ɑɑ», m] = [«ɑɑ», «ʋ», «ɑ̃ɑ̃», m] := by
  decide +kernel

-- (5b): assimilation feeds harmony, which would apply in the other order
theorem feeds_generalPublic :
    Feeds assimilation.apply (¬ IsFixedPt harmony.apply ·) [«ɑɑ», «ʋ», «ɑɑ», m] ∧
      harmony.apply (assimilation.apply [«ɑɑ», «ʋ», «ɑɑ», m]) = [«ɑ̃ɑ̃», «ʋ̃», «ɑ̃ɑ̃», m] := by
  decide +kernel

-- (5b): in the attested order harmony changes nothing, and would change the surface form
theorem counterfeeding_generalPublic :
    surface [«ɑɑ», «ʋ», «ɑɑ», m] = assimilation.apply [«ɑɑ», «ʋ», «ɑɑ», m] ∧
      ¬ IsFixedPt harmony.apply (surface [«ɑɑ», «ʋ», «ɑɑ», m]) :=
  feeds_generalPublic.1.underapplication

-- (5b): the two orders give different results, and the surface form is not its own surface form
theorem not_isFixedPt_surface_generalPublic :
    assimilation.apply (harmony.apply [«ɑɑ», «ʋ», «ɑɑ», m]) ≠
        harmony.apply (assimilation.apply [«ɑɑ», «ʋ», «ɑɑ», m]) ∧
      ¬ IsFixedPt surface (surface [«ɑɑ», «ʋ», «ɑɑ», m]) :=
  ⟨feeds_generalPublic.1.apply_ne_apply,
    feeds_generalPublic.1.not_isFixedPt_comp (by decide +kernel)⟩

-- /ɑɑʋɑɑm/ is covert whether or not harmony applies; /tʃɑɑʋẽẽ/ only if it applies
theorem covert_generalPublic :
    (Covert surface [«ɑɑ», «ʋ», «ɑɑ», m] ∧ Covert assimilation.apply [«ɑɑ», «ʋ», «ɑɑ», m]) ∧
      Covert surface [«tʃ», «ɑɑ», «ʋ», «ẽẽ»] ∧
      ¬ Covert assimilation.apply [«tʃ», «ɑɑ», «ʋ», «ẽẽ»] :=
  ⟨covert_of_infix (a := «ɑɑ») (b := m) ⟨[«ɑɑ», «ʋ»], [], rfl⟩ (by decide),
    covert_surface_iff.2 (by decide +kernel),
    fun h ↦ covert_assimilation_iff.1 h (by decide +kernel)⟩

-- the stem of /kʰɑɑ/ 'eat-IMP' is not covert, and its vowel is nasal in /kʰɑɑ-ɳ/ 'eating'
theorem alternation_eat :
    ¬ Covert surface [«kʰ», «ɑɑ»] ∧ surface [«kʰ», «ɑɑ», «ɳ»] = [«kʰ», «ɑ̃ɑ̃», «ɳ»] :=
  ⟨fun h ↦ covert_surface_iff.1 h (by decide +kernel), by decide +kernel⟩

-- [ɑɑʋɑ̃ɑ̃m], taken as an underlying form, undergoes harmony
theorem surface_surface_generalPublic :
    surface [«ɑɑ», «ʋ», «ɑ̃ɑ̃», m] = [«ɑ̃ɑ̃», «ʋ̃», «ɑ̃ɑ̃», m] := by
  decide +kernel

-- the phonemes that differ in nasality alone from [ɑɑ], [ʋ] and [m]
theorem eq_of_denasal_eq : ∀ x ∈ phonemes,
    (denasal x = denasal «ɑɑ» → x = «ɑɑ» ∨ x = «ɑ̃ɑ̃») ∧ (denasal x = denasal «ʋ» → x = «ʋ») ∧
      (denasal x = denasal m → x = m) := by
  decide +kernel

/-- Over the phonemes, the underlying forms of [ɑɑʋɑ̃ɑ̃m] 'general public' are /ɑɑʋɑɑm/ alone. -/
theorem surface_eq_generalPublic_iff {u : List Segment} (hu : ∀ x ∈ u, x ∈ phonemes) :
    surface u = [«ɑɑ», «ʋ», «ɑ̃ɑ̃», m] ↔ u = [«ɑɑ», «ʋ», «ɑɑ», m] := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ surface_generalPublic⟩
  obtain ⟨a, b, c, d, rfl, ha, hb, hc, hd⟩ := exists_of_surface_eq h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hu
  obtain ⟨ha', hb', hc', hd'⟩ := hu
  obtain rfl := (eq_of_denasal_eq b hb').2.1 hb
  obtain rfl := (eq_of_denasal_eq d hd').2.2 hd
  obtain rfl | rfl := (eq_of_denasal_eq a ha').1 ha <;>
    obtain rfl | rfl := (eq_of_denasal_eq c hc').1 (hc.trans (by decide))
  · rfl
  all_goals exact absurd h (by decide +kernel)

/-! ### Constraints on adjacent segments -/

/-- The morphemes: the words over the phonemes with no nasal vowel before a nasal consonant. -/
def morphemes : Set (List Segment) :=
  {u | (∀ x ∈ u, x ∈ phonemes) ∧ u.IsChain fun a b ↦ ¬ (nasalVocoid ≤ a ∧ nasalConsonant ≤ b)}

/-- The surface forms of the morphemes standing alone. -/
def citationForms : Language Segment := surface '' morphemes

/-- A nasal glide, a nasal vowel and a nasal consonant, the sequence that the constraint
`*[G̃ṼN]` bans. -/
def NasalGVN (g v c : Segment) : Prop :=
  nasalVocoid ≤ g ∧ ¬ g.IsSyllabic ∧ nasalVocoid ≤ v ∧ nasalConsonant ≤ c

instance (g v c : Segment) : Decidable (NasalGVN g v c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem isSyllabic_of_nasalVocoid_le : ∀ x ∈ phonemes, nasalVocoid ≤ x → x.IsSyllabic := by
  decide +kernel

-- the surface form of no morpheme has a nasal glide, a nasal vowel and a nasal consonant in
-- sequence
theorem not_nasalGVN_of_infix {w : List Segment} (hw : w ∈ citationForms) {g v c : Segment}
    (h : [g, v, c] <:+: w) : ¬ NasalGVN g v c := by
  obtain ⟨u, ⟨hp, hch⟩, rfl⟩ := hw
  obtain ⟨l₁, l₂, hl⟩ := h
  rintro ⟨hg, hg', -, hc⟩
  have h1 : surface (u.drop l₁.length) = g :: v :: c :: l₂ := by
    rw [surface_drop, ← hl, List.append_assoc, List.drop_left]; rfl
  have hd := (map_denasal_surface (u.drop l₁.length)).symm
  rw [h1] at hd
  obtain ⟨x, y, z, rest, hu⟩ : ∃ x y z rest, u.drop l₁.length = x :: y :: z :: rest := by
    have hl := congrArg List.length hd
    simp only [List.length_map, List.length_cons] at hl
    match u.drop l₁.length, hl with
    | x :: y :: z :: rest, _ => exact ⟨x, y, z, rest, rfl⟩
  rw [hu] at h1 hd
  simp only [List.map_cons, List.cons.injEq] at hd
  obtain ⟨hxg, -, hzc, -⟩ := hd
  have hch' : (x :: y :: z :: rest).IsChain fun a b ↦ ¬ (nasalVocoid ≤ a ∧ nasalConsonant ≤ b) :=
    hu ▸ hch.suffix (List.drop_suffix _ _)
  have hzcons : z .consonantal = true :=
    (apply_eq_of_denasal_eq hzc (by decide)).trans (nasalConsonant_le_iff.1 hc).1
  -- the consonant is unchanged, so it is nasal underlyingly
  have hz : harmony.apply (z :: rest) = z :: harmony.apply rest := by
    rw [harmony_apply_cons, ite_eq_right]
    rintro ⟨h, -⟩
    exact absurd ((vocoid_le_iff.1 h).symm.trans hzcons) (by decide)
  have h3 : surface (z :: rest) = c :: l₂ := by
    have := congrArg (List.drop 2) h1
    rwa [← surface_drop] at this
  rw [surface, hz, assimilation_apply_cons, ite_eq_right fun h ↦
    absurd ((vowel_le_iff.1 h.1).2.symm.trans hzcons) (by decide)] at h3
  obtain rfl : z = c := (List.cons.inj h3).1
  -- so the vowel before it is oral underlyingly, and triggers no harmony
  have hy : ¬ nasalVocoid ≤ y := fun h ↦
    (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch').2).1 ⟨h, hc⟩
  have hyz : harmony.apply (y :: z :: rest) = y :: z :: harmony.apply rest := by
    rw [harmony_apply_cons, hz, ite_eq_right]
    rintro ⟨-, c', hc', hN⟩
    obtain rfl : z = c' := by simpa using hc'
    exact not_vocoid_le_of_nasalConsonant_le hc (vocoid_le_of_nasalVocoid_le hN)
  have hxy : harmony.apply (x :: y :: z :: rest) = x :: y :: z :: harmony.apply rest := by
    rw [harmony_apply_cons, hyz, ite_eq_right]
    rintro ⟨-, c', hc', hN⟩
    obtain rfl : y = c' := by simpa using hc'
    exact hy hN
  have hxs : ¬ x.IsSyllabic := fun h ↦
    hg' ((apply_eq_of_denasal_eq hxg (f := .syllabic) (by decide)).symm.trans h)
  rw [surface, hxy, assimilation_apply_cons, ite_eq_right fun h ↦ hxs (vowel_le_iff.1 h.1).1] at h1
  obtain rfl : x = g := (List.cons.inj h1).1
  exact hg' (isSyllabic_of_nasalVocoid_le x
    (hp x (List.mem_of_mem_drop (hu ▸ List.mem_cons_self))) hg)

/-- The surface forms of the morphemes are not a strictly 2-local language: no grammar of
constraints on two adjacent segments generates them. -/
theorem not_isStrictlyLocal_two : ¬ citationForms.IsStrictlyLocal 2 := fun h ↦ by
  have h1 : [«ɑ̃ɑ̃», «ʋ̃», «ɑ̃ɑ̃»] ∈ citationForms :=
    ⟨[«ɑɑ», «ʋ», «ɑ̃ɑ̃»], ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel⟩
  have h2 : [«ɑɑ», «ʋ», «ɑ̃ɑ̃», m] ∈ citationForms :=
    ⟨[«ɑɑ», «ʋ», «ɑɑ», m], ⟨by decide +kernel, by decide +kernel⟩, surface_generalPublic⟩
  obtain ⟨u, ⟨hp, hch⟩, hs⟩ :=
    h.suffixSubstitutionClosed [«ɑ̃ɑ̃», «ʋ̃»] [] [«ɑɑ», «ʋ»] [m] [«ɑ̃ɑ̃»] rfl h1 h2
  obtain ⟨a, b, c, d, rfl, ha, hb, hc, hd⟩ :=
    exists_of_surface_eq (show surface u = [«ɑ̃ɑ̃», «ʋ̃», «ɑ̃ɑ̃», m] from hs)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
  obtain ⟨ha', hb', hc', hd'⟩ := hp
  obtain rfl := (eq_of_denasal_eq b hb').2.1 (hb.trans (denasal_setFeature _ _))
  obtain rfl := (eq_of_denasal_eq d hd').2.2 hd
  obtain rfl | rfl := (eq_of_denasal_eq a ha').1 (ha.trans (by decide)) <;>
    obtain rfl | rfl := (eq_of_denasal_eq c hc').1 (hc.trans (by decide))
  · exact absurd hs (by decide +kernel)
  · exact absurd hch (by decide +kernel)
  · exact absurd hs (by decide +kernel)
  · exact absurd hch (by decide +kernel)

end Panjabi

/-! ### Output–output faithfulness: Berbice Dutch Creole (7)

Place assimilation of a nasal to a following stop underapplies in [nim-tɛ] 'know-ANTERIOR', whose
cluster arises by deletion of the stem vowel of [nimi]. -/

namespace BerbiceDutch

open Transderivational
open Correspondence (diagonalPairs)

/-- The segment [n]. -/
def n : Segment := .ofChart .«n»
/-- The segment [i]. -/
def i : Segment := .ofChart .«i»
/-- The segment [m]. -/
def m : Segment := .ofChart .«m»
/-- The segment [t]. -/
def t : Segment := .ofChart .«t»
/-- The segment [ɛ]. -/
def «ɛ» : Segment := .ofChart .«ɛ»

/-- The place of articulation of a segment, its values for [labial], [coronal] and [dorsal]. -/
def place (s : Segment) : Option Bool × Option Bool × Option Bool :=
  (s .labial, s .coronal, s .dorsal)

/-- (7a): NT PLACE ASSIMILATION counts the nasal consonants before an oral stop of another
place. -/
def ntPlace : List Segment → ℕ
  | a :: b :: rest =>
    (if nasalConsonant ≤ a ∧ b .sonorant = false ∧ b .continuant = false ∧ place a ≠ place b
      then 1 else 0) + ntPlace (b :: rest)
  | _ => 0

/-- (7c): the ranking OO-IDENT-PLACE ≫ NT PLACE ASSIMILATION. -/
def ranking : List (Unit → ParadigmConstraint Segment) :=
  [ooIdentity () (Correspondence.Coindexation.identViolFeature place), markedness ntPlace]

/-- The candidates of (7c). -/
inductive Candidate
  /-- [nin-tɛ], with place assimilation. -/
  | assimilated
  /-- [nim-tɛ], without it. -/
  | unassimilated
  deriving DecidableEq, Repr

/-- (7c): the suffixed word with its base [nimi], whose final vowel has no correspondent. -/
def suffixed : Candidate → Correspondence.Coindexation Role Segment
  | .assimilated => paradigm [n, i, m, i] [n, i, m, i] [n, i, m, i, t, «ɛ»] [n, i, n, t, «ɛ»]
      (diagonalPairs 4) [(0, 0), (1, 1), (2, 2), (4, 3), (5, 4)]
  | .unassimilated => paradigm [n, i, m, i] [n, i, m, i] [n, i, m, i, t, «ɛ»] [n, i, m, t, «ɛ»]
      (diagonalPairs 4) [(0, 0), (1, 1), (2, 2), (4, 3), (5, 4)]

/-- The two strings as words without a base. -/
def simplex : Candidate → Correspondence.Coindexation Role Segment
  | .assimilated => paradigm [n, i, m, t, «ɛ»] [n, i, n, t, «ɛ»] [] [] (diagonalPairs 5) []
  | .unassimilated => paradigm [n, i, m, t, «ɛ»] [n, i, m, t, «ɛ»] [] [] (diagonalPairs 5) []

-- (7c): identity with the base keeps the nasal of [nim-tɛ] from assimilating
theorem underapplication_suffixed :
    Constraint.evalOn suffixed {.assimilated, .unassimilated} (recursive ranking ()) =
      {.unassimilated} := by
  decide +kernel

-- a word without a base is evaluated by NT PLACE ASSIMILATION alone, which assimilates
theorem assimilation_simplex :
    Constraint.evalOn simplex {.assimilated, .unassimilated} (baseRecursion ranking ()) =
      {.assimilated} := by
  rw [show ranking = [] ++ ooIdentity () (Correspondence.Coindexation.identViolFeature place) ::
    [markedness ntPlace] from rfl, evalOn_baseRecursion_ooIdentity]
  decide +kernel

end BerbiceDutch

/-! ### The forms and the stimuli -/

/-- The segment that a symbol of the paper's transcription writes: a phoneme, or the nasalized
segment of a phoneme written under a tilde. -/
def ofGlyph? (g : String) : Option Segment :=
  (Punjabi.Phonology.ofGlyph? g).or
    ((Punjabi.Phonology.ofGlyph? (String.ofList (g.toList.filter (· ≠ '\u0303')))).map
      (·.setFeature .nasal true))

/-- The underlying form of a row, a stem with its postposition. -/
def underlying? (a : Wordlist.Analysis) : Option (List Segment) :=
  (a.underlying ++ a.clitic.getD []).mapM ofGlyph?

/-- The surface form that the paper prints for a row. -/
def printed? (a : Wordlist.Analysis) : Option (List Segment) := a.form.segments.mapM ofGlyph?

-- (2c), (5a), (5b): the printed surface form is the surface form of the underlying form
theorem surface_underlying :
    ∀ a ∈ [Wordlist.pumicestone.analysis, Wordlist.generalPublic.analysis,
      Wordlist.division.analysis], ∃ u ∈ underlying? a, ∃ s ∈ printed? a, surface u = s := by
  decide +kernel

-- (2c), (2d), (5a), (5b): the nasality of each printed surface form is derived
theorem map_nasal_surface_underlying : ∀ a ∈ Wordlist.analyses, a.form.segments ≠ [] →
    ∃ u ∈ underlying? a, ∃ s ∈ printed? a, (surface u).map (· .nasal) = s.map (· .nasal) := by
  decide +kernel

/-- The values of [nasal] that the label of a condition gives the vowel, the glide and the vowel
that end a stem. -/
def nasality : Wordlist.Condition → List Bool
  | .oral => [false, false, false]
  | .preN => [false, false, true]
  | .nasalNV | .nasalCV => [true, true, true]

/-- The last three [−consonantal] segments among the first `n` of a word: the vowel, the glide
and the vowel that end a stem of `n` segments. -/
def stemEnd (n : ℕ) (w : List Segment) : List Segment :=
  ((w.take n).filter fun s : Segment ↦ decide (s .consonantal = false)).rtake 3

-- Table 3: each stimulus surfaces with the nasality that its condition names
theorem map_nasal_stemEnd : ∀ a ∈ Wordlist.analyses, ∀ c ∈ a.condition, ∃ u ∈ underlying? a,
    (stemEnd a.underlying.length (surface u)).map (· .nasal) = (nasality c).map some := by
  decide +kernel

/-- The surface form of a stimulus of the second experiment is its own surface form exactly when
the stimulus is not of the pre-N condition. -/
theorem surface_surface_iff : ∀ a ∈ Wordlist.analyses, ∀ c ∈ a.condition, ∃ u ∈ underlying? a,
    (surface (surface u) = surface u ↔ c ≠ .preN) := by
  decide +kernel

/-- A word has a nasal glide, a nasal vowel and a nasal consonant from position `i`. -/
def NasalGVNAt (w : List Segment) (i : ℕ) : Prop :=
  match w.drop i with
  | g :: v :: c :: _ => NasalGVN g v c
  | _ => False

instance (w : List Segment) (i : ℕ) : Decidable (NasalGVNAt w i) := by
  unfold NasalGVNAt; split <;> infer_instance

-- Table 3: before a postposition that begins in a nasal consonant, the glide and the vowel
-- ending the stem form that sequence with the consonant
theorem nasalGVNAt_nasalNV : ∀ a ∈ Wordlist.analyses, a.condition = some .nasalNV →
    ∃ u ∈ underlying? a, NasalGVNAt (surface u) (a.underlying.length - 2) := by
  decide +kernel

/-! ### Nasalance -/

-- Table 2: the interval for the vowel before a nasal consonant lies within the region of
-- practical equivalence of the contrastive nasal vowel
theorem equivalent_cvvn :
    -ropeMonosyllable.toRat < (vowelModel .cvvn).ciLow.toRat ∧
      (vowelModel .cvvn).ciHigh.toRat < ropeMonosyllable.toRat := by
  norm_num [vowelModel, ropeMonosyllable, Decimal.toRat]

-- Table 5: the glide before a contrastive nasal vowel is at least as nasal as that vowel, and the
-- glide of the pre-N condition lies below its region of practical equivalence
theorem glide_nasalance :
    0 < (glideModel .nasal).ciLow.toRat ∧
      (glideModel .preN).ciHigh.toRat < -ropeFinal.toRat := by
  norm_num [glideModel, ropeFinal, Decimal.toRat]

-- Table 6: the vowel before the glide lies above the region of practical equivalence of an oral
-- vowel when a contrastive nasal vowel follows; in the pre-N condition its interval reaches above
-- the region, with an estimate 0.269 below that of the nasal condition
theorem penult_nasalance :
    ropePenult.toRat < (penultModel .nasal).ciLow.toRat ∧
      ropePenult.toRat < (penultModel .preN).ciHigh.toRat ∧
      (penultModel .nasal).beta.toRat - (penultModel .preN).beta.toRat = 269 / 1000 := by
  norm_num [penultModel, ropePenult, Decimal.toRat]

end ParamoreBennett2026
