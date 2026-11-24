module

public import Linglib.Data.Statistics.ParamoreBennett2026
public import Linglib.Data.Wordlist.ParamoreBennett2026
public import Linglib.Languages.Punjabi.Phonology
public import Linglib.Phonology.OptimalityTheory.Correspondence.Transderivational
public import Linglib.Phonology.RuleInteraction
public import Linglib.Phonology.SearchCopy
public import Linglib.Phonology.Subregular.LocalRewrite
public import Linglib.Phonology.Subregular.StrictlyLocal

/-!
# Paramore and Bennett (2026): Covert URs: Evidence from nasalization in Panjabi

In Pakistani Panjabi long vowels contrast in nasality, except before a nasal consonant, where
every vowel is nasal, and nasality spreads leftward from a nasal vowel through vowels and glides.
This file formalizes the analysis of that pattern by two ordered rules. Harmony gives [+nasal] to
a segment that is [−consonantal] when only such segments stand between it and a following nasal
vowel; assimilation gives [+nasal] to a vowel before a nasal consonant. Harmony applies first, so
the surface form of an underlying form `u` is `surface u = assimilation (harmony u)`, and a vowel
that assimilation nasalizes triggers no harmony. An underlying form is covert when its morpheme
surfaces unaltered in no context.

Harmony changes a word only if the word has an underlying nasal vowel or glide. No surface form
has an oral vowel before a nasal consonant, so an underlying form with one is covert. A word with
an oral vowel or glide before a nasal one is not its own surface form, so no underlying form of
it is identical to it; over the phonemes, the underlying forms of [ɑɑʋɑ̃ɑ̃m] 'general public' are
/ɑɑʋɑɑm/ alone. Among the stimuli of the paper's second experiment, the surface form taken as an
underlying form surfaces unchanged except in the pre-N condition. The surface forms of the words
without a nasal vowel before a nasal consonant have no nasal glide, nasal vowel and nasal
consonant in sequence, and no grammar of constraints on two adjacent segments generates them.

Two further cases are run. In Berbice Dutch Creole, identity to the base [nimi] keeps the nasal
of [nim-tɛ] from assimilating in place, and the same strings without a base assimilate. In
Máíhɨ̃ki, where nasality spreads rightward, [nãji] taken as an underlying form harmonizes. The
paper's forms and stimuli are read from its data, and the intervals of its nasalance models are
compared with its regions of practical equivalence.

## Implementation notes

* Harmony is a search-and-copy rule of [nevins-2010]: a [−consonantal] segment takes [+nasal]
  from the output of the segment to its right when that is a nasal vowel or glide, and every
  other segment halts its search. Scanning from the right, it applies the paper's rule
  iteratively. The two differ on a nasal glide in the input, which triggers here; the phonemes
  have none. On the chart's values the glottal fricative is [−consonantal], so it is a target
  with the vowels and glides.
* A `Phonology.Harmony.Pattern` holds tier-adjacent segments to the same value in both
  directions, so it does not state that an oral vowel or glide stands before no nasal one while a
  nasal vowel stands freely before an oral one. The surface generalizations are stated on
  adjacent segments directly.
* The paper finds harmony optional before a contrastive nasal vowel and sets that aside in its
  analysis; harmony is obligatory here.
* The glide of /sɑɑ-ɑ̃ɑ̃/ 'breath-PL', which breaks hiatus, and the [x] of [ʃɑɑxɑ̃ɑ̃] 'branch-PL'
  are not derived. The stimuli are written with their glides, as the paper writes them, and
  'branch-PL' is compared with its underlying form in nasality.
* `Covert` quantifies over the strings on either side of a morpheme and reads no boundary, since
  neither rule does.
* The lexicon of the section on phonotactics is the words over the phonemes with no nasal vowel
  before a nasal consonant, the restriction on underlying forms that the paper's discussion of
  learning considers.
* The tableau of Berbice Dutch Creole is run on the transderivational correspondence of
  [benua-1997], with the base [nimi] and the suffixed word in chart segments. Máíhɨ̃ki is stated
  with the mirror image of the Panjabi rules, not with the harmony domains of
  [cole-kisseberth-1995].
* The items of the first experiment, the model of the final vowel in the second, the two
  speakers set aside there, and the corpus counts are not entered.

## References

* [J. C. Paramore and R. Bennett, *Covert URs: Evidence from nasalization in Panjabi*
  (2026)][paramore-bennett-2026]
* [N. Chomsky and M. Halle, *The Sound Pattern of English* (1968)][chomsky-halle-1968]
* [P. Kiparsky, *Abstractness, opacity, and global rules* (1973)][kiparsky-1973]
* [E. Baković and L. Blumenfeld, *A formal typology of process interactions*
  (2024)][bakovic-blumenfeld-2024]
* [A. Nevins, *Locality in Vowel Harmony* (2010)][nevins-2010]
* [T. K. Bhatia, *Punjabi: A Cognitive-Descriptive Grammar* (1993)][bhatia-1993]
* [L. Benua, *Transderivational Identity* (1997)][benua-1997]
* [M. Dow, *Hybrid opacity in Berbice Dutch Creole* (2014)][dow-2014]
* [J. Cole and C. Kisseberth, *Nasal harmony in Optimal Domains Theory*
  (1995)][cole-kisseberth-1995]
-/

@[expose] public section

namespace ParamoreBennett2026

open Function Phonology Subregular.LocalRewrite OptimalityTheory Data.PHOIBLE Data.Statistics

/-! ### The rules -/

/-- A nasal vowel or glide: a segment that is [−consonantal, +nasal]. -/
def IsNasalVocoid (s : Segment) : Prop := s .consonantal = false ∧ s .nasal = true

instance : DecidablePred IsNasalVocoid := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A nasal consonant: a segment that is [+consonantal, +nasal]. -/
def IsNasalConsonant (s : Segment) : Prop := s .consonantal = true ∧ s .nasal = true

instance : DecidablePred IsNasalConsonant := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- (5): nasal harmony, `[−cons] → [+nas] / __ [−cons]₀ V[+nas]` when the scan starts at the
right edge. A [−consonantal] segment searches the adjacent segment on the side the scan comes
from and takes [+nasal] from a nasal vowel or glide. -/
def harmony (d : Edge) : SearchCopy Segment where
  tier _ := True
  IsTarget s := s .consonantal = false
  IsSource c _ := IsNasalVocoid c
  value s := s .nasal
  write v s := s.setFeature .nasal v
  value_write v s _ := show Function.update s.val .nasal (some v) .nasal = some v from
    Function.update_self ..
  write_value v s _ h := Segment.ext <| by
    rw [Segment.setFeature, ← show s.val .nasal = some v from h]; exact Function.update_eq_self ..
  direction := d

/-- (5): nasal assimilation, `V → [+nas] / __ C[+nas]`. -/
def assimilation : Rule where
  target := [+syllabic, −consonantal]
  effect := .changeFeatures [+nasal]
  rightContext := [.seg [+consonantal, +nasal]]

/-- The surface form of an underlying form: harmony, then assimilation. -/
def surface (u : List Segment) : List Segment := assimilation.apply ((harmony .right).apply u)

theorem harmony_emit (d : Edge) (q : Option Segment) (s : Segment) :
    (harmony d).emit q s =
      if s .consonantal = false ∧ ∃ c ∈ q, IsNasalVocoid c then s.setFeature .nasal true
      else s := by
  cases q with
  | none => simp [SearchCopy.emit, SearchCopy.copied, harmony]
  | some c =>
    by_cases hc : IsNasalVocoid c
    · simp [SearchCopy.emit, SearchCopy.copied, harmony, hc, hc.2]
    · simp [SearchCopy.emit, SearchCopy.copied, harmony, hc]

theorem harmony_apply_cons (s : Segment) (w : List Segment) :
    (harmony .right).apply (s :: w) =
      (if s .consonantal = false ∧ ∃ c ∈ ((harmony .right).apply w).head?, IsNasalVocoid c then
        s.setFeature .nasal true else s) :: (harmony .right).apply w := by
  have h : ((harmony .right).apply w).filter ((harmony .right).tier ·) = (harmony .right).apply w :=
    List.filter_eq_self.2 fun _ _ ↦ decide_eq_true trivial
  rw [(harmony .right).apply_cons rfl (fun _ _ _ ↦ Iff.rfl), harmony_emit, h]

theorem assimilation_apply_cons (s : Segment) (w : List Segment) :
    assimilation.apply (s :: w) =
      (if s.IsVowel ∧ ∃ c ∈ w.head?, IsNasalConsonant c then s.setFeature .nasal true else s) ::
        assimilation.apply w := by
  have ht : assimilation.target ≤ s ↔ s.IsVowel := by
    rw [assimilation, Segment.setFeature_le_iff (by decide), Segment.setFeature_le_iff rfl]
    simp [Segment.IsVowel, Segment.IsSyllabic]
  have hr : MatchesRight assimilation.rightContext w ↔ ∃ c ∈ w.head?, IsNasalConsonant c := by
    cases w <;> simp [assimilation, MatchesRight, IsNasalConsonant]
  have hl : MatchesLeft assimilation.leftContext [] := trivial
  rw [Rule.apply_cons_of_leftReach_eq_zero (by decide)]
  simp only [Rule.verdict, hr, hl, true_and, ht]
  split_ifs <;> simp [assimilation, Effect.apply, Segment.setFeature_bot_or]

@[simp] theorem surface_nil : surface [] = [] := by simp [surface]

/-! ### Underlying and derived nasality -/

-- harmony changes no word without an underlying nasal vowel or glide
theorem harmony_apply_eq_self {u : List Segment} (h : ∀ s ∈ u, ¬ IsNasalVocoid s) :
    (harmony .right).apply u = u := by
  induction u with
  | nil => simp
  | cons s w ih =>
    rw [harmony_apply_cons, ih fun t ht ↦ h t (List.mem_cons_of_mem _ ht), ite_eq_right]
    rintro ⟨-, c, hc, hN⟩
    exact h c (List.mem_cons_of_mem _ (List.mem_of_mem_head? hc)) hN

theorem harmony_apply_drop (n : ℕ) (u : List Segment) :
    (harmony .right).apply (u.drop n) = ((harmony .right).apply u).drop n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => cases u with
    | nil => simp
    | cons s w => rw [harmony_apply_cons, List.drop_succ_cons, List.drop_succ_cons, ih]

theorem assimilation_apply_drop (n : ℕ) (u : List Segment) :
    assimilation.apply (u.drop n) = (assimilation.apply u).drop n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => cases u with
    | nil => simp
    | cons s w => rw [assimilation_apply_cons, List.drop_succ_cons, List.drop_succ_cons, ih]

theorem surface_drop (n : ℕ) (u : List Segment) : surface (u.drop n) = (surface u).drop n := by
  rw [surface, harmony_apply_drop, assimilation_apply_drop, surface]

/-- A segment without its value for [nasal]. -/
abbrev denasal : Segment → Segment := Segment.restrict {.nasal}ᶜ

theorem denasal_setFeature (s : Segment) (v : Bool) :
    denasal (s.setFeature .nasal v) = denasal s :=
  Segment.restrict_eq_restrict_iff.2 fun _ hg ↦
    Segment.setFeature_apply_of_ne (by rintro rfl; simp at hg) s v

-- the rules change nasality alone
theorem map_denasal_surface (u : List Segment) : (surface u).map denasal = u.map denasal := by
  have hH : ∀ w : List Segment, ((harmony .right).apply w).map denasal = w.map denasal := by
    intro w
    induction w with
    | nil => simp
    | cons s w ih =>
      rw [harmony_apply_cons, List.map_cons, List.map_cons, ih]
      split_ifs <;> simp [denasal_setFeature]
  have hA : ∀ w : List Segment, (assimilation.apply w).map denasal = w.map denasal := by
    intro w
    induction w with
    | nil => simp
    | cons s w ih =>
      rw [assimilation_apply_cons, List.map_cons, List.map_cons, ih]
      split_ifs <;> simp [denasal_setFeature]
  rw [surface, hA, hH]

/-! ### Neutralization and covert underlying forms -/

/-- An oral vowel before a nasal consonant. -/
def OralVN (a b : Segment) : Prop := a.IsVowel ∧ a .nasal ≠ some true ∧ IsNasalConsonant b

instance : DecidableRel OralVN := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- no surface form has an oral vowel before a nasal consonant
theorem isChain_surface (u : List Segment) : (surface u).IsChain fun a b ↦ ¬ OralVN a b := by
  rw [surface]
  generalize (harmony .right).apply u = w
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
      have hy : IsNasalConsonant y := by
        split_ifs at hc with h
        · have h1 := hc.1
          rw [Segment.setFeature_apply_of_ne (by decide)] at h1
          exact absurd (h.1.2.symm.trans h1) (by decide)
        · exact hc
      by_cases hx : x.IsVowel
      · rw [ite_eq_left ⟨hx, y, rfl, hy⟩] at hn
        exact hn (Segment.setFeature_apply_self ..)
      · rw [ite_eq_right fun h ↦ hx h.1] at hv
        exact hx hv

/-- The exponent of the morpheme `u` standing between `pre` and `post`. -/
def exponent (pre u post : List Segment) : List Segment :=
  ((surface (pre ++ u ++ post)).drop pre.length).take u.length

/-- An underlying form is covert when its morpheme surfaces unaltered in no context. -/
def Covert (u : List Segment) : Prop := ∀ pre post, exponent pre u post ≠ u

theorem exponent_infix (pre u post : List Segment) :
    exponent pre u post <:+: surface (pre ++ u ++ post) :=
  (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-- An underlying form with an oral vowel before a nasal consonant is covert. -/
theorem covert_of_infix {u : List Segment} {a b : Segment} (h : [a, b] <:+: u)
    (hab : OralVN a b) : Covert u := fun pre post he ↦
  List.isChain_pair.1 (((isChain_surface _).infix (exponent_infix pre u post)).infix
    (he.symm ▸ h)) hab

/-- A word in which a [−consonantal] segment that is not nasal stands before a nasal vowel or
glide is not its own surface form. -/
theorem surface_ne_self {s : List Segment} {a b : Segment} (h : [a, b] <:+: s)
    (ha : a .consonantal = false) (ha' : a .nasal ≠ some true) (hb : IsNasalVocoid b) :
    surface s ≠ s := by
  obtain ⟨l₁, l₂, rfl⟩ := h
  intro he
  have h1 := congrArg (List.drop l₁.length) he
  rw [← surface_drop, List.append_assoc, List.drop_left] at h1
  have hb' (q : Prop) [Decidable q] :
      IsNasalVocoid (if q then b.setFeature .nasal true else b) := by
    split_ifs
    · exact ⟨(Segment.setFeature_apply_of_ne (by decide) ..).trans hb.1,
        Segment.setFeature_apply_self ..⟩
    · exact hb
  have h2 : (surface (a :: b :: l₂)).head?.bind (· .nasal) = some true := by
    rw [surface, harmony_apply_cons a, harmony_apply_cons b, ite_eq_left ⟨ha, _, rfl, hb' _⟩,
      assimilation_apply_cons]
    split_ifs <;> simp
  rw [show surface (a :: b :: l₂) = a :: b :: l₂ from h1] at h2
  exact ha' (by simpa using h2)

theorem apply_eq_of_denasal_eq {a b : Segment} (h : denasal a = denasal b) {f : Phonology.Feature}
    (hf : f ≠ .nasal) : a f = b f :=
  Segment.restrict_eq_restrict_iff.1 h (by simpa using hf)

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

-- an underlying form without a nasal vowel or glide undergoes assimilation alone
theorem surface_eq_assimilation {u : List Segment} (h : ∀ s ∈ u, ¬ IsNasalVocoid s) :
    surface u = assimilation.apply u := by
  rw [surface, harmony_apply_eq_self h]

-- (5b): assimilation feeds harmony, which would apply in the other order
theorem feeds_generalPublic :
    Feeds assimilation.apply (¬ IsFixedPt (harmony .right).apply ·) [«ɑɑ», «ʋ», «ɑɑ», m] ∧
      (harmony .right).apply (assimilation.apply [«ɑɑ», «ʋ», «ɑɑ», m]) =
        [«ɑ̃ɑ̃», «ʋ̃», «ɑ̃ɑ̃», m] := by
  decide +kernel

-- (5b): in the attested order harmony changes nothing, and would change the surface form
theorem counterfeeding_generalPublic :
    surface [«ɑɑ», «ʋ», «ɑɑ», m] = assimilation.apply [«ɑɑ», «ʋ», «ɑɑ», m] ∧
      ¬ IsFixedPt (harmony .right).apply (surface [«ɑɑ», «ʋ», «ɑɑ», m]) :=
  feeds_generalPublic.1.underapplication

-- /ɑɑʋɑɑm/ surfaces unaltered in no context
theorem covert_generalPublic : Covert [«ɑɑ», «ʋ», «ɑɑ», m] :=
  covert_of_infix (a := «ɑɑ») (b := m) ⟨[«ɑɑ», «ʋ»], [], rfl⟩ (by decide)

-- the stem of /kʰɑɑ/ 'eat-IMP' surfaces unaltered alone, and nasal in /kʰɑɑ-ɳ/ 'eating'
theorem alternation_eat :
    ¬ Covert [«kʰ», «ɑɑ»] ∧ exponent [] [«kʰ», «ɑɑ»] [«ɳ»] = [«kʰ», «ɑ̃ɑ̃»] :=
  ⟨fun h ↦ h [] [] (by decide +kernel), by decide +kernel⟩

-- [tʃɑ̃ɑ̃ʋ̃ẽẽ] is its own surface form, and [ɑɑʋɑ̃ɑ̃m] is not
theorem surface_surface :
    surface [«tʃ», «ɑ̃ɑ̃», «ʋ̃», «ẽẽ»] = [«tʃ», «ɑ̃ɑ̃», «ʋ̃», «ẽẽ»] ∧
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

/-- The words over the phonemes with no nasal vowel before a nasal consonant. -/
def lexicon : Set (List Segment) :=
  {u | (∀ x ∈ u, x ∈ phonemes) ∧ u.IsChain fun a b ↦ ¬ (IsNasalVocoid a ∧ IsNasalConsonant b)}

/-- The surface forms of the lexicon. -/
def attested : Language Segment := surface '' lexicon

theorem isSyllabic_of_isNasalVocoid : ∀ x ∈ phonemes, IsNasalVocoid x → x.IsSyllabic := by
  decide +kernel

-- no surface form of the lexicon has a nasal glide, a nasal vowel and a nasal consonant in sequence
theorem not_infix_attested {w : List Segment} (hw : w ∈ attested) {g v c : Segment}
    (h : [g, v, c] <:+: w) :
    ¬ (IsNasalVocoid g ∧ ¬ g.IsSyllabic ∧ IsNasalVocoid v ∧ IsNasalConsonant c) := by
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
  have hch' : (x :: y :: z :: rest).IsChain fun a b ↦ ¬ (IsNasalVocoid a ∧ IsNasalConsonant b) :=
    hu ▸ hch.suffix (List.drop_suffix _ _)
  have hzcons : z .consonantal = true :=
    (apply_eq_of_denasal_eq hzc (by decide)).trans hc.1
  -- the consonant is unchanged, so it is nasal underlyingly
  have hz : (harmony .right).apply (z :: rest) = z :: (harmony .right).apply rest := by
    rw [harmony_apply_cons, ite_eq_right]
    rintro ⟨h, -⟩
    exact absurd (h.symm.trans hzcons) (by decide)
  have h3 : surface (z :: rest) = c :: l₂ := by
    have := congrArg (List.drop 2) h1
    rwa [← surface_drop] at this
  rw [surface, hz, assimilation_apply_cons, ite_eq_right fun h ↦
    absurd (h.1.2.symm.trans hzcons) (by decide)] at h3
  obtain rfl : z = c := (List.cons.inj h3).1
  -- so the vowel before it is oral underlyingly, and triggers no harmony
  have hy : ¬ IsNasalVocoid y := fun h ↦
    (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch').2).1 ⟨h, hc⟩
  have hyz : (harmony .right).apply (y :: z :: rest) = y :: z :: (harmony .right).apply rest := by
    rw [harmony_apply_cons, hz, ite_eq_right]
    rintro ⟨-, c', hc', hN⟩
    obtain rfl : z = c' := by simpa using hc'
    exact absurd (hN.1.symm.trans hzcons) (by decide)
  have hxy : (harmony .right).apply (x :: y :: z :: rest) =
      x :: y :: z :: (harmony .right).apply rest := by
    rw [harmony_apply_cons, hyz, ite_eq_right]
    rintro ⟨-, c', hc', hN⟩
    obtain rfl : y = c' := by simpa using hc'
    exact hy hN
  have hxs : ¬ x.IsSyllabic := fun h ↦
    hg' ((apply_eq_of_denasal_eq hxg (f := .syllabic) (by decide)).symm.trans h)
  rw [surface, hxy, assimilation_apply_cons, ite_eq_right fun h ↦ hxs h.1.1] at h1
  obtain rfl : x = g := (List.cons.inj h1).1
  exact hg' (isSyllabic_of_isNasalVocoid x
    (hp x (List.mem_of_mem_drop (hu ▸ List.mem_cons_self))) hg)

/-- No grammar of constraints on two adjacent segments generates the surface forms of the
lexicon. -/
theorem not_isStrictlyLocal_two : ¬ attested.IsStrictlyLocal 2 := fun h ↦ by
  have h1 : [«ɑ̃ɑ̃», «ʋ̃», «ɑ̃ɑ̃»] ∈ attested :=
    ⟨[«ɑɑ», «ʋ», «ɑ̃ɑ̃»], ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel⟩
  have h2 : [«ɑɑ», «ʋ», «ɑ̃ɑ̃», m] ∈ attested :=
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
    (if IsNasalConsonant a ∧ b .sonorant = false ∧ b .continuant = false ∧ place a ≠ place b
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

/-! ### Máíhɨ̃ki (8)

Nasality spreads rightward from a nasal vowel, and a vowel after a nasal consonant is nasal
without spreading. -/

namespace Maihiki

/-- The segment [s]. -/
def s : Segment := .ofChart .«s»
/-- The segment [e]. -/
def e : Segment := .ofChart .«e»
/-- The segment [ẽ]. -/
def «ẽ» : Segment := .ofChart .«ẽ»
/-- The segment [j]. -/
def j : Segment := .ofChart .«j»
/-- The segment [n]. -/
def n : Segment := .ofChart .«n»
/-- The segment [a]. -/
def a : Segment := .ofChart .«a»
/-- The segment [ã]. -/
def «ã» : Segment := .ofChart .«ã»
/-- The segment [i]. -/
def i : Segment := .ofChart .«i»
/-- The segment [ĩ]. -/
def «ĩ» : Segment := .ofChart .«ĩ»

/-- Nasalization of a vowel after a nasal consonant, `V → [+nas] / C[+nas] __`. -/
def postNasal : Rule where
  target := [+syllabic, −consonantal]
  effect := .changeFeatures [+nasal]
  leftContext := [.seg [+consonantal, +nasal]]

/-- The surface form of an underlying form: rightward harmony, then nasalization after a nasal
consonant. -/
def surface (u : List Segment) : List Segment := postNasal.apply ((harmony .left).apply u)

-- (8a): /sẽje/ 'species of bird' harmonizes
theorem surface_bird : surface [s, «ẽ», j, e] = [s, «ẽ», j.setFeature .nasal true, «ẽ»] := by
  decide +kernel

-- (8b): /naji/ 'grandson' is nasalized after the nasal alone, and [nãji] as an underlying form
-- harmonizes
theorem surface_grandson :
    surface [n, a, j, i] = [n, «ã», j, i] ∧
      surface [n, «ã», j, i] = [n, «ã», j.setFeature .nasal true, «ĩ»] := by
  decide +kernel

end Maihiki

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
-- vowel when a contrastive nasal vowel follows, and below that interval in the pre-N condition
theorem penult_nasalance :
    ropePenult.toRat < (penultModel .nasal).ciLow.toRat ∧
      (penultModel .preN).ciHigh.toRat < (penultModel .nasal).ciLow.toRat := by
  norm_num [penultModel, ropePenult, Decimal.toRat]

end ParamoreBennett2026
