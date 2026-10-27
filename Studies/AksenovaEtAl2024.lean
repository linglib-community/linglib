module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.Harmony.Basic
public import Linglib.Phonology.Subregular.Agree
public import Linglib.Data.Wordlist.AksenovaEtAl2024

/-!
# Aksënova, Rawski, Graf & Heinz (2024): The computational power of harmonic forms

Vowel-harmony phonotactics are tier-based strictly 2-local: project the harmonizing segments on
a tier and ban the disagreeing bigrams. Lokaa ATR harmony is strictly local at no width, since
no window bounds the transparent material between two agreeing vowels, but it is strictly
2-piecewise as well. Kirghiz, Buryat, and Yakut double harmonies each fit on a single tier,
where Buryat's blocking high vowels and Yakut's harmonizing blockers are bigram bans, and
blocking puts both beyond every strictly piecewise grammar. Kikongo's vowel and nasal harmonies
need two tiers: together they are tier-based strictly local at no width.

Each printed grammar is a `TierStrictlyLocalGrammar.ofForbiddenPairs` whose tier is the
paper's tier alphabet, checked against the forms of the examples and figures and their starred
counterparts. In the undergoer, blocker, and transparent vocabulary of the double harmonies,
which `Phonology.Harmony.Pattern` encodes, Kirghiz's and Buryat's grammars are each two
patterns sharing a tier, the chapter's condition for one tier to suffice. Yakut's harmonizing
blockers are no segment-level participation, so its rounding is no pattern beside its fronting
harmony.

## Main statements

* `lokaa_not_isStrictlyLocal`, `lokaa_language_eq_strictlyPiecewise`: Lokaa is SL at no width,
  and its TSL₂ grammar and SP₂ grammar generate one language.
* `buryat_language`, `buryat_not_isStrictlyPiecewise`: Buryat's grammar is ATR harmony and
  blocked rounding harmony on one tier, and SP at no width.
* `yakut_rounding_not_pattern`: no segment-level pattern beside fronting harmony gives Yakut.
* `kikongo_not_isTierStrictlyLocal`: no single tier carries Kikongo's two harmonies.

## Implementation notes

* A single-tier grammar's surface alphabet is `Option V` for its tier alphabet `V`, with `none`
  for everything off the tier: consonants, transparent vowels, length and tone marks. Kikongo's
  forms are read onto its two tier alphabets alone, since a segment on neither is invisible to
  both grammars, and a prenasalized stop is read as one onset off the nasal tier: with `m`
  projected, Table 34.7 would ban the paper's own `-somp-el-`, `-tomb-ol-`, and `-lemb-ol-`.
* The starred counterparts the paper prints are rows of their own, marked ungrammatical, so each
  harmony theorem accepts the forms of `Wordlist.all` and rejects those of `Wordlist.marked`.
* Table 34.5's `H_r2` prints `*üö` twice and omits `*üo`, which `H_front` bans anyway.

## References

* [aksenova-rawski-graf-heinz-2024]
* [heinz-2010]
* [rogers-pullum-2011]
* [lambert-2023]
-/

@[expose] public section

namespace AksenovaEtAl2024

open Phonology.Harmony Subregular
open Subregular.TierStrictlyLocalGrammar (mem_ofForbiddenPairs_language_iff
  mem_ofForbiddenPairs_or_language_iff ofForbiddenPairs_language_congr)

/-! ### Grammars on a tier -/

section Tier

variable {V : Type}

/-- A printed form read into the surface alphabet `Option V`, each character as its tier symbol
or as `none`. -/
def read (ofChar : Char → Option V) (cs : List Char) : List (Option V) := cs.map ofChar

/-- `R` between two tier symbols of the surface alphabet `Option V`. -/
def TierRel (R : V → V → Prop) (x y : Option V) : Prop := ∃ a ∈ x, ∃ b ∈ y, R a b

instance (R : V → V → Prop) [DecidableRel R] : DecidableRel (TierRel R) := fun _ _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The TSL₂ grammar of a printed table has the tier `V` and bans tier-adjacent `R`-related
symbols. -/
abbrev tierGrammar (R : V → V → Prop) : TierStrictlyLocalGrammar 2 (Option V) :=
  TierStrictlyLocalGrammar.ofForbiddenPairs (TierRel R) (·.isSome)

private theorem mem_tierGrammar_window (R : V → V → Prop) (a b : V) (n : ℕ) :
    [some a] ++ List.replicate n none ++ [some b] ∈ (tierGrammar R).language ↔ ¬ R a b := by
  rw [mem_ofForbiddenPairs_language_iff]
  simp [List.filter_append, TierRel]

end Tier

/-! ### Two harmonies on one tier -/

private theorem harmonic_pair {α W : Type*} (p : Pattern α W) (x y : α) :
    p.Harmonic [x, y] ↔ (p.OnTier x → p.OnTier y → p.Licit x y) := by
  by_cases hx : p.OnTier x <;> by_cases hy : p.OnTier y <;>
    simp [Pattern.Harmonic, Pattern.tier, hx, hy]

-- §34.3.1
theorem harmonic_and_iff_mem_tsl {α W W' : Type*} (p : Pattern α W) (q : Pattern α W')
    (h : ∀ s, p.OnTier s ↔ q.OnTier s) (w : List α) :
    p.Harmonic w ∧ q.Harmonic w ↔ w ∈ (TierStrictlyLocalGrammar.ofForbiddenPairs
      (fun a b ↦ ¬ p.Licit a b ∨ ¬ q.Licit a b) p.OnTier).language := by
  rw [Pattern.harmonic_iff_mem_tsl, Pattern.harmonic_iff_mem_tsl,
    mem_ofForbiddenPairs_or_language_iff,
    ofForbiddenPairs_language_congr (p := q.OnTier) (p' := p.OnTier) (fun s ↦ (h s).symm)
      fun _ _ _ _ ↦ Iff.rfl]

/-- Every tier symbol participates; everything off the tier is transparent. -/
def allParticipate {V : Type} (x : Option V) : Participation :=
  if x.isSome then .participating else .transparent

/-! ### Lokaa (Table 34.2): ATR agreement on the tier of non-high vowels -/

/-- The Lokaa tier `T = {ɛ, e, o, ə, ɔ, a}`; `eh` = ɛ, `oh` = ɔ. -/
inductive LokaaV where
  | eh | e | o | schwa | oh | a
  deriving DecidableEq, Fintype, Repr

def LokaaV.tense : LokaaV → Bool
  | .e | .o | .schwa => true
  | .eh | .oh | .a => false

/-- Akinlabi's transcription carries tone as a precomposed accent on e, o, a and as a combining
mark after ɛ, ɔ, ə. High vowels are off the tier. -/
def LokaaV.ofChar : Char → Option LokaaV
  | 'ɛ' => some .eh | 'ɔ' => some .oh | 'ə' => some .schwa
  | 'e' | 'è' | 'é' => some .e | 'o' | 'ò' | 'ó' => some .o | 'a' | 'à' | 'á' => some .a
  | _ => none

/-- `H_ATR` bans tier-adjacent vowels disagreeing in tenseness. -/
def lokaaBanned (x y : LokaaV) : Prop := x.tense ≠ y.tense

instance : DecidableRel lokaaBanned := fun _ _ ↦ by unfold lokaaBanned; infer_instance

abbrev lokaa : TierStrictlyLocalGrammar 2 (Option LokaaV) := tierGrammar lokaaBanned

-- (3)
theorem lokaa_rows :
    (∀ f ∈ Wordlist.all, f.languageId = "loka1252" →
        read LokaaV.ofChar f.form.toList ∈ lokaa.language) ∧
      ∀ f ∈ Wordlist.marked, f.languageId = "loka1252" →
        read LokaaV.ofChar f.form.toList ∉ lokaa.language := by
  decide

/-- No strictly local grammar captures Lokaa harmony (§34.2.1). -/
theorem lokaa_not_isStrictlyLocal (k : ℕ) : ¬ lokaa.language.IsStrictlyLocal k := fun h ↦
  (mem_tierGrammar_window _ _ _ _).1 (h.suffixSubstitutionClosed [some .e] [some .o] [some .eh]
    [some .oh] _ (List.length_replicate ..) ((mem_tierGrammar_window _ _ _ _).2 (by decide))
    ((mem_tierGrammar_window _ _ _ _).2 (by decide))) (by decide : lokaaBanned .e .oh)

/-- The SP₂ grammar of Table 34.1 bans two non-high vowels disagreeing in tenseness, however far
apart. -/
def lokaaSP : StrictlyPiecewiseGrammar (Option LokaaV) :=
  .ofForbiddenPairs (TierRel lokaaBanned) (·.isSome)

/-- The TSL₂ grammar of Table 34.2 and the SP₂ grammar of Table 34.1 generate one language. -/
theorem lokaa_language_eq_strictlyPiecewise : lokaa.language = lokaaSP.language 2 :=
  TierStrictlyLocalGrammar.ofForbiddenPairs_language_eq_strictlyPiecewise (by decide)

/-! ### Kirghiz ((5), Table 34.3): fronting and rounding on one tier -/

/-- The tier `T = {a, ɨ, e, i, o, ö, u, ü}` of Kirghiz and Yakut; `ih` = ɨ, `oe` = ö,
`ue` = ü. -/
inductive TurkicV where
  | a | ih | e | i | o | oe | u | ue
  deriving DecidableEq, Fintype, Repr

namespace TurkicV

def front : TurkicV → Bool
  | .e | .i | .oe | .ue => true
  | .a | .ih | .o | .u => false

def round : TurkicV → Bool
  | .o | .oe | .u | .ue => true
  | .a | .ih | .e | .i => false

def high : TurkicV → Bool
  | .ih | .i | .u | .ue => true
  | .a | .e | .o | .oe => false

def ofChar : Char → Option TurkicV
  | 'a' => some .a | 'ɨ' => some .ih | 'e' => some .e | 'i' => some .i | 'o' => some .o
  | 'ö' => some .oe | 'u' => some .u | 'ü' => some .ue | _ => none

end TurkicV

/-- `H_front ∪ H_round` bans a bigram disagreeing in fronting or in rounding. -/
def kirghizBanned (x y : TurkicV) : Prop := x.front ≠ y.front ∨ x.round ≠ y.round

instance : DecidableRel kirghizBanned := fun _ _ ↦ by unfold kirghizBanned; infer_instance

abbrev kirghiz : TierStrictlyLocalGrammar 2 (Option TurkicV) := tierGrammar kirghizBanned

-- (5), Figure 34.3
theorem kirghiz_rows :
    (∀ f ∈ Wordlist.all, f.languageId = "kirg1245" →
        read TurkicV.ofChar f.form.toList ∈ kirghiz.language) ∧
      ∀ f ∈ Wordlist.marked, f.languageId = "kirg1245" →
        read TurkicV.ofChar f.form.toList ∉ kirghiz.language := by
  decide

/-- In Kirghiz frontness harmony every vowel participates. -/
def kirghizFront : Pattern (Option TurkicV) Bool :=
  { value := Option.map TurkicV.front, participation := allParticipate }

/-- Kirghiz rounding harmony, with the same undergoers. -/
def kirghizRound : Pattern (Option TurkicV) Bool :=
  { value := Option.map TurkicV.round, participation := allParticipate }

theorem kirghiz_language :
    kirghiz.language = {w | kirghizFront.Harmonic w ∧ kirghizRound.Harmonic w} := by
  ext w
  exact (Set.ext_iff.1 (ofForbiddenPairs_language_congr (by decide) (by decide)) w).trans
    (harmonic_and_iff_mem_tsl kirghizFront kirghizRound (fun _ ↦ Iff.rfl) w).symm

theorem kirghiz_isStrictlyPiecewise : kirghiz.language.IsStrictlyPiecewise 2 :=
  TierStrictlyLocalGrammar.ofForbiddenPairs_language_isStrictlyPiecewise (by decide)

/-! ### Buryat ((9), Table 34.4): high vowels block rounding -/

/-- The Buryat tier `T = {a, e, ɔ, o, ʊ, u}` (transparent /i/ excluded); `oh` = ɔ, `uh` = ʊ. -/
inductive BuryatV where
  | a | e | oh | o | uh | u
  deriving DecidableEq, Fintype, Repr

namespace BuryatV

def tense : BuryatV → Bool
  | .e | .o | .u => true
  | .a | .oh | .uh => false

def high : BuryatV → Bool
  | .uh | .u => true
  | .a | .e | .oh | .o => false

def round : BuryatV → Bool
  | .oh | .o | .uh | .u => true
  | .a | .e => false

def ofChar : Char → Option BuryatV
  | 'a' => some .a | 'e' => some .e | 'ɔ' => some .oh | 'o' => some .o | 'ʊ' => some .uh
  | 'u' => some .u | _ => none

end BuryatV

/-- `H_ATR ∪ H_r1 ∪ H_r2` bans a bigram disagreeing in ATR, two non-high vowels disagreeing in
rounding, and a rounded non-high vowel after a high one. -/
def buryatBanned (x y : BuryatV) : Prop :=
  x.tense ≠ y.tense ∨ (¬ x.high ∧ ¬ y.high ∧ x.round ≠ y.round) ∨ (x.high ∧ ¬ y.high ∧ y.round)

instance : DecidableRel buryatBanned := fun _ _ ↦ by unfold buryatBanned; infer_instance

abbrev buryat : TierStrictlyLocalGrammar 2 (Option BuryatV) := tierGrammar buryatBanned

-- (9)
theorem buryat_rows :
    (∀ f ∈ Wordlist.all, f.languageId = "russ1264" →
        read BuryatV.ofChar f.form.toList ∈ buryat.language) ∧
      ∀ f ∈ Wordlist.marked, f.languageId = "russ1264" →
        read BuryatV.ofChar f.form.toList ∉ buryat.language := by
  decide

/-- In Buryat ATR harmony every tier vowel participates. -/
def buryatATR : Pattern (Option BuryatV) Bool :=
  { value := Option.map BuryatV.tense, participation := allParticipate }

/-- In Buryat rounding harmony high vowels are opaque, imposing unroundedness on what follows. -/
def buryatRound : Pattern (Option BuryatV) Bool :=
  { value := Option.map fun v ↦ if v.high then false else v.round
    participation := fun x ↦ match x with
      | some v => if v.high then .opaque else .participating
      | none => .transparent }

/-- The printed grammar is ATR harmony and rounding harmony with opaque high vowels, on one
tier. -/
theorem buryat_language :
    buryat.language = {w | buryatATR.Harmonic w ∧ buryatRound.Harmonic w} := by
  ext w
  exact (Set.ext_iff.1 (ofForbiddenPairs_language_congr (by decide) (by decide)) w).trans
    (harmonic_and_iff_mem_tsl buryatATR buryatRound (by decide) w).symm

/-- **Blocking is strictly piecewise at no width** (§34.2.2). Deleting the blocking causative
vowel of `ɔr-ʊːl-aːd` (9b) leaves the starred `*ɔr-aːd` of (9a). -/
theorem buryat_not_isStrictlyPiecewise (k : ℕ) : ¬ buryat.language.IsStrictlyPiecewise k :=
  fun h ↦ by
    have hmem : read BuryatV.ofChar "ɔr-ʊːl-aːd".toList ∈ buryat.language := by decide
    exact (by decide : read BuryatV.ofChar "ɔr-aːd".toList ∉ buryat.language)
      (h.isSublistClosed (by decide) hmem)

/-! ### Yakut ((14), Table 34.5): harmonizing blockers -/

/-- `H_front ∪ H_r1 ∪ H_r2 ∪ H_r3` bans a bigram disagreeing in fronting, two high vowels
disagreeing in rounding, a rounded non-high vowel after a high one, and a non-high vowel
followed by one disagreeing in rounding. -/
def yakutBanned (x y : TurkicV) : Prop :=
  x.front ≠ y.front ∨ (x.high ∧ y.high ∧ x.round ≠ y.round) ∨ (x.high ∧ ¬ y.high ∧ y.round) ∨
    (¬ x.high ∧ x.round ≠ y.round)

instance : DecidableRel yakutBanned := fun _ _ ↦ by unfold yakutBanned; infer_instance

abbrev yakut : TierStrictlyLocalGrammar 2 (Option TurkicV) := tierGrammar yakutBanned

theorem yakut_rows :
    (∀ f ∈ Wordlist.all, f.languageId = "yaku1245" →
        read TurkicV.ofChar f.form.toList ∈ yakut.language) ∧
      ∀ f ∈ Wordlist.marked, f.languageId = "yaku1245" →
        read TurkicV.ofChar f.form.toList ∉ yakut.language := by
  decide

-- §34.2.2, (14g)
theorem yakut_not_isStrictlyPiecewise (k : ℕ) : ¬ yakut.language.IsStrictlyPiecewise k :=
  fun h ↦ (by decide : [some .o, some .a] ∉ yakut.language) <|
    h.isSublistClosed (by decide) (by decide : [some .o, some .u, some .a] ∈ yakut.language)

/-- In Yakut fronting harmony every vowel participates. -/
def yakutFront : Pattern (Option TurkicV) Bool :=
  { value := Option.map TurkicV.front, participation := allParticipate }

/-- **Yakut's rounding is no segment-level pattern beside its fronting harmony**, whatever its
values, tier, blockers, icy targets, and direction. The tier bigram `u a` is licit and `a u` is
not, so read left to right `a` would have to be opaque or `u` an icy target, and either would
license `*oa` or `*uo`; read right to left the two roles swap. -/
theorem yakut_rounding_not_pattern {W : Type*} (q : Pattern (Option TurkicV) W) :
    yakut.language ≠ {w | yakutFront.Harmonic w ∧ q.Harmonic w} := fun h ↦ by
  have hmem : ∀ w, w ∈ yakut.language ↔ yakutFront.Harmonic w ∧ q.Harmonic w := fun w ↦ by
    rw [h]; rfl
  have hua := ((hmem [some .u, some .a]).1 (by decide)).2
  have hau : ¬ q.Harmonic [some .a, some .u] := fun hq ↦
    (by decide : [some .a, some .u] ∉ yakut.language) ((hmem _).2 ⟨by decide, hq⟩)
  have huo : ¬ q.Harmonic [some .u, some .o] := fun hq ↦
    (by decide : [some .u, some .o] ∉ yakut.language) ((hmem _).2 ⟨by decide, hq⟩)
  have hoa : ¬ q.Harmonic [some .o, some .a] := fun hq ↦
    (by decide : [some .o, some .a] ∉ yakut.language) ((hmem _).2 ⟨by decide, hq⟩)
  simp only [harmonic_pair, not_imp] at hua hau huo hoa
  obtain ⟨ha, hu, hau⟩ := hau
  obtain ⟨-, -, huo⟩ := huo
  obtain ⟨-, -, hoa⟩ := hoa
  have hua := hua hu ha
  rcases hq : q.direction.scanEdge with _ | _ <;>
    simp only [Pattern.Licit, hq, Pattern.Compatible, not_or] at hua hau huo hoa
  · rcases hua with h | h | h
    exacts [huo.1 h, hoa.2.1 h, hau.2.2 h.symm]
  · rcases hua with h | h | h
    exacts [hoa.1 h, huo.2.1 h, hau.2.2 h.symm]

/-! ### Kikongo ((16), (18), Tables 34.6–34.7): two disjoint tiers -/

/-- The Kikongo tier symbols are the vowels `T_v = {e, o, i, u}` and `T_n = {n, m, d, l}`. -/
inductive KikongoSeg where
  | e | o | i | u | n | m | d | l
  deriving DecidableEq, Fintype, Repr

namespace KikongoSeg

def isVowel : KikongoSeg → Bool
  | .e | .o | .i | .u => true
  | _ => false

def high : KikongoSeg → Bool
  | .i | .u => true
  | _ => false

def isNasal : KikongoSeg → Bool
  | .n | .m => true
  | _ => false

def ofChar : Char → Option KikongoSeg
  | 'e' => some .e | 'o' => some .o | 'i' => some .i | 'u' => some .u | 'n' => some .n
  | 'm' => some .m | 'd' => some .d | 'l' => some .l | _ => none

/-- A printed form read onto the two tiers, a nasal before a stop read as that stop's
prenasalized onset. -/
def parse : List Char → List KikongoSeg
  | 'm' :: 'p' :: rest | 'm' :: 'b' :: rest | 'n' :: 'g' :: rest => parse rest
  | c :: rest => (ofChar c).toList ++ parse rest
  | [] => []

end KikongoSeg

/-- The vowel tier `T_v` and the nasal tier `T_n`, which partition the symbols. -/
abbrev kikongoVowelTier (s : KikongoSeg) : Prop := s.isVowel = true
abbrev kikongoNasalTier (s : KikongoSeg) : Prop := s.isVowel = false

/-- `H_v` bans tier-adjacent vowels disagreeing in height. -/
abbrev kikongoVowel : TierStrictlyLocalGrammar 2 KikongoSeg :=
  TierStrictlyLocalGrammar.ofForbiddenPairs (fun x y ↦ x.high ≠ y.high) kikongoVowelTier

/-- `H_n` bans `d` or `l` after a nasal. -/
abbrev kikongoNasal : TierStrictlyLocalGrammar 2 KikongoSeg :=
  TierStrictlyLocalGrammar.ofForbiddenPairs (fun x y ↦ x.isNasal ∧ ¬ y.isNasal) kikongoNasalTier

/-- Kikongo phonotactics conjoins the two harmonies, each on its own tier. -/
def kikongo : Language KikongoSeg := kikongoVowel.language ⊓ kikongoNasal.language

instance : DecidablePred (· ∈ kikongo) := fun w ↦
  inferInstanceAs (Decidable (w ∈ kikongoVowel.language ∧ w ∈ kikongoNasal.language))

-- (16), (18), Figure 34.6
theorem kikongo_rows :
    (∀ f ∈ Wordlist.all, f.languageId = "koon1247" →
        KikongoSeg.parse f.form.toList ∈ kikongo) ∧
      ∀ f ∈ Wordlist.marked, f.languageId = "koon1247" →
        KikongoSeg.parse f.form.toList ∉ kikongo := by
  decide

private theorem mem_kikongo_window (x y : KikongoSeg) (hx : x.isVowel = false)
    (hy : y.isVowel = false) (n : ℕ) :
    [x] ++ List.replicate n KikongoSeg.e ++ [y] ∈ kikongo ↔ ¬ (x.isNasal ∧ ¬ y.isNasal) := by
  show _ ∈ kikongoVowel.language ∧ _ ∈ kikongoNasal.language ↔ _
  rw [mem_ofForbiddenPairs_language_iff,
    mem_ofForbiddenPairs_language_iff]
  have he : KikongoSeg.e.isVowel = true := rfl
  simp [List.filter_append, hx, hy, he, List.isChain_replicate_of_rel]

/-- No single tier carries Kikongo's two harmonies (§34.3.3), by [lambert-2023]'s method. -/
theorem kikongo_not_isTierStrictlyLocal (k : ℕ) : ¬ Language.IsTierStrictlyLocal k kikongo :=
  fun h ↦ by
    obtain ⟨T, _, hinv, hL⟩ := h.exists_tier
    have hT (a : KikongoSeg) (u v : List KikongoSeg)
        (h : ¬ (u ++ a :: v ∈ kikongo ↔ u ++ v ∈ kikongo)) : T a :=
      by_contra fun ha ↦ h (hinv u v a ha)
    have he := hT .e [.i] [] (by decide)
    have hx : (List.replicate (k - 1) KikongoSeg.e).filter (T ·) = List.replicate (k - 1) .e := by
      simp [he]
    exact (mem_kikongo_window .n .l rfl rfl (k - 1)).1
      (hL [.n] _ [.n] [.l] _ [.l] rfl (by rw [hx, List.length_replicate])
        ((mem_kikongo_window _ _ rfl rfl _).2 (by decide))
        ((mem_kikongo_window _ _ rfl rfl _).2 (by decide))) (by decide)

end AksenovaEtAl2024
