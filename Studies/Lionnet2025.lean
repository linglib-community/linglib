/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.Transduction
public import Linglib.Phonology.Tone.Register
public import Linglib.Fragments.Drubea.Prosody
public import Linglib.Fragments.Numee.Prosody
public import Studies.Hyman2006
public import Linglib.Data.Examples.Lionnet2025
import all Init.Data.List.Scan.Basic
import all Init.Data.List.Control
public import Linglib.Data.Examples.Readers

/-!
# Lionnet (2025): Tonal languages without tone

This file formalizes the word prosody of Drubea and Numèè (Oceanic, New Caledonia) as register
features alone. [Every register feature of a stem is the downstep
`l`](##Lionnet2025.stems_downstep_only), at most one per stem (`stems_culminative`), and the stem
tiers are three patterns (`stems_patterned`) whose alignment [puts the downstep of a polysyllable
on a syllable-initial mora](##Lionnet2025.associate_syllable_initial); the CVꜜV monosyllables
[make the mora the register-bearing unit](##Lionnet2025.mora_is_rbu). Postlexical docking
processes and terracing [reproduce the direction of each transcribed step between
syllables](##Lionnet2025.rows_signs), and Drubea [is tonal by Hyman's
definition](##Lionnet2025.drubea_tonal) without a stress accent (`drubea_not_stressAccent`).

## Implementation notes

* Shifts are unit steps, so the realization is ordinal: the source's half steps and the
  larger drops it transcribes after a raised syllable ((13b), (32), (62)), Rivierre's
  observation that raising rarely compensates the lowering, are not derived. The joins
  with the rows compare the sign of each step between syllables, a syllable's level being
  that of its last mora, over the tokens the source levels.
* Displacement and h-epenthesis are optional in the source; each derivation applies the
  steps its surface transcription shows. H-epenthesis targets a registerless mora before a
  downstep unless the mora's own syllable is downstepped before it, which is what keeps
  /ꜜgoo/ at the baseline in (33) and /ꜜɳii/ unraised in (12). Spreading h-epenthesis ((16))
  and the lh contour on a downstepped mora ((18), (63)) are stated on their own.
* The quantifier-free processes are relabelling transductions over the register alphabet
  (`Transduction.apply_relabel`) and depend boundedly on both sides
  (`raising_boundedDependence`); spreading h-epenthesis has no quantifier-free guard
  (`spreading_not_qf`).
* The comparison with a tonal alternative (§5) is prose and is not represented.

## References

* [lionnet-2025]
* [leben-2018]
* [hyman-2006]
* [rivierre-1973]
* [chandlee-jardine-2019]
-/

@[expose] public section

namespace Lionnet2025

open Tone Tone.Registered Subregular
open Prosody (Syllable)

/-- The weight a syllable contributes: its mora count. -/
abbrev μ : Syllable → ℕ+ := Prosody.Syllable.pnatMoraCount

/-! ### Stem patterns (§4.2, Tables 2–4) -/

/-- The three stem-level register patterns: no `l`, an `l` on the first syllable, an `l`
after a registerless syllable. -/
inductive StemPattern where
  | empty
  | l
  | emptyL
  deriving DecidableEq, Fintype

/-- A tier of registerless morae. -/
def registerless (shape : List ℕ) : RegisterTier := shape.flatMap fun n ↦ List.replicate n []

/-- The tier a pattern associates to a stem shape (Table 4): `l` on the leftmost mora of the
first syllable, or of the second syllable, or — in a monosyllable, for lack of a second
syllable — on its second mora; nothing when the shape has no mora for it. -/
def StemPattern.associate : StemPattern → List ℕ → Option RegisterTier
  | .empty, shape => some (registerless shape)
  | .l, [] => none
  | .l, n :: rest => some ([.l] :: registerless ((n - 1) :: rest))
  | .emptyL, [] => none
  | .emptyL, [n] => if 2 ≤ n then some ([] :: [.l] :: registerless [n - 2]) else none
  | .emptyL, n :: m :: rest =>
    some (registerless [n] ++ [.l] :: registerless ((m - 1) :: rest))

theorem stems_patterned :
    ∀ s ∈ Drubea.stems, ∃ p : StemPattern, p.associate (s.shape μ) = some s.tier := by
  decide

theorem numee_stems_patterned :
    ∀ s ∈ Numee.stems, ∃ p : StemPattern, p.associate (s.shape μ) = some s.tier := by
  decide

-- (54), Table 3
theorem loans_unpatterned :
    ∀ s ∈ Drubea.loans, ∀ p : StemPattern, p.associate (s.shape μ) ≠ some s.tier := by
  decide

theorem mem_registerless {shape : List ℕ} {ns : List RegisterFeature}
    (h : ns ∈ registerless shape) :
    ns = [] := by
  obtain ⟨_, -, h⟩ := List.mem_flatMap.1 h
  exact List.eq_of_mem_replicate h

theorem getElem?_registerless (shape : List ℕ) (i : ℕ) :
    (registerless shape)[i]?.getD [] = [] := by
  rcases h : (registerless shape)[i]? with _ | ns
  · rfl
  · simpa using mem_registerless (List.mem_of_getElem? h)

/-- On a stem of two or more syllables, every pattern puts its `l` on a syllable-initial mora
(§4.2). -/
theorem associate_syllable_initial (p : StemPattern) {shape : List ℕ} (h : 2 ≤ shape.length)
    {tier : RegisterTier} (ht : p.associate shape = some tier) :
    ∀ i ∈ RegisterTier.bearing .l tier, ∃ k, i = (shape.take k).sum := by
  intro i hi
  obtain ⟨hlt, hi⟩ := RegisterTier.mem_bearing.1 hi
  replace hi : RegisterFeature.l ∈ tier[i]?.getD [] := by simpa [List.getElem?_eq_getElem hlt]
  obtain ⟨n, m, rest, rfl⟩ : ∃ n m rest, shape = n :: m :: rest := by
    match shape, h with
    | n :: m :: rest, _ => exact ⟨n, m, rest, rfl⟩
  cases p with
  | empty =>
    simp only [StemPattern.associate, Option.some.injEq] at ht
    subst ht
    simp [getElem?_registerless] at hi
  | l =>
    simp only [StemPattern.associate, Option.some.injEq] at ht
    subst ht
    refine ⟨0, ?_⟩
    rcases i with _ | i
    · rfl
    · simp [getElem?_registerless] at hi
  | emptyL =>
    simp only [StemPattern.associate, Option.some.injEq] at ht
    subst ht
    suffices i = n from ⟨1, by simp [this]⟩
    have hlen : (registerless [n]).length = n := by simp [registerless]
    rcases lt_trichotomy i n with hlt | rfl | hgt
    · rw [List.getElem?_append_left (by rw [hlen]; exact hlt), getElem?_registerless] at hi
      simp at hi
    · rfl
    · rw [List.getElem?_append_right (by rw [hlen]; exact hgt.le), hlen] at hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      rw [show n + j + 1 - n = j + 1 by omega, List.getElem?_cons_succ,
        getElem?_registerless] at hi
      simp at hi

/-! ### Culminativity, downstep as the only primitive, and the register-bearing unit -/

/-- Register culminativity (§3.8, §3.10): at most one downstep per stem. -/
def IsCulminative {S : Type*} (r : Registered S) : Prop :=
  (RegisterTier.bearing .l r.tier).length ≤ 1

instance {S : Type*} (r : Registered S) : Decidable (IsCulminative r) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem stems_culminative : ∀ s ∈ Drubea.stems, IsCulminative s := by decide

theorem loans_culminative : ∀ s ∈ Drubea.loans, IsCulminative s := by decide

theorem numee_stems_culminative : ∀ s ∈ Numee.stems, IsCulminative s := by decide

/-- /koꜜo·ꜜmwa/ 'mound' ((55a)), field·house. -/
def mound : Registered Syllable := Drubea.kooPlace ++ Drubea.mwaHouse

/-- /ꜜʊʊ·ũ·pooꜜka/ 'blanket' ((55b)), mat·hair·animal. -/
def blanket : Registered Syllable := Drubea.uuMat ++ Drubea.uHair ++ Drubea.pookaAnimal

/-- /ꜜko·ꜜvuu-ɽe/ 'voice, language' ((55c)), manner·speak-ACT. -/
def voice : Registered Syllable := Drubea.koManner ++ Drubea.vuuSpeak ++ Drubea.reAct

-- (55)
theorem compounds_not_culminative :
    ¬ IsCulminative mound ∧ ¬ IsCulminative blanket ∧ ¬ IsCulminative voice := by decide

/-- Every register feature a stem bears is the downstep `l`, the only underlying primitive of the
system (§4.2, §7). A stem is a register tier over its morae with no tonal root node, so it bears
no tone feature. -/
theorem stems_downstep_only :
    ∀ s ∈ Drubea.stems ++ Numee.stems, ∀ f ∈ s.tier.flatten, f = .l := by
  decide

-- An upstep on the tier fails the condition.
example : ¬ ∀ f ∈ ([[], [.h], [.l]] : RegisterTier).flatten, f = .l := by decide

/-- The two morae of the one syllable of /beꜜe/ differ in register, so the register-bearing
unit is the mora, not the syllable (§3.7, §4.2). -/
theorem mora_is_rbu : Drubea.beeNeg.syllableFeatures μ = [[[], [.l]]] := by decide

/-! ### Hyman's typology (§6.2) -/

/-- The native stems of Drubea. -/
abbrev Stem := {s // s ∈ Drubea.stems}

/-- The downstep as a marking of morae: on each stem, the morae bearing `l`, assigned by
mora. -/
def drubea : Hyman2006.Marking Stem ℕ where
  units s := Finset.range (s.1.moraCount μ)
  marked s := (RegisterTier.bearing .l s.1.tier).toFinset
  marked_subset s i hi := by
    have h : s.1.tier.length = s.1.moraCount μ := Drubea.stems_aligned s.1 s.2
    obtain ⟨hlt, -⟩ := RegisterTier.mem_bearing.1 (List.mem_toFinset.1 hi)
    exact Finset.mem_range.2 (h ▸ hlt)
  tbu := .mora

theorem drubea_culminative : Hyman2006.Culminative drubea := fun ⟨a, ha⟩ =>
  (show ∀ a ∈ Drubea.stems, (RegisterTier.bearing .l a.tier).toFinset.card ≤ 1 by
    decide) a ha

theorem drubea_not_obligatory : ¬ Hyman2006.Obligatory drubea := fun h =>
  (h ⟨Drubea.kureForest, by decide⟩).ne_empty (by decide)

theorem drubea_not_stressAccent : ¬ Hyman2006.StressAccent drubea := fun h =>
  drubea_not_obligatory h.2.1

/-- The indication of pitch a stem carries: its tier, when a downstep is in it. -/
def pitch (s : Stem) : Option RegisterTier :=
  if RegisterTier.bearing .l s.1.tier = [] then none else some s.1.tier

/-- Tonal by Hyman's definition (3): pitch enters the lexical realization of /ꜜkuɽe/
'end'. -/
theorem drubea_tonal : Hyman2006.Tonal pitch := ⟨⟨Drubea.kureEnd, by decide⟩, by decide⟩

/-! ### The postlexical derivation

The processes act on the tier with its syllabification written in: a boundary before each
syllable's morae. -/

/-- A slot of the marked tier: a mora's register features, or a syllable boundary. -/
abbrev Slot := Option (List RegisterFeature)

/-- The tier of a word with a boundary before each syllable. -/
def marked (r : Registered Syllable) : List Slot :=
  (r.syllableFeatures μ).flatMap fun ms ↦ none :: ms.map some

/-- The tier back from a marked string. -/
def unmark (m : List Slot) : RegisterTier := m.filterMap id

theorem unmark_flatMap (L : List (List (List RegisterFeature))) :
    unmark (L.flatMap fun ms ↦ none :: ms.map some) = L.flatten := by
  induction L with
  | nil => rfl
  | cons ms L ih =>
    simp only [List.flatMap_cons, List.flatten_cons, unmark, List.filterMap_append] at ih ⊢
    rw [ih]
    congr 1
    simp

theorem unmark_marked {r : Registered Syllable} (h : r.IsAligned μ) :
    unmark (marked r) = r.tier := by
  rw [marked, unmark_flatMap, syllableFeatures, List.splitWrtComposition]
  exact List.flatten_splitWrtCompositionAux h.symm

/-- The register alphabet of the derivations: a boundary, a registerless mora, a downstep,
a double downstep, an upstep, and the `lh` contour. -/
def alphabet : List Slot :=
  [none, some [], some [.l], some [.l, .l], some [.h], some [.l, .h]]

/-- The position variable. -/
def x : Walk := .var

/-- `t` reads a syllable boundary. -/
def bar (t : Walk) : WindowFormula Slot := .label none t

/-- `t` reads a registerless mora. -/
def empty (t : Walk) : WindowFormula Slot := .label (some []) t

/-- `t` reads a mora bearing a downstep, single or double. -/
def bearsL (t : Walk) : WindowFormula Slot :=
  .disj (.label (some [.l]) t) (.label (some [.l, .l]) t)

/-- The next mora, across a boundary if there is one, bears a downstep. -/
def nextBearsL : WindowFormula Slot :=
  .disj (bearsL x.succ) (.conj (bar x.succ) (bearsL x.succ.succ))

/-- A register feature appended to a mora. -/
def append (f : RegisterFeature) : Slot → Slot := Option.map (· ++ [f])

/-- Pre-downstep h-epenthesis (§4.4): a registerless mora before a downstepped one takes `h`,
unless its own syllable is downstepped before it — one mora back, the syllables being at
most bimoraic. -/
def raisingGuard : WindowFormula Slot := .conj (empty x) (.conj nextBearsL (.neg (bearsL x.pred)))

/-- Pre-downstep h-epenthesis as a process. -/
def raising : Docking Slot := .ofQF raisingGuard (append .h)

/-- Spreading h-epenthesis ((16)): every registerless mora of the stretch before a downstep
takes `h`. The look-ahead is unbounded, so the guard is not quantifier-free. -/
def spreading : Docking Slot where
  dock := append .h
  Docks m i := m[i]? = some (some []) ∧ ∃ k < m.length, i < k ∧
    (m[k]? = some (some [.l]) ∨ m[k]? = some (some [.l, .l])) ∧
    ∀ j < k, i < j → m[j]? = some (some []) ∨ m[j]? = some none
  lt_length h := (List.getElem?_eq_some_iff.1 h.1).1
  decDocks _ _ := inferInstance

/-- Utterance-initial neutralisation (§3.5, §4.5): the first mora's downstep is left
unrealized, there being no preceding register to contrast with; the feature is not
deleted, so it still blocks h-epenthesis on its syllable. -/
def neutralizationGuard : WindowFormula Slot := .conj (bar x.pred) (WindowFormula.initial x.pred)

/-- Utterance-initial neutralisation as a process. -/
def neutralization : Docking Slot :=
  .ofQF neutralizationGuard (Option.map (·.filter (· ≠ RegisterFeature.l)))

/-- Downstep displacement, first half (§4.6): the downstep on the last mora of a bimoraic
syllable spreads to the next syllable's first mora, stacking on a downstep there. -/
def spreadLGuard : WindowFormula Slot :=
  .conj (bar x.pred) (.conj (bearsL x.pred.pred)
    (.conj (.defined x.pred.pred.pred) (.neg (bar x.pred.pred.pred))))

/-- The spreading half of displacement as a process. -/
def spreadL : Docking Slot := .ofQF spreadLGuard (append .l)

/-- Downstep displacement, second half: the spread downstep delinks from its host. -/
def delinkLGuard : WindowFormula Slot :=
  .conj (bearsL x) (.conj (.defined x.pred) (.conj (.neg (bar x.pred))
    (.conj (bar x.succ) (.defined x.succ.succ))))

/-- The delinking half of displacement as a process. -/
def delinkL : Docking Slot := .ofQF delinkLGuard (Option.map (·.erase RegisterFeature.l))

/-- The final syllable bears no register feature. -/
def finalRegisterless : WindowFormula Slot :=
  .conj (WindowFormula.final x)
    (.conj (empty x) (.disj (bar x.pred) (.conj (empty x.pred) (bar x.pred.pred))))

/-- Drubea's final raising (§3.3, §4.8): h% docks on an utterance-final registerless
syllable. -/
def finalRaising : Docking Slot := .ofQF finalRegisterless (append .h)

/-- Numèè's final lowering (§3.4, §4.8): l% docks on a light final syllable after a
registerless syllable, whether the final is registerless or downstepped. -/
def finalLoweringGuard : WindowFormula Slot :=
  .conj (WindowFormula.final x) (.conj (bar x.pred) (.conj (empty x.pred.pred)
    (.disj (bar x.pred.pred.pred) (.conj (empty x.pred.pred.pred) (bar x.pred.pred.pred.pred)))))

/-- Numèè's final lowering as a process. -/
def finalLowering : Docking Slot := .ofQF finalLoweringGuard (append .l)

/-- The surface form of a morpheme sequence under the processes its transcription shows, in
order. -/
def derive (steps : List (Docking Slot)) (ws : List (Registered Syllable)) :
    Registered Syllable :=
  ⟨(concat ws).syllables, unmark (steps.foldl (fun m D ↦ D.map m) (marked (concat ws)))⟩

/-- The baseline: level 4 of the 1-to-5 scale (§3.5). -/
def baseline : Int := 4

/-- The level each mora reaches, the utterance-initial downstep unrealized. -/
def realize (r : Registered Syllable) : List Int :=
  RegisterTier.realize baseline (unmark (neutralization.map (marked r)))

/-- The level of each syllable: that of its last mora. -/
def syllableLevels (r : Registered Syllable) (levels : List Int) : List Int :=
  (((r.shape μ).scanl (· + ·) 0).tail).map fun e ↦ levels.getD (e - 1) 0

/-! ### Locality

Every process but `spreading` is `Docking.ofQF`, so on words over the register alphabet it
is computed by a one-copy relabelling transduction, the quantifier-free logical transductions
of [chandlee-jardine-2019]. -/

theorem marked_mem_alphabet : ∀ s ∈ Drubea.stems ++ Numee.stems, ∀ a ∈ marked s, a ∈ alphabet := by
  decide

theorem raising_apply_relabel {s : Registered Syllable} (hs : s ∈ Drubea.stems ++ Numee.stems) :
    (Transduction.relabel raisingGuard (append .h) alphabet).apply (marked s) =
      raising.map (marked s) :=
  Transduction.apply_relabel (marked_mem_alphabet s hs)

theorem guards_bounded :
    raisingGuard.Bounded 1 2 ∧ neutralizationGuard.Bounded 2 0 ∧ spreadLGuard.Bounded 3 0 ∧
      delinkLGuard.Bounded 1 2 ∧ finalRegisterless.Bounded 2 1 ∧
      finalLoweringGuard.Bounded 4 1 := by
  decide

theorem raising_boundedDependence :
    BoundedDependence raising.map .left ∧ BoundedDependence raising.map .right :=
  ⟨Docking.ofQF_boundedDependence_left guards_bounded.1 _,
    Docking.ofQF_boundedDependence_right guards_bounded.1 _⟩

theorem spreading_not_qf :
    ¬ ∃ (l r : ℕ) (φ : WindowFormula Slot), φ.Bounded l r ∧
      ∀ m i, spreading.Docks m i ↔ i < m.length ∧ φ.Realize m i := by
  rintro ⟨l, r, φ, hφ, h⟩
  let m₁ : List Slot := List.replicate (r + 2) (some []) ++ [some [.l]]
  let m₂ : List Slot := List.replicate (r + 3) (some [])
  have hlen₁ : m₁.length = r + 3 := by simp [m₁]
  have hlen₂ : m₂.length = r + 3 := by simp [m₂]
  have h₁ : spreading.Docks m₁ 0 := by
    refine ⟨by simp [m₁], r + 2, by omega, by omega, ?_, ?_⟩
    · left; simp [m₁]
    · intro j hj _; left
      simp [m₁, List.getElem?_append_left, hj]
  have h₂ : ¬ spreading.Docks m₂ 0 := by
    rintro ⟨-, k, hk, -, hk', -⟩
    rw [hlen₂] at hk
    simp [m₂, hk] at hk'
  refine h₂ ((h m₂ 0).2 ⟨by omega, ?_⟩)
  refine (WindowFormula.Bounded.realize_congr (w := m₁) (w' := m₂) (n := 0) (n' := 0)
    (by omega) (by omega)
    (fun j _ ↦ ⟨Iff.rfl, fun hj ↦ by
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      simp [m₁, m₂]⟩)
    (fun j hj ↦ ⟨by rw [hlen₁, hlen₂], by
      simp [m₁, m₂, show j < r + 2 by omega,
        show j < r + 3 by omega]⟩)
    hφ).1 ((h m₁ 0).1 h₁).2

/-! ### Drubea utterances -/

open Drubea in
-- (11)
theorem ex11_levels : realize (derive [] [ni3pl, mwaPfv, niiSay, meThat]) = [4, 3, 2, 2, 1] := by
  decide

open Drubea in
-- (19)
theorem ex19_levels : realize (derive [] [taaOne, diiSmall, beeFish]) = [4, 4, 4, 4, 4, 4] := by
  decide

open Drubea in
-- (20)
theorem ex20_levels :
    realize (derive [finalRaising] [taaOne, beeFish, pwiCooked]) = [4, 4, 4, 4, 5] := by
  decide

open Drubea in
-- (30)
theorem ex30_levels :
    realize (derive [] [ko1sg, teDescr, tiiLook, reAct, kureForest]) = [4, 4, 4, 4, 4, 4, 4] := by
  decide

open Drubea in
-- (32), (33), §3.5, §4.5
theorem ex32_ex33_contrast :
    (∃ x ∈ realize (derive [raising] [gooHibbertia, mieWet]), baseline < x) ∧
      (∀ x ∈ realize (derive [raising] [gooTree, mieWet]), x ≤ baseline) ∧
      realize (derive [raising] [gooTree, mieWet]) = [4, 4, 3, 3] := by
  decide

open Drubea in
-- (32), (33), (64), (65)
theorem ex32_ex33_tiers :
    (derive [raising] [gooHibbertia, mieWet]).tier = [[], [.h], [.l], []] ∧
      (derive [raising] [gooTree, mieWet]).tier = [[.l], [], [.l], []] := by
  decide

open Drubea in
-- (53), §3.7, §4.6
theorem ex53_displacement :
    (derive [spreadL, delinkL, raising] [kooPlace, kweDance, reAct]).tier =
        [[], [.h], [.l], []] ∧
      (derive [spreadL, delinkL, raising] [kooPlace, kweEat, reAct]).tier =
        [[], [.h], [.l, .l], []] ∧
      realize (derive [spreadL, delinkL, raising] [kooPlace, kweDance, reAct]) = [4, 5, 4, 4] ∧
      realize (derive [spreadL, delinkL, raising] [kooPlace, kweEat, reAct]) = [4, 5, 3, 3] := by
  decide

open Drubea in
-- (46)
theorem ex46_undisplaced :
    (derive [raising] [ni3sg, beeNeg, ngaWork, reAct]).tier =
        [[], [.h], [.l], [], []] ∧
      realize (derive [raising] [ni3sg, beeNeg, ngaWork, reAct]) = [4, 5, 4, 4, 4] := by
  decide

/-- Register copying (§3.9, §4.7): a verbal classifier prefix takes the register features of
the verb's first mora. -/
def copyPrefix (prefix_ verb : Registered Syllable) : Registered Syllable :=
  ⟨prefix_.syllables, prefix_.tier.map fun _ ↦ verb.tier.getD 0 []⟩

open Drubea in
-- (56)
theorem ex56_copy :
    (copyPrefix taHand uruCut).tier = [[]] ∧
      (copyPrefix taHand tieTear).tier = [[.l]] := by
  decide

open Drubea in
-- (57)
theorem ex57_levels :
    realize (derive [raising] [ko1sg, teDescr, copyPrefix taHand tieTear, tieTear, reAct]) =
      [4, 5, 4, 3, 3, 3] := by
  decide

-- (16)
theorem spreading_stretch :
    spreading.map [none, some [], some [], none, some [], some [.l]] =
      [none, some [.h], some [.h], none, some [.h], some [.l]] := by
  decide

/-! ### Numèè utterances -/

open Numee in
-- (24)
theorem ex24_levels :
    (derive [finalLowering] [jaaJuice, niCoconut]).tier = [[], [], [.l]] ∧
      realize (derive [finalLowering, raising] [jaaJuice, niCoconut]) = [4, 5, 4] := by
  decide

open Numee in
-- (25), (24)
theorem ex25_double :
    (derive [finalLowering, raising] [jaaJuice, niBreast]).tier =
        [[], [.h], [.l, .l]] ∧
      realize (derive [finalLowering, raising] [jaaJuice, niBreast]) = [4, 5, 3] := by
  decide

open Numee in
-- (26)
theorem ex26_heavy_blocks :
    derive [finalLowering] [denuJaw, aRel, miiLow] = concat [denuJaw, aRel, miiLow] ∧
      realize (derive [finalLowering] [denuJaw, aRel, miiLow]) = [4, 4, 4, 4, 4] := by
  decide

open Numee in
-- (28), (29)
theorem ex28_ex29_after_downstep_blocks :
    derive [finalLowering] [teeGirl, eProx, noGrill, betiiThree, kuYam] =
        concat [teeGirl, eProx, noGrill, betiiThree, kuYam] ∧
      derive [finalLowering] [ni3sg, yuuBerth, aLoc, paaUp, kweSand] =
        concat [ni3sg, yuuBerth, aLoc, paaUp, kweSand] := by
  decide

open Numee in
-- (38)
theorem ex38_levels :
    realize (derive [finalLowering, raising] [ciibuRat, mwaPfv, kuFlee, mworoAlive]) =
      [4, 4, 5, 4, 3, 4, 3] := by
  decide

open Numee in
-- (52), §4.6
theorem ex52_double :
    (derive [spreadL, delinkL, raising] [yaaNeg, meThat, gee1plExcl, meFut, nyaiArrive]).tier =
      [[], [.h], [.l, .l], [], [.h], [.l, .l], [.h], [.l]] := by
  decide

-- (18), (63)
theorem ex18_contour :
    RegisterTier.realize baseline
        (unmark (neutralization.map
          [none, some [.l], none, some [.l, .h], none, some [.l]])) =
      [4, 4, 3] := by
  decide

/-! ### Leben's properties of downstep (§6.1)

[leben-2018]'s definitional properties, as the paper rephrases them for a system without
tones, are theorems above: the drop changes the register for what follows and affects the
whole following domain (`ex11_levels`, `ex46_undisplaced`), it is cumulative without limit
(`ex11_levels`, `terrace_append`), it is neutralised utterance-initially (`ex19_levels`,
`ex32_ex33_contrast`), and it functions contrastively, lexically (`stems_patterned` on the
minimal triplets). -/

/-! ### The rows -/

/-- The space-separated tokens of a character string. -/
def tokens : List Char → List (List Char)
  | [] => [[]]
  | ' ' :: cs => [] :: tokens cs
  | c :: cs =>
    match tokens cs with
    | t :: ts => (c :: t) :: ts
    | [] => [[c]]

/-- A pitch level in half steps, from the source's whole or half numeral. -/
def halfSteps? (cs : List Char) : Option ℕ := go cs [] where
  /-- The digits read so far, reversed. -/
  go : List Char → List Char → Option ℕ
    | [], acc => (Datum.digits? acc.reverse).map (2 * ·)
    | ['.', '5'], acc => (Datum.digits? acc.reverse).map (2 * · + 1)
    | '.' :: _, _ => none
    | c :: cs, acc => go cs (c :: acc)

/-- The levels a row transcribes, in half steps. -/
def levels? (e : Datum) : Option (List ℕ) :=
  (e.feature? "levels").bind fun s ↦ (tokens s.toList).mapM halfSteps?

/-- The direction of each step. -/
def signs (xs : List Int) : List Int := (xs.zip xs.tail).map fun p ↦ Int.sign (p.2 - p.1)

/-- The derivation of each levelled row's utterance from the fragments, under the steps its
surface transcription shows. The two transcriptions of (13) are left out: their drop within
/ꜜbeɽu/ is a half step of declination on a registerless syllable, not a register shift. -/
def derivations : List (Registered Syllable × Datum) :=
  [(derive [] [Drubea.ni3pl, Drubea.mwaPfv, Drubea.niiSay, Drubea.meThat], Examples.ex11),
    (derive [] [Drubea.taaOne, Drubea.diiSmall, Drubea.beeFish], Examples.ex19),
    (derive [finalRaising] [Drubea.taaOne, Drubea.beeFish, Drubea.pwiCooked], Examples.ex20),
    (derive [] [Drubea.ko1sg, Drubea.teDescr, Drubea.tiiLook, Drubea.reAct, Drubea.kureForest],
      Examples.ex30),
    (derive [raising] [Drubea.gooHibbertia, Drubea.mieWet], Examples.ex32),
    (derive [raising] [Drubea.gooTree, Drubea.mieWet], Examples.ex33),
    (derive [spreadL, delinkL, raising] [Drubea.kooPlace, Drubea.kweDance, Drubea.reAct],
      Examples.ex53a),
    (derive [spreadL, delinkL, raising] [Drubea.kooPlace, Drubea.kweEat, Drubea.reAct],
      Examples.ex53b),
    (derive [raising] [Drubea.ko1sg, Drubea.teDescr, copyPrefix Drubea.taHand Drubea.tieTear,
      Drubea.tieTear, Drubea.reAct], Examples.ex57),
    (derive [finalLowering, raising] [Numee.denuJaw, Numee.aRel, Numee.naUp], Examples.ex22),
    (derive [finalLowering, raising] [Numee.jaaJuice, Numee.niCoconut], Examples.ex24),
    (derive [finalLowering, raising] [Numee.jaaJuice, Numee.niBreast], Examples.ex25),
    (derive [finalLowering] [Numee.denuJaw, Numee.aRel, Numee.miiLow], Examples.ex26),
    (derive [raising] [Numee.teeGirl, Numee.eProx, Numee.noGrill, Numee.betiiThree, Numee.kuYam],
      Examples.ex28),
    (derive [finalLowering, raising] [Numee.ciibuRat, Numee.mwaPfv, Numee.kuFlee, Numee.mworoAlive],
      Examples.ex38),
    (derive [spreadL, delinkL, raising]
      [Numee.yaaNeg, Numee.meThat, Numee.gee1plExcl, Numee.meFut, Numee.nyaiArrive],
      Examples.ex52),
    (derive [raising] [Numee.gu2sg, Numee.capeRaise, Numee.panaaMast, Numee.koOn, Numee.nyuBoat,
      Numee.wiiDown, Numee.toThere], Examples.ex62)]

/-- On every levelled row it derives, the realization reproduces the direction of each step
between syllables that the source transcribes. -/
theorem rows_signs :
    ∀ d ∈ derivations, ∀ ls ∈ levels? d.2,
      (signs (syllableLevels d.1 (realize d.1))).take (ls.length - 1) =
        signs (ls.map (↑)) := by
  decide

end Lionnet2025
