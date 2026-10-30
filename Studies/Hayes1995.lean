module

public import Linglib.Phonology.Prosody.Grid
public import Linglib.Phonology.Prosody.Foot

/-!
# Hayes (1995): Metrical Stress Theory

This file formalizes the moraic-trochee analysis of Cairene Arabic stress: the word is parsed
from left to right into moraic trochees, a heavy syllable or two lights, and End Rule Right
builds the word layer over the rightmost foot, so that a heavy syllable
[restarts the alternating count](##Hayes1995.parseCells_heavy). By the Iambic/Trochaic Law a
trochee is even in duration and an iamb's head is longer than its dependent, so
[no even iamb of two or more syllables conforms](##Hayes1995.IsEven.not_conformsToITL), a
weight-blind reading [admits trochees and no such iamb](##Hayes1995.conformsToITL_const_iff),
and [every foot of the Cairene parse conforms](##Hayes1995.parseCells_conformsToITL).

## Implementation notes

* The input is the weight profile after Consonant and Mora Extrametricality (14a–b), which
  demote a final CVC, and a final CV: of a Classical form, to light; those rules are upstream
  of the parse.

## References

* [hayes-1995]
* [hayes-1985]
* [prince-1983]
* [mccarthy-prince-1990]
-/

@[expose] public section

namespace Hayes1995

open Prosody

/-! ### The moraic-trochee parse

A heavy syllable (`2 ≤ w`, bimoraic) is its own foot, two lights make a trochee with the head
on the left, and a light with no light to pair with is left stray. Foot heads are marked as the
parse builds them; `markHeadFoot` then promotes the rightmost foot to head foot, End Rule
Right. -/

/-- Foot Construction (14c) parses a weight string from left to right into moraic trochees. -/
def parseCells : Yield → List Tree
  | [] => []
  | [w] =>
      if Syllable.Weight.heavy ≤ w then [.ft false [.σ w true]]
      else [.σ w false]
  | w :: w2 :: rest =>
      if Syllable.Weight.heavy ≤ w then
        .ft false [.σ w true] :: parseCells (w2 :: rest)
      else if Syllable.Weight.heavy ≤ w2 then
        .σ w false :: parseCells (w2 :: rest)
      else
        .ft false [.σ w true, .σ w2 false] :: parseCells rest

/-- A heavy syllable forms a foot of its own and restarts the count (Section 4.1.3, after (15)). -/
theorem parseCells_heavy {w : Syllable.Weight} (hw : Syllable.Weight.heavy ≤ w) (rest : Yield) :
    parseCells (w :: rest) = .ft false [.σ w true] :: parseCells rest := by
  cases rest <;> simp [parseCells, hw]

/-- Is this ω-daughter an `f`-level foot? -/
def isFootChild : Tree → Bool
  | .node a _ => decide (a.level = .ft)

/-- By End Rule Right (16), the first foot with no foot to its right is promoted to head foot. -/
def markHeadFoot : List Tree → List Tree
  | [] => []
  | .node a ds :: rest =>
      if a.level = .ft ∧ !rest.any isFootChild then
        .ft true ds :: rest
      else
        .node a ds :: markHeadFoot rest

/-- The Cairene parse builds a prosodic word over moraic trochees from left to right, with the
rightmost foot heading the word. -/
def parse (y : Yield) : Tree := .om (markHeadFoot (parseCells y))

/-! ### Quantity-sensitive stress

The forms are those of (12), as their post-extrametricality weight profiles (`1` light CV, `2`
heavy). `Tree.columns ∘ parse` recovers the stress: the column of `3` is the primary, `2` a
secondary, `1` unstressed. -/

/-- *kátaba* 'he wrote' (Classical) is all light. -/
def kataba : Yield := [1, 1, 1]
/-- *mudárris* 'teacher' has a heavy penult, the final CVC demoted to light. -/
def mudarris : Yield := [1, 2, 1]
/-- *ʔinkásara* 'it got broken' (Classical) has a heavy initial. -/
def Pinkasara : Yield := [2, 1, 1, 1]
/-- *katábt* 'I wrote' has a superheavy final, heavy after Consonant Extrametricality. -/
def katabt : Yield := [1, 2]
/-- *mudarrísit* 'teacher (f. construct)' has a heavy second syllable and the final CVC light. -/
def mudarrisit : Yield := [1, 2, 1, 1]
/-- *ʔadwiyatúhu* 'his drugs (nom.)' (Classical) has a heavy initial, then an even run of
lights. -/
def Padwiyatuhu : Yield := [2, 1, 1, 1, 1]
/-- *šaǰaratuhúma:* 'their (dual) tree (nom.)' (Classical) has six lights, the final long-vowel
syllable light by Mora Extrametricality. -/
def sajaratuhuma : Yield := [1, 1, 1, 1, 1, 1]

-- (12c.ii), (15d)
theorem gridColumns_kataba : Tree.columns (parse kataba) = [3, 1, 1] := by decide

-- (12b), (15b)
theorem gridColumns_mudarris : Tree.columns (parse mudarris) = [1, 3, 1] := by decide

-- (12c.ii), (15d)
theorem gridColumns_Pinkasara : Tree.columns (parse Pinkasara) = [2, 3, 1, 1] := by decide

-- (12a), (15a)
theorem gridColumns_katabt : Tree.columns (parse katabt) = [1, 3] := by decide

-- (12c.i), (15c)
theorem gridColumns_mudarrisit : Tree.columns (parse mudarrisit) = [1, 2, 3, 1] := by decide

-- (12c.i), (15c)
theorem gridColumns_Padwiyatuhu : Tree.columns (parse Padwiyatuhu) = [2, 2, 1, 3, 1] := by
  decide

-- (12c.i), (15c)
theorem gridColumns_sajaratuhuma :
    Tree.columns (parse sajaratuhuma) = [2, 1, 2, 1, 3, 1] := by decide

theorem headTerminals_kataba : Tree.headTerminals (parse kataba) = [.σ 1 true] := by decide

/-! ### The Continuous Column Constraint blocks final promotion

End Rule Right would, naively, mark the rightmost column, the stray final light of *kátaba*.
That column rests only on its syllable-layer beat: a word-layer mark over it would leave the
foot layer empty beneath, the gapped column of (17) that the Continuous Column Constraint (9)
of Section 3.4.2 rules out, so the mark falls on the rightmost foot head and the peak lands
inward. -/

theorem toGrid_kataba :
    Grid.ofTree (parse kataba) =
      [[true, true, true], [true, false, false], [true, false, false]] := by
  decide

theorem cairene_grid_continuous : Marks.IsContinuous (Grid.ofTree (parse kataba)) :=
  Grid.ofTree_isContinuous _

/-- If End Rule Right promoted the stray final light, (17), *kátaba* would have this grid, with
a word-layer mark on the final column and no foot-layer mark beneath. -/
def promotedKataba : Marks := [[true, true, true], [true, false, false], [false, false, true]]

theorem promotedKataba_not_continuous : ¬ Marks.IsContinuous promotedKataba := by decide

-- [prince-1983]
theorem kataba_final_below_peak :
    (Tree.columns (parse kataba)).getLast?.getD 0 < Grid.peak (Tree.columns (parse kataba)) := by
  decide

/-! ### The Iambic/Trochaic Law (§4.5.2)

By the Iambic/Trochaic Law ([hayes-1985]) elements contrasting in intensity group with initial
prominence and elements contrasting in duration with final prominence. On feet a trochee consists
of units even in duration (`conformsToITL_trochee_iff`), and the canonical iamb concatenates a
light syllable with a heavy one (`conformsToITL_iamb_iff`). The law is a condition on a reading
`w` of syllable duration, a constant one for syllabic counting and the mora count for moraic
counting, and not part of the definition of a foot. -/

section ITL

variable {S : Type*} (w : S → ℕ)

/-- A foot is **even** under the duration reading `w` when its syllables have equal duration. -/
def IsEven (f : Foot S) : Prop := ∀ a ∈ f.syllables, ∀ b ∈ f.syllables, w a = w b

instance (f : Foot S) : Decidable (IsEven w f) := by
  unfold IsEven; infer_instance

/-- (33): A foot **conforms to the Iambic/Trochaic Law** under the duration reading `w` when a
trochee is even and an iamb's head is longer than each of its other syllables. -/
def ConformsToITL (f : Foot S) : Prop :=
  (f.IsTrochaic → IsEven w f) ∧
    (f.IsIambic → ∀ i, i ≠ f.head → w f.syllables[i] < w f.syllables[f.head])

instance (f : Foot S) : Decidable (ConformsToITL w f) := by
  unfold ConformsToITL Foot.IsTrochaic Foot.IsIambic; infer_instance

variable {w} {a b : S} {f : Foot S}

@[simp] theorem isEven_trochee_iff : IsEven w (Foot.trochee a b) ↔ w a = w b := by
  refine ⟨fun h ↦ h a (by simp [Foot.trochee]) b (by simp [Foot.trochee]), fun h x hx y hy ↦ ?_⟩
  simp only [Foot.trochee, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [h]

@[simp] theorem isEven_iamb_iff : IsEven w (Foot.iamb a b) ↔ w a = w b :=
  isEven_trochee_iff

@[simp] theorem conformsToITL_trochee_iff : ConformsToITL w (Foot.trochee a b) ↔ w a = w b := by
  simp [ConformsToITL]

@[simp] theorem conformsToITL_iamb_iff : ConformsToITL w (Foot.iamb a b) ↔ w a < w b := by
  simp only [ConformsToITL, Foot.not_isTrochaic_iamb, Foot.isIambic_iamb, false_imp_iff,
    true_imp_iff, true_and]
  refine ⟨fun h ↦ h ⟨0, by simp [Foot.iamb]⟩ (by simp [Foot.iamb, Fin.ext_iff]), ?_⟩
  rintro h ⟨_ | _ | i, hi⟩ hne
  · exact h
  · exact absurd rfl hne
  · simp only [Foot.iamb, List.length_cons, List.length_nil] at hi; omega

@[simp] theorem conformsToITL_monosyllable : ConformsToITL w (Foot.monosyllable a) := by
  refine ⟨fun _ x hx y hy ↦ ?_, fun _ ⟨i, hi⟩ hne ↦ absurd (Fin.ext (Nat.lt_one_iff.1 hi)) hne⟩
  simp only [Foot.monosyllable, List.mem_singleton] at hx hy
  rw [hx, hy]

/-- An even iamb of two or more syllables violates the Iambic/Trochaic Law: it has final
prominence without a contrast in duration. -/
theorem IsEven.not_conformsToITL (he : IsEven w f) (hi : f.IsIambic) (hl : 1 < f.length) :
    ¬ ConformsToITL w f := by
  intro h
  have hh : f.head.val + 1 = f.syllables.length := hi
  have hl' : 1 < f.syllables.length := hl
  exact (h.2 hi ⟨0, by omega⟩ (Fin.ne_of_val_ne (by dsimp only; omega))).ne
    (he _ (by simp) _ (by simp))

/-- Under a weight-blind reading a foot conforms to the Iambic/Trochaic Law exactly when it is
not an iamb of two or more syllables: the law admits every syllabic trochee and no syllabic
iamb. -/
theorem conformsToITL_const_iff (c : ℕ) :
    ConformsToITL (fun _ ↦ c) f ↔ ¬ (f.IsIambic ∧ 1 < f.length) := by
  refine ⟨fun h ⟨hi, hl⟩ ↦ IsEven.not_conformsToITL (w := fun _ ↦ c) (fun _ _ _ _ ↦ rfl) hi hl h,
    fun h ↦ ⟨fun _ _ _ _ _ ↦ rfl, fun hi i hne ↦ absurd ⟨hi, ?_⟩ h⟩⟩
  have hne' : i.val ≠ f.head.val := fun e ↦ hne (Fin.ext e)
  have := i.isLt
  have := f.head.isLt
  unfold Foot.length
  omega

/-- A moraic trochee over syllables of positive duration, `(H)` or `(LL)`, conforms to the
Iambic/Trochaic Law. -/
theorem IsMoraicTrochee.conformsToITL (h : f.IsMoraicTrochee w)
    (hw : ∀ s ∈ f.syllables, 0 < w s) : ConformsToITL w f := by
  obtain ⟨syls, head⟩ := f
  obtain ⟨ht, hm⟩ := h
  have ht' : head.val = 0 := ht
  refine ⟨fun _ ↦ ?_, fun hi i hne ↦ absurd (Fin.ext ?_) hne⟩
  · rcases syls with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact head.elim0
    · intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rw [hx, hy]
    · simp only [Foot.moraCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero] at hm
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
    · simp only [Foot.moraCount, List.map_cons, List.sum_cons] at hm
      have := hw a (by simp)
      have := hw b (by simp)
      have := hw c (by simp)
      omega
  · have hi' : head.val + 1 = syls.length := hi
    have := i.isLt
    dsimp only at this ⊢
    omega

/-- Every foot of the Cairene parse conforms to the Iambic/Trochaic Law under moraic counting,
being a heavy syllable alone or two lights of one mora each. -/
theorem parseCells_conformsToITL : ∀ {y : Yield}, (∀ x ∈ y, 0 < x) → ∀ {t : Tree},
    t ∈ parseCells y → t.value.level = .ft →
      ∃ f : Foot Syllable.Weight, f.toProsTree id = t ∧ ConformsToITL id f
  | [], _, _, ht, _ => by simp [parseCells] at ht
  | [w], _, t, ht, hft => by
    simp only [parseCells] at ht
    split_ifs at ht
    · obtain rfl := List.mem_singleton.1 ht
      exact ⟨Foot.monosyllable w, rfl, conformsToITL_monosyllable⟩
    · obtain rfl := List.mem_singleton.1 ht
      simp at hft
  | w :: w2 :: rest, hy, t, ht, hft => by
    have hy' : ∀ x ∈ w2 :: rest, 0 < x := fun x hx ↦ hy x (List.mem_cons_of_mem _ hx)
    simp only [parseCells] at ht
    split_ifs at ht with hw hw2
    · rcases List.mem_cons.1 ht with rfl | ht
      · exact ⟨Foot.monosyllable w, rfl, conformsToITL_monosyllable⟩
      · exact parseCells_conformsToITL hy' ht hft
    · rcases List.mem_cons.1 ht with rfl | ht
      · simp at hft
      · exact parseCells_conformsToITL hy' ht hft
    · rcases List.mem_cons.1 ht with rfl | ht
      · refine ⟨Foot.trochee w w2, rfl, conformsToITL_trochee_iff.2 ?_⟩
        have light : ∀ m n : ℕ, 0 < m → 0 < n → ¬ 2 ≤ m → ¬ 2 ≤ n → m = n := by omega
        exact light w w2 (hy w (by simp)) (hy w2 (by simp)) hw hw2
      · exact parseCells_conformsToITL (fun x hx ↦ hy' x (List.mem_cons_of_mem _ hx)) ht hft

-- Under moraic counting the light–heavy iamb conforms, and the heavy–light trochee and the
-- light–light iamb do not.
example : ConformsToITL id (Foot.iamb 1 2 : Foot ℕ) := by decide
example : ¬ ConformsToITL id (Foot.trochee 2 1 : Foot ℕ) := by decide
example : ¬ ConformsToITL id (Foot.iamb 1 1 : Foot ℕ) := by decide
-- Under a constant reading the light–heavy iamb does not conform.
example : ¬ ConformsToITL (fun _ ↦ 1) (Foot.iamb 1 2 : Foot ℕ) := by decide
-- A zero-weight syllable makes a bimoraic trochee uneven, so the positivity is needed.
example : (Foot.trochee 2 0 : Foot ℕ).IsMoraicTrochee id ∧
    ¬ ConformsToITL id (Foot.trochee 2 0 : Foot ℕ) := by decide
-- The feet of the Cairene parse: *mudárris* has a heavy one, *kátaba* a light pair.
example : (parseCells mudarris).filter (fun t ↦ t.value.level = .ft) =
    [(Foot.monosyllable 2 : Foot ℕ).toProsTree id] := by decide
example : (parseCells kataba).filter (fun t ↦ t.value.level = .ft) =
    [(Foot.trochee 1 1 : Foot ℕ).toProsTree id] := by decide

end ITL

end Hayes1995
