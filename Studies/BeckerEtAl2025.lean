module

public import Linglib.Phonology.Prosody.Grid
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Becker et al. (2025): The incoherent stress of Kuikuro

Becker, Franchetto, Kuikuro, Kuikuro and Petrović analyze Kuikuro prosody with two
optimality-theoretic grammars. Words are footed into iambs from left to right with a final
trochee under *V:]φ ≫ Max-μ ≫ Parse-σ ≫ Iamb, and the last foot heads the word. The High tone of
a phrase is realized in a domain chosen by Align-L(Δφ,H), NonFin(H) and Culminativity-H over
Align-R(H), and `tone_optimal` derives the paper's generalization from these
constraints: the domain runs from the primary stress up to the next foot head, so the High
target can fall up to three syllables after the stress it marks.

## Implementation notes

* A σ-leaf's weight is its mora count. Max-μ compares input and output weights syllable by
  syllable, since no candidate of Tables 2, 4 and 6 adds or deletes a syllable.
* A tone domain is a nonempty interval of syllable positions over a fixed metrical tree.
* Table 14 gives its winner two Align-R(H) marks, one per syllable after the domain, where (5)
  counts three moras. The winner is the same under either count.
* Culminativity-H follows (7), which marks more than one foot head. The prose after Table 14
  marks domains without exactly one, which differs only on domains missing the phrase head, and
  Align-L(Δφ,H) already excludes those.

## TODO

Lexical tone (§5), initial-vowel unparsing (§4.3) as a constraint rather than a parse built into
the tree of Fig. 3, the shortening of lexical long vowels outside the head word (§4.4), and word
minimality (§3.5).

## References

* [becker-etal-2025]
* [gordon-2016]
* [liberman-prince-1977]
* [prince-smolensky-1993]
-/

@[expose] public section

namespace BeckerEtAl2025

open Prosody OptimalityTheory

/-! ### Footing -/

/-- Iamb, constraint (2), assigns one mark to every foot that is not right-headed. -/
def iamb : Constraint Tree := fun t ↦
  t.localTrees.countP fun x ↦ decide (x.1.level = .ft) && !(x.2.getLast?.any (·.isHead))

/-- *V:]φ, constraint (3), assigns one mark to a long vowel in the phrase-final syllable. -/
def finalLong : Constraint Tree :=
  Constraint.binary fun t ↦ 2 ≤ (t.leafList.getLast?.bind (·.weight?)).getD 0

/-- Max-μ assigns one mark to every input mora missing from the output. -/
def maxMora (input : List ℕ) : Constraint Tree := fun t ↦
  (List.zipWith (· - ·) input (t.leafList.filterMap (·.weight?))).sum

/-- The footing ranking *V:]φ ≫ Max-μ ≫ Parse-σ ≫ Iamb of Tables 2, 4 and 6, where Parse-σ,
    constraint (1), marks every syllable no foot dominates. -/
def footing (input : List ℕ) : List (Constraint Tree) :=
  [finalLong, maxMora input, parseInto .ft, iamb]

/-- Trochaic reversal `(σˌσː)(ˈσσ)` is the optimal footing of `/σσσσ/` (Table 2), since two
    iambs `(σˌσː)(σˈσː)` end in a long vowel and an iamb with two strays `(σˈσː)σσ` leaves two
    syllables unparsed. -/
theorem table2 :
    (Tableau.ofList
      {.om [.ft false [.σ 1, .σ 2 true], .ft true [.σ 1, .σ 2 true]],
       .om [.ft true [.σ 1, .σ 2 true], .σ 1, .σ 1],
       .om [.ft false [.σ 1, .σ 2 true], .ft true [.σ 1 true, .σ 1]]}
      (footing [1, 1, 1, 1])).optimal =
      {.om [.ft false [.σ 1, .σ 2 true], .ft true [.σ 1 true, .σ 1]]} := by
  decide

/-- The lexical long vowel of `/σσσːσ/` heads a monosyllabic foot in the optimal `(σˌσː)(ˈσː)σ`
    (Table 4), since shortening it into a trochee violates Max-μ and an iamb around it leaves
    two strays. -/
theorem table4 :
    (Tableau.ofList
      {.om [.ft false [.σ 1, .σ 2 true], .ft true [.σ 1 true, .σ 1]],
       .om [.σ 1, .ft true [.σ 1, .σ 2 true], .σ 1],
       .om [.ft false [.σ 1, .σ 2 true], .ft true [.σ 2 true], .σ 1]}
      (footing [1, 1, 2, 1])).optimal =
      {.om [.ft false [.σ 1, .σ 2 true], .ft true [.σ 2 true], .σ 1]} := by
  decide

/-- A lexical long vowel shortens phrase-finally (Table 6), so `/σσː/` surfaces as the trochee
    `(ˈσσ)` because *V:]φ dominates Max-μ. -/
theorem table6 :
    (Tableau.ofList {.om [.ft true [.σ 1, .σ 2 true]], .om [.ft true [.σ 1 true, .σ 1]]}
      (footing [1, 2])).optimal = {.om [.ft true [.σ 1 true, .σ 1]]} := by
  decide

/-! ### Words in isolation -/

/-- *[(alaː)(makíː)lɨ]* 's/he fell' (Fig. 1) has two iambs and a stray final syllable, and the
    second iamb heads the word. -/
def fell : Tree :=
  .om [.ft false [.σ 1, .σ 2 true], .ft true [.σ 1, .σ 2 true], .σ 1]

/-- *[(tsihaː)(lamaː)(kílɨ)]* 'we fell' (Fig. 2) has an even number of syllables, so its last two
    form a trochee, which heads the word. -/
def weFell : Tree :=
  .om [.ft false [.σ 1, .σ 2 true], .ft false [.σ 1, .σ 2 true], .ft true [.σ 1 true, .σ 1]]

/-- *[(umíː)ŋi]* 'annatto' (§1) is an iamb and a stray final syllable. -/
def annatto : Tree :=
  .om [.ft true [.σ 1, .σ 2 true], .σ 1]

/-- The grid puts secondary stress on every foot head and primary stress on the head of the head
    foot ([liberman-prince-1977]). -/
theorem columns_words :
    Tree.columns fell = [1, 2, 1, 3, 1] ∧ Tree.columns weFell = [1, 2, 1, 2, 3, 1] ∧
      Tree.columns annatto = [1, 3, 1] := by
  decide

/-- The primary stress of each word, the head of its head foot (p. 2365), is its unique head
    terminal, the long *kíː*, the trochee-initial *kí* and the long *míː*. -/
theorem headTerminals_words :
    Tree.headTerminals fell = [.σ 2 true] ∧ Tree.headTerminals weFell = [.σ 1 true] ∧
      Tree.headTerminals annatto = [.σ 2 true] := by
  decide

/-! ### Tone domains -/

section ToneDomain

variable (t : Tree)

/-- The mora count of the `i`th syllable. -/
def moras (i : ℕ) : ℕ := ((Tree.terminals t)[i]?.bind (·.value.weight?)).getD 0

/-- A syllable is stressed when it heads a foot (p. 2365), its grid column rising above the
    bottom row. -/
def Stressed (i : ℕ) : Prop := 2 ≤ (Tree.columns t).getD i 0

instance : DecidablePred (Stressed t) := fun _ ↦ inferInstanceAs (Decidable (2 ≤ _))

/-- The phrase head Δφ, the primary stress of the phrase, is the position of the head
    terminal. -/
def head : ℕ := (Tree.project t).findIdx (·.onSpine)

/-- The tone-domain candidates are the nonempty intervals of syllable positions. -/
def domains : Finset (NonemptyInterval ℕ) :=
  (Finset.range (Tree.columns t).length ×ˢ Finset.range (Tree.columns t).length).filterMap
    (fun x ↦ if h : x.1 ≤ x.2 then some ⟨x, h⟩ else none) fun x y d hx hy ↦ by
      by_cases hx' : x.1 ≤ x.2 <;> by_cases hy' : y.1 ≤ y.2 <;> simp_all
      exact congrArg NonemptyInterval.toProd (hx.trans hy.symm)

variable {t} in
theorem mem_domains {d : NonemptyInterval ℕ} :
    d ∈ domains t ↔ d.snd < (Tree.columns t).length := by
  simp only [domains, Finset.mem_filterMap, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨x, ⟨-, hx⟩, h⟩
    split_ifs at h with hle
    cases h
    exact hx
  · intro hd
    exact ⟨d.toProd, ⟨d.fst_le_snd.trans_lt hd, hd⟩, by simp [d.fst_le_snd]⟩

/-- Align-L(Δφ,H), (4), counts the moras between the phrase head and the left edge of the
    domain. -/
def alignL : Constraint (NonemptyInterval ℕ) := fun d ↦
  ∑ i ∈ Finset.Ico (min d.fst (head t)) (max d.fst (head t)), moras t i

/-- NonFin(H), (6), marks a domain containing the phrase-final syllable. -/
def nonFin : Constraint (NonemptyInterval ℕ) :=
  Constraint.binary fun d ↦ (Tree.columns t).length ≤ d.snd + 1

/-- Culminativity-H, (7), marks a domain containing more than one foot head. -/
def culm : Constraint (NonemptyInterval ℕ) :=
  Constraint.binary fun d ↦ 1 < ((Finset.Icc d.fst d.snd).filter (Stressed t)).card

/-- Align-R(H), (5), counts the moras after the right edge of the domain. -/
def alignR : Constraint (NonemptyInterval ℕ) := fun d ↦
  ∑ i ∈ Finset.Ioo d.snd (Tree.columns t).length, moras t i

/-- The labels of the tone-domain constraints. -/
inductive ToneConstraint
  | alignL | nonFin | culm | alignR
  deriving DecidableEq, Fintype

/-- The tone-domain constraints (4)–(7). -/
def tone : ConstraintSet (NonemptyInterval ℕ) ToneConstraint
  | .alignL => alignL t
  | .nonFin => nonFin t
  | .culm => culm t
  | .alignR => alignR t

/-- The column order of Tables 7 and 14. -/
def toneRanking : Ranking ToneConstraint 4 := Ranking.ofList [.alignL, .nonFin, .culm, .alignR]

theorem toneRanking_dominates_alignR :
    ∀ c ≠ ToneConstraint.alignR, toneRanking.Dominates c .alignR := by
  decide

/-- The tone-domain tableau of Tables 7 and 14. -/
def toneTableau : Tableau (NonemptyInterval ℕ) 4 := .ofRanking (tone t) toneRanking (domains t)

/-- The extent of the predicted domain is the number of syllables it takes in after the phrase
    head, the most it can take without a foot head or the phrase-final syllable. -/
def extent : ℕ :=
  Nat.findGreatest (fun k ↦ ∀ i ∈ Finset.Ioc (head t) (head t + k), ¬ Stressed t i)
    ((Tree.columns t).length - head t - 2)

/-- The predicted domain runs from the phrase head over `extent t` further syllables. -/
def toneDomain : NonemptyInterval ℕ := ⟨(head t, head t + extent t), Nat.le_add_right _ _⟩

variable {t} {d d' : NonemptyInterval ℕ}

theorem alignL_eq_zero_iff (hμ : ∀ i < (Tree.columns t).length, 0 < moras t i)
    (hd : d ∈ domains t) : alignL t d = 0 ↔ d.fst = head t := by
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun h ↦ by simp [alignL, h]⟩
  have := d.fst_le_snd.trans_lt (mem_domains.1 hd)
  exact (Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
    ⟨min d.fst (head t), Finset.mem_Ico.2 ⟨le_rfl, by omega⟩, hμ _ (by omega)⟩).ne' h

theorem nonFin_eq_zero_iff : nonFin t d = 0 ↔ d.snd + 1 < (Tree.columns t).length := by
  simp [nonFin]

theorem culm_eq_zero_iff (hp : Stressed t (head t)) (hl : d.fst = head t) :
    culm t d = 0 ↔ ∀ i ∈ Finset.Ioc (head t) d.snd, ¬ Stressed t i := by
  rw [culm, Constraint.binary_eq_zero_iff, not_lt, Finset.card_le_one]
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, hl]
  refine ⟨fun h i hi hs ↦ ?_, fun h a ha b hb ↦ ?_⟩
  · have := h i ⟨⟨hi.1.le, hi.2⟩, hs⟩ (head t) ⟨⟨le_rfl, hl ▸ d.fst_le_snd⟩, hp⟩
    omega
  · have ha' : a = head t := by_contra fun h' ↦ h a ⟨by omega, ha.1.2⟩ ha.2
    have hb' : b = head t := by_contra fun h' ↦ h b ⟨by omega, hb.1.2⟩ hb.2
    rw [ha', hb']

theorem alignR_lt_alignR (hμ : ∀ i < (Tree.columns t).length, 0 < moras t i)
    (h : d.snd < d'.snd) (h' : d'.snd < (Tree.columns t).length) : alignR t d' < alignR t d :=
  Finset.sum_lt_sum_of_subset (Finset.Ioo_subset_Ioo_left h.le) (Finset.mem_Ioo.2 ⟨h, h'⟩)
    (by simp) (hμ _ h') fun _ _ _ ↦ Nat.zero_le _

/-- If every syllable has a mora and the phrase head is a non-final foot head, then under any
    ranking that puts Align-R(H) lowest the optimal tone domain is `toneDomain t`, the widest
    domain that starts at the phrase head and contains neither a second foot head nor the
    phrase-final syllable (§4.5). -/
theorem tone_optimal {r : Ranking ToneConstraint 4}
    (hr : ∀ c ≠ ToneConstraint.alignR, r.Dominates c .alignR)
    (hμ : ∀ i < (Tree.columns t).length, 0 < moras t i) (hp : Stressed t (head t))
    (hn : head t + 1 < (Tree.columns t).length) :
    (Tableau.ofRanking (tone t) r (domains t)).optimal = {toneDomain t} := by
  have hext : ∀ i ∈ Finset.Ioc (head t) (head t + extent t), ¬ Stressed t i :=
    Nat.findGreatest_spec (P := fun k ↦ ∀ i ∈ Finset.Ioc (head t) (head t + k), ¬ Stressed t i)
      (Nat.zero_le _) (by simp)
  have hle : extent t ≤ (Tree.columns t).length - head t - 2 := Nat.findGreatest_le _
  -- a domain satisfies Align-L(Δφ,H), NonFin(H) and Culminativity-H iff it lies in `toneDomain t`
  have hfeas : ∀ d ∈ domains t, (∀ c ≠ ToneConstraint.alignR, tone t c d = 0) ↔
      d.fst = head t ∧ d.snd ≤ head t + extent t := by
    intro d hd
    have hpd := d.fst_le_snd
    constructor
    · intro h
      have hl := (alignL_eq_zero_iff hμ hd).1 (h .alignL (by decide))
      have hF := nonFin_eq_zero_iff.1 (h .nonFin (by decide))
      have hC := (culm_eq_zero_iff hp hl).1 (h .culm (by decide))
      have : d.snd - head t ≤ extent t :=
        Nat.le_findGreatest (by omega) (by rwa [Nat.add_sub_cancel' (hl ▸ hpd)])
      exact ⟨hl, by omega⟩
    · rintro ⟨hl, hsnd⟩ (_ | _ | _ | _) hc
      · exact (alignL_eq_zero_iff hμ hd).2 hl
      · exact nonFin_eq_zero_iff.2 (by omega)
      · exact (culm_eq_zero_iff hp hl).2 fun i hi ↦ hext i (Finset.Ioc_subset_Ioc_right hsnd hi)
      · exact absurd rfl hc
  have hm : toneDomain t ∈ domains t :=
    mem_domains.2 (by simp only [toneDomain]; omega)
  have hmf := (hfeas _ hm).2 ⟨rfl, le_rfl⟩
  rw [Tableau.ofRanking_optimal_eq_argmin_filter hr ⟨_, hm, hmf⟩]
  refine StrictAntiOn.argmin_eq_singleton (fun d hd d' hd' hlt ↦ ?_)
    ⟨Finset.mem_filter.2 ⟨hm, hmf⟩, fun d hd ↦ ?_⟩
  · rw [Finset.coe_filter] at hd hd'
    have hl := ((hfeas d hd.1).1 hd.2).1
    have hl' := ((hfeas d' hd'.1).1 hd'.2).1
    refine alignR_lt_alignR hμ (lt_of_le_of_ne (NonemptyInterval.le_def.1 hlt.le).2 fun h ↦
      hlt.ne (NonemptyInterval.ext (Prod.ext (hl.trans hl'.symm) h))) (mem_domains.1 hd'.1)
  · rw [Finset.coe_filter] at hd
    obtain ⟨hl, hsnd⟩ := (hfeas d hd.1).1 hd.2
    exact NonemptyInterval.le_def.2 ⟨hl.ge, hsnd⟩

/-- The optimal tone domain of a phrase under the column order of Tables 7 and 14. -/
theorem toneTableau_optimal (hμ : ∀ i < (Tree.columns t).length, 0 < moras t i)
    (hp : Stressed t (head t)) (hn : head t + 1 < (Tree.columns t).length) :
    (toneTableau t).optimal = {toneDomain t} :=
  tone_optimal toneRanking_dominates_alignR hμ hp hn

end ToneDomain

/-- In isolation the domain cannot expand past the primary stress (Table 7), the next syllable
    being phrase-final, so the High target is the primary stress itself. -/
theorem tone_in_isolation :
    (toneTableau fell).optimal = {⟨(3, 3), le_rfl⟩} ∧
      (toneTableau weFell).optimal = {⟨(4, 4), le_rfl⟩} ∧
      (toneTableau annatto).optimal = {⟨(1, 1), le_rfl⟩} :=
  ⟨by rw [toneTableau_optimal (by decide) (by decide) (by decide)]; decide,
    by rw [toneTableau_optimal (by decide) (by decide) (by decide)]; decide,
    by rw [toneTableau_optimal (by decide) (by decide) (by decide)]; decide⟩

/-! ### Phrases -/

/-- *[(atɔ́ː) (hɛlɨ)]* 'the friend was injured' (Fig. 9), whose second word is a trochee. -/
def friendInjured : Tree :=
  .ph [.node (.om true) [Tree.ft true [.σ 1, .σ 2 true]], .om [.ft true [.σ 1 true, .σ 1]]]

/-- *[(atɔː) (hɛ́pɨː)ɾɨ]* 'the friend has been injured' (Fig. 10), whose second word begins with
    an iamb. -/
def friendHasBeenInjured : Tree :=
  .ph [.node (.om true) [Tree.ft true [.σ 1, .σ 2 true]],
    .om [.ft true [.σ 1, .σ 2 true], .σ 1]]

/-- The head of a trochee blocks the domain (Fig. 9), so the High target stays on the primary
    stress *tɔ́ː*. -/
theorem tone_blocked_by_trochee_head :
    (toneTableau friendInjured).optimal = {⟨(1, 1), le_rfl⟩} :=
  by rw [toneTableau_optimal (by decide) (by decide) (by decide)]; decide

/-- The same short *hɛ* joins the domain as the dependent of an iamb (Fig. 10). That it blocks
    only as the head of a trochee is the paper's third argument for trochaic reversal (§1). -/
theorem tone_crosses_iamb_dependent :
    (toneTableau friendHasBeenInjured).optimal = {⟨(1, 2), by decide⟩} :=
  by rw [toneTableau_optimal (by decide) (by decide) (by decide)]; decide

/-- *[(itɔː)tɔ (tápɨː)ɾɨ]* 'the man has been heard' (Table 12), an instance of Table 14's
    `/σσσ # σσσ/`. -/
def manHasBeenHeard : Tree :=
  .ph [.node (.om true) [Tree.ft true [.σ 1, .σ 2 true], Tree.σ 1],
    .om [.ft true [.σ 1, .σ 2 true], .σ 1]]

/-- The domain left-aligns to *tɔː* and takes in the unstressed *tɔ* and *tá* (Table 14),
    stopping before the iamb head *pɨː*. -/
theorem table14 : (toneTableau manHasBeenHeard).optimal = {⟨(1, 3), by decide⟩} :=
  by rw [toneTableau_optimal (by decide) (by decide) (by decide)]; decide

/-- *[(umɨː)ŋi ⟨a⟩(lámaː)(kilɨ)]* 'the annatto fell' (Fig. 3), in which the noun heads the phrase
    and the verb's initial vowel is unparsed (§4.3), leaving an iamb and a final trochee. -/
def annattoFell : Tree :=
  .ph [.node (.om true) [Tree.ft true [.σ 1, .σ 2 true], Tree.σ 1],
    .om [.σ 1, .ft false [.σ 1, .σ 2 true], .ft true [.σ 1 true, .σ 1]]]

/-- In Fig. 3 the domain runs from the primary stress *mɨː* over three unstressed syllables to
    *lá* and stops before the foot head *maː*, so the High target is an unstressed syllable three
    syllables after the stress it marks (§1, §7). -/
theorem stress_tone_incoherence :
    head annattoFell = 1 ∧ (toneTableau annattoFell).optimal = {⟨(1, 4), by decide⟩} ∧
      ¬ Stressed annattoFell 4 ∧ Stressed annattoFell 5 :=
  ⟨by decide,
    by rw [toneTableau_optimal (by decide) (by decide) (by decide)]; decide,
    by decide, by decide⟩

end BeckerEtAl2025
