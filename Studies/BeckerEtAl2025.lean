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
Align-R(H), and `tone_optimal_eq_singleton_iff` derives the paper's generalization from these
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

variable {t}

/-- If every syllable has a mora and the phrase head is a non-final foot head, then under any
    ranking that puts Align-R(H) lowest the unique optimal tone domain starts at the phrase head
    and extends up to, but not including, the next foot head or the phrase-final syllable
    (§4.5). -/
theorem tone_optimal_eq_singleton_iff {r : Ranking ToneConstraint 4}
    (hr : ∀ c ≠ ToneConstraint.alignR, r.Dominates c .alignR)
    (hμ : ∀ i < (Tree.columns t).length, 0 < moras t i) (hp : Stressed t (head t))
    (hn : head t + 1 < (Tree.columns t).length) {d : NonemptyInterval ℕ} :
    (Tableau.ofRanking (tone t) r (domains t)).optimal = {d} ↔
      d.fst = head t ∧ d.snd + 1 < (Tree.columns t).length ∧
        (∀ i ∈ Finset.Ioc (head t) d.snd, ¬ Stressed t i) ∧
        (d.snd + 2 = (Tree.columns t).length ∨ Stressed t (d.snd + 1)) := by
  set n := (Tree.columns t).length
  set p := head t with hp_eq
  have hex : ∃ k, p + k + 2 = n ∨ Stressed t (p + k + 1) := ⟨n - p - 2, .inl (by omega)⟩
  set k := Nat.find hex
  have hk : p + k + 2 = n ∨ Stressed t (p + k + 1) := Nat.find_spec hex
  have hkn : p + k + 2 ≤ n := by
    by_contra h
    exact Nat.find_min hex (show n - p - 2 < k by omega) (.inl (by omega))
  have hfree : ∀ i ∈ Finset.Ioc p (p + k), ¬ Stressed t i := fun i hi hs ↦ by
    rw [Finset.mem_Ioc] at hi
    exact Nat.find_min hex (show i - p - 1 < k by omega) (.inr (by convert hs using 2; omega))
  -- the blocker characterizes the winner's right edge
  have hchar : ∀ e, p ≤ e → (e + 1 < n ∧ (∀ i ∈ Finset.Ioc p e, ¬ Stressed t i) ∧
      (e + 2 = n ∨ Stressed t (e + 1)) ↔ e = p + k) := by
    intro e hpe
    constructor
    · rintro ⟨he, hfr, hb⟩
      have : k = e - p := (Nat.find_eq_iff hex).2 ⟨by rwa [Nat.add_sub_cancel' hpe],
        fun j hj ↦ by
          rintro (h | h)
          · omega
          · exact hfr (p + j + 1) (Finset.mem_Ioc.2 ⟨by omega, by omega⟩) h⟩
      omega
    · rintro rfl
      exact ⟨by omega, hfree, hk⟩
  let m : NonemptyInterval ℕ := ⟨(p, p + k), by simp⟩
  have hm : m ∈ domains t := mem_domains.2 (by simp [m]; omega)
  have hpos : ∀ s : Finset ℕ, (∀ i ∈ s, i < n) → s.Nonempty → 0 < ∑ i ∈ s, moras t i :=
    fun s hs ⟨i, hi⟩ ↦ Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨i, hi, hμ i (hs i hi)⟩
  -- the winner violates none of Align-L(Δφ,H), NonFin(H) and Culminativity-H
  have hm0 : ∀ c ≠ ToneConstraint.alignR, tone t c m = 0 := by
    rintro (_ | _ | _ | _) hc
    · simp [tone, alignL, m, ← hp_eq]
    · simp [tone, nonFin, Constraint.binary, m]; omega
    · simp only [tone, culm, Constraint.binary, m, ite_eq_right_iff, one_ne_zero, imp_false,
        not_lt]
      refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
      have ha' : a = p := by
        by_contra h; exact hfree a (Finset.mem_Ioc.2 ⟨by omega, ha.1.2⟩) ha.2
      have hb' : b = p := by
        by_contra h; exact hfree b (Finset.mem_Ioc.2 ⟨by omega, hb.1.2⟩) hb.2
      rw [ha', hb']
    · exact absurd rfl hc
  -- a competitor can beat the winner only on Align-R(H)
  have hlose : ∀ d j, tone t j d < tone t j m → j = .alignR := fun d j hj ↦ by
    by_contra h
    exact absurd hj (by rw [hm0 j h]; exact Nat.not_lt_zero _)
  have hwin : (Tableau.ofRanking (tone t) r (domains t)).optimal = {m} := by
    rw [Tableau.ofRanking_optimal_eq_singleton_iff]
    refine ⟨hm, fun d hd hne ↦ ?_⟩
    have hdn := mem_domains.1 hd
    have hbeat : ∀ c ≠ ToneConstraint.alignR, 0 < tone t c d →
        ∃ i, tone t i m < tone t i d ∧ ∀ j, tone t j d < tone t j m → r.Dominates i j :=
      fun c hc h ↦ ⟨c, by rwa [hm0 c hc], fun j hj ↦ hlose d j hj ▸ hr c hc⟩
    by_cases hL : 0 < tone t .alignL d
    · exact hbeat _ (by decide) hL
    have hl : d.fst = p := by
      by_contra hne'
      refine hL (hpos _ (fun i hi ↦ ?_) (Finset.nonempty_Ico.2 ?_))
      · have := d.fst_le_snd; simp only [Finset.mem_Ico] at hi; omega
      · omega
    by_cases hF : 0 < tone t .nonFin d
    · exact hbeat _ (by decide) hF
    have hdF : d.snd + 1 < n := by
      simp only [tone, nonFin, Constraint.binary] at hF; split_ifs at hF with h
      · simp at hF
      · omega
    by_cases hC : 0 < tone t .culm d
    · exact hbeat _ (by decide) hC
    have hdC : ∀ i ∈ Finset.Ioc p d.snd, ¬ Stressed t i := fun i hi hs ↦ by
      have h2 : 1 < ((Finset.Icc d.fst d.snd).filter (Stressed t)).card := by
        refine Finset.one_lt_card.2 ⟨p, ?_, i, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hl.le, hl ▸ d.fst_le_snd⟩, hp⟩
        · rw [Finset.mem_Ioc] at hi
          simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hi.2⟩, hs⟩
        · rw [Finset.mem_Ioc] at hi; omega
      exact hC (by simp [tone, culm, Constraint.binary, h2])
    have hle : d.snd ≤ p + k := by
      by_contra h
      rcases hk with hk | hk
      · omega
      · exact hdC _ (Finset.mem_Ioc.2 ⟨by omega, by omega⟩) hk
    have hlt : d.snd < p + k := by
      refine lt_of_le_of_ne hle fun h ↦ hne ?_
      exact NonemptyInterval.ext (Prod.ext hl h)
    have hR : tone t .alignR m < tone t .alignR d :=
      Finset.sum_lt_sum_of_subset (Finset.Ioo_subset_Ioo_left hlt.le)
        (Finset.mem_Ioo.2 ⟨hlt, by omega⟩) (by simp) (hμ _ (by omega)) fun _ _ _ ↦ Nat.zero_le _
    refine ⟨.alignR, hR, fun j hj ↦ ?_⟩
    obtain rfl := hlose d j hj
    exact absurd hj hR.not_gt
  rw [hwin, Finset.singleton_inj, eq_comm]
  constructor
  · rintro rfl
    obtain ⟨h1, h2, h3⟩ := (hchar (p + k) (Nat.le_add_right _ _)).2 rfl
    exact ⟨rfl, h1, h2, h3⟩
  · rintro ⟨hl, he, hfr, hb⟩
    have hpe : p ≤ d.snd := hl ▸ d.fst_le_snd
    exact NonemptyInterval.ext (Prod.ext hl ((hchar _ hpe).1 ⟨he, hfr, hb⟩))

/-- The optimal tone domain of a phrase whose phrase head is a non-final foot head, under the
    paper's column order. -/
theorem toneTableau_optimal_eq_singleton_iff
    (hμ : ∀ i < (Tree.columns t).length, 0 < moras t i) (hp : Stressed t (head t))
    (hn : head t + 1 < (Tree.columns t).length) {d : NonemptyInterval ℕ} :
    (toneTableau t).optimal = {d} ↔
      d.fst = head t ∧ d.snd + 1 < (Tree.columns t).length ∧
        (∀ i ∈ Finset.Ioc (head t) d.snd, ¬ Stressed t i) ∧
        (d.snd + 2 = (Tree.columns t).length ∨ Stressed t (d.snd + 1)) :=
  tone_optimal_eq_singleton_iff toneRanking_dominates_alignR hμ hp hn

end ToneDomain

/-- In isolation the domain cannot expand past the primary stress (Table 7), the next syllable
    being phrase-final, so the High target is the primary stress itself. -/
theorem tone_in_isolation :
    (toneTableau fell).optimal = {⟨(3, 3), le_rfl⟩} ∧
      (toneTableau weFell).optimal = {⟨(4, 4), le_rfl⟩} ∧
      (toneTableau annatto).optimal = {⟨(1, 1), le_rfl⟩} :=
  ⟨(toneTableau_optimal_eq_singleton_iff (by decide) (by decide) (by decide)).2 (by decide),
    (toneTableau_optimal_eq_singleton_iff (by decide) (by decide) (by decide)).2 (by decide),
    (toneTableau_optimal_eq_singleton_iff (by decide) (by decide) (by decide)).2 (by decide)⟩

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
  (toneTableau_optimal_eq_singleton_iff (by decide) (by decide) (by decide)).2 (by decide)

/-- The same short *hɛ* joins the domain as the dependent of an iamb (Fig. 10). That it blocks
    only as the head of a trochee is the paper's third argument for trochaic reversal (§1). -/
theorem tone_crosses_iamb_dependent :
    (toneTableau friendHasBeenInjured).optimal = {⟨(1, 2), by decide⟩} :=
  (toneTableau_optimal_eq_singleton_iff (by decide) (by decide) (by decide)).2 (by decide)

/-- *[(itɔː)tɔ (tápɨː)ɾɨ]* 'the man has been heard' (Table 12), an instance of Table 14's
    `/σσσ # σσσ/`. -/
def manHasBeenHeard : Tree :=
  .ph [.node (.om true) [Tree.ft true [.σ 1, .σ 2 true], Tree.σ 1],
    .om [.ft true [.σ 1, .σ 2 true], .σ 1]]

/-- The domain left-aligns to *tɔː* and takes in the unstressed *tɔ* and *tá* (Table 14),
    stopping before the iamb head *pɨː*. -/
theorem table14 : (toneTableau manHasBeenHeard).optimal = {⟨(1, 3), by decide⟩} :=
  (toneTableau_optimal_eq_singleton_iff (by decide) (by decide) (by decide)).2 (by decide)

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
    (toneTableau_optimal_eq_singleton_iff (by decide) (by decide) (by decide)).2 (by decide),
    by decide, by decide⟩

end BeckerEtAl2025
