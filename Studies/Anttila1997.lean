module

public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Linglib.Data.Examples.Anttila1997
public import Linglib.Fragments.Finnish.Phonology
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify

/-!
# Anttila 1997: deriving variation from grammar

Finnish genitive plurals come in a strong variant (heavy penult, *naa.pu.rei.den*) and a weak
one (light penult, *naa.pu.ri.en*). Stems of one or two syllables choose categorically, longer
CV-final stems vary, and the variation is biased by the stem-final vowel and by the weight of
the antepenult. One partially ordered grammar covers all of it. Its constraints are the
harmonic alignments of stress, weight, and sonority together with bans on adjacent syllables of
equal stress or weight; Finnish stratifies them by promoting No Clash and the two stress–weight
mismatches above the rest. Every total ranking consistent with the grammar picks a winner, and
a variant's probability is the share of rankings under which it wins. The stress
constraints decide short stems and stems with a heavy antepenult outright; where they tie,
secondary stress being optional, the two internally unranked intermediate sets resolve the
competition at rates that the corpus frequencies track.

Item and page numbers follow the ROA-63 manuscript.

## Main definitions

* `Syllable`, `Constraint`: syllables as stress, weight, and nuclear sonority, and the twenty
  constraints of (50), with `Constraint.violations` counting on a syllable string.
* `Sonority.ofVowel`: the nuclear sonority of a vowel, by its height.
* `finnishGrammar`: the strata of (50) refined by the universal rankings (28).
* `Shape.cands`: the candidate sets of the categorical tableaux; `word`: the trisyllabic
  candidates of (52) by motif; `wins`: the rankings under which a variant wins its motif.
* `predicted`: the result column of (52), as the paper's fraction of rankings.

## References

* [anttila-1997]
* [prince-smolensky-1993] — harmonic alignment
* [tesar-smolensky-1995] — stratified domination hierarchies
* [kiparsky-1993b] — partial ranking as a source of quantitative predictions
-/

@[expose] public section

namespace Anttila1997

open OptimalityTheory

/-! ### Syllable prominence (25) -/

/-- Nuclear sonority, ordered `i < o < a`. -/
inductive Sonority
  | i
  | o
  | a
  deriving DecidableEq, Repr, Fintype

/-- Position on the sonority hierarchy. -/
def Sonority.rank : Sonority → Fin 3
  | .i => 0
  | .o => 1
  | .a => 2

instance : LinearOrder Sonority := LinearOrder.lift' Sonority.rank (by decide)

/-- The sonority of a vowel by its height: the low vowels are A, the high vowels I, and the
others O. -/
def Sonority.ofVowel (v : Phonology.Segment) : Sonority :=
  if v.HasValue .low true then .a else if v.HasValue .high true then .i else .o

/-- The high vowels /i u y/ are I, the mid vowels /o ö/ O, and the low vowels /a ä/ A (§2.2). -/
theorem Sonority.ofVowel_finnish :
    [Finnish.i, Finnish.u, Finnish.y, Finnish.o, Finnish.ö, Finnish.a, Finnish.ä].map ofVowel =
      [.i, .i, .i, .o, .o, .a, .a] := by
  decide

/-- Syllable weight. -/
inductive Weight
  | light
  | heavy
  deriving DecidableEq, Repr, Fintype

/-- Whether a weight is the prominent value of its scale, the one stress aligns with. -/
def Weight.prominent : Weight → Bool
  | .heavy => true
  | .light => false

/-- A syllable of a candidate records its stress, and its weight and nuclear sonority where the
tableau specifies them (`X` leaves both open). -/
structure Syllable where
  stressed : Bool
  weight : Option Weight := none
  nucleus : Option Sonority := none
  deriving DecidableEq, Repr

/-- Each constraint of (50) stars a stress–weight, weight–sonority, or stress–sonority
combination within a syllable (28), or an adjacency of equal stress or weight (29). -/
inductive Constraint
  | stressWeight (stressed : Bool) (w : Weight)
  | weightSonority (w : Weight) (s : Sonority)
  | stressSonority (stressed : Bool) (s : Sonority)
  | clash (stressed : Bool)
  | collision (w : Weight)
  deriving DecidableEq, Repr, Fintype

/-- A constraint's violations on a syllable string are the syllables showing the starred
combination, or the adjacent pairs sharing the starred value. -/
def Constraint.violations : Constraint → List Syllable → ℕ
  | .stressWeight st w, l => l.countP fun σ => decide (σ.stressed = st ∧ σ.weight = some w)
  | .weightSonority w s, l => l.countP fun σ => decide (σ.weight = some w ∧ σ.nucleus = some s)
  | .stressSonority st s, l =>
    l.countP fun σ => decide (σ.stressed = st ∧ σ.nucleus = some s)
  | .clash st, l => (l.zip l.tail).countP fun p => decide (p.1.stressed = st ∧ p.2.stressed = st)
  | .collision w, l =>
    (l.zip l.tail).countP fun p => decide (p.1.weight = some w ∧ p.2.weight = some w)

/-! ### The grammar for Finnish (28), (50) -/

/-- Harmonic alignment (27) of sonority with a binary scale ranks the constraint against the less
sonorous nucleus higher on the scale's prominent value, and the one against the more sonorous
nucleus higher on the other value. -/
def alignedAbove (prominent : Bool) (s s' : Sonority) : Prop :=
  if prominent then s < s' else s' < s

instance (p : Bool) (s s' : Sonority) : Decidable (alignedAbove p s s') := by
  unfold alignedAbove; infer_instance

/-- In the universal rankings (28) the stress–weight mismatches outrank the matches, and
sonority aligns with weight and with stress. -/
def Universal : Constraint → Constraint → Prop
  | .stressWeight st w, .stressWeight st' w' => st ≠ w.prominent ∧ st' = w'.prominent
  | .weightSonority w s, .weightSonority w' s' => w = w' ∧ alignedAbove w.prominent s s'
  | .stressSonority st s, .stressSonority st' s' => st = st' ∧ alignedAbove st s s'
  | _, _ => False

instance : DecidableRel Universal := fun a b => by
  cases a <;> cases b <;> dsimp only [Universal] <;> infer_instance

theorem alignedAbove_trans {p : Bool} {s₁ s₂ s₃ : Sonority} (h : alignedAbove p s₁ s₂)
    (h' : alignedAbove p s₂ s₃) : alignedAbove p s₁ s₃ := by
  cases p <;> simp only [alignedAbove, Bool.false_eq_true, ite_false, ite_true] at *
  · exact h'.trans h
  · exact h.trans h'

theorem alignedAbove_asymm {p : Bool} {s s' : Sonority} (h : alignedAbove p s s')
    (h' : alignedAbove p s' s) : False := by
  cases p <;> simp only [alignedAbove, Bool.false_eq_true, ite_false, ite_true] at * <;>
    exact lt_asymm h h'

theorem Universal.trans {a b c : Constraint} (hab : Universal a b) (hbc : Universal b c) :
    Universal a c := by
  cases a <;> cases b <;> cases c <;> simp only [Universal] at hab hbc ⊢
  · exact ⟨hab.1, hbc.2⟩
  · obtain ⟨rfl, h⟩ := hab
    obtain ⟨rfl, h'⟩ := hbc
    exact ⟨rfl, alignedAbove_trans h h'⟩
  · obtain ⟨rfl, h⟩ := hab
    obtain ⟨rfl, h'⟩ := hbc
    exact ⟨rfl, alignedAbove_trans h h'⟩

theorem Universal.asymm {a b : Constraint} (hab : Universal a b) (hba : Universal b a) : False := by
  cases a <;> cases b <;> simp only [Universal] at hab hba
  · exact hab.1 hba.2
  · obtain ⟨rfl, h⟩ := hab
    exact alignedAbove_asymm h hba.2
  · obtain ⟨rfl, h⟩ := hab
    exact alignedAbove_asymm h hba.2

/-- The strata of (50) are No Clash, the two stress–weight mismatches, the intermediary sets
(49), and the rest. -/
def Constraint.set : Constraint → Fin 5
  | .clash true => 0
  | .stressWeight true .light | .stressWeight false .heavy => 1
  | .weightSonority .heavy .i | .stressSonority true .i | .collision .light => 2
  | .weightSonority .heavy .o | .stressSonority true .o | .weightSonority .light .a
  | .collision .heavy | .stressWeight true .heavy | .clash false => 3
  | _ => 4

/-- Finnish only adds rankings to (28), reversing no universal ranking across strata. -/
theorem set_mono : ∀ a b, Universal a b → a.set ≤ b.set := by decide

/-- The roster in the column order of (50). -/
def constraint : Fin 20 → Constraint :=
  ![.clash true, .stressWeight true .light, .stressWeight false .heavy,
    .weightSonority .heavy .i, .stressSonority true .i, .collision .light,
    .weightSonority .heavy .o, .stressSonority true .o, .weightSonority .light .a,
    .collision .heavy, .stressWeight true .heavy, .clash false,
    .weightSonority .heavy .a, .stressSonority true .a, .weightSonority .light .o,
    .weightSonority .light .i, .stressSonority false .a, .stressSonority false .o,
    .stressSonority false .i, .stressWeight false .light]

/-- Stratum of a roster position. -/
def stratumOf (c : Fin 20) : Fin 5 := (constraint c).set

/-- The universal rankings on the roster, reflexively. -/
def universalOn (a b : Fin 20) : Prop := a = b ∨ Universal (constraint a) (constraint b)

instance : DecidableRel universalOn := fun a b => by unfold universalOn; infer_instance

instance : IsPartialOrder (Fin 20) universalOn where
  refl _ := Or.inl rfl
  trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    exact Or.inr (hab.trans hbc)
  antisymm a b hab hba := by
    rcases hab with rfl | hab
    · rfl
    rcases hba with rfl | hba
    · rfl
    exact (hab.asymm hba).elim

theorem set_eq_of_universal : ∀ a b, Universal a b → a.set = b.set → a.set = 4 := by decide

theorem stratum_triv {k : Fin 5} (hk : k ≠ 4) :
    ∀ a b, stratumOf a = k → stratumOf b = k → universalOn a b → a = b := by
  rintro a b ha hb (rfl | h)
  · rfl
  · exact absurd (ha.symm.trans (set_eq_of_universal _ _ h (ha.trans hb.symm))) hk

/-- The grammar for Finnish, final version (50). -/
def finnishGrammar : Fin 20 → Fin 20 → Prop := stratified stratumOf universalOn

instance : IsPartialOrder (Fin 20) finnishGrammar :=
  inferInstanceAs (IsPartialOrder (Fin 20) (stratified stratumOf universalOn))

instance : DecidableRel finnishGrammar :=
  inferInstanceAs (DecidableRel (stratified stratumOf universalOn))

/-! ### Categorical predictions (§5.1) -/

/-- The tableau syllables are stressed or unstressed, and of unspecified, heavy, or light
weight. -/
def X' : Syllable := ⟨true, none, none⟩
def X : Syllable := ⟨false, none, none⟩
def H' : Syllable := ⟨true, some .heavy, none⟩
def H : Syllable := ⟨false, some .heavy, none⟩
def L' : Syllable := ⟨true, some .light, none⟩
def L : Syllable := ⟨false, some .light, none⟩

/-- The stem shapes of the categorical tableaux, named by their examples (33) *maa*, (35) *kala*,
(37) *maailma*, (39) *ministeri*, (40) *margariini*, (42) *Aleksanteri*, (43)
*koordinaatisto*, (44) *italiaano*. -/
inductive Shape
  | maa
  | kala
  | maailma
  | ministeri
  | margariini
  | aleksanteri
  | koordinaatisto
  | italiaano
  deriving DecidableEq, Repr, Fintype

/-- The candidates of the tableaux (32), (34), (36), (38), (41) are the weak variant, the strong
one, and after a heavy antepenult the strong one with its stress shifted. -/
def Shape.cands : Shape → Finset (List Syllable)
  | .maa => {[H', H], [L', H]}
  | .kala => {[X', L, H], [X', H, H]}
  | .maailma => {[X', X, H', H], [X', X, L, H]}
  | .ministeri => {[X', X, L, L, H], [X', X, L, H', H]}
  | .margariini => {[X', X, H', L, H], [X', X, H', H, H], [X', X, H, H', H]}
  | .aleksanteri => {[X', X, X, L, H', H], [X', X, X, L, L, H]}
  | .koordinaatisto => {[X', X, H', H, L, H], [X', X, H', H, H', H]}
  | .italiaano => {[X', X, L, H', L, H], [X', X, L, H', H, H], [X', X, L, H, H', H]}

/-- The roster's constraints on the candidates of a shape's tableau. -/
def tableauCon : ConstraintSet (Shape × List Syllable) (Fin 20) :=
  fun c x ↦ (constraint c).violations x.2

/-- The total rankings consistent with the Finnish grammar. -/
def rankings : Finset (Ranking (Fin 20) 20) := consistentTotalOrders finnishGrammar

/-- A tableau candidate that every consistent ranking picks. -/
def Shape.Categorical (s : Shape) (cand : List Syllable) : Prop :=
  ∀ σ ∈ rankings, PicksAt ⟨Shape.cands, tableauCon⟩ σ s cand

/-- Monosyllabic stems take the strong variant (32), *mai.den* and not *ma.jen* (33). -/
theorem maa_strong : Shape.Categorical .maa [H', H] := fun _ hσ =>
  picksAt_stratified_of_dominates (mem_consistentTotalOrders.mp hσ) (Finset.mem_insert_self _ _)
    (by decide +kernel)

/-- Disyllabic CV-final stems take the weak variant (34), *ka.lo.jen* and not *ka.loi.den*
(35). -/
theorem kala_weak : Shape.Categorical .kala [X', L, H] := fun _ hσ =>
  picksAt_stratified_of_dominates (mem_consistentTotalOrders.mp hσ) (Finset.mem_insert_self _ _)
    (by decide +kernel)

/-- A heavy antepenult in a 4-syllabic stem is stressed and forces a light penult (38), giving
*mar.ga.rii.ni.en* only (40). -/
theorem margariini_weak : Shape.Categorical .margariini [X', X, H', L, H] := fun _ hσ =>
  picksAt_stratified_of_dominates (mem_consistentTotalOrders.mp hσ) (Finset.mem_insert_self _ _)
    (by decide +kernel)

/-- A light ante-antepenult before a heavy antepenult likewise forces a light penult (41),
giving *i.ta.li.aa.no.jen* only (44). -/
theorem italiaano_weak : Shape.Categorical .italiaano [X', X, L, H', L, H] := fun _ hσ =>
  picksAt_stratified_of_dominates (mem_consistentTotalOrders.mp hσ) (Finset.mem_insert_self _ _)
    (by decide +kernel)

/-- After a light antepenult, or a heavy one after a heavy ante-antepenult, the stress constraints
tie, so secondary stress is optional ((36), (38), (41)). -/
theorem stress_tie :
    ∀ s ∈ [Shape.maailma, .ministeri, .aleksanteri, .koordinaatisto],
      ∀ o ∈ s.cands, ∀ o' ∈ s.cands, ∀ c, stratumOf c ≤ 1 →
        tableauCon c (s, o) = tableauCon c (s, o') := by
  decide +kernel

/-! ### Quantitative predictions (§5.3) -/

/-- The two genitive-plural variants (1). -/
inductive Variant
  | strong
  | weak
  deriving DecidableEq, Repr, Fintype

/-- The other variant. -/
def Variant.other : Variant → Variant
  | .strong => .weak
  | .weak => .strong

theorem Variant.ne_other (v : Variant) : v ≠ v.other := by cases v <;> decide

theorem Variant.univ_eq_pair (v : Variant) :
    (Finset.univ : Finset Variant) = {v, v.other} := by cases v <;> decide

/-- A motif of (52) pairs the antepenult's weight with the stem-final vowel. -/
abbrev Motif := Weight × Sonority

/-- The penult of a variant with nucleus `s` is stressed and heavy, or unstressed and light. -/
def penult : Variant → Sonority → Syllable
  | .strong, s => ⟨true, some .heavy, some s⟩
  | .weak, s => ⟨false, some .light, some s⟩

/-- A trisyllabic candidate of (52) has initial stress, an unstressed antepenult of the motif's
weight, the variant's penult, and an unstressed heavy final. -/
def word : Motif → Variant → List Syllable
  | (w, s), v => [X', ⟨false, some w, none⟩, penult v s, H]

/-- The roster's constraints on the variants of a motif. -/
def con : ConstraintSet (Motif × Variant) (Fin 20) :=
  fun c x ↦ (constraint c).violations (word x.1 x.2)

/-- The rankings under which variant `v` wins motif `m`. -/
def wins (m : Motif) (v : Variant) : Finset (Ranking (Fin 20) 20) :=
  rankings.filter fun σ ↦ PicksAt ⟨fun _ ↦ Finset.univ, con⟩ σ m v

theorem card_wins_mul (m : Motif) (v : Variant) (k : Fin 5)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → universalOn a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → con c (m, v) = con c (m, v.other))
    (h_dec : ((active con m v v.other).filter (stratumOf · = k)).Nonempty) :
    (wins m v).card * ((active con m v v.other).filter (stratumOf · = k)).card =
      rankings.card *
        (favoring con m v v.other ∩ (active con m v v.other).filter (stratumOf · = k)).card :=
  card_filter_picksAt_stratified_binary (Variant.univ_eq_pair v) v.ne_other h_triv h_tie h_dec

theorem card_wins_of_counts (m : Motif) (v : Variant) (k : Fin 5) (n t : ℕ)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → universalOn a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → con c (m, v) = con c (m, v.other))
    (h_dec : ((active con m v v.other).filter (stratumOf · = k)).Nonempty)
    (hn : (favoring con m v v.other ∩ (active con m v v.other).filter (stratumOf · = k)).card = n)
    (ht : ((active con m v v.other).filter (stratumOf · = k)).card = t) :
    (wins m v).card * t = rankings.card * n := by
  rw [← hn, ← ht]; exact card_wins_mul m v k h_triv h_tie h_dec

/-- The result column of (52) gives the strong variant's share of the rankings as the paper's
fraction. -/
def predictedStrong : Motif → ℕ × ℕ
  | (.light, .i) => (1, 3)
  | (.light, _) => (1, 1)
  | (.heavy, .a) => (1, 2)
  | (.heavy, .o) => (1, 5)
  | (.heavy, .i) => (0, 1)

/-- The result column of (52). -/
def predicted (m : Motif) : Variant → ℕ × ℕ
  | .strong => predictedStrong m
  | .weak => ((predictedStrong m).2 - (predictedStrong m).1, (predictedStrong m).2)

theorem card_wins_strong_of {m : Motif} {n t : ℕ} (hp : predictedStrong m = (n, t))
    (h : (wins m .strong).card * t = rankings.card * n) :
    (wins m .strong).card * (predictedStrong m).2 = rankings.card * (predictedStrong m).1 := by
  have hn : n = (predictedStrong m).1 := by rw [hp]
  have ht : t = (predictedStrong m).2 := by rw [hp]
  subst hn ht
  exact h

/-- The shares of (52) are decided in Set 3 after a light antepenult and for *h.tii*, and in Set 4
for *h.taa* and *h.too*. -/
theorem card_wins_strong : ∀ m : Motif,
    (wins m .strong).card * (predictedStrong m).2 = rankings.card * (predictedStrong m).1
  | (.light, .i) => card_wins_strong_of rfl
    (card_wins_of_counts (.light, .i) .strong 2 1 3 (stratum_triv (by decide))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  | (.light, .o) => card_wins_strong_of rfl
    (card_wins_of_counts (.light, .o) .strong 2 1 1 (stratum_triv (by decide))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  | (.light, .a) => card_wins_strong_of rfl
    (card_wins_of_counts (.light, .a) .strong 2 1 1 (stratum_triv (by decide))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  | (.heavy, .i) => card_wins_strong_of rfl (by
    have h := card_wins_of_counts (.heavy, .i) .strong 2 0 2 (stratum_triv (by decide))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    omega)
  | (.heavy, .o) => card_wins_strong_of rfl
    (card_wins_of_counts (.heavy, .o) .strong 3 1 5 (stratum_triv (by decide))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  | (.heavy, .a) => card_wins_strong_of rfl (by
    have h := card_wins_of_counts (.heavy, .a) .strong 3 2 4 (stratum_triv (by decide))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    omega)

theorem card_wins_add (m : Motif) : (wins m .strong).card + (wins m .weak).card = rankings.card :=
  card_filter_picksAt_binary_add (r := finnishGrammar) (i := m) (Variant.univ_eq_pair .strong)
    (Variant.ne_other .strong) (by obtain ⟨w, s⟩ := m; cases w <;> cases s <;> decide +kernel)

theorem predictedStrong_le : ∀ m : Motif, (predictedStrong m).1 ≤ (predictedStrong m).2 := by
  decide

theorem card_wins_weak {m : Motif}
    (h : (wins m .strong).card * (predictedStrong m).2 = rankings.card * (predictedStrong m).1) :
    (wins m .weak).card * (predicted m .weak).2 = rankings.card * (predicted m .weak).1 := by
  have h₂ := card_wins_add m
  have hle := predictedStrong_le m
  generalize (wins m .strong).card = ws at h h₂
  generalize (wins m .weak).card = ww at h₂ ⊢
  generalize rankings.card = r at h h₂ ⊢
  dsimp only [predicted]
  generalize (predictedStrong m).1 = n at h hle ⊢
  generalize (predictedStrong m).2 = t at h hle ⊢
  subst h₂
  zify [hle] at h ⊢
  linear_combination (-1 : ℤ) * h

/-- Each variant wins the share of rankings (52) predicts. -/
theorem card_wins (m : Motif) :
    ∀ v, (wins m v).card * (predicted m v).2 = rankings.card * (predicted m v).1
  | .strong => card_wins_strong m
  | .weak => card_wins_weak (card_wins_strong m)

/-! ### The paper's data -/

/-- Antepenult weight from a motif label. -/
def Weight.ofChar? : Char → Option Weight
  | 'l' => some .light
  | 'h' => some .heavy
  | _ => none

/-- Stem-final vowel from a motif label. -/
def Sonority.ofChar? : Char → Option Sonority
  | 'a' => some .a
  | 'o' => some .o
  | 'i' => some .i
  | _ => none

/-- A motif label of (52)–(53) writes the antepenult weight, `t`, and the stem-final vowel,
doubled for the strong variant. -/
def Motif.parse? (s : String) : Option (Motif × Variant) :=
  match s.toList with
  | [w, '.', 't', v] => do pure ((← Weight.ofChar? w, ← Sonority.ofChar? v), .weak)
  | [w, '.', 't', v, v'] =>
    if v = v' then do pure ((← Weight.ofChar? w, ← Sonority.ofChar? v), .strong) else none
  | _ => none

/-- The value of a digit string. -/
def digits (l : List Char) : ℕ := l.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- A printed whole percentage. -/
def percent? (s : String) : Option ℕ :=
  if s.toList.all Char.isDigit then some (digits s.toList) else none

/-- A printed percentage in tenths, reading `99.4` as `994` and `100` as `1000`. -/
def tenths? (s : String) : Option ℕ :=
  match s.toList.span (· ≠ '.') with
  | (int, []) => if int.all Char.isDigit then some (10 * digits int) else none
  | (int, [_, d]) =>
    if int.all Char.isDigit && d.isDigit then some (10 * digits int + digits [d]) else none
  | _ => none

/-- The predicted percentage of Table (53) is the share of (52) to the nearest percent. -/
theorem rows_predicted :
    ∀ r ∈ Examples.all, r.feature? "syllables" = some "3" →
      ∀ mv ∈ (r.feature? "motif" >>= Motif.parse?).toList,
        ∀ p ∈ (r.feature? "pred_pct" >>= percent?).toList,
          2 * p * (predicted mv.1 mv.2).2 ≤
              200 * (predicted mv.1 mv.2).1 + (predicted mv.1 mv.2).2 ∧
            200 * (predicted mv.1 mv.2).1 ≤ (2 * p + 1) * (predicted mv.1 mv.2).2 := by
  decide +kernel

/-- In Tables (48) and (53) the variant the grammar favors is the more frequent one. -/
theorem rows_frequency :
    ∀ r ∈ Examples.all, r.feature? "syllables" = some "3" →
      ∀ mv ∈ (r.feature? "motif" >>= Motif.parse?).toList,
        ∀ q ∈ (r.feature? "obs_pct" >>= tenths?).toList,
          ((predicted mv.1 mv.2).2 < 2 * (predicted mv.1 mv.2).1 → 500 < q) ∧
            (2 * (predicted mv.1 mv.2).1 < (predicted mv.1 mv.2).2 → q < 500) := by
  decide +kernel

/-- In (6) the stems ending in a high vowel prefer the weak variant, and those ending in a low
vowel the strong one. -/
theorem rows_final_vowel :
    ∀ r ∈ Examples.all, r.source.paperLabel ∈ ["(6a)", "(6b)", "(6c)"] →
      ∀ v ∈ (r.feature? "stem" >>= (·.toList.getLast?) >>= Finnish.ofChar).toList,
        (Sonority.ofVowel v = .i → r.feature? "variant" = some "weak") ∧
          (Sonority.ofVowel v = .a → r.feature? "variant" = some "strong") := by
  decide +kernel

end Anttila1997
