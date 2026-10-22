module

public import Studies.Benua1997
public import Linglib.Data.Wordlist.Alderete2001
public import Linglib.Data.PHOIBLE.Chart
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Alderete 2001: dominance effects as transderivational anti-faithfulness

Alderete adds to Optimality Theory, for every faithfulness constraint `F`, an anti-faithfulness
constraint `¬F` that is satisfied exactly when `F` is violated at least once (9). Ranked on the
output–output relation an affix subcategorizes for in Benua's Transderivational Correspondence
Theory (8), `¬F` forces one alternation in the base of the derived word: the Luo voicing exchange
(§2.2.2), the accent deletion of Japanese dominant affixes (§3) and the dragging-tone mutation of
Limburg Dutch (§5.2). The subparadigms, the relation-indexed OO constraints and recursive
evaluation are those of `Benua1997`.

## Main definitions

* `ooAnti`: the anti-faithfulness counterpart of `Benua1997.ooIdentity`.
* `derivation`: the subparadigm of a suffixed word.
* `Japanese.grammar`, `Limburg.grammar`: the summary rankings (24) and (54), with the ranking of
  the anti-faithfulness constraint over its IO counterpart that they leave out.

## Main results

* `not_isFaithfulness_antifaithful_maxViol`, `not_isMarkedness_antifaithful_maxViol`:
  anti-faithfulness is neither faithfulness nor markedness (§2.1.2).
* `Luo.optimal_exchange`: under `¬F ≫ F` the winners are the derivatives with exactly one voicing
  alternation in the base, so the plural of *bat* could as well be *pet-e* as *bed-e* (fn. 7).
* `ooAnti_eq_of_take_eq`: strict base mutation (27); an OO constraint reads the derivative only
  where it shares the base.
* `maxViolFeature_base_le_input`: when the base surfaces as it is underlyingly, a derivative that
  satisfies ¬OO-MAX violates IO-MAX, so a dominance effect needs ¬OO-MAX ≫ IO-MAX.
* `Japanese.summary_mispredicts`, `Limburg.summary_mispredicts`: (24) and (54) leave that ranking
  out, and rankings consistent with them keep the base accent of *kóobe-kko* and the dragging tone
  of *káál-ə*.
* `Japanese.rows`, `Limburg.rows`: with it, one ranking per language derives every word of the
  data from its input over every candidate.
* `Limburg.toneless_wins`: (53) also needs the tonic to bear a tone (§5.2.2).

## Implementation notes

Accent and tone are read off the paper's transcription: an acute vowel bears the accent, and in
Limburg Dutch an acute mora is linked to the H tone, so the dragging tone *áá* is a doubly linked
H and the falling tone *áa* an H on the first mora (43). With the accent a property of its bearer,
NOFLOP(Accent) of (24) is a deletion plus an insertion and is not stated separately, NOFLOP(Tone)
counts the links an H loses and NOSPREAD(Tone) those it gains. The candidates vary only the
accent or tone of the derivative's segments: in Japanese at most one vowel is accented, as in
every Japanese word (12), and in Limburg Dutch the tonic, the first two moras, bears the H
(§5.2.2). Luo segments are PHOIBLE's, and a Luo candidate may change the voicing of any
obstruent.

The base of a Japanese derivative is the first morph of its underlying form, since Japanese
nouns surface as they are underlyingly. For (1) this is the root, where tableau (22) uses the
past tense *yón-da*; the two agree on the accent the derivative inherits.

## References

* [alderete-2001]
* [alderete-1999]
* [benua-1997]
* [mccarthy-prince-1995]
* [moran-mccloy-2019]
-/

@[expose] public section

namespace Alderete2001

open OptimalityTheory Benua1997
open Wordlist (OORelation)

/-! ### Transderivational anti-faithfulness -/

section Theory

variable {α ρ : Type*} [DecidableEq ρ]

/-- The subparadigm of a suffixed word ((8), [benua-1997] (11)) has a base that surfaces as its
input, the derivative and its input, and pairs positions from the left edge in every
correspondence relation. -/
def derivation (base input d : List α) : Correspondence Role α :=
  paradigm base base input d (Correspondence.diagonalPairs base.length)
    (Correspondence.diagonalPairs input.length) (Correspondence.diagonalPairs base.length)

variable {b i d : List α}

@[simp] theorem derivation_edge_base :
    (derivation b i d).edge .base .derivative = Correspondence.diagonal b.length d.length :=
  Correspondence.edgeOfPairs_diagonalPairs (min_le_left _ _)

@[simp] theorem derivation_edge_input :
    (derivation b i d).edge .derivInput .derivative = Correspondence.diagonal i.length d.length :=
  Correspondence.edgeOfPairs_diagonalPairs (min_le_left _ _)

@[simp] theorem derivation_form_derivative : (derivation b i d).form .derivative = d := rfl

/-- The anti-faithfulness constraint `¬OO_rel-F` ((9), (19)) is the counterpart of the OO
constraint `ooIdentity rel f`. A derived word bearing `rel` satisfies it exactly when its OO
relation violates `F`, and it is vacuous at the base and on words bearing another relation. -/
def ooAnti (rel : ρ) (f : Correspondence Role α → Role → Role → ℕ) : ρ → ParadigmConstraint α :=
  fun r ↦ ⟨fun _ ↦ 0, fun c ↦
    if r = rel then Constraint.antifaithful (f · .base .derivative) c else 0⟩

theorem ooAnti_atDerived (rel : ρ) (f : Correspondence Role α → Role → Role → ℕ) :
    (ooAnti rel f rel).atDerived = Constraint.antifaithful (ooIdentity rel f rel).atDerived := by
  ext c
  simp [ooAnti, ooIdentity]

/-- Anti-faithfulness is not faithfulness (§2.1.2), since the fully faithful candidate violates
¬MAX. -/
theorem not_isFaithfulness_antifaithful_maxViol :
    ¬ Correspondence.IsFaithfulness
      (Constraint.antifaithful fun c : Correspondence BinaryRole α ↦ c.maxViol .lhs .rhs) :=
  Correspondence.isFaithfulness_maxViol.not_antifaithful

/-- Anti-faithfulness is not markedness either (§2.1.2), since two candidates with one output rate
differently on ¬MAX. -/
theorem not_isMarkedness_antifaithful_maxViol [Inhabited α] :
    ¬ Correspondence.IsMarkedness .rhs
      (Constraint.antifaithful fun c : Correspondence BinaryRole α ↦ c.maxViol .lhs .rhs) := by
  intro h
  have := h (a := .identity []) (b := .parallel [default] []) rfl
  simp [Constraint.antifaithful, Correspondence.maxViol_of_diagonal _ _ _
    (Correspondence.parallel_edge_lhs_rhs _ _)] at this

/-! #### Strict base mutation (§3.2) -/

private theorem zip_take_length {β : Type*} (b : List α) (d : List β) :
    b.zip (d.take b.length) = b.zip d := by
  induction b generalizing d with
  | nil => rfl
  | cons x b ih => cases d <;> simp [ih]

private theorem zip_isPrefix_zip_append {β : Type*} (b a : List α) (d : List β) :
    b.zip d <+: (b ++ a).zip d := by
  induction b generalizing d with
  | nil => exact List.nil_prefix
  | cons x b ih =>
    cases d with
    | nil => simp
    | cons y d => exact List.cons_prefix_cons.2 ⟨rfl, ih d⟩

variable (P : α → Prop) [DecidablePred P]

/-- MAX(P) on two strings paired from the left edge counts the pairs whose first member has `P`
and whose second lacks it. -/
def zipMax (x y : List α) : ℕ := (x.zip y).countP fun p ↦ P p.1 ∧ ¬ P p.2

/-- DEP(P) on two strings paired from the left edge counts the pairs whose second member has `P`
and whose first lacks it. -/
def zipDep (x y : List α) : ℕ := (x.zip y).countP fun p ↦ ¬ P p.1 ∧ P p.2

theorem maxViolFeature_base :
    (derivation b i d).maxViolFeature P .base .derivative = zipMax P b d :=
  Correspondence.maxViolFeature_of_diagonal _ _ _ P derivation_edge_base

theorem maxViolFeature_input :
    (derivation b i d).maxViolFeature P .derivInput .derivative = zipMax P i d :=
  Correspondence.maxViolFeature_of_diagonal _ _ _ P derivation_edge_input

theorem depViolFeature_base :
    (derivation b i d).depViolFeature P .base .derivative = zipDep P b d :=
  Correspondence.depViolFeature_of_diagonal _ _ _ P derivation_edge_base

theorem depViolFeature_input :
    (derivation b i d).depViolFeature P .derivInput .derivative = zipDep P i d :=
  Correspondence.depViolFeature_of_diagonal _ _ _ P derivation_edge_input

/-- **Strict base mutation** ((27)). The OO relation reads the derivative only where it shares the
base, so derivatives that differ only in their affixes rate alike on ¬OO-MAX(P), and deleting an
affix's accent never satisfies it. -/
theorem ooAnti_eq_of_take_eq (rel r : ρ) {i' d' : List α}
    (h : d.take b.length = d'.take b.length) :
    (ooAnti rel (Correspondence.maxViolFeature P) r).atDerived (derivation b i d) =
      (ooAnti rel (Correspondence.maxViolFeature P) r).atDerived (derivation b i' d') := by
  simp only [ooAnti, Constraint.antifaithful, Constraint.binary, maxViolFeature_base, zipMax,
    ← zip_take_length b d, ← zip_take_length b d', h]

/-- When the base surfaces as it is underlyingly, an accent the derivative loses from its base it
loses from its input, so every derivative satisfying ¬OO-MAX(P) violates IO-MAX(P) and a TAF effect
needs ¬OO-MAX(P) to dominate IO-MAX(P). -/
theorem maxViolFeature_base_le_input (a : List α) :
    (derivation b (b ++ a) d).maxViolFeature P .base .derivative ≤
      (derivation b (b ++ a) d).maxViolFeature P .derivInput .derivative := by
  rw [maxViolFeature_base, maxViolFeature_input]
  exact (zip_isPrefix_zip_append b a d).countP_le

end Theory

/-! ### Transcriptions -/

/-- The segments of a transcription, without its morph boundaries and slashes. -/
def word (s : String) : List Char := s.toList.filter (· ∉ ['-', '+', '/'])

/-- The first morph of an underlying form. -/
def stem (s : String) : List Char := (s.toList.filter (· ≠ '/')).takeWhile (· ≠ '+')

/-- The suffixes of a derived form, after its first morph boundary. -/
def suffix (s : String) : List Char := (s.toList.dropWhile (· ≠ '-')).filter (· ≠ '-')

/-- A vowel of the Japanese and Limburg Dutch transcriptions. -/
def IsVowel (c : Char) : Prop := c ∈ ['a', 'e', 'i', 'o', 'u', 'ə', 'á', 'é', 'í', 'ó', 'ú']

/-- An accented vowel, or in Limburg Dutch a mora linked to the H tone. -/
def IsAccented (c : Char) : Prop := c ∈ ['á', 'é', 'í', 'ó', 'ú']

instance : DecidablePred IsVowel := fun c ↦ inferInstanceAs (Decidable (c ∈ _))
instance : DecidablePred IsAccented := fun c ↦ inferInstanceAs (Decidable (c ∈ _))

/-- The vowels of a word. -/
def vowels (w : List Char) : List (Fin w.length) := (List.finRange w.length).filter (IsVowel w[·])

/-- A vowel with its accent. -/
def accent : Char → Char
  | 'a' => 'á' | 'e' => 'é' | 'i' => 'í' | 'o' => 'ó' | 'u' => 'ú' | c => c

/-- A vowel without its accent. -/
def deaccent : Char → Char
  | 'á' => 'a' | 'é' => 'e' | 'í' => 'i' | 'ó' => 'o' | 'ú' => 'u' | c => c

/-- A word with its `i`-th segment accented. -/
def accentAt (w : List Char) (i : Fin w.length) : List Char := w.set i (accent w[i])

/-- MAX(Accent) (14a), and NOFLOP(Tone) (35d) on the links of an H tone. -/
abbrev maxAccent : Correspondence Role Char → Role → Role → ℕ :=
  Correspondence.maxViolFeature IsAccented

/-- DEP(Accent) (14b), and NOSPREAD(Tone) (35c) on the links of an H tone. -/
abbrev depAccent : Correspondence Role Char → Role → Role → ℕ :=
  Correspondence.depViolFeature IsAccented

/-! ### Luo: the voicing exchange (§2.2.2) -/

namespace Luo

open Phonology Data.PHOIBLE

/-- The segment a letter of the Luo transcription (6) writes, by its PHOIBLE chart entry; *č* is
the voiceless palato-alveolar affricate. -/
def segment : Char → Segment
  | 'b' => FeatureMatrix.«b».toSegment | 'p' => FeatureMatrix.«p».toSegment
  | 't' => FeatureMatrix.«t».toSegment | 'd' => FeatureMatrix.«d».toSegment
  | 'k' => FeatureMatrix.«k».toSegment | 'g' => FeatureMatrix.«ɡ».toSegment
  | 'θ' => FeatureMatrix.«θ».toSegment | 'ð' => FeatureMatrix.«ð».toSegment
  | 'č' => FeatureMatrix.«t̠ʃ».toSegment | 'w' => FeatureMatrix.«w».toSegment
  | 'a' => FeatureMatrix.«a».toSegment | 'e' => FeatureMatrix.«e».toSegment
  | 'o' => FeatureMatrix.«o».toSegment | 'u' => FeatureMatrix.«u».toSegment
  | 'l' => FeatureMatrix.«l».toSegment | _ => ⊥

/-- The segments of a Luo transcription. -/
def segments (s : String) : List Segment := (word s).map segment

/-- The segment with the opposite voicing. -/
def toggleVoice (s : Segment) : Segment := s.setFeature .voice (s .voice ≠ ↑true)

/-- A derivative's candidates are its segments with each obstruent voiced or voiceless. -/
def voicings (w : List Segment) : Finset (List Segment) :=
  (w.map fun s ↦ if s.IsObstruent then [s, toggleVoice s] else [s]).sections.toFinset

/-- IDENT[voice] (10a). -/
abbrev identVoice : Correspondence Role Segment → Role → Role → ℕ :=
  Correspondence.identViolFeature (· .voice)

/-- The exchange ranking (11), `¬OO_Ex-IDENT[voice] ≫ OO_Ex-IDENT[voice]`. -/
def exchange : List (OORelation → ParadigmConstraint Segment) :=
  [ooAnti .exchange identVoice, ooIdentity .exchange identVoice]

/-- **Anti-faithfulness forces one alternation and no more** ((9), fn. 7). Under the exchange
ranking the winners are the candidates with exactly one voicing alternation in the base, whenever
one has. -/
theorem optimal_exchange {b i : List Segment} {S : Finset (List Segment)}
    (h : ∃ d ∈ S, identVoice (derivation b i d) .base .derivative = 1) :
    (tableau (derivation b i) S recursive exchange .exchange).optimal =
      S.filter fun d ↦ identVoice (derivation b i d) .base .derivative = 1 := by
  obtain ⟨d₀, hd₀, h₀⟩ := h
  rw [optimal_tableau_recursive (by simp [exchange, ooAnti, ooIdentity]),
    show exchange.map (fun k ↦ (k .exchange).atDerived ∘ derivation b i) =
      [Constraint.antifaithful fun d ↦ identVoice (derivation b i d) .base .derivative,
        fun d ↦ identVoice (derivation b i d) .base .derivative] from rfl,
    Tableau.optimal_ofList_antifaithful ⟨d₀, hd₀, h₀ ▸ Nat.one_pos⟩]
  ext d
  simp only [Finset.mem_argmin, Finset.mem_filter]
  refine ⟨fun ⟨⟨hd, hpos⟩, hmin⟩ ↦ ⟨hd, ?_⟩, fun ⟨hd, h1⟩ ↦ ⟨⟨hd, h1 ▸ Nat.one_pos⟩, ?_⟩⟩
  · have := hmin d₀ ⟨hd₀, h₀ ▸ Nat.one_pos⟩
    omega
  · rintro e ⟨-, he⟩
    omega

/-- In (11a) *bat* pluralizes as *bed-e*. The faithful *bet-e* violates the anti-faithfulness
constraint, and the total reversal *ped-e* satisfies it only with a gratuitous second violation of
faithfulness. -/
theorem bat_bede :
    (tableau (derivation (segments "bat") (segments "bat-e")) {segments "bed-e", segments "bet-e",
      segments "ped-e"} recursive exchange .exchange).optimal = {segments "bed-e"} := by
  decide

/-- In (11b) the same ranking gives the other half of the exchange, *čogo* pluralizing as
*čok-e*. -/
theorem cogo_coke :
    (tableau (derivation (segments "čogo") (segments "čogo-e")) {segments "čok-e",
      segments "čog-e"} recursive exchange .exchange).optimal = {segments "čok-e"} := by
  decide

/-- The input of a plural of (6) is its singular followed by the plural suffix. -/
def pluralInput (r : Data.Wordlist.FormRelation Wordlist.Analysis) : List Segment :=
  (word r.form.form.form ++ suffix r.target.form.form).map segment

/-- Every plural of (6) is a winner of the exchange ranking among all the voicings of its
segments, the voiced *bed-e*, *luð-e* and the devoiced *čok-e*, *owet-e* alike. -/
theorem plurals : ∀ r ∈ Wordlist.analysisRelations, r.target.relation = some .exchange →
    segments r.target.form.form ∈ (tableau (derivation (segments r.form.form.form) (pluralInput r))
      (voicings (segments r.target.form.form)) recursive exchange .exchange).optimal := by
  have h : ∀ r ∈ Wordlist.analysisRelations, r.target.relation = some .exchange →
      segments r.target.form.form ∈ voicings (segments r.target.form.form) ∧
        identVoice (derivation (segments r.form.form.form) (pluralInput r)
          (segments r.target.form.form)) .base .derivative = 1 := by
    decide +kernel
  intro r hr hex
  obtain ⟨hmem, h1⟩ := h r hr hex
  rw [optimal_exchange ⟨_, hmem, h1⟩]
  exact Finset.mem_filter.2 ⟨hmem, h1⟩

/-- The plural of *bat* could as well be *pet-e*, since the exchange ranking fixes that one
voicing alternation occurs and not where (fn. 7). -/
theorem pete_wins :
    segments "pet-e" ∈ (tableau (derivation (segments "bat") (segments "bat-e"))
      (voicings (segments "bed-e")) recursive exchange .exchange).optimal := by
  rw [optimal_exchange ⟨segments "bed-e", by decide, by decide⟩]
  decide

end Luo

/-! ### Japanese dominance effects (§3.1–§3.3) -/

namespace Japanese

/-- CULMINATIVITY (15a) requires a word to bear an accent. -/
def culmin : List Char → ℕ := Constraint.binary fun w ↦ ∀ c ∈ w, ¬ IsAccented c

/-- ALIGN-R(Accent, PrWd) (15b) assigns a violation to each accent off the word's last vowel. -/
def alignR (w : List Char) : ℕ := ((w.filter IsVowel).dropLast).countP IsAccented

/-- A derivative's candidates are its segments with at most one vowel accented. -/
def accentings (w : List Char) : Finset (List Char) :=
  insert (w.map deaccent) ((vowels (w.map deaccent)).map (accentAt _)).toFinset

/-- The constraints of the summary rankings (24), NOFLOP(Accent) aside. -/
inductive Con
  | antiDomMax | domMax | recMax | antiRecMax | ioMax | ioDep | alignR | culmin
  deriving DecidableEq, Fintype, Repr

/-- The paradigm constraint each label names. -/
def Con.eval : Con → OORelation → ParadigmConstraint Char
  | .antiDomMax => ooAnti .dominant maxAccent
  | .domMax => ooIdentity .dominant maxAccent
  | .recMax => ooIdentity .recessive maxAccent
  | .antiRecMax => ooAnti .recessive maxAccent
  | .ioMax => ioFaith maxAccent
  | .ioDep => ioFaith depAccent
  | .alignR => markedness Japanese.alignR
  | .culmin => markedness Japanese.culmin

/-- The rankings (24) draws, IO-MAX(Ac) over ALIGN-R, IO-DEP(Ac) over CULMIN, and ¬OO_Dom-MAX(Ac)
over OO-MAX(Ac) over ¬OO_Rec-MAX(Ac). -/
def summary : Finset (Con × Con) :=
  {(.ioMax, .alignR), (.ioDep, .culmin), (.antiDomMax, .domMax), (.antiDomMax, .recMax),
    (.domMax, .antiRecMax), (.recMax, .antiRecMax)}

/-- The winners under `σ` for a derived word bearing `rel`, with base `base` and input `input`,
among the accentings of its segments `w`. -/
def eval {n : ℕ} (σ : Ranking Con n) (base input w : List Char) (rel : OORelation) :
    Finset (List Char) :=
  (tableau (derivation base input) (accentings w) recursive (List.ofFn fun p ↦ (σ p).eval)
    rel).optimal

/-- The violations each constraint assigns a derivative of base `b` and input `i`, counted on the
zips of their strings (`Con.atDerived_derivation`). -/
def Con.violations (rel : OORelation) (b i : List Char) : Con → Constraint (List Char)
  | .antiDomMax => if rel = .dominant then Constraint.antifaithful (zipMax IsAccented b) else 0
  | .domMax => if rel = .dominant then zipMax IsAccented b else 0
  | .recMax => if rel = .recessive then zipMax IsAccented b else 0
  | .antiRecMax => if rel = .recessive then Constraint.antifaithful (zipMax IsAccented b) else 0
  | .ioMax => zipMax IsAccented i
  | .ioDep => zipDep IsAccented i
  | .alignR => Japanese.alignR
  | .culmin => Japanese.culmin

theorem Con.atDerived_derivation (c : Con) (rel : OORelation) (b i : List Char) :
    (c.eval rel).atDerived ∘ derivation b i = c.violations rel b i := by
  funext d
  cases c <;> by_cases h : rel = .dominant <;> by_cases h' : rel = .recessive <;>
    simp [Con.eval, Con.violations, ooAnti, ooIdentity, ioFaith, markedness, h, h',
      Constraint.antifaithful, maxViolFeature_base, maxViolFeature_input, depViolFeature_input]

theorem Con.atBase_derivation (c : Con) (rel : OORelation) {b i d d' : List Char} :
    (c.eval rel).atBase (derivation b i d) = (c.eval rel).atBase (derivation b i d') := by
  cases c <;> rfl

theorem eval_eq {n : ℕ} (σ : Ranking Con n) (b i w : List Char) (rel : OORelation) :
    eval σ b i w rel =
      (Tableau.ofList (accentings w) (List.ofFn fun p ↦ (σ p).violations rel b i)).optimal := by
  rw [eval, optimal_tableau_recursive fun k hk _ _ _ _ ↦ ?_, List.map_ofFn,
    show ((fun k ↦ (k rel).atDerived ∘ derivation b i) ∘ fun p ↦ (σ p).eval) =
      fun p ↦ (σ p).violations rel b i from funext fun p ↦ Con.atDerived_derivation _ _ _ _]
  obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hk
  exact Con.atBase_derivation _ _

/-- A ranking extending (24) with ¬OO_Dom-MAX(Ac) over IO-MAX(Ac) and CULMIN. -/
def grammar : Ranking Con 8 :=
  .ofList [.antiDomMax, .domMax, .recMax, .antiRecMax, .ioMax, .ioDep, .alignR, .culmin]

theorem grammar_extends_summary : ∀ p ∈ summary, grammar.Dominates p.1 p.2 := by decide

/-- The rankings `grammar` adds to (24). -/
theorem grammar_antiDomMax : grammar.Dominates .antiDomMax .ioMax ∧
    grammar.Dominates .antiDomMax .culmin := by decide

/-- In (21) the dominant accented *-ppó* deletes the base accent and keeps its own,
*ada-ppó-i*. -/
theorem dominant_accented :
    (tableau (derivation (word "adá") (word "adá+ppó+i"))
      {word "adá-ppo-i", word "ada-ppo-i", word "ada-ppó-i"} recursive
      [ooAnti OORelation.dominant maxAccent, ooIdentity .dominant maxAccent, ioFaith maxAccent]
      .dominant).optimal = {word "ada-ppó-i"} := by
  decide

/-- In (22) the recessive *-tára* leaves the base accent, *yón-dara*. -/
theorem recessive :
    (tableau (derivation (word "yón-da") (word "yóm+tára")) {word "yon-dára", word "yón-dara"}
      recursive [ooIdentity OORelation.recessive maxAccent, ooAnti .recessive maxAccent]
      .recessive).optimal = {word "yón-dara"} := by
  decide

/-- In (23) the dominant unaccented *-kko* deletes the base accent and, with IO-DEP(Ac) over
CULMIN, nothing replaces it, *koobe-kko*. -/
theorem dominant_unaccented :
    (tableau (derivation (word "kóobe") (word "kóobe+kko"))
      {word "kóobe-kko", word "koobé-kko", word "koobe-kko"} recursive
      [ooAnti OORelation.dominant maxAccent, ioFaith depAccent, markedness culmin]
      .dominant).optimal = {word "koobe-kko"} := by
  decide

/-- In (27), were a root dominant, ¬OO-MAX(Ac) would still delete the base accent and never the
affix's, giving *root-áf* and not *róot-af*. -/
theorem root_dominance :
    (tableau (derivation (word "róot") (word "róot+áf")) {word "róot-af", word "root-áf"} recursive
      [ooAnti OORelation.dominant maxAccent, ooIdentity .dominant maxAccent] .dominant).optimal =
      {word "root-áf"} := by
  decide

/-- The words of (1), (12), (17), (18) are those of the data with an underlying form; the base of a
derivative is the first morph of it, and an underived word has none. -/
def base (x : Wordlist.Analysis) : List Char :=
  if x.relation.isSome then stem (x.underlying.getD "") else []

/-- **One grammar for every word** (§3.4). With ¬OO_Dom-MAX(Ac) over IO-MAX(Ac) and CULMIN, the
summary ranking derives each word of (1), (12), (17), (18) from its input over every placement of
at most one accent, the dominant derivatives (17), (18) like the recessive (1) and the underived
*hasi* (28). An underived word has no base, so it rates its candidates alike on every OO
constraint, whichever relation it is evaluated under. -/
theorem rows : ∀ x ∈ Wordlist.analyses, ∀ u ∈ x.underlying,
    eval grammar (base x) (word u) (word x.form.form) (x.relation.getD .dominant) =
      {word x.form.form} := by
  simp only [eval_eq]
  decide +kernel

/-- **(24) does not derive (23).** A ranking consistent with every ranking (24) draws, with
IO-MAX(Ac) over ¬OO_Dom-MAX(Ac), keeps the base accent, *kóobe-kko*. -/
theorem summary_mispredicts :
    ∃ σ : Ranking Con 8, (∀ p ∈ summary, σ.Dominates p.1 p.2) ∧
      eval σ (word "kóobe") (word "kóobe+kko") (word "koobe-kko") .dominant = {word "kóobe-kko"} :=
  ⟨.ofList [.ioDep, .ioMax, .culmin, .antiDomMax, .domMax, .recMax, .antiRecMax, .alignR],
    by decide, by rw [eval_eq]; decide +kernel⟩

end Japanese

/-! ### Limburg Dutch: dragging tone mutation (§5.2) -/

namespace Limburg

/-- The tonic's two moras, the first two vowels of the forms (42), (48). -/
def tonic (w : List Char) : List (Fin w.length) := (vowels w).take 2

/-- ALIGN-L(H, σ) (44): the H tone of the tonic is linked to its first mora. -/
def alignL (w : List Char) : ℕ :=
  match tonic w with
  | [i, j] => if ¬ IsAccented w[i] ∧ IsAccented w[j] then 1 else 0
  | _ => 0

/-- *H (45), one violation for each mora linked to the H tone, as (47) counts. -/
def starH (w : List Char) : ℕ := w.countP IsAccented

/-- A derivative's candidates are its segments with the H linked to one or both moras of the
tonic. -/
def tonePatterns (w : List Char) : Finset (List Char) :=
  match tonic (w.map deaccent) with
  | [i, j] => {(accentAt _ i).set j (accent (w.map deaccent)[j]), accentAt _ i, accentAt _ j}
  | _ => {w.map deaccent}

/-- The constraints of the summary rankings (54), *L aside, since no candidate bears an L tone. -/
inductive Con
  | alignL | antiDomNoFlop | ioNoFlop | ioNoSpread | domNoFlop | domNoSpread | antiRecNoFlop | starH
  deriving DecidableEq, Fintype, Repr

/-- The paradigm constraint each label names. -/
def Con.eval : Con → OORelation → ParadigmConstraint Char
  | .alignL => markedness Limburg.alignL
  | .antiDomNoFlop => ooAnti .dominant maxAccent
  | .ioNoFlop => ioFaith maxAccent
  | .ioNoSpread => ioFaith depAccent
  | .domNoFlop => ooIdentity .dominant maxAccent
  | .domNoSpread => ooIdentity .dominant depAccent
  | .antiRecNoFlop => ooAnti .recessive maxAccent
  | .starH => markedness Limburg.starH

/-- The rankings (54) draws, ALIGN-L over IO-TONE-FAITH and ¬OO_Dom-NOFLOP(Tone), IO-TONE-FAITH
over *H, and ¬OO_Dom-NOFLOP(Tone) over OO-TONE-FAITH over ¬OO_Rec-NOFLOP(Tone). -/
def summary : Finset (Con × Con) :=
  {(.alignL, .ioNoFlop), (.alignL, .ioNoSpread), (.alignL, .antiDomNoFlop), (.ioNoFlop, .starH),
    (.ioNoSpread, .starH), (.antiDomNoFlop, .domNoFlop), (.antiDomNoFlop, .domNoSpread),
    (.domNoFlop, .antiRecNoFlop), (.domNoSpread, .antiRecNoFlop)}

/-- The winners under `σ` for a word derived by a mutating suffix, with base `base` and input
`input`, among the tone patterns of its segments `w`. -/
def eval {n : ℕ} (σ : Ranking Con n) (base input w : List Char) : Finset (List Char) :=
  (tableau (derivation base input) (tonePatterns w) recursive (List.ofFn fun p ↦ (σ p).eval)
    .dominant).optimal

/-- The violations each constraint assigns a derivative of base `b` and input `i` bearing the
relation of the mutating suffixes, counted on the zips of their strings
(`Con.atDerived_derivation`). -/
def Con.violations (b i : List Char) : Con → Constraint (List Char)
  | .alignL => Limburg.alignL
  | .antiDomNoFlop => Constraint.antifaithful (zipMax IsAccented b)
  | .ioNoFlop => zipMax IsAccented i
  | .ioNoSpread => zipDep IsAccented i
  | .domNoFlop => zipMax IsAccented b
  | .domNoSpread => zipDep IsAccented b
  | .antiRecNoFlop => 0
  | .starH => Limburg.starH

theorem Con.atDerived_derivation (c : Con) (b i : List Char) :
    (c.eval .dominant).atDerived ∘ derivation b i = c.violations b i := by
  funext d
  cases c <;> simp [Con.eval, Con.violations, ooAnti, ooIdentity, ioFaith, markedness,
    Constraint.antifaithful, maxViolFeature_base, maxViolFeature_input, depViolFeature_base,
    depViolFeature_input]

theorem Con.atBase_derivation (c : Con) {b i d d' : List Char} :
    (c.eval .dominant).atBase (derivation b i d) =
      (c.eval .dominant).atBase (derivation b i d') := by
  cases c <;> rfl

theorem eval_eq {n : ℕ} (σ : Ranking Con n) (b i w : List Char) :
    eval σ b i w =
      (Tableau.ofList (tonePatterns w) (List.ofFn fun p ↦ (σ p).violations b i)).optimal := by
  rw [eval, optimal_tableau_recursive fun k hk _ _ _ _ ↦ ?_, List.map_ofFn,
    show ((fun k ↦ (k .dominant).atDerived ∘ derivation b i) ∘ fun p ↦ (σ p).eval) =
      fun p ↦ (σ p).violations b i from funext fun p ↦ Con.atDerived_derivation _ _ _]
  obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hk
  exact Con.atBase_derivation _

/-- A ranking extending (54) with ¬OO_Dom-NOFLOP(Tone) over IO-NOFLOP(Tone). -/
def grammar : Ranking Con 8 :=
  .ofList [.alignL, .antiDomNoFlop, .ioNoFlop, .ioNoSpread, .domNoFlop, .domNoSpread,
    .antiRecNoFlop, .starH]

theorem grammar_extends_summary : ∀ p ∈ summary, grammar.Dominates p.1 p.2 := by decide

/-- In (52) the dragging tone of *káál* loses its second link, *káal-ə*, not its first, which would
leave the rising tone ALIGN-L bans. -/
theorem dragging_mutates :
    (tableau (derivation (word "káál") (word "káál+ə")) {word "káal-ə", word "káál-ə",
      word "kaál-ə"} recursive
      [markedness alignL, ooAnti OORelation.dominant maxAccent, ooIdentity .dominant maxAccent]
      .dominant).optimal = {word "káal-ə"} := by
  decide

/-- In (53) a falling tone cannot mutate, since losing its only link leaves a rising tone and
spreading it violates NOSPREAD, so *stúur-ə* stays faithful. -/
theorem falling_stays :
    (tableau (derivation (word "stúur") (word "stúur+ə")) {word "stúur-ə", word "stúúr-ə",
      word "stuúr-ə"} recursive
      [markedness alignL, ooAnti OORelation.dominant maxAccent, ooIdentity .dominant depAccent]
      .dominant).optimal = {word "stúur-ə"} := by
  decide

/-- (53) needs the tonic to bear a tone (§5.2.2). Admitted, the toneless *stuur-ə* satisfies
¬OO-NOFLOP(Tone) by losing the base's only link, and wins. -/
theorem toneless_wins :
    (tableau (derivation (word "stúur") (word "stúur+ə")) {word "stúur-ə", word "stúúr-ə",
      word "stuúr-ə", word "stuur-ə"} recursive
      [markedness alignL, ooAnti OORelation.dominant maxAccent, ooIdentity .dominant depAccent]
      .dominant).optimal = {word "stuur-ə"} := by
  decide

/-- **One grammar for every word.** With ¬OO_Dom-NOFLOP(Tone) over IO-NOFLOP(Tone), the summary
ranking derives each derived form of (42) and (48) from its base, the dragging tone mutating and
the falling tone staying. -/
theorem rows : ∀ r ∈ Wordlist.analysisRelations, r.target.relation = some .dominant →
    eval grammar (word r.form.form.form) (word r.form.form.form ++ suffix r.target.form.form)
      (word r.target.form.form) = {word r.target.form.form} := by
  simp only [eval_eq]
  decide +kernel

/-- **(54) does not derive (52).** A ranking consistent with every ranking (54) draws, with
IO-NOFLOP(Tone) over ¬OO_Dom-NOFLOP(Tone), keeps the dragging tone, *káál-ə*. -/
theorem summary_mispredicts :
    ∃ σ : Ranking Con 8, (∀ p ∈ summary, σ.Dominates p.1 p.2) ∧
      eval σ (word "káál") (word "káál+ə") (word "káal-ə") = {word "káál-ə"} :=
  ⟨.ofList [.alignL, .ioNoFlop, .ioNoSpread, .antiDomNoFlop, .domNoFlop, .domNoSpread,
    .antiRecNoFlop, .starH], by decide, by rw [eval_eq]; decide +kernel⟩

end Limburg

end Alderete2001
