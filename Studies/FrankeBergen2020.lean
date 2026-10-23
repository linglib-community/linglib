module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Exhaustification.Finite
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Tactic.DeriveFintype

/-!
# Franke and Bergen (2020): Theory-Driven Statistical Modeling for Semantics and Pragmatics

Franke and Bergen compare four rational speech act models, in the style of Frank and Goodman, of the
nested Aristotelians *Q₁ of the aliens drank Q₂ of their water*, with *none*, *some* and *all* in
each position. An alien's type is the vertex of the triangle of opposition its drinking falls on
(`Aristotelian.Triangle`), none of its water, some but not all, or all, a world state is the
nonempty set of types some alien realizes, and a parse is the set of sites, among the whole sentence
and the two quantifiers, at which an exhaustivity operator applies. The vanilla model has only the
literal parse; lexical uncertainty, after Bergen, Levy and Goodman and Potts et al., fixes a lexicon
per speaker; the local- and global-implicature speakers choose an utterance together with a
matrix-free or arbitrary parse, one softmax over pairs per world.

## Main results

* `table1_ss` and its siblings: the readings of every utterance under every parse, the paper's
  Table 1.
* `vanilla_ss_prefers_wNA`, `gi_ss_prefers_wNS`: the global model corrects the interpretation of
  *some of the aliens drank some of their water* that the vanilla model gets wrong.
* `ss_m_parse_pref`, `m_ss_singleton`: its parse posterior peaks at the matrix-only parse, whose
  reading singles out the world with none- and some-drinkers only, the paper's explanation of
  the global model's win.
* `perParse_ss_prefers_o`: under the per-parse normalization the paper rejects, exhaustifying
  the outer quantifier beats exhaustifying the whole sentence at every rationality.

## Implementation notes

* One reading family, `ext`, generates every model: the vanilla model is its literal member, the
  speakers of the pooled models choose among utterance–parse pairs and their listeners hear the
  utterance, and lexical uncertainty, like the rejected per-parse architecture, fixes the latent
  as an argument of the speaker. Sentential alternatives range over a fourth quantifier, *not
  all*, that is never uttered. This is the paper's distinction between grammatical and utterance
  alternatives, which its model comparison favors over the alternative set of Gotzner and Romoli.
* Findings that hold at every rationality are closed by strict stochastic dominance of
  informativity profiles (`Multiset.StrictDominates`); the rationality-dependent ones are pinned
  at the paper's illustrative value of 5, where the comparisons clear to inequalities of naturals.
* The paper's cost term for *none*-initial utterances and its fixed error rate are omitted, and
  the vanilla preference reverses at the fitted cost. The second-level layer of the
  lexical-uncertainty model, after Lassiter and Goodman, is omitted; the first-level listener
  formalized here keeps the preference the paper's second-level listener loses.
* The paper's matrix exhaustivity operator is not Fox's innocent exclusion
  (`moi_ss_ne_innocent_exclusion`). The distinct matrix reading of *none of the aliens drank none
  of their water* comes from the lexical alternative *not all* of *none*, after Levinson.

## References

* [franke-bergen-2020]
* [frank-goodman-2012]
* [bergen-levy-goodman-2016]
* [potts-etal-2016]
* [lassiter-goodman-2017]
* [gotzner-romoli-2018]
* [levinson-2000]
* [fox-2007]
-/

@[expose] public section

namespace FrankeBergen2020

open scoped ENNReal
open MeasureTheory ProbabilityTheory Aristotelian

/-! ## The grammar of readings -/

/-! ### Domain -/

/-- A world state is the set of alien types realized by at least one alien, a nonempty set of
vertices of the triangle. -/
def World := {s : Finset Triangle // s.Nonempty}

instance : DecidableEq World := Subtype.instDecidableEq
instance : Fintype World := Subtype.fintype _

instance : Membership Triangle World := ⟨fun w t ↦ t ∈ w.val⟩

instance (t : Triangle) (w : World) : Decidable (t ∈ w) :=
  inferInstanceAs (Decidable (t ∈ w.val))

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨fun _ ↦ trivial⟩

/-- The world with only N-type aliens (each drank none). -/
def wN : World := ⟨{.E}, Finset.singleton_nonempty _⟩
/-- The world with N-type and S-type aliens. -/
def wNS : World := ⟨{.E, .IO}, by decide +kernel⟩
/-- The world with N-type and A-type aliens. -/
def wNA : World := ⟨{.E, .A}, by decide +kernel⟩
/-- The world with all three alien types. -/
def wNSA : World := ⟨{.E, .IO, .A}, by decide +kernel⟩
/-- The world with only S-type aliens (each drank some but not all). -/
def wS : World := ⟨{.IO}, Finset.singleton_nonempty _⟩
/-- The world with S-type and A-type aliens. -/
def wSA : World := ⟨{.IO, .A}, by decide +kernel⟩
/-- The world with only A-type aliens (each drank all). -/
def wA : World := ⟨{.A}, Finset.singleton_nonempty _⟩

instance : Nonempty World := ⟨wN⟩

/-- An EXH operator can be inserted at the whole sentence, the outer quantifier, or the inner
quantifier. -/
inductive ExhPosition where
  | matrix | outer | inner
  deriving DecidableEq, Fintype

/-- A parse is the set of EXH insertion sites. -/
abbrev Parse := Finset ExhPosition

instance : MeasurableSpace Parse := ⊤
instance : DiscreteMeasurableSpace Parse := ⟨fun _ ↦ trivial⟩
instance : Nonempty Parse := ⟨∅⟩

/-- The matrix-only parse M. -/
def pM : Parse := {.matrix}

/-- The outer-only parse O. -/
def pO : Parse := {.outer}

/-- The Aristotelian quantifiers make up the utterance vocabulary. -/
inductive AristQuant where
  | none | some | all
  deriving DecidableEq, Repr, Fintype

/-- The nine nested Aristotelian utterances are named outer quantifier first, so that `.ns` is
"None of the aliens drank some of their water". -/
inductive Utterance where
  | nn | ns | na
  | sn | ss | sa
  | an | as | aa
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Utterance := ⟨.nn⟩
instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- Outer quantifier of an utterance. -/
def Utterance.outer : Utterance → AristQuant
  | .nn | .ns | .na => .none
  | .sn | .ss | .sa => .some
  | .an | .as | .aa => .all

/-- Inner quantifier of an utterance. -/
def Utterance.inner : Utterance → AristQuant
  | .nn | .sn | .an => .none
  | .ns | .ss | .as => .some
  | .na | .sa | .aa => .all

/-! ### Alternative quantifiers

Sentential alternatives (A3a) substitute lexical alternatives per quantifier
position: `some ↔ all`, and `not all` for `none`. -/

/-- The quantifiers of sentential alternatives are the utterance quantifiers and *not all*, the
lexical alternative of *none*. -/
inductive AltQuant where
  | none | some | all | notAll
  deriving DecidableEq, Repr

instance : Coe AristQuant AltQuant where
  coe
    | .none => .none
    | .some => .some
    | .all => .all

/-- The scale-mate candidates at a quantifier position of a sentential alternative are the
quantifier itself and its lexical alternatives. -/
def AristQuant.altCandidates : AristQuant → List AltQuant
  | .none => [.none, .notAll]
  | .some => [.some, .all]
  | .all => [.all, .some]

/-! ### Compositional semantics -/

/-- An alien of a given type satisfies "drank Q" according to its place on the scale, *some*
holding above the bottom vertex and *all* at the top one. -/
def AltQuant.sat : AltQuant → Triangle → Prop
  | .none => (· = ⊥)
  | .some => (⊥ < ·)
  | .all => (· = ⊤)
  | .notAll => (· < ⊤)

instance : ∀ q : AltQuant, DecidablePred q.sat
  | .none, t => inferInstanceAs (Decidable (t = ⊥))
  | .some, t => inferInstanceAs (Decidable (⊥ < t))
  | .all, t => inferInstanceAs (Decidable (t = ⊤))
  | .notAll, t => inferInstanceAs (Decidable (t < ⊤))

/-- Quantifier denotation over the alien types realized in a world. -/
def AltQuant.eval : AltQuant → World → (Triangle → Prop) → Prop
  | .none, w, sat => ∀ t ∈ w, ¬ sat t
  | .some, w, sat => ∃ t ∈ w, sat t
  | .all, w, sat => ∀ t ∈ w, sat t
  | .notAll, w, sat => ¬ ∀ t ∈ w, sat t

instance : ∀ (q : AltQuant) (w : World) (sat : Triangle → Prop) [DecidablePred sat],
    Decidable (q.eval w sat)
  | .none, _, _, _ => inferInstanceAs (Decidable (∀ _ ∈ _, ¬ _))
  | .some, _, _, _ => inferInstanceAs (Decidable (∃ _ ∈ _, _))
  | .all, _, _, _ => inferInstanceAs (Decidable (∀ _ ∈ _, _))
  | .notAll, _, _, _ => inferInstanceAs (Decidable (¬ ∀ _ ∈ _, _))

theorem eval_notAll_iff (w : World) (sat : Triangle → Prop) :
    AltQuant.eval .notAll w sat ↔ ¬ AltQuant.eval .all w sat := Iff.rfl

theorem eval_none_iff (w : World) (sat : Triangle → Prop) :
    AltQuant.eval .none w sat ↔ ¬ AltQuant.eval .some w sat := by
  simp [AltQuant.eval]

/-- A sentential alternative is a pair of alternative quantifiers. -/
abbrev AltSentence := AltQuant × AltQuant

/-- Literal meaning of a sentential alternative. -/
def altLiteral (a : AltSentence) (w : World) : Prop := a.1.eval w a.2.sat

instance (a : AltSentence) : DecidablePred (altLiteral a) := fun _ ↦
  inferInstanceAs (Decidable (AltQuant.eval _ _ _))

/-- Literal meaning of an utterance. -/
def literalMeaning (u : Utterance) : World → Prop := altLiteral (↑u.outer, ↑u.inner)

instance (u : Utterance) : DecidablePred (literalMeaning u) :=
  inferInstanceAs (DecidablePred (altLiteral _))

/-! ### Compositional exhaustification -/

/-- The sentential alternatives at matrix position (A3a) combine the scale-mate candidates at
the two quantifier positions. -/
def matrixAlts (u : Utterance) : List AltSentence :=
  u.outer.altCandidates ×ˢ u.inner.altCandidates

/-- After EXH enrichment, when licensed, inner *some* is conjoined with its not-all implicature
and holds at the `IO` vertex exactly; Exh(none) and Exh(all) are vacuous. -/
def enrichedSat (qi : AristQuant) (p : Parse) (t : Triangle) : Prop :=
  (↑qi : AltQuant).sat t ∧ (ExhPosition.inner ∈ p ∧ qi = .some → t < ⊤)

instance (qi : AristQuant) (p : Parse) : DecidablePred (enrichedSat qi p) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The sub-matrix reading applies the in-situ enrichments, with outer EXH (Exh(some) at the
outer position) as an implication guard. -/
def subMatrix (p : Parse) (u : Utterance) (w : World) : Prop :=
  AltQuant.eval (↑u.outer) w (enrichedSat u.inner p)
  ∧ (ExhPosition.outer ∈ p ∧ u.outer = .some →
      ¬ AltQuant.eval .all w (enrichedSat u.inner p))

instance (p : Parse) (u : Utterance) : DecidablePred (subMatrix p u) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- A sentential alternative is strictly stronger than the sub-matrix reading when its literal
meaning is a proper subset of it (A3b), so an utterance's own literal meaning qualifies when a
parse weakens it, as for NS under MI. -/
def StrictlyStronger (p : Parse) (u : Utterance) (a : AltSentence) : Prop :=
  (∀ w, altLiteral a w → subMatrix p u w) ∧ ∃ w, subMatrix p u w ∧ ¬ altLiteral a w

instance (p : Parse) (u : Utterance) (a : AltSentence) :
    Decidable (StrictlyStronger p u a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The matrix-exhaustified reading is the sub-matrix reading with the literal meaning of every
strictly stronger sentential alternative negated. -/
def matrixExh (p : Parse) (u : Utterance) (w : World) : Prop :=
  subMatrix p u w ∧ ∀ a ∈ matrixAlts u, StrictlyStronger p u a → ¬ altLiteral a w

instance (p : Parse) (u : Utterance) : DecidablePred (matrixExh p u) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The exhaustified meaning under a parse is the sub-matrix reading, negating the strictly
stronger alternatives when M is in the parse and doing so is noncontradictory (eq. A2). -/
def exhMeaning (p : Parse) (u : Utterance) (w : World) : Prop :=
  subMatrix p u w ∧ (ExhPosition.matrix ∈ p ∧ (∃ w', matrixExh p u w') →
    ∀ a ∈ matrixAlts u, StrictlyStronger p u a → ¬ altLiteral a w)

instance (p : Parse) (u : Utterance) : DecidablePred (exhMeaning p u) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Truth-table verification (the paper's Table 1)

One characterization per utterance, total over all eight parses — the paper's
row-groups appear as the guards. Each reading is a membership predicate on
the world's alien-type set, not a truth vector. -/

/-- In Table 1, NN excludes N-types, and matrix parses also negate "none drank not all", which
is {wA}, the reading of fn. 7 from the alternative *not all* of *none*. -/
theorem table1_nn : ∀ (p : Parse) (w : World),
    exhMeaning p .nn w ↔ (.E ∉ w ∧ (.matrix ∈ p → w ≠ wA)) := by decide +kernel

/-- In Table 1, NS literally holds at wN alone; inner EXH weakens it to the S-free worlds,
whereupon matrix EXH negates the sentence's own now-stronger literal meaning {wN}. -/
theorem table1_ns : ∀ (p : Parse) (w : World),
    exhMeaning p .ns w ↔
      if .inner ∈ p then .IO ∉ w ∧ (.matrix ∈ p → w ≠ wN)
      else w = wN := by decide +kernel

/-- In Table 1, NA excludes A-types, and matrix EXH negates the stronger NS, which is {wN}. -/
theorem table1_na : ∀ (p : Parse) (w : World),
    exhMeaning p .na w ↔ (.A ∉ w ∧ (.matrix ∈ p → w ≠ wN)) := by decide +kernel

/-- In Table 1, SN requires an N-type, and outer or matrix EXH negates AN, which is {wN}. -/
theorem table1_sn : ∀ (p : Parse) (w : World),
    exhMeaning p .sn w ↔
      (.E ∈ w ∧ (.outer ∈ p ∨ .matrix ∈ p → w ≠ wN)) := by decide +kernel

/-- In Table 1, SS has five row-groups. Inner EXH requires an S-type, matrix EXH then being
vacuous, and adding outer EXH excludes wS; outer EXH alone keeps the mixed worlds, matrix EXH
alone pins wNS, and the literal parse excludes wN alone. -/
theorem table1_ss : ∀ (p : Parse) (w : World),
    exhMeaning p .ss w ↔
      if .inner ∈ p then .IO ∈ w ∧ (.outer ∈ p → w ≠ wS)
      else if .outer ∈ p then .E ∈ w ∧ w ≠ wN
      else if .matrix ∈ p then w = wNS
      else w ≠ wN := by decide +kernel

/-- In Table 1, SA requires an A-type, and outer or matrix EXH excludes wA. -/
theorem table1_sa : ∀ (p : Parse) (w : World),
    exhMeaning p .sa w ↔
      (.A ∈ w ∧ (.outer ∈ p ∨ .matrix ∈ p → w ≠ wA)) := by decide +kernel

/-- In Table 1, AN holds at wN alone under every parse. -/
theorem table1_an : ∀ (p : Parse) (w : World), exhMeaning p .an w ↔ w = wN := by decide +kernel

/-- In Table 1, AS excludes N-types; inner EXH pins wS, and matrix EXH without inner EXH negates
AA, excluding wA. -/
theorem table1_as : ∀ (p : Parse) (w : World),
    exhMeaning p .as w ↔
      if .inner ∈ p then w = wS
      else .E ∉ w ∧ (.matrix ∈ p → w ≠ wA) := by decide +kernel

/-- In Table 1, AA holds at wA alone under every parse. -/
theorem table1_aa : ∀ (p : Parse) (w : World), exhMeaning p .aa w ↔ w = wA := by decide +kernel

theorem literal_eq_exh_none : ∀ (u : Utterance) (w : World),
    literalMeaning u w ↔ exhMeaning ∅ u w := by decide +kernel

/-- ⟦SS⟧^M = {wNS}, the reading that "uniquely singles out this world state" in the
discussion of eq. 22 and drives GI's win; the matrix-alone case of `table1_ss`. -/
theorem m_ss_singleton : ∀ w, exhMeaning pM .ss w ↔ w = wNS := by decide +kernel

/-- The matrix operator (eq. A2) is not innocent exclusion, since at MOI its strictly-stronger
filter is empty and ⟦SS⟧^MOI keeps wSA, which innocent exclusion over the same alternatives
excludes. -/
theorem moi_ss_ne_innocent_exclusion :
    exhMeaning {.matrix, .outer, .inner} .ss wSA
      ∧ wSA ∉ Exhaustification.innocent.exh
          (Exhaustification.altsFromPreds
            ((matrixAlts .ss).map fun a w ↦ decide (altLiteral a w)))
          (Exhaustification.predToFinset
            fun w ↦ decide (exhMeaning {.outer, .inner} .ss w)) :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem exists_true : ∀ (w : World) (p : Parse), ∃ u, exhMeaning p u w := by decide +kernel

/-! ## The models -/

/-! ### The reading family and the pooled models

Each parse gives every utterance an extension, and every model is the speaker and listener of
`RSA` at a uniform prior over this family. The vanilla model (§3.1) uses the literal parse. In GI
(eq. 21a) and LI (eq. 18a) the speaker chooses an utterance together with a parse and the
listener hears the utterance, while in LU (eq. 11) the lexicon is an argument of the speaker,
who addresses that lexicon's literal listener. The weights agree, so the models differ only in
the position of the latent parameter (p. e86), and `ss_m_parse_pref` against
`perParse_ss_prefers_o` turns that difference into diverging predictions. -/

/-- The extension of an utterance under a parse. -/
def ext (p : Parse) (u : Utterance) : Finset World :=
  Finset.univ.filter (exhMeaning p u)

@[simp] theorem mem_ext {p : Parse} {u : Utterance} {w : World} :
    w ∈ ext p u ↔ exhMeaning p u w := by
  simp [ext]

/-- The literal listener under a parse (eq. 5) is uniform on the extension of the utterance. -/
noncomputable abbrev literal (p : Parse) : Kernel Utterance World :=
  RSA.listener (uniformOn Set.univ) (RSA.truthful fun u ↦ (ext p u : Set World))

/-- The speaker under a parse (eq. 7) knows the world and addresses that parse's literal
listener. -/
noncomputable abbrev speaker (p : Parse) (α : ℝ) : Kernel World Utterance :=
  RSA.speaker α 0 (literal p) Measure.dirac

/-- The vanilla listener (eq. 9) inverts the speaker of the literal parse. -/
noncomputable abbrev vanillaListener (α : ℝ) : Kernel Utterance World :=
  RSA.listener (uniformOn Set.univ) (speaker ∅ α)

/-- The GI choice space (eq. 21a) consists of utterance–parse pairs over the full reading family,
heard as the utterance. -/
def giSem (cl : Utterance × Parse) : Finset World := ext cl.2 cl.1

/-- The GI speaker (eq. 21a) chooses an utterance together with a parse. -/
noncomputable abbrev giSpeaker (α : ℝ) : Kernel World (Utterance × Parse) :=
  RSA.speaker α 0 (RSA.listener (uniformOn Set.univ) (RSA.truthful fun c ↦ (giSem c : Set World)))
    Measure.dirac

/-- The GI listener (eq. 21b) hears the utterance of the speaker's choice and infers the world
and the choice. -/
noncomputable abbrev giJointListener (α : ℝ) : Kernel Utterance (World × Utterance × Parse) :=
  RSA.listener (uniformOn Set.univ ⊗ₘ giSpeaker α) fun p ↦ Measure.dirac p.2.1

/-- The GI listener marginalized to worlds. -/
noncomputable abbrev giListener (α : ℝ) : Kernel Utterance World := (giJointListener α).fst

/-- The GI listener marginalized to the speaker's choice of utterance and parse. -/
noncomputable abbrev giParsePosterior (α : ℝ) : Kernel Utterance (Utterance × Parse) :=
  (giJointListener α).snd

/-- An LI parse is lit, I, O or OI, matrix-EXH parses being unavailable. -/
inductive LIParse where
  | lit | i | o | oi
  deriving DecidableEq, Repr, Fintype

instance : Nonempty LIParse := ⟨.lit⟩
instance : MeasurableSpace LIParse := ⊤
instance : DiscreteMeasurableSpace LIParse := ⟨fun _ ↦ trivial⟩

/-- Map LI parse to the full parse space. -/
def LIParse.toParse : LIParse → Parse
  | .lit => ∅
  | .i => {.inner}
  | .o => {.outer}
  | .oi => {.outer, .inner}

theorem li_excludes_matrix : ∀ l : LIParse, .matrix ∉ l.toParse := by decide +kernel

/-- The LI choice space (eq. 18a) consists of pairs over the matrix-free parses. -/
def liSem (cl : Utterance × LIParse) : Finset World := ext cl.2.toParse cl.1

/-- The LI speaker (eq. 18a) chooses an utterance together with a matrix-free parse. -/
noncomputable abbrev liSpeaker (α : ℝ) : Kernel World (Utterance × LIParse) :=
  RSA.speaker α 0 (RSA.listener (uniformOn Set.univ) (RSA.truthful fun c ↦ (liSem c : Set World)))
    Measure.dirac

/-- The LI listener (eq. 18b), marginalized to worlds. -/
noncomputable abbrev liListener (α : ℝ) : Kernel Utterance World :=
  (RSA.listener (uniformOn Set.univ ⊗ₘ liSpeaker α) fun p ↦ Measure.dirac p.2.1).fst

/-! ### Lexical uncertainty: the latent as a speaker argument -/

/-- An LU lexicon is literal or OI, with inner and outer EXH. Each speaker has a fixed lexicon,
and the listener marginalizes over the two lexica. -/
inductive LULex where
  | lit | oi
  deriving DecidableEq, Repr, Fintype

instance : Nonempty LULex := ⟨.lit⟩
instance : MeasurableSpace LULex := ⊤
instance : DiscreteMeasurableSpace LULex := ⟨fun _ ↦ trivial⟩

/-- Map LU lexicon to the corresponding parse. -/
def LULex.toParse : LULex → Parse
  | .lit => ∅
  | .oi => {.outer, .inner}

theorem lu_excludes_matrix : ∀ l : LULex, .matrix ∉ l.toParse := by decide +kernel

/-- The LU listener (eqs. 12–13) inverts the speaker of eq. 11, who has a fixed lexicon, at a
uniform prior over worlds and lexica. -/
noncomputable def luListener (α : ℝ) : Kernel Utterance (World × LULex) :=
  RSA.listener (uniformOn Set.univ) fun p ↦ speaker p.2.toParse α p.1

/-! ### The rejected architecture: per-parse normalization -/

/-- The architecture the paper rejects as "conceptually highly implausible" (p. e85) takes the
full parse family with the parse as a speaker argument, eq. 11 with an enlarged latent set rather
than the pooled choice of eq. 21a. Its listener inverts the per-parse speaker at a uniform prior
over worlds and parses. -/
noncomputable def perParseListener (α : ℝ) : Kernel Utterance (World × Parse) :=
  RSA.listener (uniformOn Set.univ) fun p ↦ speaker p.2 α p.1

/-! ## The findings -/

/-! ### Exhaustified interpretation -/

theorem ss_inner_exh :
    (giListener 5 .ss).real {wNSA} < (giListener 5 .ss).real {wNS} :=
  RSA.listener_compProd_speaker_uniformOn_fst_real_lt_of_divPowSum giSem Prod.fst (k := 5)
    (D := 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (giListener α .ss).real {wS} < (giListener α .ss).real {wNS} :=
  RSA.listener_compProd_speaker_uniformOn_fst_real_lt_of_strictDominates giSem Prod.fst hα
    (by decide +kernel)

theorem aa_identifies {α : ℝ} (hα : 0 < α) :
    (giListener α .aa).real {wSA} < (giListener α .aa).real {wA} :=
  RSA.listener_compProd_speaker_uniformOn_fst_real_lt_of_strictDominates giSem Prod.fst hα
    (by decide +kernel)

theorem as_inner_exh {α : ℝ} (hα : 0 < α) :
    (giListener α .as).real {wA} < (giListener α .as).real {wS} :=
  RSA.listener_compProd_speaker_uniformOn_fst_real_lt_of_strictDominates giSem Prod.fst hα
    (by decide +kernel)

/-! ### The model comparison -/

/-- Hearing "some of the aliens drank some of their water", the
literal-semantics listener favors all-drinkers over some-but-not-all
drinkers — opposite to the attested preference. -/
theorem vanilla_ss_prefers_wNA {α : ℝ} (hα : 0 < α) :
    (vanillaListener α .ss).real {wNS} < (vanillaListener α .ss).real {wNA} :=
  RSA.listener_speaker_uniformOn_real_singleton_lt_of_strictDominates (ext ∅) hα
    (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the pooled
listener favors some-but-not-all drinkers over all-drinkers, as attested. -/
theorem gi_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (giListener α .ss).real {wNA} < (giListener α .ss).real {wNS} :=
  RSA.listener_compProd_speaker_uniformOn_fst_real_lt_of_strictDominates giSem Prod.fst hα
    (by decide +kernel)

theorem li_ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (liListener α .ss).real {wS} < (liListener α .ss).real {wNS} :=
  RSA.listener_compProd_speaker_uniformOn_fst_real_lt_of_strictDominates liSem Prod.fst hα
    (by decide +kernel)

theorem li_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (liListener α .ss).real {wNA} < (liListener α .ss).real {wNS} :=
  RSA.listener_compProd_speaker_uniformOn_fst_real_lt_of_strictDominates liSem Prod.fst hα
    (by decide +kernel)

theorem lu_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (luListener α .ss).fst.real {wNA} < (luListener α .ss).fst.real {wNS} := by
  rw [luListener, RSA.listener_fst_real_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
    uniformOn_univ_singleton_ne_zero]
  calc (∑ l : LULex, (speaker l.toParse α wNA).real {.ss})
      = (speaker ∅ α wNA).real {.ss} :=
        Fintype.sum_eq_single LULex.lit fun
          | .lit, hl => absurd rfl hl
          | .oi, _ => RSA.speaker_listener_truthful_dirac_real_singleton_eq_zero hα _ _ _
              (by decide +kernel : wNA ∉ ext LULex.oi.toParse .ss)
    _ < (speaker LULex.oi.toParse α wNS).real {.ss} := by
        rw [RSA.speaker_uniformOn_dirac_real_singleton_of_profile_replicate
          (ext LULex.oi.toParse) hα (by decide +kernel :
            RSA.profile (ext LULex.oi.toParse) Finset.univ wNS = Multiset.replicate 3 3)
          (by decide +kernel : wNS ∈ ext LULex.oi.toParse .ss)]
        have hsum := RSA.sum_speaker_real_singleton_le_one α 0 (literal ∅) Measure.dirac wNA
          {.ss, .sn, .sa}
        rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at hsum
        have hsn := RSA.speaker_uniformOn_dirac_real_singleton_lt_of_card_lt (ext ∅) hα
          (by decide +kernel : wNA ∈ ext ∅ .ss) (by decide +kernel : wNA ∈ ext ∅ .sn)
          (by decide +kernel)
        have hsa := RSA.speaker_uniformOn_dirac_real_singleton_lt_of_card_lt (ext ∅) hα
          (by decide +kernel : wNA ∈ ext ∅ .ss) (by decide +kernel : wNA ∈ ext ∅ .sa)
          (by decide +kernel)
        linarith
    _ ≤ ∑ l : LULex, (speaker l.toParse α wNS).real {.ss} :=
        Finset.single_le_sum
          (fun l _ ↦ measureReal_nonneg (μ := speaker l.toParse α wNS))
          (Finset.mem_univ LULex.oi)

/-! ### The position of the latent parameter -/

/-- Hearing "some of the aliens drank some of their water", the pooled
listener's parse posterior peaks at exhaustification of the whole
sentence. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ pM →
    (giParsePosterior 5 .ss).real {(.ss, p)} < (giParsePosterior 5 .ss).real {(.ss, pM)} :=
  fun p _ ↦
  RSA.listener_compProd_speaker_uniformOn_snd_real_lt_of_divPowSum giSem Prod.fst (k := 5)
    (D := 12) (by decide +kernel) rfl rfl (by revert p; decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the per-parse
listener favors exhaustifying the outer quantifier over exhaustifying the
whole sentence. -/
theorem perParse_ss_prefers_o {α : ℝ} (hα : 0 < α) :
    (perParseListener α .ss).snd.real {pM} < (perParseListener α .ss).snd.real {pO} := by
  have hOprof : ∀ w ∈ ({wNS, wNA, wNSA} : Finset World),
      RSA.profile (ext pO) Finset.univ w = Multiset.replicate 3 3 := by decide +kernel
  have hOmem : ∀ w ∈ ({wNS, wNA, wNSA} : Finset World), w ∈ ext pO .ss := by decide +kernel
  rw [perParseListener, RSA.listener_snd_real_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
    uniformOn_univ_singleton_ne_zero]
  calc (∑ w : World, (speaker pM α w).real {.ss})
      = (speaker pM α wNS).real {.ss} :=
        Fintype.sum_eq_single wNS fun w hw ↦
          RSA.speaker_listener_truthful_dirac_real_singleton_eq_zero hα _ _ _ fun hmem ↦
            hw ((m_ss_singleton w).mp (mem_ext.mp hmem))
    _ < 1 :=
        RSA.speaker_real_singleton_lt_one (nofun : Utterance.sn ≠ Utterance.ss)
          ((RSA.speaker_uniformOn_dirac_apply_singleton_ne_zero_iff (ext pM) hα 0 wNS .sn).2
            (by decide +kernel))
    _ = ∑ w ∈ ({wNS, wNA, wNSA} : Finset World), (speaker pO α w).real {.ss} := by
        rw [Finset.sum_eq_card_nsmul fun w hw ↦
            RSA.speaker_uniformOn_dirac_real_singleton_of_profile_replicate (ext pO) hα
              (hOprof w hw) (hOmem w hw),
          show ({wNS, wNA, wNSA} : Finset World).card = 3 from by decide +kernel]
        norm_num
    _ ≤ ∑ w : World, (speaker pO α w).real {.ss} :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun w _ _ ↦ measureReal_nonneg

end FrankeBergen2020
