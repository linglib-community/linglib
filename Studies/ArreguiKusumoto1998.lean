module

public import Linglib.Data.Examples.ArreguiKusumoto1998
public import Linglib.Fragments.Japanese.TemporalConnectives
public import Linglib.Semantics.Composition.Tree
public import Linglib.Semantics.Tense.Embedding
public import Linglib.Semantics.Tense.Quantificational
public import Linglib.Semantics.Tense.RunTimes
public import Linglib.Data.Examples.Readers

/-!
# Arregui and Kusumoto (1998): Tense in Temporal Adjunct Clauses

Japanese *mae* 'before' takes a present clause and *ato* 'after' a past one, while English and
Polish *before*- and *after*-clauses take the past. Ogihara's relative-tense account has the
adjunct tense order its event against the matrix event, in agreement with the connective, unless
the sequence-of-tense rule deletes it. Arregui and Kusumoto object that Polish has no such rule
and patterns with English, and that a Japanese *toki* 'when'-clause takes the past. For them the
past tense is Prior's operator and the present a variable. English and Polish adjuncts and
Japanese past *when*-clauses are relative clauses over times, whose past is evaluated at the
speech time, and *mae* and *ato* select a tensed clause directly, *mae* being stipulated to bind
a variable. The logical forms are interpreted by Heim and Kratzer's type-driven composition,
which gives a past under *mae* and a present under *ato* no denotation.

## Implementation notes

* A time is an interval of moments, with precedence and inclusion. The entity type of the
  composition engine is the type of times, so its type `e` is the paper's type of times.
* An attitude verb comes with its subject and takes the property of times its complement
  denotes, as *say* does in the paper's sketch of the sequence-of-tense rule.
* The downstairs reading of an adjunct that embeds a clause is identified by the *at*-phrase of
  the relative pronoun, which a selected clause lacks.
* The *when* of the habitual logical form, a node with no denotation of its own, is left out.

## TODO

* The paper stars the present in Polish *before*- and *after*-clauses and the future in Polish
  *before*-clauses without deriving the judgments, and assigns Polish tenses no entries;
  `not_holds_present_relative` and `holds_before_present_relative` give what the entries of
  English and Japanese would entail for the present.
* The habitual present of Japanese relative clauses over places and people is observed and not
  derived.

## References

* [arregui-kusumoto-1998]
* [ogihara-1989]
* [ogihara-1994]
* [ogihara-1996]
* [geis-1970]
* [larson-1990]
* [prior-1967]
* [partee-1973]
* [anscombe-1964]
* [ogihara-1995b]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace ArreguiKusumoto1998

open Montague PhraseStructure.Tree PhraseStructure ModalLogic Tense
open scoped Denotes
open Japanese.TemporalConnectives (mae ato toki)
open scoped SetRel

/-! ### The fragment -/

/-- The words of the fragment are the tenseless verb phrases and the attitude verbs, each
numbered, the past tense, the speech time, the preposition *at*, *before*, *after* and the
covert adverb of quantification. -/
inductive Word
  | vp (k : ℕ)
  | attitude (k : ℕ)
  | past | speechTime | at_ | before | after | adverb
  deriving DecidableEq

/-- A logical form is a binary tree of words, traces and binders. -/
abbrev LF := Tree Unit Word

/-- A model gives the times each verb phrase holds at, the times each attitude verb holds at
given the times of its complement, and the speech time. -/
structure Model (T : Type) [LinearOrder T] where
  /-- The times at which the verb phrase of a number holds. -/
  vp : ℕ → NonemptyInterval T → Prop
  /-- The times at which the attitude verb of a number holds of a property of times. -/
  attitude : ℕ → (NonemptyInterval T → Prop) → NonemptyInterval T → Prop
  /-- The speech time. -/
  speechTime : NonemptyInterval T

variable {T : Type} [LinearOrder T] {M : Model T} {X : NonemptyInterval T → Prop}
  {t : NonemptyInterval T} {k l : ℕ}

/-- *Before* (19) holds of the times that precede every time of its clause. -/
def before (X : NonemptyInterval T → Prop) (t : NonemptyInterval T) : Prop :=
  ∀ t', X t' → t.Precedes t'

/-- The semantic type of a word. -/
def Word.ty : Word → Ty
  | .vp _ => .e ⇒ .t
  | .attitude _ | .past | .after | .before => (.e ⇒ .t) ⇒ .e ⇒ .t
  | .speechTime => .e
  | .at_ => .e ⇒ .e ⇒ .t
  | .adverb => (.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .e ⇒ .t

/-- The denotation of a word in a model. The past tense is Prior's operator (13), whose
denotation *after* shares (19), *at* identifies two times, and the adverb of quantification
(34c) holds of a time when each time of its restrictor within it contains a time of its
scope. -/
def Model.denote (M : Model T) : (w : Word) → Ty.Domain (NonemptyInterval T) Unit w.ty
  | .vp k => M.vp k
  | .attitude k => M.attitude k
  | .past | .after => ◇[Allen.toSetRel Allen.precedes]
  | .before => before
  | .speechTime => M.speechTime
  | .at_ => fun t' t ↦ t = t'
  | .adverb => fun X Y t ↦ ∀ t' ≤ t, X t' → ∃ t'' ≤ t', Y t''

/-- The lexicon of a model gives each word its type and its denotation. -/
def Model.lex (M : Model T) (w : Word) : Option (Denotation (NonemptyInterval T) Unit) :=
  some ⟨w.ty, M.denote w⟩

/-- A logical form is interpretable when type-driven composition gives it a type. -/
def Interpretable (lf : LF) : Prop := (ty? individualIndices (fun w ↦ some w.ty) lf).isSome

instance : DecidablePred Interpretable := fun _ ↦ inferInstanceAs (Decidable (_ = true))

theorem interpretable_iff (M : Model T) (g : Assignment (NonemptyInterval T)) (lf : LF) :
    Interpretable lf ↔ (interp M.lex g lf).isSome :=
  Bool.eq_iff_iff.1 (isSome_interp (lex := M.lex) (fun _ ↦ rfl) g lf).symm

/-- A logical form is true in a model when it composes to a true truth value, its free
variables denoting the speech time, as an unbound tense variable does (12). -/
def Model.Holds (M : Model T) (lf : LF) : Prop :=
  valueAt (M := Id) .t False (interp M.lex (fun _ ↦ M.speechTime) lf)

/-- The extension of a logical form in a model is the set of times it composes to, its free
variables denoting the speech time. -/
def Model.extension (M : Model T) (lf : LF) : NonemptyInterval T → Prop :=
  valueAt (M := Id) (.e ⇒ .t) (fun _ ↦ False) (interp M.lex (fun _ ↦ M.speechTime) lf)

/-! ### Before and after -/

theorem before_iff_not_diamond :
    before X t ↔ ¬ ◇[Allen.toSetRel (Allen.ofPosition ⟦future⟧ᶜ)] X t := by
  simp only [before, Diamond, Allen.mem_toSetRel, Allen.relation_mem_ofPosition,
    Finset.mem_compl, denote_future, Finset.mem_singleton, NonemptyInterval.position_eq_gt,
    not_exists, not_and]
  exact forall_congr' fun _ ↦ not_imp_not.symm

-- (18a)
theorem before_of_forall_not (h : ∀ t', ¬ X t') (t : NonemptyInterval T) : before X t :=
  fun t' ht' ↦ absurd ht' (h t')

/-- A time of one clause before another clause puts the first before ever the second, the
universal *before* of Anscombe. -/
theorem beforeEver_of_before {A B : Set (NonemptyInterval T)} (ht : t ∈ A)
    (h : before (· ∈ B) t) : beforeEver A B :=
  ⟨t.snd, ⟨t, ht, t.fst_le_snd, le_rfl⟩, fun _ ⟨t', ht', h'⟩ ↦ (h t' ht').trans_le h'.1⟩

/-- Anscombe's *before ever* does not imply the interval *before* of (19). -/
theorem not_forall_before_of_beforeEver :
    ¬ ∀ A B : Set (NonemptyInterval ℤ), beforeEver A B → ∃ t ∈ A, before (· ∈ B) t := by
  intro h
  obtain ⟨_, rfl, ht⟩ := h {⟨(1, 5), by decide⟩} {⟨(3, 8), by decide⟩}
    ⟨1, by simp [NonemptyInterval.mem_def], fun _ ht' ↦ by
      simp only [timeTrace_singleton, SetLike.mem_coe, NonemptyInterval.mem_def] at ht'
      omega⟩
  exact absurd (ht _ rfl) (by decide)

/-! ### Tense as operator and as variable -/

/-- The past tense is an operator on properties of times (13). -/
def pastOperator : LF := .leaf .past

/-- The present tense is a variable over times (12), here of index 0. -/
def presentVariable : LF := .tr 0

/-- A root or relative clause of tense `τ` over a verb phrase. A tense variable saturates the
verb phrase (12b), and with an operator the speech time in C saturates the tensed clause
(13b). -/
def clause : LF → LF → LF
  | .tr i, vp => .bin (.tr i) vp
  | τ, vp => .bin (.leaf .speechTime) (.bin τ vp)

-- (12)
theorem holds_present : M.Holds (clause presentVariable (.leaf (.vp k))) ↔ M.vp k M.speechTime :=
  .rfl

-- (13)
theorem holds_past :
    M.Holds (clause pastOperator (.leaf (.vp k))) ↔ ∃ t, t.Precedes M.speechTime ∧ M.vp k t :=
  Allen.diamond_toSetRel_precedes

theorem not_interpretable_speechTime_present :
    ¬ Interpretable (.bin (.leaf .speechTime) (.bin presentVariable (.leaf (.vp k)))) :=
  Bool.false_ne_true

/-! ### Relative-clause adjuncts -/

/-- A verb phrase modified by *at* and the trace of the relative pronoun, of index 1 (16b). -/
def atTrace (vp : LF) : LF := .bin vp (.bin (.leaf .at_) (.tr 1))

/-- A relative clause over times, in which the relative pronoun binds its trace in a clause of
tense `τ` (16b). -/
def relative (τ vp : LF) : LF := .binder 1 (clause τ vp)

/-- A past matrix clause whose verb phrase a temporal adjunct modifies (17). -/
def matrix (vp adjunct : LF) : LF := clause pastOperator (.bin vp adjunct)

attribute [local simp] Model.Holds Model.extension Model.lex Model.denote Word.ty clause relative
  atTrace matrix pastOperator presentVariable

-- (16b)
theorem extension_relative :
    M.extension (relative pastOperator (atTrace (.leaf (.vp k)))) t ↔
      t.Precedes M.speechTime ∧ M.vp k t := by
  simp [Diamond]

-- (24)
theorem holds_after_relative :
    M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .after) (relative pastOperator (atTrace (.leaf (.vp l)))))) ↔
      ∃ t, t.Precedes M.speechTime ∧ M.vp k t ∧
        ∃ t', t'.Precedes M.speechTime ∧ M.vp l t' ∧ t'.Precedes t := by
  simp [Diamond, and_comm, and_left_comm]

-- (25)
theorem holds_before_relative :
    M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .before) (relative pastOperator (atTrace (.leaf (.vp l)))))) ↔
      ∃ t, t.Precedes M.speechTime ∧ M.vp k t ∧
        ∀ t', t'.Precedes M.speechTime → M.vp l t' → t.Precedes t' := by
  simp [Diamond, before]

-- (33)
theorem holds_when_relative :
    M.Holds (matrix (.leaf (.vp k)) (relative pastOperator (atTrace (.leaf (.vp l))))) ↔
      ∃ t, t.Precedes M.speechTime ∧ M.vp k t ∧ M.vp l t := by
  simp [Diamond, and_left_comm]

-- (18b)
theorem exists_of_holds_after :
    M.Holds (matrix (.leaf (.vp k))
      (.bin (.leaf .after) (relative pastOperator (atTrace (.leaf (.vp l)))))) →
    ∃ t, M.vp l t := by
  rw [holds_after_relative]
  rintro ⟨_, _, _, t', _, h', _⟩
  exact ⟨t', h'⟩

-- (18a)
theorem holds_before_of_forall_not (h : ∀ t, ¬ M.vp l t) :
    M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .before) (relative pastOperator (atTrace (.leaf (.vp l)))))) ↔
      M.Holds (clause pastOperator (.leaf (.vp k))) := by
  simp [Diamond, before, h]

-- (34)
theorem not_holds_present_relative :
    ¬ M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .after) (relative presentVariable (atTrace (.leaf (.vp l)))))) ∧
      ¬ M.Holds (matrix (.leaf (.vp k)) (relative presentVariable (atTrace (.leaf (.vp l))))) := by
  simp +contextual [Diamond, NonemptyInterval.precedes_asymm, NonemptyInterval.precedes_irrefl]

theorem holds_before_present_relative :
    M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .before) (relative presentVariable (atTrace (.leaf (.vp l)))))) ↔
      M.Holds (clause pastOperator (.leaf (.vp k))) := by
  have key (p q r : Prop) : p ∧ q ∧ (r → p) ↔ p ∧ q := by grind
  simp [Diamond, before, key]

/-! ### Connectives that select a tensed clause -/

/-- On dense time, *after* absorbs the past operator of its clause, giving the form at the root of
(27). -/
theorem extension_after_past [DenselyOrdered T] :
    M.extension (.bin (.leaf .after) (.bin pastOperator (.leaf (.vp k)))) t ↔
      ∃ t', t'.Precedes t ∧ M.vp k t' := by
  simp [↓Allen.diamond_precedes_diamond_precedes]

theorem not_extension_after_past_int :
    ∃ (M : Model ℤ) (t : NonemptyInterval ℤ), (∃ t', t'.Precedes t ∧ M.vp 0 t') ∧
      ¬ M.extension (.bin (.leaf .after) (.bin pastOperator (.leaf (.vp 0)))) t := by
  have key (t' : NonemptyInterval ℤ) (h : t'.snd < 1) : ¬ 0 < t'.fst := by
    have := t'.fst_le_snd
    omega
  exact ⟨⟨fun _ t ↦ t = .pure 0, fun _ X ↦ X, .pure 0⟩, .pure 1, ⟨.pure 0, by decide, rfl⟩,
    by simpa [Diamond, NonemptyInterval.Precedes] using key⟩

-- (30)
theorem extension_before_present :
    M.extension (.bin (.leaf .before) (.binder 0 (.bin presentVariable (.leaf (.vp k))))) =
      before (M.vp k) :=
  rfl

/-- The present composes under *before* and the past under *after*, but not conversely ((5a), (6b)).
-/
theorem interpretable_selected :
    Interpretable (.bin (.leaf .before) (.binder 0 (.bin presentVariable (.leaf (.vp k))))) ∧
      ¬ Interpretable (.bin (.leaf .before) (.binder 0 (.bin pastOperator (.leaf (.vp k))))) ∧
      Interpretable (.bin (.leaf .after) (.bin pastOperator (.leaf (.vp k)))) ∧
      ¬ Interpretable (.bin (.leaf .after) (.bin presentVariable (.leaf (.vp k)))) :=
  ⟨rfl, Bool.false_ne_true, rfl, Bool.false_ne_true⟩

-- (28)
theorem holds_after_selected [DenselyOrdered T] :
    M.Holds (matrix (.leaf (.vp k)) (.bin (.leaf .after) (.bin pastOperator (.leaf (.vp l))))) ↔
      ∃ t, t.Precedes M.speechTime ∧ M.vp k t ∧ ∃ t', t'.Precedes t ∧ M.vp l t' := by
  simp [↓Allen.diamond_precedes_diamond_precedes, Diamond]

-- (29)
theorem holds_before_selected :
    M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .before) (.binder 0 (.bin presentVariable (.leaf (.vp l)))))) ↔
      ∃ t, t.Precedes M.speechTime ∧ M.vp k t ∧ ∀ t', M.vp l t' → t.Precedes t' := by
  simp [Diamond, before]

-- (24), (28)
theorem holds_after_relative_iff_selected [DenselyOrdered T] :
    M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .after) (relative pastOperator (atTrace (.leaf (.vp l)))))) ↔
      M.Holds (matrix (.leaf (.vp k))
        (.bin (.leaf .after) (.bin pastOperator (.leaf (.vp l))))) := by
  rw [holds_after_relative, holds_after_selected]
  exact exists_congr fun t ↦ and_congr_right fun ht ↦ and_congr_right fun _ ↦
    exists_congr fun t' ↦ ⟨fun h ↦ ⟨h.2.2, h.2.1⟩,
      fun h ↦ ⟨NonemptyInterval.precedes_trans h.1 ht, h.2, h.1⟩⟩

/-! ### The ambiguity of an adjunct that embeds a clause -/

/-- In the paper's scenario for *I encountered Satoshi when you said he had left* (14), you said
at three that Satoshi left at ten. Times are hours of the day, and the speech time, which the
paper leaves open, is put at eight in the evening. -/
def amherst : Model ℤ where
  vp _ t := t = .pure 10
  attitude _ X t := t = .pure 15 ∧ X t
  speechTime := .pure 20

-- (15a), (15b)
theorem extension_upstairs_downstairs :
    let upstairs := relative pastOperator
      (atTrace (.bin (.leaf (.attitude 0)) (.bin pastOperator (.leaf (.vp 0)))))
    let downstairs := relative pastOperator
      (.bin (.leaf (.attitude 0)) (.bin pastOperator (atTrace (.leaf (.vp 0)))))
    (amherst.extension upstairs (.pure 15) ∧ ¬ amherst.extension upstairs (.pure 10)) ∧
      amherst.extension downstairs (.pure 10) ∧ ¬ amherst.extension downstairs (.pure 15) := by
  simp [amherst, Diamond, NonemptyInterval.Precedes]

theorem mem_freeIndices_selected :
    1 ∈ Tree.freeIndices (.bin (.leaf .after) (.bin pastOperator
      (.bin (.leaf (.attitude k)) (.bin pastOperator (atTrace (.leaf (.vp l))))))) := by
  simp [Tree.freeIndices_phrase]

/-! ### The present of a when-clause -/

/-- The covert adverb of quantification with its restrictor, a clause of tense `τ` over whose
tense variable the adverb abstracts (34c). -/
def quantificational (τ vp : LF) : LF := .bin (.leaf .adverb) (.binder 0 (.bin τ vp))

-- (34)
theorem holds_whenever :
    M.Holds (matrix (.leaf (.vp k)) (quantificational presentVariable (.leaf (.vp l)))) ↔
      ∃ t, t.Precedes M.speechTime ∧ ∀ t' ≤ t, M.vp l t' → ∃ t'' ≤ t', M.vp k t'' :=
  Allen.diamond_toSetRel_precedes

-- (34b)
theorem holds_whenever_of_forall_not (ht : t.Precedes M.speechTime)
    (h : ∀ t' ≤ t, ¬ M.vp l t') :
    M.Holds (matrix (.leaf (.vp k)) (quantificational presentVariable (.leaf (.vp l)))) :=
  holds_whenever.2 ⟨t, ht, fun t' ht' hl ↦ absurd hl (h t' ht')⟩

/-! ### Languages -/

/-- The tense parameters of a language. -/
structure Language where
  /-- The language has the sequence-of-tense rule. -/
  sot : Bool
  /-- The positions the present admits against its evaluation time. -/
  present : Finset Ordering
  /-- The relations whose connectives select a tensed clause, where a connective otherwise takes
  a relative clause over times. -/
  tensed : Finset Connective.Relation

/-- English has the sequence-of-tense rule, and its adjuncts are relative clauses. -/
def english : Language where
  sot := true
  present := ⟦present⟧
  tensed := ∅

/-- Polish has no sequence-of-tense rule, and its adjuncts are relative clauses. -/
def polish : Language where
  sot := false
  present := ⟦present⟧
  tensed := ∅

/-- Japanese has no sequence-of-tense rule and a present with a future interpretation (fn. 1),
and its *before* and *after*, *mae* and *ato*, select a tensed clause (p. 12). -/
def japanese : Language where
  sot := false
  present := nonpast
  tensed := {.before, .after}

/-- The positions a tense of a language admits against its evaluation time. -/
def Language.cell (L : Language) : Tense → Finset Ordering
  | .present => L.present
  | τ => ⟦τ⟧

/-- The adjunct of a temporal relation over a verb phrase in the tense `τ`. A *when*-clause in a
tense variable restricts the adverb of quantification that binds the variable, the form the
paper gives the Japanese present (34c), and is otherwise a relative clause over times (16). The
clause of *before* and *after* is a relative clause (23) unless their connective selects a tensed
clause (27), over whose tense variable *before*, bearing a binder index, abstracts (30). -/
def Language.adjunct (L : Language) : Connective.Relation → LF → LF → Option LF
  | .when_, .tr i, vp => some (quantificational (.tr i) vp)
  | .when_, τ, vp => some (relative τ (atTrace vp))
  | .before, τ, vp => some (.bin (.leaf .before)
      (if .before ∈ L.tensed then .binder 0 (.bin τ vp) else relative τ (atTrace vp)))
  | .after, τ, vp => some (.bin (.leaf .after)
      (if .after ∈ L.tensed then .bin τ vp else relative τ (atTrace vp)))
  | _, _, _ => none

/-- The tense heads the paper analyses, the past an operator and the present a variable. The
Polish future has none. -/
def head? : Tense → Option LF
  | .past => some pastOperator
  | .present => some presentVariable
  | .future => none

/-- A past or present clause under *mae*, *ato* or *toki* composes exactly when the connective
admits that tense ((5), (6), (31a), (31b)). -/
theorem interpretable_iff_tense :
    ∀ c ∈ [mae, ato, toki], ∀ τ ∈ [Tense.past, .present], ∀ h ∈ head? τ,
      ∀ lf ∈ japanese.adjunct c.relation h (.leaf (.vp 0)),
        (Interpretable lf ↔ ∀ τ' ∈ c.tense, τ' = τ) := by
  decide

/-! ### The relative-tense account -/

/-- The positions a temporal relation admits for the adjunct event against the matrix event. -/
def adjunctCell? : Connective.Relation → Option (Finset Ordering)
  | .before => some ⟦future⟧
  | .after => some ⟦past⟧
  | .when_ => some ⟦present⟧
  | _ => none

/-- On the relative-tense account a tense in an adjunct under a past locates the adjunct event
against the matrix event, in a position the connective, of cell `c`, must admit, unless it is a
past that the sequence-of-tense rule deletes. -/
def Language.RelativeTense (L : Language) (c : Finset Ordering) (τ : Tense) : Prop :=
  L.sot ∧ τ = .past ∨ (L.cell τ ⊓ c).Nonempty

instance (L : Language) (c : Finset Ordering) (τ : Tense) : Decidable (L.RelativeTense c τ) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The relative-tense account also derives the tenses of *mae* and *ato*, though not the past of
*toki* (31a). -/
theorem relativeTense_iff_tense :
    ∀ c ∈ [mae, ato], ∀ τ ∈ [Tense.past, .present], ∃ cell ∈ adjunctCell? c.relation,
      (japanese.RelativeTense cell τ ↔ ∀ τ' ∈ c.tense, τ' = τ) := by
  decide

/-! ### The examples -/

/-- The languages of the example rows. -/
def languages : List (String × Language) :=
  [("stan1293", english), ("poli1260", polish), ("nucl1643", japanese)]

/-- The temporal relations of the adjuncts of the example rows. -/
def relations : List (String × Connective.Relation) :=
  [("before", .before), ("after", .after), ("when", .when_)]

/-- The tenses of the example rows. -/
def tenses : List (String × Tense) := [("past", .past), ("present", .present), ("future", .future)]

/-- The readings of a complement tense, by the position of its event against the matrix event. -/
def positions : List (String × Ordering) :=
  [("shifted", .lt), ("simultaneous", .eq), ("posterior", .gt)]

-- (1), (4), (10)
theorem complement_readings :
    ∀ r ∈ Examples.all, r.feature? "clause" = some "complement" →
      ∃ L ∈ languages.lookup r.language, ∃ τ ∈ r.parse? "embeddedTense" tenses, ∀ p ∈ positions,
        (r.readings.lookup p.1 = some .acceptable →
          p.2 ∈ if τ = .past then pastUnderPast L.sot else L.cell τ) ∧
        (τ = .past → p.2 ∈ pastUnderPast L.sot → r.readings.lookup p.1 = some .acceptable) := by
  decide

-- (5a), (6b), (11c), (11b), fn. 3
theorem judgment_iff_interpretable :
    ∀ r ∈ Examples.all, ∀ rel ∈ r.parse? "clause" relations,
      ∀ τ ∈ r.parse? "embeddedTense" tenses, ∀ h ∈ head? τ, ∃ L ∈ languages.lookup r.language,
        ∃ lf ∈ L.adjunct rel h (.leaf (.vp 0)),
          ((r.judgment = .acceptable ↔ Interpretable lf) ↔
            ¬ (τ = .present ∧ rel ≠ .when_ ∧ rel ∉ L.tensed)) := by
  decide

/-- The relative-tense account gives each adjunct's judgment except, without sequence of tense, past
*when*- and relative *before*-clauses ((8), (32), (11a), (22b)) and the future (11c), and admits (9)
without its habitual reading. -/
theorem judgment_iff_relativeTense :
    ∀ r ∈ Examples.all, ∀ rel ∈ r.parse? "clause" relations,
      ∃ τ ∈ r.parse? "embeddedTense" tenses, ∃ L ∈ languages.lookup r.language,
        ∃ c ∈ adjunctCell? rel,
          ((r.judgment = .acceptable ↔ L.RelativeTense c τ) ↔
            ¬ (¬ L.sot ∧ (τ = .past ∧ (rel = .when_ ∨ rel = .before ∧ rel ∉ L.tensed) ∨
              τ = .future))) := by
  decide

/-- No sequence-of-tense setting lets the relative-tense account derive both the shifted-only Polish
past complement (10b) and the Polish past *before*-clause (11a). -/
theorem not_exists_sot_polish :
    ¬ ∃ sot : Bool,
      (Examples.ex_10b.readings.lookup "simultaneous" = some .acceptable ↔
        .eq ∈ pastUnderPast sot) ∧
      (Examples.ex_11a.judgment = .acceptable ↔
        ({ polish with sot := sot } : Language).RelativeTense ⟦future⟧ .past) := by
  decide

-- (14), (20), (22), (32), (26)
theorem downstairs_iff :
    ∀ r ∈ Examples.all, r.feature? "embeddedClauses" = some "2" →
      ∃ rel ∈ r.parse? "clause" relations, ∃ L ∈ languages.lookup r.language,
        (r.readings.lookup "downstairs" = some .acceptable ↔ rel ∉ L.tensed) := by
  decide

-- (8), (9), (35), (36)
theorem habitual_iff :
    ∀ r ∈ Examples.all, r.language = "nucl1643" →
      r.feature? "clause" ∈ [some "when", some "relative"] →
        ∃ τ ∈ r.parse? "embeddedTense" tenses, ∃ h ∈ head? τ,
          (r.readings.lookup "habitual" = some .acceptable ↔
            Interpretable (quantificational h (.leaf (.vp 0)))) := by
  decide

end ArreguiKusumoto1998
