module

public import Linglib.Data.Examples.Egressy2026
public import Linglib.Data.Examples.Gloss
public import Linglib.Fragments.Hungarian.Verbs
public import Linglib.Fragments.Hungarian.Pronouns
public import Linglib.Semantics.Tense.Embedding
public import Linglib.Syntax.Minimalist.Clause.Size
public import Linglib.Syntax.Minimalist.Probe.Profile

/-!
# Egressy (2026): Size-Sensitive Sequence of Tense in Hungarian

This file formalizes [egressy-2026]'s account of a split among Hungarian past-under-past
clauses: a non-speech-reporting clause (perception, dreaming, thought, belief, a reason adjunct)
has the simultaneous reading, like an English complement, while a speech-reporting clause, one
encoding the content of a verbal or other sign, is backshifted only, like a Japanese one. The
split is clause-internal, since one verb embeds either type. Non-speech-reporting clauses are
bare TPs and speech-reporting clauses SayPs with Say > Foc > T, Hungarian having no CP; the
Sequence of Tense Rule of [ogihara-1996] deletes an embedded PAST under Agree with a matrix
PAST, and that Agree obeys the Williams Cycle of [williams-2003]: a dependency headed at T cannot
search a projection above T in the functional sequence. It therefore crosses a TP and is blocked
by a SayP, just as focus movement to Spec,FocP escapes a TP but not a SayP and raising to Spec,TP
crosses a TP but not a CP. The Williams Cycle in Agree is derived from size-dependent adjunction:
an embedded clause adjoins to the matrix projection of its own size, so only a clause no larger
than TP lies inside a projection of the matrix PAST. The same derivation gives the
multiple-embedding data, where only structurally adjacent clauses interact, and locates the
size-insensitive Sequence of Tense of English in its CP complements sitting inside the VP.

## Implementation notes

* Clause size is `Minimalist.ComplementSize` on the shared functional sequence `Cat.fValue`, where
  `Cat.Say` sits at Say > Foc > T. The Williams Cycle (26) and its version for Agree (35) are one
  relation, `WilliamsCycle x y`, between the head of a dependency and the crossed projection.
* Readings are positions of the embedded reference time against the attitude's now, an
  `Ordering`: backshifted `.lt`, simultaneous `.eq`. The clause-internal value of
  [ogihara-sharvit-2012]'s Sequence of Tense parameter is `SOTRule.Applicable` itself, so
  `readings` is `Tense.pastUnderPast` at it, and a chain of embeddings is read pairwise by
  `profile`.
* The examples are `Data.Examples.Egressy2026`. A row's clause type is its `clauseType`
  feature; its matrix verb and the clause's grammatical role are read off its gloss line
  (`Data/Examples/Gloss.lean`), the verb by its declared past stem in `Hungarian.Verbs` and the
  role by the case cell of `Hungarian.Pronouns.az` its expletive realizes. Direct perception, which the paper says removes the
  backshifted reading pragmatically, is its `directPerception` feature.
* Footnote 9 allows the complement of *mond* to be an XP with Say > Foc > X > T, which movement
  to Spec,FocP escapes but Agree from T does not; the shared sequence has no such head, so those
  complements are SayPs here.

## References

* [egressy-2026]
* [egressy-2025]
* [williams-2003]
* [keine-2019]
* [keine-2020]
* [ogihara-1996]
* [ogihara-sharvit-2012]
* [sharvit-2020]
* [kiss-2023]
* [abusch-1988]
* [heim-1994-comments]
-/

@[expose] public section

namespace Egressy2026

open Semantics

open Minimalist Tense Hungarian.Verbs Egressy2026.Examples

/-! ### The two clause types and their size (§2, §3.1) -/

/-- An embedded clause either encodes the content of a verbal or other sign or does not (§2.2),
a property of the clause, not of the matrix predicate, which may embed either type. -/
inductive ClauseType
  | nonSpeechReporting
  | speechReporting
  deriving DecidableEq, Repr, Fintype

/-- (21)–(22): a non-speech-reporting clause is a bare TP, a speech-reporting clause a SayP. -/
def ClauseType.size : ClauseType → ComplementSize
  | .nonSpeechReporting => .tP
  | .speechReporting => ⟨.Say⟩

/-- Speech-reporting clauses are the larger ones (§3.1). -/
theorem size_nonSpeech_lt_speech :
    ClauseType.nonSpeechReporting.size.fLevel < ClauseType.speechReporting.size.fLevel := by
  decide

/-! ### The Williams Cycle (26) and the Williams Cycle in Agree (35) -/

/-- A dependency headed at `x`, movement to Spec,XP or Agree from X or XP, may cross or search
a projection of `y` unless Y is above X in the functional sequence. -/
def WilliamsCycle (x y : Cat) : Prop := y.fValue ≤ x.fValue

instance (x y : Cat) : Decidable (WilliamsCycle x y) := inferInstanceAs (Decidable (_ ≤ _))

/-- A projection of the dependency's own category is crossed. -/
theorem WilliamsCycle.refl (x : Cat) : WilliamsCycle x x := le_rfl

theorem WilliamsCycle.of_le {x y y' : Cat} (h : y'.fValue ≤ y.fValue) (hxy : WilliamsCycle x y) :
    WilliamsCycle x y' :=
  h.trans hxy

/-- (24)–(25), [egressy-2025]: focus and wh-movement to Spec,FocP escape a TP. -/
theorem focus_crosses_TP : WilliamsCycle .Foc .T := by decide

/-- (24)–(25): movement to Spec,FocP cannot leave a SayP, whose Say is above Foc. -/
theorem focus_blocked_by_SayP : ¬ WilliamsCycle .Foc .Say := by decide

/-- (27): raising to Spec,TP crosses a TP. -/
theorem raising_crosses_TP : WilliamsCycle .T .T := WilliamsCycle.refl _

/-- (28), the ban on hyperraising: raising to Spec,TP cannot cross a CP. -/
theorem raising_blocked_by_CP : ¬ WilliamsCycle .T .C := by decide

/-- The complement size crossed in a raising row. -/
def crossed? (e : Datum) : Option ComplementSize :=
  e.parse? "crossed" [("tP", .tP), ("cP", .cP)]

theorem raising_rows : ∀ e ∈ [ex_27, ex_28], ∀ cs ∈ crossed? e,
    e.judgment = .acceptable ↔ WilliamsCycle .T cs.highestHead := by
  decide

/-- (23): evaluative adverbs such as *sajnos* sit in the Say layer above foci, so a clause hosts
one iff it is at least a SayP. -/
def HostsEvaluativeAdverb (cs : ComplementSize) : Prop := Cat.fValue .Say ≤ cs.fLevel

instance (cs : ComplementSize) : Decidable (HostsEvaluativeAdverb cs) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The complements of *mond*, *hall* and *gondol* in (23) host *sajnos*; the TP complement of
*álmodik* cannot. -/
theorem hostsEvaluativeAdverb_iff (ct : ClauseType) :
    HostsEvaluativeAdverb ct.size ↔ ct = .speechReporting := by
  cases ct <;> decide

/-! ### The Sequence of Tense Rule (31) and size-dependent adjunction (41) -/

/-- An embedded clause attaches (§4) by (41) to the matrix projection of its own size, as in
Hungarian, or inside the matrix VP as the sister of V, as in English, where (41) does not
hold. -/
inductive Attachment
  | sizeDependent
  | vpInternal
  deriving DecidableEq

/-- The functional-sequence level of the matrix projection an embedded clause attaches to. -/
def Attachment.level : Attachment → ComplementSize → ℕ
  | .sizeDependent, cs => cs.fLevel
  | .vpInternal, _ => Cat.fValue .V

/-- The Sequence of Tense Rule (31) can delete an embedded PAST iff the embedded T is contained
in a projection of the matrix PAST T, that is, iff the clause attaches no higher than TP. -/
def SOTRule.Applicable (a : Attachment) (cs : ComplementSize) : Prop := a.level cs ≤ Cat.fValue .T

instance (a : Attachment) (cs : ComplementSize) : Decidable (SOTRule.Applicable a cs) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Under size-dependent adjunction, the Sequence of Tense Rule applies exactly where the Williams
Cycle lets T search the clause (§3.3, §4). -/
theorem applicable_sizeDependent_iff (cs : ComplementSize) :
    SOTRule.Applicable .sizeDependent cs ↔ WilliamsCycle .T cs.highestHead :=
  Iff.rfl

/-- With the embedded clause inside the VP, the rule applies to English CP complements, which the
Williams Cycle would keep from T (§4). -/
theorem applicable_vpInternal_cP :
    SOTRule.Applicable .vpInternal .cP ∧ ¬ WilliamsCycle .T .C := by
  decide

/-! ### Readings: the language-wide parameter realized clause-internally (§1, §2.4) -/

/-- The readings of a past clause under a past matrix, where backshift is the default and the
simultaneous reading arises only through the rule. -/
def readings (a : Attachment) (cs : ComplementSize) : Finset Ordering :=
  pastUnderPast (SOTRule.Applicable a cs)

theorem applicable_nonSpeech :
    SOTRule.Applicable .sizeDependent ClauseType.nonSpeechReporting.size := by
  decide

theorem not_applicable_speech :
    ¬ SOTRule.Applicable .sizeDependent ClauseType.speechReporting.size := by
  decide

/-- The core asymmetry (§2.4) is that the simultaneous reading is available exactly in
non-speech-reporting clauses. -/
theorem simultaneous_iff (ct : ClauseType) :
    .eq ∈ readings .sizeDependent ct.size ↔
      ct = .nonSpeechReporting := by
  cases ct <;> decide

theorem shifted_mem (a : Attachment) (cs : ComplementSize) :
    .lt ∈ readings a cs :=
  lt_mem_pastUnderPast

/-- (19): an English past-under-past complement has the simultaneous reading. -/
theorem english_simultaneous :
    .eq ∈ readings .vpInternal .cP := by
  decide

/-! ### Direct perception (§2.1) -/

/-- One can only perceive directly what happens now: the readings the paper reports are the
grammatical ones, narrowed to the simultaneous reading under direct perception. -/
def observed (direct : Prop) [Decidable direct] (rs : Finset Ordering) : Finset Ordering :=
  if direct then rs ⊓ ⟦present⟧ else rs

theorem observed_le (direct : Prop) [Decidable direct] (rs : Finset Ordering) :
    observed direct rs ≤ rs := by
  unfold observed
  split
  · exact inf_le_left
  · exact le_rfl

/-! ### The data (§2) -/

/-- The clause types as recorded in the rows. -/
def clauseTypeTable : List (String × ClauseType) :=
  [("nonSpeechReporting", .nonSpeechReporting), ("speechReporting", .speechReporting)]

/-- The clause type of a single-embedding row. -/
def clauseType? (e : Datum) : Option ClauseType :=
  e.parse? "clauseType" clauseTypeTable

/-- Whether a row's feature `key` records direct perception. -/
def DirectPerceptionAt (e : Datum) (key : String) : Prop :=
  e.feature? key = some "yes"

instance (e : Datum) (key : String) : Decidable (DirectPerceptionAt e key) :=
  inferInstanceAs (Decidable (_ = _))

/-- The readings as named in the rows. -/
def readingTable : List (String × Ordering) := [("simultaneous", .eq), ("backshifted", .lt)]

/-- A row's reported readings at embedding level `lvl` agree with a predicted reading set when
each named reading is judged acceptable exactly if predicted. -/
def Agrees (e : Datum) (lvl : String) (rs : Finset Ordering) : Prop :=
  ∀ r ∈ e.readings, ∀ x ∈ readingTable, r.1 = lvl ++ x.1 → (r.2 = .acceptable ↔ x.2 ∈ rs)

instance (e : Datum) (lvl : String) (rs : Finset Ordering) : Decidable (Agrees e lvl rs) :=
  inferInstanceAs (Decidable (∀ r ∈ e.readings, ∀ x ∈ readingTable, _ → _))

/-- The predicted readings of a single-embedding Hungarian row: the grammar at its clause
type, narrowed by direct perception. -/
def predicted (e : Datum) (ct : ClauseType) : Finset Ordering :=
  observed (DirectPerceptionAt e "directPerception") (readings .sizeDependent ct.size)

/-- The single-embedding rows of §2.1–2.2: object, subject and adjunct clauses of both types. -/
def singleRows : List Datum :=
  [ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_11a, ex_11b, ex_11c, ex_12, ex_13, ex_14]

theorem singleRows_predicted :
    ∀ e ∈ singleRows, ∀ ct : ClauseType, clauseType? e = some ct →
      Agrees e "" (predicted e ct) := by
  decide

/-- The matrix verb of a row: among the words before the first complementizer glossed *that*,
the past-tense one whose stem is a past stem the fragment declares, so *álmod-t-a* finds
*álmodik*. Every condition is the row's own structure or the lexicon's own forms: matrix
material precedes the *hogy*-clause, finiteness is the `PST` gloss label, every matrix of the
paper being past, and the stem matches `Hungarian.Verbs.Verb.stem` exactly. -/
def matrixVerb? (e : Datum) : Option Hungarian.Verbs.Verb :=
  (e.glossedWords.takeWhile fun w ↦ w.lexicalGloss? != some "that".toList).findSome? fun w ↦
    if w.labels.contains "PST".toList then
      verbs.find? fun v ↦ w.stem == v.stem.toList
    else none

/-- The grammatical role of the embedded clause in the matrix. -/
inductive ClauseRole where
  | object
  | subject
  | adjunct
  deriving DecidableEq, Repr

/-- The clause's role, read off its expletive correlate (§2.1–2.2): the word glossed *it* — the
gloss setting the demonstrative apart from its article homograph — realizes a case cell of
`Hungarian.Pronouns.az`, accusative *azt* for an object clause, nominative *az* for the subject
clause, and instrumental *azzal* or *amiatt* 'because of that' for an adjunct. -/
def clauseRole? (e : Datum) : Option ClauseRole :=
  e.glossedWords.findSome? fun w ↦
    if w.lexicalGloss? = some "it".toList then
      if some w.wordform == (Hungarian.Pronouns.az .acc).map (·.toList) then some .object
      else if some w.wordform == (Hungarian.Pronouns.az .nom).map (·.toList) then some .subject
      else if some w.wordform == (Hungarian.Pronouns.az .inst).map (·.toList) ∨
          w.wordform == Hungarian.Pronouns.amiatt.toList then some .adjunct
      else none
    else none

/-- The frame shape a clause role demands of the matrix verb: a clausal complement for an object
clause, a clausal subject for a subject clause, and for an adjunct a frame with no clausal
position, the clause sitting outside the valency. -/
def ClauseRole.FrameOf (r : ClauseRole) (v : _root_.Verb) : Prop :=
  match r with
  | .object => ∃ fr ∈ v.valency.frames, fr.HasClausal
  | .subject => ∃ fr ∈ v.valency.frames, fr.HasClausalSubject
  | .adjunct => ∃ fr ∈ v.valency.frames, ¬ fr.HasClausal ∧ ¬ fr.HasClausalSubject

instance (r : ClauseRole) (v : _root_.Verb) : Decidable (r.FrameOf v) :=
  match r with
  | .object => inferInstanceAs (Decidable (∃ fr ∈ _, _))
  | .subject => inferInstanceAs (Decidable (∃ fr ∈ _, _))
  | .adjunct => inferInstanceAs (Decidable (∃ fr ∈ _, _))

/-- The verb, clause-role and clause-type readers read every single-embedding row. -/
theorem singleRows_readCounts :
    Datum.ReadCount matrixVerb? singleRows 12 ∧ Datum.ReadCount clauseRole? singleRows 12 ∧
      Datum.ReadCount clauseType? singleRows 12 := by
  decide +kernel

/-- The expletive's case diagnoses the clause's grammatical role, and the role matches a frame
of the row's matrix verb, both read off the row's own gloss line. -/
theorem clauseRole_frames : ∀ e ∈ singleRows, ∀ v, matrixVerb? e = some v →
    ∀ r ∈ clauseRole? e, r.FrameOf v.toVerb := by
  decide +kernel

/-- No assignment of clause types to matrix verbs fits the rows: two rows share their matrix
verb, *hall* 'hear' in (5) and (13), and differ in clause type (§2.2). -/
theorem clauseType_not_of_verb :
    ¬ ∀ e₁ ∈ singleRows, ∀ e₂ ∈ singleRows,
      ((matrixVerb? e₁).map (·.toVerb.form) == (matrixVerb? e₂).map (·.toVerb.form)) = true →
        clauseType? e₁ = clauseType? e₂ := by
  decide +kernel

/-! ### Multiple embedding (§2.3, §4) -/

/-- An embedded clause carries its morphological tense and its size. -/
structure Clause where
  /-- The clause's tense as a comparison cell, `⟦Tense.past⟧` or `⟦Tense.future⟧`. -/
  tense : Finset Ordering
  /-- The clause's size. -/
  size : ComplementSize

/-- The readings of an embedded clause against the clause immediately containing it. A past
clause under a past clause is read by the rule; a past clause under any other tense is
backshifted only, since the rule needs an agreeing PAST above; a non-past clause has no
past-under-past reading. -/
def linkReadings (a : Attachment) (matrix : Finset Ordering) (c : Clause) : Finset Ordering :=
  if c.tense = ⟦past⟧ then (if matrix = ⟦past⟧ then readings a c.size else ⟦past⟧) else ⊥

/-- The readings at each level of a chain of embedded clauses under a matrix tense, matrix first.
Each clause is read against the clause immediately containing it: by (41) every clause attaches
at its own size, so a SayP is never inside a TP of any higher clause while a TP is inside the TP
of the clause containing it, and only structurally adjacent clauses interact (§2.3, §4). -/
def profile (a : Attachment) : Finset Ordering → List Clause → List (Finset Ordering)
  | _, [] => []
  | m, c :: rest => linkReadings a m c :: profile a c.tense rest

/-- The chain of a two-level Hungarian row, from its two clause-type features. -/
def chain (ct₁ ct₂ : ClauseType) : List Clause := [⟨⟦past⟧, ct₁.size⟩, ⟨⟦past⟧, ct₂.size⟩]

/-- (16): shout > see > be. The speech-reporting intermediate clause is backshifted; the
non-speech-reporting deepest clause is simultaneous with it. -/
theorem ex16_profile :
    profile .sizeDependent ⟦past⟧ (chain .speechReporting .nonSpeechReporting) =
      [⟦past⟧, ⟦past⟧ ⊔ ⟦present⟧] := by
  decide

/-- (17): hear > shout > be, the mirror image of (16): only adjacent clauses interact, and a
speech-reporting clause is backshifted whatever contains it. -/
theorem ex17_profile :
    profile .sizeDependent ⟦past⟧ (chain .nonSpeechReporting .speechReporting) =
      [⟦past⟧ ⊔ ⟦present⟧, ⟦past⟧] := by
  decide

/-- The two-level rows (10), (15), (16) and (17) are predicted level by level, direct perception
narrowing the level of the perceiving clause. -/
theorem doubleRows_predicted : ∀ e ∈ [ex_10, ex_15, ex_16, ex_17], ∀ ct₁ ct₂ : ClauseType,
    e.parse? "intermediateClauseType" clauseTypeTable = some ct₁ →
    e.parse? "deepestClauseType" clauseTypeTable = some ct₂ →
      Agrees e "intermediate " (observed (DirectPerceptionAt e "intermediateDirectPerception")
          ((profile .sizeDependent ⟦past⟧ (chain ct₁ ct₂)).getD 0 ⊥)) ∧
        Agrees e "deepest " (observed (DirectPerceptionAt e "deepestDirectPerception")
          ((profile .sizeDependent ⟦past⟧ (chain ct₁ ct₂)).getD 1 ⊥)) := by
  decide

/-- In English past under *will* under past (18), the deepest past has no simultaneous reading
([ogihara-1996]). -/
theorem ex18_profile :
    profile .vpInternal ⟦past⟧ [⟨⟦future⟧, .cP⟩, ⟨⟦past⟧, .cP⟩] = [⊥, ⟦past⟧] := by
  decide

theorem ex18_predicted : Agrees ex_18 "deepest " ⟦past⟧ := by decide

/-! ### Rival mechanisms (§3.3, §4) -/

theorem resMovement_blocked_by_TP : ¬ WilliamsCycle .V .T := by decide

/-- Sequence of Tense as a probe of [keine-2020]: a probe on T whose horizon is Say. -/
def sotProbe : Probe.Profile := ⟨.T, some .Say⟩

theorem sotProbe_clauseTypes :
    sotProbe.TransparentTo ClauseSpine.tP.label ∧
      ¬ sotProbe.TransparentTo (ClauseSpine.tP.append [.Foc, .Say]).label := by
  decide

/-- A FocP clause is transparent to the horizon probe yet beyond T under the Williams Cycle, so the
horizon account is less restrictive (§4, footnote 9). -/
theorem horizon_admits_FocP :
    sotProbe.TransparentTo (ClauseSpine.tP.append [.Foc]).label ∧ ¬ WilliamsCycle .T .Foc := by
  decide

end Egressy2026
