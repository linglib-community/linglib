module

public import Linglib.Data.Examples.Egressy2026
public import Linglib.Data.Examples.Gloss
public import Linglib.Morphology.Word.Leipzig
public import Linglib.Fragments.Hungarian.Verbs
public import Linglib.Fragments.Hungarian.Pronouns
public import Linglib.Semantics.Tense.Embedding
public import Linglib.Syntax.Minimalist.Clause.Size
public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Linglib.Syntax.Minimalist.Probe.Profile
public import Linglib.Data.Examples.Readers

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

* Clause size is `Minimalist.ComplementSize` in the extension order of `Minimalist.Cat`, where
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
  role by the case cell of `Hungarian.Pronouns.az` its expletive realizes. Direct perception,
  which the paper says removes the backshifted reading pragmatically, is its `directPerception`
  feature. Each single-embedding
  row also carries a linearized witness over a study lexicon that pronounces the row's gloss
  line (`Minimalist.SpellsOut`) and shows the same matrix verb and expletive cell the readers
  find.
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

open scoped Denotes

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

-- §3.1
theorem size_nonSpeech_lt_speech :
    ClauseType.nonSpeechReporting.size < ClauseType.speechReporting.size := by
  decide +kernel

/-! ### The Williams Cycle (26) and the Williams Cycle in Agree (35) -/

/-- A dependency headed at `x`, movement to Spec,XP or Agree from X or XP, may cross or search
a projection of `y` unless Y is above X in the functional sequence. -/
def WilliamsCycle (x y : Cat) : Prop := ¬ AsymmRel Cat.ExtendsTo x y

instance (x y : Cat) : Decidable (WilliamsCycle x y) :=
  inferInstanceAs (Decidable (¬ (x.ExtendsTo y ∧ ¬ y.ExtendsTo x)))

theorem WilliamsCycle.refl (x : Cat) : WilliamsCycle x x := fun h ↦ h.2 h.1

theorem WilliamsCycle.of_extendsTo {x y y' : Cat} (h : y'.ExtendsTo y)
    (hxy : WilliamsCycle x y) : WilliamsCycle x y' :=
  fun hxy' ↦ hxy (hxy'.trans_le h)

-- (24), (25) [egressy-2025]
theorem focus_crosses_TP : WilliamsCycle .Foc .T := by decide +kernel

-- (24), (25)
theorem focus_blocked_by_SayP : ¬ WilliamsCycle .Foc .Say := by decide +kernel

-- (27)
theorem raising_crosses_TP : WilliamsCycle .T .T := WilliamsCycle.refl _

-- (28)
theorem raising_blocked_by_CP : ¬ WilliamsCycle .T .C := by decide +kernel

/-- The complement size crossed in a raising row. -/
def crossed? (e : Datum) : Option ComplementSize :=
  e.parse? "crossed" [("tP", .tP), ("cP", .cP)]

theorem raising_rows : ∀ e ∈ [ex_27, ex_28], ∀ cs ∈ crossed? e,
    e.judgment = .acceptable ↔ WilliamsCycle .T cs.highestHead := by
  decide +kernel

/-- (23): evaluative adverbs such as *sajnos* sit in the Say layer above foci, so a clause hosts
one iff it is at least a SayP. -/
def HostsEvaluativeAdverb (cs : ComplementSize) : Prop := ⟨.Say⟩ ≤ cs

instance (cs : ComplementSize) : Decidable (HostsEvaluativeAdverb cs) :=
  inferInstanceAs (Decidable (_ ≤ _))

-- (23)
theorem hostsEvaluativeAdverb_iff (ct : ClauseType) :
    HostsEvaluativeAdverb ct.size ↔ ct = .speechReporting := by
  cases ct <;> decide +kernel

/-! ### The Sequence of Tense Rule (31) and size-dependent adjunction (41) -/

/-- An embedded clause attaches (§4) by (41) to the matrix projection of its own size, as in
Hungarian, or inside the matrix VP as the sister of V, as in English, where (41) does not
hold. -/
inductive Attachment
  | sizeDependent
  | vpInternal
  deriving DecidableEq

/-- The head of the matrix projection an embedded clause attaches to. -/
def Attachment.level : Attachment → ComplementSize → Cat
  | .sizeDependent, cs => cs.highestHead
  | .vpInternal, _ => .V

/-- The Sequence of Tense Rule (31) can delete an embedded PAST iff the embedded T is contained
in a projection of the matrix PAST T, that is, iff the clause attaches no higher than TP. -/
def SOTRule.Applicable (a : Attachment) (cs : ComplementSize) : Prop :=
  WilliamsCycle .T (a.level cs)

instance (a : Attachment) (cs : ComplementSize) : Decidable (SOTRule.Applicable a cs) :=
  inferInstanceAs (Decidable (WilliamsCycle _ _))

-- §3.3, §4
theorem applicable_sizeDependent_iff (cs : ComplementSize) :
    SOTRule.Applicable .sizeDependent cs ↔ WilliamsCycle .T cs.highestHead :=
  Iff.rfl

-- §4
theorem applicable_vpInternal_cP :
    SOTRule.Applicable .vpInternal .cP ∧ ¬ WilliamsCycle .T .C := by
  decide +kernel

/-! ### Readings: the language-wide parameter realized clause-internally (§1, §2.4) -/

/-- The readings of a past clause under a past matrix, where backshift is the default and the
simultaneous reading arises only through the rule. -/
def readings (a : Attachment) (cs : ComplementSize) : Finset Ordering :=
  pastUnderPast (SOTRule.Applicable a cs)

theorem applicable_nonSpeech :
    SOTRule.Applicable .sizeDependent ClauseType.nonSpeechReporting.size := by
  decide +kernel

theorem not_applicable_speech :
    ¬ SOTRule.Applicable .sizeDependent ClauseType.speechReporting.size := by
  decide +kernel

-- §2.4
theorem simultaneous_iff (ct : ClauseType) :
    .eq ∈ readings .sizeDependent ct.size ↔
      ct = .nonSpeechReporting := by
  cases ct <;> decide +kernel

theorem shifted_mem (a : Attachment) (cs : ComplementSize) :
    .lt ∈ readings a cs :=
  lt_mem_pastUnderPast

-- (19)
theorem english_simultaneous :
    .eq ∈ readings .vpInternal .cP := by
  decide +kernel

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
  decide +kernel

/-- The matrix word of a row with its verb: among the words before the first complementizer
glossed *that*, the past-tense one whose stem is a stem the fragment declares, so *álmod-t-a*
finds *álmodik*. Every condition is the row's own structure or the lexicon's own forms: matrix
material precedes the *hogy*-clause, finiteness is the `PST` gloss label, every matrix of the
paper being past, and the stem matches `Hungarian.Verbs.Verb.stem` exactly. -/
def matrixWord? (e : Datum) : Option (GlossedWord × Hungarian.Verbs.Verb) :=
  (e.glossedWords.takeWhile fun w ↦ w.lexicalGloss? != some "that".toList).findSome? fun w ↦
    if Morphology.Features.ofLabels w.labels .tense == (UD.Tense.Past : Flat _) then
      (verbs.find? fun v ↦ w.stem == v.stem.toList).map (w, ·)
    else none

/-- The matrix verb of a row, by `matrixWord?`. -/
def matrixVerb? (e : Datum) : Option Hungarian.Verbs.Verb := (matrixWord? e).map (·.2)

/-- The grammatical role of the embedded clause in the matrix. -/
inductive ClauseRole where
  | object
  | subject
  | adjunct
  deriving DecidableEq, Repr

/-- The case cells of the expletive paradigm with the clause role each diagnoses (§2.1–2.2):
accusative *azt* for an object clause, nominative *az* for the subject clause, and instrumental
*azzal* or *amiatt* 'because of that' for an adjunct. -/
def roleTable : List (Option String × ClauseRole) :=
  [(Hungarian.Pronouns.az .acc, .object), (Hungarian.Pronouns.az .nom, .subject),
    (Hungarian.Pronouns.az .inst, .adjunct), (some Hungarian.Pronouns.amiatt, .adjunct)]

/-- The clause's role, read off its expletive correlate: the word glossed *it* — the gloss
setting the demonstrative apart from its article homograph — realizes a case cell of
`Hungarian.Pronouns.az`, and `roleTable` names the cell's role. -/
def clauseRole? (e : Datum) : Option ClauseRole :=
  e.glossedWords.findSome? fun w ↦
    if w.lexicalGloss? = some "it".toList then
      (roleTable.find? fun x ↦ x.1.map (·.toList) == some w.wordform).map (·.2)
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

theorem singleRows_readCounts :
    Datum.ReadCount matrixVerb? singleRows 12 ∧ Datum.ReadCount clauseRole? singleRows 12 ∧
      Datum.ReadCount clauseType? singleRows 12 := by
  decide +kernel

theorem clauseRole_frames : ∀ e ∈ singleRows, ∀ v, matrixVerb? e = some v →
    ∀ r ∈ clauseRole? e, r.FrameOf v.toVerb := by
  decide +kernel

-- (5), (13), §2.2
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

-- (16)
theorem ex16_profile :
    profile .sizeDependent ⟦past⟧ (chain .speechReporting .nonSpeechReporting) =
      [⟦past⟧, ⟦past⟧ ⊔ ⟦present⟧] := by
  decide +kernel

-- (17), (16)
theorem ex17_profile :
    profile .sizeDependent ⟦past⟧ (chain .nonSpeechReporting .speechReporting) =
      [⟦past⟧ ⊔ ⟦present⟧, ⟦past⟧] := by
  decide +kernel

-- (10), (15), (16), (17)
theorem doubleRows_predicted : ∀ e ∈ [ex_10, ex_15, ex_16, ex_17], ∀ ct₁ ct₂ : ClauseType,
    e.parse? "intermediateClauseType" clauseTypeTable = some ct₁ →
    e.parse? "deepestClauseType" clauseTypeTable = some ct₂ →
      Agrees e "intermediate " (observed (DirectPerceptionAt e "intermediateDirectPerception")
          ((profile .sizeDependent ⟦past⟧ (chain ct₁ ct₂)).getD 0 ⊥)) ∧
        Agrees e "deepest " (observed (DirectPerceptionAt e "deepestDirectPerception")
          ((profile .sizeDependent ⟦past⟧ (chain ct₁ ct₂)).getD 1 ⊥)) := by
  decide +kernel

-- (18) [ogihara-1996]
theorem ex18_profile :
    profile .vpInternal ⟦past⟧ [⟨⟦future⟧, .cP⟩, ⟨⟦past⟧, .cP⟩] = [⊥, ⟦past⟧] := by
  decide

theorem ex18_predicted : Agrees ex_18 "deepest " ⟦past⟧ := by decide

/-! ### Rival mechanisms (§3.3, §4) -/

theorem resMovement_blocked_by_TP : ¬ WilliamsCycle .V .T := by decide +kernel

/-- Sequence of Tense as a probe of [keine-2020]: a probe on T whose horizon is Say. -/
def sotProbe : Probe.Profile := ⟨.T, some .Say⟩

theorem sotProbe_clauseTypes :
    sotProbe.TransparentTo ClauseSpine.tP.label ∧
      ¬ sotProbe.TransparentTo (ClauseSpine.tP.append [.Foc, .Say]).label := by
  decide

-- §4, footnote 9
theorem horizon_admits_FocP :
    sotProbe.TransparentTo (ClauseSpine.tP.append [.Foc]).label ∧ ¬ WilliamsCycle .T .Foc := by
  decide +kernel

/-! ### Recognition by witness

A linearized syntactic object over a study lexicon pronounces each single-embedding row's gloss
line (`Minimalist.SpellsOut`), and its pre-complementizer verb and its expletive cell are the
matrix verb and clause role the gloss readers find, so the readers run against derived
structure. The witnesses are right-branching linearizations, each *hogy*-clause a constituent;
fuller argument structure is the derivation step's work. The expletive items take their forms
from the `Hungarian.Pronouns.az` paradigm; the remaining words, inflected verbs and nouns among
them, enter the study lexicon at their surface forms, Hungarian conjugation and declension being
no fragment's yet. -/

def liPeti : LexicalItem.Token := ⟨.of .D [] "Peti", 0⟩
def liPetit : LexicalItem.Token := ⟨.of .D [] "Petit", 1⟩
def liPetitől : LexicalItem.Token := ⟨.of .D [] "Petitől", 2⟩
def liMari : LexicalItem.Token := ⟨.of .D [] "Mari", 3⟩
def liZsuzsi : LexicalItem.Token := ⟨.of .D [] "Zsuzsi", 4⟩
def liA : LexicalItem.Token := ⟨.of .D [] "a", 5⟩

/-- The expletive at its accusative cell. -/
def liAzt : LexicalItem.Token := ⟨.of .D [] ((Hungarian.Pronouns.az .acc).getD ""), 6⟩

/-- The expletive at its nominative cell. -/
def liAz : LexicalItem.Token := ⟨.of .D [] ((Hungarian.Pronouns.az .nom).getD ""), 7⟩

/-- The expletive at its instrumental cell. -/
def liAzzal : LexicalItem.Token := ⟨.of .D [] ((Hungarian.Pronouns.az .inst).getD ""), 8⟩

/-- The expletive with the postposition, *amiatt*. -/
def liAmiatt : LexicalItem.Token := ⟨.of .P [] Hungarian.Pronouns.amiatt, 9⟩

/-- The complementizer *hogy*. -/
def liHogy : LexicalItem.Token := ⟨.of .C [] "hogy", 10⟩

def liLátta : LexicalItem.Token := ⟨.of .V [] "látta", 11⟩
def liHallotta : LexicalItem.Token := ⟨.of .V [] "hallotta", 12⟩
def liÁlmodta : LexicalItem.Token := ⟨.of .V [] "álmodta", 13⟩
def liGondolta : LexicalItem.Token := ⟨.of .V [] "gondolta", 14⟩
def liAggasztotta : LexicalItem.Token := ⟨.of .V [] "aggasztotta", 15⟩
def liMondta : LexicalItem.Token := ⟨.of .V [] "mondta", 16⟩
def liRikoltotta : LexicalItem.Token := ⟨.of .V [] "rikoltotta", 17⟩
def liMorogta : LexicalItem.Token := ⟨.of .V [] "morogta", 18⟩
def liMorogtál : LexicalItem.Token := ⟨.of .V [] "morogtál", 19⟩
def liTelefonáltál : LexicalItem.Token := ⟨.of .V [] "telefonáltál", 20⟩
def liSírt : LexicalItem.Token := ⟨.of .V [] "sírt", 21⟩

/-- *volt*, the embedded finite past of *van* 'be'. -/
def liVolt : LexicalItem.Token := ⟨.of .T [] "volt", 22⟩

def liSzemével : LexicalItem.Token := ⟨.of .N [] "szemével", 23⟩
def liFülével : LexicalItem.Token := ⟨.of .N [] "fülével", 24⟩
def liZsebkendőkből : LexicalItem.Token := ⟨.of .N [] "zsebkendőkből", 25⟩
def liSaját : LexicalItem.Token := ⟨.of .A [] "saját", 26⟩
def liSzomorú : LexicalItem.Token := ⟨.of .A [] "szomorú", 27⟩
def liTelesírt : LexicalItem.Token := ⟨.of .A [] "telesírt", 28⟩
def liSajnos : LexicalItem.Token := ⟨.of .P [] "sajnos", 29⟩
def liKorábban : LexicalItem.Token := ⟨.of .P [] "korábban", 30⟩

/-- The study lexicon of the single-embedding rows, the witness tokens' items. -/
def lexicon : List LexicalItem :=
  ([liPeti, liPetit, liPetitől, liMari, liZsuzsi, liA, liAzt, liAz, liAzzal, liAmiatt, liHogy,
    liLátta, liHallotta, liÁlmodta, liGondolta, liAggasztotta, liMondta, liRikoltotta, liMorogta,
    liMorogtál, liTelefonáltál, liSírt, liVolt, liSzemével, liFülével, liZsebkendőkből, liSaját,
    liSzomorú, liTelesírt, liSajnos, liKorábban] : List LexicalItem.Token).map (·.item)

/-- The embedded clause the rows share, *Mari szomorú volt*. -/
def wSad : LinearizedSyntacticObject := liMari * (liSzomorú * liVolt)

/-- (4): *Peti saw with his own eyes that Mari was sad*. -/
def w4 : LinearizedSyntacticObject :=
  liPeti * (liA * (liSaját * (liSzemével * (liLátta * (liAzt * (liHogy * wSad))))))

/-- (5): the heard variant of (4), *that Mari cried*. -/
def w5 : LinearizedSyntacticObject :=
  liPeti * (liA * (liSaját * (liFülével * (liHallotta * (liAzt * (liHogy * (liMari * liSírt)))))))

/-- (6): *Peti dreamt it that Mari was sad*. -/
def w6 : LinearizedSyntacticObject :=
  liPeti * (liAzt * (liÁlmodta * (liHogy * wSad)))

/-- (7): the *think* variant of (6). -/
def w7 : LinearizedSyntacticObject :=
  liPeti * (liAzt * (liGondolta * (liHogy * wSad)))

/-- (8): *It worried Peti that Mari was sad*, the subject clause. -/
def w8 : LinearizedSyntacticObject :=
  liAz * (liAggasztotta * (liPetit * (liHogy * wSad)))

/-- (9): *You growled because of it that Mari was sad*, the adjunct clause. -/
def w9 : LinearizedSyntacticObject :=
  liMorogtál * (liAmiatt * (liHogy * wSad))

/-- (11a): *Peti said it that (unfortunately) Mari was sad*. -/
def w11a : LinearizedSyntacticObject :=
  liPeti * (liAzt * (liMondta * (liHogy * (liSajnos * wSad))))

/-- (11b): the *shout* variant of (11a). -/
def w11b : LinearizedSyntacticObject :=
  liPeti * (liAzt * (liRikoltotta * (liHogy * (liSajnos * wSad))))

/-- (11c): the *growl* variant of (11a). -/
def w11c : LinearizedSyntacticObject :=
  liPeti * (liAzt * (liMorogta * (liHogy * (liSajnos * wSad))))

/-- (12): *You phoned with it that (unfortunately) Mari was sad*, the adjunct clause. -/
def w12 : LinearizedSyntacticObject :=
  liTelefonáltál * (liAzzal * (liHogy * (liSajnos * wSad)))

/-- (13): *Zsuzsi heard it from Peti that unfortunately Mari was sad*. -/
def w13 : LinearizedSyntacticObject :=
  liZsuzsi * (liPetitől * (liAzt * (liHallotta * (liHogy * (liSajnos * wSad)))))

/-- (14): *Peti saw from the cried-in handkerchiefs that (earlier) Mari was sad*. -/
def w14 : LinearizedSyntacticObject :=
  liPeti * (liA * (liTelesírt * (liZsebkendőkből *
    (liLátta * (liAzt * (liHogy * (liKorábban * wSad)))))))

/-- The matrix verb token of a witness: the verb-category token pronounced before the
complementizer. -/
def matrixToken? (t : LinearizedSyntacticObject) : Option LexicalItem.Token :=
  ((Minimalist.pfYield t).takeWhile fun tok ↦ tok.item.cat ≠ .C).find? fun tok ↦
    tok.item.cat = .V

/-- The clause role a witness shows: the role `roleTable` gives the paradigm cell its pronounced
expletive realizes. -/
def roleOf (t : LinearizedSyntacticObject) : Option ClauseRole :=
  (Minimalist.pfYield t).findSome? fun tok ↦
    (roleTable.find? fun x ↦ x.1 == tok.item.phonForm?).map (·.2)

/-- The single-embedding rows with their witnesses. -/
def witnessRows : List (Datum × LinearizedSyntacticObject) :=
  [(ex_4, w4), (ex_5, w5), (ex_6, w6), (ex_7, w7), (ex_8, w8), (ex_9, w9), (ex_11a, w11a),
    (ex_11b, w11b), (ex_11c, w11c), (ex_12, w12), (ex_13, w13), (ex_14, w14)]

theorem witnesses_spell : ∀ p ∈ witnessRows,
    Minimalist.SpellsOut p.2 lexicon (Minimalist.pfPhon p.2) ∧
      (Minimalist.pfPhon p.2).flatMap (Gloss.tokens ·) = p.1.glossStream := by
  decide +kernel

theorem witnesses_verb : ∀ p ∈ witnessRows,
    (matrixToken? p.2).map (·.item.phonForm.toList) = (matrixWord? p.1).map (·.1.wordform) := by
  decide +kernel

theorem witnesses_role : ∀ p ∈ witnessRows, roleOf p.2 = clauseRole? p.1 := by
  decide +kernel

end Egressy2026
