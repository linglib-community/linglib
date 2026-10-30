module

public import Mathlib.Algebra.Order.Ring.Int
public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Tense.Defs
public import Linglib.Syntax.Minimalist.Clause.Size
public import Linglib.Data.Examples.Wurmbrand2014
public import Linglib.Data.Examples.Gloss
public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Verbs.Implicative
public import Linglib.Fragments.English.Verbs.Communication
public import Linglib.Data.Examples.Readers

/-!
# Wurmbrand (2014): Tense and Aspect in English Infinitives

This file formalizes [wurmbrand-2014]'s account of the temporal composition of English
infinitival complements. Three classes are distinguished by whether a bare, nonprogressive
verb phrase can be episodic: future infinitives allow it, propositional attitude infinitives
never do, and tenseless simultaneous infinitives allow it depending on the matrix tense
(`InfinitivalTenseClass`). The distribution is derived from viewpoint aspect. Perfective
aspect includes the event time in the reference time and imperfective the reverse
(`Perfective`), and an episodic eventive predicate occupies an extended interval, so
perfective fails whenever the reference time is an instant (`not_perfective_of_isPoint`).
Each class fixes the embedded reference time (`ReferenceTime`): the future modal *woll* shifts
it to an unrestricted interval after the evaluation time, a propositional attitude imposes the
holder's NOW, an instant, and a tenseless simultaneous infinitive inherits the matrix reference
time, an instant under present tense and an extended interval under past. The three rows of
the paper's table follow (`Episodic`), and a verb ambiguous between classes, like *seem*, is
episodic exactly when one of its classes is (`Verb.Episodic`).

Future infinitives are tenseless: finite *will* is present tense plus *woll* and *would* is
past plus *woll* (`Composition`), so finite future is absolute while infinitival future is
relative to the matrix event (`infinitival_relative`), and infinitives are invisible to the
sequence-of-tense rule, whose local tense feature skips them (`localTense`): a past under an
infinitive under past deletes, a past under *will* does not, and a silent *would* in the
infinitive would wrongly license deletion under a *will* matrix (`silent_would_wrong`).

## Implementation notes

Times are the nonempty intervals of a linear order; an instant is an interval whose endpoints
coincide. The evaluation time of *woll* and the attitude holder's NOW are one instant
parameter, and adverbials that restrict a reference time to an instant fall under the same
lemma as the NOW. The obligatory deletion of *would*'s past is taken as the paper does, as a
lexical requirement. The `…_rows` fits read the episodic, aspect and sequence-of-tense rows on
integer time, episodicity decided by the table's three theorems and the tense stack recognized
in each sentence's words against the forms the English fragment declares or realizes. Each
sequence-of-tense row also carries a linearized witness over a study lexicon that pronounces
the row's sentence (`Minimalist.SpellsOut`) and whose tense spine is that recognized stack.

## References

* [wurmbrand-2014]
* [ogihara-1996]
* [abusch-1988]
* [wurmbrand-2001]
* [landau-2000]
-/

@[expose] public section

namespace Wurmbrand2014

open scoped Denotes

/-- The three classes of infinitival complement by tense behaviour. Future irrealis infinitives,
*decide*, *want* and *plan*, are tenseless with *woll* and future-oriented; propositional
infinitives, *believe* and *claim*, are anchored to the attitude holder's now; restructuring
infinitives, *try*, *begin* and *seem*, have no attitude holder and take the matrix reference
time. -/
inductive InfinitivalTenseClass
  | futureIrrealis
  | propositional
  | restructuring
  deriving DecidableEq, Repr, Inhabited

/-- The structural size of each class, the modal layer of *woll* for a future irrealis
infinitive, a TP for a propositional one and a bare vP for a restructuring one, the modal and
tense layers sharing a level of the functional sequence. -/
def InfinitivalTenseClass.complementSize : InfinitivalTenseClass → Minimalist.ComplementSize
  | .futureIrrealis => .modP
  | .propositional => .tP
  | .restructuring => .vP

open Tense Minimalist

/-! ### Viewpoint aspect -/

section Aspect

variable {T : Type*} [LinearOrder T]

/-- Perfective aspect includes the event time in the reference time. -/
def Perfective (e r : NonemptyInterval T) : Prop := e ≤ r

/-- Imperfective aspect includes the reference time in the event time. -/
def Imperfective (e r : NonemptyInterval T) : Prop := r ≤ e

theorem not_perfective_of_isPoint {e r : NonemptyInterval T} (he : ¬ e.IsPoint)
    (hr : r.IsPoint) : ¬ Perfective e r := by
  intro h
  rw [Perfective, NonemptyInterval.le_def] at h
  exact he (le_antisymm e.fst_le_snd (h.2.trans (hr.symm.le.trans h.1)))

theorem imperfective_pure_of_mem {e : NonemptyInterval T} {t : T} (h : t ∈ e) :
    Imperfective e (NonemptyInterval.pure t) := by
  rw [Imperfective, NonemptyInterval.le_def]
  exact NonemptyInterval.mem_def.mp h

/-! ### The reference time of an infinitive -/

variable (matrixR : NonemptyInterval T) (now : T)

/-- The reference time each class assigns the embedded aspect, given the matrix reference
time and the evaluation instant: after *woll*, any interval after the evaluation time; under a
propositional attitude, the holder's NOW; in a tenseless simultaneous infinitive, the matrix
reference time. -/
def ReferenceTime : InfinitivalTenseClass → NonemptyInterval T → Prop
  | .futureIrrealis, r => now < r.fst
  | .propositional, r => r = NonemptyInterval.pure now
  | .restructuring, r => r = matrixR

/-- A bare episodic verb phrase is available when some reference time of the class includes
an extended event time. -/
def Episodic (c : InfinitivalTenseClass) : Prop :=
  ∃ r, ReferenceTime matrixR now c r ∧
    ∃ e : NonemptyInterval T, ¬ e.IsPoint ∧ Perfective e r

theorem episodic_futureIrrealis [NoMaxOrder T] : Episodic matrixR now .futureIrrealis := by
  obtain ⟨a, ha⟩ := exists_gt now
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨⟨(a, b), hb.le⟩, ha, ⟨(a, b), hb.le⟩, hb.ne, le_rfl⟩

theorem not_episodic_propositional : ¬ Episodic matrixR now .propositional := by
  rintro ⟨r, rfl, e, he, h⟩
  exact not_perfective_of_isPoint he (show (NonemptyInterval.pure now).IsPoint from rfl) h

theorem episodic_restructuring_iff :
    Episodic matrixR now .restructuring ↔ ¬ matrixR.IsPoint := by
  constructor
  · rintro ⟨r, rfl, e, he, h⟩ hp
    exact not_perfective_of_isPoint he hp h
  · exact fun h ↦ ⟨matrixR, rfl, matrixR, h, le_rfl⟩

/-- Episodicity is decided by the three cells of the table: always available after *woll*, never
at the holder's NOW, and at the matrix reference time exactly when it is extended. -/
instance [NoMaxOrder T] [DecidableEq T] (c : InfinitivalTenseClass) :
    Decidable (Episodic matrixR now c) :=
  match c with
  | .futureIrrealis => .isTrue (episodic_futureIrrealis matrixR now)
  | .propositional => .isFalse (not_episodic_propositional matrixR now)
  | .restructuring =>
      decidable_of_iff (¬ matrixR.fst = matrixR.snd) (episodic_restructuring_iff matrixR now).symm

/-! ### Verbs -/

/-- The infinitive-taking verbs of the paper's table. -/
inductive Verb where
  | decide
  | want
  | promise
  | expect
  | claim
  | believe
  | try_
  | begin_
  | manage
  | seem
  deriving DecidableEq, Repr

/-- The classes a verb's infinitive may belong to. *Expect* is future or, as a belief,
propositional; *seem* is tenseless simultaneous or, with an attitude holder, propositional. -/
def Verb.classes : Verb → List InfinitivalTenseClass
  | .decide | .want | .promise => [.futureIrrealis]
  | .expect => [.futureIrrealis, .propositional]
  | .claim | .believe => [.propositional]
  | .try_ | .begin_ | .manage => [.restructuring]
  | .seem => [.restructuring, .propositional]

/-- A verb's infinitive has an episodic reading when one of its classes does. -/
def Verb.Episodic (v : Verb) : Prop :=
  ∃ c ∈ v.classes, Wurmbrand2014.Episodic matrixR now c

theorem believe_not_episodic : ¬ Verb.believe.Episodic matrixR now := by
  rintro ⟨c, hc, h⟩
  simp only [Verb.classes, List.mem_singleton] at hc
  exact not_episodic_propositional matrixR now (hc ▸ h)

theorem seem_episodic_iff : Verb.seem.Episodic matrixR now ↔ ¬ matrixR.IsPoint := by
  constructor
  · rintro ⟨c, hc, h⟩
    simp only [Verb.classes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact (episodic_restructuring_iff matrixR now).mp h
    · exact absurd h (not_episodic_propositional matrixR now)
  · exact fun h ↦ ⟨.restructuring, by simp [Verb.classes],
      (episodic_restructuring_iff matrixR now).mpr h⟩

theorem decide_episodic [NoMaxOrder T] : Verb.decide.Episodic matrixR now :=
  ⟨.futureIrrealis, by simp [Verb.classes], episodic_futureIrrealis matrixR now⟩

end Aspect

/-! ### Temporal composition -/

/-- The temporal composition of a clause is an optional tense feature together with whether the
future modal *woll* is present. -/
structure Composition where
  tense : Option (Finset Ordering)
  woll : Bool
  deriving DecidableEq

/-- Finite *will* is present tense plus *woll*. -/
def will : Composition := ⟨some ⟦present⟧, true⟩

/-- Finite *would* is past tense plus *woll*. -/
def would : Composition := ⟨some ⟦past⟧, true⟩

/-- An infinitive has no tense, with or without *woll*. -/
def infinitive (woll : Bool) : Composition := ⟨none, woll⟩

/-- The composition of each class is tenseless, with *woll* in the future class only. -/
def composition : InfinitivalTenseClass → Composition
  | .futureIrrealis => infinitive true
  | .propositional | .restructuring => infinitive false

theorem woll_iff_modP (c : InfinitivalTenseClass) :
    (composition c).woll = true ↔ c.complementSize = .modP := by
  cases c <;> decide

section Future

variable {T : Type*} [LinearOrder T]

/-- A composition with *woll* locates its event after the utterance time when present tense is
present and after the evaluation time otherwise. -/
def Composition.Locates (c : Composition) (utterance eval e : T) : Prop :=
  c.woll = true ∧ if c.tense = some ⟦present⟧ then utterance < e else eval < e

theorem will_absolute {utterance eval e : T} (h : will.Locates utterance eval e) :
    utterance < e := by
  simpa [will, Composition.Locates] using h.2

theorem infinitival_relative [DenselyOrdered T] {utterance eval : T} (h : eval < utterance) :
    ∃ e, (infinitive true).Locates utterance eval e ∧ e < utterance := by
  obtain ⟨e, h₁, h₂⟩ := exists_between h
  exact ⟨e, ⟨rfl, by simpa [infinitive] using h₁⟩, h₂⟩

end Future

/-! ### Sequence of tense -/

/-- The local tense feature of an embedded tense is the nearest tense feature above it,
infinitives contributing none. -/
def localTense : List (Option (Finset Ordering)) → Option (Finset Ordering)
  | [] => none
  | some f :: _ => some f
  | none :: rest => localTense rest

/-- Ogihara's rule lets an embedded tense delete when its local tense feature is the same
feature. -/
def sotApplies (above : List (Option (Finset Ordering))) (embedded : Finset Ordering) : Bool :=
  match localTense above with
  | some m => decide (m = embedded)
  | none => false

theorem sot_will_blocks : sotApplies [will.tense, some ⟦past⟧] ⟦past⟧ = false := by decide

theorem sot_infinitive_transparent :
    sotApplies [(infinitive true).tense, some ⟦past⟧] ⟦past⟧ = true := by
  decide

theorem sot_would : sotApplies [would.tense, some ⟦past⟧] ⟦past⟧ = true := by decide

theorem sot_will_infinitive : sotApplies [(infinitive true).tense, will.tense] ⟦past⟧ = false := by
  decide

theorem silent_would_wrong : sotApplies [would.tense, will.tense] ⟦past⟧ = true := by decide

/-- *would*'s past must delete: it is licensed only below a past. -/
def WouldLicensed (above : List (Option (Finset Ordering))) : Prop := sotApplies above ⟦past⟧ = true

instance : DecidablePred WouldLicensed := fun _ ↦ inferInstanceAs (Decidable (_ = true))

theorem would_licensing : ¬ WouldLicensed [will.tense] ∧ WouldLicensed [some ⟦past⟧] := by decide

/-! ### The data -/

section Data

open Examples

/-- A bare-episodic test row: its infinitival class, or for a finite baseline its tense, with
the reference time the matrix provides, on integer time. -/
def episodicTest? (e : Datum) : Option (InfinitivalTenseClass × NonemptyInterval ℤ) := do
  guard ((e.feature? "episodic").isSome)
  match e.feature? "class", e.feature? "tense" with
  | some "future", _ => some (.futureIrrealis, .pure 0)
  | some "propositional", _ => some (.propositional, .pure 0)
  | none, some "present" => some (.restructuring, .pure 0)
  | none, some "past" => some (.restructuring, ⟨(-1, 0), by omega⟩)
  | none, some "future" => some (.restructuring, ⟨(0, 1), by omega⟩)
  | _, _ => none

-- (2), (3), (45)
theorem episodic_rows : Datum.Checks episodicTest?
    (fun p ↦ .ofProp (Episodic p.2 (0 : ℤ) p.1)) Examples.all 6 := by
  decide

/-- An aspect test row: whether its aspect is perfective, with its class and reference time; a
*seem* with an overt or understood attitude holder is propositional, (70), and the tenseless
simultaneous row (57b) sits under a present matrix, an instant. -/
def aspectTest? (e : Datum) : Option (Bool × InfinitivalTenseClass × NonemptyInterval ℤ) := do
  let perf ← e.parse? "aspect" [("perfective", true), ("imperfective", false)]
  match e.feature? "class", e.feature? "attitude holder" with
  | some "future", _ => some (perf, .futureIrrealis, .pure 0)
  | some "propositional", _ => some (perf, .propositional, .pure 0)
  | some "tenseless simultaneous", _ => some (perf, .restructuring, .pure 0)
  | none, some _ => some (perf, .propositional, .pure 0)
  | _, _ => none

-- (53), (57), (70)
theorem aspect_rows : Datum.Checks aspectTest?
    (fun p ↦ if p.1 then .ofProp (Episodic p.2.2 (0 : ℤ) p.2.1) else .accepted)
    Examples.all 9 := by
  decide

/-- The tense stack above the lowest past, nearest first, recognized in the sentence's words:
every lexical condition is a form the English fragment declares or realizes — *promised* and
*promise* are `English.Verbs.promise.realize` at its past and base cells, *will* and *would* the
auxiliary entries, and *to tell* the infinitival marker `toInf` with `tell.realize .base`. -/
def stackOfForm? (e : Datum) : Option (List (Option (Finset Ordering))) :=
  let ts := Gloss.tokens e.primaryText
  let has (f : String) : Bool := Gloss.containsForm ts f
  let willF := English.Auxiliaries.will.form
  let wouldF := English.Auxiliaries.would.form
  let toF := English.Auxiliaries.toInf.form
  let tellB := English.Verbs.tell.realize .base
  if has (willF ++ " " ++ English.Verbs.promise.realize .base) then
    if has wouldF then some [Wurmbrand2014.will.tense]
    else if has (toF ++ " " ++ tellB) then
      some [(infinitive true).tense, Wurmbrand2014.will.tense]
    else none
  else if has (English.Verbs.promise.realize .past) then
    if has (willF ++ " " ++ tellB) then some [Wurmbrand2014.will.tense, some ⟦past⟧]
    else if has (wouldF ++ " " ++ tellB) then some [Wurmbrand2014.would.tense, some ⟦past⟧]
    else if has (toF ++ " " ++ tellB) then some [(infinitive true).tense, some ⟦past⟧]
    else none
  else none

/-- A sequence-of-tense row: its stack with the paper's applies/blocked verdict. -/
def sotTest? (e : Datum) : Option (List (Option (Finset Ordering)) × Bool) := do
  pure (← stackOfForm? e,
    ← e.parse? "SOT" [("applies", true), ("blocked", false)])

-- (24), (30)
theorem sot_rows :
    (∀ e ∈ Examples.all, ∀ p ∈ sotTest? e, sotApplies p.1 ⟦past⟧ = p.2) ∧
      Datum.ReadCount sotTest? Examples.all 5 := by
  decide +kernel

end Data

/-! ### Recognition by witness

A linearized syntactic object over a study lexicon pronounces each sequence-of-tense row's
sentence (`Minimalist.SpellsOut`), and its tense spine is the stack the reader reconstructs, so
the sequence-of-tense verdicts run on derived structure. The witnesses are right-branching
linearizations, each embedded clause a constituent; fuller argument structure is the derivation
step's work. Items take their forms from the English fragment where it declares or realizes
them; the rows' remaining words, names, pronouns and adverbs among them, enter the study lexicon
directly, the adverbs at the adpositional category for want of a closer one. -/

section Witness

open Minimalist Examples

/-- *John*. -/
def liJohn : LexicalItem.Token := ⟨.of .D [] "John", 0⟩

/-- *promised*, the matrix past, `promise` realized at its past cell. -/
def liPromised : LexicalItem.Token := ⟨.of .V [] (English.Verbs.promise.realize .past), 1⟩

/-- *promise*, the base under *will*. -/
def liPromise : LexicalItem.Token := ⟨.of .V [] (English.Verbs.promise.realize .base), 2⟩

/-- *will*, the auxiliary entry. -/
def liWill : LexicalItem.Token := ⟨.of .Mod [] English.Auxiliaries.will.form, 3⟩

/-- *would*, the auxiliary entry. -/
def liWould : LexicalItem.Token := ⟨.of .Mod [] English.Auxiliaries.would.form, 4⟩

/-- The infinitival marker, `toInf`. -/
def liTo : LexicalItem.Token := ⟨.of .T [] English.Auxiliaries.toInf.form, 5⟩

/-- *tell* at its base cell. -/
def liTell : LexicalItem.Token := ⟨.of .V [] (English.Verbs.tell.realize .base), 6⟩

/-- *that*. -/
def liThat : LexicalItem.Token := ⟨.of .C [] "that", 7⟩

/-- The lower *that*, a second token of the same item. -/
def liThat' : LexicalItem.Token := ⟨liThat.item, 8⟩

/-- *were*, the embedded past. -/
def liWere : LexicalItem.Token := ⟨.of .T [] "were", 9⟩

def liMe : LexicalItem.Token := ⟨.of .D [] "me", 10⟩
def liHe : LexicalItem.Token := ⟨.of .D [] "he", 11⟩
def liHis : LexicalItem.Token := ⟨.of .D [] "his", 12⟩
def liMother : LexicalItem.Token := ⟨.of .N [] "mother", 13⟩
def liThey : LexicalItem.Token := ⟨.of .D [] "they", 14⟩
def liHaving : LexicalItem.Token := ⟨.of .V [] "having", 15⟩
def liTheir : LexicalItem.Token := ⟨.of .D [] "their", 16⟩
def liLast : LexicalItem.Token := ⟨.of .A [] "last", 17⟩
def liMeal : LexicalItem.Token := ⟨.of .N [] "meal", 18⟩
def liTogether : LexicalItem.Token := ⟨.of .P [] "together", 19⟩
def liYesterday : LexicalItem.Token := ⟨.of .P [] "yesterday", 20⟩
def liTomorrow : LexicalItem.Token := ⟨.of .P [] "tomorrow", 21⟩
def liTonight : LexicalItem.Token := ⟨.of .P [] "tonight", 22⟩
def liWhen : LexicalItem.Token := ⟨.of .C [] "when", 23⟩

/-- The study lexicon of the sequence-of-tense sentences, the witness tokens' items. -/
def lexicon : List LexicalItem :=
  ([liJohn, liPromised, liPromise, liWill, liWould, liTo, liTell, liThat, liWere, liMe, liHe,
    liHis, liMother, liThey, liHaving, liTheir, liLast, liMeal, liTogether, liYesterday,
    liTomorrow, liTonight, liWhen] : List LexicalItem.Token).map (·.item)

/-- The deepest clause the rows share, *they were having their last meal together*. -/
def wMeal : LinearizedSyntacticObject :=
  liThey * (liWere * (liHaving * (liTheir * (liLast * (liMeal * liTogether)))))

/-- *tell his mother tomorrow* with the complement `k`. -/
def wTell (k : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  liTell * (liHis * (liMother * (liTomorrow * k)))

/-- (24a): *John promised me yesterday that he will tell … that they were … (when …)*. -/
def w24a : LinearizedSyntacticObject :=
  liJohn * (liPromised * (liMe * (liYesterday * (liThat * (liHe * (liWill *
    wTell (liThat' * (wMeal * liWhen))))))))

/-- (25a): the infinitival variant of (24a). -/
def w25a : LinearizedSyntacticObject :=
  liJohn * (liPromised * (liMe * (liYesterday * (liTo * wTell (liThat * wMeal)))))

/-- (27a): the *would* variant of (24a). -/
def w27a : LinearizedSyntacticObject :=
  liJohn * (liPromised * (liMe * (liYesterday * (liThat * (liHe * (liWould *
    wTell (liThat' * wMeal)))))))

/-- (29a): *John will promise me tonight that he would tell … that …*, the deepest clause
elided in the text. -/
def w29a : LinearizedSyntacticObject :=
  liJohn * (liWill * (liPromise * (liMe * (liTonight * (liThat * (liHe * (liWould *
    wTell ↑liThat')))))))

/-- (30a): the infinitival variant of (29a). -/
def w30a : LinearizedSyntacticObject :=
  liJohn * (liWill * (liPromise * (liMe * (liTonight * (liTo *
    wTell (liThat * (wMeal * liWhen)))))))

/-- The tense a token contributes: the finite pasts, the modal compositions, and the tenseless
infinitival marker. -/
def tenseOf (tok : LexicalItem.Token) : Option (Option (Finset Ordering)) :=
  if tok = liPromised ∨ tok = liWere then some (some ⟦past⟧)
  else if tok = liWill then some Wurmbrand2014.will.tense
  else if tok = liWould then some Wurmbrand2014.would.tense
  else if tok = liTo then some (infinitive true).tense
  else none

/-- The stack above a witness's lowest tense: its tense items in pronounced order, the lowest
dropped, nearest first. -/
def tenseSpine (t : LinearizedSyntacticObject) : List (Option (Finset Ordering)) :=
  (((Minimalist.pfYield t).filterMap fun tok ↦ tenseOf tok).dropLast).reverse

/-- The five sequence-of-tense rows with their witnesses. -/
def witnessRows : List (Datum × LinearizedSyntacticObject) :=
  [(ex_17, w24a), (ex_18, w25a), (ex_19, w27a), (ex_21, w29a), (ex_22, w30a)]

theorem witnesses_spell : ∀ p ∈ witnessRows,
    Minimalist.SpellsOut p.2 lexicon (Minimalist.pfPhon p.2) ∧
      (Minimalist.pfPhon p.2).flatMap (Gloss.tokens ·) = Gloss.tokens p.1.primaryText := by
  decide +kernel

theorem witnesses_spine : ∀ p ∈ witnessRows, ∀ s ∈ sotTest? p.1, tenseSpine p.2 = s.1 := by
  decide +kernel

end Witness

end Wurmbrand2014
