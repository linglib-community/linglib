module

public import Linglib.Data.Examples.ChanShen2026
public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Linglib.Syntax.Minimalist.SyntacticObject.Locality

/-!
# Chan and Shen (2026): Conditions on *wh-the-hell* licensing

A Singlish single wh-question fronts its wh-phrase, moves it to an intermediate Spec-CP, or leaves
it in situ, and Chan and Shen's acceptability experiment, two 2×2 designs in the manner of
Sprouse, Wagers and Phillips, finds that *the-hell* survives the first two and not the third. On
their account the modifier's point-of-view feature is checked in matrix Spec-CP, after Chou, and
*the-hell*, adjoined to the wh-head after Merchant, gets there only inside its wh-phrase; partial
movement reaches matrix Spec-CP by a covert step and an in-situ wh-phrase is bound unselectively,
after Sato and Ngui. Mandarin *daodi* moves on its own. The intervention account of den Dikken and
Giannakidou and the attitude-phrase account of Vu and Lohiniva each miss one strategy (Table 5).

## Main definitions

* `full`, `partialMovement`, `bound`: the structures (7), (14), (8); `covert`, Huang's LF movement.
* `PartOf`, `Licensed`: a modifier is licensed when a phrase it is part of takes scope in matrix
  Spec-CP.
* `Intervention.Licensed`, `AttP.Licensed`: the rival accounts.

## Main statements

* `licensed_theHell_iff`: *the-hell* is licensed iff its wh-phrase takes scope in matrix Spec-CP.
* `licensed_daodi`: *daodi* is licensed over a wh-phrase in situ.
* `licensed_iff_intervention_multiple`: in English multiple questions the accounts agree.
* `ascription_rows`, `intervention_rows`, `attP_rows`, `island_rows`: the accounts against the
  rows; `covert_mispredicts`: covert movement gets the island and modifier facts wrong.

## Implementation notes

The structures are schematic Singlish questions (2), (11), which the Malay and Mandarin rows
share, since what the accounts read, the chains and where their copies are pronounced, is the
same; the English rows are multiple questions with the subject wh-phrase fronted. Planar objects
have no pair-Merge, so *the-hell* adjoined to the wh-head is merged as the head's complement: the
head projects, as the host of an adjunct does, and every copy of the wh-phrase carries the
modifier. The schematic clauses have no T, so C selects the verb phrase and each verb selects its
subject as well as its complement.

## References

* [chan-shen-2026]
* [chou-2012]
* [merchant-2002]
* [sato-2013]
* [sato-ngui-2017]
* [huang-1982]
* [cole-hermon-1998]
* [pesetsky-1987]
* [martin-2020]
* [rawlins-2008]
* [ippolito-2024]
* [hoeksema-napoli-2008]
* [jackendoff-audring-2020]
* [den-dikken-giannakidou-2002]
* [linebarger-1987]
* [vu-lohiniva-2020]
* [huang-ochi-2004]
* [sprouse-et-al-2012]
-/

@[expose] public section

namespace ChanShen2026

open Minimalist Core.Order RoseTree

/-! ### The lexicon -/

/-- A token of the schematic questions. -/
def tok (id : ℕ) (cat : Cat) (sel : SelStack := []) (phon : String := "") (wh : Bool := false) :
    LexicalItem.Token :=
  ⟨LexicalItem.of cat sel phon wh false, id⟩

/-- The wh-phrase of the single questions. -/
def what := tok 0 .D (phon := "what") (wh := true)
/-- The matrix interrogative C and the embedded C. -/
def c₁ := tok 1 .C [.V]
def c₂ := tok 2 .C [.V]
def you := tok 3 .D (phon := "you")
def think := tok 4 .V [.C, .D] "think"
def natalie := tok 5 .D (phon := "Natalie")
def baking := tok 6 .V [.D, .D] "baking"
/-- The complex NP of (11): *John like the man that think Mary eat …*. -/
def john := tok 7 .D (phon := "John")
def like := tok 8 .V [.D, .D] "like"
def the := tok 9 .D [.N] "the"
def man := tok 10 .N [.C] "man"
def that := tok 11 .C [.V] "that"
def mary := tok 12 .D (phon := "Mary")
def eat := tok 13 .V [.D, .D] "eat"
/-- *Think* in the relative clause, whose subject is relativized. -/
def thinkRel := tok 14 .V [.C] "think"
/-- *The hell*, one of a family of taboo-term wh-modifiers with *the heck* and *in the world*
([hoeksema-napoli-2008], [jackendoff-audring-2020]), which Chan and Shen expect to behave alike
where Singlish has them. -/
def theHell := tok 15 .D (phon := "the hell")
/-- The wh-heads that host *the-hell*. -/
def whatH := tok 16 .D [.D] "what" (wh := true)
def whoH := tok 17 .D [.D] "who" (wh := true)
/-- Mandarin *daodi*, an adverb in the clause of the wh-phrase it modifies; nothing selects it. -/
def daodi := tok 18 .A (phon := "daodi")
/-- The English multiple questions (1), (25), (26). -/
def who := tok 19 .D (phon := "who") (wh := true)
def loves := tok 20 .V [.D, .D] "loves"

/-! ### The three strategies (7), (8), (14) -/

/-- A wh-phrase is pronounced as `phrase`, and its deleted copies are those of its head. -/
structure WhPhrase where
  head : LexicalItem.Token
  phrase : PlanarSyntacticObject

/-- A bare wh-phrase. -/
def WhPhrase.bare (w : LexicalItem.Token) : WhPhrase := ⟨w, w⟩

/-- The wh-phrase headed by `w` with `m` adjoined to its head. -/
def WhPhrase.adjoin (w m : LexicalItem.Token) : WhPhrase := ⟨w, (w : PlanarSyntacticObject) * m⟩

/-- *What the hell*. -/
def whatTheHell : WhPhrase := .adjoin whatH theHell

/-- The embedded CP, *Natalie baking x* or, in the island, *Mary eat x*, with `spec` in its
specifier. -/
def embedded (island : Bool) (spec : Option PlanarSyntacticObject) (x : PlanarSyntacticObject) :
    PlanarSyntacticObject :=
  let tp := if island then mary * (eat * x) else natalie * (baking * x)
  (spec.map (· * (c₂ * tp))).getD (c₂ * tp)

/-- The matrix CP over the embedded one, *you think …* or, in the island, *John like the man that
think …*, with `spec` in matrix Spec-CP. -/
def matrix (island : Bool) (spec : Option PlanarSyntacticObject) (emb : PlanarSyntacticObject) :
    PlanarSyntacticObject :=
  let vp := if island then john * (like * (the * (man * (that * (thinkRel * emb)))))
    else you * (think * emb)
  (spec.map (· * (c₁ * vp))).getD (c₁ * vp)

variable (w : WhPhrase) (island : Bool)

/-- (7): full movement, successive cyclic, the top copy pronounced. -/
def full : PlanarSyntacticObject :=
  matrix island (some w.phrase) (embedded island (some (.traceOf w.head)) (.traceOf w.head))

/-- (14): partial movement, overt to the intermediate Spec-CP and covert from there. -/
def partialMovement : PlanarSyntacticObject :=
  matrix island (some (.traceOf w.head)) (embedded island (some w.phrase) (.traceOf w.head))

/-- (8): the wh-phrase in situ, bound by the question operator: one copy. -/
def bound : PlanarSyntacticObject :=
  matrix island none (embedded island none w.phrase)

/-- The LF-movement analysis of wh-in-situ ([huang-1982]): a deleted copy in matrix Spec-CP over
the pronounced one. -/
def covert : PlanarSyntacticObject :=
  matrix island (some (.traceOf w.head)) (embedded island none w.phrase)

/-- (19): *daodi* before the verb of the embedded clause over a wh-phrase in situ, moved covertly
on its own to the embedded and then the matrix point-of-view operator ([chou-2012]'s (31c)),
which Chan and Shen place in Spec-CP. -/
def daodiQuestion : PlanarSyntacticObject :=
  matrix false (some (.traceOf daodi))
    (.traceOf daodi * (c₂ * (natalie * (daodi * (baking * what)))))

/-- An English multiple question, the subject wh-phrase fronted over the object in situ. -/
def multiple (subj obj : WhPhrase) : PlanarSyntacticObject :=
  subj.phrase * (c₁ * (.traceOf subj.head * (loves * obj.phrase)))

variable (t : PlanarSyntacticObject)

/-- The chain of `h` takes scope in matrix Spec-CP: the phrase of a copy at its top is there. -/
def ReachesScope (h : LexicalItem.Token) : Prop :=
  ∃ p ∈ chainTop t h, projectionAt t p = ⟨[0]⟩

instance (h : LexicalItem.Token) : Decidable (ReachesScope t h) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- `m` is pronounced in matrix Spec-CP. -/
def PronouncedAtScope (m : LexicalItem.Token) : Prop :=
  ∃ q ∈ occurrences t m, (⟨[0]⟩ : TreePath) ≤ q

instance (m : LexicalItem.Token) : Decidable (PronouncedAtScope t m) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Full and partial movement reach matrix Spec-CP, the latter pronounced lower; the bound
wh-phrase stays in situ ((7), (14), (8)). -/
example : (ReachesScope (full (.bare what) false) what ∧
      PronouncedAtScope (full (.bare what) false) what) ∧
    (ReachesScope (partialMovement (.bare what) false) what ∧
      ¬ PronouncedAtScope (partialMovement (.bare what) false) what) ∧
    ¬ ReachesScope (bound (.bare what) false) what := by
  decide

/-- Covert movement pronounces the in-situ string. -/
example : ∀ w ∈ [.bare what, whatTheHell], ∀ island : Bool,
    pfYield (covert w island) = pfYield (bound w island) := by
  decide

/-! ### Negative attitude ascription (§3.2–3.3) -/

/-- `m` is part of the phrase of `h`: a pronounced copy of `m` lies in the phrase a pronounced
copy of `h` heads, so that every copy of `h` carries `m`. Every token is part of its own phrase. -/
def PartOf (m h : LexicalItem.Token) : Prop :=
  ∃ p ∈ occurrences t h, ∃ q ∈ occurrences t m, projectionAt t p ≤ q

instance (m h : LexicalItem.Token) : Decidable (PartOf t m h) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The modifier's point-of-view feature is checked in matrix Spec-CP, which ascribes its
negative attitude (surprise, [pesetsky-1987]; ignorance of the answer, [martin-2020]; doubt of
every answer, [rawlins-2008], [ippolito-2024]) to the speaker, so it is licensed iff it is there
at the end of the derivation: iff a phrase it is part of, its own or its host's, takes scope
there. -/
def Licensed (m : LexicalItem.Token) : Prop :=
  ∃ x ∈ tokenList t.val, PartOf t m x.2 ∧ ReachesScope t x.2

instance (m : LexicalItem.Token) : Decidable (Licensed t m) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- *The-hell* is licensed iff its wh-phrase takes scope in matrix Spec-CP ((20), (21), (24)). -/
theorem licensed_theHell_iff : ∀ s ∈ [full, partialMovement, bound, covert], ∀ island : Bool,
    Licensed (s whatTheHell island) theHell ↔ ReachesScope (s whatTheHell island) whatH := by
  decide

/-- Across the three strategies, *the-hell* is out exactly in situ ((3a–c)). -/
example : Licensed (full whatTheHell false) theHell ∧
    Licensed (partialMovement whatTheHell false) theHell ∧
    ¬ Licensed (bound whatTheHell false) theHell := by
  decide

/-- *Daodi* is licensed over a wh-phrase in situ ((19)). -/
theorem licensed_daodi : Licensed daodiQuestion daodi ∧ ¬ ReachesScope daodiQuestion what := by
  decide

/-! ### Rival accounts (§3.4) -/

/-- [den-dikken-giannakidou-2002]: *wh-the-hell* is a polarity item licensed in the immediate
scope of the question operator ([linebarger-1987]), which a wh-phrase c-commanding it blocks. -/
def Intervention.Licensed (m : LexicalItem.Token) : Prop :=
  ∃ q ∈ occurrences t m, ∀ x ∈ tokenList t.val, x.2.item.wh = true → ¬ PartOf t m x.2 →
    ¬ CCommands t.val (projectionAt t x.1) q

instance (m : LexicalItem.Token) : Decidable (Intervention.Licensed t m) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- [vu-lohiniva-2020]: *the-hell* is base-generated in the specifier of a matrix attitude
phrase, whose [+wh] feature the nearest wh-phrase checks by moving there before the pair moves
to Spec-CP; a *wh-the-hell* string therefore surfaces only in matrix Spec-CP. -/
def AttP.Licensed (m : LexicalItem.Token) : Prop := PronouncedAtScope t m

instance (m : LexicalItem.Token) : Decidable (AttP.Licensed t m) :=
  inferInstanceAs (Decidable (PronouncedAtScope _ _))

/-- In an English multiple question the in-situ wh-phrase is under the fronted one, so in situ
and intervened coincide and ascription agrees with intervention ((1), (25), (26)). -/
theorem licensed_iff_intervention_multiple :
    ∀ t ∈ [multiple (.adjoin whoH theHell) (.bare what), multiple (.bare who) whatTheHell],
      (Licensed t theHell ↔ Intervention.Licensed t theHell) := by
  decide

/-- The two part only where a single question leaves its wh-phrase in situ. -/
example : Intervention.Licensed (bound whatTheHell false) theHell ∧
    ¬ Licensed (bound whatTheHell false) theHell := by
  decide

/-! ### The data -/

/-- The structure of a row: its strategy, in a complex NP or not, with the modifier it records
and an in-situ wh-phrase construed by `inSitu`; a multiple question fronts its subject. -/
def structureOf (inSitu : WhPhrase → Bool → PlanarSyntacticObject) (e : Datum) :
    Option PlanarSyntacticObject :=
  let island := e.feature? "island" = some "complexNP"
  let hell := e.feature? "modifier" = some "theHell"
  if e.feature? "modifier" = some "daodi" then some daodiQuestion
  else if e.feature? "question" = some "multiple" then
    e.parse? "strategy"
      [("full", multiple (if hell then .adjoin whoH theHell else .bare who) (.bare what)),
       ("inSitu", multiple (.bare who) (if hell then whatTheHell else .bare what))]
  else
    let w : WhPhrase := if hell then whatTheHell else .bare what
    e.parse? "strategy"
      [("full", full w island), ("partial", partialMovement w island), ("inSitu", inSitu w island)]

/-- A row's modifier. -/
def modifierOf (e : Datum) : Option LexicalItem.Token :=
  e.parse? "modifier" [("theHell", theHell), ("daodi", daodi)]

/-- Every row with a modifier has a structure, so the statements below range over all of them. -/
theorem structureOf_isSome :
    ∀ e ∈ Examples.all, (modifierOf e).isSome → (structureOf bound e).isSome := by
  decide

/-- Extraction fails when a link of the wh-phrase's chain leaves the complex NP. -/
def CrossesIsland : Prop := ∃ h ∈ occurrences t the, Escapes t what (projectionAt t h)

instance : Decidable (CrossesIsland t) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Extraction from a complex NP fails exactly where a link of the chain leaves it: under full
movement, and under partial movement by its covert step, but not in situ ((11), (15), Malay
(17)). -/
theorem island_rows : ∀ e ∈ Examples.all, e.feature? "island" = some "complexNP" →
    ∀ t ∈ structureOf bound e, (CrossesIsland t ↔ e.judgment ≠ .acceptable) := by
  decide

/-- Ascription predicts every modifier row: English (1), (25), (26), the experiment's (4) and
(6), the subject question (22), and Mandarin (19). -/
theorem ascription_rows : ∀ e ∈ Examples.all, ∀ m ∈ modifierOf e, ∀ t ∈ structureOf bound e,
    (Licensed t m ↔ e.judgment = .acceptable) := by
  decide

/-- Intervention is right except on the in-situ single questions ((4d), (22b)): nothing
intervenes, yet *the-hell* is out. -/
theorem intervention_rows :
    ∀ e ∈ Examples.all, e.feature? "modifier" = some "theHell" → ∀ t ∈ structureOf bound e,
      ((Intervention.Licensed t theHell ↔ e.judgment = .acceptable) ↔
        (Licensed t theHell ∨ ¬ Intervention.Licensed t theHell)) := by
  decide

/-- The attitude phrase is right except under partial movement ((6d)), where *the-hell* takes
scope from a position it is not pronounced in. -/
theorem attP_rows :
    ∀ e ∈ Examples.all, e.feature? "modifier" = some "theHell" → ∀ t ∈ structureOf bound e,
      ((AttP.Licensed t theHell ↔ e.judgment = .acceptable) ↔
        (Licensed t theHell → PronouncedAtScope t theHell)) := by
  decide

/-- Covert movement of the in-situ wh-phrase crosses the complex NP of (11b) and licenses
*the-hell* in the in-situ question (4d), both acceptable and unacceptable the other way round:
the island facts and the modifier facts each choose binding ([sato-ngui-2017]). -/
theorem covert_mispredicts :
    (∃ t ∈ structureOf covert Examples.ex11b, CrossesIsland t) ∧
      Examples.ex11b.judgment = .acceptable ∧
      (∃ m ∈ modifierOf Examples.ex4d, ∃ t ∈ structureOf covert Examples.ex4d, Licensed t m) ∧
      Examples.ex4d.judgment = .ungrammatical := by
  decide

end ChanShen2026
