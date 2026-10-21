/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Match
public import Linglib.Phonology.OptimalityTheory.Typology
public import Mathlib.Tactic.DeriveFintype

/-!
# Itô and Mester (2019): Match as syntax–prosody MAX/DEP

Itô and Mester replace Match Theory's demand that each phrase be matched exactly by a φ with
the existential correspondence of Correspondence Theory: SP:MAX-XP asks only that each phrase have
a corresponding φ, no φ answering to two phrases. An English auxiliary reduces to an enclitic 's
phrase-medially (*Kim's leaving*) but not phrase-finally (*I wonder if Kim is*, not *Kim's*): a
final 's leaves its phrase without a φ of its own, a medial one does not. With PRIORITY of 's
unranked against Align-R(XP, φ) the medial position varies and the final one does not, a line
that exact Match cannot draw.

## Main results

* `forms_phraseFinal`, `language_michelleCan`: HEADEDNESS and MAX-XP over DEP-ω give a stranded
  function word its strong form, in a φ of its own, with no constraint that a φ end in a prosodic
  word, (18), (21), (25).
* `language_kimIsLeaving`, `language_kimIs`: the two English rankings of (41) and (42).
* `matchTheory_enclitic_final_of_medial`: under every ranking of standard Match Theory a medial
  enclitic winning makes a final one win, (43)–(46), which correspondence escapes
  (`correspondence_not_enclitic_final_of_medial`).

## Implementation notes

* A φ or ω corresponds to a phrase or lexical word when it contains its head and no foreign head
  (`Prosody.Corresponds`), and no φ answers to two phrases: a φ over a verb and a stranded
  preposition is no φ of the PP, and one φ over a subject and T serves only one of their phrases.
* Positions are terminals: the host, the function word, and the lexical word after it if any.
  Each word is one syllable, and a host's syllable realizes an enclitic 's too, so the spans of
  the prosodic tree are carried to terminal cuts by the number of terminals each syllable realizes.
* GEN pairs each form with every choice of φs over the host, over the function word and what
  follows it, and over both. A φ over nothing is no φ, so the ban on prosodic vacuity (39) needs
  no statement.
* The topmost phrase is counted, which the tableaux of (40)–(46) leave out. The flat and enclitic
  rows of (40) and (42) then have two MAX-XP violations, not one; exact Match(ω, lex) counts
  ω(Kim's), which spans the enclitic, as (43)–(46) do not; and PRIORITY counts *əs* in (42) as it
  does in (41). No winner changes.

## References

* [ito-mester-2019]
* [mccarthy-prince-1995]
* [selkirk-1996]
* [selkirk-2011]
* [mascaro-2007]
-/

@[expose] public section

namespace ItoMester2019

open Prosody OptimalityTheory

/-! ### Inputs and candidates -/

/-- A function word after a lexical host, and the phrases over them. -/
structure Input where
  /-- The host is a phrase of its own, a subject before T as in (21), not a verb before its
  complement as in (18). -/
  hostPhrase : Bool
  /-- The function word heads a phrase over itself and what follows, PP[at __] or TP[is leaving],
  not an object pronoun inside the verb (24b). -/
  fncPhrase : Bool
  /-- A lexical word follows the function word in its phrase, TP[is leaving], not a gap. -/
  next : Bool
  /-- The function word has a monoconsonantal allomorph, the 's of *is* (27). -/
  clitic : Bool
  deriving DecidableEq

namespace Input

variable (x : Input)

/-- The phrases, in terminals, each with its head: the topmost phrase, headed by the host unless
the host is a phrase of its own, the host's, and the function word's, headed by the lexical word
after the function word, the phrase being that word's extended projection (fn. 3), or else by the
function word. -/
def phrases : List ((ℕ × ℕ) × ℕ) :=
  let n := if x.next then 3 else 2
  let h := if x.next then 2 else 1
  ((0, n), if x.hostPhrase then h else 0) ::
    ((if x.hostPhrase then [((0, 1), 0)] else []) ++ if x.fncPhrase then [((1, n), h)] else [])

/-- The lexical words, in terminals, each its own head: the host and the word after the function
word. -/
def lex : List ((ℕ × ℕ) × ℕ) := ((0, 1), 0) :: if x.next then [((2, 3), 2)] else []

end Input

/-- *What did Mary look at __*, VP[look PP[at]] (18); *see you* with a phrasal object (25a) has
the same structure. -/
def lookAt : Input := ⟨false, true, false, false⟩

/-- *I can eat more than Michelle can __*, TP[DP[Michelle] TP[can]] (21). -/
def michelleCan : Input := ⟨true, true, false, false⟩

/-- *see ya*, the object pronoun an enclitic inside the verb, VP[see-Pro DP[__]] (25b). -/
def seeYa : Input := ⟨false, false, false, false⟩

/-- *I wonder if Kim is leaving*, TP[NP[Kim] TP[is leaving]] (41). -/
def kimIsLeaving : Input := ⟨true, true, true, true⟩

/-- *Tim's leaving if Kim is __*, TP[NP[Kim] TP[is]] (42). -/
def kimIs : Input := ⟨true, true, false, true⟩

/-- The forms of a function word. -/
inductive Form
  /-- A prosodic word of its own, *ìs*, *kǽn*, *ǽt*. -/
  | strong
  /-- A syllable, *əs*, *kən*, *ət*. -/
  | weak
  /-- The consonant 's in the final syllable of the host, *Kim's*. -/
  | enclitic
  /-- The consonant 's at the beginning of the next word, *'sleaving*. -/
  | proclitic
  deriving DecidableEq, Repr

/-- A candidate: a form of the function word and the φs over the words. -/
structure Candidate where
  /-- The form of the function word. -/
  form : Form
  /-- A φ over the host. -/
  host : Bool
  /-- A φ over the function word and what follows it. -/
  fnc : Bool
  /-- A φ over both. -/
  top : Bool
  deriving DecidableEq

/-- GEN: each available form, strong and weak, and 's where the word has it, proclitic only before
a word, under each choice of φs. -/
def candidates (x : Input) : Finset Candidate :=
  let forms : List Form :=
    [.strong, .weak] ++ if x.clitic then .enclitic :: if x.next then [.proclitic] else [] else []
  (forms.flatMap fun f ↦ [false, true].flatMap fun h ↦ [false, true].flatMap fun g ↦
    [false, true].map fun t ↦ (⟨f, h, g, t⟩ : Candidate)).toFinset

/-- A lexical word, or a function word in its strong form: a prosodic word over a foot over its
syllable. -/
def word : Tree := .om [.ft true [.σ 0 true]]

namespace Candidate

variable (x : Input) (c : Candidate)

/-- The prosodic tree: an intonational phrase over the chosen φs, over the host and the function
word and what follows it, an enclitic or proclitic having no syllable of its own; a φ over nothing
is none. -/
def tree : Tree :=
  let tail := (match c.form with | .strong => [word] | .weak => [.σ] | _ => []) ++
    if x.next then [word] else []
  .node .iota (wrap c.top (wrap c.host [word] ++ wrap c.fnc tail))
where
  /-- A φ over a nonempty list of nodes, if chosen. -/
  wrap (b : Bool) (l : List Tree) : List Tree := if b ∧ l ≠ [] then [Tree.ph l] else l

/-- The spans of the `ℓ`-nodes, in terminals, each syllable realizing one terminal and a second
where it holds 's. -/
def spans (ℓ : Level) : List (ℕ × ℕ) :=
  let realizes := [if c.form = .enclitic then 2 else 1] ++
    (if c.form = .strong ∨ c.form = .weak then [1] else []) ++
      if x.next then [if c.form = .proclitic then 2 else 1] else []
  let cut (i : ℕ) := (realizes.take i).sum
  (levelSpans ℓ (c.tree x)).map (Prod.map cut cut)

end Candidate

/-! ### Constraints -/

/-- The constraint slots of (41)–(46). The two theories fill the phrase and word slots
differently. -/
inductive Con
  | initFaith | headedness | phrase | alignR | priority | word
  deriving DecidableEq, Repr, Fintype

/-- The correspondence-theoretic system: SP:MAX-XP fills the phrase slot and PS:DEP-ω the word
slot, a φ or ω corresponding to a phrase or lexical word when it contains its head and no foreign
one (`Prosody.Corresponds`). INIT-FAITH (34) counts each ω corresponding to a lexical word but
beginning where none does, as ω('sleaving) does, and PRIORITY ([mascaro-2007]) each form of *is*
where 's is available. HEADEDNESS ([selkirk-1996]) counts each node above the syllable
immediately dominating no node of its own level or the level below, as a φ over a lone syllable
does. -/
def correspondence : ConstraintSystem Input Candidate Con where
  gen := candidates
  con
    | .initFaith => Constraint.alignLeft.comap fun xc ↦
        ((xc.2.spans xc.1 .om).filter fun w ↦ ∃ l ∈ xc.1.lex, Corresponds xc.1.lex l w,
          xc.1.lex.map (·.1))
    | .headedness => fun xc ↦ (xc.2.tree xc.1).subtrees.countP fun s ↦
        s.value.level ≠ .syl ∧ ∀ c ∈ s.children,
          c.value.level ≠ s.value.level ∧ c.value.level.toNat + 1 ≠ s.value.level.toNat
    | .phrase => fun xc ↦
        Constraint.deficiency (Corresponds xc.1.phrases) (xc.1.phrases, xc.2.spans xc.1 .ph)
    | .alignR => Constraint.alignRight.comap fun xc ↦
        (xc.1.phrases.map (·.1), xc.2.spans xc.1 .ph)
    | .priority => fun xc ↦
        if xc.1.clitic ∧ (xc.2.form = .strong ∨ xc.2.form = .weak) then 1 else 0
    | .word => fun xc ↦ Constraint.align (fun w l ↦ Corresponds xc.1.lex l w)
        (xc.2.spans xc.1 .om, xc.1.lex)

/-- Standard Match Theory: MATCH-PHRASE, each phrase the span of a φ, fills the phrase slot, and
MATCH-ω, each ω the span of a lexical word, the word slot. -/
def matchTheory : ConstraintSystem Input Candidate Con where
  gen := candidates
  con
    | .phrase => (Constraint.align Eq).comap fun xc ↦
        (xc.1.phrases.map (·.1), xc.2.spans xc.1 .ph)
    | .word => (Constraint.align Eq).comap fun xc ↦ (xc.2.spans xc.1 .om, xc.1.lex.map (·.1))
    | i => correspondence.con i

/-- MAX-XP asks no more than MATCH-PHRASE of any candidate, `Prosody.deficiency_corresponds_le` on
terminal spans. -/
theorem phrase_le (x : Input) (c : Candidate) :
    correspondence.con .phrase (x, c) ≤ matchTheory.con .phrase (x, c) := by
  have hx : (x.phrases.map (·.1)).Nodup ∧ ∀ a ∈ x.phrases, a.2 ∈ Set.Ico a.1.1 a.1.2 := by
    obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := x <;> decide
  exact deficiency_corresponds_le hx.1 hx.2 (c.spans x .ph)

/-! ### English -/

/-- English with Align-R over PRIORITY, (41a) and (42a). -/
def alignFirst : Ranking Con 6 :=
  Ranking.ofList [.initFaith, .headedness, .phrase, .alignR, .priority, .word]

/-- English with PRIORITY over Align-R, (41b) and (42b). -/
def priorityFirst : Ranking Con 6 :=
  Ranking.ofList [.initFaith, .headedness, .phrase, .priority, .alignR, .word]

/-- **No StrongEnd** (18), (25): a function word stranded at the end of its phrase takes its strong
form, HEADEDNESS barring a φ over a lone syllable and MAX-XP requiring the φ, while an object
pronoun inside the verb, heading no phrase, is weak; no constraint asks a φ to end in a prosodic
word. -/
theorem forms_phraseFinal :
    ∀ r ∈ [alignFirst, priorityFirst],
      (correspondence.language r lookAt).image (·.form) = {.strong} ∧
      (correspondence.language r seeYa).image (·.form) = {.weak} := by
  decide +kernel

/-- **Recursive phrasing** (21): φ(φ(Michelle) φ(kǽn)), the higher TP needing a φ of its own. -/
theorem language_michelleCan :
    ∀ r ∈ [alignFirst, priorityFirst],
      correspondence.language r michelleCan = {⟨.strong, true, true, true⟩} := by
  decide +kernel

/-- **Variation phrase-medially** (41): φ(Kim) φ(əs leaving) where Align-R(XP, φ) outranks
PRIORITY, φ(Kim's) φ(leaving) where PRIORITY outranks it. -/
theorem language_kimIsLeaving :
    correspondence.language alignFirst kimIsLeaving = {⟨.weak, true, true, true⟩} ∧
      correspondence.language priorityFirst kimIsLeaving = {⟨.enclitic, true, true, true⟩} := by
  decide +kernel

/-- **No phrase-final enclisis** (42): under both rankings φ(Kim) φ(ìs), since a final 's leaves TP
without a φ of its own. -/
theorem language_kimIs :
    ∀ r ∈ [alignFirst, priorityFirst],
      correspondence.language r kimIs = {⟨.strong, true, true, true⟩} := by
  decide +kernel

/-! ### Exact Match -/

private theorem final_le_medial :
    ∀ c ∈ candidates kimIsLeaving, c.form = .enclitic → ∃ d ∈ candidates kimIs, d.form = .enclitic ∧
      ∀ i, matchTheory.con i (kimIs, d) ≤ matchTheory.con i (kimIsLeaving, c) := by
  decide +kernel

private theorem medial_le_final :
    ∀ d ∈ candidates kimIs, ∃ c ∈ candidates kimIsLeaving,
      ∀ i, matchTheory.con i (kimIsLeaving, c) ≤ matchTheory.con i (kimIs, d) := by
  decide +kernel

/-- **Exact Match cannot separate medial from final enclisis** (43)–(46): under every ranking of
standard Match Theory, an enclitic winning in *Kim 's leaving* makes one win in *Kim 's*, so the
English pattern, which `language_kimIsLeaving` and `language_kimIs` derive under correspondence, is
out of its reach. -/
theorem matchTheory_enclitic_final_of_medial (r : Ranking Con 6)
    (h : Form.enclitic ∈ (matchTheory.language r kimIsLeaving).image (·.form)) :
    Form.enclitic ∈ (matchTheory.language r kimIs).image (·.form) := by
  obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 h
  obtain ⟨d, hd, hde, hdc⟩ :=
    final_le_medial c (Tableau.optimal_subset hc) hce
  exact Finset.mem_image.2 ⟨d, Tableau.ofRanking_mem_optimal_of_forall_le hc hd hdc
    medial_le_final, hde⟩

/-- Existential correspondence draws the line: under `priorityFirst` an enclitic wins in
*Kim 's leaving* and none in *Kim 's*, against the implication exact Match obeys. -/
theorem correspondence_not_enclitic_final_of_medial :
    ¬ ∀ r : Ranking Con 6,
      Form.enclitic ∈ (correspondence.language r kimIsLeaving).image (·.form) →
        Form.enclitic ∈ (correspondence.language r kimIs).image (·.form) := fun h ↦ by
  simpa [language_kimIs priorityFirst (by simp)] using
    h priorityFirst (by simp [language_kimIsLeaving.2])

end ItoMester2019
