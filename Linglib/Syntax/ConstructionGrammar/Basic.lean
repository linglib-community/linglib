/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.UD.UPOS
public import Mathlib.Data.List.Dedup

/-!
# Constructions

A construction is a learned pairing of a form and a meaning, for Goldberg the basic unit of
grammatical knowledge. The form side is a `TypedForm`, a sequence of `Slot`s, each fixing a
lexeme, opening a category, or admitting any phrase, and a construction's `Specificity` is derived
from its slot structure rather than stipulated.

## Main definitions

* `SlotFiller`, `Slot`, `TypedForm`: the typed form side
* `RepresentationLevel`, `SlotFiller.level`: the level of a slot's content
* `derivedSpecificity`, `HasConstraint`, `refGroupCount`: measures derived
  from forms
* `Construction`, `Construction.specificity`, `Construction.map`: typed
  form–meaning pairings
* `Construction.IsFullyCompositional`, `Construction.IsFormalIdiom`: analyzability by the
  universal combination schemata, and lexical openness

## References

* [goldberg-2006]
* [goldberg-2003]
* [goldberg-1995]
* [dunn-2025]
* [kay-fillmore-1999]
* [fillmore-kay-oconnor-1988]
* [goldberg-shirtz-2025]
* [mueller-2013]
* [kay-michaelis-2019]
-/

@[expose] public section

namespace ConstructionGrammar

/-- The specificity of a construction is how fully its form side is specified, along
[goldberg-2003]'s degree-of-abstraction continuum as [goldberg-shirtz-2025]'s Table 8
discretizes it. -/
inductive Specificity where
  /-- Every slot is lexically filled, as in *veggie-wrap* and *must-read*. -/
  | lexicallySpecified
  /-- Fixed and open slots are mixed, as in *N-wrap* and *a simple ⟨PAL⟩*. -/
  | partiallyOpen
  /-- Every slot is open, as in [N⁰ N⁰ N⁰] and [N′ PAL⁰ N]. -/
  | fullyAbstract
  deriving Repr, DecidableEq

/-! ### Typed slots

Slot content follows [dunn-2025]'s three representation levels, a fixed lexeme (LEX), a word of
a category (SYN) and a semantic constraint (SEM), with the categories the parts of speech of
Universal Dependencies where Dunn's are learned, plus [kay-fillmore-1999]'s headed phrases,
grammatical functions, coreference indices and slot constraints. -/

/-- A slot's filler gives the slot's content at one of the representation levels. It is
parameterized over the lexeme type `Lex`, so the same representation works for strings,
morphemes, or phonological forms. -/
inductive SlotFiller (Lex : Type*) where
  /-- `fixed w` is the word form `w` itself, at the LEX level, as `fixed "must"`. -/
  | fixed : Lex → SlotFiller Lex
  /-- `open_ pos` is any word of part of speech `pos`, as `open_ .VERB`. -/
  | open_ : UD.UPOS → SlotFiller Lex
  /-- `headed w pos` is a phrase of part of speech `pos` headed by the lexeme `w`
      ([kay-fillmore-1999]), so `headed "doing" .VERB` is a VP headed by *doing*. It is at the
      LEX level, since the head lexeme is fixed even though the phrase is open. -/
  | headed : Lex → UD.UPOS → SlotFiller Lex
  /-- `semantic c` is any expression meeting the semantic constraint `c`, at the SEM level
      ([dunn-2025]), so `semantic "animate"` is any expression denoting an animate. -/
  | semantic : String → SlotFiller Lex
  /-- `phrasal` is any phrase, with no fixed head and no category restriction on its internal
      structure, the filler of a phrasal-compound or PAL slot (the ⟨phrase⟩ node of
      [goldberg-shirtz-2025]'s Figure 5). -/
  | phrasal : SlotFiller Lex
  deriving DecidableEq, Repr

/-- A filler is open when no lexeme anchors it. The `open_`, `semantic` and `phrasal` fillers
are open, while `fixed` and `headed` are not, the latter fixing its head lexeme even though the
phrase is open. -/
def SlotFiller.IsOpen {Lex : Type*} : SlotFiller Lex → Prop
  | .fixed _ | .headed _ _ => False
  | .open_ _ | .semantic _ | .phrasal => True

instance {Lex : Type*} : DecidablePred (SlotFiller.IsOpen (Lex := Lex))
  | .fixed _ | .headed _ _ => isFalse id
  | .open_ _ | .semantic _ | .phrasal => isTrue trivial

/-- A representation level is one of [dunn-2025]'s three ontologies of slot-constraints. -/
inductive RepresentationLevel where
  /-- A lexical constraint, LEX, fixes a lexeme. -/
  | lex
  /-- A syntactic constraint, SYN, admits the words of a category. -/
  | syn
  /-- A semantic constraint, SEM, admits the expressions that meet it. -/
  | sem
  deriving DecidableEq, Repr, Fintype

/-- `f.level` is lexical for fixed lexemes and headed phrases, syntactic for categories and
phrases, and semantic for semantic constraints. -/
def SlotFiller.level {Lex : Type*} : SlotFiller Lex → RepresentationLevel
  | .fixed _ | .headed _ _ => .lex
  | .open_ _ | .phrasal => .syn
  | .semantic _ => .sem

theorem SlotFiller.isOpen_iff_level_ne_lex {Lex : Type*} (f : SlotFiller Lex) :
    f.IsOpen ↔ f.level ≠ .lex := by
  cases f <;> simp [SlotFiller.IsOpen, SlotFiller.level]

/-- The grammatical function of a valence member ([kay-fillmore-1999], Figure 12) is distinct
from its semantic role, since a subject can be an agent, a theme, or an experiencer. -/
inductive GrammaticalFunction where
  /-- `subj` is the subject. -/
  | subj
  /-- `comp` is a clausal or verbal complement. -/
  | comp
  /-- `obj` is the direct object. -/
  | obj
  deriving DecidableEq, Repr

/-- A reference index marks unification across slots, [kay-fillmore-1999]'s #1 and #2; values
bearing one index are unified. -/
abbrev RefIndex := Nat

/-- A slot constraint is a syntactic constraint on a slot ([kay-fillmore-1999], Figure 12). -/
inductive SlotConstraint where
  /-- `[loc -]` requires the slot to occur left-isolated, not VP-internal. -/
  | locMinus
  /-- `[neg -]` forbids negating the slot. -/
  | negMinus
  /-- `[ref ∅]` marks the slot as no operator, "in the sense of binding the reference of something
      else". -/
  | refEmpty
  deriving DecidableEq, Repr

/-- A slot in a construction's form has a filler, a headedness flag, and Kay and Fillmore's
lexicality of the position, where `lex := none` leaves it unspecified; their maximality is not
stored, since a head is nonmaximal and every other daughter maximal. A slot's semantics bears
its `refIdx`, and a predicate phrase that does not realize its own subject bears the index of that
subject requirement as its `subjIdx`. Coinstantiation, which covers raising and control, unifies a
predicator's subject with the subject requirement of its complement ([kay-fillmore-1999],
Figure 13). -/
structure Slot (Lex : Type*) where
  /-- `filler` is what fills the slot. -/
  filler : SlotFiller Lex
  /-- `isHead` records whether the slot is the head of the construction. -/
  isHead : Bool := false
  /-- `lex` says whether the position is a word, `some true` for a word-level slot. -/
  lex : Option Bool := none
  /-- `gf` is the slot's grammatical function ([kay-fillmore-1999]). -/
  gf : Option GrammaticalFunction := none
  /-- `refIdx` is the index of the slot's semantics. -/
  refIdx : Option RefIndex := none
  /-- `subjIdx` is the index of the slot's unrealized subject requirement. -/
  subjIdx : Option RefIndex := none
  /-- `constraints` lists the slot's syntactic constraints. -/
  constraints : List SlotConstraint := []
  deriving DecidableEq, Repr

/-- A typed form is the form side of a construction, a sequence of slots. -/
abbrev TypedForm (Lex : Type*) := List (Slot Lex)

/-- A slot holds a phrase in a word-level position when its filler is phrasal and its position a
word,
the defining configuration of phrasal compounds and the PAL construction ([goldberg-shirtz-2025])
and the cell that lexical-integrity hypotheses rule out. -/
def Slot.IsPhraseInWordSlot {Lex : Type*} (s : Slot Lex) : Prop :=
  s.filler = .phrasal ∧ s.lex = some true

instance {Lex : Type*} [DecidableEq Lex] (s : Slot Lex) :
    Decidable s.IsPhraseInWordSlot :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Derived specificity -/

section DerivedSpecificity
variable {Lex : Type*}

/-- The derived specificity of a form is `fullyAbstract` when every slot is open (vacuously so
for the empty form), `lexicallySpecified` when none is, and `partiallyOpen` otherwise. -/
def derivedSpecificity (form : TypedForm Lex) : Specificity :=
  if ∀ s ∈ form, s.filler.IsOpen then .fullyAbstract
  else if ∀ s ∈ form, ¬ s.filler.IsOpen then .lexicallySpecified
  else .partiallyOpen

/-- Some slot in the form bears the constraint `c`. -/
def HasConstraint (form : TypedForm Lex) (c : SlotConstraint) : Prop :=
  ∃ s ∈ form, c ∈ s.constraints

instance (form : TypedForm Lex) (c : SlotConstraint) :
    Decidable (HasConstraint form c) :=
  inferInstanceAs (Decidable (∃ s ∈ form, c ∈ s.constraints))

/-- The number of distinct unification indices in a form, on slots and on their subject
requirements. -/
def refGroupCount (form : TypedForm Lex) : Nat :=
  (form.flatMap fun s ↦ s.refIdx.toList ++ s.subjIdx.toList).dedup.length

/-! ### Characterization lemmas -/

theorem derivedSpecificity_eq_fullyAbstract_iff (form : TypedForm Lex) :
    derivedSpecificity form = .fullyAbstract ↔ ∀ s ∈ form, s.filler.IsOpen := by
  unfold derivedSpecificity; split_ifs <;> simp_all

theorem derivedSpecificity_eq_lexicallySpecified_iff (form : TypedForm Lex) :
    derivedSpecificity form = .lexicallySpecified ↔
      form ≠ [] ∧ ∀ s ∈ form, ¬ s.filler.IsOpen := by
  unfold derivedSpecificity
  split_ifs with h₁ h₂
  · simp only [false_iff, not_and]
    intro hne hall
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil form hne
    exact hall s hs (h₁ s hs)
  · exact iff_of_true rfl ⟨by rintro rfl; simp at h₁, h₂⟩
  · simp only [false_iff, not_and]
    exact fun _ ↦ h₂

end DerivedSpecificity

/-! ### Constructions and the network -/

/-- A construction is a learned pairing of form and meaning. The meaning pole is typed by the
domain that owns the construction, such as a composition rule or a presupposition, with `Unit`
for a purely formal record or a defective, form-only construction. -/
structure Construction (Sem : Type*) where
  /-- `form` is the form pole. -/
  form : TypedForm String
  /-- `meaning` is the meaning pole. -/
  meaning : Sem
  /-- `pragmaticPoint` records whether the construction carries a conventional pragmatic point
      ([fillmore-kay-oconnor-1988] §1.1.4). -/
  pragmaticPoint : Bool := false
  deriving DecidableEq, Repr

variable {Sem : Type*}

/-- A construction's specificity is derived from its slot structure. -/
def Construction.specificity (c : Construction Sem) : Specificity :=
  derivedSpecificity c.form

/-- `c.map f` reinterprets the meaning pole of `c` along `f`, keeping the form. -/
def Construction.map {Sem' : Type*} (f : Sem → Sem') (c : Construction Sem) :
    Construction Sem' :=
  { form := c.form, meaning := f c.meaning, pragmaticPoint := c.pragmaticPoint }

/-- A construction is fully compositional when the universal combination schemata alone analyze
it, when its form is fully abstract and it carries no pragmatic point. This is a proxy for
[mueller-2013]'s structural criterion, approximating what [kay-michaelis-2019] survey as a
continuum. -/
def Construction.IsFullyCompositional (c : Construction Sem) : Prop :=
  c.specificity = .fullyAbstract ∧ c.pragmaticPoint = false

instance (c : Construction Sem) : Decidable c.IsFullyCompositional :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A construction is a formal idiom in the sense of [fillmore-kay-oconnor-1988] §1.1.3, a
lexically open idiom, when it is a syntactic pattern rather than a lexically filled expression.
The distinction is a cline (fn. 3), which `Specificity` discretizes. -/
def Construction.IsFormalIdiom (c : Construction Sem) : Prop :=
  c.specificity ≠ .lexicallySpecified

instance (c : Construction Sem) : Decidable c.IsFormalIdiom :=
  inferInstanceAs (Decidable (¬ _))

end ConstructionGrammar
