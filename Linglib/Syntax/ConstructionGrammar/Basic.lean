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

A construction is a learned pairing of a form with a meaning, the unit of grammatical knowledge in
construction grammar. We define the form pole as a `TypedForm`, a list of `Slot`s. The filler of a
slot fixes a lexeme, admits the words of a category, admits the expressions meeting a semantic
constraint, or admits any phrase, and a slot may also carry a grammatical function, a lexicality
value and syntactic constraints. A `Construction Sem` pairs a typed form with a meaning of type
`Sem`.

A filler is open when no lexeme anchors it. The `Specificity` of a form is `fullyAbstract` when
every slot is open, `lexicallySpecified` when the form is nonempty and no slot is open, and
`partiallyOpen` otherwise; specificities are linearly ordered by abstraction.

For valence, a slot whose filler a construct gives a value determines a `Requirement`, and
`Coinstantiates` says of a valence set that the unrealized subject of each complement is the
intrinsic value of another member.

## Implementation notes

A form is a flat list of slots. Which values the slots of a construct share is not part of the
form; it is stated of valence sets, by `Coinstantiates`. The semantic constraint of a slot is a
label, compared only for equality.

## References

* [goldberg-1995]
* [goldberg-2003]
* [goldberg-2006]
* [fillmore-kay-oconnor-1988]
* [kay-fillmore-1999]
* [dunn-2025]
* [goldberg-shirtz-2025]
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
  deriving DecidableEq, Fintype, Repr

/-- Specificities are ordered by abstraction, the lexically specified forms lowest. -/
instance : LinearOrder Specificity := LinearOrder.lift' Specificity.ctorIdx (by decide)

/-! ### Typed slots

Slot content follows [dunn-2025]'s three representation levels, a fixed lexeme (LEX), a word of
a category (SYN) and a semantic constraint (SEM), with the categories the parts of speech of
Universal Dependencies where Dunn's are learned, plus [kay-fillmore-1999]'s headed phrases,
grammatical functions and slot constraints. -/

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

/-- A filler is open when no lexeme anchors it, when its level is not the lexical one. A headed
phrase is not open, since its head lexeme is fixed. -/
def SlotFiller.IsOpen {Lex : Type*} (f : SlotFiller Lex) : Prop :=
  f.level ≠ .lex

instance {Lex : Type*} : DecidablePred (SlotFiller.IsOpen (Lex := Lex)) :=
  fun f ↦ inferInstanceAs (Decidable (f.level ≠ .lex))

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
stored, since a head is nonmaximal and every other daughter maximal. Which values the slots share
is not part of the form: it is a property of a construct, which coinstantiation constrains
(`Coinstantiates`). -/
structure Slot (Lex : Type*) where
  /-- `filler` is what fills the slot. -/
  filler : SlotFiller Lex
  /-- `isHead` records whether the slot is the head of the construction. -/
  isHead : Bool := false
  /-- `lex` says whether the position is a word, `some true` for a word-level slot. -/
  lex : Option Bool := none
  /-- `gf` is the slot's grammatical function ([kay-fillmore-1999]). -/
  gf : Option GrammaticalFunction := none
  /-- `constraints` lists the slot's syntactic constraints. -/
  constraints : List SlotConstraint := []
  deriving DecidableEq, Repr

/-- A typed form is the form side of a construction, a sequence of slots. -/
abbrev TypedForm (Lex : Type*) := List (Slot Lex)

/-- A slot holds a phrase in a word-level position when its filler is phrasal and its position a
word, the configuration of phrasal compounds and of the PAL construction
([goldberg-shirtz-2025]). -/
def Slot.IsPhraseInWordSlot {Lex : Type*} (s : Slot Lex) : Prop :=
  s.filler = .phrasal ∧ s.lex = some true

instance {Lex : Type*} [DecidableEq Lex] (s : Slot Lex) :
    Decidable s.IsPhraseInWordSlot :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Specificity -/

section Specificity
variable {Lex : Type*} {form : TypedForm Lex}

/-- The specificity of a form is `fullyAbstract` when every slot is open (vacuously so for the
empty form), `lexicallySpecified` when none is, and `partiallyOpen` otherwise. -/
def TypedForm.specificity (form : TypedForm Lex) : Specificity :=
  if ∀ s ∈ form, s.filler.IsOpen then .fullyAbstract
  else if ∀ s ∈ form, ¬ s.filler.IsOpen then .lexicallySpecified
  else .partiallyOpen

theorem TypedForm.specificity_eq_fullyAbstract_iff :
    form.specificity = .fullyAbstract ↔ ∀ s ∈ form, s.filler.IsOpen := by
  unfold TypedForm.specificity; split_ifs <;> simp_all

theorem TypedForm.specificity_eq_lexicallySpecified_iff :
    form.specificity = .lexicallySpecified ↔ form ≠ [] ∧ ∀ s ∈ form, ¬ s.filler.IsOpen := by
  unfold TypedForm.specificity
  split_ifs with h₁ h₂
  · simp only [false_iff, not_and]
    intro hne hall
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil form hne
    exact hall s hs (h₁ s hs)
  · exact iff_of_true rfl ⟨by rintro rfl; simp at h₁, h₂⟩
  · simp only [false_iff, not_and]
    exact fun _ ↦ h₂

theorem TypedForm.specificity_eq_partiallyOpen_iff :
    form.specificity = .partiallyOpen ↔
      (∃ s ∈ form, s.filler.IsOpen) ∧ ∃ s ∈ form, ¬ s.filler.IsOpen := by
  unfold TypedForm.specificity; split_ifs <;> simp_all

end Specificity

/-! ### Valence and coinstantiation -/

section Coinstantiation

variable {E : Type*}

/-- A valence requirement as unification sees it ([kay-fillmore-1999]): its grammatical function,
its intrinsic value, `none` for the semantics `[ref ∅]`, and the value of its own subject
requirement when it is a predicate phrase that does not realize its subject. -/
structure Requirement (E : Type*) where
  /-- `gf` is the requirement's grammatical function. -/
  gf : Option GrammaticalFunction
  /-- `intrinsic` is the requirement's intrinsic value, `none` for `[ref ∅]`. -/
  intrinsic : Option E
  /-- `subj` is the value of the requirement's unrealized subject requirement. -/
  subj : Option E
  deriving DecidableEq

/-- The requirement of a slot whose filler a construct gives the value `v`, and whose unrealized
subject requirement it gives `sv`. A slot marked `[ref ∅]` binds the reference of nothing, so it
has no intrinsic value whatever the construct gives it. -/
def Slot.requirement {Lex : Type*} (s : Slot Lex) (v : E) (sv : Option E) : Requirement E :=
  ⟨s.gf, if .refEmpty ∈ s.constraints then none else some v, sv⟩

/-- Coinstantiation ([kay-fillmore-1999], Figure 13) satisfies the subject requirement of each
complement in a predicator's valence set by unifying it with the intrinsic value of another member
of the set: the subject in raising and subject control, the object in object control. The list
stands for a set, so another member is one distinct from the complement. -/
def Coinstantiates (val : List (Requirement E)) : Prop :=
  ∀ k ∈ val, k.gf = some .comp → ∀ v ∈ k.subj, ∃ c ∈ val, c ≠ k ∧ c.intrinsic = some v

instance [DecidableEq E] (val : List (Requirement E)) : Decidable (Coinstantiates val) := by
  unfold Coinstantiates; infer_instance

/-- In a valence set of a subject and one complement, coinstantiation makes the complement's
subject the subject's value, as in raising and subject control. -/
theorem coinstantiates_subj_comp_iff {x e s : E} :
    Coinstantiates [⟨some .subj, some x, none⟩, ⟨some .comp, some e, some s⟩] ↔ s = x := by
  simp [Coinstantiates, eq_comm]

end Coinstantiation

/-! ### Constructions -/

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

/-- The specificity of a construction is that of its form. -/
def Construction.specificity (c : Construction Sem) : Specificity :=
  c.form.specificity

/-- `c.map f` reinterprets the meaning pole of `c` along `f`, keeping the form. -/
@[simps]
def Construction.map {Sem' : Type*} (f : Sem → Sem') (c : Construction Sem) :
    Construction Sem' :=
  { form := c.form, meaning := f c.meaning, pragmaticPoint := c.pragmaticPoint }

@[simp]
theorem Construction.map_id (c : Construction Sem) : c.map id = c := rfl

@[simp]
theorem Construction.map_map {Sem' Sem'' : Type*} (g : Sem' → Sem'') (f : Sem → Sem')
    (c : Construction Sem) : (c.map f).map g = c.map (g ∘ f) := rfl

@[simp]
theorem Construction.specificity_map {Sem' : Type*} (f : Sem → Sem') (c : Construction Sem) :
    (c.map f).specificity = c.specificity := rfl

/-- A construction is a formal idiom in the sense of [fillmore-kay-oconnor-1988] §1.1.3, a
lexically open idiom, when its form is not lexically specified. The distinction is a cline
(fn. 3), which `Specificity` discretizes. -/
def Construction.IsFormalIdiom (c : Construction Sem) : Prop :=
  c.specificity ≠ .lexicallySpecified

instance (c : Construction Sem) : Decidable c.IsFormalIdiom :=
  inferInstanceAs (Decidable (¬ _))

end ConstructionGrammar
