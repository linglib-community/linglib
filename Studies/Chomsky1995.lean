module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Projection
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.English.Verbs.Basic

/-!
# Chomsky 1995: bare phrase structure and the linear correspondence axiom

In bare phrase structure, minimal and maximal projections are relations of a category to the
structure around it, and any other category, an X′, is invisible. Order is assigned in the
phonological component by Kayne's Linear Correspondence Axiom (LCA): a terminal precedes another
when a category dominating the first asymmetrically c-commands one dominating the second, and the
LCA requires this precedence to order the terminals linearly.

In the bare theory sister terminals are never ordered, so the LCA fails on every syntactic object
unless traces are exempt, and then one of any two sister terminals is a trace. A specifier
precedes its head and the head the inside of a branching complement, and a branching specifier is
ordered consistently only because the X′ does not c-command. The LCA is stated for any tree order
and instantiated on the positions of a linearized syntactic object, where the book's (11), *the man
saw it*, violates it and comes out as *the saw* once *man* and *it* have raised.

## Main definitions

* `PhraseStructure.Precedes`, `PhraseStructure.Linearizes`: Kayne's precedence, and the LCA.
* `PhraseStructure.IsVisible`, `PhraseStructure.bareCCommand`: the minimal and maximal
  projections, and c-command by them, the book's (157).
* `Chomsky1995.HeadDaughterAt`: the head relation on the positions of a linearized object.

## Implementation notes

* Positions individuate occurrences, so the LCA is read on the positions of a linearized object,
  whose order it ignores by `linearizes_bareCCommand_image_iff`.
* Dominance in Kayne's image is reflexive, so that a terminal specifier, the `j` of (154),
  precedes the head.
* Example and note numbers are those of the book's chapter 4.
* Adjunction, the two-segment categories of (156) and (158), is not modelled.

## References

* [chomsky-1995]
* [kayne-1994]
-/

@[expose] public section

open Set
open scoped SetRel

namespace PhraseStructure

/-! ### The linear correspondence axiom -/

section LCA

variable {α : Type*} [PartialOrder α] {R : SetRel α α} {T : Set α} {a b : α}

/-- `a` precedes `b` for `R` when a node dominating `a` asymmetrically `R`-commands a node
dominating `b`. -/
def Precedes (R : SetRel α α) (a b : α) : Prop := a ~[dominanceImage R.asymmetrize] b

theorem precedes_iff : Precedes R a b ↔ ∃ x ≤ a, ∃ y ≤ b, x ~[R] y ∧ ¬ y ~[R] x := by
  rw [Precedes, mem_dominanceImage]
  simp only [SetRel.mem_asymmetrize]

/-- The LCA for `R` holds of the terminals `T` when precedence orders them strictly and
totally. -/
def Linearizes (R : SetRel α α) (T : Set α) : Prop :=
  IsStrictTotalOrder T fun a b ↦ Precedes R a b

theorem linearizes_iff : Linearizes R T ↔
    (∀ a ∈ T, ∀ b ∈ T, a = b ∨ Precedes R a b ∨ Precedes R b a) ∧ (∀ a ∈ T, ¬ Precedes R a a) ∧
      ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, Precedes R a b → Precedes R b c → Precedes R a c := by
  refine ⟨fun h ↦ ⟨fun a ha b hb ↦ ?_, fun a ha ↦ h.irrefl ⟨a, ha⟩,
    fun a ha b hb c hc ↦ h.trans ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  · rcases @trichotomous _ _ h.toTrichotomous ⟨a, ha⟩ ⟨b, hb⟩ with h | h | h
    · exact .inr (.inl h)
    · exact .inl (congrArg Subtype.val h)
    · exact .inr (.inr h)
  · exact { trichotomous := fun a b hab hba ↦ Subtype.ext ((h₁ a a.2 b b.2).resolve_right
                (by tauto))
            irrefl := fun a ↦ h₂ a a.2
            trans := fun a b c ↦ h₃ a a.2 b b.2 c c.2 }

instance [Fintype α] [DecidableLE α] [DecidablePred (· ∈ R)] : DecidableRel (Precedes R) :=
  fun a b ↦ decidable_of_iff' _ (precedes_iff (R := R) (a := a) (b := b))

instance [Fintype α] [DecidableEq α] [DecidableLE α] [DecidablePred (· ∈ R)]
    [DecidablePred (· ∈ T)] : Decidable (Linearizes R T) :=
  haveI : Decidable (∀ a ∈ T, ∀ b ∈ T, a = b ∨ Precedes R a b ∨ Precedes R b a) := inferInstance
  haveI : Decidable (∀ a ∈ T, ¬ Precedes R a a) := inferInstance
  haveI : Decidable (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, Precedes R a b → Precedes R b c →
    Precedes R a c) := inferInstance
  decidable_of_iff' _ linearizes_iff

theorem linearizes_image_iff {β : Type*} [PartialOrder β] (e : α ≃o β) :
    Linearizes (Prod.map e e '' R) (e '' T) ↔ Linearizes R T := by
  have he : ∀ a b, Precedes (Prod.map e e '' R) (e a) (e b) ↔ Precedes R a b := fun a b ↦ by
    rw [Precedes, SetRel.asymmetrize_image_prodMap e.injective, mem_dominanceImage_image]
    rfl
  simp only [linearizes_iff, forall_mem_image, he, e.injective.eq_iff]

end LCA

/-! ### Bare c-command -/

section Bare

variable {α : Type*} [PartialOrder α] (H : α → α → Prop)

/-- A node is visible when it is a minimal or a maximal projection; any other node is an X′. -/
def IsVisible (x : α) : Prop := IsMinimalProjection H x ∨ IsMaximalProjection H x

/-- In bare c-command, the book's (157), a visible node c-commands each node disconnected from it
that every node properly dominating it dominates. -/
def bareCCommand : SetRel α α :=
  {p | IsVisible H p.1 ∧ ¬ p.1 ≤ p.2 ∧ ¬ p.2 ≤ p.1 ∧ p.1 ~[commandRelation univ] p.2}

variable {H} {R : SetRel α α} {T : Set α} {a b h j m p x J K L P : α}

theorem mem_bareCCommand : a ~[bareCCommand H] b ↔
    IsVisible H a ∧ ¬ a ≤ b ∧ ¬ b ≤ a ∧ ∀ x < a, x ≤ b := by
  simp [bareCCommand, mem_commandRelation]

theorem image_bareCCommand {β : Type*} [PartialOrder β] {H' : β → β → Prop} (e : α ≃o β)
    (hH : ∀ a b, H' (e a) (e b) ↔ H a b) : Prod.map e e '' bareCCommand H = bareCCommand H' := by
  have hv : ∀ a, IsVisible H' (e a) ↔ IsVisible H a := fun a ↦ by
    simp only [IsVisible, IsMinimalProjection, IsMaximalProjection, e.surjective.forall, hH]
  ext ⟨x, y⟩
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  rw [show (e a, e b) = Prod.map e e (a, b) from rfl,
    (e.injective.prodMap e.injective).mem_set_image]
  refine mem_bareCCommand.trans (Iff.trans ?_ mem_bareCCommand.symm)
  rw [hv, e.le_iff_le, e.le_iff_le, e.surjective.forall]
  simp only [e.lt_iff_lt, e.le_iff_le]

/-- Bare c-command commutes with order isomorphisms, so the LCA in the bare theory ignores the
order of sisters (note 108). -/
theorem linearizes_bareCCommand_image_iff {β : Type*} [PartialOrder β] {H' : β → β → Prop}
    (e : α ≃o β) (hH : ∀ a b, H' (e a) (e b) ↔ H a b) :
    Linearizes (bareCCommand H') (e '' T) ↔ Linearizes (bareCCommand H) T := by
  rw [← image_bareCCommand e hH, linearizes_image_iff]

theorem isVisible_of_isMax (hH : ∀ m d, H m d → m ⋖ d) (hx : IsMax x) : IsVisible H x :=
  .inl fun d hd ↦ (hH x d hd).lt.not_ge (hx (hH x d hd).le)

variable [IsLeftLinear α]

theorem mem_bareCCommand_of_covBy (ha : m ⋖ a) (hb : m ⋖ b) (hab : a ≠ b)
    (hv : IsVisible H a) : a ~[bareCCommand H] b :=
  ⟨hv, not_le_of_covBy ha hb hab, not_le_of_covBy hb ha hab.symm,
    mem_commandRelation_of_covBy ha hb.le⟩

/-- A node does not precede a visible sister, so two visible sisters are unordered, as the
terminals `m` and `p` of (154). -/
theorem not_precedes_of_covBy (ha : m ⋖ a) (hb : m ⋖ b) (hvb : IsVisible H b) :
    ¬ Precedes (bareCCommand H) a b := by
  refine not_mem_dominanceImage_asymmetrize_of_covBy (fun _ _ h ↦ ⟨h.2.1, h.2.2.1⟩)
    (fun h ↦ ?_) ha hb
  rcases eq_or_ne a b with rfl | hab
  · exact h
  · exact mem_bareCCommand_of_covBy hb ha hab.symm hvb

/-- Under the LCA one of two sister terminals lies outside `T`, so with traces exempt every
right-branching structure ends in a trace. -/
theorem Linearizes.not_mem_or_not_mem_of_covBy (hl : Linearizes (bareCCommand H) T)
    (hH : ∀ m d, H m d → m ⋖ d) (ha : m ⋖ a) (hb : m ⋖ b) (hab : a ≠ b) (hma : IsMax a)
    (hmb : IsMax b) : a ∉ T ∨ b ∉ T := by
  by_contra! hT
  rcases (linearizes_iff.1 hl).1 a hT.1 b hT.2 with h | h | h
  · exact hab h
  · exact not_precedes_of_covBy ha hb (isVisible_of_isMax hH hmb) h
  · exact not_precedes_of_covBy hb ha (isVisible_of_isMax hH hma) h

/-- On a finite tree in which every node with a daughter branches, the LCA fails as soon as
there is a node with a daughter, unless some terminal is exempt. This is why the bare theory
must weaken the LCA. -/
theorem not_linearizes_of_not_isMax [Finite α] (hH : ∀ m d, H m d → m ⋖ d)
    (hb : ∀ x : α, ¬ IsMax x → IsBranching x) (hx : ¬ IsMax x) :
    ¬ Linearizes (bareCCommand H) {a | IsMax a} := fun hl ↦ by
  obtain ⟨m, a, b, ha, hb', hab, hma, hmb⟩ := exists_cherry hb hx
  exact (hl.not_mem_or_not_mem_of_covBy hH ha hb' hab hma hmb).elim (· hma) (· hmb)

/-! #### The configuration (154)

`K` has daughters `J` and `L`, and `L` has daughters `h` and `P`, so that `J` is a specifier,
`h` a head and `P` its complement. -/

/-- Every node a visible specifier dominates precedes the head. -/
theorem precedes_of_spec (hJ : K ⋖ J) (hL : K ⋖ L) (hJL : J ≠ L) (hh : L ⋖ h)
    (hvJ : IsVisible H J) (hj : J ≤ j) : Precedes (bareCCommand H) j h := by
  refine precedes_iff.2 ⟨J, hj, h, le_rfl, mem_bareCCommand.2 ⟨hvJ, fun hJh ↦ ?_, fun hhJ ↦ ?_,
    fun x hx ↦ (IsLeftLinear.le_of_lt_of_covBy hJ hx).trans (hL.le.trans hh.le)⟩, fun hc ↦ ?_⟩
  · exact (IsLeftLinear.comparable_of_le_common hJh hh.le).elim (not_le_of_covBy hJ hL hJL)
      (not_le_of_covBy hL hJ hJL.symm)
  · exact not_le_of_covBy hL hJ hJL.symm (hh.le.trans hhJ)
  · exact not_le_of_covBy hL hJ hJL.symm ((mem_bareCCommand.1 hc).2.2.2 L hh.lt)

/-- A visible head precedes the nodes properly inside its complement but not the complement
itself, so the order specifier-head-complement needs a branching complement. -/
theorem precedes_of_complement (hh : L ⋖ h) (hP : L ⋖ P) (hhP : h ≠ P) (hvh : IsVisible H h)
    (hp : P < p) : Precedes (bareCCommand H) h p := by
  refine precedes_iff.2 ⟨h, le_rfl, p, le_rfl, mem_bareCCommand.2 ⟨hvh, fun hhp ↦ ?_, fun hph ↦ ?_,
    fun x hx ↦ (IsLeftLinear.le_of_lt_of_covBy hh hx).trans (hP.le.trans hp.le)⟩, fun hc ↦ ?_⟩
  · exact (IsLeftLinear.comparable_of_le_common hhp hp.le).elim (not_le_of_covBy hh hP hhP)
      (not_le_of_covBy hP hh hhP.symm)
  · exact not_le_of_covBy hP hh hhP.symm (hp.le.trans hph)
  · exact not_le_of_covBy hP hh hhP.symm ((mem_bareCCommand.1 hc).2.2.2 P hp)

/-- When the X′ is invisible the head precedes nothing in the specifier. -/
theorem not_precedes_of_spec (hJ : K ⋖ J) (hL : K ⋖ L) (hJL : J ≠ L) (hh : L ⋖ h)
    (hvL : ¬ IsVisible H L) (hj : J ≤ j) : ¬ Precedes (bareCCommand H) h j := by
  rintro ⟨⟨x, y⟩, ⟨hxy, -⟩, hxh, hyj⟩
  obtain ⟨hvx, hn₁, hn₂, hc⟩ := mem_bareCCommand.1 hxy
  rcases hxh.eq_or_lt with rfl | hxh
  · exact (IsLeftLinear.comparable_of_le_common (hc L hh.lt |>.trans hyj) hj).elim
      (not_le_of_covBy hL hJ hJL.symm) (not_le_of_covBy hJ hL hJL)
  · rcases (IsLeftLinear.le_of_lt_of_covBy hh hxh).eq_or_lt with rfl | hxL
    · exact hvL hvx
    · exact (IsLeftLinear.comparable_of_le_common
        ((IsLeftLinear.le_of_lt_of_covBy hL hxL).trans (hJ.le.trans hj)) hyj).elim hn₁ hn₂

/-- Under the LCA a specifier with a terminal properly inside it forces the X′ to be invisible,
since a visible X′ would put the head before that terminal as well as after it. -/
theorem Linearizes.not_isVisible (hl : Linearizes (bareCCommand H) T) (hJ : K ⋖ J)
    (hL : K ⋖ L) (hJL : J ≠ L) (hh : L ⋖ h) (hvJ : IsVisible H J) (hα : J < a) (haT : a ∈ T)
    (hhT : h ∈ T) : ¬ IsVisible H L := fun hvL ↦ by
  have hah : Precedes (bareCCommand H) a h := precedes_of_spec hJ hL hJL hh hvJ hα.le
  have hha : Precedes (bareCCommand H) h a := precedes_iff.2 ⟨L, hh.le, a, le_rfl,
    mem_bareCCommand.2 ⟨hvL, fun hLa ↦ ?_, fun haL ↦ ?_,
      fun x hx ↦ (IsLeftLinear.le_of_lt_of_covBy hL hx).trans (hJ.le.trans hα.le)⟩, fun hc ↦ ?_⟩
  · exact (linearizes_iff.1 hl).2.1 a haT ((linearizes_iff.1 hl).2.2 a haT h hhT a haT hah hha)
  · exact (IsLeftLinear.comparable_of_le_common hLa hα.le).elim (not_le_of_covBy hL hJ hJL.symm)
      (not_le_of_covBy hJ hL hJL)
  · exact not_le_of_covBy hJ hL hJL (hα.le.trans haL)
  · exact not_le_of_covBy hJ hL hJL ((mem_bareCCommand.1 hc).2.2.2 J hα)

end Bare

end PhraseStructure

namespace Chomsky1995

open Core.Order RoseTree PhraseStructure Minimalist

/-! ### The positions of a syntactic object -/

variable (t : LinearizedSyntacticObject)

/-- The head relation on the positions of `t`, from the head daughter of each subtree. -/
def HeadDaughterAt (m d : t.val.Positions) : Prop := headDaughterRel (HeadFunction.raising t) m d

instance : DecidableRel (HeadDaughterAt t) := fun m d ↦
  inferInstanceAs (Decidable (headDaughterRel (HeadFunction.raising t) m d))

theorem headDaughterAt_covBy {m d : t.val.Positions} (h : HeadDaughterAt t m d) : m ⋖ d :=
  Positions.covBy_iff.2 (headDaughterRel_covBy _ h)

instance (x : t.val.Positions) : Decidable (IsMinimalProjection (HeadDaughterAt t) x) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (x : t.val.Positions) : Decidable (IsMaximalProjection (HeadDaughterAt t) x) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (x : t.val.Positions) : Decidable (IsVisible (HeadDaughterAt t) x) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance : DecidablePred (· ∈ bareCCommand (HeadDaughterAt t)) := fun _ ↦
  decidable_of_iff' _ mem_bareCCommand

/-- The pronounced terminals of `t`, the positions of its heads; traces are exempt from the
LCA. -/
def pronounced : Set t.val.Positions := {p | t.IsHeadAt p}

instance : DecidablePred (· ∈ pronounced t) := fun p ↦ inferInstanceAs (Decidable (t.IsHeadAt p))

theorem not_linearizes (ht : ¬ IsMax (⊥ : t.val.Positions)) :
    ¬ Linearizes (bareCCommand (HeadDaughterAt t)) {p | IsMax p} :=
  not_linearizes_of_not_isMax (fun _ _ ↦ headDaughterAt_covBy t)
    (fun _ ↦ LinearizedSyntacticObject.isBranching_of_not_isMax) ht

/-! ### *The man saw it*, (11) -/

/-- A nominal argument c-selects a determiner phrase. -/
def positionCat : ArgumentFrame.Position → Option Cat
  | .nominal => some .D
  | _ => none

/-- The selectional stack of a verb's citation frame lists its complements and then its external
argument, the specifier of the verb in (11). -/
def selStack (v : English.Verbs.Verb) : SelStack :=
  (v.valency.frames.head?.map fun fr ↦
    (fr.complements ++ fr.external.toList).filterMap positionCat).getD []

/-- *The*, a determiner selecting a noun, as in (8b). -/
def the : LexicalItem.Token := ⟨.of .D [.N] English.Determiners.the.form, 0⟩

/-- *Man*. -/
def man : LexicalItem.Token := ⟨.of .N [] English.Nouns.man.form, 0⟩

/-- *Saw*, the past of *see*. -/
def saw : LexicalItem.Token :=
  ⟨.of .V (selStack English.Verbs.see) (English.Verbs.see.realize .past), 0⟩

/-- *It*, a determiner without a complement. -/
def it : LexicalItem.Token := ⟨.of .D [] English.Pronouns.it.form, 0⟩

/-- *The man saw it*, (11). -/
def theManSawIt : LinearizedSyntacticObject := {{↑the, ↑man}, {↑saw, ↑it}}

/-- (11) with *man* and *it* raised, leaving their traces. -/
def theManSawItRaised : LinearizedSyntacticObject :=
  {{↑the, .traceOf man}, {↑saw, .traceOf it}}

/-- The position at an address. -/
def position (l : List ℕ) (h : (⟨l⟩ : TreePath) ∈ t.val.validPaths := by exact rfl) :
    t.val.Positions :=
  ⟨⟨l⟩, h⟩

-- (11)
theorem maximalProjectionAt_theManSawIt :
    maximalProjectionAt (HeadFunction.raising theManSawIt) ⟨[1, 0]⟩ = ⊥ ∧
      maximalProjectionAt (HeadFunction.raising theManSawIt) ⟨[0, 0]⟩ = ⟨[0]⟩ := by
  decide

-- (11), (10)
theorem card_positions_theManSawIt : Fintype.card theManSawIt.val.Positions = 7 := by decide

-- (9)
theorem levels_theManSawIt :
    (IsMinimalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [1, 1]) ∧
        IsMaximalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [1, 1])) ∧
      (IsMinimalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [0, 1]) ∧
        IsMaximalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [0, 1])) ∧
      (IsMinimalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [1, 0]) ∧
        ¬ IsMaximalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [1, 0])) ∧
      (IsMinimalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [0, 0]) ∧
        ¬ IsMaximalProjection (HeadDaughterAt theManSawIt) (position theManSawIt [0, 0])) ∧
      ¬ IsVisible (HeadDaughterAt theManSawIt) (position theManSawIt [1]) := by
  decide

/-- (11) violates the LCA even with traces exempt, since *the* and *man* are unordered, and so
are *saw* and *it*. -/
theorem not_linearizes_theManSawIt :
    ¬ Linearizes (bareCCommand (HeadDaughterAt theManSawIt)) (pronounced theManSawIt) := by
  decide

/-- With *man* and *it* raised the LCA holds, and the string is *the saw*. -/
theorem linearizes_theManSawItRaised :
    Linearizes (bareCCommand (HeadDaughterAt theManSawItRaised)) (pronounced theManSawItRaised) ∧
      (∀ p, p ∈ pronounced theManSawItRaised ↔
        p = position theManSawItRaised [0, 0] ∨ p = position theManSawItRaised [1, 0]) ∧
      Precedes (bareCCommand (HeadDaughterAt theManSawItRaised))
        (position theManSawItRaised [0, 0]) (position theManSawItRaised [1, 0]) := by
  decide

end Chomsky1995
