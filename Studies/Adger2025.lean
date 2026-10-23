module

public import Linglib.Syntax.Mereological.Derivation
public import Linglib.Data.Examples.Adger2025

/-!
# Adger (2025): Mereological Syntax: Phrase Structure, Cyclicity, and Islands

Adger replaces set-theoretic Merge by Subjoin, which makes one syntactic object a proper part
of another in one of two dimensions: the first subjunction to an object yields its 1-part, the
extended-projection complement, the second its 2-part, the specifier (`Parthood`). Parthood is
transitive within a dimension only, and Angular Locality lets a part subjoin to a target only
through a single angle: it must be an n-part of some 1-part of the target (`CanSubjoin`). A
derivation is a sequence of subjunctions licensed by Dimensionality, Angular Locality and
Mereological Extension (`Derives`).

The book's list of consequences is verified on its own structures. The complement of a head
cannot resubjoin to it (`antilocality`), and subjunction to an unattached object, to a specifier,
or downward fails because the target must contain the mover, in lowering and sideward
configurations in every derivation (`parallel_blocked`, `sideward_blocked`, `lowering_blocked`).
A 2-part of a 2-part of an object in the target's extended projection subjoins, while a 1-part of
that 2-part does not (`angle_turns_once`), so that a subjunction blocked from inside a specifier
becomes possible once the mover has subjoined to that specifier (`escape_hatch`): of the objects
inside a specifier, exactly its own 2-parts reach above it (`edge`). This is successive
cyclicity without phases: *who* reaches the matrix C of *guess who you said fell* only after
subjoining to the embedded C, and in every derivation it leaves the embedded clause only from its
edge (`said_fell`, `said_successive_cyclic`).

Islands follow from the same mechanism with Dimensionality: a 2-part whose own 2-part slot is
filled is an island in every derivation. In *what you asked who bought*, the embedded C has *who*
as its 2-part, and *what* never reaches the matrix C (`wh_island`). Extraction from a nominal runs
through D, so it needs D's 2-part: an indefinite leaves it free and *who did you buy a statue of*
derives (`statue_indefinite`), while a definite fills it with Det and the wh-expression is
trapped (`statue_definite`). Subjects are not islands as such: under T[uD] the wh-expression
subjoins to D and on to C (`subject_thetic`). T[uFam] is checked by a [Fam]-bearing 2-part of T,
which in English only a Det, Dem or possessor in D's 2-part supplies, so a topic subject traps
the wh-expression, and once the wh-expression holds D's 2-part the subject can never be a topic
(`subject_topic`, `thetic_not_topic`). These predictions match the judgments of the book's rows
on extraction from clauses, nominals and subjects (`clause_rows`, `nominal_rows`). Wh-island
violations, the WIRE effect, adjunct islands, *-linearization, and the cross-linguistic feature
settings of chapters 5–7 are not formalized.

## Implementation notes

* Each structure is the book's tree cut down to the objects its claim needs: the movement of the
  subject to T in (44) and (3), and the article inside the relational nominal of (32), are left
  out, and a filler of D is a single object. Every object with a 2-part keeps its 1-part, as
  Dimensionality requires.
* A row's structure is read off its own columns: the type of nominal fixes the 2-part of D, by
  D-Interpretation for definites and by the subjunction of Dem or the possessor, and pied-piping
  makes P the mover. The wh-in-situ rows of (41)–(44) are read as covert subjunction to C, and the
  echo-only reading of (42b) is set aside.
* The prediction of a row is `Reaches`: some licensed derivation makes the mover a part of C.

## References

* [adger-2025]
-/

@[expose] public section

namespace Adger2025

open MereologicalSyntax MereologicalSyntax.Parthood

/-! ### Consequences of Angular Locality -/

/-- The objects of the schematic structures. -/
inductive Obj
  | a | b | c | d | e | f | g | u | w | x | y | z
  deriving DecidableEq, Fintype, Repr

/-- `a` with `b` as its 1-part, (28). -/
def superlocal : Parthood Obj where
  onePart | .a => some .b | _ => none
  twoPart _ := none

theorem antilocality : ¬ superlocal.CanSubjoin .b .a :=
  not_canSubjoin_of_imm_one (by decide) rfl

/-- Two roots, (30), `d` with 1-part `e` and `b` with 2-part `a` and 1-part `c`. -/
def parallel : Parthood Obj where
  onePart | .d => some .e | .b => some .c | _ => none
  twoPart | .b => some .a | _ => none

theorem parallel_blocked : ¬ parallel.CanSubjoin .a .d := by decide +kernel

/-- `c` with 2-part `b` and 1-part `a`, (31a). -/
def sideward : Parthood Obj where
  onePart | .c => some .a | _ => none
  twoPart | .c => some .b | _ => none

theorem sideward_blocked {Q : Parthood Obj} (h : sideward.Derives Q) :
    ¬ Q.CanSubjoin .a .b ∧ ¬ Q.CanSubjoin .b .a :=
  ⟨h.not_canSubjoin_of_not_descendant (by decide +kernel) (by decide +kernel),
    h.not_canSubjoin_of_not_descendant (by decide +kernel) (by decide +kernel)⟩

/-- `e` with 2-part `a` and 1-part `f`; `a` with 2-part `d` and 1-part `b`, whose 1-part chain
continues `c`, `g`, (32). -/
def lowering : Parthood Obj where
  onePart | .e => some .f | .a => some .b | .b => some .c | .c => some .g | _ => none
  twoPart | .e => some .a | .a => some .d | _ => none

theorem lowering_blocked {Q : Parthood Obj} (h : lowering.Derives Q) :
    ¬ Q.CanSubjoin .d .c :=
  h.not_canSubjoin_of_not_descendant (by decide +kernel) (by decide +kernel)

/-- `y` with 1-part `e`; `e` with 2-part `u` and 1-part `w`; `u` with 2-part `z` and 1-part `x`,
(38). -/
def angle : Parthood Obj where
  onePart | .y => some .e | .e => some .w | .u => some .x | _ => none
  twoPart | .e => some .u | .u => some .z | _ => none

theorem angle_turns_once : angle.CanSubjoin .z .y ∧ ¬ angle.CanSubjoin .x .y := by
  decide +kernel

/-- As `angle`, but `u` has only the 1-part `x`, whose 2-part is `z` and whose 1-part is `g`,
(41a). -/
def escape : Parthood Obj where
  onePart | .y => some .e | .e => some .w | .u => some .x | .x => some .g | _ => none
  twoPart | .e => some .u | .x => some .z | _ => none

/-- `escape` after `z` subjoins to `u`, (41b). -/
def escape' : Parthood Obj := escape.addPart .two .z .u

/-- `z` cannot subjoin to `y` from inside `u`, but subjoining to `u` is licensed, and then it can,
(41). -/
theorem escape_hatch :
    ¬ escape.CanSubjoin .z .y ∧ escape.Subjoins .z .u escape' ∧ escape'.CanSubjoin .z .y := by
  decide +kernel

/-- Of the objects inside `u`, the 2-part of `e`, exactly the 2-parts of `u` reach `y`. -/
theorem edge {γ : Obj} (hγ : γ ∈ ({.x, .z, .g} : Set Obj)) :
    escape'.CanSubjoin γ .y ↔ escape'.NPart .two γ .u :=
  IsDomain.canSubjoin_iff_nPart_two (S := {Obj.u, .x, .z, .g}) (d := .e) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (Set.mem_insert_of_mem _ hγ)
    (by rintro rfl; simp at hγ) (by decide +kernel)

/-! ### Clausal derivations and wh-islands -/

/-- The categories of the clausal and nominal structures; primes mark the embedded clause and the
wh-phrase inside a nominal. -/
inductive Node
  | C | T | v | O | V | Appl | C' | T' | v' | O' | V' | who | what | you | D | D' | Det | Dem
  | Poss | rel | rel' | P | N | N'
  deriving DecidableEq, Fintype, Repr

/-- In *We asked who Anson wrote the book*, (34), `who` is the 2-part of `Appl`, whose 1-part
`O` has the embedded `C` as its 2-part. -/
def asked : Parthood Node where
  onePart | .Appl => some .O | .O => some .V | .C => some .T | _ => none
  twoPart | .Appl => some .who | .O => some .C | _ => none

/-- In *Guess who you said fell*, (44) and (2) of chapter 5, the clausal complement is the 2-part
of `O`, and `who` the 2-part of the embedded `O'`. -/
def said : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O | .O => some .V
    | .C' => some .T' | .T' => some .v' | .v' => some .O' | .O' => some .V' | _ => none
  twoPart | .v => some .you | .O => some .C' | .O' => some .who | _ => none

/-- `said` after `who` subjoins to the embedded `C'`. -/
def said' : Parthood Node := said.addPart .two .who .C'

theorem said_fell :
    ¬ said.CanSubjoin .who .C ∧ said.Subjoins .who .C' said' ∧
      said'.Subjoins .who .C (said'.addPart .two .who .C) := by
  decide +kernel

/-- The embedded clause of (44). -/
abbrev embedded : Set Node := {.C', .T', .v', .O', .V', .who}

theorem said_successive_cyclic {Q : Parthood Node} (h : said.Derives Q) {β : Node} {n : Dim}
    (hβ : β ∉ embedded) (hwho : Q.Imm n .who β) : Q.NPart .two .who .C' :=
  (IsDomain.eq_or_nPart_two_of_derives (by decide +kernel) h (by decide +kernel) hβ
    hwho).resolve_left (by decide)

/-- In *(guess) what you asked who bought*, (3) of chapter 5, the embedded clause is the 2-part of
`O`; `who` has subjoined to `T'` and `C'` from `v'`, and `what` is the 2-part of `O'`. -/
def askedWhoBought : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O | .O => some .V
    | .C' => some .T' | .T' => some .v' | .v' => some .O' | .O' => some .V' | _ => none
  twoPart
    | .v => some .you | .O => some .C' | .C' => some .who | .T' => some .who
    | .v' => some .who | .O' => some .what | _ => none

/-- In the wh-island (1b) of chapter 5, `who` fills the 2-part of the embedded `C'`, and no
derivation makes `what` a part of the matrix `C`. -/
theorem wh_island : ¬ askedWhoBought.Reaches .what .C :=
  IsDomain.not_reaches (S := {Node.C', .T', .v', .O', .V', .what}) (b := .C') (c := .who)
    (by decide +kernel) rfl (by decide) (by decide) (by decide) (by decide +kernel) (by decide)

/-! ### Nominal islands -/

/-- In *Who did you buy a statue of*, (32), the object `D` is the 2-part of `O`; its 1-part is the
relational `rel`, with 2-part `P` and 1-part `N`. The 1-part of `P` is the wh-phrase `D'`, whose
relational `rel'` has `who` as its 2-part, and `who` has subjoined to `P`. -/
def statue : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O | .O => some .V | .D => some .rel
    | .rel => some .N | .P => some .D' | .D' => some .rel' | .rel' => some .N' | _ => none
  twoPart
    | .v => some .you | .O => some .D | .rel => some .P | .P => some .who | .rel' => some .who
    | _ => none

/-- *Who did you buy the statue of*, (33): `Det` has subjoined to `D`. -/
def theStatue : Parthood Node := statue.addPart .two .Det .D

theorem statue_indefinite :
    ¬ statue.CanSubjoin .who .C ∧ statue.Subjoins .who .D (statue.addPart .two .who .D) ∧
      (statue.addPart .two .who .D).Subjoins .who .C
        ((statue.addPart .two .who .D).addPart .two .who .C) := by
  decide +kernel

/-- The objects inside `D` of the statue nominal. -/
abbrev nominal : Set Node := {.D, .rel, .N, .P, .D', .rel', .N', .who}

theorem statue_definite :
    theStatue.CanSubjoin .who .D ∧ theStatue.subjoin .who .D = none ∧
      ¬ theStatue.Reaches .who .C :=
  ⟨by decide +kernel, subjoin_eq_none_of_full rfl rfl,
    IsDomain.not_reaches (S := nominal) (b := .D) (c := .Det) (by decide +kernel) rfl
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)⟩

/-! ### Subject islands -/

/-- A subject `D` in the 2-part of `v`, subjoined to `T`. Its 1-part `rel` has 2-part `Det` and
1-part `rel'`, whose 2-part is `who`, (56)–(57). -/
def subject : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .V | .D => some .rel | .rel => some .rel'
    | .rel' => some .N | _ => none
  twoPart
    | .T => some .D | .v => some .D | .rel => some .Det | .rel' => some .who | _ => none

/-- `subject` after `who` subjoins to `D`, under `T[uD]`, (57). -/
def thetic : Parthood Node := subject.addPart .two .who .D

/-- `subject` after `Det[uD, Fam]` subjoins to `D`, (56). -/
def topic : Parthood Node := subject.addPart .two .Det .D

/-- The categories that bear [Fam] in English: Det[uD, Fam], Dem and the possessor, but not D. -/
def Fam (x : Node) : Prop := x = .Det ∨ x = .Dem ∨ x = .Poss

instance : DecidablePred Fam := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- `T[uFam]` is checked when, by Transitivity, a [Fam]-bearer is a 2-part of `T`. -/
def FamChecked (P : Parthood Node) : Prop := ∃ y, P.NPart .two y .T ∧ Fam y

instance (P : Parthood Node) : Decidable (FamChecked P) :=
  inferInstanceAs (Decidable (∃ _, _))

theorem subject_thetic :
    subject.Subjoins .who .D thetic ∧ thetic.Subjoins .who .C (thetic.addPart .two .who .C) := by
  decide +kernel

theorem subject_topic :
    ¬ FamChecked subject ∧ subject.Subjoins .Det .D topic ∧ FamChecked topic ∧
      ¬ topic.Reaches .who .C :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    IsDomain.not_reaches (P := topic) (S := {Node.D, .rel, .rel', .N, .who}) (b := .D) (c := .Det)
      (by decide +kernel) rfl (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide)⟩

theorem thetic_not_topic {Q : Parthood Node} (h : thetic.Derives Q) : ¬ FamChecked Q := by
  have leaf : ∀ y, ¬ thetic.Descendant y .who := by decide +kernel
  rintro ⟨y, hyT, hy⟩
  rcases hyT.eq_or_nPart_of_imm (h.le (show thetic.Imm .two .D .T from rfl)) with rfl | hyD
  · simp [Fam] at hy
  rcases hyD.eq_or_nPart_of_imm (h.le (show thetic.Imm .two .who .D from rfl)) with rfl | hyw
  · simp [Fam] at hy
  exact leaf y (h.descendant_of_isPart (by decide +kernel) (descendant_of_nPart hyw))

/-! ### Well-formedness -/

theorem wellFormed :
    (∀ P ∈ [superlocal, parallel, sideward, lowering, angle, escape, escape'],
      P.Acyclic ∧ P.Dimensional) ∧
    ∀ P ∈ [asked, said, said', askedWhoBought, statue, theStatue, subject, thetic, topic],
      P.Acyclic ∧ P.Dimensional := by
  decide +kernel

/-! ### The data -/

theorem reaches_of_cycle {P : Parthood Node} {γ : Node}
    (h₁ : P.Subjoins γ .D (P.addPart .two γ .D))
    (h₂ : (P.addPart .two γ .D).Subjoins γ .C ((P.addPart .two γ .D).addPart .two γ .C)) :
    P.Reaches γ .C :=
  Reaches.of_derives h₁.derives h₂.reaches

/-- Extraction from a clausal complement, (43), is acceptable and derived; downward subjunction,
(33), and extraction from a wh-island, (1b) of chapter 5, are not. -/
theorem clause_rows :
    (asked.Reaches .who .C ↔ Examples.ch433.judgment = .acceptable) ∧
      (said.Reaches .who .C ↔ Examples.ch443.judgment = .acceptable) ∧
      (askedWhoBought.Reaches .what .C ↔ Examples.ch51b.judgment = .acceptable) := by
  refine ⟨iff_of_false (fun ⟨_, h, _, hn⟩ ↦
      h.not_imm_of_not_descendant (by decide +kernel) (by decide +kernel) hn) (by decide),
    iff_of_true ?_ rfl, iff_of_false wh_island (by decide)⟩
  obtain ⟨-, h₁, h₂⟩ := said_fell
  exact Reaches.of_derives h₁.derives h₂.reaches

/-- The structure of a row on extraction from a nominal or a subject: D's 2-part is free, or
filled as the type of nominal requires. -/
def structureOf (e : Datum) : Option (Parthood Node) :=
  (e.parse? "subject" [("indefinite or weak definite", subject)]).orElse fun _ ↦
    e.parse? "nominal"
      [("indefinite", statue), ("postnominal possessive", statue), ("indefinite relative", statue),
        ("definite", theStatue), ("demonstrative", statue.addPart .two .Dem .D),
        ("demonstrative relative", statue.addPart .two .Dem .D),
        ("prenominal possessor", statue.addPart .two .Poss .D)]

/-- The mover of a row is `P` under pied-piping and `who` otherwise. -/
def moverOf (e : Datum) : Node := if (e.feature? "pied-piping").isSome then .P else .who

/-- The structures and movers of the rows. -/
def cases : List (Parthood Node × Node) :=
  [(subject, .who), (statue, .who), (statue, .P), (theStatue, .who), (theStatue, .P),
    (statue.addPart .two .Dem .D, .who), (statue.addPart .two .Dem .D, .P),
    (statue.addPart .two .Poss .D, .who), (statue.addPart .two .Poss .D, .P)]

private theorem mem_cases : ∀ e ∈ Examples.all, ∀ P ∈ structureOf e, (P, moverOf e) ∈ cases := by
  decide +kernel

private theorem reaches_iff : ∀ p ∈ cases, p.1.Reaches p.2 .C ↔ p.1.twoPart .D = none := by
  have trapped (f γ : Node) (hf : f = .Det ∨ f = .Dem ∨ f = .Poss) (hγ : γ = .who ∨ γ = .P) :
      ¬ (statue.addPart .two f .D).Reaches γ .C := by
    rcases hγ with rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
      exact IsDomain.not_reaches (S := nominal) (b := .D) (by decide +kernel) rfl (by decide)
        (by decide) (by decide) (by decide +kernel) (by decide)
  simp only [cases, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨iff_of_true (reaches_of_cycle (by decide +kernel) (by decide +kernel)) rfl,
    iff_of_true (reaches_of_cycle (by decide +kernel) (by decide +kernel)) rfl,
    iff_of_true (reaches_of_cycle (by decide +kernel) (by decide +kernel)) rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact iff_of_false (trapped _ _ (by decide) (by decide)) (by decide)

/-- The rows on extraction from nominals and subjects, (31)–(44) of chapter 6 and (59) of
chapter 7: the mover reaches `C` exactly in the acceptable ones. -/
theorem nominal_rows :
    ∀ e ∈ Examples.all, ∀ P ∈ structureOf e, e.feature? "wh" ≠ some "in situ, echo question only" →
      (P.Reaches (moverOf e) .C ↔ e.judgment = .acceptable) := by
  have h : ∀ e ∈ Examples.all, ∀ P ∈ structureOf e,
      e.feature? "wh" ≠ some "in situ, echo question only" →
        (P.twoPart .D = none ↔ e.judgment = .acceptable) := by
    decide +kernel
  intro e he P hP hecho
  rw [reaches_iff _ (mem_cases e he P hP)]
  exact h e he P hP hecho

end Adger2025
