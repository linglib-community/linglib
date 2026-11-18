module

public import Linglib.Data.Examples.Helmantel2002
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Dutch.Adpositions
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Tree.Projection
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.LinearAlgebra.Ray
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Helmantel 2002: interactions in the Dutch adpositional domain

Helmantel sorts the Dutch adpositions by whether their denotation specifies a path, and locates
directionality in a functional projection above the adposition. The postpositional order is the
prepositional one with the object raised to the specifier of that projection, and its distribution
is read off that specifier: [the object must be readable as a path there](##licensed_postPP_iff),
which excludes bare mass nouns, R-words and small objects together with the point locatives; [only
a specifier leaves the phrase](##escapes_tree_iff); and [a phrase whose specifier is occupied cannot
extrapose](##extraposable_tree_iff). Place vectors make the prepositions regions of an inner product
space, where [closure under lengthening](##closedUnderLengthening_carrier_iff) coincides with the
absence of a vector length restriction, while [that restriction](##restriction_does_not_separate)
does not separate a rejected preposition from an accepted postposition.

## Implementation notes

* The classes are the lists of Appendix I.1 restricted to the fragment's entries, which follow a
  later grammar. The appendix also calls *na* 'after' narrow locative, which the fragment records
  as temporal, and *af* 'off' point locative, on a seldom used prepositional use the fragment
  lacks; the productive postposition *af* is treated through the phrase in its specifier, (35)-(36)
  of chapter 6. The appendix's postposition *onder* is regional and the fragment omits it.
* The directionality phrase is category `Path`, which the thesis identifies with PathP. A tree's
  linear order is its daughters' order, so the postpositional order is [the frontier of the raised
  object](##yield_postPP) and needs no linearization parameter.
* Only the first class of postpositional phrases of chapter 3 is modelled. In *het raam uit* the
  object is a border point rather than a path, and the thesis places it outside the specifier
  without saying where, so `postPP` does not cover it. The specific R-words that stay to the right
  of *van*, *tot* and *naar*, (18) of chapter 6, are not modelled either.
* The thesis does not say why point locatives lack the postpositional order, and sets them aside
  when it discusses that order (chapter 3, footnote 14). The reason derived here combines two of
  its statements: a point locative's location has dimension 0 (p. 11), and the specifier imposes
  dimension 1. The structure of (37c) of chapter 6, an R-word in that specifier, is the tree of
  (48a).
* `Escapes` follows specifiers only, the consequence the thesis draws from the Head Constraint and
  (25), (30) of chapter 6, and does not test whether a head is phonologically specified, as every
  head at issue is.
* Extraposition is modelled for adjuncts; a predicative phrase cannot extrapose for a different
  reason, lowering. The extraposed adjunct *het hele jaar door*, (15a) of chapter 5, needs comma
  intonation, which the thesis sets outside the account, so it has no row.
* `IsLengthening` is this file's, since the thesis states only the closure condition (footnote 5 of
  chapter 4): `SameRay` with a norm comparison. Every vector lengthens the zero vector, which has
  no direction, as (8b) needs, since a definition by scalar multiples would leave `{0}` closed.
* `Modifiable` reads the modifier as `‖v‖`, as (14) does; (16) reads the projection on the axis,
  and the witness `d • a` has both values `d`.
* `pathLengths` measures the part of the path inside the object, which is what (22) draws and what
  a modifier measures in (27), and is positive since (21b) says `|v_Δl| ≠ 0`.

## References

* [helmantel-2002]
* [van-riemsdijk-1978]
* [kayne-1994]
* [barbiers-1995]
* [zwarts-1997]
-/

@[expose] public section

namespace Helmantel2002

open Dutch.Adpositions
open PhraseStructure (Tree)
open PhraseStructure.Tree (node terminal trace cat headIndex? yield terminals Label)
open Minimalist (Cat)

/-! ### The classification of the adpositions -/

/-- The three-way distinction of (21) of chapter 1: an adposition has no path specification, or
it has one and its location has dimension 0, or it has one and its location has extension. -/
inductive LocativeClass where
  | narrow
  | point
  | extended
  deriving DecidableEq, Repr

/-- What a phrase can denote. -/
inductive Reading where
  | location
  | path
  deriving DecidableEq, Repr, Fintype

/-- A narrow locative denotes a location, a point locative a path and no location, and an extended
locative either an extended location or a path. -/
def LocativeClass.Has : LocativeClass → Reading → Prop
  | .narrow, r => r = .location
  | .point, r => r = .path
  | .extended, _ => True

instance : ∀ c r, Decidable (LocativeClass.Has c r)
  | .narrow, r => inferInstanceAs (Decidable (r = _))
  | .point, r => inferInstanceAs (Decidable (r = _))
  | .extended, _ => inferInstanceAs (Decidable True)

/-- The narrow locative prepositions of Appendix I.1.1 in the fragment. -/
def narrowLocatives : List Dutch.Adposition :=
  [aan, achter, beneden, bij, binnen, boven, buiten, in_, naast, onder, op, tegen, tegenover,
   tussen, voor]

/-- The point locative prepositions of Appendix I.1.2 in the fragment, the inherently directional
ones. -/
def pointLocatives : List Dutch.Adposition := [naar, tot, van, vanaf, vanuit, via]

/-- The extended locative prepositions of Appendix I.1.3 in the fragment. -/
def extendedLocatives : List Dutch.Adposition := [door, langs, om, over₁, rond, uit, voorbij]

/-- The class of a row's adposition, by the fragment's forms. -/
def classes : List (String × LocativeClass) :=
  narrowLocatives.map (fun a ↦ (a.form, .narrow)) ++
    pointLocatives.map (fun a ↦ (a.form, .point)) ++
    extendedLocatives.map (fun a ↦ (a.form, .extended))

theorem classes_spatial :
    ∀ a ∈ narrowLocatives ++ pointLocatives ++ extendedLocatives, a.IsSpatial := by
  decide

-- p. 15
theorem met_zonder_not_spatial : ¬ met.IsSpatial ∧ ¬ zonder.IsSpatial := by
  decide

-- (26) of chapter 2 and Appendix I.2, with *af* treated through its phrase
theorem postposition_classes :
    ∀ a ∈ inventory, a.IsPostposition →
      a.toAdposition ∈ (narrowLocatives ++ extendedLocatives).map (·.toAdposition) ∨
        a.toAdposition = af.toAdposition := by
  decide

-- (21a) of chapter 4
theorem narrowLocative_locational : ∀ a ∈ narrowLocatives, a.direction .pre = some .place := by
  decide

-- (21a) of chapter 4
theorem pointLocative_directional :
    ∀ a ∈ pointLocatives, ∃ d ∈ a.direction .pre, d ≠ .place := by
  decide

-- Appendix I.2
theorem pointLocative_linearization : ∀ a ∈ pointLocatives, a.linearization = {.pre} := by
  decide

-- (24a) of chapter 4
theorem narrowLocative_direction_post :
    ∀ a ∈ narrowLocatives, a.IsPostposition → a.direction .post = some .goal := by
  decide

-- (24b) of chapter 4
theorem extendedLocative_direction_post :
    ∀ a ∈ extendedLocatives, a.IsPostposition → ∃ d ∈ a.direction .post, d ≠ .goal := by
  decide

/-! ### The structures -/

section Structures

variable {W : Type*}

/-- The prepositional phrase of (48b) of chapter 3, `[PP P DP]`. -/
def prePP (p : W) (dp : Tree Cat W) : Tree Cat W := node .P [terminal .P p, dp]

/-- The directional prepositional phrase of (48c), `[DIRP Pⱼ [PP tⱼ DP]]`. -/
def prePPDir (p : W) (dp : Tree Cat W) : Tree Cat W :=
  node .Path [terminal .Path p, node .P [trace 0 .P, dp]]

/-- The postpositional phrase of (48a), `[DIRP DPᵢ [DIR' Pⱼ [PP tⱼ tᵢ]]]`. The same tree with
an R-word is (37c) of chapter 6. -/
def postPP (p : W) (dp : Tree Cat W) : Tree Cat W :=
  node .Path [dp, node .Path [terminal .Path p,
    node .P [trace 0 .P, trace 1 (cat dp)]]]

/-- The R-word phrase of (14) of chapter 5, `[PP Rᵢ [P' P tᵢ]]`. -/
def rWordPP (p : W) (r : Tree Cat W) : Tree Cat W :=
  node .P [r, node .P [terminal .P p, trace 1 (cat r)]]

/-- The circumpositional phrase of (40) of chapter 6, `[DIRP XPᵢ [DIR' F tᵢ]]`. -/
def circumPP (f : W) (x : Tree Cat W) : Tree Cat W :=
  node .Path [x, node .Path [terminal .Path f, trace 2 (cat x)]]

/-- The specifier of a phrase is the daughter beside a head daughter that is itself a phrase, the
bar level; a head that is a terminal has a complement beside it. -/
def spec? (t : Tree Cat W) : Option (Tree Cat W) :=
  match t.children with
  | [s, b] => if headIndex? t = some 1 ∧ b.value.IsPhrase then some s else none
  | _ => none

/-- By the Head Constraint, (43) of chapter 3, nothing inside the bar level of a phrase with a
phonologically specified head is related to anything outside the phrase, so what can leave a
phrase is its specifier and whatever can leave that, the specifier within a specifier of (25) of
chapter 6. -/
def Escapes (x t : Tree Cat W) : Prop := Relation.TransGen (fun x t ↦ spec? t = some x) x t

/-- By the analysis of extraposition the thesis adopts from [barbiers-1995], an adjunct phrase is
extraposed when the verb phrase moves to its highest specifier, which must be free. -/
def Extraposable (t : Tree Cat W) : Prop := (spec? t).isNone

/-- By (34) of chapter 3 a noun phrase in the specifier of the directionality phrase is read as a
path, of dimension 1. An adposition of class `c` must admit that dimension and the object must have
it as one of its possible dimensions, which the predicate `path` says; a phrase in the specifier
has no such requirement. -/
def Licensed (c : LocativeClass) (path : Tree Cat W → Prop) (t : Tree Cat W) : Prop :=
  ∀ x ∈ spec? t, cat t = .Path → cat x = .D → c ≠ .point ∧ path x

variable {p f : W} {dp x : Tree Cat W} {c : LocativeClass} {path : Tree Cat W → Prop}

@[simp] theorem cat_prePP : cat (prePP p dp) = .P := rfl
@[simp] theorem cat_prePPDir : cat (prePPDir p dp) = .Path := rfl
@[simp] theorem cat_postPP : cat (postPP p dp) = .Path := rfl
@[simp] theorem cat_rWordPP : cat (rWordPP p x) = .P := rfl
@[simp] theorem cat_circumPP : cat (circumPP f x) = .Path := rfl

@[simp] theorem spec_prePP : spec? (prePP p dp) = none := by
  by_cases h : cat dp = .P <;> simp [spec?, prePP, headIndex?, RoseTree.children, h]

@[simp] theorem spec_prePPDir : spec? (prePPDir p dp) = none := by
  simp [spec?, prePPDir, headIndex?, RoseTree.children]

theorem spec_postPP (h : cat dp ≠ .Path) : spec? (postPP p dp) = some dp := by
  simp [spec?, postPP, headIndex?, RoseTree.children, h, Label.IsPhrase]

theorem spec_rWordPP (h : cat x ≠ .P) : spec? (rWordPP p x) = some x := by
  simp [spec?, rWordPP, headIndex?, RoseTree.children, h, Label.IsPhrase]

theorem spec_circumPP (h : cat x ≠ .Path) : spec? (circumPP f x) = some x := by
  simp [spec?, circumPP, headIndex?, RoseTree.children, h, Label.IsPhrase]

theorem yield_prePP : (prePP p dp).yield = p :: dp.yield := by
  simp [prePP, yield, terminals, RoseTree.leafList, Label.terminal?]

theorem yield_prePPDir : (prePPDir p dp).yield = p :: dp.yield := by
  simp [prePPDir, yield, terminals, RoseTree.leafList, Label.terminal?]

theorem yield_postPP : (postPP p dp).yield = dp.yield ++ [p] := by
  simp [postPP, yield, terminals, RoseTree.leafList, Label.terminal?]

theorem escapes_of_spec (h : spec? x = some dp) : Escapes dp x := .single h

theorem not_escapes_of_spec_eq_none (h : spec? x = none) : ¬ Escapes dp x := fun he ↦ by
  cases he <;> simp_all

theorem escapes_iff_of_spec {s : Tree Cat W} (h : spec? x = some s) :
    Escapes dp x ↔ dp = s ∨ Escapes dp s := by
  refine ⟨fun he ↦ ?_, ?_⟩
  · cases he with
    | single h' => exact .inl (Option.some.inj (h'.symm.trans h))
    | tail hd h' =>
      obtain rfl := Option.some.inj (h'.symm.trans h)
      exact .inr hd
  · rintro (rfl | hd)
    · exact .single h
    · exact .tail hd h

/-- A postpositional phrase is licensed exactly when its object can be read as a path and its
adposition is not a point locative, one condition for the bare mass nouns of (38)-(39) of chapter
3, the small objects of (41), and the R-words of (31) and (37) of chapter 6. -/
theorem licensed_postPP_iff (h : cat dp = .D) :
    Licensed c path (postPP p dp) ↔ c ≠ .point ∧ path dp := by
  have hne : cat dp ≠ .Path := by simp [h]
  simp [Licensed, spec_postPP hne, h]

theorem licensed_prePP : Licensed c path (prePP p dp) := by simp [Licensed]

theorem licensed_prePPDir : Licensed c path (prePPDir p dp) := by simp [Licensed]

theorem licensed_rWordPP : Licensed c path (rWordPP p x) := by simp [Licensed]

theorem licensed_circumPP (h : cat x = .P) : Licensed c path (circumPP f x) := by
  have hne : cat x ≠ .Path := by simp [h]
  simp [Licensed, spec_circumPP hne, h]

/-- The forms the rows name. -/
inductive Form where
  | prePP
  | prePPDir
  | postPP
  | rWordPP
  | circumPP
  /-- An R-word in the specifier of a phrase in the specifier, (39)-(40) of chapter 6. -/
  | circumRPP
  /-- An R-word replacing a phrase in the specifier, (35)-(36) of chapter 6. -/
  | proPP
  deriving DecidableEq, Repr

/-- The tree of a form, over a lower adposition `p`, an upper one `f`, and an object; in `proPP`
the R-word that replaces the phrase has the word `p`. -/
def Form.tree (p f : W) (o : Tree Cat W) : Form → Tree Cat W
  | .prePP => Helmantel2002.prePP p o
  | .prePPDir => Helmantel2002.prePPDir p o
  | .postPP => Helmantel2002.postPP p o
  | .rWordPP => Helmantel2002.rWordPP p o
  | .circumPP => Helmantel2002.circumPP f (Helmantel2002.prePP p o)
  | .circumRPP => Helmantel2002.circumPP f (Helmantel2002.rWordPP p o)
  | .proPP => Helmantel2002.circumPP f (terminal .P p)

variable {o : Tree Cat W}

theorem licensed_tree_iff (h : cat o = .D) (F : Form) :
    Licensed c path (F.tree p f o) ↔ (F = .postPP → c ≠ .point ∧ path o) := by
  cases F
  · simpa [Form.tree] using licensed_prePP
  · simpa [Form.tree] using licensed_prePPDir
  · simpa [Form.tree] using licensed_postPP_iff h
  · simpa [Form.tree] using licensed_rWordPP
  · simpa [Form.tree] using licensed_circumPP rfl
  · simpa [Form.tree] using licensed_circumPP rfl
  · simpa [Form.tree] using licensed_circumPP rfl

/-- What leaves a phrase is an object in its specifier, in the postpositional order, or an R-word,
in the specifier of a prepositional phrase or of one in a specifier. A full object stays inside a
prepositional phrase, whether or not it is directional. -/
theorem escapes_tree_iff (h : cat o = .D) (F : Form) :
    Escapes o (F.tree p f o) ↔ F = .postPP ∨ F = .rWordPP ∨ F = .circumRPP := by
  have h₁ : cat o ≠ .Path := by simp [h]
  have h₂ : cat o ≠ .P := by simp [h]
  have h₃ : cat (terminal Cat.P p) ≠ Cat.Path := (by decide : Cat.P ≠ Cat.Path)
  have hne (t : Tree Cat W) (ht : cat t ≠ .D) : o ≠ t := fun e ↦ ht (e ▸ h)
  cases F
  · simpa [Form.tree] using not_escapes_of_spec_eq_none spec_prePP
  · simpa [Form.tree] using not_escapes_of_spec_eq_none spec_prePPDir
  · simpa [Form.tree] using escapes_of_spec (spec_postPP h₁)
  · simpa [Form.tree] using escapes_of_spec (spec_rWordPP h₂)
  · simpa [Form.tree, escapes_iff_of_spec (spec_circumPP (by simp : cat (prePP p o) ≠ .Path)),
      hne (prePP p o) (by simp)] using not_escapes_of_spec_eq_none spec_prePP
  · simpa [Form.tree, escapes_iff_of_spec (spec_circumPP (by simp : cat (rWordPP p o) ≠ .Path)),
      hne (rWordPP p o) (by simp)] using escapes_of_spec (spec_rWordPP h₂)
  · simpa [Form.tree, escapes_iff_of_spec (spec_circumPP h₃),
      hne (terminal Cat.P p) (by decide : Cat.P ≠ Cat.D)] using
      not_escapes_of_spec_eq_none (by rfl : spec? (terminal Cat.P p) = none)

-- (28) of chapter 6
theorem not_escapes_prePP_rWordPP : ¬ Escapes o (prePP f (rWordPP p o)) :=
  not_escapes_of_spec_eq_none spec_prePP

/-- A prepositional phrase with or without a directionality phrase can extrapose, and a phrase with
its highest specifier occupied, postpositional, circumpositional or an R-word phrase, cannot. -/
theorem extraposable_tree_iff (h : cat o = .D) (F : Form) :
    Extraposable (F.tree p f o) ↔ F = .prePP ∨ F = .prePPDir := by
  have h₁ : cat o ≠ .Path := by simp [h]
  have h₂ : cat o ≠ .P := by simp [h]
  have h₃ : cat (terminal Cat.P p) ≠ Cat.Path := (by decide : Cat.P ≠ Cat.Path)
  cases F <;> simp [Extraposable, Form.tree, spec_postPP h₁, spec_rWordPP h₂, spec_circumPP h₃,
    spec_circumPP]

end Structures

/-! ### The rows of chapters 1, 2, 3, 5 and 6 -/

/-- A row's object: whether it can be read as a path. A definite can have dimension 1 (pp. 10, 76),
no dimension can be determined for a bare mass noun (p. 76), an R-word cannot be read as a path,
(33) of chapter 6, and neither can a pebble by an adult of average size, (41) of chapter 3. -/
def objects : List (String × Bool) :=
  [("definite", true), ("bareMass", false), ("rWord", false), ("pointlike", false)]

/-- The forms under the names the rows use. -/
def forms : List (String × Form) :=
  [("prePP", .prePP), ("prePPDir", .prePPDir), ("postPP", .postPP), ("rWordPP", .rWordPP),
   ("circumPP", .circumPP), ("circumRPP", .circumRPP), ("proPP", .proPP)]

/-- The reading each test requires: *plek* and *zich bevinden* a location, *reis*, *zetten* with
a postpositional phrase and resultative *wandelen* a path. -/
def tests : List (String × Reading) :=
  [("plek", .location), ("bevinden", .location), ("reis", .path), ("zetten", .path),
   ("wandelen", .path)]

/-- The class and the required reading a test row reads. -/
def test? (e : Datum) : Option (LocativeClass × Reading) := do
  pure (← e.parse? "adposition" classes, ← e.parse? "test" tests)

-- (24)-(30) of chapter 1
theorem test_rows :
    Datum.Checks test? (fun x ↦ .ofProp (x.1.Has x.2)) Examples.all 19 := by
  decide +kernel

/-- The form a row of a test names. -/
def form? (test : String) (e : Datum) : Option Form :=
  if e.feature? "test" = some test then e.parse? "structure" forms else none

/-- What a licensing row reads. -/
def licensing? (e : Datum) : Option (LocativeClass × Bool × Form) := do
  pure (← e.parse? "adposition" classes, ← e.parse? "object" objects, ← form? "licensing" e)

-- (38)-(41) of chapter 3, (31), (35)-(39) of chapter 6; the prediction is `licensed_tree_iff`
theorem licensing_rows :
    Datum.Checks licensing? (fun x ↦ .ofProp (x.2.2 = .postPP → x.1 ≠ .point ∧ x.2.1 = true))
      Examples.all 20 := by
  decide +kernel

-- (13), (18), (36) of chapter 2, (42) of chapter 3; the prediction is `escapes_tree_iff`
theorem extraction_rows :
    Datum.Checks (form? "extraction")
      (fun F ↦ .ofProp (F = .postPP ∨ F = .rWordPP ∨ F = .circumRPP)) Examples.all 6 := by
  decide +kernel

-- (14), (29) of chapter 2, (12), (17) of chapter 5; the prediction is `extraposable_tree_iff`
theorem extraposition_rows :
    Datum.Checks (form? "extraposition") (fun F ↦ .ofProp (F = .prePP ∨ F = .prePPDir))
      Examples.all 10 := by
  decide +kernel

/-! ### Place vectors -/

section Vectors

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `w` lengthens `v` when it has the direction of `v` and is at least as long. -/
def IsLengthening (v w : V) : Prop := SameRay ℝ v w ∧ ‖v‖ ≤ ‖w‖

/-- Zwarts's closure property, footnote 5 of chapter 4. -/
def ClosedUnderLengthening (S : Set V) : Prop :=
  ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, IsLengthening v w → w ∈ S

/-- A length modifier `d` restricts a region to its vectors of length `d`, (14) and (16) of chapter
4, and a region is modifiable when no length is excluded from it. -/
def Modifiable (S : Set V) : Prop := ∀ d > 0, (S ∩ Metric.sphere 0 d).Nonempty

/-- The shapes of denotation of a locative preposition, relative to its reference object. -/
inductive Region where
  /-- (11a), *op*. -/
  | zero
  /-- (11b), *bij* and *aan*, for a pragmatically given `r`. -/
  | ball
  /-- (11c), *in*, *binnen* and *tussen*, for the radius of the object or the distance between
  the objects `r`. -/
  | closedBall
  /-- (5b), *buiten*. -/
  | outside
  /-- (7), the projective prepositions, for the unit vector `a` of their axis: the vector's
  projection on the axis is longer than its projection on the perpendicular. -/
  | projective
  deriving DecidableEq, Repr

/-- The vectors of a shape, starting at the reference object as the origin, (3)-(4). -/
def Region.carrier (r : ℝ) (a : V) : Region → Set V
  | .zero => {0}
  | .ball => Metric.ball 0 r
  | .closedBall => Metric.closedBall 0 r
  | .outside => {0}ᶜ
  | .projective => {v | ‖v - ⟪a, v⟫ • a‖ < ⟪a, v⟫}

/-- The prepositions of (17) under their shapes: (17a) restricted, (17b) not. -/
def regions : List (String × Region) :=
  [("op", .zero), ("bij", .ball), ("aan", .ball), ("in", .closedBall), ("binnen", .closedBall),
   ("tussen", .closedBall), ("buiten", .outside), ("voor", .projective), ("achter", .projective),
   ("naast", .projective), ("boven", .projective), ("beneden", .projective),
   ("onder", .projective)]

/-- The shapes the length restriction of (11) covers. -/
def Region.IsRestricted : Region → Prop
  | .zero | .ball | .closedBall => True
  | .outside | .projective => False

instance : DecidablePred Region.IsRestricted := fun R ↦ by
  cases R <;> unfold Region.IsRestricted <;> infer_instance

variable {S : Set V}

omit [InnerProductSpace ℝ V] in
theorem not_modifiable_of_isBounded (h : Bornology.IsBounded S) : ¬ Modifiable S := fun hm ↦ by
  obtain ⟨R, hR⟩ := h.exists_norm_le
  obtain ⟨v, hv, hd⟩ := hm (|R| + 1) (by positivity)
  have := hR v hv
  rw [mem_sphere_zero_iff_norm] at hd
  linarith [le_abs_self R]

theorem not_closedUnderLengthening_of_isBounded [Nontrivial V] (h : Bornology.IsBounded S)
    (hne : S.Nonempty) : ¬ ClosedUnderLengthening S := fun hc ↦ by
  obtain ⟨R, hR⟩ := h.exists_norm_le
  obtain ⟨v, hv⟩ := hne
  have long : ∃ w : V, SameRay ℝ v w ∧ ‖v‖ ≤ ‖w‖ ∧ R < ‖w‖ := by
    obtain rfl | hv0 := eq_or_ne v 0
    · obtain ⟨w, hw⟩ := exists_norm_eq V (show (0 : ℝ) ≤ |R| + 1 by positivity)
      exact ⟨w, .zero_left w, by simp, by linarith [le_abs_self R]⟩
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have hw : ‖((|R| + 1 + ‖v‖) / ‖v‖) • v‖ = |R| + 1 + ‖v‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hn.ne']
      exact ⟨((|R| + 1 + ‖v‖) / ‖v‖) • v,
        SameRay.sameRay_nonneg_smul_right v (by positivity), by rw [hw]; linarith [abs_nonneg R],
        by rw [hw]; linarith [le_abs_self R]⟩
  obtain ⟨w, hs, hle, hlt⟩ := long
  exact absurd (hR w (hc hv ⟨hs, hle⟩)) (not_le.2 hlt)

theorem smul_mem_projective {r : ℝ} {a v : V} (hv : v ∈ Region.projective.carrier r a) {c : ℝ}
    (hc : 0 < c) : c • v ∈ Region.projective.carrier r a := by
  simp only [Region.carrier, Set.mem_ofPred_eq, inner_smul_right] at hv ⊢
  have : c • v - (c * ⟪a, v⟫) • a = c • (v - ⟪a, v⟫ • a) := by rw [smul_sub, smul_smul]
  rw [this, norm_smul, Real.norm_of_nonneg hc.le]
  exact mul_lt_mul_of_pos_left hv hc

variable {r : ℝ} {a : V}

theorem closedUnderLengthening_outside (a : V) :
    ClosedUnderLengthening (Region.outside.carrier r a) := fun v hv w hw ↦ by
  simp only [Region.carrier, Set.mem_compl_iff, Set.mem_singleton_iff] at hv ⊢
  rintro rfl
  exact hv (norm_le_zero_iff.1 (by simpa using hw.2))

theorem closedUnderLengthening_projective (a : V) :
    ClosedUnderLengthening (Region.projective.carrier r a) := fun v hv w hw ↦ by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [Region.carrier] at hv
  obtain ⟨c, hc, rfl⟩ := hw.1.exists_nonneg_left hv0
  have hw0 : c ≠ 0 := by
    rintro rfl
    have := hw.2
    simp only [zero_smul, norm_zero] at this
    exact hv0 (norm_le_zero_iff.1 this)
  exact smul_mem_projective hv (lt_of_le_of_ne hc hw0.symm)

theorem modifiable_outside [Nontrivial V] (a : V) : Modifiable (Region.outside.carrier r a) :=
  fun d hd ↦ by
    obtain ⟨v, hv⟩ := exists_norm_eq V hd.le
    refine ⟨v, ?_, by simpa using hv⟩
    simp only [Region.carrier, Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp at hv
    linarith

theorem modifiable_projective (ha : ‖a‖ = 1) : Modifiable (Region.projective.carrier r a) :=
  fun d hd ↦ by
    refine ⟨d • a, ?_, by simp [norm_smul, ha, abs_of_pos hd]⟩
    simp [Region.carrier, inner_smul_right, ha, hd]

theorem isBounded_carrier_of_isRestricted : ∀ {R : Region}, R.IsRestricted →
    Bornology.IsBounded (R.carrier r a)
  | .zero, _ => Bornology.isBounded_singleton
  | .ball, _ => Metric.isBounded_ball
  | .closedBall, _ => Metric.isBounded_closedBall

variable [Nontrivial V]

theorem modifiable_carrier_iff (ha : ‖a‖ = 1) (R : Region) :
    Modifiable (R.carrier r a) ↔ ¬ R.IsRestricted := by
  by_cases h : R.IsRestricted
  · exact iff_of_false (not_modifiable_of_isBounded (isBounded_carrier_of_isRestricted h))
      (not_not.2 h)
  · cases R
    exacts [absurd trivial h, absurd trivial h, absurd trivial h,
      iff_of_true (modifiable_outside a) h, iff_of_true (modifiable_projective ha) h]

theorem isBounded_carrier_iff (ha : ‖a‖ = 1) (R : Region) :
    Bornology.IsBounded (R.carrier r a) ↔ R.IsRestricted :=
  ⟨fun hb ↦ by_contra fun h ↦ not_modifiable_of_isBounded hb ((modifiable_carrier_iff ha R).2 h),
    isBounded_carrier_of_isRestricted⟩

/-- Zwarts's closure under lengthening and the thesis's vector length restriction pick out the
same denotations, as p. 107 says: the regions closed under lengthening are the unrestricted ones,
for a positive radius, in a space with more than one vector. -/
theorem closedUnderLengthening_carrier_iff (hr : 0 < r) (R : Region) :
    ClosedUnderLengthening (R.carrier r a) ↔ ¬ R.IsRestricted := by
  have hne : ∀ {R : Region}, R.IsRestricted → (R.carrier r a).Nonempty
    | .zero, _ => Set.singleton_nonempty _
    | .ball, _ => ⟨0, by simpa [Region.carrier] using hr⟩
    | .closedBall, _ => ⟨0, by simpa [Region.carrier] using hr.le⟩
  by_cases h : R.IsRestricted
  · exact iff_of_false (not_closedUnderLengthening_of_isBounded
      (isBounded_carrier_of_isRestricted h) (hne h)) (not_not.2 h)
  · cases R
    exacts [absurd trivial h, absurd trivial h, absurd trivial h,
      iff_of_true (closedUnderLengthening_outside a) h,
      iff_of_true (closedUnderLengthening_projective a) h]

omit [InnerProductSpace ℝ V] [Nontrivial V] in
-- (18) of chapter 4: a modifier is contradictory or uninformative at every length exactly when all
-- the vectors of the region have one length
theorem forall_inter_sphere_iff :
    (∀ d, S ∩ Metric.sphere 0 d = ∅ ∨ S ∩ Metric.sphere 0 d = S) ↔ (norm '' S).Subsingleton := by
  constructor
  · rintro h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hmem : u ∈ S ∩ Metric.sphere 0 ‖u‖ := ⟨hu, by simp⟩
    rcases h ‖u‖ with h' | h'
    · rw [h'] at hmem
      exact hmem.elim
    · have hv' : v ∈ S ∩ Metric.sphere 0 ‖u‖ := by rw [h']; exact hv
      simpa using hv'.2.symm
  · intro h d
    by_cases hne : (S ∩ Metric.sphere 0 d).Nonempty
    · obtain ⟨u, hu, hd⟩ := hne
      refine Or.inr (Set.inter_eq_left.2 fun v hv ↦ ?_)
      have : ‖v‖ = ‖u‖ := h ⟨v, hv, rfl⟩ ⟨u, hu, rfl⟩
      simpa [this] using hd
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)

theorem not_subsingleton_norm_image_ball (hr : 0 < r) :
    ¬ (norm '' Metric.ball (0 : V) r).Subsingleton := fun h ↦ by
  obtain ⟨v, hv⟩ := exists_norm_eq V (half_pos hr).le
  have := h ⟨v, by simp [hv, half_lt_self hr], rfl⟩ ⟨0, by simpa using hr, rfl⟩
  simp [hv] at this
  linarith

theorem not_subsingleton_norm_image_closedBall (hr : 0 < r) :
    ¬ (norm '' Metric.closedBall (0 : V) r).Subsingleton := fun h ↦
  not_subsingleton_norm_image_ball hr (h.anti (Set.image_mono Metric.ball_subset_closedBall))

-- p. 109: *vlak* is possible unless `|v| = 0`
theorem exists_ne_zero_carrier_iff (hr : 0 < r) (ha : ‖a‖ = 1) (R : Region) :
    (∃ v ∈ R.carrier r a, v ≠ 0) ↔ R ≠ .zero := by
  obtain ⟨v, hv⟩ := exists_norm_eq V (half_pos hr).le
  have hv0 : v ≠ 0 := fun h ↦ by simp [h] at hv; linarith
  cases R
  · simp [Region.carrier]
  · exact iff_of_true ⟨v, by simp [Region.carrier, hv, half_lt_self hr], hv0⟩ (by simp)
  · exact iff_of_true ⟨v, by simp [Region.carrier, hv, (half_lt_self hr).le], hv0⟩ (by simp)
  · exact iff_of_true ⟨v, by simpa [Region.carrier] using hv0, hv0⟩ (by simp)
  · obtain ⟨u, hu, -⟩ := modifiable_projective (r := r) ha 1 one_pos
    refine iff_of_true ⟨u, hu, fun h ↦ ?_⟩ (by simp)
    simp [h, Region.carrier] at hu

end Vectors

/-! ### Paths -/

/-- The length of the path relative to an object of length `ℓ`: a narrow locative postposition's
path occupies part of the object, an extended locative's the whole, (26) of chapter 4. A point
locative has no postpositional use. -/
def pathLengths (ℓ : ℝ) : LocativeClass → Set ℝ
  | .narrow => Set.Ioc 0 ℓ
  | .point => ∅
  | .extended => {ℓ}

theorem pathLengths_subsingleton_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (c : LocativeClass) :
    (pathLengths ℓ c).Subsingleton ↔ c ≠ .narrow := by
  cases c
  · refine iff_of_false (fun h ↦ ?_) (by simp)
    have := h (show ℓ / 2 ∈ Set.Ioc 0 ℓ from ⟨by positivity, by linarith⟩)
      (show ℓ ∈ Set.Ioc 0 ℓ from ⟨hℓ, le_rfl⟩)
    linarith
  · exact iff_of_true Set.subsingleton_empty (by simp)
  · exact iff_of_true Set.subsingleton_singleton (by simp)

theorem pathLengths_narrow_subset (ℓ : ℝ) :
    pathLengths ℓ .narrow ⊆ Metric.closedBall 0 ℓ := fun x hx ↦ by
  simpa [abs_of_pos hx.1] using hx.2

/-- The restriction of (13) and (29) does not separate the prepositional *in* of (15d), which a
modifier cannot measure, from the postpositional *in* of (27a), which it can: the lengths of both
are bounded by the object and neither is fixed. -/
theorem restriction_does_not_separate {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Bornology.IsBounded (pathLengths ℓ .narrow) ∧ ¬ (pathLengths ℓ .narrow).Subsingleton ∧
      Bornology.IsBounded (Metric.closedBall (0 : ℝ) ℓ) ∧
        ¬ (norm '' Metric.closedBall (0 : ℝ) ℓ).Subsingleton :=
  ⟨Metric.isBounded_closedBall.subset (pathLengths_narrow_subset ℓ),
    fun h ↦ (pathLengths_subsingleton_iff hℓ .narrow).1 h rfl, Metric.isBounded_closedBall,
    not_subsingleton_norm_image_closedBall hℓ⟩

/-! ### The rows of chapter 4 -/

/-- The shape of a row of a test. -/
def region? (test : String) (e : Datum) : Option Region :=
  if e.feature? "test" = some test then e.parse? "adposition" regions else none

-- (9), (10), (15) of chapter 4; the prediction is `modifiable_carrier_iff`
theorem length_rows :
    Datum.Checks (region? "length") (fun R ↦ .ofProp (¬ R.IsRestricted)) Examples.all 16 := by
  decide +kernel

/-- The class of a row whose object measures a path. -/
def path? (e : Datum) : Option LocativeClass :=
  if e.feature? "test" = some "pathLength" then e.parse? "adposition" classes else none

-- (27), (28) of chapter 4, (31) of chapter 1; the prediction is `pathLengths_subsingleton_iff`
theorem pathLength_rows :
    Datum.Checks path? (fun c ↦ .ofProp (c = .narrow)) Examples.all 10 := by
  decide +kernel

/-- The shape of a *vlak* row, leaving out *in* and *tussen*, which p. 108 explains otherwise. -/
def vlak? (e : Datum) : Option Region :=
  if e.feature? "adposition" = some "in" ∨ e.feature? "adposition" = some "tussen" then none
  else region? "vlak" e

-- (19), (20a) of chapter 4; the prediction is `exists_ne_zero_carrier_iff`
theorem vlak_rows : Datum.Checks vlak? (fun R ↦ .ofProp (R ≠ .zero)) Examples.all 7 := by
  decide +kernel

end Helmantel2002
