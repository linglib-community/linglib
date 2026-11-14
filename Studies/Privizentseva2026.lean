module

public import Linglib.Syntax.Minimalist.LateMerger
public import Linglib.Syntax.Minimalist.Label.MinimalSearch
public import Linglib.Syntax.Minimalist.Derivation.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Licensing
public import Linglib.Syntax.Minimalist.Derivation.Binding
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Clause.Relative
public import Linglib.Data.Examples.Privizentseva2026
public import Linglib.Data.Examples.Readers

/-!
# Privizentseva (2026): The Syntax of Relative Clauses and the Nature of Merge

In Moksha the head of an externally headed relative clause may bear the case assigned inside the
relative clause, inverse case attraction (ICA). The book derives relatives with ICA by raising
and the others by the head-external derivation, which [predicts the connectivity of
each](##analysis_fits) as [no derivation shared by both does](##no_uniform_derivation). Raising
merges the relative determiner with a noun that still selects the relative clause, so the book
lets a phrase be selected before it is saturated. [Triggered Merge is that licensing with nothing
pending](##selCheck_ne_zero_iff): it [rejects the stages of the raising
derivation](##triggeredMerge_rejects_raisingRelative) that hold the unsaturated noun, all of
which [selection before saturation licenses](##raisingRelative_licensed).

## Implementation notes

* A derivation is a chain of the head noun phrase. Its restrictor is first merged at the foot or,
  by wholesale late merger, where the noun phrase receives case, which the order of the head
  noun's case probe and its Merge feature for the relative CP fixes (`caseSite`). Heights order
  the head's position in the relative clause below the main-clause position, with a binder or
  pronoun of each clause just above the head's position there.
* Variable binding by a pronoun and crossover show no contrast between the two kinds of relative
  (`pronounVariable_and_crossover_uniform`); the book concludes that they do not rest on
  c-command in syntax, and they are not modelled as structural.
* Rows with speaker variation (`%`, the second idiom) are left out of `rows`.
* `PendingState` is a one-field structure over `Option`, as `Minimalist.SelectionState` is. Its
  product never discharges a pending selector: an object has nothing pending once the item
  selected before it was saturated is copied out, leaving a saturated trace.

## TODO

* Section 6.2 obviates Condition C in the main clause, for a name inside the relative clause,
  by late merger of the head with its relative clause into the external determiner, which the
  chain of the head's restrictor does not model; the rows ch. 6 (11) and (12) record the data.
* The merge positions that section 5.4.4 gives the head inside a postpositional phrase are not
  modelled; `konaRows_case` records the pattern they derive.
* A bare-noun object is a lexical leaf, which ties with the verb under minimal search, so the
  labeling argument of section 5.3.2 covers phrasal objects only.
* [cinque-2020] derives non-restrictive relatives by matching only (`Cinque2020.RCType.Admits`),
  while relatives with ICA raise and have an appositive reading, which section 5.4 reconciles;
  the two are not compared.

## References

* [privizentseva-2026a]
* [privizentseva-2026b]
* [takahashi-hulsey-2009]
* [grosu-landman-1998]
* [cinque-2020]
-/

@[expose] public section

namespace Privizentseva2026

open Minimalist (LateMergerBleeds)

/-! ### Sites and features -/

/-- The clauses the head of a relative clause relates to. -/
inductive Site where
  | rc
  | matrix
  deriving DecidableEq, Repr

/-- The height of the head's position in each clause, the relative clause below the main
clause. -/
def Site.height : Site → ℕ
  | .rc => 0
  | .matrix => 2

/-- A binder or pronoun in a clause sits just above the head's position in that clause. -/
def Site.binderHeight : Site → ℕ
  | .rc => 1
  | .matrix => 3

/-- The two features of the head noun whose order the book's Table 5.1 varies: its case probe
and its Merge feature for the relative CP. -/
inductive Feature where
  | case
  | mergeCP
  deriving DecidableEq, Repr

/-- The site where the head noun's case probe is valued. Only the top feature of the stack is
accessible: the probe is valued where it reaches the top, and checking the Merge feature moves
the noun from the relative clause to the main clause. -/
def caseSite : Site → List Feature → Option Site
  | s, .case :: _ => some s
  | .rc, .mergeCP :: fs => caseSite .matrix fs
  | _, _ => none

theorem caseSite_ica : caseSite .rc [.case, .mergeCP] = some .rc := rfl

-- Table 2 [privizentseva-2026b]
theorem caseSite_external : caseSite .rc [.mergeCP, .case] = some .matrix := rfl

/-! ### Derivations of the head noun phrase -/

/-- A derivation of the head noun phrase: raising from the relative clause, with the order of the
head noun's features, or the head-external derivation. -/
inductive Derivation where
  | raising (order : List Feature)
  | headExternal
  deriving DecidableEq, Repr

/-- The chain of the head noun phrase, lowest position first. -/
def Derivation.chain : Derivation → List Site
  | .raising _ => [.rc, .matrix]
  | .headExternal => [.matrix]

/-- The position where the head noun phrase receives case: where its case probe is valued when it
is raised, the main clause when it is external. -/
def Derivation.casePosition : Derivation → Option Site
  | .raising o => caseSite .rc o
  | .headExternal => some .matrix

/-- The restrictor is first merged at the foot of the chain or, by wholesale late merger, at the
position where the noun phrase receives case. -/
def Derivation.MergesAt (d : Derivation) (p : Site) : Prop :=
  p ∈ d.chain ∧ (d.chain.head? = some p ∨ d.casePosition = some p)

instance (d : Derivation) : DecidablePred d.MergesAt :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A binder at `s` binds an anaphor in the head when the restrictor can be merged at a position
the binder c-commands, binding applying at any stage. -/
def Derivation.AnaphorAt (d : Derivation) (s : Site) : Prop :=
  ∃ p ∈ d.chain, d.MergesAt p ∧ p.height < s.binderHeight

instance (d : Derivation) (s : Site) : Decidable (d.AnaphorAt s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A pronoun at `s` can corefer with a name in the head when the restrictor can be merged above
it, out of its c-command domain. -/
def Derivation.ObviatesAt (d : Derivation) (s : Site) : Prop :=
  LateMergerBleeds d.MergesAt Site.height d.chain s.binderHeight

instance (d : Derivation) (s : Site) : Decidable (d.ObviatesAt s) :=
  inferInstanceAs (Decidable (LateMergerBleeds _ _ _ _))

/-- The connectivity diagnostics that rest on c-command in syntax. -/
inductive Diagnostic where
  | idiom
  | anaphor
  | reflexiveVariable
  | conditionC
  deriving DecidableEq, Repr

/-- What a derivation licenses for a diagnostic at a site. An idiom whose verb is at the site
needs the noun first merged there, as a constituent with the verb, and a reflexive read as a
bound variable patterns with anaphor binding. -/
def Derivation.Licenses (d : Derivation) : Diagnostic → Site → Prop
  | .idiom, s => d.MergesAt s
  | .anaphor, s | .reflexiveVariable, s => d.AnaphorAt s
  | .conditionC, s => d.ObviatesAt s

instance (d : Derivation) : ∀ g s, Decidable (d.Licenses g s)
  | .idiom, s => inferInstanceAs (Decidable (d.MergesAt s))
  | .anaphor, s | .reflexiveVariable, s => inferInstanceAs (Decidable (d.AnaphorAt s))
  | .conditionC, s => inferInstanceAs (Decidable (d.ObviatesAt s))

/-! ### The data -/

/-- The case on the head of a relative clause: the internal case of ICA, assigned inside the
relative clause, or the external case of the main clause. -/
inductive HeadCase where
  | internal
  | external
  deriving DecidableEq, Repr, Fintype

/-- The case on the head of the relative clause of an example. -/
def headCase? (ex : Datum) : Option HeadCase :=
  ex.parse? "rcType" [("ICA", .internal), ("external", .external)]

/-- A relative clause of chapter 4 testing a structural diagnostic: the case on its head, the
diagnostic, the site of the idiom's verb, binder or pronoun, and the judgment of the tested
reading. -/
structure Row where
  headCase : HeadCase
  diagnostic : Diagnostic
  site : Site
  judgment : Judgment
  deriving DecidableEq, Repr

/-- Condition C rows are judged on the coreferent reading, the others on the sentence. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  guard (ex.feature? "section" ∈ [some "4.3.1", some "4.3.2", some "4.3.3", some "4.3.4",
    some "4.3.5"])
  let headCase ← headCase? ex
  let diagnostic ← ex.parse? "diagnostic"
    [("idiom", Diagnostic.idiom), ("anaphor", .anaphor),
      ("reflexiveVariable", .reflexiveVariable), ("conditionC", .conditionC)]
  let site ← ex.parse? "site" [("rc", Site.rc), ("matrix", .matrix)]
  let judgment ← match diagnostic with
    | .conditionC => ex.readings.lookup "coreferent"
    | _ => some ex.judgment
  guard (judgment ≠ .variable)
  pure ⟨headCase, diagnostic, site, judgment⟩

/-- The structural connectivity rows of chapter 4. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The case on the head of a row testing variable binding by a pronoun or crossover. -/
def boundTest? (ex : Datum) : Option HeadCase := do
  guard (ex.feature? "diagnostic" ∈ [some "pronounVariable", some "crossover"])
  headCase? ex

theorem pronounVariable_and_crossover_uniform :
    (∀ e ∈ Examples.all, ∀ _c ∈ boundTest? e, e.readings.lookup "bound" = some .acceptable) ∧
      ∀ c, (Examples.all.filterMap boundTest?).count c = 8 := by
  decide +kernel

/-! ### The analysis -/

/-- The book's analysis: relatives with ICA raise with the case probe above the Merge feature,
regular externally headed relatives are head-external. -/
def analysis : HeadCase → Derivation
  | .internal => .raising [.case, .mergeCP]
  | .external => .headExternal

/-- A derivation fits a row when it licenses the tested reading exactly when the row accepts it. -/
def Derivation.Fits (d : Derivation) (r : Row) : Prop :=
  r.judgment.band = .ofProp (d.Licenses r.diagnostic r.site)

instance (d : Derivation) (r : Row) : Decidable (d.Fits r) :=
  inferInstanceAs (Decidable (_ = _))

/-- The analysis predicts every structural connectivity judgment of chapter 4. -/
theorem analysis_fits : (∀ r ∈ rows, (analysis r.headCase).Fits r) ∧ rows.length = 20 := by
  decide

/-- No derivation shared by both kinds of relative fits the data, which rules out those of section
4.4.3.1 and section 4.4.3.3 (Section 4.4.3). -/
theorem no_uniform_derivation (d : Derivation) : ¬ ∀ r ∈ rows, d.Fits r := by
  intro h
  obtain ⟨r₁, h₁, r₂, h₂, hg, hs, hj⟩ : ∃ r₁ ∈ rows, ∃ r₂ ∈ rows,
      r₁.diagnostic = r₂.diagnostic ∧ r₁.site = r₂.site ∧
        r₁.judgment.band ≠ r₂.judgment.band := by decide
  have e₁ : r₁.judgment.band = _ := h r₁ h₁
  rw [hg, hs] at e₁
  exact hj (e₁.trans (h r₂ h₂).symm)

-- Section 4.4.3.2: raising both kinds, with the external case valued after movement, fails even
-- under wholesale late merger
theorem raising_only_fails :
    ∃ r ∈ rows, r.headCase = .external ∧ ¬ (Derivation.raising [.mergeCP, .case]).Fits r := by
  decide

theorem obviatesAt_rc :
    ¬ (analysis .internal).ObviatesAt .rc ∧
      (Derivation.raising [.mergeCP, .case]).ObviatesAt .rc := by
  decide

/-! ### The left periphery (sections 3.3.2 and 5.3) -/

/-- The case on the head of a relative clause standing in the base position of its head noun
phrase in the main clause, for a subject below a sentence adverb (section 5.3.2). -/
def inSitu? (ex : Datum) : Option HeadCase := do
  guard (ex.feature? "position" ∈ [some "inSitu", some "afterAdverb"])
  headCase? ex

-- Section 5.3.1: main-clause heads select a noun phrase with an active probe. A head noun phrase
-- whose case probe was valued inside the relative clause has no active case probe left in the
-- main clause, so it bears a topic, focus or Q probe, which displaces it to the left periphery;
-- a relative clause stays in the base position of its head exactly when its head's case was not
-- valued there
theorem inSitu_rows :
    Datum.Checks inSitu? (fun c ↦ .ofProp ((analysis c).casePosition ≠ some .rc))
      Examples.all 6 := by
  decide +kernel

-- Section 5.3.2: the labeling algorithm labels a verb merged with any phrasal object, whatever
-- case the object's head bears, so a failure to label, the alternative account of forced
-- displacement the section examines, cannot displace a direct object with ICA.
example {t : Minimalist.PlanarSyntacticObject} {v : Minimalist.LexicalItem.Token}
    {x : Minimalist.SyntacticObject} (hex : ∃ n, t.termAt n = .merge (.leaf v) x)
    (hx : x.token? = none) (hv : t.InDomain (.leaf v) (.merge (.leaf v) x)) :
    t.IsLabeledBy (.merge (.leaf v) x) v :=
  Minimalist.PlanarSyntacticObject.isLabeledBy_merge_head hex hx hv

/-! ### Projecting movement (section 5.2.2) -/

section ProjectingMovement

open Minimalist

/-- A selection state that lets an item still selecting be selected (section 5.5): the head, its
remaining selectors, and the selectors pending from items selected before they were saturated;
`0` where Merge fails. -/
structure PendingState where
  toOption : Option (LexicalItem.Token × List Cat × Multiset Cat)
  deriving DecidableEq

namespace PendingState

/-- The state with head `tok`, remaining selectors `stack` and pending selectors `pending`. -/
def of (tok : LexicalItem.Token) (stack : List Cat) (pending : Multiset Cat) : PendingState :=
  ⟨some (tok, stack, pending)⟩

instance : Zero PendingState := ⟨⟨none⟩⟩

/-- Recursor for `PendingState` using the preferred forms `0` and `of tok stack pending`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recZeroOf {motive : PendingState → Sort*} (zero : motive 0)
    (of : ∀ tok stack pending, motive (of tok stack pending)) : ∀ x, motive x
  | ⟨none⟩ => zero
  | ⟨some (tok, stack, pending)⟩ => of tok stack pending

/-- One factor selects the other, which need not be saturated; the selectee's remaining selectors
become pending. -/
instance : MulZeroClass PendingState where
  mul
    | ⟨some (a, ra, p)⟩, ⟨some (b, rb, q)⟩ =>
      if ra.head? = some b.item.cat ∧ rb.head? ≠ some a.item.cat then of a ra.tail (p + q + rb)
      else if rb.head? = some a.item.cat ∧ ra.head? ≠ some b.item.cat then
        of b rb.tail (p + q + ra)
      else 0
    | _, _ => 0
  zero_mul _ := rfl
  mul_zero x := by cases x <;> rfl

section

variable (a b : LexicalItem.Token) (ra rb : List Cat) (p q : Multiset Cat)

theorem of_mul_of : of a ra p * of b rb q =
    if ra.head? = some b.item.cat ∧ rb.head? ≠ some a.item.cat then of a ra.tail (p + q + rb)
    else if rb.head? = some a.item.cat ∧ ra.head? ≠ some b.item.cat then
      of b rb.tail (p + q + ra)
    else 0 := rfl

@[simp] theorem of_ne_zero : of a ra p ≠ 0 := mt (congrArg toOption) (Option.some_ne_none _)

instance : CommMagma PendingState where
  mul_comm x y := by
    cases x <;> cases y <;> try rfl
    simp only [of_mul_of]
    split_ifs <;> simp_all [add_comm]

instance : Head PendingState where
  head x := x.toOption.map (·.1)
  head_zero := rfl
  mem_head_or_mem_head_of_mem_head_mul {x y t} h := by
    cases x <;> cases y <;> try cases h
    simp only [of_mul_of] at h
    split_ifs at h
    exacts [.inl (by cases h; rfl), .inr (by cases h; rfl), by cases h]

@[simp] theorem head_of : head (of a ra p) = some a := rfl

/-- The selection state of a state with nothing pending, and `0` otherwise. -/
def toSelectionState : PendingState → SelectionState
  | ⟨some (a, ra, p)⟩ => if p = 0 then .of a ra else 0
  | ⟨none⟩ => 0

@[simp] theorem toSelectionState_zero : toSelectionState 0 = 0 := rfl

theorem toSelectionState_of :
    (of a ra p).toSelectionState = if p = 0 then .of a ra else 0 := rfl

theorem toSelectionState_ne_zero_iff {x : PendingState} :
    x.toSelectionState ≠ 0 ↔ ∃ a ra, x = of a ra 0 := by
  cases x with
  | zero => exact iff_of_false (fun h ↦ h rfl) fun ⟨a, ra, h⟩ ↦ of_ne_zero _ _ _ h.symm
  | of a ra p =>
    rw [toSelectionState_of]
    split_ifs with hp
    · subst hp
      exact iff_of_true (mt (congrArg SelectionState.toOption) (Option.some_ne_none _)) ⟨a, ra, rfl⟩
    · exact iff_of_false (fun h ↦ h rfl) fun ⟨b, rb, h⟩ ↦ hp (by cases h; rfl)

end

/-- Triggered Merge is selection before saturation with nothing pending, as a morphism of
magmas. -/
def toSelectionStateHom : PendingState →ₙ* SelectionState where
  toFun := toSelectionState
  map_mul' x y := by
    cases x with
    | zero => rw [zero_mul, toSelectionState_zero, zero_mul]
    | of a ra p =>
      cases y with
      | zero => rw [mul_zero, toSelectionState_zero, mul_zero]
      | of b rb q =>
        rw [of_mul_of, toSelectionState_of, toSelectionState_of]
        rcases ra with _ | ⟨c, ra⟩ <;> rcases rb with _ | ⟨c', rb⟩ <;>
          by_cases hp : p = 0 <;> by_cases hq : q = 0 <;>
          simp [SelectionState.mul_def, selCombine, SelectionState.of, hp, hq] <;>
          first | rfl | (split_ifs <;> first | rfl | simp_all [toSelectionState_of])

@[simp] theorem toSelectionStateHom_apply (x : PendingState) :
    toSelectionStateHom x = x.toSelectionState := rfl

end PendingState

/-- Selection before saturation as a licensing: a token with its selectors, a trace a saturated
copy of the phrase its token heads. -/
def pendingHom : SyntacticObject →ₙ* PendingState :=
  FreeCommMagma.lift (SyntacticObject.Leaf.elim (fun tok ↦ .of tok tok.item.sel 0)
    fun u ↦ .of (u.getD .bareTrace) [] 0)

-- Triggered Merge factors through selection before saturation
theorem toSelectionStateHom_comp_pendingHom :
    PendingState.toSelectionStateHom.comp pendingHom = SyntacticObject.selCheckHom :=
  FreeCommMagma.hom_ext fun ℓ ↦ by cases ℓ <;> rfl

theorem toSelectionState_pendingHom (s : SyntacticObject) :
    (pendingHom s).toSelectionState = s.selCheck :=
  DFunLike.congr_fun toSelectionStateHom_comp_pendingHom s

/-- Triggered Merge licenses exactly the objects that selection before saturation licenses with
nothing pending. -/
theorem selCheck_ne_zero_iff (s : SyntacticObject) :
    s.selCheck ≠ 0 ↔ ∃ a ra, pendingHom s = .of a ra 0 := by
  rw [← toSelectionState_pendingHom, PendingState.toSelectionState_ne_zero_iff]

theorem PendingState.head_toSelectionState {x : PendingState} (h : x.toSelectionState ≠ 0) :
    head x.toSelectionState = head x := by
  obtain ⟨a, ra, rfl⟩ := toSelectionState_ne_zero_iff.1 h
  simp only [toSelectionState_of, ↓reduceIte]
  rfl

-- Section 5.5: selection before saturation licenses every derivation of triggered Merge
theorem licensedBy_pendingHom {d : Minimalist.Derivation}
    (h : d.LicensedBy SyntacticObject.selCheckHom) : d.LicensedBy pendingHom :=
  .of_comp pendingHom PendingState.toSelectionStateHom rfl
    (fun _ ↦ PendingState.head_toSelectionState) (toSelectionStateHom_comp_pendingHom ▸ h)

-- (12): triggered Merge has no product of the relative determiner with a noun still selecting
theorem selCheck_merge_eq_zero_of_sel_ne_nil {d n : LexicalItem.Token}
    (hd : d.item.sel ≠ []) (hn : n.item.sel ≠ []) :
    (SyntacticObject.merge (.leaf d) (.leaf n)).selCheck = 0 := by
  by_contra h
  rw [SyntacticObject.selCheck_node, SyntacticObject.selCheck_leaf,
    SyntacticObject.selCheck_leaf] at h
  have := SelectionState.isSaturated_iff_not_isSaturated_of_mul_ne_zero h
  simp_all [SelectionState.IsSaturated, SelectionState.residual, SelectionState.of]

/-- The head noun, selecting the relative CP. -/
def headNoun : LexicalItem.Token := ⟨.of .N [.C], 1⟩

/-- The relative pronoun *kona*, selecting the noun. -/
def kona : LexicalItem.Token := ⟨.of .D [.N] (phonForm := "kona"), 2⟩

/-- The verb of the relative clause, selecting *kona*'s phrase. -/
def rcVerb : LexicalItem.Token := ⟨.of .V [.D], 3⟩

/-- Tense, selecting the verb phrase. -/
def rcTense : LexicalItem.Token := ⟨.of .T [.V], 4⟩

/-- The relative complementizer, selecting tense and then *kona*'s phrase. -/
def relC : LexicalItem.Token := ⟨.of .C [.T, .D], 5⟩

/-- The external determiner, selecting the noun. -/
def externalD : LexicalItem.Token := ⟨.of .D [.N], 6⟩

/-- *Kona*'s phrase once the noun is copied out of it, the noun's trace in its place. -/
def konaRemnant : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf kona) (.traceOf headNoun)).toSyntacticObject

/-- The raising relative of section 5.2.2. The noun merges with *kona* while it still selects the
relative CP, which is built over them. Once the complementizer is merged, the noun and then
*kona*'s phrase are copied onto the stack (the book's (14)); *kona*'s phrase merges back first, at
the edge of the CP (15), and the noun last, selecting the CP and projecting (16); the external
determiner selects it (17). -/
def raisingRelative : Minimalist.Derivation :=
  ⟨headNoun, [.em .left kona, .em .left rcVerb, .em .left rcTense, .em .left relC,
    .extract headNoun, .extract konaRemnant, .remerge, .remerge, .em .left externalD]⟩

/-- Selection before saturation licenses every stage of the raising relative, which obeys Freezing
and ends with an empty stack and nothing pending: the noun's selector, pending since *kona*
selected it, is checked once the noun merges back and selects the relative CP. -/
theorem raisingRelative_licensed :
    raisingRelative.LicensedBy pendingHom ∧ raisingRelative.ObeysFreezing ∧
      ∃ c ∈ raisingRelative.replay? (head ∘ pendingHom), c.stack = [] ∧
        pendingHom c.current.toSyntacticObject = .of externalD [] 0 := by
  decide

/-- Triggered Merge accepts the derived relative but rejects its derivation: it fails exactly at
the stages where the noun, still selecting, sits inside *kona*'s phrase, before it is copied out,
which the derived object, holding only the noun's trace there, no longer shows. -/
theorem triggeredMerge_rejects_raisingRelative :
    raisingRelative.LicensedAt SyntacticObject.selCheckHom raisingRelative.length ∧
      ∀ n ≤ raisingRelative.length,
        (¬ raisingRelative.LicensedAt SyntacticObject.selCheckHom n ↔ n ∈ [1, 2, 3, 4]) := by
  decide

/-- *Kona*'s phrase, *kona* selecting the noun. -/
def konaPhrase : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf kona) (.leaf headNoun)).toSyntacticObject

/-- The alternative footnote 14 of the article reports: *kona*'s phrase moves to the edge of the
relative CP, and the noun is then subextracted from it to select the CP. -/
def subextractionRelative : Minimalist.Derivation :=
  ⟨headNoun, [.em .left kona, .em .left rcVerb, .em .left rcTense, .em .left relC,
    .im konaPhrase, .im headNoun, .em .left externalD]⟩

theorem subextractionRelative_costs :
    subextractionRelative.LicensedBy pendingHom ∧ ¬ subextractionRelative.ObeysFreezing ∧
      subextractionRelative.CCommandsAt 4 relC headNoun ∧
      ¬ subextractionRelative.CCommandsAt 5 relC headNoun ∧
      ¬ subextractionRelative.CCommandsAt 5 headNoun relC := by
  decide

-- Read with the heads of triggered Merge, *kona*'s phrase, which has none there, leaves the bare
-- trace, and selection before saturation then rejects the stage where it moved.
example : ¬ ∃ p ∈ (subextractionRelative.take 5).externalize?,
    pendingHom p.toSyntacticObject ≠ 0 := by
  decide

end ProjectingMovement

/-! ### The attracted case (section 3.5) -/

/-- The cases the rows name, read as the comparative cases of `Case`. -/
def caseNames : List (String × Case) :=
  [("NOM", .nom), ("GEN", .gen), ("DAT", .dat), ("ABL", .abl), ("IN", .ine), ("EL", .ela),
    ("ILL", .ill)]

/-- An inverse case attraction: the external case the main clause assigns and the internal case
the head bears instead. -/
structure Attraction where
  external : Case
  internal : Case
  deriving DecidableEq

/-- The attractions of the accepted relatives with ICA. -/
def attractions : List Attraction := Examples.all.filterMap fun ex ↦ do
  guard (ex.feature? "rcType" = some "ICA" ∧ ex.judgment = .acceptable)
  pure ⟨← ex.parse? "externalCase" caseNames, ← ex.parse? "internalCase" caseNames⟩

-- Section 3.5: no asymmetric order of the cases has the internal case above the external one in
-- every attraction
theorem not_hierarchy (r : Case → Case → Prop) [Std.Asymm r] :
    ¬ ∀ a ∈ attractions, r a.internal a.external := by
  intro h
  have h₁ : (⟨.nom, .gen⟩ : Attraction) ∈ attractions := by decide
  have h₂ : (⟨.gen, .nom⟩ : Attraction) ∈ attractions := by decide
  exact Std.Asymm.asymm _ _ (h _ h₁) (h _ h₂)

/-! ### Readings (section 3.3.1) -/

/-- The three readings of a relative clause distinguished since [grosu-landman-1998]. -/
inductive Reading where
  | appositive
  | restrictive
  | maximalizing
  deriving DecidableEq, Repr

/-- The readings each placement of a relative clause allows, as section 3.3.1 states the
typology: a correlative is only maximalizing, an internally headed relative is never
appositive, and an externally headed relative allows all three. -/
def Allows : Relativization.Placement → Reading → Prop
  | .correlative, r => r = .maximalizing
  | .internallyHeaded, r => r ≠ .appositive
  | .postNominal, _ | .preNominal, _ => True

instance : ∀ p r, Decidable (Allows p r)
  | .correlative, r => inferInstanceAs (Decidable (r = .maximalizing))
  | .internallyHeaded, r => inferInstanceAs (Decidable (r ≠ .appositive))
  | .postNominal, _ | .preNominal, _ => inferInstanceAs (Decidable True)

/-- The relativization strategies of Moksha: externally headed relatives with ICA or with the
external case, and correlatives. -/
inductive Strategy where
  | ica
  | external
  | correlative
  deriving DecidableEq, Repr, Fintype

/-- The strategy of the relative clause of an example. -/
def strategy? (ex : Datum) : Option Strategy :=
  ex.parse? "rcType" [("ICA", .ica), ("external", .external), ("correlative", .correlative)]

/-- The reading a test of an example of the strategy `s` requires, a proper-name head the
appositive and a free-choice head the restrictive. -/
def reading? (s : Strategy) (ex : Datum) : Option Reading := do
  guard (strategy? ex = some s)
  (ex.features "test").findSome?
    ([("properName", Reading.appositive), ("freeChoice", .restrictive)].lookup ·)

example : ∀ s, Datum.ReadCount (reading? s) Examples.all 2 := by decide +kernel

/-- A placement fits the readings of a strategy when it allows exactly the tested readings the
rows accept. -/
def ReadingsFit (p : Relativization.Placement) (s : Strategy) : Prop :=
  ∀ e ∈ Examples.all, e.Fits (reading? s) fun r ↦ .ofProp (Allows p r)

instance (p : Relativization.Placement) (s : Strategy) : Decidable (ReadingsFit p s) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

-- Section 3.3.1
theorem fits_ica_iff (p : Relativization.Placement) :
    ReadingsFit p .ica ↔ p = .postNominal ∨ p = .preNominal := by
  revert p; decide +kernel

theorem fits_correlative_iff (p : Relativization.Placement) :
    ReadingsFit p .correlative ↔ p = .correlative := by
  revert p; decide +kernel

/-! ### The case of the relative pronoun (sections 3.5 and 5.4.4) -/

/-- The cases of the relative pronoun *kona*: nominative, genitive and dative. An ablative form
occurs only in a few contexts, after *baška* 'except'; for a missing case a genitive *kona* with
a postposition, or for direction a dative, stands in. -/
def konaCases : List Case := [.nom, .gen, .dat]

/-- The case on the head of a relative with ICA and the case on *kona*. -/
structure Marking where
  head : Case
  kona : Case

/-- The marking of a relative with ICA that records both cases. -/
def marking? (ex : Datum) : Option Marking := do
  guard (ex.feature? "rcType" = some "ICA")
  pure ⟨← ex.parse? "headCase" caseNames, ← ex.parse? "relPronounCase" caseNames⟩

theorem konaRows_case :
    (∀ e ∈ Examples.all, ∀ m ∈ marking? e,
      (e.judgment = .acceptable → (m.head = m.kona ↔ m.head ∈ konaCases)) ∧
        (m.kona ∉ konaCases → e.judgment ≠ .acceptable)) ∧
      Datum.ReadCount marking? Examples.all 34 := by
  decide +kernel

/-- The strategy, if any, of a left-peripheral noun phrase or relative clause associated with a
position inside an adjunct or complex noun phrase island. -/
def island? (ex : Datum) : Option (Option Strategy) := do
  guard ((ex.features "test").any (· ∈ ["adjunctIsland", "complexNPIsland"]) ∧
    ex.feature? "position" = some "leftEdge")
  pure (strategy? ex)

-- Section 3.3.2
theorem islandRows_accepted :
    Datum.Checks island? (fun s ↦ .ofProp (s = some .correlative)) Examples.all 8 := by
  decide +kernel

end Privizentseva2026
