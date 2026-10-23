module

public import Linglib.Syntax.Minimalist.LateMerger
public import Linglib.Syntax.Minimalist.Label.MinimalSearch
public import Linglib.Syntax.Minimalist.Locality.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Licensing
public import Linglib.Syntax.Minimalist.Derivation.Reconstruction
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Clause.Relative
public import Linglib.Data.Examples.Privizentseva2026

/-!
# Privizentseva (2026): The Syntax of Relative Clauses and the Nature of Merge

In Moksha the head of an externally headed relative clause may bear the case assigned inside the
relative clause instead of the main-clause case, inverse case attraction (ICA). The book argues
that the head's case predicts its connectivity: relatives with ICA are derived by raising,
regular externally headed relatives by the head-external derivation, and no rival that gives the
two one derivation, or raises both, fits the data (chapter 4).

A derivation is a chain of the head noun phrase. Its restrictor is first merged at the foot or,
by wholesale late merger, at a position where the noun phrase receives case, which the order of
the head noun's case probe and its Merge feature for the relative CP fixes (the book's Table 5.1,
`caseSite`). An idiom needs the noun first merged with its verb, an anaphor in the head a binder
above some merge point, and Condition C a merge point above the pronoun
(`Minimalist.LateMergerBleeds`). The same order explains the left-periphery restriction: a head
whose case was valued in the relative clause has no active case probe for main-clause selection,
so it is displaced (section 5.3), which the labeling algorithm, labeling the verb and its object
whatever the object's case, does not force. Merging the relative determiner with a noun that
still selects the relative clause is outside triggered Merge, where one factor is saturated; the
book lets a phrase be selected before it is saturated (section 5.5), which licenses every stage
of the raising derivation; triggered Merge rejects the stages before the noun is copied out,
though it accepts the derived object, which holds only the noun's trace. The derivation copies
the noun and *kona*'s phrase onto a stack and merges them back in the reverse order. Moving
*kona*'s phrase first and subextracting the noun, the alternative footnote 14 of the article
weighs, is licensed as well, but violates Freezing, which the stack derivation obeys, and leaves
the complementizer and the noun out of c-command. The appositive and restrictive readings of
relatives with ICA rule out a correlative or internally headed placement (section 3.3.1), and
attraction is not ordered by a case hierarchy (section 3.5).

## Main statements

* `rows_predicted`: the analysis predicts every structural connectivity judgment of chapter 4.
* `no_uniform_derivation`, `raising_only_fails`: the rivals the book rejects fail on the rows.
* `inSitu_rows`: a relative stays in its base position exactly when its head's case probe is
  still active there.
* `raisingRelative_licensed`, `triggeredMerge_rejects_raisingRelative`: selection before
  saturation licenses the raising derivation at every stage, which triggered Merge rejects though
  it accepts the derived object.

## Implementation notes

* Heights order the head's position in the relative clause below the main-clause position, with
  a binder or pronoun of each clause just above the head's position there.
* Variable binding by a pronoun and crossover show no contrast between the two kinds of relative
  (`pronounVariable_and_crossover_uniform`); the book concludes that they do not rest on
  c-command in syntax, and they are not modelled as structural.
* Rows with speaker variation (`%`, the second idiom) are left out of `rows_predicted`.

## TODO

* Section 6.2 obviates Condition C in the main clause, for a name inside the relative clause,
  by late merger of the head with its relative clause into the external determiner, which the
  chain of the head's restrictor does not model; the rows ch. 6 (11) and (12) record the data.
* The merge positions that section 5.4.4 gives the head inside a postpositional phrase are not
  modelled; `konaRows_case` records the pattern they derive.
* A bare-noun object is a lexical leaf, which ties with the verb under minimal search, so the
  labeling argument of section 5.3.2 covers phrasal objects only.

## References

* [privizentseva-2026a]
* [privizentseva-2026b]
* [takahashi-hulsey-2009]
* [grosu-landman-1998]
-/

@[expose] public section

namespace Privizentseva2026

open Minimalist (ChainPosition LateMergerBleeds)

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

/-- The reverse order, that of languages without ICA such as German and Polish
([privizentseva-2026b], Table 2), values it in the main clause. -/
theorem caseSite_external : caseSite .rc [.mergeCP, .case] = some .matrix := rfl

/-! ### Derivations of the head noun phrase -/

/-- A derivation of the head noun phrase: raising from the relative clause, with the order of the
head noun's features, or the head-external derivation. -/
inductive Derivation where
  | raising (order : List Feature)
  | headExternal
  deriving DecidableEq, Repr

/-- The chain of the head noun phrase, lowest position first; a position admits the late merger
of the restrictor when the noun phrase receives case there. -/
def Derivation.chain : Derivation → List ChainPosition
  | .raising o => [⟨Site.rc.height, caseSite .rc o == some .rc⟩,
      ⟨Site.matrix.height, caseSite .rc o == some .matrix⟩]
  | .headExternal => [⟨Site.matrix.height, true⟩]

/-- The restrictor is first merged at the foot of the chain or, by wholesale late merger, at a
position where the noun phrase receives case. -/
def Derivation.MergesAt (d : Derivation) (p : ChainPosition) : Prop :=
  p ∈ d.chain ∧ (d.chain.head? = some p ∨ p.admissible = true)

instance (d : Derivation) : DecidablePred d.MergesAt :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- An idiom whose verb is at `s` is licensed when the noun can be first merged there, as a
constituent with the verb. -/
def Derivation.IdiomAt (d : Derivation) (s : Site) : Prop :=
  ∃ p ∈ d.chain, d.MergesAt p ∧ p.height = s.height

/-- A binder at `s` binds an anaphor in the head when the restrictor can be merged at a position
the binder c-commands, binding applying at any stage. -/
def Derivation.AnaphorAt (d : Derivation) (s : Site) : Prop :=
  ∃ p ∈ d.chain, d.MergesAt p ∧ p.height < s.binderHeight

/-- A pronoun at `s` can corefer with a name in the head when the restrictor can be merged above
it, out of its c-command domain. -/
def Derivation.ObviatesAt (d : Derivation) (s : Site) : Prop :=
  LateMergerBleeds d.MergesAt ChainPosition.height d.chain s.binderHeight

instance (d : Derivation) (s : Site) : Decidable (d.IdiomAt s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (d : Derivation) (s : Site) : Decidable (d.AnaphorAt s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (d : Derivation) (s : Site) : Decidable (d.ObviatesAt s) :=
  inferInstanceAs (Decidable (LateMergerBleeds _ _ _ _))

/-! ### The data -/

/-- The case on the head of a relative clause: the internal case of ICA, assigned inside the
relative clause, or the external case of the main clause. -/
inductive HeadCase where
  | internal
  | external
  deriving DecidableEq, Repr

/-- The connectivity diagnostics that rest on c-command in syntax. -/
inductive Diagnostic where
  | idiom
  | anaphor
  | reflexiveVariable
  | conditionC
  deriving DecidableEq, Repr

/-- What a derivation licenses for a diagnostic at a site: a reflexive read as a bound variable
patterns with anaphor binding. -/
def Derivation.Licenses (d : Derivation) : Diagnostic → Site → Prop
  | .idiom, s => d.IdiomAt s
  | .anaphor, s | .reflexiveVariable, s => d.AnaphorAt s
  | .conditionC, s => d.ObviatesAt s

instance (d : Derivation) : ∀ g s, Decidable (d.Licenses g s)
  | .idiom, s => inferInstanceAs (Decidable (d.IdiomAt s))
  | .anaphor, s | .reflexiveVariable, s => inferInstanceAs (Decidable (d.AnaphorAt s))
  | .conditionC, s => inferInstanceAs (Decidable (d.ObviatesAt s))

/-- A relative clause of chapter 4 testing a structural diagnostic: the case on its head, the
diagnostic, the site of the idiom's verb, binder or pronoun, and whether the tested reading is
accepted. -/
structure Row where
  headCase : HeadCase
  diagnostic : Diagnostic
  site : Site
  accepted : Bool
  deriving DecidableEq, Repr

/-- Condition C rows are judged on the coreferent reading, the others on the sentence. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  guard (ex.judgment ≠ .variable)
  guard (ex.feature? "section" ∈ [some "4.3.1", some "4.3.2", some "4.3.3", some "4.3.4",
    some "4.3.5"])
  let headCase ← ex.parse? "rcType" [("ICA", HeadCase.internal), ("external", .external)]
  let diagnostic ← ex.parse? "diagnostic"
    [("idiom", Diagnostic.idiom), ("anaphor", .anaphor),
      ("reflexiveVariable", .reflexiveVariable), ("conditionC", .conditionC)]
  let site ← ex.parse? "site" [("rc", Site.rc), ("matrix", .matrix)]
  let judgment ← match diagnostic with
    | .conditionC => ex.readings.lookup "coreferent"
    | _ => some ex.judgment
  pure ⟨headCase, diagnostic, site, decide (.variable ≤ judgment)⟩

/-- The structural connectivity rows of chapter 4. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = 20 := by decide

/-- The rows testing variable binding by a pronoun and crossover: the case on the head and
whether the bound reading is accepted. -/
def boundRows : List (HeadCase × Bool) := Examples.all.filterMap fun ex ↦ do
  guard (ex.feature? "diagnostic" = some "pronounVariable" ∨
    ex.feature? "diagnostic" = some "crossover")
  let headCase ← ex.parse? "rcType" [("ICA", HeadCase.internal), ("external", .external)]
  let judgment ← ex.readings.lookup "bound" <|> some ex.judgment
  pure (headCase, judgment == .acceptable)

example : boundRows.length = 16 := by decide

theorem pronounVariable_and_crossover_uniform :
    (∀ r ∈ boundRows, r.2 = true) ∧ (∃ r ∈ boundRows, r.1 = .internal) ∧
      ∃ r ∈ boundRows, r.1 = .external := by
  decide

/-! ### The analysis -/

/-- The book's analysis: relatives with ICA raise with the case probe above the Merge feature,
regular externally headed relatives are head-external. -/
def analysis : HeadCase → Derivation
  | .internal => .raising [.case, .mergeCP]
  | .external => .headExternal

/-- A derivation fits a row when it licenses the tested reading exactly when the row accepts it. -/
def Derivation.Fits (d : Derivation) (r : Row) : Prop :=
  r.accepted = true ↔ d.Licenses r.diagnostic r.site

instance (d : Derivation) (r : Row) : Decidable (d.Fits r) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The analysis predicts every structural connectivity judgment of chapter 4. -/
theorem rows_predicted : ∀ r ∈ rows, (analysis r.headCase).Fits r := by
  decide

/-- Section 4.4.3: no derivation shared by both kinds of relative fits the data, since one cell
receives opposite judgments for the two kinds. This rules out the head-external derivation for
both, with ICA by agreement with the relative pronoun (section 4.4.3.1), and matching for both
when the two heads differ only at PF (section 4.4.3.3). -/
theorem no_uniform_derivation (d : Derivation) : ¬ ∀ r ∈ rows, d.Fits r := by
  intro h
  obtain ⟨r₁, h₁, r₂, h₂, hg, hs, ha₁, ha₂⟩ : ∃ r₁ ∈ rows, ∃ r₂ ∈ rows,
      r₁.diagnostic = r₂.diagnostic ∧ r₁.site = r₂.site ∧ r₁.accepted = true ∧
        r₂.accepted = false := by decide
  have e₁ := h r₁ h₁
  have e₂ := h r₂ h₂
  unfold Derivation.Fits at e₁ e₂
  rw [hg, hs] at e₁
  simp_all

/-- Section 4.4.3.2: raising both kinds, the external case valued after movement, fails even with
wholesale late merger tying connectivity to case: nothing keeps the restrictor of an
external-case head from being merged below its case position, in the relative clause, where it
could form an idiom or be bound. -/
theorem raising_only_fails :
    ∃ r ∈ rows, r.headCase = .external ∧ ¬ (Derivation.raising [.mergeCP, .case]).Fits r := by
  decide

theorem obviatesAt_rc :
    ¬ (analysis .internal).ObviatesAt .rc ∧
      (Derivation.raising [.mergeCP, .case]).ObviatesAt .rc := by
  decide

/-! ### The left periphery (sections 3.3.2 and 5.3) -/

/-- Main-clause heads select a noun phrase with an active probe, the second-order selection of
section 5.3.1. A head noun phrase whose case probe was valued inside the relative clause has no
active case probe left in the main clause, so it must bear another probe, a topic, focus or Q
feature, which displaces it to the left periphery. -/
def Derivation.ForcedExSitu : Derivation → Prop
  | .raising o => caseSite .rc o = some .rc
  | .headExternal => False

instance : DecidablePred Derivation.ForcedExSitu
  | .raising o => inferInstanceAs (Decidable (caseSite .rc o = some .rc))
  | .headExternal => inferInstanceAs (Decidable False)

/-- The rows placing a relative clause with its head in the base position of the head noun
phrase in the main clause, for a subject below a sentence adverb (section 5.3.2): the case on
the head and whether the sentence is accepted. -/
def inSituRows : List (HeadCase × Bool) := Examples.all.filterMap fun ex ↦ do
  guard (ex.feature? "position" ∈ [some "inSitu", some "afterAdverb"])
  let headCase ← ex.parse? "rcType" [("ICA", HeadCase.internal), ("external", .external)]
  pure (headCase, ex.judgment == .acceptable)

example : inSituRows.length = 6 := by decide

/-- A relative clause stays in the base position of its head exactly when its derivation does
not force the head noun phrase out of it. -/
theorem inSitu_rows : ∀ r ∈ inSituRows, r.2 = true ↔ ¬ (analysis r.1).ForcedExSitu := by
  decide

-- Section 5.3.2: the labeling algorithm labels a verb merged with any phrasal object, whatever
-- case the object's head bears, so a failure to label, the alternative account of forced
-- displacement the section examines, cannot displace a direct object with ICA.
example {t : Minimalist.LinearizedSyntacticObject} {v : Minimalist.LexicalItem.Token}
    {x : Minimalist.SyntacticObject} (hex : ∃ n, t.termAt n = .merge (.leaf v) x)
    (hx : x.token? = none) (hv : t.InDomain (.leaf v) (.merge (.leaf v) x)) :
    t.IsLabeledBy (.merge (.leaf v) x) v :=
  Minimalist.LinearizedSyntacticObject.isLabeledBy_merge_head hex hx hv

/-- Section 5.2.2: the relative determiner selects the head noun while the noun still selects the
relative clause, so the two merge with selection pending on both, which triggered Merge never
licenses: of the factors of a defined selection product one is saturated. -/
theorem selCheck_merge_eq_zero_of_sel_ne_nil {d n : Minimalist.LexicalItem.Token}
    (hd : d.item.sel ≠ []) (hn : n.item.sel ≠ []) :
    (Minimalist.SyntacticObject.merge (.leaf d) (.leaf n)).selCheck = 0 := by
  by_contra h
  rw [Minimalist.SyntacticObject.selCheck_node, Minimalist.SyntacticObject.selCheck_leaf,
    Minimalist.SyntacticObject.selCheck_leaf] at h
  have := Minimalist.SelectionState.isSaturated_iff_not_isSaturated_of_mul_ne_zero h
  simp_all [Minimalist.SelectionState.IsSaturated, Minimalist.SelectionState.residual,
    Minimalist.SelectionState.of]

/-! ### Projecting movement (section 5.2.2) -/

section ProjectingMovement

open Minimalist

/-- A selection state that lets an item still selecting be selected, the second implication the
book draws (section 5.5): the head, its remaining selectors, and the selectors pending from items
selected before they were saturated. -/
structure PendingState where
  toOption : Option (LexicalItem.Token × List Cat × Multiset Cat)
  deriving DecidableEq

namespace PendingState

instance : Zero PendingState := ⟨⟨none⟩⟩

/-- One factor selects the other, which need not be saturated; the selectee's remaining selectors
become pending. -/
def combine : PendingState → PendingState → PendingState
  | ⟨some (a, ra, p)⟩, ⟨some (b, rb, q)⟩ =>
    if ra.head? = some b.item.cat ∧ rb.head? ≠ some a.item.cat then ⟨some (a, ra.tail, p + q + rb)⟩
    else if rb.head? = some a.item.cat ∧ ra.head? ≠ some b.item.cat then
      ⟨some (b, rb.tail, p + q + ra)⟩
    else ⟨none⟩
  | _, _ => ⟨none⟩

instance : MulZeroClass PendingState where
  mul := combine
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | ⟨a, ra, p⟩⟩ <;> rfl

theorem mul_def (x y : PendingState) : x * y = combine x y := rfl

instance : CommMagma PendingState where
  mul_comm x y := by
    rcases x with ⟨_ | ⟨a, ra, p⟩⟩ <;> rcases y with ⟨_ | ⟨b, rb, q⟩⟩ <;>
      simp only [mul_def, combine]
    split_ifs <;> simp_all [add_comm]

instance : Head PendingState where
  head x := x.toOption.map (·.1)
  head_zero := rfl
  mem_head_or_mem_head_of_mem_head_mul {x y t} h := by
    rcases x with ⟨_ | ⟨a, ra, p⟩⟩ <;> rcases y with ⟨_ | ⟨b, rb, q⟩⟩ <;>
      simp only [Option.mem_def, mul_def, combine] at h ⊢
    all_goals first | cases h | (split_ifs at h <;> simp_all)

end PendingState

/-- Selection before saturation as a licensing: a token with its selectors, a trace a saturated
copy of the phrase its token heads. -/
noncomputable def pendingHom : SyntacticObject →ₙ* PendingState :=
  SyntacticObject.lift (fun tok ↦ ⟨some (tok, tok.item.sel, 0)⟩)
    (fun u ↦ ⟨some (u.getD .bareTrace, [], 0)⟩)

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
  (LinearizedSyntacticObject.merge (.leaf kona) (.traceOf headNoun)).toSyntacticObject

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
        pendingHom c.current.toSyntacticObject = ⟨some (externalD, [], 0)⟩ := by
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
  (LinearizedSyntacticObject.merge (.leaf kona) (.leaf headNoun)).toSyntacticObject

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

/-- Read with the heads of triggered Merge, *kona*'s phrase, which has none there, leaves the bare
trace, and selection before saturation then rejects the stage where it moved. -/
example : ¬ ∃ p ∈ (subextractionRelative.take 5).externalize?,
    pendingHom p.toSyntacticObject ≠ 0 := by
  decide

end ProjectingMovement

/-! ### The attracted case (section 3.5) -/

/-- The cases the rows name, read as the comparative cases of `Case`. -/
def caseNames : List (String × Case) :=
  [("NOM", .nom), ("GEN", .gen), ("DAT", .dat), ("ABL", .abl), ("IN", .ine), ("EL", .ela),
    ("ILL", .ill)]

/-- The accepted relatives with ICA: the external case and the attracted internal case. -/
def attractions : List (Case × Case) := Examples.all.filterMap fun ex ↦ do
  guard (ex.feature? "rcType" = some "ICA" ∧ ex.judgment = .acceptable)
  let ext ← ex.parse? "externalCase" caseNames
  let int ← ex.parse? "internalCase" caseNames
  pure (ext, int)

/-- Section 3.5: ICA is not governed by a case hierarchy. Attraction runs both ways between the
nominative and the genitive, so no asymmetric relation, a hierarchy in particular, ranks the
attracted case above the case it replaces in every accepted relative. -/
theorem not_hierarchy (r : Case → Case → Prop) [Std.Asymm r] :
    ¬ ∀ p ∈ attractions, r p.2 p.1 := by
  intro h
  have h₁ : (Case.nom, Case.gen) ∈ attractions := by decide
  have h₂ : (Case.gen, Case.nom) ∈ attractions := by decide
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
  deriving DecidableEq, Repr

/-- The rows testing a reading: the strategy, the reading the test requires, a proper-name head
the appositive and a free-choice head the restrictive, and whether the sentence is accepted. -/
def readingRows : List (Strategy × Reading × Bool) := Examples.all.filterMap fun ex ↦ do
  let strategy ← ex.parse? "rcType"
    [("ICA", Strategy.ica), ("external", .external), ("correlative", .correlative)]
  let reading ← (ex.features "test").findSome?
    ([("properName", Reading.appositive), ("freeChoice", .restrictive)].lookup ·)
  pure (strategy, reading, ex.judgment == .acceptable)

example : readingRows.length = 6 := by decide

/-- A placement fits the readings of a strategy when it allows exactly the tested readings the
rows accept. -/
def ReadingsFit (p : Relativization.Placement) (s : Strategy) : Prop :=
  ∀ x ∈ readingRows, x.1 = s → (x.2.2 = true ↔ Allows p x.2.1)

instance (p : Relativization.Placement) (s : Strategy) : Decidable (ReadingsFit p s) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Section 3.3.1: relatives with ICA have appositive and restrictive readings, so of the
placements only an externally headed one fits them, as it fits regular relatives. -/
theorem fits_ica_iff (p : Relativization.Placement) :
    ReadingsFit p .ica ↔ p = .postNominal ∨ p = .preNominal := by
  revert p; decide

theorem fits_correlative_iff (p : Relativization.Placement) :
    ReadingsFit p .correlative ↔ p = .correlative := by
  revert p; decide

/-! ### The case of the relative pronoun (sections 3.5 and 5.4.4) -/

/-- The cases of the relative pronoun *kona*: nominative, genitive and dative. An ablative form
occurs only in a few contexts, after *baška* 'except'; for a missing case a genitive *kona* with
a postposition, or for direction a dative, stands in. -/
def konaCases : List Case := [.nom, .gen, .dat]

/-- The relatives with ICA recording the case on the head and on *kona*, with whether the
sentence is accepted. -/
def konaRows : List (Case × Case × Bool) := Examples.all.filterMap fun ex ↦ do
  guard (ex.feature? "rcType" = some "ICA")
  let head ← ex.parse? "headCase" caseNames
  let kona ← ex.parse? "relPronounCase" caseNames
  pure (head, kona, ex.judgment == .acceptable)

example : konaRows.length = 34 := by decide

attribute [local instance high] List.decidableBAll in
theorem konaRows_case :
    (∀ x ∈ konaRows, x.2.2 = true → (x.1 = x.2.1 ↔ x.1 ∈ konaCases)) ∧
      ∀ x ∈ konaRows, x.2.1 ∉ konaCases → x.2.2 = false := by
  decide

/-- The rows associating a left-peripheral noun phrase or relative clause with a position inside
an adjunct or complex noun phrase island: the strategy, if any, and whether it is accepted. -/
def islandRows : List (Option Strategy × Bool) := Examples.all.filterMap fun ex ↦ do
  guard ((ex.features "test").any (· ∈ ["adjunctIsland", "complexNPIsland"]) ∧
    ex.feature? "position" = some "leftEdge")
  let strategy := ex.parse? "rcType"
    [("ICA", Strategy.ica), ("external", .external), ("correlative", .correlative)]
  pure (strategy, ex.judgment == .acceptable)

example : islandRows.length = 8 := by decide

attribute [local instance high] List.decidableBAll in
/-- Section 3.3.2: a plain noun phrase and both kinds of externally headed relative are rejected
at the left edge when their base position is inside an island, and correlatives are not, so the
first reach the left edge by movement and correlatives are generated there. -/
theorem islandRows_accepted : ∀ x ∈ islandRows, x.2 = true ↔ x.1 = some .correlative := by
  decide

end Privizentseva2026
