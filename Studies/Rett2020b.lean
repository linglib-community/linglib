module

public import Mathlib.Order.Bounds.Basic
public import Linglib.Data.Examples.Rett2020b
public import Linglib.Data.Examples.Readers

/-!
# Rett (2020): Separate but equal: a typology of equative constructions

This file formalizes the chapter's semantic typology of equatives. Descriptively, languages
mark an equative by a relativizer standard marker with or without a parameter marker, by a
predicate meaning *equal* or an adverbial meaning *equally*, by conjoined clauses, by a
case-marked standard, or by dedicated morphemes, `Strategy`. Three diagnostics sort these into
the classes of Figure 3, `Class`: predicative equatives have no weak *at least* reading;
implicit equatives, the standard-marker-only relatives and the conjoined ones, are evaluative;
and explicit equatives, whose parameter is marked, split into the sufficientive ones, which
factor modifiers like *twice* can modify, and the demonstrative ones, which they cannot. The
class semantics of section 5 derive the first two diagnostics: the sufficientive equative
relates degree sets by inclusion, `sufficientive_iff`, the demonstrative one predicates the
standard's maximal degree of the target, `demonstrative_iff`, so both hold when the target
exceeds the standard and neither mentions a standard of tallness, while the implicit equative
equates two evaluative properties, `implicit_evaluative`, and the predicative one an equality,
`not_predicative_of_lt`. Modifiability is the chapter's claim that only the sufficientive
strategy involves degree quantification. The examples of sections 3 and 4 are checked against
Figure 3, `judgment_iff_expected`, and the sufficientive is the equative `μ b ≤ μ a` read at
extent sets, `sufficientive_iff`.

## Implementation notes

The descriptive strategies split the parameter-marked relatives into sufficientive and
demonstrative as section 4.3 does; case-marked and dedicated strategies have no class, as the
chapter leaves them for future research. The Slovenian cells of Figure 2 that the chapter
leaves uncertain have no rows.

## References

* [J. Rett, *Separate but equal: a typology of equative constructions* (2020)][rett-2020b]
* [J. Rett, *The semantics of evaluativity* (2015)][rett-2015]
* [C. Kennedy, *Modes of comparison* (2007)][kennedy-2007a]
-/

@[expose] public section

namespace Rett2020b


/-! ### Strategies and classes -/

/-- The descriptive strategies of section 3, the parameter-marked relatives split as in
section 4.3. -/
inductive Strategy where
  /-- The strategy with only a relativizer standard marker, English *tall like Bill* or Italian
  *come*. -/
  | smOnly
  /-- The strategy with a degree-demonstrative parameter marker and a relativizer standard marker,
  Italian *tanto … quanto* or Spanish *tan … como*. -/
  | demonstrative
  /-- The strategy with a sufficientive parameter marker and a relativizer standard marker, English
  *as … as* or German *so … wie*. -/
  | sufficientive
  /-- The strategy with a main predicate meaning *equal*, Swahili *sawa*. -/
  | predicateMain
  /-- The strategy with an adverbial meaning *equally*, Mandarin *yíyàng* or Swedish *lika*. -/
  | predicateAdverbial
  /-- Conjoined parallel clauses, often with an additive particle. -/
  | conjoined
  /-- The strategy with a case marker or adposition as standard marker, as in Greenlandic and
  Quechua. -/
  | caseMarked
  /-- The strategy with construction-specific markers, Welsh *cyn … â*. -/
  | dedicated
  deriving DecidableEq

/-- The theoretical classes of Figure 3. -/
inductive Class where
  | predicative
  | sufficientive
  | demonstrative
  | implicit
  deriving DecidableEq, Fintype

/-- Figure 3's classification; the predicate subtypes pattern together, the standard-marker-only
relatives and the conjoined equatives are implicit, and the case-marked and dedicated
strategies are left open. -/
def Strategy.class? : Strategy → Option Class
  | .smOnly | .conjoined => some .implicit
  | .demonstrative => some .demonstrative
  | .sufficientive => some .sufficientive
  | .predicateMain | .predicateAdverbial => some .predicative
  | .caseMarked | .dedicated => none

/-- The diagnostics of section 4.1 are the continuation *in fact she's taller*, the continuation
*but she's short*, and a factor modifier. -/
inductive Diagnostic where
  | weak
  | evaluativity
  | factor
  deriving DecidableEq, Fintype

/-- Every class but the predicative one has a weak, *at least* reading. -/
def Class.HasWeakReading : Class → Prop
  | .predicative => False
  | _ => True

/-- The implicit class alone is evaluative. -/
def Class.Evaluative : Class → Prop
  | .implicit => True
  | _ => False

/-- The sufficientive class alone admits a factor modifier, being the only one whose parameter
marker is a degree quantifier. -/
def Class.Modifiable : Class → Prop
  | .sufficientive => True
  | _ => False

instance : DecidablePred Class.HasWeakReading := fun c ↦ by
  cases c <;> unfold Class.HasWeakReading <;> infer_instance

instance : DecidablePred Class.Evaluative := fun c ↦ by
  cases c <;> unfold Class.Evaluative <;> infer_instance

instance : DecidablePred Class.Modifiable := fun c ↦ by
  cases c <;> unfold Class.Modifiable <;> infer_instance

/-- A diagnostic sentence is expected to be acceptable for a class with the weak continuation when
the class has a weak reading, the short continuation when it is not evaluative, and the factor
modifier when it is modifiable. -/
def Class.Expects (c : Class) : Diagnostic → Prop
  | .weak => c.HasWeakReading
  | .evaluativity => ¬ c.Evaluative
  | .factor => c.Modifiable

instance (c : Class) : DecidablePred c.Expects := fun d ↦ by
  cases d <;> unfold Class.Expects <;> infer_instance

/-! ### The class semantics -/

variable {E D : Type*} [LinearOrder D] (μ : E → D) (s : D) (a b : E)

/-- A predicative equative holds when the target's degree equals the standard's. -/
def predicative : Prop := μ a = μ b

/-- The sufficientive equative, the set-based *as* of (5-b), holds when the standard's degrees are
among the target's. -/
def sufficientive : Prop := Set.Iic (μ b) ⊆ Set.Iic (μ a)

/-- The demonstrative equative (86) holds when the target has the maximal degree of the standard's
degree relative. -/
def demonstrative : Prop := ∃ d, IsGreatest (Set.Iic (μ b)) d ∧ d ≤ μ a

/-- The implicit equative (81) holds when the target and the standard share the evaluative property
of exceeding the standard of comparison `s`. -/
def implicit : Prop := s < μ a ∧ s < μ b

/-- A factor modifier scales the standard's degrees before the sufficientive relates them. -/
def sufficientiveFactor (f : D → D) : Prop := f '' Set.Iic (μ b) ⊆ Set.Iic (μ a)

theorem sufficientive_iff : sufficientive μ a b ↔ μ b ≤ μ a := Set.Iic_subset_Iic

theorem demonstrative_iff : demonstrative μ a b ↔ μ b ≤ μ a :=
  ⟨fun ⟨_, hd, h⟩ ↦ (hd.unique isGreatest_Iic) ▸ h, fun h ↦ ⟨μ b, isGreatest_Iic, h⟩⟩

theorem sufficientiveFactor_iff {f : D → D} (hf : Monotone f) :
    sufficientiveFactor μ a b f ↔ f (μ b) ≤ μ a :=
  ⟨fun h ↦ h ⟨μ b, le_rfl, rfl⟩, fun h _ ⟨_, hd, hdf⟩ ↦ hdf ▸ (hf hd).trans h⟩

theorem sufficientive_of_lt (h : μ b < μ a) : sufficientive μ a b :=
  (sufficientive_iff μ a b).mpr h.le

theorem demonstrative_of_lt (h : μ b < μ a) : demonstrative μ a b :=
  (demonstrative_iff μ a b).mpr h.le

theorem implicit_of_lt (hb : s < μ b) (h : μ b < μ a) : implicit μ s a b := ⟨hb.trans h, hb⟩

theorem not_predicative_of_lt (h : μ b < μ a) : ¬ predicative μ a b := h.ne'

theorem implicit_evaluative (h : implicit μ s a b) : s < μ a := h.1

theorem nonevaluative (hab : μ a = μ b) (hs : μ a ≤ s) :
    predicative μ a b ∧ sufficientive μ a b ∧ demonstrative μ a b ∧ ¬ implicit μ s a b :=
  ⟨hab, (sufficientive_iff μ a b).mpr hab.ge, (demonstrative_iff μ a b).mpr hab.ge,
    fun h ↦ absurd h.1 (not_lt.mpr hs)⟩

/-! ### The chapter's examples -/

/-- The strategies by their `paperFeatures` labels. -/
def Strategy.labels : List (String × Strategy) :=
  [("smOnly", .smOnly), ("demonstrative", .demonstrative), ("sufficientive", .sufficientive),
   ("predicateMain", .predicateMain), ("predicateAdverbial", .predicateAdverbial),
   ("conjoined", .conjoined), ("caseMarked", .caseMarked), ("dedicated", .dedicated)]

/-- The diagnostics by their `paperFeatures` labels. -/
def Diagnostic.labels : List (String × Diagnostic) :=
  [("weak", .weak), ("evaluativity", .evaluativity), ("factor", .factor)]

/-- An example records its strategy, the diagnostic it applies if any, and the judgment. -/
structure Row where
  strategy : Strategy
  diagnostic : Option Diagnostic
  judgment : Judgment

/-- A datum read into its row. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let s ← e.parse? "strategy" Strategy.labels
  let d ← match e.feature? "diagnostic" with
    | none => some none
    | some v => (Diagnostic.labels.lookup v).map some
  pure ⟨s, d, e.judgment⟩

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by decide

/-- The chapter's examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

/-- A diagnostic sentence is acceptable exactly when Figure 3 expects it of the strategy's
class. -/
theorem judgment_iff_expected :
    ∀ d ∈ data, ∀ c : Class, d.strategy.class? = some c → ∀ x : Diagnostic, d.diagnostic = some x →
      (d.judgment = .acceptable ↔ c.Expects x) := by
  decide

-- Figure 3
theorem class_attested : ∀ c : Class, ∃ d ∈ data, d.strategy.class? = some c := by
  decide

end Rett2020b
