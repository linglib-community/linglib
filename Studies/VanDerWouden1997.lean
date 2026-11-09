module

public import Linglib.Fragments.Dutch.PolarityItems
public import Linglib.Semantics.PolarityItem.Basic
public import Linglib.Data.Examples.VanDerWouden1997
public import Linglib.Data.Examples.Readers

/-!
# van der Wouden (1997): Negative Contexts: Collocation, Polarity and Multiple Negation

Van der Wouden ranks negative contexts by strength, monotone decreasing, anti-additive and
antimorphic, and classes polarity items by the weakest context that licenses or blocks them. Dutch
*ooit* 'ever' is his bipolar element: a weak negative polarity item, out in a clause that is not
monotone decreasing and fine under *weinig* 'few' and *geen van* 'none of', and a weak positive
polarity item, blocked by the antimorphic negation *niet*. The library's contexts for these
operators have the strengths he assigns them (`context_strengths`). He holds that a verb with
negative properties is anti-additive, none being only monotone decreasing; *deny* bears this out,
but *doubt*, on his own sketch of it as not believing the complement, is only monotone decreasing
(`verb_strengths`). With *ooit*'s Fragment entry every judgment of his (184) is the licensing
theory's (`judgments_predicted`). An entry that were only a negative polarity item, as on the
analysis with two items *ooit*, would be admitted under *niet*, against (184d)
(`negativeOnly_admits_niet`). *Hoeven* 'need', a weak negative polarity item, is out in questions,
conditionals and the restrictor of *alle* 'all', downward-entailing contexts all, so [no class of
item fits his table (235)](##VanDerWouden1997.hoeven_extraRestrictions).

## References

* [vanderwouden-1997]
-/

@[expose] public section

namespace VanDerWouden1997

open PolarityItem Dutch.PolarityItems

/-- The context of a row: a positive clause, or a named licensing context. -/
inductive Context where
  | positive
  | named (c : LicensingContext)
  deriving DecidableEq, Repr

/-- A positive clause admits the items that need no licensing, and a named context what its
licenser admits. -/
def Context.Admits : Context → PolarityItem → Prop
  | .positive, e => ¬ (e.IsNPI ∨ e.IsFCI)
  | .named c, e => c.licenser.Admits e

instance (c : Context) : DecidablePred c.Admits := by
  intro e; cases c <;> dsimp only [Context.Admits] <;> infer_instance

theorem context_strengths :
    LicensingContext.few.licenser.Holds .anti ∧ ¬ LicensingContext.few.licenser.Holds .antiAdd ∧
      LicensingContext.nobody.licenser.Holds .antiAdd ∧
      ¬ LicensingContext.nobody.licenser.Holds .antiAddMult ∧
      LicensingContext.negation.licenser.Holds .antiAddMult :=
  ⟨LicensingContext.holds_few_iff (s := .weak) |>.2 le_rfl,
    fun h ↦ absurd (LicensingContext.holds_few_iff (s := .antiAdditive) |>.1 h) (by decide),
    LicensingContext.holds_nobody_iff (s := .antiAdditive) |>.2 le_rfl,
    fun h ↦ absurd (LicensingContext.holds_nobody_iff (s := .antiMorphic) |>.1 h) (by decide),
    LicensingContext.holds_negation .antiMorphic⟩

theorem verb_strengths :
    LicensingContext.denyVerb.licenser.Holds .antiAdd ∧
      ¬ LicensingContext.denyVerb.licenser.Holds .antiAddMult ∧
      LicensingContext.doubtVerb.licenser.Holds .anti ∧
      ¬ LicensingContext.doubtVerb.licenser.Holds .antiAdd :=
  ⟨LicensingContext.holds_denyVerb_iff (s := .antiAdditive) |>.2 le_rfl,
    fun h ↦ absurd (LicensingContext.holds_denyVerb_iff (s := .antiMorphic) |>.1 h) (by decide),
    LicensingContext.holds_doubtVerb_iff (s := .weak) |>.2 le_rfl,
    fun h ↦ absurd (LicensingContext.holds_doubtVerb_iff (s := .antiAdditive) |>.1 h) (by decide)⟩

/-- The context a row names: for (184) by its strength, *weinig* 'few', *geen van* 'none of' and
*niet*; for *hoeven* by the named context, the restrictor of *geen* having none. -/
def Context.ofKey : String → Option Context
  | "notMonotoneDecreasing" => some .positive
  | "monotoneDecreasing" => some (.named .few)
  | "antiAdditive" => some (.named .nobody)
  | "antimorphic" => some (.named .negation)
  | "universalRestrictor" => some (.named .universalRestrictor)
  | "question" => some (.named .question)
  | "conditionalAntecedent" => some (.named .conditionalAntecedent)
  | "clausalComparative" => some (.named .clausalComparative)
  | "superlative" => some (.named .superlative)
  | "doubtVerb" => some (.named .doubtVerb)
  | "beforeClause" => some (.named .beforeClause)
  | _ => none

/-- Every row of (184) on *ooit* names its context, and is acceptable exactly when the context
admits *ooit*'s Fragment entry. -/
theorem judgments_predicted :
    ∀ d ∈ Examples.all, d.feature? "item" = some "ooit" →
      ∃ c ∈ (d.feature? "context").bind Context.ofKey,
        (d.judgment = .acceptable ↔ c.Admits ooit) := by
  decide +kernel

theorem negativeOnly_admits_niet :
    (Context.named .negation).Admits { ooit with antiLicensor := none } := by
  decide

/-- No class of polarity item is admitted wherever van der Wouden accepts *hoeven* and refused
wherever he stars it: the theory admits *hoeven* in every named context of (228)–(234), questions,
conditionals and the restrictor of *alle* included, so his extra restrictions on it lie outside
the strength classes. -/
theorem hoeven_extraRestrictions :
    (∀ d ∈ Examples.all, d.feature? "item" = some "hoeven" →
      ∀ c ∈ (d.feature? "context").bind Context.ofKey, c.Admits hoeven) ∧
    ∀ (l a : Option Negation.Strength) (fc : Bool),
      ¬ ∀ d ∈ Examples.all, d.feature? "item" = some "hoeven" →
        ∀ c ∈ (d.feature? "context").bind Context.ofKey,
          (d.judgment = .acceptable ↔ c.Admits ⟨"hoeven", l, a, fc, [], []⟩) := by
  decide +kernel

end VanDerWouden1997
