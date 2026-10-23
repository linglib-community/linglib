module

public import Linglib.Fragments.Dutch.PolarityItems
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Data.Examples.VanDerWouden1997

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
(`negativeOnly_admits_niet`).

## References

* [vanderwouden-1997]
-/

@[expose] public section

namespace VanDerWouden1997

open PolarityItem Dutch.PolarityItems

/-- The contexts of (184), a positive clause, *weinig* 'few', *geen van* 'none of' and *niet*. -/
inductive Context where
  | positive
  | weinig
  | geenVan
  | niet
  deriving DecidableEq, Repr

/-- A positive clause admits the items that need no licensing, and each operator admits what its
licensing context admits. -/
def Context.Admits : Context → PolarityItem → Prop
  | .positive, e => ¬ (e.IsNPI ∨ e.IsFCI)
  | .weinig, e => LicensingContext.few.licenser.Admits e
  | .geenVan, e => LicensingContext.nobody.licenser.Admits e
  | .niet, e => LicensingContext.negation.licenser.Admits e

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

/-- The context a row's class names. -/
def Context.ofKey : String → Option Context
  | "notMonotoneDecreasing" => some .positive
  | "monotoneDecreasing" => some .weinig
  | "antiAdditive" => some .geenVan
  | "antimorphic" => some .niet
  | _ => none

/-- Every row of (184) is on *ooit*, names its context, and is acceptable exactly when the
context admits *ooit*'s Fragment entry. -/
theorem judgments_predicted :
    ∀ d ∈ Examples.all, d.feature? "item" = some "ooit" ∧
      ∃ c ∈ (d.feature? "context").bind Context.ofKey,
        (d.judgment = .acceptable ↔ c.Admits ooit) := by
  decide +kernel

theorem negativeOnly_admits_niet : Context.niet.Admits { ooit with antiLicensor := none } := by
  decide

end VanDerWouden1997
