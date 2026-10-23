module

public import Linglib.Fragments.English.Pronouns
public import Linglib.Data.Examples.DechaineWiltschko2002

/-!
# Déchaine and Wiltschko (2002): Decomposing Pronouns

This file formalizes the categorial typology of proforms of Déchaine and Wiltschko. The
notion "pronoun" is not a primitive: a proform is a DP, a φP or an NP by the layers it projects,
and its category fixes its distribution and its binding-theoretic status, table (24). A DP is an
argument and an R-expression under Condition C, a φP an argument or a predicate and a variable
under Condition B, and an NP a predicate and undefined for binding theory, its behaviour
following from its inherent semantics as a constant. Halkomelem independent pronouns are DPs,
Shuswap ones φPs and Japanese *kare* an NP. In English, *one* is an NP, first and second person
pronouns are DPs, which is why they precede nouns, *we linguists*, and third person pronouns
are φPs, *\*they linguists*, the dialect that says *them linguists* having reanalyzed *them* as
the D-morpheme *th-* over the clitic φP *'em*. The English categories are derived from the
Fragment's person features, and the determiner and bound-variable data are rows.

## References

* [dechaine-wiltschko-2002]
-/

@[expose] public section

namespace DechaineWiltschko2002


/-! ### The categories -/

/-- The layers a proform may project. -/
inductive Layer where
  | D
  | phi
  | N
  deriving DecidableEq, Repr

/-- The three categories, by size: a full DP over a φP over an NP, a φP over an NP, or a bare
NP, (1). -/
inductive Category where
  | proDP
  | prophiP
  | proNP
  deriving DecidableEq, Repr

/-- The layers of a category, from the top down. -/
def Category.layers : Category → List Layer
  | .proDP => [.D, .phi, .N]
  | .prophiP => [.phi, .N]
  | .proNP => [.N]

theorem layers_suffix :
    Category.proNP.layers <:+ Category.prophiP.layers ∧
      Category.prophiP.layers <:+ Category.proDP.layers :=
  ⟨⟨[.phi], rfl⟩, ⟨[.D], rfl⟩⟩

/-- The top layer of a category. -/
def Category.top : Category → Layer
  | .proDP => .D
  | .prophiP => .phi
  | .proNP => .N

/-- Binding-theoretic status: an R-expression under Condition C, a variable under Condition B,
or undefined, the behaviour following from inherent semantics. -/
inductive BindingStatus where
  | rExpression
  | variable
  | undefined
  deriving DecidableEq, Repr

/-- Binding status is defined by the top layer, (24): R-expressions are DPs, variables are
φPs, and NPs, constants, are undefined for binding theory. -/
def Category.bindingStatus (c : Category) : BindingStatus :=
  match c.top with
  | .D => .rExpression
  | .phi => .variable
  | .N => .undefined

/-- The positions a nominal fills. -/
inductive Position where
  | argument
  | predicate
  deriving DecidableEq, Repr

/-- Distribution, (25): a DP is an argument, an NP a predicate, and a φP is type flexible. -/
def Category.CanBe : Category → Position → Prop
  | .proDP, .argument => True
  | .proDP, .predicate => False
  | .proNP, .predicate => True
  | .proNP, .argument => False
  | .prophiP, _ => True

/-- (25c) and (25d): not every argument is a DP, and not every nominal predicate an NP. -/
theorem canBe_argument_iff (c : Category) : c.CanBe .argument ↔ c ≠ .proNP := by
  cases c <;> simp [Category.CanBe]

theorem canBe_predicate_iff (c : Category) : c.CanBe .predicate ↔ c ≠ .proDP := by
  cases c <;> simp [Category.CanBe]

/-! ### English (§3) -/

/-- The category of an English personal pronoun, from its person: first and second person
pronouns are DPs and third person pronouns φPs, (33). -/
def english (p : PersonalPronoun) : Category :=
  if p.person = some .third then .prophiP else .proDP

/-- Dialect B, (34) and (37c): the accusative third person plural *them* is reanalyzed as the
D-morpheme *th-* over the clitic φP *'em*, a DP. -/
def dialectB (p : PersonalPronoun) : Category :=
  if p.person = some .third ∧ p.number = some .plural ∧ .acc ∈ p.cases then .proDP
  else english p

/-! ### The rows -/

/-- The category of a row's proform: the English pronouns' from the Fragment, dialect B's
*them* reanalyzed, and *one* and Japanese *kare* the NPs of sections 3.1 and 2.3. -/
def categoryOf (e : Datum) : Option Category :=
  match e.feature? "pronoun", e.feature? "dialect" with
  | some "we", _ => some (english English.Pronouns.we)
  | some "us", _ => some (english English.Pronouns.us)
  | some "you", _ => some (english English.Pronouns.you_pl)
  | some "they", _ => some (english English.Pronouns.they)
  | some "them", some "B" => some (dialectB English.Pronouns.them)
  | some "them", _ => some (english English.Pronouns.them)
  | some "he", _ => some (english English.Pronouns.he)
  | some "me", _ => some (english English.Pronouns.me)
  | some "one", _ => some .proNP
  | some "kare", _ => some .proNP
  | _, _ => none

theorem determiner_rows :
    ∀ e ∈ Examples.all, e.feature? "test" = some "precedesNoun" →
      ∀ c ∈ categoryOf e, (e.judgment = .acceptable ↔ c = .proDP) := by
  decide

/-- The judgment of a row's bound-variable construal: under VP-ellipsis its sloppy reading's,
otherwise the row's own, whose indices mark the bound construal. -/
def boundJudgment (e : Datum) : Judgment := (e.readings.lookup "sloppy").getD e.judgment

/-- A proform is construed as a bound variable exactly when its category makes it a variable ((40),
(30), (22)). -/
theorem bound_variable_rows :
    ∀ e ∈ Examples.all, e.feature? "test" = some "boundVariable" →
      ∀ c ∈ categoryOf e, (boundJudgment e = .acceptable ↔ c.bindingStatus = .variable) := by
  decide

end DechaineWiltschko2002
