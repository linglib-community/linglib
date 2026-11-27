module

public import Linglib.Data.Examples.Pollock1989
public import Mathlib.Order.Basic
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Pollock (1989): Verb Movement, Universal Grammar, and the Structure of IP

This file formalizes [pollock-1989]'s account of where French and English verbs stand relative to
negation, adverbs, floating quantifiers and the subject. A verb moves head to head, from VP to
Agr and from Agr to T, and a head that is opaque to θ-role assignment admits only a verb with no
θ-roles to assign, an auxiliary. English Agr is opaque and French Agr is not; nonfinite T is opaque
in both languages.

`Reaches` gives the heights a verb can reach. A lexical verb moves at all exactly in French
(`lexical_reaches_agr_iff`), and *do*-support arises exactly in English finite clauses with a
lexical verb (`needsDo_iff`). Each row of the paradigm is excluded exactly when no admissible
height puts the verb where the row puts it (`paradigm`).

## Implementation notes

The θ-theoretic mechanism is represented by its effect, which head hosts which verb, not by
θ-grids and chains; the ban on vacuous quantification likewise by the obligatoriness of the
highest reachable position in finite clauses. Marginal rows are counted as admitted, as the
paper treats their degradation as stylistic. The structure of TP with *do*, imperatives,
gerunds, and the ECP account of why *not* alone blocks affix lowering are not formalized.

## References

* [pollock-1989]
-/

@[expose] public section

namespace Pollock1989

open Examples

/-! ### Heads, verbs, and reachability -/

/-- A verb occupies its position in VP, Agr after short movement, or T after long movement. -/
inductive Height where
  | vp
  | agr
  | tense
  deriving DecidableEq, Repr, Fintype

/-- Height as the number of heads climbed. -/
def Height.rank : Height → ℕ
  | .vp => 0
  | .agr => 1
  | .tense => 2

instance : LinearOrder Height := LinearOrder.lift' Height.rank (by decide)

/-- A verb with θ-roles to assign, or an auxiliary with none. -/
inductive Verb where
  | lexical
  | auxiliary
  deriving DecidableEq, Repr, Fintype

/-- The two languages compared. -/
inductive Language where
  | french
  | english
  deriving DecidableEq, Repr, Fintype

/-- A clause type is a language with the finiteness of its T. -/
structure Clause where
  language : Language
  finite : Bool
  deriving DecidableEq, Repr

/-- English Agr is too poor morphologically to transmit θ-roles. -/
def Clause.AgrOpaque (c : Clause) : Prop := c.language = .english

/-- Nonfinite T is opaque to θ-role assignment in both languages. -/
def Clause.TenseOpaque (c : Clause) : Prop := c.finite = false

/-- A head hosts a verb unless it is opaque and the verb has θ-roles to assign. -/
def Hosts (isOpaque : Prop) (v : Verb) : Prop := ¬ isOpaque ∨ v = .auxiliary

/-- A verb reaches the heights of a clause head by head, Agr if Agr hosts it and T if moreover T
hosts it. -/
def Reaches (c : Clause) (v : Verb) : Height → Prop
  | .vp => True
  | .agr => Hosts c.AgrOpaque v
  | .tense => Hosts c.AgrOpaque v ∧ Hosts c.TenseOpaque v

instance (c : Clause) (v : Verb) : DecidablePred (Reaches c v) := fun h ↦ by
  cases h <;> unfold Reaches Hosts Clause.AgrOpaque Clause.TenseOpaque <;> infer_instance

theorem reaches_tense_imp_agr {c : Clause} {v : Verb} (h : Reaches c v .tense) :
    Reaches c v .agr :=
  h.1

theorem reaches_of_le {c : Clause} {v : Verb} {h h' : Height} (hle : h' ≤ h)
    (hr : Reaches c v h) : Reaches c v h' := by
  cases h <;> cases h' <;>
    first | exact hr | exact trivial | exact hr.1 | exact absurd hle (by decide)

theorem auxiliary_reaches_tense (c : Clause) : Reaches c .auxiliary .tense :=
  ⟨Or.inr rfl, Or.inr rfl⟩

theorem lexical_not_reaches_nonfinite_tense (l : Language) :
    ¬ Reaches ⟨l, false⟩ .lexical .tense :=
  fun h ↦ h.2.elim (· rfl) (nomatch ·)

theorem lexical_reaches_agr_iff (c : Clause) : Reaches c .lexical .agr ↔ c.language = .french := by
  cases c with
  | mk l f => cases l <;> cases f <;> decide

/-! ### Finiteness and do-support -/

/-- The highest position a verb reaches. -/
def top (c : Clause) (v : Verb) : Height :=
  if Reaches c v .tense then .tense else if Reaches c v .agr then .agr else .vp

/-- A verb may surface only in its highest position in a finite clause, where T is an operator
that must bind the verb's trace, and in any position it reaches in a nonfinite clause. -/
def Admits (c : Clause) (v : Verb) (h : Height) : Prop :=
  if c.finite then h = top c v else Reaches c v h

instance (c : Clause) (v : Verb) (h : Height) : Decidable (Admits c v h) := by
  unfold Admits; infer_instance

/-- The tense affix must lower onto a verb that cannot rise at all, and *do* supports it when
negation blocks the lowering. -/
def NeedsDo (c : Clause) (v : Verb) : Prop := c.finite = true ∧ top c v = .vp

instance (c : Clause) (v : Verb) : Decidable (NeedsDo c v) := by unfold NeedsDo; infer_instance

theorem needsDo_iff (c : Clause) (v : Verb) :
    NeedsDo c v ↔ c = ⟨.english, true⟩ ∧ v = .lexical := by
  cases c with
  | mk l f => cases l <;> cases f <;> cases v <;> decide

/-! ### The paradigm -/

/-- The four diagnostics of the verb's position. -/
inductive Diagnostic where
  | negation
  | adverb
  | floatingQ
  | inversion
  deriving DecidableEq, Repr, Fintype

/-- A verb precedes negation and the inverted subject from T, and an adverb or floating
quantifier in the VP-initial position from Agr or T. -/
def precedes (h : Height) : Diagnostic → Bool
  | .negation | .inversion => h = .tense
  | .adverb | .floatingQ => h ≠ .vp

theorem precedes_adverb_floatingQ (h : Height) :
    precedes h .adverb = precedes h .floatingQ ∧ precedes h .negation = precedes h .inversion := by
  cases h <;> decide

/-- A row's clause type, verb, diagnostic, and attested order, read from its features. -/
def interpret (r : Datum) : Option (Clause × Verb × Diagnostic × Bool) := do
  let language ← r.byLanguage [(.french, Language.french), (.english, Language.english)]
  let finite ← match r.feature? "finite" with
    | some "yes" => some true
    | some "no" => some false
    | _ => none
  let verb ← match r.feature? "verb" with
    | some "lexical" => some Verb.lexical
    | some "auxiliary" => some Verb.auxiliary
    | _ => none
  let diagnostic ← match r.feature? "diagnostic" with
    | some "negation" => some Diagnostic.negation
    | some "adverb" => some Diagnostic.adverb
    | some "floatingQ" => some Diagnostic.floatingQ
    | some "inversion" => some Diagnostic.inversion
    | _ => none
  let order ← match r.feature? "verbPrecedes" with
    | some "true" => some true
    | some "false" => some false
    | _ => none
  pure (⟨language, finite⟩, verb, diagnostic, order)

/-- A row is predicted when it is excluded exactly where no admitted height puts the verb on the
attested side of the diagnostic element. -/
def Predicted (r : Datum) : Prop :=
  match interpret r with
  | some (c, v, d, b) =>
    r.judgment = .acceptable ∨ r.judgment = .marginal ↔ ∃ h, Admits c v h ∧ precedes h d = b
  | none => False

instance (r : Datum) : Decidable (Predicted r) := by
  unfold Predicted; split <;> infer_instance

/-- Every row of the paradigm (2) to (39) is predicted. -/
theorem paradigm : ∀ r ∈ Examples.all, Predicted r := by
  decide

end Pollock1989
