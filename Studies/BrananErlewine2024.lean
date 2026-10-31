module

public import Linglib.Data.Examples.BrananErlewine2024
public import Linglib.Syntax.Minimalist.Copy.Chain
public import Linglib.Syntax.Minimalist.Probe.Agree
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Data.Examples.Readers

/-!
# Branan and Erlewine (2024): Ā-probing for the closest DP

An Ā-probe can be restricted to the closest DP: [PROBE:Ā+D] interacts with a goal bearing both
an Ā-feature and [D] but is satisfied by any [D] goal, so it halts on the first DP it meets and
moves it only if that DP bears the Ā-feature. A goal is closest when no other potential goal
c-commands it (8). Relativization of this kind looks subject-only because the subject is usually
the highest DP, but a non-subject moved above a low subject is extractable (10), and so is a DP at
the edge of the highest DP, which that DP does not c-command (11). Turkish relatives with the
subject-relative form and Rejang relatives with *gi* show both exceptions.

## Implementation notes

* A relative clause is a tree with the heads that probe and the clitic pronouns, which
  cliticization hides from [D]-sensitive probes (p. 387). A goal is the occurrence of a D head, read
  at its maximal projection; its features are [D], unless it is a clitic, and [REL] on the relative
  operator.
* Turkish relatives take the subject-relative (SR) form exactly when the probe finds a goal, and
  the nonsubject-relative (NSR) form otherwise (p. 384). A Rejang *gi* relative needs every *gi*
  head to find a goal; *bawo* does not probe.
* Closeness is (8) itself, not the generators-above key of `Probe.Finds`, under which a DP is
  closer than its possessor (`Probe.not_finds_ancestors_of_lt`).
* Clauses are cut down to their DPs and the heads that order them. A Rejang possessor relative
  places the operator at the edge of the possessed DP, one of the two analyses of p. 389, and its
  resumptive pronoun is left out. The agent of a Rejang passive sits below the promoted theme.

## TODO

* Kiribati, Toba Batak, Māori and Arabic (section 4), Haya long-distance relatives (35), Late
  Archaic Chinese ditransitives (37), and Tagalog non-DP fronting (section 5.3).

## References

* [branan-erlewine-2024]
-/

@[expose] public section

namespace BrananErlewine2024

open Minimalist Minimalist.LinearizedSyntacticObject Core.Order

/-! ### The probe -/

/-- The features an Ā-probe for the closest DP reads, the Ā-feature [REL] and [D]. -/
inductive Feature
  | rel | d
  deriving DecidableEq, Repr

/-- [PROBE:REL+D] restricted to the closest DP, interacting with a goal that bears [REL] and [D]
and satisfied by any goal that bears [D] (7). -/
def relD : Probe.Spec Feature := ⟨{{.rel, .d}}, {{.d}}⟩

/-! ### Relative clauses -/

/-- A relative clause: its structure, the heads that probe, and the clitic pronouns. -/
structure Relative where
  /-- The structure. -/
  tree : LinearizedSyntacticObject
  /-- The heads bearing [PROBE:REL+D]. -/
  probes : List LexicalItem.Token
  /-- The clitic pronouns, invisible to [D]-sensitive probes. -/
  clitics : List LexicalItem.Token := []

namespace Relative

variable (r : Relative)

/-- The goals of the probe on the head at `h`, the occurrences of D heads in its complement. -/
def goals (h : TreePath) : List (TreePath × LexicalItem.Token) :=
  (tokenList r.tree.val).filter fun x ↦ x.2.item.cat = .D ∧ complement h ≤ x.1

/-- The features of a goal, [D] unless it is a clitic, and [REL] on the relative operator. -/
def feats (g : TreePath × LexicalItem.Token) : Finset Feature :=
  (if g.2 ∈ r.clitics then ∅ else {.d}) ∪ (if g.2.item.IsWh then {.rel} else ∅)

/-- The probe on the goals of the relative clause. -/
def probe : Probe (TreePath × LexicalItem.Token) := relD.toProbe r.feats

/-- A goal of the probe on the head at `h` is closest when no other potential goal, a goal that
satisfies the probe, c-commands it (8). -/
def Closest (h : TreePath) (g : TreePath × LexicalItem.Token) : Prop :=
  g ∈ r.goals h ∧ r.probe.sat g ∧ ∀ g' ∈ r.goals h, r.probe.sat g' → g' ≠ g →
    ¬ r.tree.val.CCommands (projectionAt .raising r.tree g'.1) (projectionAt .raising r.tree g.1)

instance (h : TreePath) : DecidablePred (r.Closest h) := fun _ ↦ by
  unfold Closest; infer_instance

/-- The probe on the head at `h` attracts a closest goal it interacts with. -/
def Attracts (h : TreePath) (g : TreePath × LexicalItem.Token) : Prop :=
  r.Closest h g ∧ r.probe.int g

instance (h : TreePath) : DecidablePred (r.Attracts h) := fun _ ↦ by
  unfold Attracts; infer_instance

/-- Every probing head attracts a goal. -/
def Converges : Prop :=
  ∀ h ∈ occurrencesWith r.tree (· ∈ r.probes), ∃ g ∈ r.goals h, r.Attracts h g

instance : Decidable r.Converges := by unfold Converges; infer_instance

end Relative

/-! ### Turkish (12)–(20) -/

namespace Turkish

def relC : LexicalItem.Token := ⟨.of .C [.T], 0⟩
def tense : LexicalItem.Token := ⟨.of .T [.v], 1⟩
def littleV : LexicalItem.Token := ⟨.of .v [.V], 2⟩
/-- The relative operator. -/
def op : LexicalItem.Token := ⟨.of .D [] "" (features := .single .wh true), 3⟩
/-- The possessive D head. -/
def poss : LexicalItem.Token := ⟨.of .D [.N], 4⟩
def sting : LexicalItem.Token := ⟨.of .V [.D] "sok", 5⟩
def girl : LexicalItem.Token := ⟨.of .D [] "kız", 6⟩
def bee : LexicalItem.Token := ⟨.of .D [] "arı", 7⟩
def go : LexicalItem.Token := ⟨.of .V [.D] "git", 8⟩
def school : LexicalItem.Token := ⟨.of .D [] "mektep", 9⟩
def son : LexicalItem.Token := ⟨.of .N [] "oğul", 10⟩
def daughter : LexicalItem.Token := ⟨.of .N [] "kız", 11⟩
def leg : LexicalItem.Token := ⟨.of .N [] "bacak", 12⟩
def explode : LexicalItem.Token := ⟨.of .V [] "patla", 13⟩
def bomb : LexicalItem.Token := ⟨.of .D [] "bomba", 14⟩
def fall : LexicalItem.Token := ⟨.of .V [] "yağ", 15⟩
def snow : LexicalItem.Token := ⟨.of .D [] "kar", 16⟩

/-- A relative clause headed by the relative complementizer. -/
def rel (t : LinearizedSyntacticObject) : Relative := ⟨relC * t, [relC], []⟩

/-- The form a sentence takes is SR exactly when the probe finds a goal (p. 384). -/
def Derived (d : Datum) (r : Relative) : Prop := d.feature? "form" = some "SR" ↔ r.Converges

instance (d : Datum) (r : Relative) : Decidable (Derived d r) := by
  unfold Derived; infer_instance

/-- (12a): the operator is the subject. -/
def subject : Relative := rel (op * (tense * (littleV * (sting * girl))))

/-- (12b): the operator is the object, below a high subject. -/
def objectHigh : Relative := rel (bee * (tense * (littleV * (sting * op))))

/-- (13a): the object operator has moved above a low indefinite subject. -/
def objectLow : Relative := rel (op * (tense * (bee * (littleV * (sting * op)))))

/-- (14): the temporal operator is above a low indefinite subject. -/
def temporal (subj verb : LexicalItem.Token) : Relative :=
  rel (op * (tense * (subj * (littleV * verb))))

/-- The possessed DP with the operator at its edge. -/
def possessed (n : LexicalItem.Token) : LinearizedSyntacticObject := op * (poss * n)

/-- (16): the operator is at the edge of the subject. -/
def possessorSubject : Relative :=
  rel (possessed son * (tense * (littleV * (go * school))))

/-- (18): the object, with the operator at its edge, has moved above a low indefinite subject. -/
def possessorObjectLow : Relative :=
  rel (possessed daughter * (tense * (bee * (littleV * (sting * possessed daughter)))))

/-- (20): the operator is at the edge of the object, below a high subject. -/
def possessorObjectHigh : Relative :=
  rel (bee * (tense * (littleV * (sting * possessed leg))))

-- (12)
theorem ex12 : (Examples.ex12a.judgment = .acceptable ↔ Derived Examples.ex12a subject) ∧
    (Examples.ex12b.judgment = .acceptable ↔ Derived Examples.ex12b objectHigh) := by
  decide +kernel

-- (13), (14), (10)
theorem ex13_ex14 :
    (Examples.ex13a.judgment = .acceptable ↔ Derived Examples.ex13a objectLow) ∧
    (Examples.ex14a.judgment = .acceptable ↔ Derived Examples.ex14a (temporal bomb explode)) ∧
    (Examples.ex14b.judgment = .acceptable ↔ Derived Examples.ex14b (temporal snow fall)) := by
  decide +kernel

-- (16), (11)
theorem ex16 :
    (Examples.ex16a.judgment = .acceptable ↔ Derived Examples.ex16a possessorSubject) ∧
    (Examples.ex16b.judgment = .acceptable ↔ Derived Examples.ex16b possessorSubject) := by
  decide +kernel

-- (17)
theorem ex17 : ∀ g ∈ possessorSubject.goals ⟨[0]⟩, g.2 = op ∨ g.2 = poss →
    possessorSubject.Closest ⟨[0]⟩ g := by
  decide +kernel

-- (18), (20)
theorem ex18_ex20 :
    (Examples.ex18.judgment = .acceptable ↔ Derived Examples.ex18 possessorObjectLow) ∧
    (Examples.ex18_nsr.judgment = .acceptable ↔ Derived Examples.ex18_nsr possessorObjectLow) ∧
    (Examples.ex20a.judgment = .acceptable ↔ Derived Examples.ex20a possessorObjectHigh) ∧
    (Examples.ex20b.judgment = .acceptable ↔ Derived Examples.ex20b possessorObjectHigh) := by
  decide +kernel

end Turkish

/-! ### Rejang (21)–(30) -/

namespace Rejang

def gi : LexicalItem.Token := ⟨.of .C [.T] "gi", 20⟩
/-- An embedded *gi*. -/
def gi₂ : LexicalItem.Token := ⟨.of .C [.T] "gi", 21⟩
def bawo : LexicalItem.Token := ⟨.of .C [.T] "bawo", 22⟩
def tense : LexicalItem.Token := ⟨.of .T [.v], 23⟩
def aux : LexicalItem.Token := ⟨.of .T [.v] "mulaé", 24⟩
def littleV : LexicalItem.Token := ⟨.of .v [.V], 25⟩
def op : LexicalItem.Token := ⟨.of .D [] "" (features := .single .wh true), 26⟩
def poss : LexicalItem.Token := ⟨.of .D [.N], 27⟩
def police : LexicalItem.Token := ⟨.of .D [] "pelisi", 28⟩
def arrest : LexicalItem.Token := ⟨.of .V [.D] "akep", 29⟩
def ko : LexicalItem.Token := ⟨.of .D [] "ko", 30⟩
/-- A second *ko*. -/
def ko₂ : LexicalItem.Token := ⟨.of .D [] "ko", 31⟩
def ku : LexicalItem.Token := ⟨.of .D [] "ku", 32⟩
def keme : LexicalItem.Token := ⟨.of .D [] "Keme", 33⟩
def buy : LexicalItem.Token := ⟨.of .V [.D] "okoa", 34⟩
def watch : LexicalItem.Token := ⟨.of .V [.D] "oton", 35⟩
def say : LexicalItem.Token := ⟨.of .V [.C] "adea'", 36⟩
def alui : LexicalItem.Token := ⟨.of .D [] "Alui", 37⟩
/-- The resumptive pronoun. -/
def si : LexicalItem.Token := ⟨.of .D [] "si", 38⟩
def come : LexicalItem.Token := ⟨.of .V [] "teko", 39⟩
def visit : LexicalItem.Token := ⟨.of .V [.D] "anang", 40⟩
def headman : LexicalItem.Token := ⟨.of .D [] "Pak Lu'ea'", 41⟩
def nose : LexicalItem.Token := ⟨.of .N [] "nyung", 42⟩
def long : LexicalItem.Token := ⟨.of .V [] "panjang", 43⟩
def see : LexicalItem.Token := ⟨.of .V [.D] "lea'", 44⟩
def wife : LexicalItem.Token := ⟨.of .N [] "ngenyan", 45⟩
def lengthen : LexicalItem.Token := ⟨.of .V [.D] "anjang", 46⟩
def age : LexicalItem.Token := ⟨.of .N [] "omor", 47⟩

/-- A relative clause whose *gi* heads probe, with its clitic pronouns. -/
def rel (t : LinearizedSyntacticObject) (clitics : List LexicalItem.Token := []) : Relative :=
  ⟨t, [gi, gi₂], clitics⟩

/-- (21a): the theme of an active verb, below the subject. -/
def activeTheme : Relative := rel (gi * (police * (tense * (littleV * (arrest * op)))))

/-- (21b): the theme promoted by the passive. -/
def passiveTheme : Relative := rel (gi * (op * (tense * (police * (littleV * (arrest * op))))))

/-- (22): the theme of an active verb, below a clitic subject. -/
def cliticSubject : Relative := rel (gi * (ko * (littleV * (buy * op)))) [ko]

/-- (23b): the theme below an auxiliary and a clitic agent. -/
def cliticAgent : Relative := rel (gi * (aux * (ku * (littleV * (watch * op))))) [ku]

/-- (26): the embedded clause, with the operator at its edge, moved to the subject of the passive
of *say*. -/
def clausalSubject (cp : LinearizedSyntacticObject) : Relative :=
  rel (gi * (cp * (tense * (alui * (littleV * (say * cp))))))

/-- (26a): the operator base-generated at the edge of a *bawo* clause, binding a resumptive. -/
def resumptive : LinearizedSyntacticObject := op * (bawo * (si * (tense * (littleV * come))))

/-- (26b): the operator moved to the edge of a *gi* clause from its subject. -/
def gap : LinearizedSyntacticObject := op * (gi₂ * (op * (tense * (littleV * come))))

/-- (28a): the embedded subject, attracted by the embedded *gi* and then across a clitic. -/
def longSubject : Relative :=
  rel (gi * (ku * (littleV * (say * (op * (gi₂ * (op * (tense * (littleV * (visit *
    headman)))))))))) [ku]

/-- (28b): the embedded theme, attracted across two clitics. -/
def longTheme : Relative :=
  rel (gi * (ko * (littleV * (say * (op * (gi₂ * (aux * (ko₂ * (littleV * (watch * op))))))))))
    [ko, ko₂]

/-- (29a): the operator at the edge of the subject. -/
def possessorSubject : Relative :=
  rel (gi * ((op * (poss * nose)) * (tense * (littleV * long))))

/-- (29b): the operator at the edge of the object, below a full subject. -/
def possessorObject : Relative :=
  rel (gi * (alui * (tense * (littleV * (see * (op * (poss * wife)))))))

/-- (30): the operator at the edge of the object, below a clitic subject. -/
def possessorObjectClitic : Relative :=
  rel (gi * (keme * (littleV * (lengthen * (op * (poss * age)))))) [keme]

-- (21), (23)
theorem ex21_ex23 :
    (Examples.ex21a.judgment = .acceptable ↔ activeTheme.Converges) ∧
    (Examples.ex21b.judgment = .acceptable ↔ passiveTheme.Converges) ∧
    (Examples.ex22.judgment = .acceptable ↔ cliticSubject.Converges) ∧
    (Examples.ex23b.judgment = .acceptable ↔ cliticAgent.Converges) := by
  decide +kernel

-- (27), (26), (28)
theorem ex26_ex28 :
    (Examples.ex26a.judgment = .acceptable ↔ (clausalSubject resumptive).Converges) ∧
    (Examples.ex26b.judgment = .acceptable ↔ (clausalSubject gap).Converges) ∧
    (Examples.ex28a.judgment = .acceptable ↔ longSubject.Converges) ∧
    (Examples.ex28b.judgment = .acceptable ↔ longTheme.Converges) := by
  decide +kernel

-- (29), (30), (31)
theorem ex29_ex30 :
    (Examples.ex29a.judgment = .acceptable ↔ possessorSubject.Converges) ∧
    (Examples.ex29b.judgment = .acceptable ↔ possessorObject.Converges) ∧
    (Examples.ex30.judgment = .acceptable ↔ possessorObjectClitic.Converges) := by
  decide +kernel

end Rejang

end BrananErlewine2024
