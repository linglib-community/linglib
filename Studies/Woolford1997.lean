module

public import Linglib.Data.Examples.Woolford1997
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Basic

/-!
# Woolford (1997): Four-Way Case Systems: Ergative, Nominative, Objective and Accusative

This file formalizes [woolford-1997]'s account of the Nez Perce case system, in which a
transitive clause is nominative–accusative or ergative–objective and a ditransitive adds a
second object case. The core inventory has three structural cases, nominative and objective
checked in the specifiers of Agr-S and Agr-O and accusative assigned by the verb inside VP, and
the lexical cases ergative and dative, assigned with a θ-role (`WCase`). Agreement is checked
in the specifier of an Agr head, so nominative and ergative subjects both trigger subject
agreement while only objective objects trigger object agreement (`WCase.position`). A verb
assigns at most as many accusatives as it has arguments minus its lexical cases minus one, the
Max. Acc. formula (`Frame.maxAcc`), which subsumes Burzio's generalization and the
generalization that a lexically cased subject denies accusative to its highest object. An
object denied accusative moves to Spec Agr-O for objective case; there is one such position,
and economy sends the thematically highest caseless object there (`Frame.pattern`). The four
attested ditransitive patterns and the eight prohibited ones follow (`patterns_22A`,
`patterns_22B`); the strong reading of the generalization, on which a lexical subject denies
accusative to every object, leaves the ergative double-object clause underivable
(`strong_underivable`); and the differences between Nez Perce, Thangu and Kalkatungu reduce to
whether ergative and dative are assigned optionally or obligatorily (`Params.patterns`).

## Implementation notes

Accusative assignment is obligatory in Nez Perce, so a nominative subject never co-occurs
with an objective object; the paper attributes nominative–objective patterns elsewhere to
languages whose verbs assign accusative optionally or not at all, a parameter not modelled
here. Dative is placed on goals only, as in the paper's ditransitive frames.

## References

* [woolford-1997]
* [burzio-1986]
-/

@[expose] public section

namespace Woolford1997

/-! ### The case inventory and agreement -/

/-- The core cases: structural nominative, objective and accusative, and lexical ergative
and dative. -/
inductive WCase where
  | nom
  | obj
  | acc
  | erg
  | dat
  deriving DecidableEq, Repr, Fintype

/-- The lexical cases, assigned together with a θ-role. -/
inductive Lexical where
  | erg
  | dat
  deriving DecidableEq, Repr, Fintype

def Lexical.toCase : Lexical → WCase
  | .erg => .erg
  | .dat => .dat

/-- Where an argument sits at LF: the specifier of Agr-S, the specifier of Agr-O, or inside
VP. -/
inductive Position where
  | specAgrS
  | specAgrO
  | inVP
  deriving DecidableEq, Repr

/-- Nominative and ergative subjects raise to Spec Agr-S, objective objects to Spec Agr-O, and
accusative and dative objects stay inside VP. -/
def WCase.position : WCase → Position
  | .nom | .erg => .specAgrS
  | .obj => .specAgrO
  | .acc | .dat => .inVP

/-- Subject agreement is checked in Spec Agr-S. -/
def WCase.TriggersSubjectAgreement (c : WCase) : Prop := c.position = .specAgrS

/-- Object agreement is checked in Spec Agr-O. -/
def WCase.TriggersObjectAgreement (c : WCase) : Prop := c.position = .specAgrO

instance : DecidablePred WCase.TriggersSubjectAgreement :=
  λ _ => inferInstanceAs (Decidable (_ = _))

instance : DecidablePred WCase.TriggersObjectAgreement :=
  λ _ => inferInstanceAs (Decidable (_ = _))

theorem agreement_pattern :
    WCase.erg.TriggersSubjectAgreement ∧ WCase.nom.TriggersSubjectAgreement ∧
      WCase.obj.TriggersObjectAgreement ∧ ¬ WCase.acc.TriggersObjectAgreement := by
  decide

/-! ### The Max. Acc. formula and structural case -/

/-- A clause's arguments with their lexical cases: the subject, then the objects in order
of thematic prominence. -/
structure Frame where
  subject : Option Lexical
  objects : List (Option Lexical)
  deriving DecidableEq, Repr

namespace Frame

variable (f : Frame)

/-- The number of arguments with lexical case. -/
def lexicalCount : ℕ := (f.subject :: f.objects).countP Option.isSome

/-- The Max. Acc. formula: the verb assigns at most as many structural accusatives as it has
arguments minus its lexical cases minus one. -/
def maxAcc : ℕ := (f.objects.length + 1) - f.lexicalCount - 1

/-- The objects without lexical case. -/
def caseless : ℕ := f.objects.countP Option.isNone

/-- The caseless objects denied accusative, which must find case in Spec Agr-O. -/
def denied : ℕ := f.caseless - f.maxAcc

/-- Structural case on the objects: `k` caseless objects, the thematically highest, get
objective in Spec Agr-O, the rest accusative inside VP. -/
def assignObjects : ℕ → List (Option Lexical) → List WCase
  | _, [] => []
  | k, some l :: rest => l.toCase :: assignObjects k rest
  | 0, none :: rest => .acc :: assignObjects 0 rest
  | k + 1, none :: rest => .obj :: assignObjects k rest

/-- The case pattern of a clause: a caseless subject is nominative, and the objects get
structural case, provided at most one object is denied accusative, there being one Spec
Agr-O. -/
def pattern : Option (List WCase) :=
  if f.denied ≤ 1 then
    some ((f.subject.map Lexical.toCase).getD .nom :: assignObjects f.denied f.objects)
  else none

/-- Under the strong reading of the generalization a lexical subject denies accusative to
every object. -/
def deniedStrong : ℕ := if f.subject.isSome then f.caseless else f.denied

/-- The pattern under the strong reading. -/
def patternStrong : Option (List WCase) :=
  if f.deniedStrong ≤ 1 then
    some ((f.subject.map Lexical.toCase).getD .nom :: assignObjects f.deniedStrong f.objects)
  else none

theorem maxAcc_eq : f.maxAcc = f.objects.length - f.lexicalCount := by
  unfold maxAcc; omega

theorem maxAcc_intransitive (s : Option Lexical) : (Frame.mk s []).maxAcc = 0 := by
  cases s <;> rfl

theorem maxAcc_lexical_subject (l : Lexical) (o : Option Lexical) :
    (Frame.mk (some l) [o]).maxAcc = 0 := by
  cases o <;> rfl

end Frame

/-! ### Nez Perce patterns -/

theorem patterns_transitive :
    (Frame.mk none [none]).pattern = some [.nom, .acc] ∧
      (Frame.mk (some .erg) [none]).pattern = some [.erg, .obj] := by
  decide

theorem patterns_transitive_prohibited (s o : Option Lexical) :
    (Frame.mk s [o]).pattern ≠ some [.nom, .obj] ∧
      (Frame.mk s [o]).pattern ≠ some [.erg, .acc] := by
  revert s o; decide

theorem patterns_22A :
    (Frame.mk none [none, none]).pattern = some [.nom, .acc, .acc] ∧
      (Frame.mk none [some .dat, none]).pattern = some [.nom, .dat, .acc] ∧
      (Frame.mk (some .erg) [none, none]).pattern = some [.erg, .obj, .acc] ∧
      (Frame.mk (some .erg) [some .dat, none]).pattern = some [.erg, .dat, .obj] := by
  decide

theorem patterns_22B (s g t : Option Lexical) :
    (Frame.mk s [g, t]).pattern ∉ ([[.nom, .obj, .obj], [.nom, .obj, .acc], [.nom, .acc, .obj],
      [.nom, .dat, .obj], [.erg, .acc, .acc], [.erg, .acc, .obj], [.erg, .obj, .obj],
      [.erg, .dat, .acc]] : List (List WCase)).map some := by
  revert s g t; decide

theorem strong_underivable :
    (Frame.mk (some .erg) [none, none]).patternStrong = none ∧
      (Frame.mk (some .erg) [none, none]).pattern = some [.erg, .obj, .acc] := by
  decide

/-! ### Typological variation -/

/-- Whether a verb assigns a lexical case obligatorily or optionally. -/
inductive Assignment where
  | obligatory
  | optional
  deriving DecidableEq, Repr

/-- The lexical markings a setting allows on a slot. -/
def Assignment.options (l : Lexical) : Assignment → List (Option Lexical)
  | .obligatory => [some l]
  | .optional => [none, some l]

/-- A language's settings for ergative on transitive subjects and dative on goals. -/
structure Params where
  ergative : Assignment
  dative : Assignment
  deriving DecidableEq, Repr

namespace Params

variable (P : Params)

/-- The intransitive, transitive and ditransitive frames the settings allow. -/
def frames : List Frame :=
  ⟨none, []⟩ :: (P.ergative.options .erg).map (⟨·, [none]⟩) ++
    (P.ergative.options .erg).flatMap λ s => (P.dative.options .dat).map (⟨s, [·, none]⟩)

/-- The derivable case patterns. -/
def patterns : List (List WCase) := P.frames.filterMap Frame.pattern

end Params

/-- Nez Perce assigns both lexical cases optionally. -/
def nezPerce : Params := ⟨.optional, .optional⟩

/-- Thangu assigns both obligatorily. -/
def thangu : Params := ⟨.obligatory, .obligatory⟩

/-- Kalkatungu assigns ergative obligatorily and dative optionally. -/
def kalkatungu : Params := ⟨.obligatory, .optional⟩

theorem nezPerce_patterns :
    nezPerce.patterns = [[.nom], [.nom, .acc], [.erg, .obj], [.nom, .acc, .acc],
      [.nom, .dat, .acc], [.erg, .obj, .acc], [.erg, .dat, .obj]] := by
  decide

theorem thangu_no_accusative : ∀ p ∈ thangu.patterns, WCase.acc ∉ p := by decide

theorem kalkatungu_patterns :
    kalkatungu.patterns = [[.nom], [.erg, .obj], [.erg, .obj, .acc], [.erg, .dat, .obj]] := by
  decide

end Woolford1997
