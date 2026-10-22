module

public import Linglib.Semantics.ArgumentStructure.Valency
public import Linglib.Semantics.Composition.Ty
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Data.Wordlist.Coon2019
public import Linglib.Fragments.Mayan.Chuj.Voice
public import Linglib.Data.Examples.Coon2019
public import Mathlib.Tactic.DeriveFintype

/-!
# Coon 2019: building verbs in Chuj

Coon argues from the Chuj verb stem that the root decides whether there is an internal
argument and the functional head v ~ Voice⁰ decides the rest. Roots fall into four classes
that semantic type partly distinguishes, transitive and intransitive roots being event
predicates over an entity, positional roots measure functions and nominal roots properties, and
a verb stem is a root plus one of the heads Ø, -w, -ch and -j, the first doubling as the null
head of intransitive roots, which merge an agent with inherent ergative case, an agent without
it, an implicit agent, or no agent. Since finite Infl⁰ licenses one absolutive
argument, an agent without ergative case takes it, so a transitive root under -w cannot realize
its argument as a full DP and does so as a bare NP composed by Restrict or as an implicit
argument bound by Existential Closure, the suffix -aj being the overt reflex of that binding in
absolutive antipassives and in passives with an implicit agent, while an intransitive root,
whose sole argument is a DP, admits no -w at all. Every stem of a transitive root thus composes
with an internal argument, and a language without the head that merges an agent free of
ergative case, Ch'ol, has no agentive intransitive stems.

## Implementation notes

The roots of the class table (5), of (17) and (20) and of the examples are the forms of
`Data/Wordlist/Coon2019`, each with its class as Coon's analysis, and the class fixes the root's
type, valency and compatibility with the agent-merging head. The heads are Minimalist Voice heads whose parametric semantics supplies two of the three
properties the licensing count reads, an external argument and its implicitness; the third,
inherent ergative case, is the transitive head's own, since the substrate's Case checking is
the accusative of v. The count adopts the Obligatory Case Parameter of footnote 15,
one of the two options the paper leaves open. The class of a root fixes which realizations its
internal slot admits; that an intransitive root's argument is only ever a full DP encodes the
absence of unaccusative subject incorporation, (48), which the paper leaves to typology, and no
implicit option for such roots is attested. The event semantics of §3.2.2 records truth
conditions; the locus of Existential Closure that separates the two antipassives lives in the
-aj predicate. Status suffixes, derived transitives in -ej, word order, stative -an stems, the
inanimate causer of (70a) and the isolated -j form (71) are recorded as data only.

## References

* [J. Coon, *Building verbs in Chuj: Consequences for the nature of roots* (2019)][coon-2019]
* [S. Chung and W. A. Ladusaw, *Restriction and Saturation* (2004)][chung-ladusaw-2004]
* [M. Diesing, *Indefinites* (1992)][diesing-1992]
* [H. Harley, *The 'bundling' hypothesis and the disparate functions of little v*
  (2017)][harley-2017]
* [A. Kratzer, *Severing the external argument from its verb* (1996)][kratzer-1996]
* [H. Davis, *Deep unaccusativity and zero syntax in St'át'imcets* (1997)][davis-1997]
* [R. Henderson, *The roots of measurement* (2017)][henderson-2017]
* [J. M. Maxwell, *Chuj intransitives: Or when can an intransitive verb take an object?*
  (1976)][maxwell-1976]
* [A. Alexiadou, E. Anagnostopoulou and F. Schäfer, *The properties of anticausatives
  crosslinguistically* (2006)][alexiadou-anagnostopoulou-schaefer-2006]
* [J. Wood, *Icelandic Morphosyntax and Argument Structure* (2015)][wood-2015]
-/

@[expose] public section

namespace Coon2019

open Chuj Minimalist.Voice ArgumentStructure
open Wordlist (RootClass)
open scoped Montague

/-! ### Root classes -/

/-- The core-argument positions a root class introduces, in the sense of [coon-2019]'s (2):
transitive and intransitive roots an internal argument, positional and nominal roots none
(39). -/
def Wordlist.RootClass.valency : RootClass → Valency
  | .tv | .itv => {.internal}
  | .pos | .nom => ∅

/-- The semantic type of a root class, (3): transitive and intransitive roots are event
predicates over an internal argument, positional roots measure functions after
[henderson-2017] and nominal roots properties. -/
def Wordlist.RootClass.ty : RootClass → Montague.Ty
  | .tv | .itv => .e ⇒ .v ⇒ .t
  | .pos => .e ⇒ .v ⇒ .d
  | .nom => .e ⇒ .t

/-- The root class combines with the transitive-forming v ~ Voice head that merges an agent,
the coordinate separating √TV from the unaccusative √ITV, §3.3. -/
def Wordlist.RootClass.LicensesTransitiveVoice (rc : RootClass) : Prop := rc = .tv

instance : DecidablePred RootClass.LicensesTransitiveVoice :=
  fun rc ↦ inferInstanceAs (Decidable (rc = .tv))

/-- √TV and √ITV share type and valency, after [davis-1997]; compatibility with external
causation by an agent alone separates them, §3.3. -/
theorem tv_itv_differ_only_in_voice :
    RootClass.tv.ty = RootClass.itv.ty ∧ RootClass.tv.valency = RootClass.itv.valency ∧
      RootClass.tv.LicensesTransitiveVoice ∧ ¬ RootClass.itv.LicensesTransitiveVoice :=
  ⟨rfl, rfl, rfl, by decide⟩

/-! ### The v ~ Voice⁰ heads -/

/-- The v ~ Voice⁰ heads of the verb stem ((6), (78)), the transitive Ø, the null intransitive
head of §2.1, and the suffixes -w, -ch and -j. -/
inductive V
  | transitive | intransitive | w | ch | j
  deriving DecidableEq, Fintype, Repr

/-- The Minimalist Voice head each realizes, a bundled v ~ Voice⁰ after [harley-2017]
introducing the external argument as in [kratzer-1996] and specified for whether and what it
introduces as in [alexiadou-anagnostopoulou-schaefer-2006] and [wood-2015]. The transitive
head and -w both merge an agent, footnote 10; -ch merges an implicit, existentially bound agent
in its specifier, (64), the impersonal cell with a specifier; -j and the null intransitive head
introduce no external argument and project no specifier, (68), the expletive cell. -/
def V.head : V → Head
  | .transitive => Minimalist.Voice.agentive
  | .intransitive => Minimalist.Voice.middle
  | .w => Minimalist.Voice.agentive
  | .ch => { Minimalist.Voice.passive with hasD := true }
  | .j => Minimalist.Voice.middle

/-- The head assigns inherent ergative case to the agent in its specifier, as the transitive
head alone does (78). -/
def V.AssignsErgative (v : V) : Prop := v = .transitive

instance : DecidablePred V.AssignsErgative := fun v ↦ inferInstanceAs (Decidable (v = _))

/-- The two agent-introducing heads are one Voice cell and differ in inherent ergative case
alone, footnote 10. -/
theorem w_head_eq : V.w.head = V.transitive.head ∧ ¬ V.w.AssignsErgative ∧
    V.transitive.AssignsErgative :=
  ⟨rfl, by decide, rfl⟩

/-- Every head keeps its [D] feature in step with its cell except -ch, whose specifier hosts
the implicit agent of (64) that the impersonal cell leaves specifierless. -/
theorem dCoherent : (∀ v : V, v ≠ .ch → v.head.DCoherent) ∧ ¬ V.ch.head.DCoherent :=
  ⟨fun v ↦ by cases v <;> decide, by decide⟩

/-- The head properties behind (78) are read off the substrate cells. Every head but -j and the
null intransitive head introduces an external argument, and -ch alone an implicit one. -/
theorem head_table :
    (∀ v : V, v.head.IsThematic ↔ v ≠ .intransitive ∧ v ≠ .j) ∧
      ∀ v : V, v.head.ExternalImplicit ↔ v = .ch := by
  refine ⟨?_, ?_⟩ <;> intro v <;> cases v <;> decide

/-! ### Licensing -/

/-- How the internal argument slot of a root is realized ((56), (78)), by a full DP saturating
it, a bare NP restricting it, or an implicit argument saturating it as a variable to be bound,
or else absent. -/
inductive Internal
  | dp | np | implicit | absent
  deriving DecidableEq, Fintype, Repr

/-- The realizations a root class admits. A transitive root composes with its argument in every
stem, §5; nominal and positional roots select nothing, (39); an intransitive root's argument is
a full DP, a coordinate stipulated here, since nothing in the analysis rules out (48b) and the
paper leaves the absence of unaccusative subject incorporation to typology, while no implicit
option for such roots is attested. -/
def internals : RootClass → List Internal
  | .tv => [.dp, .np, .implicit]
  | .itv => [.dp]
  | .pos | .nom => [.absent]

/-- The licenser of an argument, (78). -/
inductive Licenser
  | voice | infl | unlicensed
  deriving DecidableEq, Repr

/-- Who licenses each argument position of a stem (§3.2.1, §3.2.2). The head cases its own
specifier when it assigns inherent ergative, finite Infl⁰ cases a DP the head does not, and a
bare NP, an implicit argument and an absent one need no case. -/
def licenser (v : V) (i : Internal) : ArgPosition → Licenser
  | .external =>
    if v.head.IsThematic ∧ ¬ v.head.ExternalImplicit then
      (if v.AssignsErgative then .voice else .infl) else .unlicensed
  | .internal => if i = .dp then .infl else .unlicensed

/-- A stem is licensed when Infl⁰ has exactly one argument to license. It licenses one
absolutive argument, and must license one, the Obligatory Case Parameter that footnote 15
offers beside an economy condition to keep the transitive head off stems whose only DP it would
case itself. -/
def Licensed (v : V) (i : Internal) : Prop :=
  (Finset.univ.filter fun a ↦ licenser v i a = .infl).card = 1

instance (v : V) (i : Internal) : Decidable (Licensed v i) := by unfold Licensed; infer_instance

/-- The selection each head imposes on the root ((78), §2.1). The transitive head and the
passive -ch need a root whose event admits an external agent, and so does -j apart from
isolated forms like (71); the null intransitive head needs an unaccusative root; -w needs only
a root, its ban on intransitive roots following from licensing rather than selection, §3.3. -/
def V.Selects : V → RootClass → Prop
  | .transitive, rc | .ch, rc | .j, rc => rc.LicensesTransitiveVoice
  | .intransitive, rc => rc.valency = {.internal} ∧ ¬ rc.LicensesTransitiveVoice
  | .w, _ => True

instance (v : V) (rc : RootClass) : Decidable (v.Selects rc) := by
  cases v <;> simp only [V.Selects] <;> infer_instance

/-- A stem from a root class is well-formed when the head selects the root, the root admits the
realization, and the arguments are licensed. -/
def WellFormed (rc : RootClass) (v : V) (i : Internal) : Prop :=
  v.Selects rc ∧ i ∈ internals rc ∧ Licensed v i

instance (rc : RootClass) (v : V) (i : Internal) : Decidable (WellFormed rc v i) := by
  unfold WellFormed; infer_instance

/-- The voice of the fragment a head derives with a realization of the internal argument
(Section 4) is the transitive stem under the transitive head, the passives under -ch and -j, the
attested -chaj carrying the -aj that closes the implicit agent, and under -w the incorporation
antipassive with a bare NP and, with -aj closing an implicit theme, the absolutive antipassive;
none under the null intransitive head, whose stem is no voice. -/
def V.voice : V → Internal → Option Voice
  | .transitive, _ => some Chuj.transitive
  | .intransitive, _ => none
  | .ch, _ => some Chuj.passive
  | .j, _ => some Chuj.agentlessPassive
  | .w, .implicit => some Chuj.absolutiveAntipassive
  | .w, _ => some Chuj.incorporationAntipassive

/-- A root class forms a stem with a head when the head is well-formed on it under some
realization; stems with other derivational suffixes, (11) and (15), are not in view. -/
def FormsStem (rc : RootClass) (v : V) : Prop := ∃ i, WellFormed rc v i

instance (rc : RootClass) (v : V) : Decidable (FormsStem rc v) := by
  unfold FormsStem; infer_instance

/-- The distribution of the heads over the root classes is derived. √TV takes every head but the
null intransitive one, (45) and (59) to (60); √ITV only that one, (47); √POS and √NOM only -w,
(45), apart from isolated forms like (71). -/
theorem formsStem_iff :
    (∀ v, FormsStem .tv v ↔ v ≠ .intransitive) ∧ (∀ v, FormsStem .itv v ↔ v = .intransitive) ∧
      (∀ v, FormsStem .pos v ↔ v = .w) ∧ ∀ v, FormsStem .nom v ↔ v = .w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro v <;> cases v <;> decide

/-- The stems of a transitive root are exactly the five voices of the fragment, (58). -/
theorem voice_tv_iff (vo : Voice) :
    vo ∈ Chuj.voices ↔ ∃ v i, WellFormed .tv v i ∧ v.voice i = some vo := by
  constructor
  · intro h
    simp only [Chuj.voices, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [⟨.transitive, .dp, by decide, rfl⟩, ⟨.w, .np, by decide, rfl⟩,
      ⟨.w, .implicit, by decide, rfl⟩, ⟨.j, .dp, by decide, rfl⟩, ⟨.ch, .dp, by decide, rfl⟩]
  · rintro ⟨v, i, hw, hv⟩
    cases v <;> cases i <;> simp only [V.voice, Option.some.injEq, reduceCtorEq] at hv <;>
      first | exact absurd hw (by decide) | (subst hv; decide)

/-- The stems of a transitive root ((78), (79)) have a full DP under the transitive head and
under both passives, and a bare NP or an implicit argument under -w. -/
theorem tv_stems :
    Finset.univ.filter (fun p : V × Internal ↦ WellFormed .tv p.1 p.2) =
      {(.transitive, .dp), (.ch, .dp), (.j, .dp), (.w, .np), (.w, .implicit)} := by
  decide

/-- No stem of -w has a full DP internal argument (37), since Infl⁰ is taken by the agent. -/
theorem w_no_dp (rc : RootClass) : ¬ WellFormed rc .w .dp := by
  cases rc <;> decide

/-- A transitive root under -w requires its complement, (38), and a nominal root rejects one,
(39), so the difference lies in the root. -/
theorem w_complement : ¬ WellFormed .tv .w .absent ∧ ¬ WellFormed .nom .w .np := by decide

/-- There is no -w on an intransitive root (47), since with the agent on Infl⁰ the root's DP
argument goes unlicensed, §3.3, a consequence of licensing rather than selection, given that the
argument is a DP. -/
theorem itv_no_w : (∀ i, ¬ WellFormed .itv .w i) ∧ V.w.Selects .itv :=
  ⟨fun i ↦ by cases i <;> decide, trivial⟩

/-- Every class forms a verb stem with some head, so root class is not surface category (§5). -/
theorem every_class_verbalizes (rc : RootClass) : ∃ v, FormsStem rc v := by
  cases rc
  exacts [⟨.transitive, by decide⟩, ⟨.intransitive, by decide⟩, ⟨.w, by decide⟩, ⟨.w, by decide⟩]

/-- Table (78) for the stems of a transitive root. The external argument is licensed by
v ~ Voice⁰ in the transitive, absent or implicit in the passives, and licensed by Infl⁰ under
-w; the internal argument is licensed by Infl⁰ except under -w. -/
theorem licenser_table :
    licenser .transitive .dp .external = .voice ∧ licenser .transitive .dp .internal = .infl ∧
      licenser .ch .dp .external = .unlicensed ∧ licenser .j .dp .external = .unlicensed ∧
      licenser .w .np .external = .infl ∧ licenser .w .np .internal = .unlicensed ∧
      licenser .w .implicit .internal = .unlicensed := by
  decide

/-- A stem is agentive intransitive when Infl⁰ licenses its overt external argument, hence a
single absolutive argument (§3). -/
def AgentiveIntransitive (v : V) (i : Internal) : Prop :=
  licenser v i .external = .infl ∧ Licensed v i

instance (v : V) (i : Internal) : Decidable (AgentiveIntransitive v i) := by
  unfold AgentiveIntransitive; infer_instance

/-- Only -w forms agentive intransitive stems, (49), the head that merges an agent without
ergative case. A language lacking it, Ch'ol, has no agentive intransitive verb stems and forms
its unergatives and antipassives on nominal stems under a light verb, §3.4.2. -/
theorem agentiveIntransitive_iff (v : V) (i : Internal) :
    AgentiveIntransitive v i ↔ v = .w ∧ i ≠ .dp := by
  cases v <;> cases i <;> decide

/-! ### Implicit arguments and -aj -/

/-- The implicit arguments of a stem, the existentially bound agent of -ch and the implicit
internal argument of the absolutive antipassive. -/
def Implicit (v : V) (i : Internal) : ArgPosition → Prop
  | .external => v.head.ExternalImplicit
  | .internal => i = .implicit

/-- The suffix -aj, an overt reflex of Existential Closure ([diesing-1992]) binding an implicit
argument above v ~ VoiceP (§4.2), is present exactly when the stem has one. -/
def Aj (v : V) (i : Internal) : Prop := ∃ a, Implicit v i a

instance (v : V) (i : Internal) (a : ArgPosition) : Decidable (Implicit v i a) := by
  cases a <;> simp only [Implicit] <;> infer_instance

instance (v : V) (i : Internal) : Decidable (Aj v i) := by unfold Aj; infer_instance

/-- Table (58) puts -aj on the -chaj passive and the -waj absolutive antipassive, and on neither
the -j passive, whose agent is absent, nor the incorporation antipassive, whose argument is
bound at once (footnote 28). -/
theorem aj_table :
    Aj .ch .dp ∧ Aj .w .implicit ∧ ¬ Aj .j .dp ∧ ¬ Aj .w .np ∧ ¬ Aj .transitive .dp := by
  decide

/-! ### Agent diagnostics -/

/-- The reading of an oblique -uj phrase adjoined to a passive is the agent when the head has an
implicit agent to identify, (62) and (66a); otherwise a cause of any kind, an agent not
excluded but not required, (65) and (66b). -/
inductive ObliqueReading
  | agent | cause
  deriving DecidableEq, Repr

/-- The reading of the -uj phrase under each head. -/
def V.obliqueReading (v : V) : ObliqueReading :=
  if v.head.ExternalImplicit then .agent else .cause

/-- Agent-oriented adverbs and purpose clauses need an agent, overt or implicit (§4.1), so -ch
admits them and reads its oblique as the agent, (62) and (63); -j rejects them and reads its
oblique as a cause, (65) and (67). -/
theorem passive_contrast :
    V.ch.head.IsThematic ∧ ¬ V.j.head.IsThematic ∧
      V.obliqueReading .ch = .agent ∧ V.obliqueReading .j = .cause := by
  decide

/-! ### Composing the internal argument -/

section Semantics

variable {E S : Type*} (P : E → S → Prop) (Q : E → Prop) (a : E)

/-- Restrict (footnote 19, after [chung-ladusaw-2004]) narrows the root by a property complement
without saturating its argument, (44b). -/
def restrict : E → S → Prop := fun x e ↦ P x e ∧ Q x

/-- Existential Closure (footnote 19, after [chung-ladusaw-2004]) binds the open argument at the
event level, (44c). -/
def close : S → Prop := fun e ↦ ∃ x, P x e

/-- The transitive stem (43), in which the DP saturates the root by Functional Application. -/
def transitiveStem : S → Prop := P a

/-- The incorporation antipassive (44), in which the bare NP restricts the root and Existential
Closure
applies at once, so nothing is left open above v ~ VoiceP, footnote 28. -/
def incorporationStem : S → Prop := close (restrict P Q)

/-- The absolutive antipassive (75), in which the implicit argument saturates the root as a
variable
that the closure -aj spells out binds; the truth conditions coincide with closing at the root,
the difference of locus that footnote 28 draws being what `aj` records. -/
def absolutiveStem : S → Prop := close P

/-- Every stem of a transitive root composes with an internal argument (§5). Each describes
events in which the root relation holds of some entity, so the transitive and incorporation
stems entail the absolutive one, a corollary the paper does not draw. -/
theorem stems_close :
    (∀ e, transitiveStem P a e → absolutiveStem P e) ∧
      ∀ e, incorporationStem P Q e → absolutiveStem P e :=
  ⟨fun _ h ↦ ⟨a, h⟩, fun _ ⟨x, h, _⟩ ↦ ⟨x, h⟩⟩

end Semantics

/-! ### The rows -/

/-- The analysis of a row's root, found in the root inventory by its form. -/
def rowRoot (row : Datum) : Option Wordlist.Analysis :=
  row.feature? "rootForm" >>= fun f ↦ Wordlist.analyses.find? (·.form.form == f)

def heads : List (String × V) :=
  [("transitive", .transitive), ("intransitive", .intransitive), ("w", .w), ("ch", .ch),
    ("j", .j)]

/-- A stem row, with the root class, the head, the realization of the internal slot, and
whether -aj appears. -/
structure Stem where
  /-- The root class. -/
  root : RootClass
  /-- The head. -/
  head : V
  /-- The realization of the internal slot. -/
  internal : Internal
  /-- Whether -aj appears. -/
  hasAj : Bool

/-- The stem a row records. -/
def Stem.ofRow (row : Datum) : Option Stem := do
  guard (row.feature? "construction" = some "stem")
  return ⟨(← rowRoot row).rootClass, ← row.parse? "head" heads,
    ← row.parse? "internal"
      [("dp", Internal.dp), ("np", .np), ("implicit", .implicit), ("none", .absent)],
    ← row.parse? "aj" [("yes", true), ("no", false)]⟩

/-- For the stems of §2 to §4 and (79), a row is grammatical exactly when its stem is well-formed,
and a grammatical row bears -aj exactly when its stem has an implicit argument. -/
theorem stem_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "stem" →
    ∃ s ∈ Stem.ofRow row,
      (row.judgment ≠ .ungrammatical ↔ WellFormed s.root s.head s.internal) ∧
        (row.judgment ≠ .ungrammatical → (s.hasAj = true ↔ Aj s.head s.internal)) := by
  decide

/-- The head a diagnostic row tests. -/
def diagnosticHead (row : Datum) : Option V := do
  guard (row.feature? "construction" = some "diagnostic")
  row.parse? "head" heads

/-- Agent-oriented adverbs and purpose clauses are admitted exactly under a head with an agent
((63), (67)). -/
theorem diagnostic_rows : ∀ row ∈ Examples.all,
    row.feature? "construction" = some "diagnostic" →
    ∃ v ∈ diagnosticHead row, (row.judgment ≠ .ungrammatical ↔ v.head.IsThematic) := by
  decide

/-- The head and the recorded reading of an oblique row. -/
def obliqueRow (row : Datum) : Option (V × ObliqueReading) := do
  guard (row.feature? "oblique").isSome
  return (← row.parse? "head" heads,
    ← row.parse? "oblique" [("agent", ObliqueReading.agent), ("cause", .cause)])

/-- The -uj phrase names the agent under -ch and a cause under -j ((62), (65), (66), (70),
(73)). -/
theorem oblique_rows : ∀ row ∈ Examples.all, (row.feature? "oblique").isSome = true →
    ∃ p ∈ obliqueRow row, p.2 = p.1.obliqueReading := by
  decide

end Coon2019
