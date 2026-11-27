module

public import Linglib.Semantics.Events.Closure
public import Linglib.Semantics.Modality.EventRelativity
public import Linglib.Semantics.Modality.Background
public import Linglib.Syntax.Minimalist.Spine
public import Linglib.Languages.Romance.Italian.Verbs
public import Linglib.Data.Examples.FuscoSgrizzi2026
public import Studies.Grano2024
public import Linglib.Data.Examples.Readers

/-!
# Fusco and Sgrizzi (2026): Belief or Action? Semantic Ambiguity in the Italian Non-finite Domain

This file formalizes [fusco-sgrizzi-2026]'s account of the belief and intention readings of
Italian *convincere* 'convince' with its two infinitival complements: *Marco ha convinto Gianni di
avere un figlio* reports a belief, *Marco ha convinto Gianni a avere un figlio* an intention.
Where [grano-2024] ties the alternation to mood and finiteness, the paper ties it to the size of
the complement. The *di*-infinitive is a CP: it hosts modal auxiliaries, allows subject as well
as object control, and can be assessed for truth. The *a*-infinitive stops below tense and above
vP: it hosts negation, passive and low aspectual verbs and forms a temporal domain of its own, but
blocks clitic climbing and subject control and cannot be assessed for truth. The readings follow
from the size through one lexical entry: *convincere* causes a rational-attitude state with the
property its complement supplies (`Frame.convincere`, the paper's (24)). A *di*-complement closes
the eventuality argument of the bare infinitive into a proposition, which *di* quantifies over
the state's content worlds; an *a*-complement keeps it open, and *a*, anchored to the state,
quantifies over the state's inertia worlds and binds the event to the state by the causal
relation (`aP`). Both heads are necessity anchored to the state, the event-relative modality of
[hacquard-2010]: *di* over the state's content, *a* over a circumstantial base ordered by inertia
([dowty-1979], [kratzer-2013]). This is the causal
self-referentiality of intention ([searle-1983]): in every inertia world the intended event is
caused by the attitude state, hence later than it, the future orientation of *a*-infinitives
([wurmbrand-2014]; `intention_future`). A complement is the spine it projects, a truncation of
the clause (`clause`); the reading is read off whether it reaches the complementizer, and the
diagnostics of sections 3 and 3.1 are predicted by the heads the complement contains
(`rows_predicted`).

## Implementation notes

* The *a*-infinitive is recorded with negation as its highest head, the highest the paper places
  inside it. The clause has no modal head, so the absence of modal auxiliaries ((9) and (10)) and
  the ban on past-oriented complements ((5)) stay in the prose and in `intention_future`.
* The two heads are stated over abstract eventualities and worlds, with the content, the
  circumstantial base and the inertial ordering as functions of the state. The
  closure head (23b) is `Event.closure` and the prejacent of *a* is `Event.causedClosure`, the
  operators of [grano-2024]'s account, so a complement takes its world before its eventuality.
* The examples are `Data.Examples.FuscoSgrizzi2026`; the lexical entries are those of
  `Languages/Romance/Italian/Verbs.lean`.

## References

* [fusco-sgrizzi-2026]
* [grano-2024]
* [searle-1983]
* [wurmbrand-2014]
* [dowty-1979]
* [kratzer-2013]
* [hacquard-2010]
* [rizzi-1997]
-/

@[expose] public section

open scoped PremiseOrdering

namespace FuscoSgrizzi2026

open Examples (Diagnostic)

open Modality Minimalist Italian.Verbs Event
open scoped SetRel ModalLogic

section Semantics

variable {I V W : Type*}

/-- The inertia worlds of a state, `INERTIA(s)` of (25), are the best worlds of the state's
circumstances under an inertial ordering of its own ([dowty-1979], [kratzer-2013]):
`Background.bestWorlds` with the state in place of a world. -/
def inertiaWorlds (circumstances : V → Set (W → Prop)) (inertia : V → Set (Set W)) (s : V) :
    Set W :=
  (≤[inertia s]).minimals {w | sInf (circumstances s) w}

/-- The head *a* (25), anchored to the attitude state, is necessity over the state's inertia
worlds, with the eventuality argument of its complement closed over what the state causes. -/
def aP (circumstances : V → Set (W → Prop)) (inertia : V → Set (Set W))
    (causeStar : W → SetRel V V) (P : W → V → Prop) (s : V) : Prop :=
  □[.cgraph (inertiaWorlds circumstances inertia)] (causedClosure causeStar s P) s

-- (134) [grano-2024]
theorem aP_empty (circumstances : V → Set (W → Prop)) (causeStar : W → SetRel V V)
    (P : W → V → Prop) (s : V) :
    aP circumstances (fun _ ↦ ∅) causeStar P s ↔
      Grano2024.sbjvCausal (fun s ↦ sInf (circumstances s)) causeStar P s := by
  simp [aP, inertiaWorlds, Grano2024.sbjvCausal, ModalLogic.Box]

/-- The head *di* (26) is necessity over the state's content worlds of a proposition. -/
def diP (con : V →. Set W) (Q : W → Prop) (s : V) : Prop :=
  □[compatible con] Q s

/-- The relations the denotation (24) draws on, convincing events, the thematic relations,
causation between eventualities, and the class of rational attitudes. -/
structure Frame (I V W : Type*) where
  convince : V → W → Prop
  agent : V → I → W → Prop
  patient : V → I → W → Prop
  cause : V → V → Prop
  rationalAttitude : V → Prop
  experiencer : I → V → Prop

/-- ⟦convincere⟧ (24) holds when an event of `y` convincing `x` causes a rational-attitude state
of `x` with the property `P` the complement supplies. -/
def Frame.convincere (F : Frame I V W) (P : V → Prop) (x y : I) (e : V) (w : W) : Prop :=
  ∃ s, F.convince e w ∧ F.agent e y w ∧ F.patient e x w ∧ F.cause e s ∧ F.rationalAttitude s ∧
    F.experiencer x s ∧ P s

variable (F : Frame I V W) (con : V →. Set W) (circumstances : V → Set (W → Prop))
  (inertia : V → Set (Set W)) (causeStar : W → SetRel V V) (P : W → V → Prop) (x y : I) (e : V)
  (w : W)

/-- The belief report is *convincere* with the *di*-complement, whose closure head (23b) turns the
bare infinitive into a proposition held at the state's content worlds. -/
def beliefReport : Prop := F.convincere (fun s ↦ diP con (closure P) s) x y e w

/-- The intention report is *convincere* with the *a*-complement. -/
def intentionReport : Prop :=
  F.convincere (fun s ↦ aP circumstances inertia causeStar P s) x y e w

theorem intention_causal (h : intentionReport F circumstances inertia causeStar P x y e w) :
    ∃ s, F.cause e s ∧
      ∀ w' ∈ inertiaWorlds circumstances inertia s, causedClosure causeStar s P w' :=
  let ⟨s, _, _, _, hc, _, _, ha⟩ := h
  ⟨s, hc, ha⟩

/-- When causes precede their effects, the intended event of an intention report follows the
attitude state, excluding a past-oriented complement (5b). -/
theorem intention_future {T : Type*} [Preorder T] (τ : V → T)
    (hτ : ∀ s e' w', s ~[causeStar w'] e' → τ s < τ e')
    (h : intentionReport F circumstances inertia causeStar P x y e w) :
    ∃ s, F.cause e s ∧
      ∀ w' ∈ inertiaWorlds circumstances inertia s, ∃ e', τ s < τ e' ∧ P w' e' :=
  let ⟨s, hc, ha⟩ := intention_causal F circumstances inertia causeStar P x y e w h
  ⟨s, hc, fun w' hw' ↦ let ⟨e', hce, hP⟩ := ha w' hw'; ⟨e', hτ s e' w' hce, hP⟩⟩

end Semantics

/-! ### Readings from complement size -/

/-- The two construals of a rational attitude. -/
inductive Reading
  | belief
  | intention
  deriving DecidableEq, Repr

/-- The heads of the clause that the diagnostics refer to, from the bottom up. The verb, little v,
tense and the complementizer are those of (21); Voice and negation are placed between little v and
tense, and finiteness between tense and the complementizer. -/
def clause : Spine Cat := ⟨[.V, .v, .Voice, .Neg, .T, .Fin, .C]⟩

/-- The *di*-infinitive is a CP (21): it projects the whole clause. -/
def diComplement : Spine Cat := clause

/-- The *a*-infinitive is a projection below tense with negation as its highest head (22). -/
def aComplement : Spine Cat := clause.below .T

-- the vP is the clause below Voice
theorem clause_below_Voice : clause.below .Voice = Spine.vP := by decide

/-- The reading a complement yields, belief for one that reaches the complementizer, which carries
the closure head, and intention for a smaller one. -/
def readingOf (s : Spine Cat) : Reading :=
  if Cat.C ∈ s then .belief else .intention

/-- The complement an infinitival complementizer of the language file selects. -/
def complementOf (z : Complementizer) : Option (Spine Cat) :=
  if z = di then some diComplement else if z = a then some aComplement else none

/-- The readings a verb's complementizers yield, in the order the language file lists them. -/
def readings (v : Italian.Verb) : List Reading :=
  v.clauseTypers.filterMap fun z ↦ (complementOf z).map readingOf

-- (4)
theorem convincere_pensare_readings :
    readings convincere = [.belief, .intention] ∧ readings pensare = [.belief, .intention] := by
  decide +kernel

/-! ### The diagnostics of sections 3 and 3.1 -/

/-- What a complement predicts for a diagnostic: the readings by whether it reaches the
complementizer; truth assessment by the complementizer; subject control by the finiteness head
that hosts the logophoric centre ([rizzi-1997]); passive, low aspectual verbs and negation by the
Voice, v and negation heads; a temporal domain of its own by structure above vP; clitic climbing
by a complement no larger than vP. -/
def Examples.Diagnostic.Predicted : Diagnostic → Spine Cat → Prop
  | .belief, s => readingOf s = .belief
  | .intention, s => readingOf s = .intention
  | .truthAssessable, s => Cat.C ∈ s
  | .subjectControl, s => Cat.Fin ∈ s
  | .passive, s => Cat.Voice ∈ s
  | .aspectual, s => Cat.v ∈ s
  | .negation, s => Cat.Neg ∈ s
  | .independentTime, s => Spine.vP < s
  | .cliticClimbing, s => s ≤ Spine.vP

instance (d : Diagnostic) (s : Spine Cat) : Decidable (d.Predicted s) := by
  cases d <;> unfold Diagnostic.Predicted <;> infer_instance

/-- A sentence of the paper carries its infinitival complement, the diagnostic it tests and
whether it is grammatical. -/
structure Row where
  complement : Spine Cat
  diagnostic : Diagnostic
  grammatical : Bool
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let s ← ex.parse? "size" [("cP", diComplement), ("aP", aComplement), ("vP", Spine.vP)]
  let d ← (Examples.diagnostic ex)
  let g ← ex.parse? "grammatical" [("yes", true), ("no", false)]
  pure ⟨s, d, g⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_predicted :
    ∀ r ∈ rows, (r.grammatical = true ↔ r.diagnostic.Predicted r.complement) := by
  decide +kernel

end FuscoSgrizzi2026
