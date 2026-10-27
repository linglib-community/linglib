module

public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Discourse.SpeechAct
public import Linglib.Discourse.QUD.Basic
public import Linglib.Core.Data.List.Forall2

/-!
# Roberts (2023): Imperatives in dynamic pragmatics

This file formalizes the paper's semantics and dynamic pragmatics for imperative mood. An
imperative denotes a property indexed to the addressee, its realization conditions. Over
circumstances, world–time pairs, a goal-based ordering source gives an agent's goals at a
circumstance in priority order, the timely futures of a circumstance are its possible futures at
which those goals remain in force, `timelyFut`, and a futurate circumstantial modal base delivers
the actual future circumstances in which realizing the prejacent is feasible, `IsFuturate`. The
paper's first-pass preference over circumstances ranks them by the highest-priority goal and
breaks ties by the next, which is the lexicographic order on goal profiles, `profile`; it
refines Kratzer's ordering, `profile_le_of_atLeastAsGoodAs`. The applicable circumstances are
those in whose timely futures realizing the prejacent is never worse, by the goals held there,
than not realizing it, `applic`, and the property holds of an addressee who in every applicable
circumstance comes to realize the prejacent in time, `realizes`. The content is conditional and
futurate but not deontic: an if-clause restricts the modal base, `realizes_restrict`, and
deontic force arises only when a direction is accepted and the realization of the property joins
the addressee's goals on the scoreboard, after which, other goals being equal, circumstances
realizing it are preferred, `Scoreboard.accept_prefers`. The illocutionary force linking
principle sends each type of denotation to the scoreboard coordinate it updates,
`Denotation.defaultForce`, and the conservativity presupposition on imperative subjects restricts
quantificational subjects to the addressees, `nobody_livesOn`, so that *Nobody move!* directs
each addressee not to move, `realizes_nobody_move`.

## Implementation notes

A goal-based ordering source assigns each circumstance its goals in priority order, whose set
is a Kratzer ordering source over circumstances (`Background`), and possible futures are
the substrate's `futureHistoryBase`; a goal held at a circumstance remains in force at a later
one when it is among the goals held there. The goal profile of a circumstance is the
list of its goals' truth values in priority order, so goal-relative preference is `<` on
`List Prop`, the lexicographic order with `False < True`, and "at least as good" in the
applicability condition is its negation `≤`, which agrees with the paper's `≥` because the
order is total. The property an accepted direction adds to the goals is the imperative's
denotation, its realization conditions, and the paper leaves where it enters the hierarchy
open; here it is appended below the goals already held. The common ground is the library's
filter of `Discourse/CommonGround.lean`, and assertion meets it with the asserted proposition
(`Scoreboard.semiconj_assert`). The addressee-part relation is flattened to membership in the set of
addressees, and the restriction of the property to addressees, which the paper writes as a
domain restriction on the abstracted individual, is left to the conservativity presupposition
rather than built into the domain of `realizes`.

## TODO

* Formulas (51c) and (53) reuse the world variable of the circumstance being rated for the
  realizing witness while quantifying that witness over the timely futures, which range over
  possible worlds; the possible-futures reading is formalized, and the gloss "it's possible
  ... for a to come to realize P" supports it.
* The retirement clauses of (58) and (59), a question dropped once answered and a goal dropped
  once realized or unrealizable, the comparison with the rival accounts of §5, the desiderata
  of §1, the plural-addressee derivation of *Everyone gather!*, embedded imperatives and free
  choice disjunction are discussed in the paper without a proposal formalized here.

## References

* [C. Roberts, *Imperatives in a dynamic pragmatics* (2023)][roberts-2023]
* [M. Kaufmann, *Interpreting imperatives* (2012)][kaufmann-2012]
* [P. Portner, *The semantics of imperatives within a theory of clause types*
  (2004)][portner-2004]
* [P. Portner, *Imperatives and modals* (2007)][portner-2007]
* [C. Roberts, *Information structure in discourse: towards an integrated formal theory of
  pragmatics* (2012)][roberts-2012]
* [R. C. Stalnaker, *Assertion* (1978)][stalnaker-1978]
* [A. Kratzer, *The notional category of modality* (1981)][kratzer-1981]
* [F. Veltman, *Notes on imperatives* (2018)][veltman-2018]
-/

@[expose] public section

namespace Roberts2023

open HistoricalAlternatives Modality Quantifier Filter Kaplan

variable {W T E : Type*}

/-! ### Goal profiles -/

/-- The goal profile of a circumstance under goals ranked by priority: whether it realizes each
goal, highest priority first. Goal-relative preference (52), the paper's first pass, is the
lexicographic order on profiles: `profile G c < profile G c'` when `c'` realizes the first goal
on which they differ. -/
def profile (G : List (Index W T → Prop)) (c : Index W T) : List Prop := G.map (· c)

/-- Goal-relative preference refines Kratzer's ordering: a circumstance realizing every goal
another realizes has at least as good a profile. -/
theorem profile_le_of_atLeastAsGoodAs {G : List (Index W T → Prop)} {c c' : Index W T}
    (h : c ≤[{p | p ∈ G}] c') : profile G c' ≤ profile G c :=
  List.Forall₂.le <| List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
    List.forall₂_same.2 h

theorem profile_lt_of_strictlyBetter {G : List (Index W T → Prop)} {c c' : Index W T}
    (h : (c <[{p | p ∈ G}] c')) : profile G c' < profile G c :=
  List.Forall₂.lt_of_ne
    (List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <| List.forall₂_same.2 h.1)
    fun heq ↦ h.2 fun p hp ↦ (List.map_inj_left.1 heq p hp).mpr

/-! ### Circumstances, goals and futures -/

section Semantics

variable [Preorder T] (history : HistoricalAlternatives W T)
  (g : Index W T → List (Index W T → Prop))

/-- The timely future circumstances of a circumstance (50): its possible futures at which the
goals held at it remain in force. -/
def timelyFut (c : Index W T) : Set (Index W T) :=
  {c' ∈ futureHistoryBase history c | ∀ p ∈ g c, p ∈ g c'}

theorem timelyFut_subset (c : Index W T) :
    timelyFut history g c ⊆ futureHistoryBase history c :=
  fun _ h ↦ h.1

variable (f : Background (Index W T)) (P : Index W T → E → Prop) (a : E)

/-- A futurate circumstantial modal base (51) for the realization of `P` by `a`: every
circumstance compatible with the base at a circumstance lies in its world, later than it, and
has a timely future at which `a` realizes `P`. -/
def IsFuturate : Prop :=
  ∀ c c', c' ∈ f.accessibleWorlds c →
    c'.world = c.world ∧ c.time < c'.time ∧ ∃ c'' ∈ timelyFut history g c', P c'' a

/-- The applicable circumstances (53) for the realization of `P` by `a` at `c`: those
compatible with the modal base at `c` in whose timely futures a realizer of `P` is at least as
good as a non-realizer by the goals held there. -/
def applic (c : Index W T) : Set (Index W T) :=
  {c' ∈ f.accessibleWorlds c |
    ∀ c₁ ∈ timelyFut history g c', ∀ c₂ ∈ timelyFut history g c',
      P c₁ a → ¬ P c₂ a → profile (g c') c₂ ≤ profile (g c') c₁}

/-- The realization conditions (54): `a` has the property at `c` when in every applicable
circumstance `a` comes, at a timely later time in the same world, to realize `P`. -/
def realizes (c : Index W T) : Prop :=
  ∀ c' ∈ applic history g f P a c,
    ∃ t', c'.time < t' ∧ P (c'.world, t') a ∧ (c'.world, t') ∈ timelyFut history g c'

variable {history g f P a}

theorem applic_future (hf : IsFuturate history g f P a) {c c' : Index W T}
    (h : c' ∈ applic history g f P a c) : c'.world = c.world ∧ c.time < c'.time :=
  let ⟨h₁, h₂, _⟩ := hf c c' h.1
  ⟨h₁, h₂⟩

theorem realizes_time_lt {c c' : Index W T} (h : realizes history g f P a c)
    (hc' : c' ∈ applic history g f P a c) : ∃ t', c'.time < t' ∧ P (c'.world, t') a :=
  let ⟨t', ht, hP, _⟩ := h c' hc'
  ⟨t', ht, hP⟩

theorem not_mem_applic {c c' c₁ c₂ : Index W T} (h₁ : c₁ ∈ timelyFut history g c')
    (h₂ : c₂ ∈ timelyFut history g c') (hP : P c₁ a) (hnP : ¬ P c₂ a)
    (hlt : profile (g c') c₁ < profile (g c') c₂) : c' ∉ applic history g f P a c :=
  fun h ↦ h.2 c₁ h₁ c₂ h₂ hP hnP hlt

theorem not_mem_applic_of_strictlyBetter {c c' c₁ c₂ : Index W T}
    (h₁ : c₁ ∈ timelyFut history g c') (h₂ : c₂ ∈ timelyFut history g c') (hP : P c₁ a)
    (hnP : ¬ P c₂ a) (hlt : (c₂ <[{p | p ∈ g c'}] c₁)) : c' ∉ applic history g f P a c :=
  not_mem_applic h₁ h₂ hP hnP (profile_lt_of_strictlyBetter hlt)

theorem applic_restrict_subset (q : Index W T → Prop) (c : Index W T) :
    applic history g (f.restrict q) P a c ⊆ applic history g f P a c :=
  fun _ h ↦ ⟨Background.accessibleWorlds_anti (Set.subset_insert _ _) h.1, h.2⟩

theorem IsFuturate.restrict (hf : IsFuturate history g f P a) (q : Index W T → Prop) :
    IsFuturate history g (f.restrict q) P a :=
  fun c c' h ↦ hf c c' (Background.accessibleWorlds_anti (Set.subset_insert _ _) h)

theorem realizes_restrict {c : Index W T} (h : realizes history g f P a c)
    (q : Index W T → Prop) : realizes history g (f.restrict q) P a c :=
  fun c' hc' ↦ h c' (applic_restrict_subset q c hc')

end Semantics

/-! ### The scoreboard and the pragmatics of direction -/

/-- The central coordinates of the scoreboard: the common ground, the questions under
discussion, and each interlocutor's evident goals in priority order. -/
structure Scoreboard (I W T : Type*) where
  /-- The common ground, the propositions the interlocutors accept. -/
  cg : Filter (Index W T)
  /-- The questions under discussion, the immediate one first. -/
  qud : List (Question (Index W T))
  /-- Each interlocutor's evident goals, highest priority first. -/
  goals : I → List (Index W T → Prop)

/-- The denotation of a root sentence: a proposition, a question, or a property indexed to
the addressee, an imperative's realization conditions. -/
inductive Denotation (I W T : Type*)
  /-- A declarative's proposition. -/
  | proposition (p : Set (Index W T))
  /-- An interrogative's question. -/
  | question (q : Question (Index W T))
  /-- An imperative's property, indexed to the addressee. -/
  | property (P : Index W T → I → Prop)

variable {I : Type*}

/-- The illocutionary force linking principle (56): the default force of a root sentence,
assertion, interrogation or direction, is fixed by the type of its denotation. -/
def Denotation.defaultForce : Denotation I W T → Discourse.SpeechAct.Force
  | .proposition _ => .assertion
  | .question _ => .question
  | .property _ => .directive

namespace Scoreboard

/-- Assertion (57) is Stalnaker's: an accepted proposition joins the common ground. -/
def assert (K : Scoreboard I W T) (p : Set (Index W T)) : Scoreboard I W T :=
  { K with cg := K.cg ⊓ 𝓟 p }

theorem semiconj_assert (p : Set (Index W T)) :
    Function.Semiconj (cg : Scoreboard I W T → _) (·.assert p) (· ⊓ 𝓟 p) :=
  fun _ ↦ rfl

variable [DecidableEq I] (K : Scoreboard I W T) (i : I)

/-- Accepting a move (57), (58), (59): an asserted proposition joins the common ground, a
posed question the questions under discussion, and a property directed to `i` adds its
realization by `i` to `i`'s goals, below those already held. -/
def accept : Denotation I W T → Scoreboard I W T
  | .proposition p => K.assert p
  | .question q => { K with qud := q :: K.qud }
  | .property P => { K with goals := Function.update K.goals i (K.goals i ++ [(P · i)]) }

variable (p : Set (Index W T)) (P : Index W T → I → Prop)

@[simp] theorem accept_proposition : K.accept i (.proposition p) = K.assert p :=
  rfl

@[simp] theorem cg_accept_property : (K.accept i (.property P)).cg = K.cg :=
  rfl

@[simp] theorem accept_property_qud : (K.accept i (.property P)).qud = K.qud := rfl

@[simp] theorem accept_property_goals :
    (K.accept i (.property P)).goals i = K.goals i ++ [(P · i)] := by
  simp [accept]

@[simp] theorem accept_property_goals_of_ne {j : I} (hj : j ≠ i) :
    (K.accept i (.property P)).goals j = K.goals j := by
  simp [accept, Function.update_of_ne hj]

/-- Deontic force is pragmatic: once `i` accepts a direction, among circumstances alike with
respect to `i`'s prior goals one in which `i` realizes the property is preferred to one in
which `i` does not. -/
theorem accept_prefers {c c' : Index W T} (h : ∀ p ∈ K.goals i, p c ↔ p c')
    (hc : P c i) (hc' : ¬ P c' i) :
    profile ((K.accept i (.property P)).goals i) c' <
      profile ((K.accept i (.property P)).goals i) c := by
  rw [accept_property_goals]
  unfold profile
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.map_congr_left fun p hp ↦ propext (h p hp).symm]
  exact List.Lex.append_left _ (.rel ⟨fun _ ↦ hc, fun h ↦ hc' (h hc)⟩) _

end Scoreboard

/-! ### Imperative subjects -/

/-- *Nobody* restricted to the addressees (68). The second-person pronoun (66), overt or null,
is the Montague lift `NP.individual` of an addressee, which lives on the set of addressees by
`NP.individual_livesOn`. -/
def nobody (addr : E → Prop) : NP E := GQ.no addr

theorem nobody_livesOn (addr : E → Prop) : NP.LivesOn (nobody addr) addr :=
  (GQ.conservative_iff_livesOn GQ.no).1 GQ.conservative_no addr

theorem realizes_nobody_move [Preorder T] {history : HistoricalAlternatives W T}
    {g : Index W T → List (Index W T → Prop)} {f : Background (Index W T)}
    {addr : E → Prop}
    {move : Index W T → E → Prop} {c c' : Index W T} {x y : E}
    (h : realizes history g f (fun c _ ↦ nobody addr (move c)) x c)
    (hc' : c' ∈ applic history g f (fun c _ ↦ nobody addr (move c)) x c) (hy : addr y) :
    ∃ t', c'.time < t' ∧ ¬ move (c'.world, t') y ∧ (c'.world, t') ∈ timelyFut history g c' :=
  let ⟨t', ht, hP, hfut⟩ := h c' hc'
  ⟨t', ht, hP y hy, hfut⟩

end Roberts2023
