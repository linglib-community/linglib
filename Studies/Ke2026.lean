module

public import Linglib.Data.Examples.Ke2026
public import Linglib.Syntax.Minimalist.Linearization.SpelloutDomain
public import Linglib.Syntax.Minimalist.Phase.Transfer
public import Linglib.Syntax.Minimalist.Label.RaisingHead

/-!
# Ke (2026): The domain of transfer

Ke argues that Transfer applies to whole phases, edge included, rather than to the complement of a
phase head, and that a phase is transferred either when it is complete or, if something in it has
yet to move out, when the next phase is complete. With every phase waiting, Transfer
[seals no more than the Phase Impenetrability Condition does](##sealed_hybrid_subset_pic1) at any
stage of any object, so whatever the condition allows still moves; with none waiting, it traps
whatever sits at an edge. Successive-cyclic movement then need not stop at the edge of the phase it
starts in: in the paper's long-distance question Transfer
[requires a stop in each higher phase](##obeysTransfer_iff) and nothing more. The edge effects come
instead from Fox and Pesetsky's preservation of spell-out order, which
[only movement through every edge satisfies](##linearizes_iff), and only when whole phases are
spelled out, since under complement spell-out
[every stop reverses an order](##complement_linearizes_iff). A phase with nothing left to move,
such as the embedded CP of a declarative, need not wait, while
[a vP must](##cp_at_completion), its subject raising out of it.

## Implementation notes

* The phase heads are v and C. The clauses are built without T-to-C movement, and nominals and the
  wh-phrase are single heads.
* Every landing site of the wh-phrase is the edge of a phase, so a route is the set of edges it
  stops at below the one where it is pronounced.
* Spell-out order preservation is the consistency of the derivation's spell-outs
  (`Minimalist.Derivation.Linearizes`). A whole phase is spelled out when it is complete
  (`Minimalist.Derivation.phaseSchedule`), a complement when its phase head merges.
* Transfer is read off the chains of the derived object, a link failing when its lower copy lies in
  a domain transferred by the stage it lands at. A phase is its head's projection under
  `HeadFunction.raising`, so a phase head's specifiers are in its phase. The root is the last
  stage, so the transfer of the root phase seals nothing.
* Which phases wait is a parameter of the schedule. In the paper it follows from the feature
  criterion: a phase waits when it contains an unvalued feature.

## TODO

* The feature criterion (8), under which a transferred phase crashes if it contains an unvalued
  feature other than on a lower copy, so that a phrase that stays in situ with an unvalued feature
  crashes, and which decides the phases that wait.
* Head movement across a phase boundary (14)–(15), and the problems of Table 35.1 beyond the
  domain and timing of transfer and the edge effects.

## References

* [ke-2026]
* [fox-pesetsky-2005]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Ke2026

open Minimalist

/-! ### The timing of Transfer -/

section Schedule

variable (hd : HeadFunction) (t : PlanarSyntacticObject)

/-- Ke's schedule: the domain of a phase head in `W` is transferred once a phase containing its
phase in its complement is complete, that of any other once its own phase is complete. -/
def Hybrid (W : Finset GornAddress) : Schedule := fun Φ h s ↦
  if h ∈ W then ∃ z ∈ Φ, s < projectionAt hd t z ∧ complement z ≤ projectionAt hd t h
  else Pic1 hd t Φ h s

instance (W Φ : Finset GornAddress) (h s : GornAddress) : Decidable (Hybrid hd t W Φ h s) := by
  unfold Hybrid; infer_instance

variable {hd t} {W Φ : Finset GornAddress} {h s : GornAddress}

@[simp] theorem hybrid_empty : Hybrid hd t ∅ = Pic1 hd t := by
  funext Φ h s
  simp [Hybrid]

-- p. 699: the schedule is that of [chomsky-2001] where a phase waits
theorem pic2_of_hybrid (hW : h ∈ W) (hp : Hybrid hd t W Φ h s) : Pic2 hd t Φ h s := by
  simp only [Hybrid, hW, ↓reduceIte] at hp
  obtain ⟨z, hz, hs, hc⟩ := hp
  exact ⟨z, hz, by simpa [GornAddress.pred_eq_parent] using
    Order.le_pred_of_lt (hs.trans_le (projectionAt_le hd t z)), hc⟩

/-- With every phase waiting, whole-phase Transfer seals at each stage only positions that the
Phase Impenetrability Condition of [chomsky-2000] seals: a phase transferred when the next is
complete lies in that phase's complement. -/
theorem sealed_hybrid_subset_pic1 :
    sealed Φ (wholePhaseDomain hd t) (Hybrid hd t Φ) s ⊆
      sealed Φ (complementDomain hd t ∅) (Pic1 hd t) s := by
  rintro q ⟨h, hΦ, hσ, hq⟩
  simp only [Hybrid, hΦ, ↓reduceIte] at hσ
  obtain ⟨z, hz, hs, hc⟩ := hσ
  exact ⟨z, hz, hs, by
    simpa [complementDomain, transferHead] using
      hc.trans (show projectionAt hd t h < q from hq).le⟩

end Schedule

/-- The phase heads, v and C. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop := a.item.cat = .v ∨ a.item.cat = .C

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- No link of a chain in the object a derivation derives leaves a domain `D` of its phase heads
that has been transferred, the phases whose heads `W` holds of waiting for the next phase. -/
def ObeysTransfer (d : Derivation) (D : PlanarSyntacticObject → GornAddress → Set GornAddress)
    (W : LexicalItem.Token → Prop) [DecidablePred W] : Prop :=
  ∀ t ∈ d.externalize?, ∀ y ∈ tokenList t.toRoseTree,
    ¬ LinkLeaves .raising t y.2 (sealed (occurrencesWith t IsPhaseHead).toFinset (D t)
      (Hybrid .raising t (occurrencesWith t W).toFinset))

instance (d : Derivation) (D : PlanarSyntacticObject → GornAddress → Set GornAddress)
    [∀ t h, DecidablePred (· ∈ D t h)] (W : LexicalItem.Token → Prop) [DecidablePred W] :
    Decidable (ObeysTransfer d D W) := by
  unfold ObeysTransfer; infer_instance

-- p. 684: the approach keeps what the complement domain derives
theorem ObeysTransfer.of_pic1 {d : Derivation}
    (h : ObeysTransfer d (complementDomain .raising · ∅) fun _ ↦ False) :
    ObeysTransfer d (wholePhaseDomain .raising) IsPhaseHead := fun t ht y hy hl ↦
  h t ht y hy <| hl.mono fun s ↦ by
    have : occurrencesWith t (fun _ ↦ False) = [] := by simp [occurrencesWith]
    simpa [this] using sealed_hybrid_subset_pic1

/-! ### The derivation of (13) -/

def toWhom : LexicalItem.Token := ⟨.of .P [] "to whom", 1⟩
def gave : LexicalItem.Token := ⟨.of .V [.D, .P] "gave", 2⟩
def book : LexicalItem.Token := ⟨.of .D [] "the book", 3⟩
def v₁ : LexicalItem.Token := ⟨.of .v [.V], 4⟩
def mary : LexicalItem.Token := ⟨.of .D [] "Mary", 5⟩
def t₁ : LexicalItem.Token := ⟨.of .T [.v], 6⟩
def that : LexicalItem.Token := ⟨.of .C [.T] "that", 7⟩
def say : LexicalItem.Token := ⟨.of .V [.C] "say", 8⟩
def v₂ : LexicalItem.Token := ⟨.of .v [.V], 9⟩
def he : LexicalItem.Token := ⟨.of .D [] "he", 10⟩
def will : LexicalItem.Token := ⟨.of .T [.v] "will", 11⟩
def cQ : LexicalItem.Token := ⟨.of .C [.T], 12⟩

/-- The edges of the phases below the interrogative CP, where *to whom* may stop. -/
inductive Landing
  | vP₁ | CP₁ | vP₂
  deriving DecidableEq, Fintype

/-- The derivation of (13) in which *to whom* stops at the edges in `r` on its way to the edge of
the interrogative CP. -/
def derivation (r : Finset Landing) : Derivation :=
  ⟨gave, [.em .right book, .em .right toWhom, .em .left v₁, .em .left mary] ++
    (if .vP₁ ∈ r then [.im toWhom] else []) ++ [.em .left t₁, .im mary, .em .left that] ++
    (if .CP₁ ∈ r then [.im toWhom] else []) ++ [.em .left say, .em .left v₂, .em .left he] ++
    (if .vP₂ ∈ r then [.im toWhom] else []) ++
    [.em .left will, .im he, .em .left cQ, .im toWhom]⟩

/-! ### Spell-out order preservation -/

/-- The schedule that spells the complement of each phase head of (13) out when the head merges,
the complement being the object built just before. -/
def complementSchedule (d : Derivation) : List (ℕ × ℕ) :=
  [v₁, that, v₂, cQ].filterMap fun a ↦ (d.mergeStage? a).map fun n ↦ (n - 1, n)

/-- In (13), with phases spelled out when complete, a derivation linearizes exactly when *to whom*
stops at every edge: one that skips an edge is spelled out after material of that phase and
before it in the next. -/
theorem linearizes_iff (r : Finset Landing) :
    (derivation r).Linearizes ((derivation r).phaseSchedule .raising IsPhaseHead) ↔ r = .univ := by
  revert r; decide +kernel

-- (13)
theorem rows_predicted : ∀ e ∈ Examples.all, (e.judgment = .acceptable ↔
    ∃ r, (derivation r).Linearizes ((derivation r).phaseSchedule .raising IsPhaseHead)) := by
  decide +kernel

/-- Spelling complements out instead, a derivation linearizes only when *to whom* stops nowhere:
even through every edge, the complement of v₁ spells *the book* out before *to whom*, that of C₁
after it. -/
theorem complement_linearizes_iff (r : Finset Landing) :
    (derivation r).Linearizes (complementSchedule (derivation r)) ↔ r = ∅ := by
  revert r; decide +kernel

/-! ### The domain and timing of Transfer -/

/-- In (13), with whole phases transferred and every phase waiting for the next, Transfer is obeyed
exactly when *to whom* stops in CP₁ and in vP₂: it may skip the edge of vP₁, the phase it starts
in (11), but not a whole phase. -/
theorem obeysTransfer_iff (r : Finset Landing) :
    ObeysTransfer (derivation r) (wholePhaseDomain .raising) IsPhaseHead ↔
      .CP₁ ∈ r ∧ .vP₂ ∈ r := by
  revert r; decide +kernel

-- (1), (2a): the Phase Impenetrability Condition allows only movement through every edge
theorem pic1_iff (r : Finset Landing) :
    ObeysTransfer (derivation r) (complementDomain .raising · ∅) (fun _ ↦ False) ↔ r = .univ := by
  revert r; decide +kernel

-- (2b): transferred whole as soon as it is complete, vP₁ traps *Mary* at its edge
theorem trapped_at_completion (r : Finset Landing) :
    ¬ ObeysTransfer (derivation r) (wholePhaseDomain .raising) fun _ ↦ False := by
  revert r; decide +kernel

/-! ### Phases that need not wait -/

def visited : LexicalItem.Token := ⟨.of .V [.D] "visited", 13⟩
def bill : LexicalItem.Token := ⟨.of .D [] "Bill", 14⟩
def c₁ : LexicalItem.Token := ⟨.of .C [.T], 15⟩
def john : LexicalItem.Token := ⟨.of .D [] "John", 16⟩
def t₂ : LexicalItem.Token := ⟨.of .T [.v], 17⟩
def c₂ : LexicalItem.Token := ⟨.of .C [.T], 18⟩

/-- The derivation of (10), *John said Mary visited Bill*, each subject raising from the edge of
its vP. -/
def declarative : Derivation :=
  ⟨visited, [.em .right bill, .em .left v₁, .em .left mary, .em .left t₁, .im mary, .em .left c₁,
    .em .left say, .em .left v₂, .em .left john, .em .left t₂, .im john, .em .left c₂]⟩

/-- In (10) the embedded CP can be transferred as soon as it is complete, while the vPs must wait
for their subjects to raise; in (13) the CP that *to whom* passes through must wait as well. -/
theorem cp_at_completion :
    ObeysTransfer declarative (wholePhaseDomain .raising) (·.item.cat = .v) ∧
      ¬ ObeysTransfer declarative (wholePhaseDomain .raising) (·.item.cat = .C) ∧
      ¬ ObeysTransfer (derivation .univ) (wholePhaseDomain .raising) (·.item.cat = .v) := by
  decide +kernel

end Ke2026
