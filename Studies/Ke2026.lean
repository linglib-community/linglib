module

public import Linglib.Data.Examples.Ke2026
public import Linglib.Syntax.Minimalist.Linearization.SpelloutDomain
public import Linglib.Syntax.Minimalist.Phase.Transfer
public import Linglib.Syntax.Minimalist.Label.RaisingHead

/-!
# Ke (2026): The domain of transfer

Ke argues that Transfer applies to whole phases, edge included, rather than to the complement of a
phase head, and that a phase is transferred either when it is complete or, if something in it has
yet to move out, when the next phase is complete. With every phase waiting, Transfer seals
[no more than the Phase Impenetrability Condition does](##sealed_hybrid_subset_complementDomain)
at any stage of any object, so whatever the condition allows still moves; with none waiting, it
traps whatever sits at an edge. Successive-cyclic movement then need not stop at the edge of the
phase it starts in: in the paper's long-distance question Transfer
[requires a stop in each higher phase](##obeysTransfer_iff) and nothing more. The edge effects come
instead from Fox and Pesetsky's preservation of spell-out order, which
[only movement through every edge satisfies](##linearizes_iff), a skipped edge
[reversing the order of the verb and the wh-phrase](##gave_toWhom_of_skip), and only when whole
phases are spelled out, since under complement spell-out
[every stop reverses an order](##complement_linearizes_iff). The phases that must wait are
[those a chain link leaves](##forall_not_linkLeaves_hybrid_iff): the vPs of a declarative, whose
subjects raise, but not its embedded CP.

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
  `HeadDaughter.raising`, so a phase head's specifiers are in its phase. The root is the last
  stage, so the transfer of the root phase seals nothing.
* A phase is spelled out when it is complete, whether or not its transfer waits. Spelled out only
  when the next phase is complete, vP₁ no longer holds the wh-phrase, and
  [the derivation that skips its edge linearizes](##skip_linearizes_nextPhase).
* A waiting phase is transferred when the next phase is complete. The paper also speaks of the
  next phase head entering the derivation; on that timing a subject still raises in time, but
  [the wh-phrase of (13) is held in vP₁](##trapped_at_next_merger).
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

open Schedule

variable (hd : HeadDaughter) (t : PlanarSyntacticObject TokenLeaf)

/-- Ke's schedule: the domain of a phase head in `W` is transferred once the next phase is
complete, that of any other once its own phase is complete. -/
def Hybrid (W : Finset GornAddress) : Schedule := fun Φ ↦
  W.piecewise (ofNextPhase hd t (atCompletion hd t) Φ) (atCompletion hd t Φ)

variable {hd t} {W Φ : Finset GornAddress} {h s : GornAddress}

theorem hybrid_of_mem (hW : h ∈ W) :
    Hybrid hd t W Φ h s ↔ ofNextPhase hd t (atCompletion hd t) Φ h s := by
  rw [Hybrid, Finset.piecewise_eq_of_mem _ _ _ hW]

theorem hybrid_of_notMem (hW : h ∉ W) : Hybrid hd t W Φ h s ↔ atCompletion hd t Φ h s := by
  rw [Hybrid, Finset.piecewise_eq_of_notMem _ _ _ hW]

instance : Decidable (Hybrid hd t W Φ h s) :=
  if hW : h ∈ W then decidable_of_iff _ (hybrid_of_mem hW).symm
  else decidable_of_iff _ (hybrid_of_notMem hW).symm

-- a phase that waits is transferred after it is complete
theorem atCompletion_of_hybrid (hp : Hybrid hd t W Φ h s) : atCompletion hd t Φ h s := by
  by_cases hW : h ∈ W
  · exact ofNextPhase_atMerger_le_atCompletion _ _ _
      (ofNextPhase_mono atCompletion_le_atMerger _ _ _ ((hybrid_of_mem hW).1 hp))
  · exact (hybrid_of_notMem hW).1 hp

-- the more phases wait, the later each domain is transferred
theorem hybrid_anti {W' : Finset GornAddress} (hW : W ⊆ W') (hp : Hybrid hd t W' Φ h s) :
    Hybrid hd t W Φ h s := by
  by_cases h' : h ∈ W
  · exact (hybrid_of_mem h').2 ((hybrid_of_mem (hW h')).1 hp)
  · exact (hybrid_of_notMem h').2 (atCompletion_of_hybrid hp)

/-- With every phase waiting, whole-phase Transfer seals at each stage only positions that the
Phase Impenetrability Condition of [chomsky-2000] seals: a phase transferred when the next is
complete lies in that phase's complement. -/
theorem sealed_hybrid_subset_complementDomain :
    sealed Φ (wholePhaseDomain hd t) (Hybrid hd t Φ) s ⊆
      sealed Φ complementDomain (atCompletion hd t) s := by
  rintro q ⟨h, hΦ, hσ, hq⟩
  obtain ⟨z, hz, hs, hc⟩ := (hybrid_of_mem hΦ).1 hσ
  exact ⟨z, hz, hs, hc.trans (show projectionAt hd t h < q from hq).le⟩

variable (hd t) in
/-- Some chain link leaves the phase of `h` after it is complete. -/
def Leaves (h : GornAddress) : Prop :=
  ∃ y ∈ tokenList t.toRoseTree,
    LinkLeaves hd t y.2 (sealed {h} (wholePhaseDomain hd t) (atCompletion hd t))

instance (h : GornAddress) : Decidable (Leaves hd t h) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Whole-phase Transfer is obeyed with the phases in `W` waiting exactly when it is obeyed with
every phase waiting and `W` contains each phase that a chain link leaves: these are the phases that
must wait, and any other may be transferred as soon as it is complete. -/
theorem forall_not_linkLeaves_hybrid_iff :
    (∀ y ∈ tokenList t.toRoseTree,
        ¬ LinkLeaves hd t y.2 (sealed Φ (wholePhaseDomain hd t) (Hybrid hd t W))) ↔
      (∀ y ∈ tokenList t.toRoseTree,
        ¬ LinkLeaves hd t y.2 (sealed Φ (wholePhaseDomain hd t) (Hybrid hd t Φ))) ∧
      ∀ h ∈ Φ, Leaves hd t h → h ∈ W := by
  refine ⟨fun H ↦ ⟨fun y hy hl ↦ H y hy (hl.mono fun s ↦ sealed_mono (fun _ _ ↦ subset_rfl)
      fun h hΦ hp ↦ ?_), fun h hΦ ⟨y, hy, hl⟩ ↦ by_contra fun hW ↦ H y hy (hl.mono fun s ↦ ?_)⟩,
    fun ⟨H, HW⟩ y hy ⟨x, hx, h, hΦ, hσ, hq⟩ ↦ ?_⟩
  · by_cases hW : h ∈ W
    · exact (hybrid_of_mem hW).2 ((hybrid_of_mem hΦ).1 hp)
    · exact (hybrid_of_notMem hW).2 (atCompletion_of_hybrid hp)
  · rintro q ⟨h', hh', hp, hq⟩
    obtain rfl := Finset.mem_singleton.1 hh'
    exact ⟨h', hΦ, (hybrid_of_notMem hW).2 hp, hq⟩
  · by_cases hW : h ∈ W
    · exact H y hy ⟨x, hx, h, hΦ, (hybrid_of_mem hΦ).2 ((hybrid_of_mem hW).1 hσ), hq⟩
    · have hc : atCompletion hd t Φ h x.1.parent := (hybrid_of_notMem hW).1 hσ
      exact hW (HW h hΦ ⟨y, hy, x, hx, h, Finset.mem_singleton_self h, hc, hq⟩)

end Schedule

/-- The phase heads, v and C. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop := a.item.cat = .v ∨ a.item.cat = .C

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Ke's schedule on an object, the phases whose heads `W` holds of waiting. -/
def Waiting (W : LexicalItem.Token → Prop) [DecidablePred W] (t : PlanarSyntacticObject TokenLeaf) :
    Schedule :=
  Hybrid .raising t (occurrencesWith t W).toFinset

instance (W : LexicalItem.Token → Prop) [DecidablePred W] (t : PlanarSyntacticObject TokenLeaf)
    (Φ : Finset GornAddress) (h s : GornAddress) : Decidable (Waiting W t Φ h s) :=
  inferInstanceAs (Decidable (Hybrid _ _ _ _ _ _))

/-- The cut of an object: the domains `D` of its phase heads, transferred under `σ`. -/
abbrev transferCut (D : PlanarSyntacticObject TokenLeaf → GornAddress → Set GornAddress)
    (σ : PlanarSyntacticObject TokenLeaf → Schedule) (t : PlanarSyntacticObject TokenLeaf) : Cut :=
  sealed (occurrencesWith t IsPhaseHead).toFinset (D t) (σ t)

-- p. 684: the approach keeps what the complement domain derives
theorem respects_of_complementDomain {d : Derivation}
    (h : d.Respects .raising
      (transferCut (fun _ ↦ complementDomain) (Schedule.atCompletion .raising))) :
    d.Respects .raising (transferCut (wholePhaseDomain .raising) (Waiting IsPhaseHead)) :=
  h.anti fun _ _ ↦ sealed_hybrid_subset_complementDomain

theorem respects_iff_leaves {d : Derivation} {W : LexicalItem.Token → Prop}
    [DecidablePred W] :
    d.Respects .raising (transferCut (wholePhaseDomain .raising) (Waiting W)) ↔
      d.Respects .raising (transferCut (wholePhaseDomain .raising) (Waiting IsPhaseHead)) ∧
        ∀ t ∈ d.externalize?, ∀ h ∈ occurrencesWith t IsPhaseHead,
          Leaves .raising t h → h ∈ occurrencesWith t W := by
  constructor
  · rintro ⟨t, ht, H⟩
    have H' := forall_not_linkLeaves_hybrid_iff.1 (respectsCut_iff_forall_mem.1 H)
    refine ⟨⟨t, ht, respectsCut_iff_forall_mem.2 H'.1⟩, fun t' ht' h hh hl ↦ ?_⟩
    obtain rfl := Option.mem_unique ht' ht
    exact List.mem_toFinset.1 (H'.2 h (List.mem_toFinset.2 hh) hl)
  · rintro ⟨⟨t, ht, H⟩, HW⟩
    exact ⟨t, ht, respectsCut_iff_forall_mem.2 (forall_not_linkLeaves_hybrid_iff.2
      ⟨respectsCut_iff_forall_mem.1 H, fun h hh hl ↦
        List.mem_toFinset.2 (HW t ht h (List.mem_toFinset.1 hh) hl)⟩)⟩

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

/-- The schedule that spells each phase out when the next phase is complete, and the last when it
is itself complete. -/
def nextPhaseSchedule (d : Derivation) : List (ℕ × ℕ) :=
  (d.phaseStages .raising IsPhaseHead).zip
    ((d.phaseStages .raising IsPhaseHead).tail ++ [d.length])

-- fn. 20: spelled out only when transferred, vP₁ no longer holds *to whom*, and skipping its edge
-- reverses no order
theorem skip_linearizes_nextPhase :
    (derivation {.CP₁, .vP₂}).Linearizes (nextPhaseSchedule (derivation {.CP₁, .vP₂})) := by
  decide +kernel

/-- The spell-outs of a derivation under a schedule. -/
def spellouts (d : Derivation) (sched : List (ℕ × ℕ)) : List (List LexicalItem.Token) :=
  sched.map fun p ↦ d.spellout p.1 p.2

open Linearization in
-- p. 697: skipping the edge of vP₁, *gave* is spelled out before *to whom* in vP₁, after it in CP₁
theorem gave_toWhom_of_skip :
    let d := derivation {.CP₁, .vP₂}
    Statement (spellouts d (d.phaseSchedule .raising IsPhaseHead)) gave toWhom ∧
      Statement (spellouts d (d.phaseSchedule .raising IsPhaseHead)) toWhom gave := by
  decide +kernel

open Linearization in
-- pp. 697–698: skipping the edge of vP₂, *say* is spelled out before *to whom* in vP₂, after it
-- in the interrogative CP
theorem say_toWhom_of_skip :
    let d := derivation {.vP₁, .CP₁}
    Statement (spellouts d (d.phaseSchedule .raising IsPhaseHead)) say toWhom ∧
      Statement (spellouts d (d.phaseSchedule .raising IsPhaseHead)) toWhom say := by
  decide +kernel

open Linearization in
-- p. 698: with complements spelled out, *the book* precedes *to whom* in that of v₁ and follows it
-- in that of C₁
theorem book_toWhom_of_complement :
    let d := derivation .univ
    Statement (spellouts d (complementSchedule d)) book toWhom ∧
      Statement (spellouts d (complementSchedule d)) toWhom book := by
  decide +kernel

/-! ### The domain and timing of Transfer -/

-- every route replays, so a failure below is a failure of Transfer
theorem isSome_externalize?_derivation (r : Finset Landing) :
    (derivation r).externalize?.isSome := by
  revert r; decide +kernel

/-- In (13), with whole phases transferred and every phase waiting for the next, Transfer is obeyed
exactly when *to whom* stops in CP₁ and in vP₂: it may skip the edge of vP₁, the phase it starts
in (11), but not a whole phase. -/
theorem obeysTransfer_iff (r : Finset Landing) :
    (derivation r).Respects .raising
        (transferCut (wholePhaseDomain .raising) (Waiting IsPhaseHead)) ↔
      .CP₁ ∈ r ∧ .vP₂ ∈ r := by
  revert r; decide +kernel

-- (1), (2a): the Phase Impenetrability Condition allows only movement through every edge
theorem complementDomain_iff (r : Finset Landing) :
    (derivation r).Respects .raising
        (transferCut (fun _ ↦ complementDomain) (Schedule.atCompletion .raising)) ↔
      r = .univ := by
  revert r; decide +kernel

-- (2b): transferred whole as soon as it is complete, vP₁ traps *Mary* at its edge
theorem trapped_at_completion (r : Finset Landing) :
    ¬ (derivation r).Respects .raising
        (transferCut (wholePhaseDomain .raising) (Schedule.atCompletion .raising)) := by
  revert r; decide +kernel

-- pp. 699–700: were a waiting phase transferred when the next phase head merges, vP₁ would hold
-- *to whom* whichever way it went
theorem trapped_at_next_merger (r : Finset Landing) :
    ¬ (derivation r).Respects .raising
        (transferCut (wholePhaseDomain .raising) (Schedule.ofNextPhase .raising · .atMerger)) := by
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

-- (10): the vPs must wait, their subjects raising out of them, and the embedded CP need not
theorem leaves_declarative : ∀ t ∈ declarative.externalize?,
    ∀ h ∈ occurrencesWith t IsPhaseHead,
      Leaves .raising t h ↔ h ∈ occurrencesWith t (·.item.cat = .v) := by
  decide +kernel

-- (13): every phase *to whom* passes through must wait, the embedded CP included
theorem leaves_ex13 : ∀ t ∈ (derivation .univ).externalize?,
    ∀ h ∈ occurrencesWith t IsPhaseHead,
      Leaves .raising t h ↔ h ∈ occurrencesWith t (· ≠ cQ) := by
  decide +kernel

theorem isSome_externalize?_declarative : declarative.externalize?.isSome := by decide +kernel

-- (10), p. 695
theorem obeysTransfer_declarative :
    declarative.Respects .raising
        (transferCut (wholePhaseDomain .raising) (Waiting (·.item.cat = .v))) ∧
      ¬ declarative.Respects .raising
        (transferCut (wholePhaseDomain .raising) (Waiting (·.item.cat = .C))) := by
  decide +kernel

-- (15): a subject raises before the next phase head merges, so (10) survives that timing
theorem declarative_at_next_merger :
    declarative.Respects .raising
        (transferCut (wholePhaseDomain .raising) (Schedule.ofNextPhase .raising · .atMerger)) := by
  decide +kernel

end Ke2026
