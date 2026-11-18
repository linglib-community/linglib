module

public import Linglib.Semantics.Dynamic.FileChange
public import Linglib.Semantics.Reference.Iota
public import Linglib.Data.Examples.Roberts2003

/-!
# Roberts (2003): Uniqueness in definite noun phrases

A definite noun phrase presupposes an antecedent discourse referent that is weakly familiar and
informationally unique: of the referents in the domain of the context, it is the only one the
context entails to have the definite's descriptive content. The presupposition is [the iota over
the familiar referents entailed to have the content](##informationallyUnique_iff), and its
existence half is [Heim's Familiarity Condition](##admits_def_of_informationallyUnique), which
alone [admits *the strange man* beside a second strange man](##strangeMen). A pronoun's
presupposition takes the iota over the referents at least as salient as its antecedent, and [with
every referent equally salient it is the definite's](##pronounPresupposes_top_iff).

## Implementation notes

* A context ⟨Dom, Sat⟩ (31) is a `DynamicSemantics.State`, whose points are the world–assignment
  pairs of Sat and whose familiar referents (`State.Familiar`) are Dom. Weak familiarity is
  membership in Dom, whether the referent was introduced by mention, acquaintance or contextual
  entailment, so it needs no predicate of its own. Roberts, after Heim, keeps Dom apart from Sat;
  here every referent is familiar at the absurd state.
* The salience order of (50) is a relation `r` on referents, `r k i` reading *`k` is at least as
  salient as `i`*.

## References

* [roberts-2003]
* [heim-1982]
-/

@[expose] public section

namespace Roberts2003

open DynamicSemantics

variable {W V M : Type*} {C : State W V M} {desc : W → M → Prop} {i : V}

/-! ### The presupposition of a definite (32) -/

/-- A context entails of a referent that it has a descriptive content when every point assigns
the referent a value with that content at its world. -/
def Entails (C : State W V M) (desc : W → M → Prop) (k : V) : Prop :=
  ∀ p ∈ C, ∃ m ∈ p.assignment k, desc p.world m

/-- The familiar referents a context entails to have a descriptive content. -/
def candidates (C : State W V M) (desc : W → M → Prop) : Set V :=
  {k | State.Familiar C k ∧ Entails C desc k}

/-- A referent is informationally unique for a descriptive content in a context when it is the
iota of the familiar referents the context entails to have the content (32). -/
def InformationallyUnique (C : State W V M) (desc : W → M → Prop) (i : V) : Prop :=
  i ∈ iota (candidates C desc)

/-- A referent is informationally unique when it is familiar and entailed to have the content,
and every familiar referent entailed to have the content is that referent (32). -/
theorem informationallyUnique_iff :
    InformationallyUnique C desc i ↔
      (State.Familiar C i ∧ Entails C desc i) ∧
        ∀ k, State.Familiar C k ∧ Entails C desc k → k = i :=
  mem_iota

/-! ### Heim's Familiarity Condition -/

-- At a familiar referent, a context supports the update by a content at that referent exactly
-- when it entails the content of the referent.
theorem supports_atomAt_iff (h : State.Familiar C i) :
    (FCP.ofState (State.atomAt i desc)).supports C ↔ Entails C desc i := by
  rw [PartialUpdate.supports_iff_mem, FCP.ofState_apply, Part.mem_some_iff, State.mul_atomAt,
    h.mul_stratum_singleton, eq_comm]
  exact Set.sep_eq_self_iff_mem_true

/-- An informationally unique referent meets Heim's Familiarity Condition, the first clause of
(32) (p. 310). -/
theorem admits_def_of_informationallyUnique (h : InformationallyUnique C desc i) :
    (FCP.def_ i (FCP.ofState (State.atomAt i desc))).Admits C :=
  let ⟨⟨hfam, hent⟩, _⟩ := informationallyUnique_iff.1 h
  (FCP.admits_def_ _).2 ⟨hfam, (supports_atomAt_iff hfam).2 hent⟩

/-! ### Two strange men (33), (35) -/

/-- The two strange men of (33) and (35). -/
inductive Man where
  /-- The strange man who lives here. -/
  | here
  /-- The strange man who lives down the block. -/
  | downTheBlock
  deriving DecidableEq

/-- The point after *A strange man lives here, and another one lives down the block*, with
referent 0 for the man here and 1 for the man down the block. -/
def strangeMenPoint : Possibility Unit ℕ (Part Man) :=
  ⟨(), fun n ↦
    if n = 0 then Part.some Man.here else if n = 1 then Part.some Man.downTheBlock else ⊥⟩

/-- The context of (33) and (35), whose only point is `strangeMenPoint`. -/
def strangeMenContext : State Unit ℕ Man :=
  ({strangeMenPoint} : Set (Possibility Unit ℕ (Part Man)))

private theorem mem_strangeMenContext {p : Possibility Unit ℕ (Part Man)} :
    p ∈ strangeMenContext ↔ p = strangeMenPoint :=
  Iff.rfl

/-- The content of *strange man*. -/
def strangeMan : Unit → Man → Prop := fun _ _ ↦ True

/-- The content of *strange man who lives here*. -/
def strangeManHere : Unit → Man → Prop := fun _ m ↦ m = .here

private theorem familiar_iff {k : ℕ} : State.Familiar strangeMenContext k ↔ k = 0 ∨ k = 1 := by
  simp only [State.Familiar, mem_strangeMenContext, forall_eq, strangeMenPoint]
  rcases k with _ | _ | k <;> simp [Part.bot_eq_none, Part.not_none_dom]

private theorem entails_iff {d : Unit → Man → Prop} {k : ℕ} :
    Entails strangeMenContext d k ↔
      (k = 0 ∧ d () .here) ∨ (k = 1 ∧ d () .downTheBlock) := by
  simp only [Entails, mem_strangeMenContext, forall_eq, strangeMenPoint]
  rcases k with _ | _ | k <;> simp [Part.bot_eq_none, Part.notMem_none]

/-- Familiarity admits *the strange man* beside a second strange man, but no referent is
informationally unique for it, while *the strange man who lives here* is, as the judgments on
(35) and (33) have it. -/
theorem strangeMen :
    (FCP.def_ 0 (FCP.ofState (State.atomAt 0 strangeMan))).Admits strangeMenContext ∧
      ((∃ i, InformationallyUnique strangeMenContext strangeMan i) ↔
        Examples.two_strange_men.judgment = .acceptable) ∧
      (InformationallyUnique strangeMenContext strangeManHere 0 ↔
        Examples.enriched_definite.judgment = .acceptable) := by
  have h0 : State.Familiar strangeMenContext 0 := familiar_iff.2 (.inl rfl)
  refine ⟨(FCP.admits_def_ _).2 ⟨h0, (supports_atomAt_iff h0).2 (entails_iff.2 (.inl ⟨rfl, ⟨⟩⟩))⟩,
    ⟨fun ⟨i, hi⟩ ↦ ?_, fun h ↦ absurd h (by decide)⟩, ⟨fun _ ↦ rfl, fun _ ↦ ?_⟩⟩
  · have hne : iota (candidates strangeMenContext strangeMan) = Part.none :=
      iota_eq_none_of_ne (e := 0) (e' := 1)
        ⟨familiar_iff.2 (.inl rfl), entails_iff.2 (.inl ⟨rfl, ⟨⟩⟩)⟩
        ⟨familiar_iff.2 (.inr rfl), entails_iff.2 (.inr ⟨rfl, ⟨⟩⟩)⟩ (by decide)
    exact absurd (hne ▸ hi : i ∈ (Part.none : Part ℕ)) (Part.notMem_none _)
  · refine informationallyUnique_iff.2 ⟨⟨h0, entails_iff.2 (.inl ⟨rfl, rfl⟩)⟩, ?_⟩
    rintro k ⟨-, hk⟩
    rcases entails_iff.1 hk with ⟨rfl, -⟩ | ⟨-, h⟩
    · rfl
    · exact absurd h (by simp [strangeManHere])

/-! ### Pronouns (50) -/

/-- A pronoun at referent `i` with the content of its person, number and gender presupposes that
`i` is salient and entailed to have the content, and that every salient referent at least as
salient as `i` and entailed to have the content is `i` (50); `r k i` reads *`k` is at least as
salient as `i`*. -/
def PronounPresupposes (C : State W V M) (desc : W → M → Prop) (sal : Set V)
    (r : V → V → Prop) (i : V) : Prop :=
  (i ∈ sal ∧ Entails C desc i) ∧ ∀ k ∈ sal, r k i → Entails C desc k → k = i

/-- A pronoun's presupposition is the iota over the salient referents entailed to have its
content and at least as salient as its antecedent. -/
theorem pronounPresupposes_iff_iota {sal : Set V} {r : V → V → Prop} (hr : r i i) :
    PronounPresupposes C desc sal r i ↔
      i ∈ iota ({k ∈ sal | Entails C desc k} ∩ {k | r k i}) := by
  rw [mem_iota]
  exact ⟨fun ⟨hi, h⟩ ↦ ⟨⟨hi, hr⟩, fun k ⟨⟨hk, hd⟩, hki⟩ ↦ h k hk hki hd⟩,
    fun ⟨⟨hi, _⟩, h⟩ ↦ ⟨hi, fun k hk hki hd ↦ h k ⟨⟨hk, hd⟩, hki⟩⟩⟩

/-- With every familiar referent salient and all equally salient, a pronoun's presupposition is a
definite's. -/
theorem pronounPresupposes_top_iff :
    PronounPresupposes C desc {k | State.Familiar C k} (fun _ _ ↦ True) i ↔
      InformationallyUnique C desc i := by
  rw [informationallyUnique_iff]
  exact ⟨fun ⟨hi, h⟩ ↦ ⟨hi, fun k ⟨hk, hd⟩ ↦ h k hk trivial hd⟩,
    fun ⟨hi, h⟩ ↦ ⟨hi, fun k hk _ hd ↦ h k ⟨hk, hd⟩⟩⟩

end Roberts2003
