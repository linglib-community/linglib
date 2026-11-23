module

public import Linglib.Semantics.Dynamic.FileChange
public import Linglib.Semantics.Reference.Iota
public import Linglib.Data.Examples.Roberts2003

/-!
# Roberts (2003): Uniqueness in definite noun phrases

A definite noun phrase presupposes an antecedent discourse referent that is weakly familiar and
informationally unique: of the referents in the domain of the context, it is the only one the
context entails to have the definite's descriptive content. A context is a file, its domain and
its satisfaction set, and the referents in the domain that it entails to have a content `desc`
are the `k` with `C ≤ File.atomAt k desc` (`mem_candidates_iff`). Heim's Familiarity Condition
asks that the definite's referent be one of them (`admits_definite_iff_mem_candidates`), and
informational uniqueness that it be the only one (`informationallyUnique_iff`), so the first
alone admits *the strange man* beside a second strange man (`strangeMen`). A pronoun's
presupposition takes the iota over the referents at least as salient as its antecedent, and with
every referent of the domain equally salient it is the definite's (`pronounPresupposes_top_iff`).

## Implementation notes

* A context ⟨Dom, Sat⟩ (31) is a `DynamicSemantics.File`. Weak familiarity is membership in the
  domain, whether the referent was introduced by mention, acquaintance or contextual entailment,
  so it needs no predicate of its own.
* The salience order of (50) is a relation `r` on referents, `r k i` reading *`k` is at least as
  salient as `i`*.

## References

* [roberts-2003]
* [heim-1982]
-/

@[expose] public section

namespace Roberts2003

open DynamicSemantics

variable {W V M : Type*} {C : File W V M} {desc : W → M → Prop} {i k : V}

/-! ### The presupposition of a definite (32) -/

/-- A context entails of a referent that it has a descriptive content when every point of its
satisfaction set assigns the referent a value with that content at its world. -/
def Entails (C : File W V M) (desc : W → M → Prop) (k : V) : Prop :=
  ∀ p ∈ C.sat, desc p.world (p.assignment k)

/-- The referents in the domain of a context that it entails to have a descriptive content. -/
def candidates (C : File W V M) (desc : W → M → Prop) : Set V :=
  {k | k ∈ C.dom ∧ Entails C desc k}

/-- A referent is informationally unique for a descriptive content in a context when it is the
iota of the referents in the domain that the context entails to have the content (32). -/
def InformationallyUnique (C : File W V M) (desc : W → M → Prop) (i : V) : Prop :=
  i ∈ iota (candidates C desc)

-- The candidates are the referents whose content file the context lies below.
theorem mem_candidates_iff : k ∈ candidates C desc ↔ C ≤ File.atomAt k desc :=
  File.le_atomAt_iff.symm

/-- A referent is informationally unique when it is in the domain and entailed to have the
content, and every referent in the domain entailed to have the content is that referent (32). -/
theorem informationallyUnique_iff :
    InformationallyUnique C desc i ↔
      (i ∈ C.dom ∧ Entails C desc i) ∧ ∀ k, k ∈ C.dom ∧ Entails C desc k → k = i :=
  mem_iota

/-! ### Heim's Familiarity Condition -/

/-- Heim's Familiarity Condition, the first clause of (32), holds of the referents in the domain
that the context entails to have the content (p. 310). -/
theorem admits_definite_iff_mem_candidates :
    (FCP.definite i (FCP.ofFile (File.atomAt i desc))).Admits C ↔ i ∈ candidates C desc :=
  FCP.admits_definite_atomAt.trans mem_candidates_iff.symm

theorem admits_definite_of_informationallyUnique (h : InformationallyUnique C desc i) :
    (FCP.definite i (FCP.ofFile (File.atomAt i desc))).Admits C :=
  admits_definite_iff_mem_candidates.2 (informationallyUnique_iff.1 h).1

/-! ### Two strange men (33), (35) -/

/-- The two strange men of (33) and (35). -/
inductive Man where
  /-- The strange man who lives here. -/
  | here
  /-- The strange man who lives down the block. -/
  | downTheBlock
  deriving DecidableEq

/-- The context after *A strange man lives here, and another one lives down the block*, with
referent 0 for the man here and 1 for the man down the block. -/
def strangeMenContext : File Unit ℕ Man where
  dom := {0, 1}
  sat := {p | p.assignment 0 = .here ∧ p.assignment 1 = .downTheBlock}
  mem_sat_of_agreeOn _ _ h hp :=
    ⟨(h.eqOn (.inl rfl)).symm.trans hp.1, (h.eqOn (.inr rfl)).symm.trans hp.2⟩

/-- The content of *strange man*. -/
def strangeMan : Unit → Man → Prop := fun _ _ ↦ True

/-- The content of *strange man who lives here*. -/
def strangeManHere : Unit → Man → Prop := fun _ m ↦ m = .here

/-- Familiarity admits *the strange man* beside a second strange man, but no referent is
informationally unique for it, while *the strange man who lives here* is, as the judgments on
(35) and (33) have it. -/
theorem strangeMen :
    (FCP.definite 0 (FCP.ofFile (File.atomAt 0 strangeMan))).Admits strangeMenContext ∧
      ((∃ i, InformationallyUnique strangeMenContext strangeMan i) ↔
        Examples.two_strange_men.judgment = .acceptable) ∧
      (InformationallyUnique strangeMenContext strangeManHere 0 ↔
        Examples.enriched_definite.judgment = .acceptable) := by
  have h0 : 0 ∈ candidates strangeMenContext strangeMan := ⟨.inl rfl, fun _ _ ↦ trivial⟩
  have h1 : 1 ∈ candidates strangeMenContext strangeMan := ⟨.inr rfl, fun _ _ ↦ trivial⟩
  refine ⟨admits_definite_iff_mem_candidates.2 h0,
    ⟨fun ⟨i, hi⟩ ↦ ?_, fun h ↦ absurd h (by decide)⟩, ⟨fun _ ↦ rfl, fun _ ↦ ?_⟩⟩
  · have hne : iota (candidates strangeMenContext strangeMan) = Part.none :=
      iota_eq_none_of_ne (e := 0) (e' := 1) h0 h1 (by decide)
    exact absurd (hne ▸ hi : i ∈ (Part.none : Part ℕ)) (Part.notMem_none _)
  · refine informationallyUnique_iff.2 ⟨⟨.inl rfl, fun _ hp ↦ hp.1⟩, ?_⟩
    rintro k ⟨rfl | rfl, hk⟩
    · rfl
    · have hp : (⟨(), fun n ↦ if n = 0 then .here else .downTheBlock⟩ :
          Possibility Unit ℕ Man) ∈ strangeMenContext.sat := ⟨rfl, rfl⟩
      exact absurd (hk _ hp) (by simp [strangeManHere])

/-! ### Pronouns (50) -/

/-- A pronoun at referent `i` with the content of its person, number and gender presupposes that
`i` is salient and entailed to have the content, and that every salient referent at least as
salient as `i` and entailed to have the content is `i` (50); `r k i` reads *`k` is at least as
salient as `i`*. -/
def PronounPresupposes (C : File W V M) (desc : W → M → Prop) (sal : Set V)
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

/-- With every referent of the domain salient and all equally salient, a pronoun's
presupposition is a definite's. -/
theorem pronounPresupposes_top_iff :
    PronounPresupposes C desc C.dom (fun _ _ ↦ True) i ↔ InformationallyUnique C desc i := by
  rw [informationallyUnique_iff]
  exact ⟨fun ⟨hi, h⟩ ↦ ⟨hi, fun k ⟨hk, hd⟩ ↦ h k hk trivial hd⟩,
    fun ⟨hi, h⟩ ↦ ⟨hi, fun k hk _ hd ↦ h k ⟨hk, hd⟩⟩⟩

end Roberts2003
