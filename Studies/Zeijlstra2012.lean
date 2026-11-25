module

public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Minimalist.Phase.Basic
public import Linglib.Syntax.Minimalist.Probe.Minimal

/-!
# Zeijlstra (2012): There Is Only One Way to Agree

This file formalizes [zeijlstra-2012]'s proposal that Agree applies upward only: an element
carrying an uninterpretable feature is checked by the closest c-commanding element carrying the
matching interpretable feature (`IsUpwardGoalIn`), reversing the direction of
[chomsky-2000]'s Agree, and several such elements may be checked by one goal at once
(`MultipleAgree`). The evidence is the concord phenomena, Negative Concord and Sequence of
Tense, whose configurations place one interpretable feature above one or more uninterpretable
ones. In Sequence of Tense, an abstract past operator carries `[iPAST]` and every finite past
morpheme, the matrix verb included, carries a vacuous `[uPAST]`; the matrix and the subordinate
verb of *John said Mary was ill* both Agree upward with the operator (`sot_multipleAgree`),
which no downward-probing Agree could establish (`sot_not_downward`). Agree across a phase
boundary requires the phase edge to participate: the corollary of phase theory that
distinguishes the two phenomena, since the embedding complementizer carries an uninterpretable
tense feature but no uninterpretable negative feature, so Sequence of Tense crosses the
clause boundary (`sot_licit`) while Negative Concord does not (`nc_across_cp_illicit`,
`nc_clausemate_licit`).

## Implementation notes

* Feature bearers are given by predicates on the leaves of a syntactic object, as the paper
  annotates its bracketings; the lexical items themselves carry only categories and selection.
* Upward Agree is the probe's search (`Probe.Finds`) over the elements c-commanding it, with
  closeness the dual of depth, so that the closest is the lowest.
* The phase-edge condition is stated for a phase head leaf through the substrate's phase
  domains: when the probe lies in the phase interior and the goal outside the phase, some
  element of the phase edge must carry the uninterpretable feature.
* The subordinate verb selects its subject as well as its predicate, so that the clause is a
  constituent the complementizer selects and projects over; the paper's bracketings leave the
  subject's position open.
* The semantics of the subordinate past morpheme as a relative non-future, which the paper
  leaves to later work, is not formalized.

## References

* [zeijlstra-2012]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Zeijlstra2012

open Minimalist Minimalist.SyntacticObject


/-! ### Upward Agree -/

/-- The depth of `x` in `root`, the number of its terms that contain `x`. -/
def depthIn (root x : SyntacticObject TokenLeaf) : ℕ := (root.terms.filter (Contains · x)).card

/-- The domain of upward Agree, the terms c-commanding the probe. -/
def upwardDomain (root probe : SyntacticObject TokenLeaf) : Set (SyntacticObject TokenLeaf) :=
  {x | x ∈ root.terms ∧ CCommands root x probe}

/-- In upward Agree, `goal`, carrying the interpretable feature marked by `pred`, is what the
probe finds among its c-commanders, the lowest of those carrying the feature. -/
def IsUpwardGoalIn (root probe goal : SyntacticObject TokenLeaf)
    (pred : SyntacticObject TokenLeaf → Prop)
    [DecidablePred pred] : Prop :=
  (Probe.relativized pred).Finds (upwardDomain root probe) (OrderDual.toDual ∘ depthIn root) goal

instance (root probe goal : SyntacticObject TokenLeaf) (pred : SyntacticObject TokenLeaf → Prop)
    [DecidablePred pred] : Decidable (IsUpwardGoalIn root probe goal pred) :=
  decidable_of_iff ((goal ∈ root.terms ∧ CCommands root goal probe) ∧ (∀ x ∈ root.terms,
      CCommands root x probe → pred x → ¬ depthIn root goal < depthIn root x) ∧ pred goal) <| by
    simp [IsUpwardGoalIn, Probe.finds_iff, Probe.Inspects, upwardDomain, and_assoc]

/-- In Multiple Agree every probe in the list is checked by the same goal. -/
def MultipleAgree (root goal : SyntacticObject TokenLeaf)
    (probes : List (SyntacticObject TokenLeaf))
    (pred : SyntacticObject TokenLeaf → Prop) [DecidablePred pred] : Prop :=
  ∀ p ∈ probes, IsUpwardGoalIn root p goal pred

instance (root goal : SyntacticObject TokenLeaf) (probes : List (SyntacticObject TokenLeaf))
    (pred : SyntacticObject TokenLeaf → Prop) [DecidablePred pred] :
    Decidable (MultipleAgree root goal probes pred) :=
  inferInstanceAs (Decidable (∀ p ∈ probes, _))

/-- The phase-edge condition on Agree across a phase: with `ℓ` a phase head, a probe in the
phase interior may Agree with a goal outside the phase only if an element of the phase edge
carries the uninterpretable feature `uF` too. -/
def EdgeParticipates (root probe goal : SyntacticObject TokenLeaf)
    (uF : SyntacticObject TokenLeaf → Prop)
    (ℓ : LexicalItem.Token) : Prop :=
  probe ∈ root.phaseInterior raisingHead ℓ → goal ∉ root.phase raisingHead ℓ →
    ∃ e ∈ root.phaseEdge raisingHead ℓ, uF e

instance {uF : SyntacticObject TokenLeaf → Prop} [DecidablePred uF]
    (root probe goal : SyntacticObject TokenLeaf)
    (ℓ : LexicalItem.Token) : Decidable (EdgeParticipates root probe goal uF ℓ) :=
  have : Decidable (∃ e ∈ root.phaseEdge raisingHead ℓ, uF e) := Multiset.decidableExistsMultiset
  inferInstanceAs (Decidable (_ → _ → _))

/-! ### Sequence of Tense -/

/-- The abstract past operator carrying `[iPAST]`. -/
def opPast : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .T [.V] "Op[PAST]", 1⟩
def john : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .D [] "John", 2⟩
/-- The matrix verb, with its own vacuous `[uPAST]`. -/
def said : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .V [.C] "said", 3⟩
/-- The embedding complementizer, carrying `[uT]`. -/
def thatC : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .C [.V] "that", 4⟩
def mary : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .D [] "Mary", 5⟩
/-- The subordinate verb, with `[uPAST]`, selecting its predicate and its subject. -/
def was : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .V [.A, .D] "was", 6⟩
def ill : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .A [] "ill", 7⟩

/-- *John said Mary was ill*, with the past operator above both verbs. -/
def sot : PlanarSyntacticObject TokenLeaf :=
  {john, {opPast, {said, {thatC, {mary, {was, ill}}}}}}

/-- The bearers of `[iPAST]`. -/
def iPast (s : SyntacticObject TokenLeaf) : Prop := s = opPast

instance : DecidablePred iPast := fun s ↦ inferInstanceAs (Decidable (s = _))

/-- The bearers of `[uPAST]` or `[uT]` are both finite verbs and the complementizer. -/
def uPast (s : SyntacticObject TokenLeaf) : Prop := s = said ∨ s = was ∨ s = thatC

instance : DecidablePred uPast := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- A second past operator. -/
def opPast₂ : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .T [.V] "Op[PAST]", 30⟩

/-- Two past operators above a verb. -/
def twoOps : PlanarSyntacticObject TokenLeaf := {opPast, {opPast₂, {was, ill}}}

/-- The bearers of `[iPAST]` in `twoOps`. -/
def iPast₂ (s : SyntacticObject TokenLeaf) : Prop := s = opPast ∨ s = opPast₂

instance : DecidablePred iPast₂ := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Of two past operators above a verb, upward Agree checks the verb against the lower. -/
example : IsUpwardGoalIn twoOps was opPast₂ iPast₂ ∧ ¬ IsUpwardGoalIn twoOps was opPast iPast₂ := by
  decide

theorem sot_multipleAgree : MultipleAgree sot opPast [said, was] iPast := by decide

theorem sot_not_downward :
    ¬ CCommands sot said (opPast : SyntacticObject TokenLeaf) ∧
      ¬ CCommands sot was (opPast : SyntacticObject TokenLeaf) := by
  decide

theorem sot_licit :
    (sot : SyntacticObject TokenLeaf).WithinComplement raisingHead ⟨.of .C [.V] "that", 4⟩ was ∧
      ¬ (sot : SyntacticObject TokenLeaf).WithinProjection raisingHead
          ⟨.of .C [.V] "that", 4⟩ opPast ∧
      EdgeParticipates sot was opPast uPast ⟨.of .C [.V] "that", 4⟩ := by decide

/-! ### Negative Concord -/

def gianni : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .D [] "Gianni", 11⟩
/-- The negative marker carrying `[iNEG]`. -/
def non : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .Neg [.T] "non", 12⟩
def ha : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .T [.V] "ha", 13⟩
def detto : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .V [.D] "detto", 14⟩
def dettoC : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .V [.C] "detto", 15⟩
def niente : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .D [.P] "niente", 16⟩
def a : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .P [.D] "a", 17⟩
def nessuno : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .D [] "nessuno", 18⟩
/-- The embedding complementizer, without any negative feature. -/
def che : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .C [.T] "che", 19⟩
def ha₂ : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .T [.V] "ha", 20⟩
def telefonato : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of .V [.P] "telefonato", 21⟩

/-- *Gianni non ha detto niente a nessuno* has two n-words under one negative marker. -/
def ncClausemate : PlanarSyntacticObject TokenLeaf :=
  {gianni, {non, {ha, {detto, {niente, {a, nessuno}}}}}}

/-- *Gianni non ha detto che ha telefonato a nessuno* has the n-word inside an embedded
clause. -/
def ncAcrossCP : PlanarSyntacticObject TokenLeaf :=
  {gianni, {non, {ha, {dettoC, {che, {ha₂, {telefonato, {a, nessuno}}}}}}}}

/-- The bearers of `[iNEG]`. -/
def iNeg (s : SyntacticObject TokenLeaf) : Prop := s = non

instance : DecidablePred iNeg := fun s ↦ inferInstanceAs (Decidable (s = _))

/-- The bearers of `[uNEG]`, the n-words. -/
def uNeg (s : SyntacticObject TokenLeaf) : Prop := s = niente ∨ s = nessuno

instance : DecidablePred uNeg := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem nc_clausemate_multipleAgree : MultipleAgree ncClausemate non [niente, nessuno] iNeg := by
  decide

theorem nc_clausemate_licit :
    ∀ x ∈ (ncClausemate : SyntacticObject TokenLeaf).terms, x.cat? ≠ some .C := by decide

theorem nc_across_cp_illicit :
    ¬ EdgeParticipates ncAcrossCP nessuno non uNeg ⟨.of .C [.T] "che", 19⟩ := by decide

end Zeijlstra2012
