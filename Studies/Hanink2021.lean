module

public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Modification.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Person.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Data.Examples.Hanink2021
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Hanink (2021): DP Structure and Internally Headed Relatives in Washo

Hanink argues that an index is a syntactic head of its own, idx below D, which Washo pronounces
*gi ~ ge* in third-person pronouns (1), in demonstratives (2), and at the edge of internally
headed relative clauses (3), DPs over a nominalized CP (40). The index has two meanings (80). As
a variable it restricts D's ι to its antecedent (15), with the deixis of *hádi* and *wídi* a
presupposition on D (34). As a binder it turns the embedded clause, whose semantic head is a
restricted variable (69), into a property without movement, so the relative denotes what an
externally headed relative denotes by raising and Predicate Modification, (72) and (60). The
Prohibition against Vacuous Binding (86) leaves the binder meaning to complements with a free
variable, and the Vocabulary for idx (119) and D (130), with contextual specificity ranked above
the Elsewhere Principle (118), derives where *gi* is overt. The examples are the rows of
`Data.Examples.Hanink2021`, among them section 4's island-insensitivity and stacking and the
absence of the head's φ-features on idx (91), which makes its relation to the head binding
rather than Agree.

## Main results

* `denote_anaphoric_eq_iota`, `denote_demonstrative_eq_iota`: a familiar or demonstrative DP is
  D's ι over the restriction modified by the index as a variable.
* `idxBind_openClause`, `iota_idxBind`: the index as a binder yields the property and the
  referent of the externally headed relative.
* `idxBind_eq_const`: without a free occurrence of its index the binder binds nothing, which
  leaves a perception nominalization a familiar DP (106).
* `idxExponent_distribution`, `demonstrative_forms`: the Vocabulary derives the distribution of
  *gi ~ ge* and the demonstratives *hádigi* and *wídigi*.

## Implementation notes

The index is the substrate's assignment index, so the variable meaning is `idxVar` and the
binder meaning `lambdaAbsG`; D's ι is `iota`, whose `∃!` presupposition is (34a)'s.
The R head of demonstratives (35) is the identity relation, so it is not represented. Ellipsis
of a pronoun's NP is recorded as the complement lacking the feature that makes an NP overt
(section 6.3). The quantified heads of section 5.1 and the German relative-clause parallel of
section 4.4 are recorded as data and prose only. Hanink calls *wídi* proximal and *hádi* distal;
their deictic content is read as the two cells of Harbour's author bipartition, the participant
sets containing the speaker and the others.

## TODO

* Quantified heads (98) to (103), Matthewson's *all* over an index-hosting DP, and the
  relative-internal scope it predicts.

## References

* [hanink-2021]
* [schwarz-2009]
* [elbourne-2005]
* [heim-kratzer-1998]
* [kratzer-2009]
* [arregi-nevins-2012]
* [jacobsen-1964]
* [matthewson-2001]
-/

@[expose] public section

namespace Hanink2021

open Semantics Montague Reference DistributedMorphology Morphology.Exponence
open scoped Assignment

variable {E W : Type}

/-! ### The two meanings of the index, (80) -/

/-- The index as a variable, (80a) and (14), denotes the property of being its value. -/
def idxVar (n : ℕ) : Assignment E → E → Prop := fun g x ↦ x = g n

/-- The index as a binder, (80b), takes the open proposition of its complement to the property of
the values of the variable that verify it. It is the substrate's abstraction over `n`, achieved
without movement. -/
abbrev idxBind (n : ℕ) (φ : Assignment E → Prop) : Assignment E → E → Prop := lambdaAbsG n φ

/-- A familiar DP, D's ι over the restriction modified by the index as a variable ((15), (35b),
(97) and (106)), is the substrate's anaphoric description, which denotes the antecedent if it
satisfies the restriction. -/
theorem denote_anaphoric_eq_iota (R : Restrictor E W) (d : ℕ) (g : Assignment E) (s : W) :
    ⟦Description.anaphoric R d⟧ g s = iota (fun x ↦ R g s x ∧ idxVar d g x) := rfl

/-- The demonstrative D heads *hádi* and *wídi* of (34b) and (34c) add a deictic presupposition
and otherwise contribute ι, so a demonstrative refers as the anaphoric DP does. -/
theorem denote_demonstrative_eq_iota (R : Restrictor E W) (d : ℕ) (g : Assignment E) (s : W) :
    ⟦Description.demonstrative R d⟧ g s = iota (fun x ↦ R g s x ∧ idxVar d g x) :=
  rfl

/-! ### Internally headed relatives, section 4 -/

/-- The embedded clause of an internally headed relative, (69) and (70), is an open proposition
whose semantic head is the restricted variable `n`. The restriction `P` holds of the variable's
value, and the clause `ψ` says the rest of it. -/
def openClause (n : ℕ) (P : E → Prop) (ψ : Assignment E → Prop) : Assignment E → Prop :=
  fun g ↦ P (g n) ∧ ψ g

/-- The property (71) that the index yields by binding the restricted variable in situ is the
property (59) that an externally headed relative builds by abstracting over the trace and
intersecting with the head noun. -/
theorem idxBind_openClause (n : ℕ) (P : E → Prop) (ψ : Assignment E → Prop) (g : Assignment E) :
    idxBind n (openClause n P ψ) g = Modifier.intersective P (lambdaAbsG n ψ g) := by
  funext x
  simp only [idxBind, lambdaAbsG, openClause, Function.update_self, Modifier.intersective_apply]

/-- The silent D over the bound clause, (72), refers to what the definite over the externally
headed relative, (60), refers to, the same meaning reached by different steps. -/
theorem iota_idxBind (n : ℕ) (P : E → Prop) (ψ : Assignment E → Prop) (g : Assignment E) :
    iota (idxBind n (openClause n P ψ) g) =
      iota (Modifier.intersective P (lambdaAbsG n ψ g)) := by
  rw [idxBind_openClause]

/-- Without a free occurrence of the index, when `φ` depends only on the other indices, the
binder meaning is constant and binds nothing. The Prohibition against Vacuous Binding (86) then
leaves only the variable meaning, which is why a perception nominalization (106), a property of
events with no open variable, is a familiar DP. -/
theorem idxBind_eq_const {n : ℕ} {φ : Assignment E → Prop} (h : DependsOn φ {n}ᶜ)
    (g : Assignment E) : idxBind n φ g = fun _ ↦ φ g :=
  lambdaAbsG_eq_const_iff.2 h g

/-! ### The exponence of idx and D, section 6 -/

/-- The features Vocabulary Insertion reads at idx and D and on their complements are the index
head, dependent (accusative) case, the D head with its deixis, and the complement's category. The
complement is an overt NP, a CP, an RP, or a nominal under ellipsis, which lacks the phonological
features that make an NP overt (section 6.3). -/
inductive Feat where
  | idx | dep | np | cp | rp | elided
  | d | deixis (δ : Finset (Finset Discourse.Role))
  deriving DecidableEq

/-- The Vocabulary entries for idx, (119) and (131), are *gi* elsewhere, *ge* under dependent
case, and null before an overt NP. -/
def idxItems : RuleSet (VocabularyItem Feat String) :=
  [[Feat.idx] ⟷ "gi", [Feat.idx, .dep] ⟷ "ge", ⟨⟨[.idx], [], [[.np]]⟩, ""⟩]

/-- The Vocabulary entries for D, (130), are null elsewhere, *hádi* distal and *wídi* proximal,
the speaker's space. -/
def dItems : RuleSet (VocabularyItem Feat String) :=
  [[Feat.d] ⟷ "", [Feat.d, .deixis Person.first.participantSetsᶜ] ⟷ "hádi",
    [Feat.d, .deixis Person.first.participantSets] ⟷ "wídi"]

/-- Under (118), contextual specificity takes precedence over the Elsewhere Principle, the
ordering of [arregi-nevins-2012]. An item is ranked first by the features it demands of the
context and then by those it spells out. -/
def contextualSpecificity (i : VocabularyItem Feat String) : ℕ ×ₗ ℕ :=
  toLex ((i.site.leftCtx ++ i.site.rightCtx).flatten.length, i.site.focus.length)

/-- `idxExponent n` is the exponent of idx in the neighborhood `n`. -/
def idxExponent (n : Neighborhood (List Feat)) : Option String :=
  idxItems.realize contextualSpecificity n

/-- `dExponent n` is the exponent of D in the neighborhood `n`. -/
def dExponent (n : Neighborhood (List Feat)) : Option String :=
  dItems.realize contextualSpecificity n

/-- The exponent *gi ~ ge* is distributed as in (108) to (115) and (127) to (129). It is overt in
pronouns, whose NP is elided (113), at the edge of clausal nominalizations (114), and in
demonstratives, whose complement is RP (129), each alternating for case ((44), (45)). It is null
before the overt NP of an anaphoric bare definite (115), and still null under dependent case
(22), where the contextual entry outranks the case entry. -/
theorem idxExponent_distribution :
    idxExponent ⟨[.idx], [], [[.elided]]⟩ = some "gi" ∧
      idxExponent ⟨[.idx, .dep], [], [[.elided]]⟩ = some "ge" ∧
      idxExponent ⟨[.idx], [], [[.cp]]⟩ = some "gi" ∧
      idxExponent ⟨[.idx, .dep], [], [[.cp]]⟩ = some "ge" ∧
      idxExponent ⟨[.idx], [[.d, .deixis Person.first.participantSetsᶜ]], [[.rp]]⟩ = some "gi" ∧
      idxExponent ⟨[.idx], [], [[.np]]⟩ = some "" ∧
      idxExponent ⟨[.idx, .dep], [], [[.np]]⟩ = some "" := by
  decide

/-- Under the Elsewhere score alone the case entry and the contextual entry tie on the accusative
bare definite and vocabulary order decides for *ge*; the paper's ordering (118) is what makes
the null entry win. -/
theorem subsetPrinciple_accusative_bare :
    subsetPrinciple idxItems ⟨[.idx, .dep], [], [[.np]]⟩ = some "ge" := by
  decide

/-- The demonstratives *hádigi* and *wídigi* of (25) and (127) decompose as the D exponent
followed by the idx exponent. -/
theorem demonstrative_forms :
    (dExponent ⟨[.d, .deixis Person.first.participantSetsᶜ], [], [[.idx]]⟩).bind (fun a ↦
        (idxExponent ⟨[.idx], [[.d, .deixis Person.first.participantSetsᶜ]], [[.rp]]⟩).map
          (a ++ ·)) = some "hádigi" ∧
    (dExponent ⟨[.d, .deixis Person.first.participantSets], [], [[.idx]]⟩).bind (fun a ↦
        (idxExponent ⟨[.idx], [[.d, .deixis Person.first.participantSets]], [[.rp]]⟩).map
          (a ++ ·)) = some "wídigi" := by
  decide

end Hanink2021
