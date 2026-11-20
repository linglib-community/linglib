module

public import Linglib.Data.Examples.ThomsEtAl2026
public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.SyntacticObject.Extend
public import Linglib.Syntax.Minimalist.Spine
public import Mathlib.Basic.Real.Basic
public import Studies.ArregiPietraszko2021
public import Studies.Myler2016

/-!
# Thoms, Adger, Heycock, Jamieson and Smith (2026): HAVE-raising and predicative possession

This file formalizes the two structures that [thoms-etal-2026] give possessive HAVE. In the
existential structure the possessor raises out of the possessee to the specifier of v; in the
locative structure an applicative head relates the two. The probe on v finds the possessor exactly
when the possessee has no D layer (`extracts_iff`), so the existential structure takes only
possessees with a weak determiner.

A variety is a rule that pronounces the span of HAVE at one of its heads, and HAVE is raised when
that head is T. Group A raises HAVE in the existential structure alone, hence with exactly the
possessees of *there*-existentials (`generates_groupA_iff_extractable`). Where the position of
HAVE does not show, all varieties agree (`generates_iff_of_not_raised`). A learner who keeps a
raising rule from a threshold of unambiguous input on loses it for the locative structure first
(`raises_acquired_existential`).

## Implementation notes

* The possessee is the spine `[n, Poss, Num]` with or without `D`, and its tree is the noun
  extended by the heads above it, with the possessor above Poss.
* The locative structure is restricted to alienable relations, and an amount phrase with *the*
  counts as weak, both as in the paper. The animacy of the possessor is not modelled.
* A row attributed to a group is checked against that group's rule, and a row given for English
  generally against all three.
* The paper leaves the implementation of its spell-out rules open. With the Head Chain
  Pronunciation of [arregi-pietraszko-2021] a strong applicative head gives Group A's raising
  (`pronounced_strong_appl_eq_T_iff`), with the applicative as the low position; no choice of
  strong heads makes that position v (`not_pronounced_v_and_T`).

## TODO

* The realization of v as HAVE when it attracts a DP with φ-features and as BE otherwise.
* The Scots Syntax Atlas ratings by age group and region.
* Modal, epistemic and light-verb HAVE, whose spans the paper does not draw.

## References

* [thoms-etal-2026]
* [myler-2016]
* [arregi-pietraszko-2021]
* [kayne-1993]
* [nelson-2004]
-/

@[expose] public section

namespace ThomsEtAl2026

open Minimalist Minimalist.PlanarSyntacticObject ArregiPietraszko2021

/-! ### The size of the possessee -/

/-- The definite article, demonstratives, possessives and strong quantifiers are introduced in the
D layer; *any*, *much* and the article of an amount phrase are introduced below it. -/
def Examples.Determiner.NeedsD : Examples.Determiner → Prop
  | .the | .that | .your | .every | .most => True
  | .any | .much | .amountThe => False

instance : DecidablePred Examples.Determiner.NeedsD := fun d ↦ by
  cases d <;> unfold Examples.Determiner.NeedsD <;> infer_instance

/-- The nominal predicate of (38), a possessed noun phrase up to its number head. -/
def numP : Spine := ⟨[.n, .Poss, .Num]⟩

/-- The full noun phrase, the nominal predicate under D. -/
def dP : Spine := numP.append [.D]

theorem dP_isExtendedProjection : dP.IsExtendedProjection := by decide +kernel

theorem numP_le_dP : numP ≤ dP := numP.le_append _

/-- The sizes a nominal with the determiner may have: a full DP, and also a NumP when the
determiner does not need the D layer. -/
def sizes (d : Examples.Determiner) : List Spine := if d.NeedsD then [dP] else [numP, dP]

/-! ### Raising out of the nominal -/

/-- The light verb, whose probe searches for a D. -/
def v₀ : LexicalItem.Token := ⟨.of .v [], 100⟩

/-- The phrase in the specifier of Poss, the possessor or *there*. -/
def specifier : LexicalItem.Token := ⟨.of .D [], 101⟩

/-- The noun at the foot of the nominal. -/
def noun : LexicalItem.Token := ⟨.of .n [], 0⟩

/-- The tree of a nominal with spine `s`: the heads above the noun merge in turn, and the
specifier merges above Poss, as in (38). -/
def nominal (s : Spine) : PlanarSyntacticObject :=
  (PlanarSyntacticObject.leaf noun).extend .n 1
    (fun i ↦ if (s.above .n)[i]? = some .Poss then some (.leaf specifier) else none) (s.above .n)

/-- The φ-probe of v, merged with a nominal of spine `s`, finds the specifier of Poss. -/
def Extracts (s : Spine) : Prop :=
  let t : PlanarSyntacticObject := {.leaf v₀, nominal s}
  ↑specifier ∈ t.goals (t.leafProbe .D) ↑v₀

instance (s : Spine) : Decidable (Extracts s) := by unfold Extracts; infer_instance

/-- The probe of v finds the specifier of Poss exactly when the nominal has no D layer: the D of
a full DP is a closer goal. -/
theorem extracts_iff : ∀ s ∈ [numP, dP], Extracts s ↔ .D ∉ s := by decide

/-- The specifier of a nominal with the determiner can be raised: the nominal has a size that
`Extracts` it. -/
def Extractable (d : Examples.Determiner) : Prop := ∃ s ∈ sizes d, Extracts s

theorem extractable_iff {d : Examples.Determiner} : Extractable d ↔ ¬ d.NeedsD := by
  cases d <;> simp [Extractable, sizes, Examples.Determiner.NeedsD, extracts_iff] <;> decide

instance : DecidablePred Extractable := fun _ ↦ decidable_of_iff _ extractable_iff.symm

/-! ### The two structures -/

/-- The existential structure (38), where the possessor raises out of the possessee, and the
locative structure (44), where an applicative head relates them. -/
inductive Structure where
  | existential
  | locative
  deriving DecidableEq, Repr, Fintype

namespace Structure

/-- The head chain of HAVE in each structure, (53) and (54). -/
def chain : Structure → HeadChain
  | existential => .ofHeads .v [.T]
  | locative => .ofHeads .Appl [.v, .T]

/-- The span of HAVE, the heads from the foot of its chain to T. -/
def span (σ : Structure) : Spine := ⟨σ.chain.positions⟩

theorem span_injective : Function.Injective span := by decide

theorem exists_iff {p : Structure → Prop} : (∃ σ, p σ) ↔ p existential ∨ p locative :=
  ⟨fun ⟨σ, h⟩ ↦ by cases σ <;> simp [h], fun h ↦ h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩

/-- A structure derives a possessee with the determiner in the relation: the existential one when
the possessor can be raised, the locative one when the relation is alienable. -/
def Derives : Structure → Examples.Determiner → Examples.Relation → Prop
  | existential, d, _ => Extractable d
  | locative, _, r => r = .alienable

instance (σ : Structure) (d : Examples.Determiner) (r : Examples.Relation) :
    Decidable (σ.Derives d r) := by
  cases σ <;> unfold Derives <;> infer_instance

end Structure

/-! ### Varieties -/

/-- Group B pronounces every span of HAVE at T. -/
def groupB : Spine → Cat := fun _ ↦ .T

/-- (55): Group A pronounces a span at T unless it contains the applicative, and then at v. -/
def groupA : Spine → Cat := fun s ↦ if .Appl ∈ s then .v else .T

/-- The standard variety pronounces every span of HAVE at v. -/
def standard : Spine → Cat := fun _ ↦ .v

variable {g : Spine → Cat} {σ : Structure} {f : Examples.Frame} {d : Examples.Determiner}
  {r : Examples.Relation}

/-- A variety raises HAVE in a structure when it pronounces the span of the structure at T. -/
def Raises (g : Spine → Cat) (σ : Structure) : Prop := g σ.span = .T

instance : Decidable (Raises g σ) := inferInstanceAs (Decidable (_ = _))

/-- HAVE stands before negation or the subject. -/
def Examples.Frame.Raised : Examples.Frame → Prop
  | .raisedNegation | .raisedQuestion => True
  | .plain | .haveGot | .doSupport | .thereBe => False

instance : DecidablePred Examples.Frame.Raised := fun f ↦ by
  cases f <;> unfold Examples.Frame.Raised <;> infer_instance

/-- A variety generates a HAVE clause when a structure derives its possessee and, if the clause
shows HAVE raised, the variety raises HAVE in that structure. -/
def Generates (g : Spine → Cat) (f : Examples.Frame) (d : Examples.Determiner)
    (r : Examples.Relation) : Prop :=
  ∃ σ : Structure, σ.Derives d r ∧ (f.Raised → Raises g σ)

instance : Decidable (Generates g f d r) := inferInstanceAs (Decidable (∃ _, _))

/-- A clause that does not show the position of HAVE is generated alike in every variety. -/
theorem generates_iff_of_not_raised (g : Spine → Cat) (hf : ¬ f.Raised) :
    Generates g f d r ↔ ¬ d.NeedsD ∨ r = .alienable := by
  simp [Generates, Structure.exists_iff, hf, Structure.Derives,
    extractable_iff]

/-- Group A generates HAVE-raising with exactly the possessees whose specifier can be raised, the
pivots of *there*-existentials. -/
theorem generates_groupA_iff_extractable (hf : f.Raised) :
    Generates groupA f d r ↔ Extractable d := by
  cases r <;> simp [Generates, Structure.exists_iff, hf, Structure.Derives,
    Raises, groupA, Structure.span, Structure.chain, HeadChain.ofHeads]

-- (34)
theorem generates_groupB_iff : Generates groupB f d r ↔ ¬ d.NeedsD ∨ r = .alienable := by
  simp [Generates, Structure.exists_iff, Structure.Derives, Raises, groupB,
    extractable_iff]

theorem not_generates_standard (hf : f.Raised) : ¬ Generates standard f d r := by
  simp [Generates, hf, Raises, standard]

/-- The judgment of a row is the one the variety predicts: an existential is accepted when its
pivot's specifier can be raised, a HAVE clause when the variety generates it. -/
def Predicted (g : Spine → Cat) (x : Datum) : Prop :=
  match Examples.frame x, Examples.determiner x, Examples.relation x with
  | some .thereBe, some d, _ => x.judgment = .acceptable ↔ Extractable d
  | some f, some d, some r => x.judgment = .acceptable ↔ Generates g f d r
  | _, _, _ => False

instance (x : Datum) : Decidable (Predicted g x) := by unfold Predicted; split <;> infer_instance

/-- The varieties a row is judged in: the group it is attributed to, or all three. -/
def varieties (x : Datum) : List (Spine → Cat) :=
  match Examples.group x with
  | some .a => [groupA]
  | some .b => [groupB]
  | none => [groupA, groupB, standard]

theorem rows_predicted : ∀ x ∈ Examples.all, ∀ g ∈ varieties x, Predicted g x := by
  decide +kernel

/-! ### Head Chain Pronunciation -/

theorem pronounced_strong_appl_eq_T_iff :
    σ.chain.pronounced {.Appl} = some .T ↔ Raises groupA σ := by
  cases σ <;> decide

theorem pronounced_empty_eq_T : σ.chain.pronounced ∅ = some .T := by
  cases σ <;> decide

-- No choice of strong heads pronounces the locative chain at v and the existential chain at T.
theorem not_pronounced_v_and_T (strong : Finset Cat) :
    ¬ (Structure.locative.chain.pronounced strong = some .v ∧
      Structure.existential.chain.pronounced strong = some .T) := by
  by_cases hA : Cat.Appl ∈ strong <;> by_cases hv : Cat.v ∈ strong <;>
    by_cases hT : Cat.T ∈ strong <;>
    simp [Structure.chain, HeadChain.pronounced, HeadChain.ofHeads, List.filter, hA, hv, hT]

/-! ### The uniform HAVE of Myler -/

/-- In [myler-2016] every context that spells v out as *have* has the same Voice, so a rule that
reads Voice cannot tell two HAVE clauses apart, while the spans of the two structures differ
(`Structure.span_injective`). -/
theorem myler_have_voice_eq {c c' : Myler2016.Context}
    (h : Myler2016.spellout Myler2016.englishItems c = some "have")
    (h' : Myler2016.spellout Myler2016.englishItems c' = some "have") :
    c.voiceD = c'.voiceD ∧ c.voicePhi = c'.voicePhi := by
  obtain ⟨hD, hφ⟩ := (Myler2016.have_iff_transitive c).1 h
  obtain ⟨hD', hφ'⟩ := (Myler2016.have_iff_transitive c').1 h'
  exact ⟨hD.trans hD'.symm, hφ.trans hφ'.symm⟩

/-! ### The loss of raising -/

open Classical in
/-- The rule a learner acquires from `n` clauses with HAVE raised, when a share `rate σ` of them
is derived by structure `σ` alone and a rule is kept from `θ` such clauses on: the span of a
structure is pronounced at T when its evidence reaches the threshold. -/
noncomputable def acquired (θ n : ℝ) (rate : Structure → ℝ) : Spine → Cat := fun s ↦
  if ∃ σ : Structure, σ.span = s ∧ θ ≤ rate σ * n then .T else .v

variable {θ n : ℝ} {rate : Structure → ℝ}

theorem raises_acquired_iff : Raises (acquired θ n rate) σ ↔ θ ≤ rate σ * n := by
  simp [Raises, acquired, Structure.span_injective.eq_iff]

/-- With unambiguous evidence rarer for the locative structure, a learner who raises HAVE there
raises it in the existential structure. -/
theorem raises_acquired_existential (hn : 0 ≤ n) (h : rate .locative ≤ rate .existential)
    (hl : Raises (acquired θ n rate) .locative) : Raises (acquired θ n rate) .existential :=
  raises_acquired_iff.2 ((raises_acquired_iff.1 hl).trans (mul_le_mul_of_nonneg_right h hn))

-- (35): some amount of input yields the rule of Group A.
theorem exists_acquired_eq_groupA (hθ : 0 < θ) (h0 : 0 ≤ rate .locative)
    (h : rate .locative < rate .existential) :
    ∃ n, 0 ≤ n ∧ ∀ σ, Raises (acquired θ n rate) σ ↔ Raises groupA σ := by
  have he : 0 < rate .existential := h0.trans_lt h
  refine ⟨θ / rate .existential, (div_pos hθ he).le, fun σ ↦ ?_⟩
  rw [raises_acquired_iff]
  cases σ
  · simpa [Raises, groupA, Structure.span, Structure.chain, HeadChain.ofHeads] using
      (mul_div_cancel₀ θ he.ne').ge
  · have : rate .locative * (θ / rate .existential) < θ := by
      rw [← mul_div_assoc, div_lt_iff₀ he, mul_comm]
      exact mul_lt_mul_of_pos_left h hθ
    simpa [Raises, groupA, Structure.span, Structure.chain, HeadChain.ofHeads] using this

end ThomsEtAl2026
