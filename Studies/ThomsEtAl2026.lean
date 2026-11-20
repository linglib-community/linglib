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
when the possessee has no D layer (`Structure.finds_iff`), so the existential structure takes only
possessees with a weak determiner.

A variety is a list of rules, each pronouncing a span of heads at one of them, and HAVE is raised
when its span is pronounced at T. Group A raises HAVE in the existential structure alone, hence
with exactly the possessees of *there*-existentials (`generates_groupA_iff_extractable`). Where
the position of HAVE does not show, all varieties agree (`generates_iff_of_not_raised`). A learner
who keeps a raising rule from a threshold of unambiguous input on loses it for the locative
structure first (`raises_acquired_existential`).

## Implementation notes

* The possessee is the spine `[n, Poss, Num]` with or without `D`. The tree of a structure is the
  noun extended by the heads of the complement of v, with the possessor in the specifier of Poss
  or of the applicative, and the span of HAVE is the verbal part of the clause's heads.
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

/-! ### The two structures -/

/-- The existential structure (38), where v takes the possessee, and the locative structure (44),
where v takes the phrase of an applicative head over the possessee. -/
inductive Structure where
  | existential
  | locative
  deriving DecidableEq, Repr, Fintype

/-- The light verb, whose probe searches for a D. -/
def v₀ : LexicalItem.Token := ⟨.of .v [], 100⟩

/-- The possessor, or *there* in an existential. -/
def specifier : LexicalItem.Token := ⟨.of .D [], 101⟩

/-- The noun at the foot of the possessee. -/
def noun : LexicalItem.Token := ⟨.of .n [], 0⟩

namespace Structure

/-- The heads between the possessee and v: none, or the applicative. -/
def shell : Structure → List Cat
  | existential => []
  | locative => [.Appl]

/-- The head whose specifier holds the possessor: the applicative when there is one, and Poss
inside the possessee otherwise. -/
def host (σ : Structure) : Cat := σ.shell.head?.getD .Poss

/-- The heads of the complement of v over a possessee with spine `s`, from the noun up. -/
def complement (σ : Structure) (s : Spine) : Spine := s.append σ.shell

/-- The phrase v projects, (38) and (44) below the specifier of v: the noun extended by the heads
of the complement, with the possessor in the specifier of its host, under v. -/
def tree (σ : Structure) (s : Spine) : PlanarSyntacticObject :=
  let above := (σ.complement s).above .n
  let complement := (PlanarSyntacticObject.leaf noun).extend .n 1
    (fun i ↦ if above[i]? = some σ.host then some (.leaf specifier) else none) above
  {.leaf v₀, complement}

/-- The φ-probe of v finds the possessor. -/
def Finds (σ : Structure) (s : Spine) : Prop :=
  ↑specifier ∈ (σ.tree s).goals ((σ.tree s).leafProbe .D) ↑v₀

instance (σ : Structure) (s : Spine) : Decidable (σ.Finds s) := by unfold Finds; infer_instance

/-- In the existential structure the probe of v finds the possessor exactly when the possessee
has no D layer, the D of a full DP being a closer goal; in the locative structure it finds the
possessor over a possessee of either size. -/
theorem finds_iff : ∀ σ : Structure, ∀ s ∈ [numP, dP],
    σ.Finds s ↔ σ = locative ∨ .D ∉ s := by
  decide

/-- The applicative head selects a DP; v takes a nominal of either size. -/
def Selects : Structure → Spine → Prop
  | existential, _ => True
  | locative, s => .D ∈ s

instance (σ : Structure) (s : Spine) : Decidable (σ.Selects s) := by
  cases σ <;> unfold Selects <;> infer_instance

/-- The span of HAVE, (53) and (54): the verbal heads of the clause, from the foot of the
complement of v to T. -/
def span (σ : Structure) : Spine :=
  ⟨(((σ.complement dP).append [.v, .T]).heads.filter (·.family = .verbal))⟩

@[simp] theorem span_existential : existential.span = ⟨[.v, .T]⟩ := by decide

@[simp] theorem span_locative : locative.span = ⟨[.Appl, .v, .T]⟩ := by decide

theorem span_injective : Function.Injective span := by decide

/-- The head chain of HAVE, the heads of its span sharing one M-value. -/
def chain (σ : Structure) : HeadChain :=
  .ofHeads (σ.span.heads.head?.getD .v) σ.span.heads.tail

theorem exists_iff {p : Structure → Prop} : (∃ σ, p σ) ↔ p existential ∨ p locative :=
  ⟨fun ⟨σ, h⟩ ↦ by cases σ <;> simp [h], fun h ↦ h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩

end Structure

/-- The specifier of a nominal with the determiner can be raised out of it: the nominal has a size
at which the probe of v finds it. -/
def Extractable (d : Examples.Determiner) : Prop := ∃ s ∈ sizes d, Structure.existential.Finds s

theorem extractable_iff {d : Examples.Determiner} : Extractable d ↔ ¬ d.NeedsD := by
  cases d <;> simp [Extractable, sizes, Examples.Determiner.NeedsD, Structure.finds_iff] <;>
    decide

instance : DecidablePred Extractable := fun _ ↦ decidable_of_iff _ extractable_iff.symm

/-- A structure derives a possessee with the determiner in the relation when the possessee has a
size that the structure selects and at which v finds the possessor; the applicative head moreover
relates the possessor to what it has with it, an alienable relation. -/
def Structure.Derives (σ : Structure) (d : Examples.Determiner) (r : Examples.Relation) : Prop :=
  (∃ s ∈ sizes d, σ.Selects s ∧ σ.Finds s) ∧ (σ = .locative → r = .alienable)

theorem Structure.derives_existential_iff {d : Examples.Determiner} {r : Examples.Relation} :
    Structure.existential.Derives d r ↔ ¬ d.NeedsD := by
  simpa [Structure.Derives, Structure.Selects, Extractable] using extractable_iff (d := d)

theorem Structure.derives_locative_iff {d : Examples.Determiner} {r : Examples.Relation} :
    Structure.locative.Derives d r ↔ r = .alienable := by
  cases d <;> simp [Structure.Derives, Structure.Selects, sizes, Examples.Determiner.NeedsD,
    Structure.finds_iff] <;> intro _ <;> decide

instance (σ : Structure) (d : Examples.Determiner) (r : Examples.Relation) :
    Decidable (σ.Derives d r) := by
  cases σ
  · exact decidable_of_iff _ Structure.derives_existential_iff.symm
  · exact decidable_of_iff _ Structure.derives_locative_iff.symm

/-! ### Varieties -/

/-- A spell-out rule pronounces the heads of a span at one of its positions. -/
structure Rule where
  /-- The heads the rule spells out. -/
  span : Spine
  /-- The position at which they are pronounced. -/
  site : Cat
  deriving DecidableEq

/-- Group B pronounces both spans of HAVE at T. -/
def groupB : List Rule := [⟨⟨[.v, .T]⟩, .T⟩, ⟨⟨[.Appl, .v, .T]⟩, .T⟩]

/-- (55): Group A pronounces the span of v and T at T and the span with the applicative at v. -/
def groupA : List Rule := [⟨⟨[.v, .T]⟩, .T⟩, ⟨⟨[.Appl, .v, .T]⟩, .v⟩]

/-- The standard variety pronounces both spans of HAVE at v. -/
def standard : List Rule := [⟨⟨[.v, .T]⟩, .v⟩, ⟨⟨[.Appl, .v, .T]⟩, .v⟩]

variable {g : List Rule} {σ : Structure} {f : Examples.Frame} {d : Examples.Determiner}
  {r : Examples.Relation}

/-- A variety raises HAVE in a structure when it has the rule that pronounces the span of the
structure at T. -/
def Raises (g : List Rule) (σ : Structure) : Prop := ⟨σ.span, .T⟩ ∈ g

instance : Decidable (Raises g σ) := inferInstanceAs (Decidable (_ ∈ _))

@[simp] theorem raises_groupA : Raises groupA σ ↔ σ = .existential := by cases σ <;> decide

@[simp] theorem raises_groupB : Raises groupB σ := by cases σ <;> decide

@[simp] theorem not_raises_standard : ¬ Raises standard σ := by cases σ <;> decide

/-- HAVE stands before negation or the subject. -/
def Examples.Frame.Raised : Examples.Frame → Prop
  | .raisedNegation | .raisedQuestion => True
  | .plain | .haveGot | .doSupport | .thereBe => False

instance : DecidablePred Examples.Frame.Raised := fun f ↦ by
  cases f <;> unfold Examples.Frame.Raised <;> infer_instance

/-- A variety generates a HAVE clause when a structure derives its possessee and, if the clause
shows HAVE raised, the variety raises HAVE in that structure. -/
def Generates (g : List Rule) (f : Examples.Frame) (d : Examples.Determiner)
    (r : Examples.Relation) : Prop :=
  ∃ σ : Structure, σ.Derives d r ∧ (f.Raised → Raises g σ)

instance : Decidable (Generates g f d r) := inferInstanceAs (Decidable (∃ _, _))

/-- A clause that does not show the position of HAVE is generated alike in every variety. -/
theorem generates_iff_of_not_raised (g : List Rule) (hf : ¬ f.Raised) :
    Generates g f d r ↔ ¬ d.NeedsD ∨ r = .alienable := by
  simp [Generates, Structure.exists_iff, hf, Structure.derives_existential_iff,
    Structure.derives_locative_iff]

/-- Group A generates HAVE-raising with exactly the possessees whose specifier can be raised, the
pivots of *there*-existentials. -/
theorem generates_groupA_iff_extractable (hf : f.Raised) :
    Generates groupA f d r ↔ Extractable d := by
  simp [Generates, hf, Structure.derives_existential_iff, extractable_iff]

-- (34)
theorem generates_groupB_iff : Generates groupB f d r ↔ ¬ d.NeedsD ∨ r = .alienable := by
  simp [Generates, Structure.exists_iff, Structure.derives_existential_iff,
    Structure.derives_locative_iff]

theorem not_generates_standard (hf : f.Raised) : ¬ Generates standard f d r := by
  simp [Generates, hf]

/-- The judgment of a row is the one the variety predicts: an existential is accepted when its
pivot's specifier can be raised, a HAVE clause when the variety generates it. -/
def Predicted (g : List Rule) (x : Datum) : Prop :=
  match Examples.frame x, Examples.determiner x, Examples.relation x with
  | some .thereBe, some d, _ => x.judgment = .acceptable ↔ Extractable d
  | some f, some d, some r => x.judgment = .acceptable ↔ Generates g f d r
  | _, _, _ => False

instance (x : Datum) : Decidable (Predicted g x) := by unfold Predicted; split <;> infer_instance

/-- The varieties a row is judged in: the group it is attributed to, or all three. -/
def varieties (x : Datum) : List (List Rule) :=
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
/-- The rules a learner acquires from `n` clauses with HAVE raised, when a share `rate σ` of them
is derived by structure `σ` alone and a raising rule is kept from `θ` such clauses on: the span of
a structure is pronounced at T when its evidence reaches the threshold, and at v otherwise. -/
noncomputable def acquired (θ n : ℝ) (rate : Structure → ℝ) : List Rule :=
  [Structure.existential, .locative].map fun σ ↦ ⟨σ.span, if θ ≤ rate σ * n then .T else .v⟩

variable {θ n : ℝ} {rate : Structure → ℝ}

theorem raises_acquired_iff : Raises (acquired θ n rate) σ ↔ θ ≤ rate σ * n := by
  cases σ <;> simp [Raises, acquired, Rule.mk.injEq]

/-- With unambiguous evidence rarer for the locative structure, a learner who raises HAVE there
raises it in the existential structure. -/
theorem raises_acquired_existential (hn : 0 ≤ n) (h : rate .locative ≤ rate .existential)
    (hl : Raises (acquired θ n rate) .locative) : Raises (acquired θ n rate) .existential :=
  raises_acquired_iff.2 ((raises_acquired_iff.1 hl).trans (mul_le_mul_of_nonneg_right h hn))

-- (35): some amount of input yields the rules of Group A.
theorem exists_acquired_eq_groupA (hθ : 0 < θ) (h0 : 0 ≤ rate .locative)
    (h : rate .locative < rate .existential) :
    ∃ n, 0 ≤ n ∧ acquired θ n rate = groupA := by
  have he : 0 < rate .existential := h0.trans_lt h
  have hl : ¬ θ ≤ rate .locative * (θ / rate .existential) := by
    rw [not_le, ← mul_div_assoc, div_lt_iff₀ he, mul_comm]
    exact mul_lt_mul_of_pos_left h hθ
  exact ⟨θ / rate .existential, (div_pos hθ he).le, by
    simp [acquired, groupA, hl, (mul_div_cancel₀ θ he.ne').ge]⟩

end ThomsEtAl2026
