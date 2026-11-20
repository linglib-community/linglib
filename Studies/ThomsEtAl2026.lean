module

public import Linglib.Data.Examples.ThomsEtAl2026
public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.SyntacticObject.Extend
public import Linglib.Syntax.Minimalist.SyntacticObject.Notation
public import Linglib.Syntax.Minimalist.Lexicon
public import Linglib.Syntax.Minimalist.Spine
public import Mathlib.Basic.Real.Basic
public import Studies.ArregiPietraszko2021
public import Studies.Myler2016
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Syntax.Minimalist.Probe.Minimal

/-!
# Thoms, Adger, Heycock, Jamieson and Smith (2026): HAVE-raising and predicative possession

This file formalizes the two structures that [thoms-etal-2026] give possessive HAVE, as trees. In
`existential` the possessor is in the specifier of Poss inside the possessee, and v raises it; in
`locative` an applicative head relates the two. Over a possessee with a D layer the probe of v
does not find the possessor of the existential structure (`not_finds_existential_dP`), so that
structure takes only possessees with a weak determiner. In both structures v copies the
φ-features of the possessor and is realized as HAVE; over *there*, which has none, it is BE
(`copula_eq`).

A variety is a list of rules, each pronouncing a span of heads at one of them, and HAVE is raised
when its span is pronounced at T. Group A raises HAVE over the span without the applicative alone,
hence with exactly the possessees of *there*-existentials (`generates_groupA_iff_extractable`).
Where the position of HAVE does not show, all varieties agree (`generates_iff_of_not_raised`). A
learner who keeps a raising rule from a threshold of unambiguous input on loses it for the span
with the applicative first (`raises_acquired_vT_of_applvT`).

## Implementation notes

* The possessee is the spine `[n, Poss, Num]` with or without `D`, built by
  `PlanarSyntacticObject.extend`. The span of HAVE is read off a tree as its verbal heads and T,
  which is right for these trees, whose arguments contain no verbal head.
* The locative structure is restricted to alienable relations, and an amount phrase with *the*
  counts as weak, both as in the paper. The animacy of the possessor is not modelled.
* A row attributed to a group is checked against that group's rules, and a row given for English
  generally against all three.
* The paper leaves the implementation of its spell-out rules open. With the Head Chain
  Pronunciation of [arregi-pietraszko-2021] a strong applicative head gives Group A's raising
  (`pronounced_strong_appl`), with the applicative as the low position; no choice of strong heads
  makes that position v (`not_pronounced_v_and_T`).

## TODO

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

/-- The words of the two structures beside the heads of the possessee. -/
lexicon tokens from 100 where
  /-- The light verb, whose probe searches for a D. -/
  v₀ : .v
  /-- The possessor. -/
  specifier : .D
  /-- *there*, the specifier of the pivot of an existential. -/
  there : .D "there"
  /-- The applicative head, which selects a DP. -/
  appl₀ : .Appl [.D]
  /-- The noun at the foot of the possessee. -/
  noun : .n

/-- The possessee with spine `s`: the noun extended by the heads above it, with `spec`, when there
is one, in the specifier of Poss. -/
def nominal (s : Spine) (spec : Option PlanarSyntacticObject) : PlanarSyntacticObject :=
  (PlanarSyntacticObject.leaf noun).extend .n 1
    (fun i ↦ if (s.above .n)[i]? = some .Poss then spec else none) (s.above .n)

/-- (38): the existential structure, in which v takes the possessee and the possessor is in the
specifier of its Poss head; with *there* in that specifier it is the existential of (40). -/
def existential (s : Spine) (x : LexicalItem.Token := specifier) : PlanarSyntacticObject :=
  so% [v₀ (nominal s (some (so% x)))]

/-- (44): the locative structure, in which v takes the phrase of an applicative head, with the
possessor in its specifier and the possessee as its complement. -/
def locative (s : Spine) : PlanarSyntacticObject :=
  so% [v₀ [specifier [appl₀ (nominal s none)]]]

-- (38) as drawn, with *a* in Num.
theorem existential_numP :
    existential numP =
      so% [v₀ [⟨⟨.of .Num [.Poss], 2⟩⟩ [specifier [⟨⟨.of .Poss [.n], 1⟩⟩ noun]]]] := by
  decide

/-- The φ-probe of v finds the possessor. -/
def Finds (t : PlanarSyntacticObject) : Prop := ↑specifier ∈ t.goals (t.leafProbe .D) ↑v₀

instance (t : PlanarSyntacticObject) : Decidable (Finds t) := by unfold Finds; infer_instance

@[simp] theorem finds_existential_numP : Finds (existential numP) := by decide

/-- In the existential structure over a full DP the probe of v does not find the possessor: the D
of the possessee is a closer goal. -/
@[simp] theorem not_finds_existential_dP : ¬ Finds (existential dP) := by decide

@[simp] theorem finds_locative_dP : Finds (locative dP) := by decide

/-- The specifier of a nominal with the determiner can be raised out of it: the nominal has a size
at which the probe of v finds it. -/
def Extractable (d : Examples.Determiner) : Prop := ∃ s ∈ sizes d, Finds (existential s)

theorem extractable_iff {d : Examples.Determiner} : Extractable d ↔ ¬ d.NeedsD := by
  cases d <;> simp [Extractable, sizes, Examples.Determiner.NeedsD]

instance : DecidablePred Extractable := fun _ ↦ decidable_of_iff _ extractable_iff.symm

/-! ### Spans and varieties -/

/-- The span of HAVE in a structure: its verbal heads from the lowest, and T. -/
def span (t : PlanarSyntacticObject) : Spine :=
  ⟨(t.yield.map (·.item.cat)).reverse.filter (fun c ↦ decide (c.family = .verbal)) ++ [.T]⟩

/-- The span of (53), v and T. -/
abbrev vT : Spine := ⟨[.v, .T]⟩

/-- The span of (54), the applicative, v and T. -/
abbrev applvT : Spine := ⟨[.Appl, .v, .T]⟩

@[simp] theorem span_existential_numP : span (existential numP) = vT := by decide

@[simp] theorem span_existential_dP : span (existential dP) = vT := by decide

@[simp] theorem span_locative_dP : span (locative dP) = applvT := by decide

/-- A spell-out rule pronounces the heads of a span at one of its positions. -/
structure Rule where
  /-- The heads the rule spells out. -/
  span : Spine
  /-- The position at which they are pronounced. -/
  site : Cat
  deriving DecidableEq

/-- Group B pronounces both spans of HAVE at T. -/
def groupB : List Rule := [⟨vT, .T⟩, ⟨applvT, .T⟩]

/-- (55): Group A pronounces the span of v and T at T and the span with the applicative at v. -/
def groupA : List Rule := [⟨vT, .T⟩, ⟨applvT, .v⟩]

/-- The standard variety pronounces both spans of HAVE at v. -/
def standard : List Rule := [⟨vT, .v⟩, ⟨applvT, .v⟩]

variable {g : List Rule} {f : Examples.Frame} {d : Examples.Determiner} {r : Examples.Relation}

/-- A variety raises HAVE over a span when it has the rule that pronounces the span at T. -/
def Raises (g : List Rule) (s : Spine) : Prop := ⟨s, .T⟩ ∈ g

instance (s : Spine) : Decidable (Raises g s) := inferInstanceAs (Decidable (_ ∈ _))

/-- HAVE stands before negation or the subject. -/
def Examples.Frame.Raised : Examples.Frame → Prop
  | .raisedNegation | .raisedQuestion => True
  | .plain | .haveGot | .doSupport | .thereBe => False

instance : DecidablePred Examples.Frame.Raised := fun f ↦ by
  cases f <;> unfold Examples.Frame.Raised <;> infer_instance

/-- The structures a possessee with the determiner in the relation can be built into: the
existential structure at each of its sizes, and the locative structure over a full DP when the
relation is alienable, the applicative head relating a possessor to what it has with it. -/
def analyses (d : Examples.Determiner) (r : Examples.Relation) : List PlanarSyntacticObject :=
  (sizes d).map existential ++ if r = .alienable then [locative dP] else []

/-- A variety generates a HAVE clause when, in one of the structures of its possessee, v finds the
possessor and, if the clause shows HAVE raised, the variety raises HAVE over the span. -/
def Generates (g : List Rule) (f : Examples.Frame) (d : Examples.Determiner)
    (r : Examples.Relation) : Prop :=
  ∃ t ∈ analyses d r, Finds t ∧ (f.Raised → Raises g (span t))

-- A HAVE clause is generated by the existential structure, when its determiner is weak, or by the
-- locative structure, when its relation is alienable.
theorem generates_iff :
    Generates g f d r ↔
      (¬ d.NeedsD ∧ (f.Raised → Raises g vT)) ∨
        (r = .alienable ∧ (f.Raised → Raises g applvT)) := by
  cases d <;> cases r <;> simp [Generates, analyses, sizes, Examples.Determiner.NeedsD]

instance : Decidable (Generates g f d r) := decidable_of_iff _ generates_iff.symm

/-- A clause that does not show the position of HAVE is generated alike in every variety. -/
theorem generates_iff_of_not_raised (g : List Rule) (hf : ¬ f.Raised) :
    Generates g f d r ↔ ¬ d.NeedsD ∨ r = .alienable := by
  simp [generates_iff, hf]

/-- Group A generates HAVE-raising with exactly the possessees whose specifier can be raised, the
pivots of *there*-existentials. -/
theorem generates_groupA_iff_extractable (hf : f.Raised) :
    Generates groupA f d r ↔ Extractable d := by
  simp [generates_iff, hf, extractable_iff, Raises, groupA]

-- (34)
theorem generates_groupB_iff : Generates groupB f d r ↔ ¬ d.NeedsD ∨ r = .alienable := by
  simp [generates_iff, Raises, groupB]

theorem not_generates_standard (hf : f.Raised) : ¬ Generates standard f d r := by
  simp [generates_iff, hf, Raises, standard]

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

/-! ### HAVE and BE -/

/-- The features a terminal shows the probe of v: a D, with φ-features unless it is *there*. -/
def features (tok : LexicalItem.Token) : Finset Myler2016.Feature :=
  if tok = there then {.d} else if tok.item.cat = .D then {.d, .phi} else ∅

/-- The probe of v: it copies φ-features and halts at a D. -/
def phiProbe : Probe.Spec Myler2016.Feature := ⟨{{.phi}}, {{.d}}⟩

/-- The features v has copied in a structure, from the closest D it c-commands. -/
def copied (t : PlanarSyntacticObject) : Finset Myler2016.Feature :=
  (Finset.univ.filter fun a ↦ t.termAt a = ↑v₀).biUnion fun a ↦
    phiProbe.copied (fun q ↦ (t.termAt q).token?.elim ∅ features)
      {q | t.toRoseTree.CCommands a q} (t.above t.toRoseTree.branching)

/-- The exponents of v: *has* when v has copied φ-features, and *is* otherwise. -/
def englishItems : List (DistributedMorphology.VocabularyItem Myler2016.Feature Auxiliary) :=
  open DistributedMorphology in [{.phi} ⟷ English.Auxiliaries.has, ∅ ⟷ English.Auxiliaries.is_]

/-- The form of v in a structure, by the Subset Principle over what v has copied. -/
def copula (t : PlanarSyntacticObject) : Option Auxiliary :=
  DistributedMorphology.subsetPrinciple englishItems (copied t)

/-- v is realized as HAVE over a possessor, in either structure, and as BE over *there*, which
has no φ-features for it to copy. -/
theorem copula_eq :
    copula (existential numP) = some English.Auxiliaries.has ∧
      copula (locative dP) = some English.Auxiliaries.has ∧
      copula (existential numP there) = some English.Auxiliaries.is_ := by
  decide

/-! ### Head Chain Pronunciation -/

/-- The head chain of a span, its heads sharing one M-value. -/
def chain (s : Spine) : HeadChain := .ofHeads (s.heads.head?.getD .v) s.heads.tail

-- A strong applicative head leaves the chain of (53) at T and holds that of (54) down.
theorem pronounced_strong_appl :
    (chain vT).pronounced {.Appl} = some .T ∧ (chain applvT).pronounced {.Appl} = some .Appl := by
  decide

-- No choice of strong heads pronounces the chain of (54) at v and that of (53) at T.
theorem not_pronounced_v_and_T (strong : Finset Cat) :
    ¬ ((chain applvT).pronounced strong = some .v ∧ (chain vT).pronounced strong = some .T) := by
  by_cases hA : Cat.Appl ∈ strong <;> by_cases hv : Cat.v ∈ strong <;>
    by_cases hT : Cat.T ∈ strong <;>
    simp [chain, HeadChain.pronounced, HeadChain.ofHeads, List.filter, hA, hv, hT]

/-! ### The uniform HAVE of Myler -/

-- In [myler-2016] every context that spells v out as *have* has the same Voice, so a rule that
-- reads Voice cannot tell two HAVE clauses apart, while the two structures here differ in span.
theorem myler_have_voice_eq {c c' : Myler2016.Context}
    (h : Myler2016.spellout Myler2016.englishItems c = some "have")
    (h' : Myler2016.spellout Myler2016.englishItems c' = some "have") :
    c.voiceD = c'.voiceD ∧ c.voicePhi = c'.voicePhi := by
  obtain ⟨hD, hφ⟩ := (Myler2016.have_iff_transitive c).1 h
  obtain ⟨hD', hφ'⟩ := (Myler2016.have_iff_transitive c').1 h'
  exact ⟨hD.trans hD'.symm, hφ.trans hφ'.symm⟩

/-! ### The loss of raising -/

open Classical in
/-- The rules a learner acquires from `n` clauses with HAVE raised, when a share `rate s` of them
is derived only with the span `s` at T and a raising rule is kept from `θ` such clauses on: a span
is pronounced at T when its evidence reaches the threshold, and at v otherwise. -/
noncomputable def acquired (θ n : ℝ) (rate : Spine → ℝ) : List Rule :=
  [vT, applvT].map fun s ↦ ⟨s, if θ ≤ rate s * n then .T else .v⟩

variable {θ n : ℝ} {rate : Spine → ℝ}

theorem raises_acquired_vT : Raises (acquired θ n rate) vT ↔ θ ≤ rate vT * n := by
  simp [Raises, acquired, Rule.mk.injEq]

theorem raises_acquired_applvT : Raises (acquired θ n rate) applvT ↔ θ ≤ rate applvT * n := by
  simp [Raises, acquired, Rule.mk.injEq]

/-- With unambiguous evidence rarer for the span with the applicative, a learner who raises HAVE
over it raises HAVE over the span without. -/
theorem raises_acquired_vT_of_applvT (hn : 0 ≤ n) (h : rate applvT ≤ rate vT)
    (hl : Raises (acquired θ n rate) applvT) : Raises (acquired θ n rate) vT :=
  raises_acquired_vT.2 ((raises_acquired_applvT.1 hl).trans (mul_le_mul_of_nonneg_right h hn))

-- (35): some amount of input yields the rules of Group A.
theorem exists_acquired_eq_groupA (hθ : 0 < θ) (h0 : 0 ≤ rate applvT)
    (h : rate applvT < rate vT) : ∃ n, 0 ≤ n ∧ acquired θ n rate = groupA := by
  have he : 0 < rate vT := h0.trans_lt h
  have hl : ¬ θ ≤ rate applvT * (θ / rate vT) := by
    rw [not_le, ← mul_div_assoc, div_lt_iff₀ he, mul_comm]
    exact mul_lt_mul_of_pos_left h hθ
  exact ⟨θ / rate vT, (div_pos hθ he).le, by
    simp [acquired, groupA, hl, (mul_div_cancel₀ θ he.ne').ge]⟩

end ThomsEtAl2026
