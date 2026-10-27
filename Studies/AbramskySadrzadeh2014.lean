module

public import Linglib.Semantics.Dynamic.DRS.Gluing
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum
public import Linglib.Data.Examples.AbramskySadrzadeh2014
public import Linglib.Data.Experiments.AbramskySadrzadeh2014

/-!
# Abramsky and Sadrzadeh (2014): Semantic Unification: A Sheaf Theoretic Approach to Natural Language

Abramsky and Sadrzadeh model basic discourse representation structures as a presheaf on
contexts, finite vocabularies of relation symbols with finite sets of variables
(`DRT.presheaf`), and read anaphora resolution as gluing: the local theories of a discourse's
parts glue along a cover, a choice of which referents to identify, when some global theory
restricts to each of them.

Proposition 1 claims that a gluing is unique when it exists. The paper's own second example
refutes it: `John(b)` is invisible to every restriction, so it can be added to the listed gluing
(`isGluing_beats_insert`). Gluings are unique exactly along covers jointly surjective on
literals (`DRT.isSeparatedFor_iff`), the covers of the Grothendieck topology the paper asks for
but leaves aside, for which basic DRSs form a sheaf (`DRT.isSheaf_literalCoverage`). The proof of
Proposition 1 builds the right candidate, the least gluing (`DRT.Cover.exists_isGluing_iff`): the
discussion example fails because the candidate does not restrict back, Example 3's merged cover
because it is inconsistent. The discussion's claim that disjoint vocabularies leave consistency
as the only obstruction needs injective cover maps (`not_forall_exists_isGluing_of_disjoint`), and
Example 3's vocabularies are not disjoint: `Man` occurs in two parts.

The probabilistic half composes the presheaf with a distribution functor. A distribution glues a
family of point masses iff it is carried by the deterministic gluings
(`map_restrict_eq_dirac_iff`), so the several multivalued gluings of §5.1 are mixtures of
deterministic ones. In the bananas discourse the corpus frequencies weight the coverings, and the
image of that distribution along the gluing map ranks *ripe bananas, cheeky monkeys* first
(`gluingMeasure_le`).

## Implementation notes

* `Var` is the paper's variable names; the substrate's sheaf theorem assumes infinitely many.
* `D_R` is formalised for probabilities, as image measures (`Measure.map`), not over an
  arbitrary semiring.
* The corpus frequencies and the printed probabilities are read from
  `Data.Experiments.AbramskySadrzadeh2014`.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
* [geach-1962]
-/

@[expose] public section

namespace AbramskySadrzadeh2014

open CategoryTheory FirstOrder MeasureTheory DRT Data.Experiments
open scoped ENNReal

/-! ### The paper's examples -/

/-- `Rel n` lists the `n`-ary relation symbols of the paper's examples. -/
inductive Rel : ℕ → Type
  | R : Rel 1
  | S : Rel 1
  | john : Rel 1
  | man : Rel 1
  | sleeps : Rel 1
  | snores : Rel 1
  | donkey : Rel 1
  | grey : Rel 1
  | cup : Rel 1
  | plate : Rel 1
  | banana : Rel 1
  | monkey : Rel 1
  | ripe : Rel 1
  | cheeky : Rel 1
  | owns : Rel 2
  | beats : Rel 2
  | broke : Rel 2
  | putOn : Rel 3
  | gave : Rel 3
  deriving DecidableEq

/-- `lang` is the relational language of the examples. -/
abbrev lang : Language := ⟨fun _ => Empty, Rel⟩

/-- `Var` lists the variables of the paper's examples. -/
inductive Var | x | y | z | u | v | w | a | b
  deriving DecidableEq

/-- `lit A x̄` is the literal `A(x̄)`, and `lit A x̄ false` is `¬A(x̄)`. -/
def lit {c : Context lang Var} {n : ℕ} (r : Rel n) (args : Fin n → Var) (pos : Bool := true)
    (hr : ⟨n, r⟩ ∈ c.vocab := by decide +kernel) (h : ∀ i, args i ∈ c.vars := by decide +kernel) :
    Literal c :=
  ⟨⟨⟨n, r⟩, hr⟩, fun i => ⟨args i, h i⟩, pos⟩

/-- `hom f` is the context morphism acting as `f` on variables. -/
def hom {c c' : Context lang Var} (f : Var → Var)
    (hf : ∀ t ∈ c.vars, f t ∈ c'.vars := by decide +kernel)
    (hL : c.vocab ⊆ c'.vocab := by decide +kernel) : c ⟶ c' :=
  ⟨hL, fun t => ⟨f t, hf t t.2⟩⟩

/-! #### Example 1: *John sleeps. He snores.* (`Examples.ex1`) -/

/-- The first example glues over this context. -/
abbrev snoresCtx : Context lang Var := ⟨{⟨1, .john⟩, ⟨1, .sleeps⟩, ⟨1, .snores⟩}, {.z}⟩

/-- The cover `{x} ↦ z ↤ {y}` merges *he* with *John*. -/
def snoresCover : Cover snoresCtx (Fin 2) where
  part := ![⟨{⟨1, .john⟩, ⟨1, .sleeps⟩}, {.x}⟩, ⟨{⟨1, .snores⟩}, {.y}⟩]
  map
    | 0 => hom fun _ => .z
    | 1 => hom fun _ => .z
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The local sections are `s₁ = {John(x), sleeps(x)}` and `s₂ = {snores(y)}`. -/
def snoresSections : ∀ i, Theory (snoresCover.part i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .sleeps (fun _ => .x)}, by decide +kernel⟩
  | 1 => ⟨{lit .snores (fun _ => .y)}, by decide +kernel⟩

/-- The gluing is `s = {John(z), sleeps(z), snores(z)}`. -/
def snoresGluing : Theory snoresCtx :=
  ⟨{lit .john (fun _ => .z), lit .sleeps (fun _ => .z), lit .snores (fun _ => .z)},
    by decide +kernel⟩

theorem isGluing_snores : snoresCover.IsGluing (presheaf lang Var) snoresSections snoresGluing := by
  decide +kernel

theorem snores_unique {s : Theory snoresCtx}
    (hs : snoresCover.IsGluing (presheaf lang Var) snoresSections s) : s = snoresGluing :=
  hs.unique (by decide +kernel) isGluing_snores

/-! #### Example 2: *John beats his donkey.* (`Examples.ex2`) -/

/-- The second example glues over this context. -/
abbrev beatsCtx : Context lang Var :=
  ⟨{⟨1, .john⟩, ⟨1, .donkey⟩, ⟨2, .owns⟩, ⟨2, .beats⟩}, {.a, .b}⟩

/-- The cover maps `x ↦ a`, `y ↦ b`, and `u ↦ a, v ↦ b`. -/
def beatsCover : Cover beatsCtx (Fin 3) where
  part := ![⟨{⟨1, .john⟩}, {.x}⟩, ⟨{⟨1, .donkey⟩}, {.y}⟩, ⟨{⟨2, .owns⟩, ⟨2, .beats⟩}, {.u, .v}⟩]
  map
    | 0 => hom fun _ => .a
    | 1 => hom fun _ => .b
    | 2 => hom fun | .u => .a | _ => .b
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The local sections are `s₁ = {John(x)}`, `s₂ = {donkey(y)}` and
`s₃ = {owns(u, v), beats(u, v)}`. -/
def beatsSections : ∀ i, Theory (beatsCover.part i)
  | 0 => ⟨{lit .john (fun _ => .x)}, by decide +kernel⟩
  | 1 => ⟨{lit .donkey (fun _ => .y)}, by decide +kernel⟩
  | 2 => ⟨{lit .owns ![.u, .v], lit .beats ![.u, .v]}, by decide +kernel⟩

/-- The paper's gluing is `s = {John(a), donkey(b), owns(a, b), beats(a, b)}`. -/
def beatsGluing : Theory beatsCtx :=
  ⟨{lit .john (fun _ => .a), lit .donkey (fun _ => .b), lit .owns ![.a, .b], lit .beats ![.a, .b]},
    by decide +kernel⟩

theorem isGluing_beats : beatsCover.IsGluing (presheaf lang Var) beatsSections beatsGluing := by
  decide +kernel

/-- `s ∪ {John(b)}` is a second gluing, since `John(b)` renames no literal of a part and adding
it changes no restriction. -/
def beatsGluing' : Theory beatsCtx :=
  ⟨insert (lit .john (fun _ => .b)) beatsGluing.lits, by decide +kernel⟩

theorem isGluing_beats_insert :
    beatsCover.IsGluing (presheaf lang Var) beatsSections beatsGluing' := by
  decide +kernel

/-- Proposition 1 fails for Example 2, whose cover is not jointly surjective on literals. -/
theorem not_isSeparatedFor_beats : ¬ beatsCover.presieve.IsSeparatedFor (presheaf lang Var) :=
  isSeparatedFor_iff.not.2 (by decide +kernel)

/-! #### Example 3: *John owns a donkey. It is grey.* (`Examples.ex3`) -/

/-- The third example glues over this context. -/
abbrev greyCtx : Context lang Var := ⟨{⟨1, .john⟩, ⟨1, .man⟩, ⟨1, .donkey⟩, ⟨1, .grey⟩}, {.a, .b}⟩

/-- The third example has these covering contexts; `Man` occurs in the first two. -/
def greyParts : Fin 3 → Context lang Var :=
  ![⟨{⟨1, .john⟩, ⟨1, .man⟩}, {.x}⟩, ⟨{⟨1, .donkey⟩, ⟨1, .man⟩}, {.y}⟩, ⟨{⟨1, .grey⟩}, {.z}⟩]

/-- The local sections are `s₁ = {John(x), Man(x)}`, `s₂ = {donkey(y), ¬Man(y)}` and
`s₃ = {grey(z)}`. -/
def greySections : ∀ i, Theory (greyParts i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .man (fun _ => .x)}, by decide +kernel⟩
  | 1 => ⟨{lit .donkey (fun _ => .y), lit .man (fun _ => .y) false}, by decide +kernel⟩
  | 2 => ⟨{lit .grey (fun _ => .z)}, by decide +kernel⟩

/-- The cover `x ↦ a`, `y ↦ a`, `z ↦ b` merges John's variable with the donkey's, the cover the
paper rules out as inconsistent. -/
def mergedCover : Cover greyCtx (Fin 3) where
  part := greyParts
  map
    | 0 => hom fun _ => .a
    | 1 => hom fun _ => .a
    | 2 => hom fun _ => .b
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

theorem not_exists_isGluing_merged :
    ¬ ∃ s, mergedCover.IsGluing (presheaf lang Var) greySections s :=
  fun h => absurd (Cover.exists_isGluing_iff.1 h).1 (by decide +kernel)

/-- The cover `x ↦ a`, `y ↦ b`, `z ↦ b` merges *it* with the donkey. -/
def greyCover : Cover greyCtx (Fin 3) where
  part := greyParts
  map
    | 0 => hom fun _ => .a
    | 1 => hom fun _ => .b
    | 2 => hom fun _ => .b
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The gluing is `s = {John(a), Man(a), donkey(b), ¬Man(b), grey(b)}`. -/
def greyGluing : Theory greyCtx :=
  ⟨{lit .john (fun _ => .a), lit .man (fun _ => .a), lit .donkey (fun _ => .b),
    lit .man (fun _ => .b) false, lit .grey (fun _ => .b)}, by decide +kernel⟩

theorem isGluing_grey : greyCover.IsGluing (presheaf lang Var) greySections greyGluing := by
  decide +kernel

-- Example 3
theorem ex3_readings :
    (Examples.ex3.readings.lookup "it = the donkey" = some .acceptable ↔
      ∃ s, greyCover.IsGluing (presheaf lang Var) greySections s) ∧
    (Examples.ex3.readings.lookup "it = John" = some .acceptable ↔
      ∃ s, mergedCover.IsGluing (presheaf lang Var) greySections s) :=
  ⟨iff_of_true rfl ⟨_, isGluing_grey⟩, iff_of_false (by decide) not_exists_isGluing_merged⟩

/-! #### Example 4: *John put the cup on the plate. He broke it.* (`Examples.ex4`) -/

/-- The fourth example glues over this context. -/
abbrev brokeCtx : Context lang Var :=
  ⟨{⟨1, .john⟩, ⟨1, .cup⟩, ⟨1, .plate⟩, ⟨3, .putOn⟩, ⟨2, .broke⟩}, {.x, .y, .z}⟩

/-- The fourth example has these covering contexts. -/
def brokeParts : Fin 2 → Context lang Var :=
  ![⟨{⟨1, .john⟩, ⟨1, .cup⟩, ⟨1, .plate⟩, ⟨3, .putOn⟩}, {.x, .y, .z}⟩, ⟨{⟨2, .broke⟩}, {.u, .v}⟩]

/-- The local sections are `s₁ = {John(x), Cup(y), Plate(z), PutOn(x, y, z)}` and
`s₂ = {Broke(u, v)}`. -/
def brokeSections : ∀ i, Theory (brokeParts i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .cup (fun _ => .y), lit .plate (fun _ => .z),
      lit .putOn ![.x, .y, .z]}, by decide +kernel⟩
  | 1 => ⟨{lit .broke ![.u, .v]}, by decide +kernel⟩

/-- *It* has two plausible antecedents. -/
inductive Broken | cup | plate
  deriving DecidableEq, Fintype

/-- Each antecedent has a referent. -/
def Broken.var : Broken → Var
  | cup => .y
  | plate => .z

theorem Broken.var_mem (b : Broken) : b.var ∈ brokeCtx.vars := by cases b <;> decide +kernel

/-- The cover extends the identity on `{x, y, z}` by `u ↦ x` and `v ↦` the chosen antecedent. -/
def brokeCover (b : Broken) : Cover brokeCtx (Fin 2) where
  part := brokeParts
  map
    | 0 => hom id
    | 1 => hom (fun | .u => .x | _ => b.var) fun t _ => by cases t <;> cases b <;> decide +kernel
  exists_map_eq := by cases b <;> decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The gluing is `{John(x), Cup(y), Plate(z), PutOn(x, y, z), Broke(x, ·)}`, with the chosen
antecedent. -/
def brokeGluing (b : Broken) : Theory brokeCtx :=
  ⟨{lit .john (fun _ => .x), lit .cup (fun _ => .y), lit .plate (fun _ => .z),
    lit .putOn ![.x, .y, .z],
    lit .broke ![.x, b.var] (h := Fin.forall_fin_two.2 ⟨by cases b <;> decide +kernel, b.var_mem⟩)},
    by cases b <;> decide +kernel⟩

theorem isGluing_broke :
    ∀ b, (brokeCover b).IsGluing (presheaf lang Var) brokeSections (brokeGluing b) := by
  decide +kernel

-- Example 4
theorem ex4_readings :
    (Examples.ex4.readings.lookup "it = the cup" = some .acceptable ↔
      ∃ s, (brokeCover .cup).IsGluing (presheaf lang Var) brokeSections s) ∧
    (Examples.ex4.readings.lookup "it = the plate" = some .acceptable ↔
      ∃ s, (brokeCover .plate).IsGluing (presheaf lang Var) brokeSections s) :=
  ⟨iff_of_true rfl ⟨_, isGluing_broke .cup⟩, iff_of_true rfl ⟨_, isGluing_broke .plate⟩⟩

/-! #### The discussion example: overlapping vocabularies -/

/-- The discussion example glues over this context. -/
abbrev overlapCtx : Context lang Var := ⟨{⟨1, .R⟩, ⟨1, .S⟩}, {.z, .w}⟩

/-- The cover maps `x ↦ z, u ↦ w` and `y ↦ z, v ↦ w`; both parts carry the whole vocabulary. -/
def overlapCover : Cover overlapCtx (Fin 2) where
  part := ![⟨{⟨1, .R⟩, ⟨1, .S⟩}, {.x, .u}⟩, ⟨{⟨1, .R⟩, ⟨1, .S⟩}, {.y, .v}⟩]
  map
    | 0 => hom fun | .x => .z | _ => .w
    | 1 => hom fun | .y => .z | _ => .w
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The local sections are `s₁ = {R(x), S(u)}` and `s₂ = {S(y), R(v)}`. -/
def overlapSections : ∀ i, Theory (overlapCover.part i)
  | 0 => ⟨{lit .R (fun _ => .x), lit .S (fun _ => .u)}, by decide +kernel⟩
  | 1 => ⟨{lit .S (fun _ => .y), lit .R (fun _ => .v)}, by decide +kernel⟩

theorem not_exists_isGluing_overlap :
    ¬ ∃ s, overlapCover.IsGluing (presheaf lang Var) overlapSections s := by
  rw [Cover.exists_isGluing_iff]
  decide +kernel

/-- The one-part cover `{x, u} ↦ {z}` identifies two referents of one part. -/
def collapseCover : Cover (⟨{⟨1, .R⟩}, {.z}⟩ : Context lang Var) (Fin 1) where
  part _ := ⟨{⟨1, .R⟩}, {.x, .u}⟩
  map _ := hom fun _ => .z
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The local section is `s₁ = {R(x)}`. -/
def collapseSections : ∀ i, Theory (collapseCover.part i)
  | 0 => ⟨{lit .R (fun _ => .x)}, by decide +kernel⟩

/-- Pairwise disjoint vocabularies and a consistent candidate do not guarantee a gluing, contrary to
the discussion of Proposition 1. -/
theorem not_forall_exists_isGluing_of_disjoint :
    ¬ ∀ (ι : Type) [Fintype ι] (c : Context lang Var) (C : Cover c ι) (x : ∀ i, Theory (C.part i)),
      (Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab) →
        Literal.Consistent (C.pushforward x) → ∃ s, C.IsGluing (presheaf lang Var) x s :=
  fun h => absurd (h _ _ collapseCover collapseSections Subsingleton.pairwise (by decide +kernel))
    (by rw [Cover.exists_isGluing_iff]; decide +kernel)

/-! ### Multivalued gluing -/

section Multivalued

instance {L : Language} {V : Type*} (c : Context L V) : MeasurableSpace (Theory c) := ⊤

instance {L : Language} {V : Type*} (c : Context L V) : DiscreteMeasurableSpace (Theory c) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

variable {L : Language} {V : Type*} [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]
  {c : Context L V} {ι : Type*} {C : Cover c ι} {x : ∀ i, Theory (C.part i)}

/-- A probability measure on global theories glues the point masses `δ_{sᵢ}` in `D ∘ F` iff it
is carried by the gluings of the `sᵢ`. -/
theorem map_restrict_eq_dirac_iff [Countable ι] (d : Measure (Theory c))
    [IsProbabilityMeasure d] :
    (∀ i, d.map (Theory.restrict (C.map i)) = Measure.dirac (x i)) ↔
      d {s | ¬ C.IsGluing (presheaf L V) x s} = 0 := by
  have hmeas (i : ι) : Measurable (Theory.restrict (C.map i) : Theory c → Theory (C.part i)) :=
    measurable_from_top
  constructor
  · intro h
    have : {s : Theory c | ¬ C.IsGluing (presheaf L V) x s} =
        ⋃ i, Theory.restrict (C.map i) ⁻¹' {x i}ᶜ := by
      ext; simp [Cover.IsGluing]; rfl
    rw [this]
    refine measure_iUnion_null fun i => ?_
    rw [← Measure.map_apply (hmeas i) .of_discrete, h i, Measure.dirac_apply' _ .of_discrete]
    simp
  · intro h i
    refine Measure.eq_dirac_of_ae_eq ?_
    rw [ae_map_iff (hmeas i).aemeasurable .of_discrete, ae_iff]
    exact measure_mono_null (fun s hs (hg : C.IsGluing (presheaf L V) x s) => hs (hg i)) h

end Multivalued

/-! ### Probabilistic anaphora: *John gave the bananas to the monkeys. They were ripe. They were
cheeky.* (`Examples.bananas`) -/

/-- The bananas discourse glues over this context. -/
abbrev ripeCtx : Context lang Var :=
  ⟨{⟨1, .john⟩, ⟨1, .banana⟩, ⟨1, .monkey⟩, ⟨3, .gave⟩, ⟨1, .ripe⟩, ⟨1, .cheeky⟩}, {.x, .y, .z}⟩

/-- The bananas discourse has these covering contexts. -/
def ripeParts : Fin 3 → Context lang Var :=
  ![⟨{⟨1, .john⟩, ⟨1, .banana⟩, ⟨1, .monkey⟩, ⟨3, .gave⟩}, {.x, .y, .z}⟩,
    ⟨{⟨1, .ripe⟩}, {.u}⟩, ⟨{⟨1, .cheeky⟩}, {.v}⟩]

/-- The local sections are `s₁ = {John(x), Banana(y), Monkey(z), Gave(x, y, z)}`,
`s₂ = {Ripe(u)}` and `s₃ = {Cheeky(v)}`. -/
def ripeSections : ∀ i, Theory (ripeParts i)
  | 0 => ⟨{lit .john (fun _ => .x), lit .banana (fun _ => .y), lit .monkey (fun _ => .z),
      lit .gave ![.x, .y, .z]}, by decide +kernel⟩
  | 1 => ⟨{lit .ripe (fun _ => .u)}, by decide +kernel⟩
  | 2 => ⟨{lit .cheeky (fun _ => .v)}, by decide +kernel⟩

/-- Each antecedent has a referent. -/
def Noun.var : Noun → Var
  | .banana => .y
  | .monkey => .z

theorem Noun.var_mem (a : Noun) : a.var ∈ ripeCtx.vars := by
  cases a <;> decide +kernel

/-- The covering `c` extends the identity on `{x, y, z}` by `u ↦ c.1` and `v ↦ c.2`. -/
def ripeCover (c : Noun × Noun) : Cover ripeCtx (Fin 3) where
  part := ripeParts
  map
    | 0 => hom id
    | 1 => hom (fun _ => c.1.var) fun _ _ => c.1.var_mem
    | 2 => hom (fun _ => c.2.var) fun _ _ => c.2.var_mem
  exists_map_eq := by obtain ⟨a, b⟩ := c; cases a <;> cases b <;> decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The covering `c` induces the candidate global section `t_c`. -/
def ripeGluing (c : Noun × Noun) : Theory ripeCtx :=
  ⟨{lit .john (fun _ => .x), lit .banana (fun _ => .y), lit .monkey (fun _ => .z),
    lit .gave ![.x, .y, .z], lit .ripe (fun _ => c.1.var) (h := fun _ => c.1.var_mem),
    lit .cheeky (fun _ => c.2.var) (h := fun _ => c.2.var_mem)},
    by obtain ⟨a, b⟩ := c; cases a <;> cases b <;> decide +kernel⟩

theorem isGluing_ripe :
    ∀ c, (ripeCover c).IsGluing (presheaf lang Var) ripeSections (ripeGluing c) := by
  decide +kernel

theorem ripeGluing_injective : Function.Injective ripeGluing := by decide +kernel

/-- The score of a covering sums the corpus frequencies of its two mergings. -/
def score (c : Noun × Noun) : ℕ := (frequency .ripe c.1).count + (frequency .cheeky c.2).count

instance : MeasurableSpace (Noun × Noun) := ⊤

/-- The distribution over coverings weights each by its score, normalised. -/
noncomputable def coveringMeasure : Measure (Noun × Noun) :=
  (∑ c, (score c : ℝ≥0∞))⁻¹ • Measure.ofWeights fun c => (score c : ℝ≥0∞)

/-- The paper's `d ∈ D_R F(L, X)` is the image of the covering distribution along `c ↦ t_c`. -/
noncomputable def gluingMeasure : Measure (Theory ripeCtx) := coveringMeasure.map ripeGluing

theorem gluingMeasure_apply (c : Noun × Noun) :
    gluingMeasure {ripeGluing c} = score c / 48 := by
  rw [gluingMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
    ← Set.image_singleton, ripeGluing_injective.preimage_image, coveringMeasure,
    Measure.smul_apply, smul_eq_mul, Measure.ofWeights_apply_singleton, ← Nat.cast_sum,
    show ∑ c : Noun × Noun, score c = 48 from rfl, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]

/-- *Ripe bananas, cheeky monkeys* (`t₂`) is the most likely resolution, with probability `1/2`. -/
theorem gluingMeasure_le :
    gluingMeasure {ripeGluing (.banana, .monkey)} = 1 / 2 ∧
      ∀ t, gluingMeasure {t} ≤ gluingMeasure {ripeGluing (.banana, .monkey)} := by
  refine ⟨by rw [gluingMeasure_apply, ENNReal.div_eq_div_iff] <;> norm_num [score, frequency],
    fun t => ?_⟩
  by_cases ht : t ∈ Set.range ripeGluing
  · obtain ⟨c, rfl⟩ := ht
    simp only [gluingMeasure_apply]
    exact ENNReal.div_le_div_right
      (Nat.cast_le.2 (by obtain ⟨a, b⟩ := c; cases a <;> cases b <;> decide)) _
  · rw [gluingMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
      Set.preimage_singleton_eq_empty.2 ht, measure_empty]
    exact zero_le

/-- The printed `d(t_c)` is `score c / 48` rounded, except `d(t₄) = 0.205` for `10/48`. -/
theorem gluingProbability_rounds_iff (c : Noun × Noun) :
    (gluingProbability c.1 c.2).probability.Rounds (score c) 48 ↔ c ≠ (.monkey, .monkey) := by
  obtain ⟨a, b⟩ := c
  cases a <;> cases b <;> decide

end AbramskySadrzadeh2014
