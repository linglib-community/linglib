module

public import Linglib.Semantics.Modality.Kernel
public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Data.Examples.VonFintelGillies2010

/-!
# von Fintel & Gillies (2010): Must … Stay … Strong!

This file formalizes von Fintel and Gillies's defense of a strong epistemic *must* against
the Mantra that *must φ* is weaker than its prejacent, Karttunen's problem (2). On the paper's
analysis *must* stays at the top of the scale of epistemic strength (1) and entails its
prejacent, and the felt weakness is an evidential presupposition: the kernel of direct
information must not directly settle the prejacent, though its modal base may entail it. The
kernel apparatus, the explicit-representation implementation of settling (§7.1) and the
presuppositional operators (Definitions 4 to 6), is `Semantics/Modality/Kernel.lean`; this file
carries the worked kernel of Figure 3(a), Billy's weather reports in the colors of the
Mastermind scenario of §2 (`mastermindK`), on which *must blue* is defined and true while
*might red* is undefined, so that indirectness and weakness come apart (§4.1), the validity of
*if φ, must ψ; φ; so ψ* (Argument 4.3.1) and the contradictoriness of *must φ but perhaps not φ*
(Argument 4.3.2), and the second implementation of settling by the partition a kernel induces,
a subject matter in which the prejacent is an issue (Definition 7, §7.2), with the two
implementations shown non-equivalent in both directions (`settlesByPartition`).

## Implementation notes

The four worlds are red, blue, green and unknown, with *red or blue* and *not red* the kernel
propositions `P ∪ Q` and `W \ P` of the paper's figure. A subject matter is a `Setoid`, and a
proposition is an issue in it when the setoid decides the proposition. The paper's examples
are the rows of `Data.Examples.VonFintelGillies2010`.

## References

* [von-fintel-gillies-2010]
* [kratzer-1991]
* [karttunen-1972]
-/

@[expose] public section

namespace VonFintelGillies2010

/-! ### The kernel model (§7.1)

A four-world instantiation of §7.1's worked kernel `K = {P ∪ Q, W \ P}`
(Billy's weather report, Figure 3(a)), skinned with the colors of the §2
Mastermind scenario (Pascal asking Mordecai *Must there be two reds?*):
`P` = red-only, `Q` = blue, so `redOrBlue = P ∪ Q` and `notRed = W \ P`.
`B_K = {w1}` entails *blue* without either kernel proposition settling it. -/

open Modality

/-- Four worlds, with `w0` red, `w1` blue, `w2` green, and `w3` unknown. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited

/-- `⟦red or blue⟧ = {w0, w1}`, the paper's `P ∪ Q`. -/
abbrev redOrBlue : World → Prop := fun w ↦ w = .w0 ∨ w = .w1

/-- `⟦not red⟧ = {w1, w2, w3}`, the paper's `W \ P`. -/
abbrev notRed : World → Prop := (· ≠ .w0)

/-- `⟦blue⟧ = {w1}`, the paper's `Q`. -/
abbrev blue : World → Prop := (· = .w1)

/-- `⟦red⟧ = {w0}`, the paper's `P`. -/
abbrev red : World → Prop := (· = .w0)

/-- The §7.1 kernel `{P ∪ Q, W \ P}` in Mastermind colors. -/
def mastermindK : Kernel World := ⟨{redOrBlue, notRed}⟩

/-- A one-proposition kernel whose base properly contains ⟦blue⟧. -/
def indirectK : Kernel World := ⟨{redOrBlue}⟩

theorem mastermind_base : mastermindK.base = ({.w1} : Set World) := by
  ext w
  cases w <;> simp [mastermindK, redOrBlue, notRed]

theorem mastermind_blue_unsettled :
    ¬ mastermindK.directlySettles blue := by
  rintro ⟨x, hx, hxor⟩
  rcases hx with rfl | hx'
  · rcases hxor with h_sub | h_disj
    · exact (show ¬ blue .w0 from by decide)
        (h_sub (show redOrBlue .w0 from by decide))
    · exact Set.disjoint_left.mp h_disj (show redOrBlue .w1 from by decide)
        (show blue .w1 from by decide)
  · obtain rfl : x = notRed := hx'
    rcases hxor with h_sub | h_disj
    · exact (show ¬ blue .w2 from by decide)
        (h_sub (show notRed .w2 from by decide))
    · exact Set.disjoint_left.mp h_disj (show notRed .w1 from by decide)
        (show blue .w1 from by decide)

theorem mastermind_blue_follows : mastermindK.FollowsFrom blue := by
  rw [Kernel.followsFrom_iff, mastermind_base]
  rintro w rfl
  rfl

theorem mastermind_must_blue_eq_one : kernelMust mastermindK blue .w0 = 1 :=
  kernelMust_eq_one_iff.2 ⟨mastermind_blue_unsettled, mastermind_blue_follows⟩

theorem mastermind_red_settled :
    mastermindK.directlySettles red :=
  ⟨notRed, by simp [mastermindK], Or.inr (Set.disjoint_left.mpr fun _ hnr hr ↦ hnr hr)⟩

theorem mastermind_might_red_eq_zero : kernelMight mastermindK red .w0 = 0 :=
  kernelMight_eq_zero_iff.2 mastermind_red_settled

theorem mastermind_redOrBlue_settled :
    mastermindK.directlySettles redOrBlue :=
  ⟨redOrBlue, by simp [mastermindK], Or.inl subset_rfl⟩

/-! ### Deep theorems -/

theorem entailment_settling_gap :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.FollowsFrom φ ∧ ¬ k.directlySettles φ :=
  ⟨mastermindK, blue, mastermind_blue_follows, mastermind_blue_unsettled⟩

/-- Indirectness and assertion strength are orthogonal dimensions, since must can be defined and
true, undefined, or defined and false (§4.1). -/
theorem indirectness_neq_weakness :
    kernelMust mastermindK blue .w0 = 1 ∧ kernelMust mastermindK red .w0 = 0 ∧
      kernelMust indirectK blue .w0 = -1 := by
  refine ⟨mastermind_must_blue_eq_one, kernelMust_eq_zero_iff.2 mastermind_red_settled,
    kernelMust_eq_neg_one_iff.2 ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, hxor⟩
    obtain rfl : x = redOrBlue := hx
    rcases hxor with h_sub | h_disj
    · exact (show ¬ blue .w0 from by decide)
        (h_sub (show redOrBlue .w0 from by decide))
    · exact Set.disjoint_left.mp h_disj (show redOrBlue .w1 from by decide)
        (show blue .w1 from by decide)
  · intro h
    have hw0 : World.w0 ∈ indirectK.base :=
      Kernel.mem_base.mpr fun p hp ↦ by
        obtain rfl : p = redOrBlue := hp; decide
    exact (by decide : ¬ blue World.w0) (h _ hw0)

variable {W : Type*} (k : Kernel W)

theorem modus_ponens_with_must (φ ψ : W → Prop) (w : W)
    (hReal : w ∈ k.base)
    (hCond : φ w → kernelMust k ψ w = 1)
    (hPhi : φ w) :
    ψ w :=
  Modality.must_entails_prejacent k ψ w hReal (kernelMust_eq_one_iff.1 (hCond hPhi)).2

theorem must_perhaps_contradiction (φ : W → Prop) (w : W)
    (hMust : kernelMust k φ w = 1) :
    kernelMight k (fun w' ↦ ¬ φ w') w = -1 := by
  obtain ⟨hs, hf⟩ := kernelMust_eq_one_iff.1 hMust
  refine kernelMight_eq_neg_one_iff.2 ⟨(Kernel.directlySettles_not k φ).not.2 hs, ?_⟩
  rintro ⟨w', hw', hφneg⟩
  exact hφneg (hf w' hw')

/-! ### Implementation 2: settling by partitions (Definition 7, §7.2)

Def 7 presents subject matters as equivalence relations on `W`: `S[P]` keeps
the pairs of `S` that agree on `P`, and `P` is an *issue* in `S` iff
`S[P] = S`. The subject matter S_K determined by a kernel is the refinement
`S_o[P₁]…[Pₙ]` of the universal relation along each kernel proposition —
equivalently, the relation "agrees on every `X ∈ K`". Implementation 2:
K directly settles P iff P is an issue in S_K. -/

/-- The subject matter `S_K` of a kernel, relating worlds that agree on every
    proposition in `K`. -/
def subjectMatter : Setoid W where
  r w v := ∀ p ∈ k.props, (p w ↔ p v)
  iseqv := ⟨fun _ _ _ ↦ Iff.rfl, fun h p hp ↦ (h p hp).symm,
    fun h h' p hp ↦ (h p hp).trans (h' p hp)⟩

/-- `P` is an *issue* in a subject matter `S` when `S`-equivalent worlds never
    disagree on `P`. -/
def IsIssue (s : Setoid W) (φ : W → Prop) : Prop := s.Decides {w | φ w}

/-- `K` settles `P` by partition iff `P` is an issue in `S_K`. -/
def settlesByPartition (φ : W → Prop) : Prop :=
  IsIssue (subjectMatter k) φ

theorem subjectMatter_rel_base {v w : W} (hv : v ∈ k.base) (hw : w ∈ k.base) :
    (subjectMatter k).r v w := fun p hp ↦
  iff_of_true (Kernel.mem_base.mp hv p hp) (Kernel.mem_base.mp hw p hp)

theorem partition_implies_entailment (φ : W → Prop)
    (h : settlesByPartition k φ) :
    k.FollowsFrom φ ∨ k.FollowsFrom (fun w ↦ ¬ φ w) := by
  rcases Set.eq_empty_or_nonempty k.base with hEmpty | ⟨w₀, hw₀⟩
  · exact Or.inl fun w hw ↦ absurd (hEmpty ▸ hw) (Set.notMem_empty w)
  · exact (Classical.em (φ w₀)).imp
      (fun hφ v hv ↦ (Setoid.decides_iff.1 h w₀ v (subjectMatter_rel_base k hw₀ hv)).mp hφ)
      (fun hφ v hv hφv ↦
        hφ ((Setoid.decides_iff.1 h w₀ v (subjectMatter_rel_base k hw₀ hv)).mpr hφv))

/-! ### Non-equivalence of the two implementations (§7.2)

Implementation 1 settles supersets of K-propositions that Implementation 2
misses (`K = {P}` settles `P ∪ Q` explicitly, but there are worlds agreeing
on `P` that disagree on `P ∪ Q`); Implementation 2 settles propositions
determined jointly by K-propositions that no single proposition settles
(`blue` is determined by `redOrBlue` together with `notRed`). -/

private theorem not_settles_redOrBlue :
    ¬ settlesByPartition ⟨{red}⟩ redOrBlue := by
  intro h
  have h12 := Setoid.decides_iff.1 h .w1 .w2 (fun p hp ↦ by
    obtain rfl : p = red := hp; decide)
  exact absurd (h12.mp (by decide)) (by decide)

theorem explicit_not_implies_partition :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.directlySettles φ ∧ ¬ settlesByPartition k φ :=
  ⟨⟨{red}⟩, redOrBlue,
    ⟨red, by simp, Or.inl fun _ hw ↦ Or.inl hw⟩, not_settles_redOrBlue⟩

theorem partition_not_implies_explicit :
    ∃ (k : Kernel World) (φ : World → Prop),
      settlesByPartition k φ ∧ ¬ k.directlySettles φ := by
  refine ⟨mastermindK, blue, Setoid.decides_iff.2 fun w v h ↦ ?_, mastermind_blue_unsettled⟩
  have h1 := h redOrBlue (by simp [mastermindK])
  have h2 := h notRed (by simp [mastermindK])
  revert h1 h2
  cases w <;> cases v <;> decide

theorem entailment_not_implies_partition :
    ∃ (k : Kernel World) (φ : World → Prop),
      k.FollowsFrom φ ∧ ¬ settlesByPartition k φ :=
  ⟨⟨{red}⟩, redOrBlue,
    fun w hw ↦ Or.inl (by simpa using hw),
    not_settles_redOrBlue⟩

end VonFintelGillies2010
