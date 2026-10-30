module

public import Linglib.Semantics.Composition.Ty
public import Linglib.Semantics.Quantification.Exceptive
public import Studies.BarwiseCooper1981
public import Studies.VonFintel1993
public import Linglib.Core.GroupTheory.GroupAction.Blocks
public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Data.Examples.Gajewski2002
public import Mathlib.Algebra.Group.Action.End

/-!
# Gajewski (2002): On Analyticity in Natural Language

This file formalizes Gajewski's principle that a sentence is ungrammatical if its
logical form contains an L-analytic constituent, one that is true, or false, in virtue of its
logical structure alone. Logical structure has two ingredients, and the file formalizes both
halves of the paper.

The logical items are the denotations invariant under permutations of the domain, the
criterion of van Benthem: a permutation of the entity domain lifts through the
`Montague.Ty` hierarchy (`permLift`), and an item is logical when every lifted permutation
fixes it (`PermutationInvariant`). Truth-functional conjunction is fixed because the lift is
the identity at type `t` (`permutationInvariant_and`), expletive *there*, which denotes the
whole domain, is fixed, and the domain and the empty set are the only invariant properties
(`permutationInvariant_et_iff`), so a contingent predicate like *new-student* is not a logical
item. Invariance at the determiner type is exactly the quantity invariance the Quantification
substrate states on `Det` (`permutationInvariant_det_iff`), so the logicality of *every*, *some*
and *no* follows from the isomorphism invariance of their Lindström classes rather than being
stipulated. Von Fintel's *but* is a logical item too (`permutationInvariant_but`).

The logical skeleton of a sentence replaces each maximal constituent without logical items by
a distinct variable of its semantic type; a skeleton is a predicate on type-sorted assignments
(`Skeleton`, domains by `Montague.Ty.Domain`), and a sentence is L-analytic when its skeleton
receives one truth value under every assignment (`Skeleton.IsLAnalytic`). The principle puts
two analyses on firmer ground. Barwise and Cooper explained Milsark's definiteness restriction on
*there*-sentences by the tautology a strong determiner produces there: the
skeleton of *there is every new student* is an L-tautology because every set is a subset of
the domain (`thereSkeleton_isLTautology`), while with *some* or *two* the skeleton is false
under the empty assignment and true under a large enough one. Von Fintel explained the
restriction of *but*-exceptives to universal determiners by the contradiction his
least-exception semantics produces under a left-upward-monotone determiner, which admits no
nonempty least exception (`IsExceptionSet.eq_bot_of_restrictorMonotone`): the skeletons with
*some* and *three* are L-contradictions, and those with *every* and *no* are contingent. Both
analyses had appealed to trivial truth conditions, which *war is war* shows cannot be the
explanation, and L-analyticity is narrower than triviality: *every woman is a woman* and
*John is smoking and John is not smoking* receive skeletons with distinct variables for their
repeated material, which are contingent, so the garden-variety tautologies and contradictions
come out grammatical. The paper's sentences are the rows, and the principle predicts each
(`rows_predicted`) except the *most*-exceptive, the gap the paper's footnote on *most*
concedes and `exceptiveSkeleton_most_not_isLAnalytic` states.

## Implementation notes

* The paper's type hierarchy has `e`, `t` and function types only; `permLift` extends it to
  the rest of `Montague.Ty` by the identity at the degree, cardinality, eventuality and world
  sorts, so pointwise at intensions, with `Unit` as the inert index sort of the extensional
  fragment.
* The denotation of *but* is the paper's schema factored compositionally, but where the
  printed uniqueness clause reads `g ⊆ j` the least-exception schema it factors requires
  `f ⊆ j`, so `but` is `IsExceptionSet` with the arguments rearranged; the exceptive skeleton
  carries the nonemptiness of the exception set that the paper's footnote adds to the schema.
* A row's L-analyticity quantifies over every reading of its determiner and every finite
  nonempty domain, following the model quantification of the paper's strength and
  monotonicity definitions; nonemptiness reflects the remark that the *some* skeleton is true
  on every nonempty value of its variable.
* The readings of *every*, *some* and *most* are the English fragment's; *no* is read from
  the quantification substrate because the fragment has no entry for the word, *a* is read as
  *some*, *everyone* as *every*, *someone* as *some*, and the numerals as *at least n*, the
  paper's own reading of *one, two* as left-upward-monotone determiners.
* The rows cover the sentences the paper derives. Its remaining printed examples are data
  only: *the wolf* needs a partial definite determiner, *John and Mary* is not a determiner,
  *many* has no fixed reading, and the paper derives no verdict for *exactly two* or *fewer
  than three*.
* The examples are `Data.Examples.Gajewski2002`.

## TODO

* A partial definite determiner would let the *the wolf* row join `rows_predicted`.
* Cardinality arguments for *exactly two* and *fewer than three* exceptives are in the later
  literature the paper's footnote cites, not in the paper.
* The English determiner fragment lacks *no*; adding it would let `Determiner.no` read from
  the fragment.

## References

* [gajewski-2002]
* [barwise-cooper-1981]
* [von-fintel-1993]
* [milsark-1977]
* [van-benthem-1989]
-/

@[expose] public section

namespace Gajewski2002

open Montague Quantifier Quantifier.Det Quantifier.Exceptive
open English.Determiners (QuantityWord)
open scoped Denotes

variable {E : Type}

/-! ### Logical items by permutation invariance (§3.1) -/

/-- A permutation of the entity domain lifts to every type (17), as the permutation itself at
`e`, the identity at `t`, conjugation at `⟨a,b⟩`, and the image at a set of alternatives. -/
def permLift (π : Equiv.Perm E) : ∀ ty : Ty, Equiv.Perm (Ty.Domain E Unit ty)
  | .e => π
  | .t => Equiv.refl _
  | .d => Equiv.refl _
  | .n => Equiv.refl _
  | .v => Equiv.refl _
  | .s => Equiv.refl _
  | .fn a b => (permLift π a).arrowCongr (permLift π b)
  | .comp (.reader ι) b => (permLift π ι).arrowCongr (permLift π b)
  | .comp .set b => (permLift π b).setCongr

@[simp] theorem permLift_et_apply (π : Equiv.Perm E) (P : E → Prop) :
    permLift π Ty.et P = P ∘ ⇑π.symm :=
  rfl

@[simp] theorem permLift_det_apply (π : Equiv.Perm E) (Q : Det E) (A B : Set E) :
    permLift π Ty.det Q A B = Q (π ⁻¹' A) (π ⁻¹' B) :=
  rfl

/-- An item is permutation invariant (18) when every lifted permutation fixes it, van
Benthem's criterion for the logical items. -/
def PermutationInvariant (ty : Ty) (x : Ty.Domain E Unit ty) : Prop :=
  ∀ π : Equiv.Perm E, permLift π ty x = x

/-- Truth-functional conjunction is a logical item (20), preserved because the lift is the
identity at type `t`. -/
theorem permutationInvariant_and :
    PermutationInvariant (E := E) (.t ⇒ .t ⇒ .t) fun u v : Prop ↦ u ∧ v :=
  fun _ ↦ rfl

-- (36)
theorem permutationInvariant_not : PermutationInvariant (E := E) (.t ⇒ .t) Not :=
  fun _ ↦ rfl

-- (23c)
theorem permutationInvariant_there : PermutationInvariant Ty.et fun _ : E ↦ True :=
  fun _ ↦ rfl

/-- The whole domain and the empty set are the only permutation-invariant properties (25). -/
theorem permutationInvariant_et_iff {P : E → Prop} :
    PermutationInvariant Ty.et P ↔ P = (fun _ ↦ True) ∨ P = (fun _ ↦ False) := by
  constructor
  · intro h
    have hB : MulAction.IsFixedBlock (Equiv.Perm E) {x | P x} := fun π ↦ Set.ext fun x ↦ by
      simp only [Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def, Set.mem_ofPred_eq]
      exact iff_of_eq (congrFun (h π) x)
    rcases hB.eq_empty_or_univ with h0 | hu
    · exact Or.inr (funext fun x ↦ eq_false fun hx ↦
        Set.eq_empty_iff_forall_notMem.1 h0 x hx)
    · exact Or.inl (funext fun x ↦ eq_true (Set.eq_univ_iff_forall.1 hu x))
  · rintro (rfl | rfl) π <;> rfl

theorem permutationInvariant_det_iff {Q : Det E} :
    PermutationInvariant Ty.det Q ↔ QuantityInvariant Q :=
  ⟨fun h π A B ↦ iff_of_eq (congr_fun₂ (h π) A B),
    fun h π ↦ funext₂ fun A B ↦ propext (h π A B)⟩

-- (25)
theorem permutationInvariant_some : PermutationInvariant Ty.det (Det.some : Det E) :=
  permutationInvariant_det_iff.2
    (by rw [← Lindstrom.someDet_toDet]; exact Lindstrom.Det.realize_quantityInvariant _)

-- (35), (34a)
theorem permutationInvariant_every : PermutationInvariant Ty.det (every : Det E) :=
  permutationInvariant_det_iff.2
    (by rw [← Lindstrom.everyDet_toDet]; exact Lindstrom.Det.realize_quantityInvariant _)

-- (11a)
theorem permutationInvariant_no : PermutationInvariant Ty.det (no : Det E) :=
  permutationInvariant_det_iff.2
    (by rw [← Lindstrom.noDet_toDet]; exact Lindstrom.Det.realize_quantityInvariant _)

/-- Von Fintel's ||but|| (31) factors the least-exception schema compositionally; the
exception `f` is the least set whose subtraction from the restrictor `g` makes the
quantification `D _ h` true. -/
def but : Ty.Domain E Unit (Ty.et ⇒ Ty.et ⇒ Ty.det ⇒ Ty.et ⇒ .t) :=
  fun f g D h ↦ IsExceptionSet D g f h

/-- ||but|| is a permutation-invariant element of its type (31), a logical constant, so it is
not replaced by a variable in the skeletons (32)–(33). -/
theorem permutationInvariant_but :
    PermutationInvariant (Ty.et ⇒ Ty.et ⇒ Ty.det ⇒ Ty.et ⇒ .t) (but (E := E)) := by
  intro π
  funext f g D h
  show IsExceptionSet (fun A B ↦ D (π.symm ⁻¹' A) (π.symm ⁻¹' B)) (π ⁻¹' g) (π ⁻¹' f) (π ⁻¹' h) =
    IsExceptionSet D g f h
  have key (S : Set E) :
      D (π.symm ⁻¹' (π ⁻¹' g \ S)) (π.symm ⁻¹' (π ⁻¹' h)) ↔ D (g \ π.symm ⁻¹' S) h := by
    rw [Set.preimage_sdiff, π.symm_preimage_preimage, π.symm_preimage_preimage]
  refine propext ⟨fun hb ↦ ⟨?_, fun j hj ↦ ?_⟩, fun hb ↦ ⟨?_, fun j hj ↦ ?_⟩⟩
  · simpa only [Set.mem_ofPred_eq, π.symm_preimage_preimage] using (key _).1 hb.1
  · refine (π.preimage_subset f j).1 (hb.2 ((key _).2 ?_))
    rwa [π.symm_preimage_preimage]
  · exact (key _).2 (by rw [π.symm_preimage_preimage]; exact hb.1)
  · simpa only [π.preimage_symm_preimage] using Set.preimage_mono (f := π) (hb.2 ((key j).1 hj))

/-! ### Logical skeletons and L-analyticity (§3.2) -/

/-- A logical skeleton (24) carries one typed slot per maximal constituent without logical
items, and the denotation the skeleton receives under a type-sorted assignment (26)–(27). -/
structure Skeleton (E : Type) {ι : Type*} (τ : ι → Ty) where
  interpret : ((i : ι) → Ty.Domain E Unit (τ i)) → Prop

namespace Skeleton

variable {ι : Type*} {τ : ι → Ty} (S : Skeleton E τ)

/-- The skeleton receives 1 under every assignment. -/
def IsLTautology : Prop := ∀ g, S.interpret g

/-- The skeleton receives 0 under every assignment. -/
def IsLContradiction : Prop := ∀ g, ¬ S.interpret g

/-- A skeleton is L-analytic (28) when it has the same truth value under every assignment. -/
def IsLAnalytic : Prop := S.IsLTautology ∨ S.IsLContradiction

theorem isLAnalytic_iff : S.IsLAnalytic ↔ ∀ g g', S.interpret g ↔ S.interpret g' := by
  refine ⟨fun h g g' ↦ ?_, fun h ↦ ?_⟩
  · rcases h with h | h
    · exact iff_of_true (h g) (h g')
    · exact iff_of_false (h g) (h g')
  · by_cases hg : ∃ g, S.interpret g
    · obtain ⟨g₀, hg₀⟩ := hg
      exact Or.inl fun g ↦ (h g g₀).2 hg₀
    · exact Or.inr fun g hg' ↦ hg ⟨g, hg'⟩

end Skeleton

/-! ### The definiteness restriction (§3.3.1) -/

/-- The skeleton (25) of a *there*-sentence applies the determiner to a property variable and
to *there*, which denotes the domain (23c). -/
def thereSkeleton (Q : Det E) : Skeleton E fun _ : Unit ↦ Ty.et :=
  ⟨fun g ↦ Q (g ()) Set.univ⟩

/-- With a conservative positive strong determiner the *there*-skeleton is an L-tautology
(30), [barwise-cooper-1981]'s consequence that the domain belongs to every strong
quantifier. -/
theorem thereSkeleton_isLTautology {Q : Det E} (hc : Conservative Q) (hs : PositiveStrong Q) :
    (thereSkeleton Q).IsLTautology :=
  fun g ↦ BarwiseCooper1981.there_of_positiveStrong hc hs (g ())

-- (25)
theorem thereSkeleton_some_not_isLAnalytic (a : E) :
    ¬ (thereSkeleton (Det.some : Det E)).IsLAnalytic := by
  rintro (h | h)
  · obtain ⟨_, hx, -⟩ := h fun _ _ ↦ False
    exact hx
  · exact h (fun _ _ ↦ True) ⟨a, trivial, trivial⟩

-- (5b)
theorem thereSkeleton_atLeast_two_not_isLAnalytic :
    ¬ (thereSkeleton (atLeast 2 : Det Bool)).IsLAnalytic := by
  rintro (h | h)
  · have ht : (atLeast 2 : Det Bool) ∅ Set.univ := h fun _ ↦ (∅ : Set Bool)
    exact absurd ht (by decide)
  · refine h (fun _ ↦ Set.univ) ?_
    show (atLeast 2 : Det Bool) Set.univ Set.univ
    decide

/-! ### But-exceptives (§3.3.2) -/

/-- The skeleton (32)–(33) of *D n₁ but n₂ n₃* applies ||but|| to the exception, restrictor
and scope variables around the logical determiner, with the exception set nonempty as the
paper's footnote requires. -/
def exceptiveSkeleton (Q : Det E) : Skeleton E fun _ : Fin 3 ↦ Ty.et :=
  ⟨fun g ↦ (∃ x, g 1 x) ∧ but (g 1) (g 0) Q (g 2)⟩

-- (33)
theorem exceptiveSkeleton_isLContradiction {Q : Det E} (h : RestrictorMonotone Q) :
    (exceptiveSkeleton Q).IsLContradiction :=
  fun _ hg ↦ hg.1.elim fun _ hx ↦ (IsExceptionSet.eq_bot_of_restrictorMonotone h hg.2).le hx

theorem exceptiveSkeleton_not_isLTautology (Q : Det E) :
    ¬ (exceptiveSkeleton Q).IsLTautology :=
  fun h ↦ (h ![fun _ ↦ True, fun _ ↦ False, fun _ ↦ True]).1.elim fun _ hx ↦ hx

-- (32)
theorem exceptiveSkeleton_every_not_isLContradiction (a : E) :
    ¬ (exceptiveSkeleton (every : Det E)).IsLContradiction := fun h ↦
  h ![fun _ ↦ True, (· = a), (· ≠ a)]
    ⟨⟨a, rfl⟩, fun _ hx ↦ hx.2, fun _ hS _ hx ↦ by_contra fun hs ↦ hS ⟨trivial, hs⟩ hx⟩

theorem exceptiveSkeleton_no_not_isLContradiction (a : E) :
    ¬ (exceptiveSkeleton (no : Det E)).IsLContradiction := fun h ↦
  h ![fun _ ↦ True, (· = a), (· = a)]
    ⟨⟨a, rfl⟩, fun _ hx hxa ↦ hx.2 hxa, fun _ hS _ hx ↦ by_contra fun hs ↦ hS ⟨trivial, hs⟩ hx⟩

/-- The *most*-exceptive (11c) is ungrammatical, yet its skeleton is not L-analytic, a gap through
[von-fintel-1993]'s limiting case (Footnote 7). -/
theorem exceptiveSkeleton_most_not_isLAnalytic :
    ¬ (exceptiveSkeleton (most : Det (Fin 2))).IsLAnalytic :=
  fun h ↦ h.elim (exceptiveSkeleton_not_isLTautology _) fun hc ↦
    hc ![fun _ ↦ True, (· = 0), (· = 1)] ⟨⟨0, rfl⟩, VonFintel1993.isExceptionSet_most_two⟩

/-! ### Garden-variety tautologies and contradictions (§3.3.3) -/

/-- The skeleton (35) of *every woman is a woman*, with distinct variables for the two
occurrences. -/
def everyIsSkeleton (E : Type) : Skeleton E fun _ : Fin 2 ↦ Ty.et :=
  ⟨fun g ↦ every (g 0) (g 1)⟩

theorem everyIsSkeleton_not_isLAnalytic (a : E) : ¬ (everyIsSkeleton E).IsLAnalytic := by
  rintro (h | h)
  · exact h ![fun _ ↦ True, fun _ ↦ False] (Set.mem_univ a)
  · exact h ![fun _ ↦ True, fun _ ↦ True] fun _ _ ↦ trivial

/-- The skeleton (36) of *John is smoking and John is not smoking*, with two propositional
variables. -/
def andNotSkeleton (E : Type) : Skeleton E fun _ : Fin 2 ↦ Ty.t :=
  ⟨fun g ↦ g 0 ∧ ¬ g 1⟩

theorem andNotSkeleton_not_isLAnalytic : ¬ (andNotSkeleton E).IsLAnalytic := by
  rintro (h | h)
  · exact (h ![True, True]).2 trivial
  · exact h ![True, False] ⟨trivial, id⟩

/-! ### The paper's sentences -/

/-- The determiners of the paper's analyzed sentences. -/
inductive Determiner
  | every
  | some
  | no
  | most
  | two
  | three
  deriving DecidableEq, Repr

/-- The readings of a determiner, from the English fragment where it has the word, from the
quantification substrate for *no*, and *at least n* for the numerals, the paper's reading of
the left-upward-monotone *one, two*. -/
noncomputable def Determiner.readings : Determiner → Set Det.Family.{0}
  | .every => ⟦QuantityWord.every⟧
  | .some => ⟦QuantityWord.some_⟧
  | .no => {Det.Family.no}
  | .most => ⟦QuantityWord.most⟧
  | .two => {Det.Family.atLeast 2}
  | .three => {Det.Family.atLeast 3}

/-- The constructions of the paper's sentences, with their determiner where one matters. -/
inductive Construction
  | there (d : Determiner)
  | exceptive (d : Determiner)
  | everyIs
  | andNot
  deriving DecidableEq, Repr

/-- A row records a sentence of the paper by its construction and whether it is
grammatical. -/
structure Row where
  construction : Construction
  grammatical : Bool
  deriving DecidableEq

/-- Whether the row's skeleton is L-analytic on every reading of its determiner and every
finite nonempty domain, the model quantification of the paper's definitions (6) and (14). -/
def Row.LAnalytic (r : Row) : Prop :=
  match r.construction with
  | .there d => ∀ q ∈ d.readings, ∀ (α : Type) [Fintype α] [Nonempty α],
      (thereSkeleton (q α)).IsLAnalytic
  | .exceptive d => ∀ q ∈ d.readings, ∀ (α : Type) [Fintype α] [Nonempty α],
      (exceptiveSkeleton (q α)).IsLAnalytic
  | .everyIs => ∀ (α : Type) [Fintype α] [Nonempty α], (everyIsSkeleton α).IsLAnalytic
  | .andNot => ∀ (α : Type) [Fintype α] [Nonempty α], (andNotSkeleton α).IsLAnalytic

def Row.ofDatum (ex : Datum) : Option Row := do
  let g ← ex.parse? "grammatical" [("yes", true), ("no", false)]
  let d := ex.parse? "determiner"
    [("every", Determiner.every), ("some", .some), ("no", .no), ("most", .most),
     ("two", .two), ("three", .three)]
  let c ← match ex.feature? "construction", d with
    | some "there", some d => some (Construction.there d)
    | some "exceptive", some d => some (.exceptive d)
    | some "everyIs", _ => some .everyIs
    | some "andNot", _ => some .andNot
    | _, _ => none
  pure ⟨c, g⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

private theorem rows_eq : rows =
    [⟨.there .every, false⟩, ⟨.there .some, true⟩, ⟨.there .two, true⟩, ⟨.there .some, true⟩,
     ⟨.exceptive .every, true⟩, ⟨.exceptive .no, true⟩, ⟨.exceptive .some, false⟩,
     ⟨.exceptive .three, false⟩, ⟨.exceptive .most, false⟩, ⟨.there .every, false⟩,
     ⟨.everyIs, true⟩, ⟨.andNot, true⟩] := by
  decide

/-- By principle (29) the paper's sentences are grammatical exactly when their skeletons are
not L-analytic. The *most*-exceptive is the gap footnote 7 concedes,
`exceptiveSkeleton_most_not_isLAnalytic`. -/
theorem rows_predicted :
    ∀ r ∈ rows, r.construction ≠ .exceptive .most →
      (r.grammatical = true ↔ ¬ r.LAnalytic) := by
  have hevery : (Row.mk (.there .every) false).LAnalytic := by
    intro q hq α _ _
    obtain rfl : q = Det.Family.every := hq
    exact Or.inl (thereSkeleton_isLTautology conservative_every positiveStrong_every)
  have hsome : (Row.mk (.there .some) true).grammatical = true ↔
      ¬ (Row.mk (.there .some) true).LAnalytic :=
    iff_of_true rfl fun h ↦ thereSkeleton_some_not_isLAnalytic true (h Det.Family.some rfl Bool)
  rw [rows_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact fun _ ↦ iff_of_false Bool.false_ne_true (not_not.2 hevery)
  · exact fun _ ↦ hsome
  · exact fun _ ↦ iff_of_true rfl fun h ↦
      thereSkeleton_atLeast_two_not_isLAnalytic (h (Det.Family.atLeast 2) rfl Bool)
  · exact fun _ ↦ hsome
  · exact fun _ ↦ iff_of_true rfl fun h ↦
      (h Det.Family.every rfl Bool).elim (exceptiveSkeleton_not_isLTautology _)
        (exceptiveSkeleton_every_not_isLContradiction true)
  · exact fun _ ↦ iff_of_true rfl fun h ↦
      (h Det.Family.no rfl Bool).elim (exceptiveSkeleton_not_isLTautology _)
        (exceptiveSkeleton_no_not_isLContradiction true)
  · refine fun _ ↦ iff_of_false Bool.false_ne_true (not_not.2 fun q hq α _ _ ↦ ?_)
    obtain rfl : q = Det.Family.some := hq
    exact Or.inr (exceptiveSkeleton_isLContradiction restrictorMonotone_some)
  · refine fun _ ↦ iff_of_false Bool.false_ne_true (not_not.2 fun q hq α _ _ ↦ ?_)
    obtain rfl : q = Det.Family.atLeast 3 := hq
    exact Or.inr (exceptiveSkeleton_isLContradiction (restrictorMonotone_atLeast 3))
  · exact fun hne ↦ absurd rfl hne
  · exact fun _ ↦ iff_of_false Bool.false_ne_true (not_not.2 hevery)
  · exact fun _ ↦ iff_of_true rfl fun h ↦ everyIsSkeleton_not_isLAnalytic true (h Bool)
  · exact fun _ ↦ iff_of_true rfl fun h ↦ andNotSkeleton_not_isLAnalytic (h Bool)

end Gajewski2002
