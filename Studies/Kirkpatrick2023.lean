module

public import Linglib.Semantics.Genericity.Normality
public import Studies.Veltman1996

/-!
# Kirkpatrick (2023): The Dynamics of Generics

This file formalizes [kirkpatrick-2023]'s dynamic semantics for generics and its account of
generic Sobel sequences: a generic followed by a statement of its exceptions, (1), is felicitous
and judged true, while the reverse order, (2), is infelicitous and sounds contradictory. Static
theories assign each generic a truth value on its own, so the truth of a sequence is a
conjunction invariant under reordering and the contrast is invisible to them, §3
(`static_perm`). The theory builds on the normality-based semantics (22), on which a generic is
true when every normal instance of its restrictor satisfies its matrix: the normality functor of
(21) is a `Genericity.Normality` and (22) is its generic. The dynamic theory of (24) evaluates a
generic against a modal horizon, the set of salient individuals, which the generic first expands
with the normal instances of its restrictor when none is yet salient (`update`), and the generic
is true when every salient instance of its restrictor satisfies its matrix (`holds`). This is
again a generic, under the normality whose normal instances of a restrictor are those on the
updated horizon (`horizon`), and discourse-initially it is the static generic (22)
(`holds_empty`). In a Sobel sequence the exceptions are abnormal for the general and so absent
from its horizon, while the reverse order puts them on the horizon first, where the general
finds them and no longer expands: the two orders come apart exactly as the paper predicts
(`SobelPair.order_sensitive`). The ravens of (25) and (28) are ranked by how they are coloured,
the albino abnormal (`ravenNormality`), and a mixed sequence like (29) survives because each
generic's restrictor excludes the individuals the other made salient (`lions_both_orders`).
Appendix A's comparison with [veltman-1996] is checked on his eight worlds: the frame presented
by accepted rules is insensitive to their order, so his theory predicts the reverse sequence
consistent (`veltman_reverse_consistent`).

## Implementation notes

* (24) is taken at a single world: the dispositional orbit is a point, so the normality functor
  of (21) is a normality at a single index and the modal horizon a set of individuals. The
  arguments of §5 are pointwise in the accessible world and survive the restriction.
* The contextual variable C of (20) is folded into the restrictor, as (26) and (31) do.

## References

* [kirkpatrick-2023]
* [veltman-1996]
* [cohen-1999a]
-/

@[expose] public section

namespace Kirkpatrick2023

open Genericity Set

variable {E : Type*}

/-- A generic Gen[φ][ψ], (20): its restrictor, with the contextual variable folded in, and its
matrix. -/
structure GenericSentence (E : Type*) where
  /-- The restrictor. -/
  restrictor : Set E
  /-- The matrix. -/
  scope : Set E

variable (N : Normality Unit E)

/-- The context change potential (24a): a generic presupposes a salient instance of its
restrictor and, failing that, expands the horizon by the normal instances (21). -/
def update (R σ : Set E) : Set E := σ ∪ {x | x ∈ N.normal () R ∧ ∀ y ∈ σ, y ∉ R}

/-- The normality of the dynamic generic: at a horizon, the normal instances of a restrictor are
its instances on the horizon the generic updates. -/
def horizon : Normality (Set E) E := ⟨fun σ R ↦ update N R σ ∩ R, fun _ _ ↦ inter_subset_right⟩

/-- The truth conditions (24b): every salient instance of the restrictor on the updated horizon
satisfies the matrix. -/
def holds (g : GenericSentence E) (σ : Set E) : Prop := σ ∈ (horizon N).gen g.restrictor g.scope

variable {N} {R σ : Set E}

theorem update_of_exists (h : ∃ y ∈ σ, y ∈ R) : update N R σ = σ := by
  obtain ⟨y, hy, hyR⟩ := h
  exact union_eq_left.2 fun _ hx ↦ (hx.2 y hy hyR).elim

theorem update_of_forall (h : ∀ y ∈ σ, y ∉ R) : update N R σ = σ ∪ N.normal () R :=
  congrArg (σ ∪ ·) (ext fun _ ↦ ⟨And.left, fun hx ↦ ⟨hx, h⟩⟩)

theorem update_empty : update N R ∅ = N.normal () R := by
  rw [update_of_forall fun _ h ↦ (notMem_empty _ h).elim, empty_union]

-- fn. 24
theorem subset_update : σ ⊆ update N R σ := subset_union_left

theorem update_update : update N R (update N R σ) = update N R σ := by
  by_cases h : ∃ y ∈ σ, y ∈ R
  · rw [update_of_exists h, update_of_exists h]
  · push Not at h
    rw [update_of_forall h]
    rcases (N.normal () R).eq_empty_or_nonempty with he | ⟨e, he⟩
    · rw [he, union_empty, update_of_forall h, he, union_empty]
    · exact update_of_exists ⟨e, Or.inr he, N.normal_subset () R he⟩

variable (N) in
/-- Discourse-initial truth, (23) and (26): against an empty horizon the dynamic generic is the
static generic (22) of the normality functor. -/
theorem holds_empty (g : GenericSentence E) : holds N g ∅ ↔ () ∈ N.gen g.restrictor g.scope := by
  rw [holds, Normality.mem_gen, Normality.mem_gen]
  change update N _ ∅ ∩ _ ⊆ _ ↔ _
  rw [update_empty, inter_eq_left.2 (N.normal_subset () _)]

variable (N) in
/-- A sequence of generics is consistent from a horizon when each is true against the horizon
its predecessors have expanded, §5. -/
def ConsistentFrom : Set E → List (GenericSentence E) → Prop
  | _, [] => True
  | σ, g :: gs => holds N g σ ∧ ConsistentFrom (update N g.restrictor σ) gs

variable (N) in
/-- Consistency from the empty discourse-initial horizon, §5.1. -/
abbrev Consistent (gs : List (GenericSentence E)) : Prop := ConsistentFrom N ∅ gs

/-! ### Static theories, §3 -/

/-- A static semantics assigns each generic a truth value on its own, so a sequence is true
when each member is, whatever the order: the probabilistic truth conditions (18) of
[cohen-1999a], the normality-based ones of (19) and the indexical approach of §3.3 all take
this form. -/
abbrev Static (truth : GenericSentence E → Prop) (gs : List (GenericSentence E)) : Prop :=
  ∀ g ∈ gs, truth g

/-- §3.4: no static semantics is sensitive to the order of a sequence. -/
theorem static_perm (truth : GenericSentence E → Prop) {gs gs' : List (GenericSentence E)}
    (h : gs.Perm gs') : Static truth gs ↔ Static truth gs' :=
  ⟨fun hs g hg ↦ hs g (h.mem_iff.2 hg), fun hs g hg ↦ hs g (h.mem_iff.1 hg)⟩

/-! ### Generic Sobel sequences, §5 -/

theorem consistent_pair {g₁ g₂ : GenericSentence E} (h₁ : holds N g₁ ∅) (h₂ : holds N g₂ ∅)
    (hdis : ∀ e ∈ N.normal () g₁.restrictor, e ∉ g₂.restrictor) : Consistent N [g₁, g₂] := by
  refine ⟨h₁, fun x ⟨hx, hxR⟩ ↦ ?_, trivial⟩
  change x ∈ update N _ (update N _ ∅) at hx
  rw [update_empty, update_of_forall hdis] at hx
  exact hx.elim (fun hx ↦ (hdis x hx hxR).elim) ((holds_empty N g₂).1 h₂ ·)

-- §5.3
theorem consistent_both_orders {g₁ g₂ : GenericSentence E} (h₁ : holds N g₁ ∅)
    (h₂ : holds N g₂ ∅) (h₁₂ : ∀ e ∈ N.normal () g₁.restrictor, e ∉ g₂.restrictor)
    (h₂₁ : ∀ e ∈ N.normal () g₂.restrictor, e ∉ g₁.restrictor) :
    Consistent N [g₁, g₂] ∧ Consistent N [g₂, g₁] :=
  ⟨consistent_pair h₁ h₂ h₁₂, consistent_pair h₂ h₁ h₂₁⟩

variable (N) in
/-- A pair of generics forming a Sobel sequence in the order general, exception, (1): the
exception's restrictor picks out a subkind of the general's, §5.2, its matrix contradicts the
general's, and the general's normal instances are not exceptions. -/
structure SobelPair (N : Normality Unit E) where
  /-- The general. -/
  general : GenericSentence E
  /-- The exception. -/
  exception : GenericSentence E
  sub : exception.restrictor ⊆ general.restrictor
  contra : Disjoint exception.scope general.scope
  abnormal : ∀ e ∈ N.normal () general.restrictor, e ∉ exception.restrictor

namespace SobelPair

variable (p : SobelPair N)

-- §5.1
theorem consistent (hg : holds N p.general ∅) (he : holds N p.exception ∅) :
    Consistent N [p.general, p.exception] :=
  consistent_pair hg he p.abnormal

-- §5.2
theorem reverse_inconsistent (he : holds N p.exception ∅)
    (hne : (N.normal () p.exception.restrictor).Nonempty) :
    ¬ Consistent N [p.exception, p.general] := by
  obtain ⟨e, he'⟩ := hne
  have hr : e ∈ p.general.restrictor := p.sub (N.normal_subset () _ he')
  rintro ⟨-, hgen, -⟩
  have hσ : update N p.exception.restrictor ∅ = N.normal () p.exception.restrictor :=
    update_empty
  have hmem : e ∈ update N p.general.restrictor (update N p.exception.restrictor ∅) := by
    rw [hσ, update_of_exists ⟨e, he', hr⟩]
    exact he'
  exact p.contra.ne_of_mem ((holds_empty N _).1 he he') (hgen ⟨hmem, hr⟩) rfl

/-- The order sensitivity of §5: the same two generics, each true on its own, are consistent
in the Sobel order and inconsistent in the reverse. -/
theorem order_sensitive (hg : holds N p.general ∅) (he : holds N p.exception ∅)
    (hne : (N.normal () p.exception.restrictor).Nonempty) :
    Consistent N [p.general, p.exception] ∧ ¬ Consistent N [p.exception, p.general] :=
  ⟨p.consistent hg he, p.reverse_inconsistent he hne⟩

end SobelPair

/-! ### Ravens, (1a) and (2a) -/

/-- Two normally coloured ravens and an albino one. -/
inductive Raven
  | normal₁
  | normal₂
  | albino
  deriving DecidableEq

/-- How abnormally a raven is coloured: the albino is, the others are not. -/
def Raven.rank : Raven → ℕ
  | .albino => 1
  | _ => 0

/-- The normality functor (21) on ravens: the normal instances of a property are its
best-coloured instances. -/
def ravenNormality : Normality Unit Raven :=
  .ofOrdering (fun _ ↦ univ) fun _ ↦ Preorder.lift Raven.rank

/-- Black ravens: all but the albino. -/
def Raven.black : Set Raven := {x | x ≠ .albino}

/-- *Ravens are black*, (20a): every raven is coloured in some way. -/
def ravensAreBlack : GenericSentence Raven := ⟨univ, Raven.black⟩

/-- *Albino ravens aren't black*. -/
def albinoRavensArentBlack : GenericSentence Raven := ⟨{.albino}, Raven.blackᶜ⟩

theorem ne_albino_of_mem_normal {x : Raven} (hx : x ∈ ravenNormality.normal () univ) :
    x ≠ .albino := by
  rintro rfl
  have h := (Preorder.mem_minimals_iff.1 hx).2
    (show Raven.normal₁ ∈ (univ : Set Raven) ∩ univ from ⟨trivial, trivial⟩)
    (show Raven.rank .normal₁ ≤ Raven.rank .albino by decide)
  exact absurd (h : Raven.rank .albino ≤ Raven.rank .normal₁) (by decide)

theorem mem_normal_albino {x : Raven} :
    x ∈ ravenNormality.normal () {.albino} ↔ x = .albino :=
  ⟨fun hx ↦ (Preorder.mem_minimals_iff.1 hx).1.2, fun hx ↦ hx ▸ Preorder.mem_minimals_iff.2
    ⟨⟨trivial, rfl⟩, fun _ hb _ ↦ hb.2 ▸ (Preorder.lift Raven.rank).le_refl _⟩⟩

/-- Albino ravens are ravens, are not black, and are abnormal as ravens. -/
def ravenPair : SobelPair ravenNormality :=
  ⟨ravensAreBlack, albinoRavensArentBlack, subset_univ _, disjoint_compl_left,
    fun _ he ↦ ne_albino_of_mem_normal he⟩

theorem holds_ravensAreBlack : holds ravenNormality ravensAreBlack ∅ :=
  (holds_empty _ _).2 fun _ hx ↦ ne_albino_of_mem_normal hx

theorem holds_albinoRavensArentBlack : holds ravenNormality albinoRavensArentBlack ∅ :=
  (holds_empty _ _).2 fun _ hx ↦ (mem_normal_albino.1 hx ▸ not_not.2 rfl : _)

-- (25), (28)
theorem ravens_order_sensitive :
    Consistent ravenNormality [ravensAreBlack, albinoRavensArentBlack] ∧
      ¬ Consistent ravenNormality [albinoRavensArentBlack, ravensAreBlack] :=
  ravenPair.order_sensitive holds_ravensAreBlack holds_albinoRavensArentBlack
    ⟨.albino, mem_normal_albino.2 rfl⟩

-- §3.1
theorem ravens_static :
    Static (holds ravenNormality · ∅) [albinoRavensArentBlack, ravensAreBlack] := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  exacts [holds_albinoRavensArentBlack, holds_ravensAreBlack]

/-! ### Mixed generics, (12) -/

/-- A male and a female lion. -/
inductive Lion
  | male
  | female
  deriving DecidableEq

/-- *Lions have manes*, (31): the restrictor is lions with some male sexually selected trait. -/
def lionsHaveManes : GenericSentence Lion := ⟨{.male}, {.male}⟩

/-- *Lions give birth to live young*, (32): the restrictor is lions that produce offspring in
some way. -/
def lionsGiveBirth : GenericSentence Lion := ⟨{.female}, {.female}⟩

/-- The mixed sequence (29) is consistent in both orders. -/
theorem lions_both_orders :
    Consistent ⊤ [lionsHaveManes, lionsGiveBirth] ∧ Consistent ⊤ [lionsGiveBirth, lionsHaveManes] :=
  consistent_both_orders ((holds_empty _ _).2 (Normality.mem_gen_top.2 subset_rfl))
    ((holds_empty _ _).2 (Normality.mem_gen_top.2 subset_rfl))
    (by rintro _ rfl; exact Lion.noConfusion) (by rintro _ rfl; exact Lion.noConfusion)

/-! ### Appendix A: Veltman (1996) -/

open Veltman1996

/-- σ₁ of Appendix A: the minimal state after `p ⇝ r` then `(p ∧ q) ⇝ ¬r`, with `p` raven,
`q` albino and `r` black on the eight worlds of Table 1. -/
def sobelState : State World := State.init |> rule p r |> rule (p ∩ q) rᶜ

/-- σ₂ of Appendix A: the rules accepted in the reverse order. -/
def reverseState : State World := State.init |> rule (p ∩ q) rᶜ |> rule p r

theorem sobelState_eq : sobelState = ⟨[⟨p ∩ q, rᶜ⟩, ⟨p, r⟩], Finset.univ⟩ := by decide +kernel

theorem reverseState_eq : reverseState = ⟨[⟨p, r⟩, ⟨p ∩ q, rᶜ⟩], Finset.univ⟩ := by
  decide +kernel

/-- In Veltman's theory neither order crashes and both reach the same frame, so the reverse Sobel
sequence is consistent (Appendix A). -/
theorem veltman_reverse_consistent :
    sobelState ≠ State.absurd ∧ reverseState ≠ State.absurd ∧
      sobelState.frame = reverseState.frame :=
  ⟨by rw [sobelState_eq]; decide, by rw [reverseState_eq]; decide,
    by rw [sobelState_eq, reverseState_eq]; exact Frame.ofRules_perm (List.Perm.swap _ _ _)⟩

end Kirkpatrick2023
