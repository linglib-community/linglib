module

public import Linglib.Semantics.Degree.PropertyDomain
public import Linglib.Semantics.Reference.Distinguishing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Minimal

/-!
# Dale and Reiter, computational interpretations of the Gricean maxims (1995)

A referring expression is a distinguishing description: a set of attribute-value pairs that
all hold of the intended referent and that together rule out every member of the contrast
set, which makes finding one a set-cover problem and finding a shortest one NP-hard. Dale and
Reiter compare four computational readings of Grice's brevity submaxim, Full Brevity (a
shortest description), Dale's Greedy Heuristic, Reiter's Local Brevity rules and their own
Incremental Algorithm, which walks a fixed preference list of attributes and keeps any value
that rules out a distractor not yet ruled out. They argue for the last on cost and on two
psycholinguistic observations: speakers include unnecessary modifiers, which only the greedy
and incremental algorithms produce, and speakers begin an expression before they have
finished scanning the distractors, which only the incremental algorithm allows.

We define distinguishing descriptions and the four readings with a finite contrast set, prove
that a shortest description satisfies Reiter's two rules while the greedy and incremental
algorithms return unnecessary pairs on the paper's own examples, and prove that Fig. 6's
output rules out every distractor, never retracts a pair and, under §4.5's accuracy user
model, is a distinguishing description.

## Implementation notes

* Reiter's third rule, Lexical Preference, is not modelled.
* Fig. 6's `FindBestValue` recurses until the taxonomy has no more specific value; the
  descent is bounded by the domain's `depth`, which must cover the taxonomies' height.
* Fig. 3 leaves ties between equally discriminating properties open; `greedy` takes the
  first in the order of `P`.

## References

* [R. Dale and E. Reiter, *Computational Interpretations of the Gricean Maxims in the
  Generation of Referring Expressions* (1995)][dale-reiter-1995]
* [H. P. Grice, *Logic and Conversation* (1975)][grice-1975]
-/

@[expose] public section

namespace DaleReiter1995

open Finset

section Brevity

variable {E A V : Type*}

/-! ### Distinguishing descriptions (§2.2) -/

/-- The value an entity has for an attribute in the host's knowledge base, if it has one
(§4.1). -/
abbrev KB (E A V : Type*) := E → A → Option V

/-- The semantic content of a referring expression, a set of attribute-value pairs (§2.2). -/
abbrev Description (A V : Type*) := Finset (A × V)

/-- The pair holds of the entity. -/
def Applies (kb : KB E A V) (x : E) (p : A × V) : Prop := kb x p.1 = some p.2

instance [DecidableEq V] (kb : KB E A V) (x : E) (p : A × V) : Decidable (Applies kb x p) := by
  unfold Applies; infer_instance

/-- Every pair of a description holds of the entity. -/
def extension (kb : KB E A V) (L : Description A V) (x : E) : Prop := ∀ p ∈ L, Applies kb x p

instance [DecidableEq V] (kb : KB E A V) (L : Description A V) (x : E) :
    Decidable (extension kb L x) := by
  unfold extension; infer_instance

/-- A distinguishing description of `r` against the contrast set `C` holds of `r` and
distinguishes it from `C`, so that every pair holds of `r` and every distractor fails some
pair. -/
def Distinguishing (kb : KB E A V) (r : E) (C : Finset E) (L : Description A V) : Prop :=
  extension kb L r ∧ Distinguishes (extension kb) C r L

instance [DecidableEq V] (kb : KB E A V) (r : E) (C : Finset E) (L : Description A V) :
    Decidable (Distinguishing kb r C L) := by
  unfold Distinguishing; infer_instance

theorem distinguishing_iff {kb : KB E A V} {r : E} {C : Finset E} {L : Description A V} :
    Distinguishing kb r C L ↔
      (∀ p ∈ L, Applies kb r p) ∧ ∀ c ∈ C, ∃ p ∈ L, ¬ Applies kb c p := by
  simp only [Distinguishing, Distinguishes, Prop.lt_iff, extension]
  refine and_congr_right fun h ↦ forall₂_congr fun c _ ↦ ?_
  rw [and_iff_left h]
  push Not
  exact Iff.rfl

/-- The members of the contrast set a pair rules out (§2.2). -/
def rulesOut [DecidableEq V] (kb : KB E A V) (C : Finset E) (p : A × V) : Finset E :=
  C.filter (¬ Applies kb · p)

/-- A description distinguishes when its pairs' `rulesOut` sets cover the contrast set, the
set-cover problem of §2.2. -/
theorem distinguishing_iff_biUnion [DecidableEq E] [DecidableEq V] (kb : KB E A V) (r : E)
    (C : Finset E) (L : Description A V) :
    Distinguishing kb r C L ↔
      (∀ p ∈ L, Applies kb r p) ∧ C ⊆ L.biUnion (rulesOut kb C) := by
  simp only [distinguishing_iff, rulesOut, subset_iff, mem_biUnion, mem_filter]
  exact and_congr_right λ _ => forall₂_congr λ c hc =>
    exists_congr λ p => and_congr_right λ _ => (and_iff_right hc).symm

/-! ### Four interpretations of brevity (§3.1) -/

variable (kb : KB E A V) (r : E) (C : Finset E) (L : Description A V)

/-- A distinguishing description of least cardinality, the Full Brevity reading (§3.1.1). -/
abbrev IsShortest : Prop := MinimalFor (Distinguishing kb r C) card L

variable {kb r C L}

/-- A distinguishing description with two pairs is shortest once neither the empty
description nor any single pair distinguishes. -/
theorem isShortest_of_card_two (hL : Distinguishing kb r C L) (h2 : L.card = 2)
    (h0 : ¬ Distinguishing kb r C ∅) (h1 : ∀ p, ¬ Distinguishing kb r C {p}) :
    IsShortest kb r C L :=
  minimalFor_iff_forall_lt.mpr ⟨hL, λ L' hlt hL' => by
    have : L'.card = 0 ∨ L'.card = 1 := by omega
    rcases this with h | h
    · obtain rfl := card_eq_zero.mp h
      exact h0 hL'
    · obtain ⟨p, rfl⟩ := card_eq_one.mp h
      exact h1 p hL'⟩

variable (kb r C L) [DecidableEq A] [DecidableEq V]

/-- A distinguishing description none of whose pairs can be dropped, Reiter's No Unnecessary
Components rule (§3.1.3). -/
def NoUnnecessary : Prop :=
  Distinguishing kb r C L ∧ ∀ p ∈ L, ¬ Distinguishing kb r C (L.erase p)

/-- A description with no unnecessary pair in which no set of pairs can be replaced by a
single new pair, Reiter's Local Brevity rule (§3.1.3). -/
def LocallyBrief : Prop :=
  NoUnnecessary kb r C L ∧
    ∀ S ⊆ L, 2 ≤ S.card → ∀ p, ¬ Distinguishing kb r C (insert p (L \ S))

instance : Decidable (NoUnnecessary kb r C L) := by unfold NoUnnecessary; infer_instance

variable {kb r C L}

/-- Reiter's first rule is subset-minimality among distinguishing descriptions. -/
theorem noUnnecessary_iff_minimal :
    NoUnnecessary kb r C L ↔ Minimal (Distinguishing kb r C) L := by
  refine ⟨fun h ↦ ⟨h.1, fun L' hL' hle ↦ ?_⟩, fun h ↦ ⟨h.1, fun p hp hd ↦ ?_⟩⟩
  · by_contra hne
    obtain ⟨p, hp, hp'⟩ := not_subset.mp hne
    refine h.2 p hp (distinguishing_iff.2
      ⟨fun q hq ↦ h.1.1 q (mem_of_mem_erase hq), fun c hc ↦ ?_⟩)
    obtain ⟨q, hq, hcq⟩ := (distinguishing_iff.1 hL').2 c hc
    exact ⟨q, mem_erase.mpr ⟨fun h ↦ hp' (h ▸ hq), hle hq⟩, hcq⟩
  · exact notMem_erase p L (h.2 hd (erase_subset p L) hp)

/-- A shortest description has no unnecessary pair, so Full Brevity never includes an
unnecessary modifier (§3.2.1). -/
theorem IsShortest.noUnnecessary (h : IsShortest kb r C L) : NoUnnecessary kb r C L :=
  ⟨h.1, λ _ hp => h.not_prop_of_lt (card_erase_lt_of_mem hp)⟩

/-- A shortest description is locally brief. -/
theorem IsShortest.locallyBrief (h : IsShortest kb r C L) : LocallyBrief kb r C L :=
  ⟨h.noUnnecessary, λ S hS hS2 p => h.not_prop_of_lt (by
    have h₁ := card_insert_le p (L \ S)
    have h₂ := card_sdiff_of_subset hS
    have h₃ := card_le_card hS
    omega)⟩

/-- Descriptions the exhaustive Full Brevity search checks, with `na` available attributes
and a shortest description of `nl` pairs (§3.1.1). -/
def fullBrevitySteps (na nl : ℕ) : ℕ := ∑ i ∈ Icc 1 nl, na.choose i

/-- The paper's four counts, six for §2.2's example, 175, over 6,000 and over 2,000,000. -/
theorem fullBrevitySteps_values :
    fullBrevitySteps 3 2 = 6 ∧ fullBrevitySteps 10 3 = 175 ∧
      6000 < fullBrevitySteps 20 4 ∧ 2000000 < fullBrevitySteps 50 5 := by
  decide +kernel

variable (kb) in
def greedyAux :
    ℕ → Finset E → List (A × V) → Description A V → Option (Description A V)
  | 0, C, _, L => if C.Nonempty then none else some L
  | n + 1, C, P, L =>
    if C.Nonempty then
      match P.argmin (λ p => (C.filter (Applies kb · p)).card) with
      | none => none
      | some p => greedyAux n (C.filter (Applies kb · p)) (P.erase p) (insert p L)
    else some L

variable (kb C) in
/-- Fig. 3's Greedy Heuristic, which from the properties `P` true of the referent adds the
one leaving the fewest distractors, the first in `P` on a tie, until none remain, and fails
when `P` runs out. -/
def greedy (P : List (A × V)) : Option (Description A V) := greedyAux kb P.length C P ∅

end Brevity

/-! ### The Incremental Algorithm (§4, Fig. 6) -/

/-- The three values of Fig. 6's UserKnows (§4.1): the user knows the pair holds of the
entity, knows it does not, or neither. -/
inductive Knowledge where
  | holds | fails | unknown
  deriving DecidableEq, Repr

section Incremental

variable {E A V : Type*}

/-- The head-noun attribute, basic-level values, value taxonomies and user model the host
system supplies (§4.1). -/
structure Domain (E A V : Type*) where
  /-- The attribute realized as the head noun (§2.2). -/
  type : A
  /-- The depth of the value taxonomies, bounding `findBestValue`'s descent. -/
  depth : ℕ
  /-- The basic-level value of an attribute for an entity (BasicLevelValue). -/
  basicLevel : E → A → Option V
  /-- The child of a value in the attribute's taxonomy that still subsumes the entity's own
  value (MoreSpecificValue). -/
  moreSpecific : E → A → V → Option V
  /-- What the user knows of the pair holding of the entity (UserKnows). -/
  userKnows : E → A → V → Knowledge

namespace Domain

variable (d : Domain E A V)

/-- A domain without value taxonomies whose user knows a pair to hold exactly when it is
accurate, the user model of §4.5. -/
def flat [DecidableEq V] (kb : KB E A V) (type : A) : Domain E A V where
  type := type
  depth := 0
  basicLevel := kb
  moreSpecific _ _ _ := none
  userKnows x a v := match kb x a with
    | some w => if w = v then .holds else .fails
    | none => .unknown

/-- Under the accuracy user model, what the user knows is what the knowledge base records. -/
theorem flat_userKnows [DecidableEq V] {kb : KB E A V} {t : A} (x : E) (a : A) (v : V) :
    ((flat kb t).userKnows x a v = .holds ↔ kb x a = some v) ∧
      ((flat kb t).userKnows x a v = .fails ↔ ∃ w, kb x a = some w ∧ w ≠ v) := by
  simp only [flat]
  split
  · next w hw => by_cases hwv : w = v <;> simp [hw, hwv]
  · next hw => simp [hw]

/-- The remaining distractors the user knows not to bear the pair (Fig. 6, RulesOut). -/
def rulesOut (C : Finset E) (a : A) (v : V) : Finset E :=
  C.filter λ x => d.userKnows x a v = .fails

/-- Fig. 6's FindBestValue, the initial value when the user knows it to hold of `r`, refined
to a more specific value only when that rules out more distractors. -/
def findBestValue (r : E) (C : Finset E) (a : A) : ℕ → V → Option V
  | 0, v => if d.userKnows r a v = .holds then some v else none
  | n + 1, v =>
    if d.userKnows r a v = .holds then
      some <| match d.moreSpecific r a v with
        | none => v
        | some more =>
          match findBestValue r C a n more with
          | none => v
          | some new =>
            if (d.rulesOut C a v).card < (d.rulesOut C a new).card then new else v
    else none

/-- `FindBestValue` returns only values the user knows to hold of the referent. -/
theorem findBestValue_userKnows (r : E) (C : Finset E) (a : A) :
    ∀ (n : ℕ) (v w : V), d.findBestValue r C a n v = some w → d.userKnows r a w = .holds
  | 0, v, w, h => by
    simp only [findBestValue] at h
    split_ifs at h with hv
    exact Option.some.inj h ▸ hv
  | n + 1, v, w, h => by
    simp only [findBestValue] at h
    split_ifs at h with hv
    obtain rfl := Option.some.inj h
    split
    · exact hv
    · split
      · exact hv
      next new hnew =>
        split_ifs
        · exact findBestValue_userKnows r C a n _ new hnew
        · exact hv

section

variable [DecidableEq A] [DecidableEq V]

/-- Fig. 6's return, which always includes a head noun, the basic-level type added without a
`UserKnows` check. -/
def withType (r : E) (L : Description A V) : Description A V :=
  if ∃ p ∈ L, p.1 = d.type then L
  else match d.basicLevel r d.type with
    | none => L
    | some b => insert (d.type, b) L

/-- The return never retracts a pair. -/
theorem withType_subset (r : E) (L : Description A V) : L ⊆ d.withType r L := by
  unfold withType
  split_ifs
  · exact subset_rfl
  · split
    · exact subset_rfl
    · exact subset_insert _ _

/-- The return adds at most the basic-level head noun. -/
theorem withType_mem (r : E) (L : Description A V) {p : A × V} (hp : p ∈ d.withType r L) :
    p ∈ L ∨ d.basicLevel r p.1 = some p.2 := by
  unfold withType at hp
  split_ifs at hp
  · exact .inl hp
  · split at hp
    · exact .inl hp
    next b hb =>
      rcases mem_insert.mp hp with rfl | hp
      · exact .inr hb
      · exact .inl hp

variable [DecidableEq E]

/-- One attribute of Fig. 6's loop, whose best value is kept when it rules out a remaining
distractor, those distractors being removed. -/
def step (r : E) (a : A) (C : Finset E) (L : Description A V) :
    Finset E × Description A V :=
  match d.basicLevel r a with
  | none => (C, L)
  | some b =>
    match d.findBestValue r C a d.depth b with
    | none => (C, L)
    | some v =>
      if (d.rulesOut C a v).Nonempty then (C \ d.rulesOut C a v, insert (a, v) L) else (C, L)

/-- A step never retracts a pair (§4.3). -/
theorem step_subset (r : E) (a : A) (C : Finset E) (L : Description A V) :
    L ⊆ (d.step r a C L).2 := by
  unfold step
  split
  · exact subset_rfl
  · split
    · exact subset_rfl
    · split_ifs
      · exact subset_insert _ _
      · exact subset_rfl

/-- A step adds only pairs the user knows to hold of the referent. -/
theorem step_mem (r : E) (a : A) (C : Finset E) (L : Description A V) {p : A × V}
    (hp : p ∈ (d.step r a C L).2) : p ∈ L ∨ d.userKnows r p.1 p.2 = .holds := by
  unfold step at hp
  split at hp
  · exact .inl hp
  next b _ =>
    split at hp
    · exact .inl hp
    next v hv =>
      split_ifs at hp
      · rcases mem_insert.mp hp with rfl | hp
        · exact .inr (d.findBestValue_userKnows r C a d.depth b v hv)
        · exact .inl hp
      · exact .inl hp

/-- Every distractor a step removes is ruled out by the pair the step adds. -/
theorem step_ruledOut (r : E) (a : A) (C : Finset E) (L : Description A V) {c : E}
    (hc : c ∈ C) (hc' : c ∉ (d.step r a C L).1) :
    ∃ p ∈ (d.step r a C L).2, d.userKnows c p.1 p.2 = .fails := by
  unfold step at hc' ⊢
  split at hc'
  · exact absurd hc hc'
  · split at hc'
    · exact absurd hc hc'
    · split_ifs at hc' ⊢
      · exact ⟨_, mem_insert_self _ _, by simpa [mem_sdiff, rulesOut, hc] using hc'⟩
      · exact absurd hc hc'

/-- Fig. 6's loop over the preferred attributes. -/
def loop (r : E) : Finset E → List A → Description A V → Option (Description A V)
  | _, [], _ => none
  | C, a :: rest, L =>
    let s := d.step r a C L
    if s.1.Nonempty then loop r s.1 rest s.2 else some (d.withType r s.2)

/-- Fig. 6's MakeReferringExpression, the Incremental Algorithm over the preferred
attributes `P`, failing when they run out before the contrast set does. -/
def makeReferringExpression (r : E) (C : Finset E) (P : List A) :
    Option (Description A V) :=
  d.loop r C P ∅

/-- The loop returns through `withType` a description that never retracts a pair, rules out
every remaining distractor and adds only pairs known to hold (§3.2.1's indelible
generation, §4.3). -/
theorem loop_spec (r : E) : ∀ (P : List A) (C : Finset E) (L L' : Description A V),
    d.loop r C P L = some L' → ∃ L₀, L' = d.withType r L₀ ∧ L ⊆ L₀ ∧
      (∀ c ∈ C, ∃ p ∈ L₀, d.userKnows c p.1 p.2 = .fails) ∧
        ∀ p ∈ L₀, p ∈ L ∨ d.userKnows r p.1 p.2 = .holds
  | [], _, _, _, h => nomatch h
  | a :: rest, C, L, L', h => by
    simp only [loop] at h
    split_ifs at h with hC
    · obtain ⟨L₀, rfl, hsub, hrule, hadm⟩ := loop_spec r rest _ _ L' h
      refine ⟨L₀, rfl, (d.step_subset r a C L).trans hsub, λ c hc => ?_, λ p hp => ?_⟩
      · by_cases hc' : c ∈ (d.step r a C L).1
        · exact hrule c hc'
        · obtain ⟨p, hp, hcp⟩ := d.step_ruledOut r a C L hc hc'
          exact ⟨p, hsub hp, hcp⟩
      · exact (hadm p hp).elim (λ h => d.step_mem r a C L h) .inr
    · obtain rfl := Option.some.inj h
      exact ⟨_, rfl, d.step_subset r a C L,
        λ c hc => d.step_ruledOut r a C L hc λ h => hC ⟨c, h⟩,
        λ p hp => d.step_mem r a C L hp⟩

/-- Fig. 6's output rules out every member of the contrast set (§4.3). -/
theorem makeReferringExpression_rulesOut {r : E} {C : Finset E} {P : List A}
    {L : Description A V} (h : d.makeReferringExpression r C P = some L) :
    ∀ c ∈ C, ∃ p ∈ L, d.userKnows c p.1 p.2 = .fails := by
  obtain ⟨L₀, rfl, -, hrule, -⟩ := d.loop_spec r P C ∅ L h
  exact λ c hc => (hrule c hc).imp λ p hp => ⟨d.withType_subset r _ hp.1, hp.2⟩

/-- Every pair of Fig. 6's output is known to the user to hold of the referent, except the
head noun added at the end, which is the basic-level type (§4.3). -/
theorem makeReferringExpression_mem {r : E} {C : Finset E} {P : List A}
    {L : Description A V} (h : d.makeReferringExpression r C P = some L) :
    ∀ p ∈ L, d.userKnows r p.1 p.2 = .holds ∨ d.basicLevel r p.1 = some p.2 := by
  obtain ⟨L₀, rfl, -, -, hadm⟩ := d.loop_spec r P C ∅ L h
  exact λ p hp => (d.withType_mem r L₀ hp).elim
    (λ h => .inl ((hadm p h).resolve_left (by simp))) .inr

/-- Fig. 6's output carries a head noun whenever the referent has a basic-level type
(§4.3). -/
theorem makeReferringExpression_type {r : E} {C : Finset E} {P : List A}
    {L : Description A V} (h : d.makeReferringExpression r C P = some L)
    (hb : (d.basicLevel r d.type).isSome) : ∃ v, (d.type, v) ∈ L := by
  obtain ⟨L₀, rfl, -, -, -⟩ := d.loop_spec r P C ∅ L h
  unfold withType
  split_ifs with hL
  · obtain ⟨⟨a, v⟩, hp, ha⟩ := hL
    exact ⟨v, ha ▸ hp⟩
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hb
    exact ⟨b, by simp [hb]⟩

/-- Under the accuracy user model the output is a distinguishing description (§2.2). -/
theorem flat_distinguishing {kb : KB E A V} {t : A} {r : E} {C : Finset E} {P : List A}
    {L : Description A V} (h : (flat kb t).makeReferringExpression r C P = some L) :
    Distinguishing kb r C L := by
  refine distinguishing_iff.mpr ⟨fun p hp ↦ ?_, fun c hc ↦ ?_⟩
  · exact ((flat kb t).makeReferringExpression_mem h p hp).elim
      (flat_userKnows r p.1 p.2).1.mp id
  · obtain ⟨p, hp, hcp⟩ := (flat kb t).makeReferringExpression_rulesOut h c hc
    obtain ⟨w, hw, hwv⟩ := (flat_userKnows c p.1 p.2).2.mp hcp
    exact ⟨p, hp, λ hap => hwv (Option.some.inj (hw.symm.trans hap))⟩

end

end Domain

end Incremental

/-! ### The paper's examples -/

/-- The head noun and the perceptual properties, the attributes of the paper's examples. -/
inductive Attr where
  | type
  | property (d : Degree.PropertyDomain)
  deriving DecidableEq, Repr, Fintype

/-- The values of the paper's examples. -/
inductive Value where
  | dog | cat | chihuahua | siameseCat | bird | cup
  | small | medium | large
  | black | white | red | green | blue
  | plastic | paper
  deriving DecidableEq, Repr, Fintype

/-! #### The two dogs and the cat (§2.2, §4.4) -/

/-- The three animals of §2.2 and §4.4. -/
inductive Animal where
  | object1 | object2 | object3
  deriving DecidableEq, Repr

namespace Animal

/-- The most specific values the system knows (§4.4). -/
def kb : KB Animal Attr Value
  | .object1, .type => some .chihuahua
  | .object1, .property .size => some .small
  | .object1, .property .color => some .black
  | .object2, .type => some .chihuahua
  | .object2, .property .size => some .large
  | .object2, .property .color => some .white
  | .object3, .type => some .siameseCat
  | .object3, .property .size => some .small
  | .object3, .property .color => some .black
  | _, _ => none

/-- The basic-level values of §2.2, dog, dog and cat. -/
def basicLevel (x : Animal) : Attr → Option Value
  | .type => match x with | .object3 => some .cat | _ => some .dog
  | a => kb x a

/-- The taxonomy of §4.4, the breeds below their basic-level types. -/
def parent : Value → Option Value
  | .chihuahua => some .dog
  | .siameseCat => some .cat
  | _ => none

/-- The domain of §4.4, in which the breeds are the only more specific values and the user
knows a pair to hold exactly when it is accurate under the taxonomy. -/
def domain : Domain Animal Attr Value where
  type := .type
  depth := 1
  basicLevel := basicLevel
  moreSpecific x a v := match kb x a with
    | some w => if parent w = some v then some w else none
    | none => none
  userKnows x a v := match kb x a with
    | some w => if w = v ∨ parent w = some v then .holds else .fails
    | none => .unknown

/-- The contrast set. -/
def contrast : Finset Animal := {.object2, .object3}

/-- *The black dog* and *the small dog* are distinguishing descriptions of Object1 (§2.2). -/
theorem black_dog_distinguishing :
    Distinguishing basicLevel .object1 contrast {(.type, .dog), (.property .color, .black)} ∧
    Distinguishing basicLevel .object1 contrast {(.type, .dog), (.property .size, .small)} := by
  decide +kernel

/-- No single pair distinguishes Object1, so *the black dog* is a shortest description
(§3.1.1's six steps). -/
theorem black_dog_isShortest :
    IsShortest basicLevel .object1 contrast {(.type, .dog), (.property .color, .black)} :=
  isShortest_of_card_two black_dog_distinguishing.1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The breed rules out no more distractors than the basic-level type, so `FindBestValue`
keeps *dog* (§4.4). -/
theorem findBestValue_type :
    domain.findBestValue .object1 contrast .type 1 .dog = some .dog := by decide +kernel

/-- With the preference order type, colour, size the algorithm returns *the black dog*; with
type, size, colour it returns *the small dog* (§4.4). -/
theorem makeReferringExpression_animal :
    domain.makeReferringExpression .object1 contrast
        [.type, .property .color, .property .size] =
      some {(.type, .dog), (.property .color, .black)} ∧
    domain.makeReferringExpression .object1 contrast
        [.type, .property .size, .property .color] =
      some {(.type, .dog), (.property .size, .small)} := by
  decide +kernel

end Animal

/-! #### The seven cups (§3.1.2) -/

/-- The seven cups of §3.1.2. -/
inductive Cup where
  | object1 | object2 | object3 | object4 | object5 | object6 | object7
  deriving DecidableEq, Repr

namespace Cup

/-- Size, colour and material of each cup. -/
def kb : KB Cup Attr Value
  | .object1, .property .size => some .large
  | .object1, .property .color => some .red
  | .object1, .property .material => some .plastic
  | .object2, .property .size => some .small
  | .object2, .property .color => some .red
  | .object2, .property .material => some .plastic
  | .object3, .property .size => some .small
  | .object3, .property .color => some .red
  | .object3, .property .material => some .paper
  | .object4, .property .size => some .medium
  | .object4, .property .color => some .red
  | .object4, .property .material => some .paper
  | .object5, .property .size => some .large
  | .object5, .property .color => some .green
  | .object5, .property .material => some .paper
  | .object6, .property .size => some .large
  | .object6, .property .color => some .blue
  | .object6, .property .material => some .paper
  | .object7, .property .size => some .large
  | .object7, .property .color => some .blue
  | .object7, .property .material => some .plastic
  | _, _ => none

/-- The contrast set for Object1. -/
def contrast : Finset Cup := {.object2, .object3, .object4, .object5, .object6, .object7}

/-- Object1's properties in the paper's order. -/
def properties : List (Attr × Value) :=
  [.property .size, .property .color, .property .material].filterMap λ a =>
    (kb .object1 a).map ((a, ·))

/-- The greedy heuristic selects plastic first, then large and red, giving *the large red
plastic cup* once the head noun is added (§3.1.2). -/
theorem greedy_cups :
    greedy kb contrast properties =
      some {(.property .material, .plastic), (.property .size, .large),
        (.property .color, .red)} := by
  decide +kernel

/-- *The large red cup* is the shortest description (§3.1.2). -/
theorem large_red_isShortest :
    IsShortest kb .object1 contrast {(.property .size, .large), (.property .color, .red)} :=
  isShortest_of_card_two (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The greedy result distinguishes Object1 but carries an unnecessary pair (§3.1.2,
§3.2.1). -/
theorem greedy_not_noUnnecessary :
    Distinguishing kb .object1 contrast
        {(.property .material, .plastic), (.property .size, .large),
          (.property .color, .red)} ∧
      ¬ NoUnnecessary kb .object1 contrast
        {(.property .material, .plastic), (.property .size, .large),
          (.property .color, .red)} := by
  decide +kernel

end Cup

/-! #### The white bird (§3.2.1) -/

/-- A picture of a white bird, a black cup and a white cup. -/
inductive Picture where
  | bird | blackCup | whiteCup
  deriving DecidableEq, Repr

namespace Picture

/-- Type and colour of each object. -/
def kb : KB Picture Attr Value
  | .bird, .type => some .bird
  | .bird, .property .color => some .white
  | .blackCup, .type => some .cup
  | .blackCup, .property .color => some .black
  | .whiteCup, .type => some .cup
  | .whiteCup, .property .color => some .white
  | _, _ => none

/-- The contrast set. -/
def contrast : Finset Picture := {.blackCup, .whiteCup}

/-- The paper's speaker scans the black cup and says *white*, then scans the white cup and
adds *bird*, which alone would have done (§3.2.1). The algorithm reproduces that output only
with colour before type in the preference order; type first yields *the bird*. -/
theorem makeReferringExpression_picture :
    (Domain.flat kb .type).makeReferringExpression .bird contrast [.property .color, .type] =
      some {(.property .color, .white), (.type, .bird)} ∧
    (Domain.flat kb .type).makeReferringExpression .bird contrast [.type, .property .color] =
      some {(.type, .bird)} := by
  decide +kernel

/-- The colour-first output contains an unnecessary modifier, the behaviour of
Observation 1 that Full Brevity and Local Brevity never produce (§3.2.1). -/
theorem white_bird_not_noUnnecessary :
    ¬ NoUnnecessary kb .bird contrast {(.property .color, .white), (.type, .bird)} ∧
    NoUnnecessary kb .bird contrast {(.type, .bird)} := by
  decide +kernel

end Picture

end DaleReiter1995
