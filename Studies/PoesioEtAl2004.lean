module

public import Linglib.Discourse.Centering.Transition
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Data.Examples.PoesioEtAl2004
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Dedup
public import Mathlib.Order.Prod.Lex.Basic
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Poesio, Stevenson, Di Eugenio and Hitzeman (2004): Centering: A Parametric Theory and Its Instantiations

This file formalizes the parametric reading of centering theory in
[poesio-stevenson-eugenio-hitzeman-2004]. The claims of [grosz-joshi-weinstein-1995], Constraint
1 on the uniqueness of the backward-looking center, Rule 1 on its pronominalization, and Rule 2
on the preference among transitions, can only be evaluated once the notions they quantify over
are fixed, and the literature has fixed them in several ways: what an utterance is, which
utterance counts as the previous one, when an entity is realized, which noun phrases introduce
forward-looking centers, how the centers are ranked, and which pronouns Rule 1 governs. Each
setting is an instantiation of the theory, and the paper's corpus study finds that different
instantiations make different claims true.

The instantiations are the substrate's parameters: the realization relation is the `Membership`
instance, the ranking is the `LinearOrder` on roles, the CF filter is `cfFilter`, the utterance
unit is `merge`, and the previous utterance is the argument of `cb`. The paper's illustrations
of each parameter are worked as such: the associative reference of (5) is a `Bridged`
realization (`ex5`), the second-person pronoun of (7) a filtered forward-looking center (`ex7`),
the egg vases of (9) recovered either by sentence units or by indirect realization (`ex9`), the
tie of (10) two backward-looking centers under grammatical-function ranking and one under its
linear disambiguation (`ex10`), and the adjunct clauses of (14) and (16) the two definitions of
the previous utterance pulling in opposite directions (`ex14`, `ex16`). Constraint 1 is
unpacked into CB uniqueness and entity continuity (`strong_iff`), uniqueness holds under any
ranking that separates the previous utterance's realizations (`cbAll_length_le_one`), the three
forms of Rule 1 are ordered (`CbPronominalized.rule1Original`), and the four-way transition
classification of [brennan-friedman-pollard-1987] refines the three-way one with its
preference order (`bfp_toTransition`, `toTransition_mono`).

## Implementation notes

The corpus statistics of Tables 1 to 15, the statistical tests, and the trade-off they reveal
between Rule 1 on the one hand and Constraint 1 and Rule 2 on the other are not formalized; the
examples carry the mechanisms the statistics measure. Utterance identification, segmentation,
and the Walker heuristics are corpus-operational choices and are represented only by the way
the examples are cut into utterances.

## References

* [poesio-stevenson-eugenio-hitzeman-2004]
* [grosz-joshi-weinstein-1995]
* [brennan-friedman-pollard-1987]
* [strube-hahn-1999]
-/

@[expose] public section

namespace PoesioEtAl2004

open Discourse.Centering

variable {E R : Type*}

/-! ### Constraint 1 unpacked (§5.3.2, §5.3.4) -/

section Constraint1

variable [DecidableEq E] [LinearOrder R] {U : Type*} [Membership E U]
  [∀ (u : U) (e : E), Decidable (e ∈ u)]

/-- The backward-looking centers of `cur` after `prev` under a partial ranking: the entities of
the highest-ranked realizations in `prev` that `cur` realizes, each once. Under a ranking that
separates the realizations there is at most one. -/
def cbAll (prev : Utterance E R) (cur : U) : List E :=
  let realized := prev.realizations.filter (·.entity ∈ cur)
  match realized.argmax (·.role) with
  | none => []
  | some top => ((realized.filter (·.role = top.role)).map (·.entity)).dedup

/-- CB uniqueness: at most one backward-looking center, the weak form of Constraint 1. -/
def CBUniqueness (prev : Utterance E R) (cur : U) : Prop := (cbAll prev cur).length ≤ 1

/-- Entity continuity: the utterance realizes some forward-looking center of the previous one. -/
def EntityContinuity (prev : Utterance E R) (cur : U) : Prop := 1 ≤ (cbAll prev cur).length

/-- The strong form of Constraint 1: exactly one backward-looking center. -/
def Constraint1Strong (prev : Utterance E R) (cur : U) : Prop := (cbAll prev cur).length = 1

instance (prev : Utterance E R) (cur : U) : Decidable (CBUniqueness prev cur) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (prev : Utterance E R) (cur : U) : Decidable (EntityContinuity prev cur) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (prev : Utterance E R) (cur : U) : Decidable (Constraint1Strong prev cur) :=
  inferInstanceAs (Decidable (_ = _))

/-- Strong Constraint 1 is CB uniqueness together with entity continuity. -/
theorem strong_iff (prev : Utterance E R) (cur : U) :
    Constraint1Strong prev cur ↔ CBUniqueness prev cur ∧ EntityContinuity prev cur := by
  unfold Constraint1Strong CBUniqueness EntityContinuity
  omega

theorem cbAll_length_le_one (prev : Utterance E R) (cur : U)
    (h : ∀ r₁ ∈ prev.realizations, ∀ r₂ ∈ prev.realizations,
      r₁.role = r₂.role → r₁.entity = r₂.entity) :
    (cbAll prev cur).length ≤ 1 := by
  dsimp only [cbAll]
  split
  · simp
  next top hm =>
    have htop : top ∈ prev.realizations :=
      List.mem_of_mem_filter (List.argmax_mem (Option.mem_def.2 hm))
    rw [← List.card_toFinset]
    refine (Finset.card_le_card fun e he ↦ Finset.mem_singleton.2 ?_).trans
      (Finset.card_singleton top.entity).le
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 he)
    obtain ⟨hr₁, hr₂⟩ := List.mem_filter.1 hr
    exact h r (List.mem_of_mem_filter hr₁) top htop (by simpa using hr₂)

end Constraint1

/-! ### Rule 1 in its three forms (§2.3.2) -/

section Rule1

variable [DecidableEq E] [LinearOrder R]

/-- Rule 1 in its original form: a backward-looking center kept from the previous utterance is
pronominalized. The form of [grosz-joshi-weinstein-1995] is `PronominalizationConstraint`, and
the unconditional form is `CbPronominalized`. -/
def Rule1Original (prev cur : Utterance E R) (prevCb : Option E) : Prop :=
  (∃ c, cb prev cur = some c ∧ prevCb = some c) → CbPronominalized prev cur

theorem CbPronominalized.rule1Original {prev cur : Utterance E R} (prevCb : Option E)
    (h : CbPronominalized prev cur) : Rule1Original prev cur prevCb :=
  fun _ ↦ h

end Rule1

/-! ### Transitions (§2.2.3, §2.3.3) -/

/-- The four transitions of [brennan-friedman-pollard-1987]: the center is kept, or the previous
utterance had none, and is the preferred center (continue) or not (retain); or the center
changes and is the preferred center (smooth shift) or not (rough shift). -/
inductive BFPTransition where
  | continue
  | retain
  | smoothShift
  | roughShift
  deriving DecidableEq, Repr, Fintype

/-- Rule 2 on single transitions: continue over retain over smooth shift over rough shift. -/
def BFPTransition.rank : BFPTransition → ℕ
  | .continue => 3
  | .retain => 2
  | .smoothShift => 1
  | .roughShift => 0

instance : LinearOrder BFPTransition := LinearOrder.lift' BFPTransition.rank (by decide)

/-- The three-way transition each four-way one refines. -/
def BFPTransition.toTransition : BFPTransition → Transition
  | .continue => .continuation
  | .retain => .retaining
  | .smoothShift | .roughShift => .shifting

/-- The four-way preference order refines the three-way one. -/
theorem toTransition_mono {t₁ t₂ : BFPTransition} (h : t₁ ≤ t₂) :
    t₁.toTransition ≤ t₂.toTransition := by
  revert t₁ t₂; decide

section Transitions

variable [DecidableEq E] [LinearOrder R]

/-- The four-way classification of an utterance after an utterance with center `prevCb`, `none`
for an utterance with no center. -/
def bfp (prev cur : Utterance E R) (prevCb : Option E) : Option BFPTransition :=
  (cb prev cur).map fun c ↦
    if ∀ p ∈ prevCb, p = c then if cur.cp = some c then .continue else .retain
    else if cur.cp = some c then .smoothShift else .roughShift

theorem bfp_eq_none_iff (prev cur : Utterance E R) (prevCb : Option E) :
    bfp prev cur prevCb = none ↔ cb prev cur = none := by
  simp [bfp]

theorem bfp_toTransition {prev cur : Utterance E R} {prevCb : Option E} {t : BFPTransition}
    (h : bfp prev cur prevCb = some t) :
    t.toTransition = transition prevCb prev cur := by
  unfold bfp transition at *
  rcases hc : cb prev cur with _ | c
  · simp [hc] at h
  · rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rw [Transition.ofCenters_some]
    split_ifs <;> rfl

end Transitions

/-! ### The parameters (§2.4, §3.4) -/

/-- The CF filter: only the entities satisfying `p` introduce forward-looking centers, as when
first- and second-person pronouns or predicative noun phrases are excluded. -/
def cfFilter (p : E → Bool) (u : Utterance E R) : Utterance E R :=
  ⟨u.realizations.filter fun r ↦ p r.entity⟩

/-- The utterance unit: clauses merged into one sentence-sized utterance. -/
def merge (us : List (Utterance E R)) : Utterance E R := ⟨(us.map (·.realizations)).flatten⟩

/-- An utterance with the anchors of its associative references, each mention paired with the
entity it indirectly realizes. -/
structure Bridged (E R : Type*) where
  utt : Utterance E R
  anchors : List (E × E)

/-- Indirect realization: an entity is realized when mentioned or when anchored by a mention. -/
instance : Membership E (Bridged E R) :=
  ⟨fun b e ↦ e ∈ b.utt ∨ ∃ a ∈ b.anchors, a.2 = e ∧ a.1 ∈ b.utt⟩

instance [DecidableEq E] (b : Bridged E R) (e : E) : Decidable (e ∈ b) :=
  inferInstanceAs (Decidable (e ∈ b.utt ∨ ∃ a ∈ b.anchors, a.2 = e ∧ a.1 ∈ b.utt))

/-- Grammatical function with linear-order disambiguation: the role together with the surface
position, an earlier mention outranking a later one of the same function. -/
abbrev GFLin (n : ℕ) := Lex (GrammaticalRole × (Fin n)ᵒᵈ)

/-- A realization by a name in role `r` at surface position `i`. -/
def GFLin.name {E : Type*} {n : ℕ} (e : E) (r : GrammaticalRole) (i : Fin n) :
    Realization E (GFLin n) :=
  ⟨e, toLex (r, OrderDual.toDual i), false⟩

/-- The three tiers of information status of [strube-hahn-1999], the ranking of §4.4.3. -/
inductive InfoStatus where
  | hearerOld
  | mediated
  | hearerNew
  deriving DecidableEq, Repr, Fintype

/-- Hearer-old entities outrank mediated ones, which outrank hearer-new ones. -/
def InfoStatus.rank : InfoStatus → ℕ
  | .hearerOld => 2
  | .mediated => 1
  | .hearerNew => 0

instance : LinearOrder InfoStatus := LinearOrder.lift' InfoStatus.rank (by decide)

/-! ### The illustrations -/

section Examples

/-- The entities of (5). -/
inductive Ent5 where
  | john
  | house
  | door
  deriving DecidableEq, Repr

/-- (5): *John walked toward the house. The door was open.* Under direct realization the second
utterance has no backward-looking center; with the door anchored to the house it has one. -/
theorem ex5 :
    let u1 : Utterance Ent5 GrammaticalRole := ⟨[⟨.john, .subject, false⟩, ⟨.house, .other, false⟩]⟩
    let u2 : Utterance Ent5 GrammaticalRole := ⟨[⟨.door, .subject, false⟩]⟩
    cb u1 u2 = none ∧
      cb u1 (⟨u2, [(.door, .house)]⟩ : Bridged Ent5 GrammaticalRole) = some .house := by
  decide

/-- The entities of (7). -/
inductive Ent7 where
  | you
  | productZ
  deriving DecidableEq, Repr

/-- (7): with the second-person pronoun introducing a forward-looking center every utterance has
one; without it the if-clause has none, and the third utterance has one only when the
if-clause is treated as embedded and the first utterance is its previous utterance. -/
theorem ex7 :
    let u1 : Utterance Ent7 GrammaticalRole :=
      ⟨[⟨.you, .subject, true⟩, ⟨.productZ, .object, false⟩]⟩
    let u2 : Utterance Ent7 GrammaticalRole := ⟨[⟨.you, .subject, true⟩]⟩
    let u3 : Utterance Ent7 GrammaticalRole :=
      ⟨[⟨.you, .subject, true⟩, ⟨.productZ, .object, false⟩]⟩
    let f := cfFilter (· != Ent7.you)
    (cb u1 u2 = some .you ∧ cb u2 u3 = some .you) ∧
      cb (f u1) (f u2) = none ∧ cb (f u2) (f u3) = none ∧ cb (f u1) (f u3) = some .productZ := by
  decide

/-- The entities of (9). -/
inductive Ent9 where
  | vases
  | bases
  | bodies
  | straw
  | handles
  | eggs
  | nests
  | finial
  | lid
  deriving DecidableEq, Repr

/-- (9): with finite clauses as utterances none of the four clauses after the first has a
backward-looking center; with sentences as utterances the second sentence continues the egg
vases, as does the second clause once its bases and bodies are anchored to the vases. -/
theorem ex9 :
    let u1 : Utterance Ent9 GrammaticalRole := ⟨[⟨.vases, .subject, false⟩]⟩
    let u2 : Utterance Ent9 GrammaticalRole :=
      ⟨[⟨.bases, .subject, false⟩, ⟨.bodies, .object, false⟩]⟩
    let u3 : Utterance Ent9 GrammaticalRole :=
      ⟨[⟨.straw, .subject, false⟩, ⟨.handles, .object, false⟩]⟩
    let u4 : Utterance Ent9 GrammaticalRole :=
      ⟨[⟨.eggs, .subject, false⟩, ⟨.nests, .other, false⟩, ⟨.finial, .other, false⟩,
        ⟨.lid, .other, false⟩]⟩
    let u5 : Utterance Ent9 GrammaticalRole := ⟨[⟨.vases, .subject, false⟩]⟩
    (cb u1 u2 = none ∧ cb u2 u3 = none ∧ cb u3 u4 = none ∧ cb u4 u5 = none) ∧
      cb (merge [u1, u2, u3, u4]) u5 = some .vases ∧
      cb u1 (⟨u2, [(.bases, .vases), (.bodies, .vases)]⟩ : Bridged Ent9 GrammaticalRole)
        = some .vases := by
  decide

/-- The entities of (10). -/
inductive Ent10 where
  | drawing
  | cupboard
  | branicki
  | dubois
  | dealer
  deriving DecidableEq, Repr

/-- (10): the corner cupboard and Branicki tie under grammatical-function ranking, so both are
backward-looking centers of the next utterance, against CB uniqueness; with linear-order
disambiguation the earlier mention, the cupboard, is the unique one. -/
theorem ex10 :
    let u227 : Utterance Ent10 GrammaticalRole :=
      ⟨[⟨.drawing, .subject, false⟩, ⟨.cupboard, .other, false⟩, ⟨.branicki, .other, false⟩]⟩
    let u229 : Utterance Ent10 GrammaticalRole :=
      ⟨[⟨.dubois, .subject, false⟩, ⟨.dealer, .other, false⟩, ⟨.cupboard, .object, false⟩,
        ⟨.branicki, .other, false⟩]⟩
    let v227 : Utterance Ent10 (GFLin 4) :=
      ⟨[GFLin.name .drawing .subject 0, GFLin.name .cupboard .other 1,
        GFLin.name .branicki .other 2]⟩
    let v229 : Utterance Ent10 (GFLin 4) :=
      ⟨[GFLin.name .dubois .subject 0, GFLin.name .dealer .other 1,
        GFLin.name .cupboard .object 2, GFLin.name .branicki .other 3]⟩
    (cbAll u227 u229).length = 2 ∧ ¬ CBUniqueness u227 u229 ∧ EntityContinuity u227 u229 ∧
      cbAll v227 v229 = [.cupboard] := by
  decide

/-- The entities of (14) and (16). -/
inductive Ent14 where
  | john
  | bill
  | door
  | appointment
  | scissors
  | you
  | patch
  deriving DecidableEq, Repr

/-- (14) and (16): the two definitions of the previous utterance of a clause after an adjunct
clause pull in opposite directions. In (14) the main clause supplies the center *John* that the
when-clause lacks, in (16) the adjunct clause supplies the center *the patch* that the main
clause lacks. -/
theorem ex14_ex16 :
    let u1 : Utterance Ent14 GrammaticalRole := ⟨[⟨.john, .subject, false⟩]⟩
    let u2 : Utterance Ent14 GrammaticalRole :=
      ⟨[⟨.bill, .subject, false⟩, ⟨.door, .object, false⟩]⟩
    let u3 : Utterance Ent14 GrammaticalRole :=
      ⟨[⟨.john, .subject, true⟩, ⟨.appointment, .object, false⟩]⟩
    let v1 : Utterance Ent14 GrammaticalRole := ⟨[⟨.scissors, .object, false⟩]⟩
    let v2 : Utterance Ent14 GrammaticalRole :=
      ⟨[⟨.you, .subject, true⟩, ⟨.patch, .object, false⟩]⟩
    let v3 : Utterance Ent14 GrammaticalRole := ⟨[⟨.patch, .object, false⟩]⟩
    (cb u2 u3 = none ∧ cb u1 u3 = some .john) ∧ (cb v2 v3 = some .patch ∧ cb v1 v3 = none) := by
  decide

/-- The entities of (23). -/
inductive Ent23 where
  | leaflet
  | summary
  | info
  | productA
  | questions
  | treatment
  | doctor
  | pharmacist
  deriving DecidableEq, Repr

/-- (23): with the second-person pronoun excluded, no utterance realizes a forward-looking
center of the previous one, so entity coherence is absent throughout a coherent text. -/
theorem ex23 :
    let u1 : Utterance Ent23 GrammaticalRole :=
      ⟨[⟨.leaflet, .subject, false⟩, ⟨.summary, .other, false⟩, ⟨.info, .other, false⟩,
        ⟨.productA, .other, false⟩]⟩
    let u2 : Utterance Ent23 GrammaticalRole :=
      ⟨[⟨.questions, .object, false⟩, ⟨.treatment, .other, false⟩]⟩
    let u3 : Utterance Ent23 GrammaticalRole :=
      ⟨[⟨.doctor, .object, false⟩, ⟨.pharmacist, .other, false⟩]⟩
    cb u1 u2 = none ∧ cb u2 u3 = none := by
  decide

end Examples

end PoesioEtAl2004
