module

public import Linglib.Data.Examples.Elbourne2026
public import Linglib.Semantics.Modification.Classification
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Powerset

/-!
# Elbourne (2026): Adjectives without syntactic categories

Elbourne's ⟨et,et⟩ theory gives every adjective the type of a function from noun meanings to noun
meanings, the type of Parsons and Lewis, so that an adjective combines with its noun by
functional application and no rule of predicate modification is needed. In predicative position
a copula applies the adjective to the trivial noun and quantifies over a time in the tense
relation, and a second meaning of the indefinite article gives *a dog* the same type. Adjectives
that never stand alone in predicative position, such as *former*, bear a compulsory selector
feature that the copula cannot select for. The relational *local*, the scope contrast of
*young alleged murderer*, and gradable adjectives under a positive morpheme all stay within the
type.

## Implementation notes

* The carrier is the substrate's `Modifier (I → E → Prop)`, properties indexed by times, with
  times first, where the article's `⟨e,it⟩` takes the entity first; conjuncts are likewise
  reordered. An intersective adjective is `Modifier.intersective Q`, meet with the property `Q`,
  and the article's second meaning of the indefinite article (32) is that same function, so
  *a dog* is `Modifier.intersective dog`.
* The syntax of §2 is represented only by the optional/compulsory distinction among selector
  features of (8), on which the attributive/predicative distribution rests; Predicate
  Abstraction and traces are Lean binders, and the meanings composed in §2.3 and §3.5 are
  stated with the article's truth conditions. The thematic relations and culmination function of
  (8) are the fields of `Frame`.
* The examples are `Data.Examples.Elbourne2026`.

## References

* [elbourne-2026]
* [elbourne-2024]
* [heim-kratzer-1998]
* [kamp-1975]
* [kamp-partee-1995]
* [parsons-1970]
* [lewis-1970]
* [montague-1973]
* [beesley-1982]
* [morzycki-2015]
* [mcnally-boleda-2004]
* [kennedy-2012]
* [bolinger-1967]
* [cresswell-1976]
-/

@[expose] public section

namespace Elbourne2026

open Modifier Elbourne2026.Examples

section Theory

variable {I E : Type*}

/-! ### Attributive position -/

/-- Applying the intersective *cute* to *donkey* gives at each time the meet of the two extensions
((24)–(26)). -/
theorem intersective_apply_time (Q N : I → E → Prop) (t : I) :
    Modifier.intersective Q N t = Modifier.intersective (Q t) (N t) :=
  rfl

/-! ### Predicative position -/

/-- The copula of (8), `λR⟨i,it⟩.λG⟨eit,eit⟩.λx.λt.∃t'(R(t')(t) & G(λy.λt''.⊤)(x)(t'))`, applies
the adjective to the trivial noun at a time that the tense relation `R` locates. -/
def copula (R : I → I → Prop) (G : Modifier (I → E → Prop)) : I → E → Prop :=
  fun t x ↦ ∃ t', R t' t ∧ G ⊤ t' x

theorem copula_intersective (R : I → I → Prop) (Q : I → E → Prop) :
    copula R (Modifier.intersective Q) = fun t x ↦ ∃ t', R t' t ∧ Q t' x := by
  funext t x
  simp only [copula, Modifier.intersective, inf_top_eq]

/-- *Fido was cute* (28)–(30) means `λt.∃t'(<(t')(t) & cute(o)(t'))`. -/
theorem fido_was_cute [LT I] (cute : I → E → Prop) (o : E) (t : I) :
    copula (· < ·) (Modifier.intersective cute) t o ↔ ∃ t' < t, cute t' o := by
  rw [copula_intersective]

/-- The second meaning (32) of the indefinite article is `Modifier.intersective`, so the copula
takes *a dog* in *Fido is a dog* ((31)–(33)). -/
theorem fido_is_a_dog (R : I → I → Prop) (dog : I → E → Prop) (o : E) (t : I) :
    copula R (Modifier.intersective dog) t o ↔ ∃ t', R t' t ∧ dog t' o := by
  rw [copula_intersective]

/-! ### Non-subsective adjectives -/

/-- *former* (44), (60) denotes `λf⟨e,it⟩.λx.λt.∃t'(<(t')(t) & f(x)(t') & ¬f(x)(t))`, asserting
both the positive and the negative condition. -/
def former [LT I] : Modifier (I → E → Prop) :=
  fun N t x ↦ (∃ t' < t, N t' x) ∧ ¬ N t x

/-- *John was a former judge* (45)–(46) means
`λt.∃t'(<(t')(t) & ∃t''(<(t'')(t') & judge(j)(t'') & ¬judge(j)(t')))`. -/
theorem john_was_a_former_judge [LT I] (judge : I → E → Prop) (j : E) (t : I) :
    copula (· < ·) (Modifier.intersective (former judge)) t j ↔
      ∃ t' < t, (∃ t'' < t', judge t'' j) ∧ ¬ judge t' j := by
  rw [copula_intersective]
  exact Iff.rfl

/-- A former N at `t` is not an N at `t` (§3.4), so *former* is privative in Kamp's sense. -/
theorem former_isPrivative [LT I] : Modifier.IsPrivative (former : Modifier (I → E → Prop)) :=
  Modifier.isPrivative_iff_forall.mpr fun _ _ _ h ↦ h.2

theorem former_not_isSubsective [Preorder I] {t' t : I} (h : t' < t) [Nonempty E] :
    ¬ Modifier.IsSubsective (former : Modifier (I → E → Prop)) :=
  Modifier.IsPrivative.not_isSubsective former_isPrivative
    ⟨fun s _ ↦ s = t', t, Classical.arbitrary E, ⟨t', h, rfl⟩, h.ne'⟩

/-- No property combined intersectively with a noun gives the meaning of *former* (§3.3–3.4). -/
theorem intersective_ne_former [Preorder I] {t' t : I} (h : t' < t) [Nonempty E]
    (Q : I → E → Prop) : Modifier.intersective Q ≠ former :=
  fun e ↦ former_not_isSubsective h
    (e ▸ Modifier.intersective_isIntersective Q : Modifier.IsIntersective former).isSubsective

/-! ### Relational adjectives -/

/-- *localᵢ* (54) denotes `λf⟨e,it⟩.λx.λt.f(x)(t) & local(x)(σ(i))(t)`. The relatum `z` is the
value of the index under the assignment, so the adjective stays within the type rather than
taking an internal argument. -/
def localTo (near : I → E → E → Prop) (z : E) : Modifier (I → E → Prop) :=
  Modifier.intersective fun t x ↦ near t x z

/-- A frame interprets the non-logical constants of the fragment (8), the thematic relations and
the culmination function on events. -/
structure Frame (I E S : Type*) where
  /-- `Agent(e)(x)`. -/
  agent : S → E → Prop
  /-- `Theme(e)(x)`. -/
  theme : S → E → Prop
  /-- `CUL(e)`, the last time at which the event obtains. -/
  cul : S → I

variable {S : Type*}

/-- *every* (8) denotes `λf⟨e,it⟩.λg⟨e,it⟩.λt.∀x(f(x)(t) → g(x)(t))`. -/
def every (f g : I → E → Prop) (t : I) : Prop := ∀ x, f t x → g t x

/-- *some* and the quantificational *a* (8) denote `λf⟨e,it⟩.λg⟨e,it⟩.λt.∃x(f(x)(t) & g(x)(t))`. -/
def indefinite (f g : I → E → Prop) (t : I) : Prop := ∃ x, f t x ∧ g t x

/-- *everyone* (56a) denotes `λf⟨e,it⟩.λt.∀x(person(x)(t) → f(x)(t))`. -/
def everyone (person g : I → E → Prop) (t : I) : Prop := ∀ x, person t x → g t x

/-- A transitive verb such as *inspect* (8) or *enter* (56d) denotes
`λR⟨i,it⟩.λx.λe.λt.P(e) & Theme(e)(x) & R(CUL(e))(t)`. -/
def Frame.transitive (F : Frame I E S) (P : S → Prop) (R : I → I → Prop) (x : E) (e : S)
    (t : I) : Prop :=
  P e ∧ F.theme e x ∧ R (F.cul e) t

/-- Little v (8), (56f) denotes `λF⟨s,it⟩.λx.λt.∃e(F(e)(t) & Agent(e)(x))`. -/
def Frame.littleV (F : Frame I E S) (G : S → I → Prop) : I → E → Prop :=
  fun t x ↦ ∃ e, G e t ∧ F.agent e x

-- (20), (21), (14)
theorem inverse_scope [LT I] (F : Frame I E S) (woman donkey : I → E → Prop)
    (inspection : S → Prop) (t : I) :
    indefinite donkey
        (fun t x ↦ every woman (F.littleV (F.transitive inspection (· < ·) x)) t) t ↔
      ∃ x, donkey t x ∧ ∀ y, woman t y →
        ∃ e, inspection e ∧ F.theme e x ∧ F.cul e < t ∧ F.agent e y := by
  simp only [indefinite, every, Frame.littleV, Frame.transitive, and_assoc]

-- (22), (23)
theorem surface_scope [LT I] (F : Frame I E S) (woman donkey : I → E → Prop)
    (inspection : S → Prop) (t : I) :
    every woman
        (fun t y ↦ indefinite donkey
          (fun t x ↦ F.littleV (F.transitive inspection (· < ·) x) t y) t) t ↔
      ∀ y, woman t y → ∃ x, donkey t x ∧
        ∃ e, inspection e ∧ F.theme e x ∧ F.cul e < t ∧ F.agent e y := by
  simp only [indefinite, every, Frame.littleV, Frame.transitive, and_assoc]

-- (55), (58)
theorem everyone_entered_a_local_bar [LT I] (F : Frame I E S) (person bar : I → E → Prop)
    (near : I → E → E → Prop) (entering : S → Prop) (t : I) :
    everyone person
        (fun t x ↦ indefinite (localTo near x bar)
          (fun t y ↦ F.littleV (F.transitive entering (· < ·) y) t x) t) t ↔
      ∀ x, person t x → ∃ y, near t y x ∧ bar t y ∧
        ∃ e, entering e ∧ F.theme e y ∧ F.cul e < t ∧ F.agent e x := by
  simp only [everyone, indefinite, localTo, intersective_apply₂, Frame.littleV, Frame.transitive,
    and_assoc]

end Theory

/-! ### Selector features and the two positions -/

/-- The selector features `E_L` and `E_R` (1) trigger External Merge (4) with a constituent to
the left or to the right. -/
inductive Selector
  | eL
  | eR
  deriving DecidableEq

/-- The syntactic features of a lexical entry (8) are the compulsory ones and, in angle brackets,
the optional ones. -/
structure Features where
  /-- Features every use of the entry carries. -/
  compulsory : Finset Selector
  /-- Features an entry may enter the derivation with or without. -/
  optional : Finset Selector
  deriving DecidableEq

namespace Features

/-- An entry can enter a derivation with its compulsory features together with any choice of its
optional ones. -/
def bundles (f : Features) : Finset (Finset Selector) :=
  f.optional.powerset.image (f.compulsory ∪ ·)

/-- An entry takes a noun to its right by External Merge (4a) when one of its bundles carries
`E_R`. -/
def TakesNoun (f : Features) : Prop := ∃ b ∈ f.bundles, Selector.eR ∈ b

/-- By Argument Interpretability (6) a constituent selected by a selector feature, as the
adjective is by the copula's `E_R`, contains no uninterpretable feature, so an entry is selectable
when one of its bundles is empty. -/
def Selectable (f : Features) : Prop := ∅ ∈ f.bundles

instance (f : Features) : Decidable f.TakesNoun :=
  inferInstanceAs (Decidable (∃ b ∈ f.bundles, _))

instance (f : Features) : Decidable f.Selectable :=
  inferInstanceAs (Decidable (_ ∈ _))

theorem selectable_iff (f : Features) : f.Selectable ↔ f.compulsory = ∅ := by
  simp only [Selectable, bundles, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, _, h⟩
    exact (Finset.union_eq_empty.mp h).1
  · intro h
    exact ⟨∅, Finset.empty_subset _, by rw [h, Finset.empty_union]⟩

theorem takesNoun_iff (f : Features) : f.TakesNoun ↔ Selector.eR ∈ f.compulsory ∪ f.optional := by
  simp only [TakesNoun, bundles, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, ⟨_, ha, rfl⟩, h⟩
    exact Finset.union_subset_union_right ha h
  · intro h
    exact ⟨_, ⟨f.optional, Finset.Subset.refl _, rfl⟩, h⟩

/-- *cute* (8) has an optional `E_R`, so it takes a noun in attributive position and, without the
feature, is selected by the copula. -/
def cute : Features := ⟨∅, {Selector.eR}⟩

/-- *former* and *mere* (§3.2) have a compulsory `E_R`, so they never stand alone in predicative
position, which accounts for (42) and, together with the types, for (36). -/
def former : Features := ⟨{Selector.eR}, ∅⟩

/-- Russian short-form adjectives (§4.2) have no selector features, so they cannot take nouns but
are selectable by the copula. -/
def shortForm : Features := ⟨∅, ∅⟩

/-- Russian long-form adjectives (§4.2) have optional `E_R` and `E_L`, so they take both
positions. -/
def longForm : Features := ⟨∅, {Selector.eR, Selector.eL}⟩

end Features

/-- The two positions of an adjective. -/
inductive Position
  | attributive
  | predicative
  deriving DecidableEq

/-- An adjective is licensed in attributive position by `E_R`, for External Merge with a noun,
and in predicative position by an empty bundle, for selection by the copula. -/
def Features.Licensed (f : Features) : Position → Prop
  | .attributive => f.TakesNoun
  | .predicative => f.Selectable

instance (f : Features) : ∀ p, Decidable (f.Licensed p)
  | .attributive => inferInstanceAs (Decidable f.TakesNoun)
  | .predicative => inferInstanceAs (Decidable f.Selectable)

/-- The entries as named in the rows. -/
def entryTable : List (String × Features) :=
  [("cute", .cute), ("former", .former), ("long form", .longForm), ("short form", .shortForm)]

/-- The positions as named in the rows. -/
def positionTable : List (String × Position) :=
  [("attributive", .attributive), ("predicative", .predicative)]

/-- The features decide the acceptability of *cute* and *former* in predicative position, (28),
(36) and (42), and of the Russian forms in both positions, (64)–(65). -/
theorem rows_licensed :
    ∀ e ∈ [ex_28, ex_36, ex_42, ex_64_long, ex_64_short, ex_65a, ex_65b],
      ∀ f, e.parse? "entry" entryTable = some f →
        ∀ p, e.parse? "position" positionTable = some p →
          (e.judgment = .acceptable ↔ f.Licensed p) := by
  decide

/-! ### Replies to criticisms -/

section Replies

variable {I E : Type*}

-- (92a)
theorem intersective_outer (Y N : I → E → Prop) (M : Modifier (I → E → Prop)) (t : I) (x : E)
    (h : Modifier.intersective Y (M N) t x) : Y t x :=
  h.1

/-- *Former* applied to an intersectively modified noun need not commit to the modifier, as in
*alleged young murderer* (92b). -/
theorem exists_inner_not_committed :
    ∃ (Y N : Bool → Unit → Prop) (t : Bool) (x : Unit),
      former (Modifier.intersective Y N) t x ∧ ¬ Y t x :=
  ⟨fun s _ ↦ s = false, ⊤, true, (),
    ⟨⟨false, by decide, rfl, trivial⟩, fun h ↦ absurd h.1 (by decide)⟩, by decide⟩

variable {D : Type*}

/-- A gradable adjective with a degree argument (100) denotes
`λd.λf⟨e,it⟩.λx.λt.f(x)(t) & tall(x)(t)(d)`, of type ⟨d,eiteit⟩. -/
def gradable (P : I → E → D → Prop) (d : D) : Modifier (I → E → Prop) :=
  Modifier.intersective fun t x ↦ P t x d

/-- The positive morpheme of [cresswell-1976] in the form (104),
`λG⟨d,et⟩.λx.∃d(d > standard(G) & G(d)(x))`, is transposed to ⟨d,eiteit⟩ as §4.6 proposes. -/
def pos [LT D] (standard : (D → Modifier (I → E → Prop)) → D) (G : D → Modifier (I → E → Prop)) :
    Modifier (I → E → Prop) :=
  fun N t x ↦ ∃ d, standard G < d ∧ G d N t x

/-- With the positive morpheme, a gradable adjective is intersective of type ⟨eit,eit⟩ (§4.6). -/
theorem pos_gradable [LT D] (standard : (D → Modifier (I → E → Prop)) → D)
    (P : I → E → D → Prop) :
    pos standard (gradable P) =
      Modifier.intersective fun t x ↦ ∃ d, standard (gradable P) < d ∧ P t x d := by
  funext N t x
  simp only [pos, gradable, intersective_apply₂]
  exact propext ⟨fun ⟨d, hd, h, hN⟩ ↦ ⟨⟨d, hd, h⟩, hN⟩, fun ⟨⟨d, hd, h⟩, hN⟩ ↦ ⟨d, hd, h, hN⟩⟩

end Replies

end Elbourne2026
