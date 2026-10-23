module

public import Linglib.Semantics.Possession.Relationalizer
public import Linglib.Semantics.Quantification.Basic

/-!
# Possessive quantifiers

[peters-westerstahl-2006] (Ch. 7) analyse a possessive determiner such as *most students'* as a
generalized quantifier assembled from a quantifier `Q₁` over possessors with its restriction `C`
(*most*, *students*), a quantifier `Q₂` over the possessed things, and the possession relation
`R`. `Q₂` is explicit in *several of John's CDs* and implicit in *John's bikes*, where it is
universal, definite or existential depending on the reading; which of these a bare possessive
carries is the question of whether possessives are definite, and nothing here fixes it.

*Most students' tennis rackets are cheap* is `Poss most student every own racket cheap`: most of
the students who own a racket own only cheap ones. The restriction to students who own a racket
is narrowing (`dom`); without it, students with no racket would count against the sentence. The
rackets a student `x` owns are the noun relationalized at `x`, `π racket own x`. `PossNP` is the
variant for a possessor that is a noun phrase taken whole, such as *John*.

## Main definitions

* `Possession.Poss`: the possessive quantifier for a possessor of the form determiner + noun.
* `Possession.PossNP`: the possessive quantifier for a possessor noun phrase taken whole.

## Main statements

* `Quantifier.GQ.Conservative.poss`: a possessive is conservative whenever `Q₂` is.
* `Quantifier.GQ.ScopeMonotone.poss` and its three variants: a possessive is upward monotone in
  its scope when `Q₁` and `Q₂` are monotone in the same direction, downward when they differ.
* `Possession.poss_eq_possNP_restrict`: narrowing makes no difference when `Q₁` is symmetric.
* `Possession.possNP_individual_the`: on the definite reading, *John's A is B* says that the
  unique `A` John possesses is `B`.
* `Possession.poss_not_quantityInvariant`: possessives are not logical quantifiers, since
  permuting individuals can change their truth value.

## References

* [peters-westerstahl-2006]
* [peters-westerstahl-2013]
* [barker-1995]
* [coppock-beaver-2015]
-/

@[expose] public section

namespace Possession

open Quantifier Quantifier.GQ Quantifier.NP

variable {α : Type*}

/-! ### Possessive operators -/

/-- `Poss Q₁ C Q₂ R A B` is *[Q₁ C]'s A are B*: `Q₁` of the `C`s that possess an `A` are
individuals `Q₂` of whose `A`s are `B`. *Most students' tennis rackets are cheap* (their
(7.31)) says that most of the students who own a racket are students all of whose rackets are
cheap. This is their (7.30), p. 255, which assumes conservative and extensional `Q₁` and `Q₂`;
the general definition (7.28) differs only in bookkeeping about the universe. -/
def Poss (Q₁ : GQ α) (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B ↦ Q₁ (fun x ↦ C x ∧ dom A R x) (fun x ↦ Q₂ (π A R x) B)

/-- `PossNP Q Q₂ R A B` is *[Q]'s A are B* for a possessor noun phrase `Q` taken whole, such as
*John*: `Q` holds of the set of individuals that possess an `A` and `Q₂` of whose `A`s are
`B`. Since possessing an `A` is part of what `Q` is said of, *John's dogs bark* requires
John to own a dog. This is their (7.45), p. 260, under the assumptions stated there. -/
def PossNP (Q : NP α) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B ↦ Q (fun a ↦ dom A R a ∧ Q₂ (π A R a) B)

/-! ### Conservativity -/

/-- If `Q₂` is conservative, so is every possessive built with it, whatever `Q₁` is: whether
*most students' rackets are cheap* is true depends only on which rackets are cheap. Their (7.29),
p. 255, states this with `Q₁` conservative too. -/
theorem _root_.Quantifier.GQ.Conservative.poss {Q₂ : GQ α} (h₂ : Conservative Q₂) (Q₁ : GQ α)
    (C : α → Prop) (R : α → α → Prop) : Conservative (Poss Q₁ C Q₂ R) := fun _ _ ↦
  iff_of_eq (congrArg (Q₁ _) (funext fun _ ↦ propext
    (Conservative.congr_scope h₂ fun _ hy ↦ (and_iff_right hy.1).symm)))

/-- If `Q₂` is conservative, so is the possessive of a whole noun phrase built with it (their
remark after (7.44)). -/
theorem _root_.Quantifier.GQ.Conservative.possNP {Q₂ : GQ α} (h₂ : Conservative Q₂) (Q : NP α)
    (R : α → α → Prop) : Conservative (PossNP Q Q₂ R) := fun _ _ ↦
  iff_of_eq (congrArg Q (funext fun _ ↦ propext (and_congr_right fun _ ↦
    Conservative.congr_scope h₂ fun _ hy ↦ (and_iff_right hy.1).symm)))

/-! ### Scope monotonicity (Proposition 5, §7.13, p. 288)

The scope `B` feeds only `Q₂`, and the possessors for whom `Q₂` holds form the scope of `Q₁`, so
the two directions combine as they do for composed functions. Same direction gives an upward
monotone possessive: *Mary's bikes are expensive* entails *Mary's bikes are expensive or new*
(7.89).
Opposite directions give a downward one: *No professors' cars are rusty* entails *No professors'
cars are gray and rusty* (7.90). -/

section Monotone

variable {Q₁ Q₂ : GQ α} (C : α → Prop) (R : α → α → Prop)

/-- `Q₁` and `Q₂` both upward monotone: the possessive is upward monotone. -/
theorem _root_.Quantifier.GQ.ScopeMonotone.poss (h₁ : ScopeMonotone Q₁)
    (h₂ : ScopeMonotone Q₂) : ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

/-- `Q₁` upward and `Q₂` downward monotone: the possessive is downward monotone. -/
theorem _root_.Quantifier.GQ.ScopeMonotone.poss_scopeAntitone (h₁ : ScopeMonotone Q₁)
    (h₂ : ScopeAntitone Q₂) : ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

/-- `Q₁` and `Q₂` both downward monotone: the possessive is upward monotone. -/
theorem _root_.Quantifier.GQ.ScopeAntitone.poss (h₁ : ScopeAntitone Q₁)
    (h₂ : ScopeAntitone Q₂) : ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

/-- `Q₁` downward and `Q₂` upward monotone: the possessive is downward monotone. -/
theorem _root_.Quantifier.GQ.ScopeAntitone.poss_scopeMonotone (h₁ : ScopeAntitone Q₁)
    (h₂ : ScopeMonotone Q₂) : ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

end Monotone

/-! ### When narrowing is idle (Fact 1, §7.8.1, p. 260) -/

/-- When `Q₁` is symmetric and conservative, as *some*, *no* and *at least two* are, narrowing
to the possessors makes no difference, and the possessive of *[Q₁ C]* equals the possessive of
the noun phrase *Q₁ C* taken whole. Narrowing matters for quantifiers like *most*. -/
theorem poss_eq_possNP_restrict {Q₁ : GQ α} (hSym : Std.Symm Q₁) (hCons : Conservative Q₁)
    (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) :
    Poss Q₁ C Q₂ R = PossNP (Q₁ C) Q₂ R :=
  funext fun _ ↦ funext fun _ ↦
    propext ((conserv_symm_iff_int Q₁ hCons).mp hSym _ _ _ _ fun _ ↦ and_assoc)

/-! ### Individual possessors -/

/-- For an individual possessor `a`, *a's A are B* says that `a` possesses an `A` and that `Q₂`
of the `A`s `a` possesses are `B`. With `Q₂` universal this is the truth condition of
*John's A are B* that they recall on p. 256: John possesses some `A`, and all of them are `B`. -/
theorem possNP_individual_iff {Q₂ : GQ α} {R : α → α → Prop} {a : α} {A B : α → Prop} :
    PossNP (individual a) Q₂ R A B ↔ dom A R a ∧ Q₂ (π A R a) B :=
  Iff.rfl

/-- Whatever `Q₂` is, *John's A are B* entails that John possesses an `A`: *Mercury's rings
are icy* is false, not trivially true, if Mercury has no rings. -/
theorem possNP_individual_existential_import {Q₂ : GQ α} {R : α → α → Prop}
    {a : α} {A B : α → Prop} (h : PossNP (individual a) Q₂ R A B) : dom A R a :=
  h.1

/-- On the definite reading, with Russell's *the* as `Q₂`, *John's A is B* says that John
possesses exactly one `A` and that it is `B`: *the* applied to the `A`s John possesses. -/
theorem possNP_individual_the {R : α → α → Prop} {a : α} {A B : α → Prop} :
    PossNP (individual a) the R A B ↔ the (π A R a) B :=
  ⟨And.right, fun h ↦ ⟨h.elim fun x hx ↦ ⟨x, (hx.1 x).2 rfl⟩, h⟩⟩

/-! ### Possessives are not logical -/

/-- A logical quantifier keeps its truth value when the individuals are permuted. A possessive
does not, because the possession relation stays put while the individuals move. Take two
individuals, `true` and `false`, where `true` possesses itself and nothing else is possessed.
*Some individual's `true`s are individuals* holds. Swap `true` and `false` in the noun and the
scope but not in the possession relation, and the result, *some individual's `false`s are
individuals*, fails, since nobody possesses `false`. They note that possessives are "almost
never" invariant in this sense (p. 256). -/
theorem poss_not_quantityInvariant :
    ¬ QuantityInvariant
        (Poss (GQ.some (α := Bool)) (fun _ ↦ True) GQ.some
          (fun x y ↦ x = true ∧ y = true)) := by
  intro h
  have hiff := h (fun x ↦ x = true) (fun _ ↦ True) (fun x ↦ x = false)
    (fun _ ↦ True) Bool.not
    ((Function.Involutive.bijective fun b ↦ Bool.not_not b))
    (fun x ↦ by cases x <;> simp) (fun _ ↦ Iff.rfl)
  have hpos : Poss (GQ.some (α := Bool)) (fun _ ↦ True) GQ.some
      (fun x y ↦ x = true ∧ y = true) (fun x ↦ x = true) (fun _ ↦ True) :=
    ⟨true, ⟨trivial, true, rfl, rfl, rfl⟩, true, ⟨rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨x, ⟨-, b, hb, -, hb'⟩, -⟩ := hiff.mp hpos
  exact absurd (hb' ▸ hb) (by simp)

end Possession
