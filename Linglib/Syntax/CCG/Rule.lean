module

public import Linglib.Syntax.CCG.Cat

/-!
# CCG rules

Every combinatory rule is an instance of one schema. Forward composition `X/Y Yβ ⇒ Xβ` combines
a primary category `X/Y` with a secondary category on its right that would give a `Y` after
taking the arguments `β`, and gives an `X` that still takes those arguments. Backward
composition `Yβ X\Y ⇒ Xβ` is its mirror image. When `β` is empty the rule is application. A
rule is *harmonic* when the arguments in `β` look the same way as the primary slash, and
*crossing* otherwise.

A *rule system* says which instances of the schema a grammar may use, and the formalisms of the
literature differ in this choice. In the multimodal system the modalities of the slashes decide:
a slash may license harmonic composition, crossing composition, both or neither. In the
classical formalism VW-CCG a grammar lists finitely many rules, each of which may restrict the
target of its primary input and its secondary input, and [restricting every rule to one target
is such a list](##CCG.RuleSystem.targetRestricted_eq_ofRestrictedRules).

## Implementation notes

`RuleSystem.multimodal` follows the rules of O-CCG, the multimodal formalism whose composition
rules [kuhlmann-koller-satta-2015] fix after OpenCCG, without OpenCCG's directional slash types
and inertness: a rule fires only when every slash in its scope, the primary slash and the slashes
of the secondary's composed arguments, has a compatible modality, and the degree bound is a
parameter of the grammar. The substitution rules and the morphemic slash are not modelled.

## References

* [steedman-2019]
* [baldridge-2002]
* [kuhlmann-koller-satta-2015]
* [weir-joshi-1988]
* [vijay-shanker-weir-1994]
-/

@[expose] public section

namespace CCG

variable {α : Type*}

/-! ### Rule systems -/

/-- A rule system says which instances of the composition schema fire. `R x a β` permits the
primary `x a`, the category `x` with outermost argument `a`, to combine with a secondary
`a.cat β` into `x β`, by a forward rule when `a` looks right and a backward rule when it looks
left, and by application when `β` is empty. -/
abbrev RuleSystem (α : Type*) := Cat α → Cat.Arg α → List (Cat.Arg α) → Prop

/-- The multimodal rule system of [baldridge-2002] and [steedman-2019], with the composition
rules of [kuhlmann-koller-satta-2015]'s O-CCG, admits composition of degree at most `degree`
into a secondary whose arguments all look one way. Every slash in the scope of the rule, the
primary slash and the slash of each composed argument, must license harmonic composition (`⋄`)
when the composed arguments look the primary slash's way and crossing composition (`×`) when
they look the other way, and application fires at every modality. -/
def RuleSystem.multimodal (degree : ℕ) : RuleSystem α := fun _ a β ↦
  β.length ≤ degree ∧ β.Pairwise (·.side = ·.side) ∧
    ∀ b ∈ β, a.modality ≤ (if b.side = a.side then .diamond else .cross) ∧
      b.modality ≤ if b.side = a.side then .diamond else .cross

instance (degree : ℕ) (x : Cat α) (a : Cat.Arg α) (β : List (Cat.Arg α)) :
    Decidable (RuleSystem.multimodal degree x a β) :=
  inferInstanceAs (Decidable (β.length ≤ degree ∧ β.Pairwise (·.side = ·.side) ∧
    ∀ b ∈ β, a.modality ≤ (if b.side = a.side then .diamond else .cross) ∧
      b.modality ≤ if b.side = a.side then .diamond else .cross))

@[simp] theorem RuleSystem.multimodal_nil {degree : ℕ} {x : Cat α} {a : Cat.Arg α} :
    multimodal degree x a [] := by
  simp [multimodal]

@[simp] theorem RuleSystem.multimodal_singleton {degree : ℕ} {x : Cat α} {a b : Cat.Arg α} :
    multimodal degree x a [b] ↔ 1 ≤ degree ∧
      a.modality ≤ (if b.side = a.side then .diamond else .cross) ∧
      b.modality ≤ if b.side = a.side then .diamond else .cross := by
  simp [multimodal]

/-- A slash of modality `⋆` is never composed into: a secondary whose composed argument has it
fails the multimodal rule system at every degree and every primary slash. -/
theorem RuleSystem.not_multimodal_of_star_mem {degree : ℕ} {x : Cat α} {a : Cat.Arg α}
    {β : List (Cat.Arg α)} {b : Cat.Arg α} (hb : b ∈ β) (hstar : b.modality = .star) :
    ¬ multimodal degree x a β := fun h ↦ by
  have := (h.2.2 b hb).2
  rw [hstar] at this
  split_ifs at this <;> exact absurd this (by decide)

/-! ### The restricted rules of VW-CCG -/

/-- A restricted rule of VW-CCG ([vijay-shanker-weir-1994], [kuhlmann-koller-satta-2015]):
forward or backward composition of one degree, application at degree `0`, whose instances may be
restricted in the target of the primary input and in the secondary input, in part or in its
entirety. -/
structure RestrictedRule (α : Type*) where
  /-- The side the primary slash looks to, `right` for a forward and `left` for a backward
  rule. -/
  side : Edge
  /-- The degree, the number of arguments the rule composes. -/
  degree : ℕ
  /-- The targets the primary input may have. -/
  primaryTarget : Set α
  /-- The secondary inputs the rule admits. -/
  secondary : Set (Cat α)

/-- The rule system of a VW-CCG whose restricted rules are `rs`: an instance of the composition
schema fires when it is a valid instance of one of them. -/
def RuleSystem.ofRestrictedRules (rs : List (RestrictedRule α)) : RuleSystem α := fun x a β ↦
  ∃ r ∈ rs, r.side = a.side ∧ r.degree = β.length ∧ x.target ∈ r.primaryTarget ∧
    a.cat.pushArgs β ∈ r.secondary

/-- The uniform target restriction admits composition up to a degree bound into a primary
input whose target is the start atom, the restriction of every rule of
[kuhlmann-koller-satta-2015]'s grammar for `aⁿbⁿcⁿ`. -/
def RuleSystem.targetRestricted (start : α) (degree : ℕ) : RuleSystem α :=
  fun x _ β ↦ β.length ≤ degree ∧ x.target = start

/-- The uniform target restriction is the VW-CCG rule system of forward and backward composition
of each degree up to the bound, restricted to primary inputs whose target is the start atom and
unrestricted in the secondary input. -/
theorem RuleSystem.targetRestricted_eq_ofRestrictedRules (start : α) (degree : ℕ) :
    targetRestricted start degree = ofRestrictedRules ((List.range (degree + 1)).flatMap
      fun n ↦ [⟨.right, n, {start}, Set.univ⟩, ⟨.left, n, {start}, Set.univ⟩]) := by
  funext x a β
  refine propext ⟨fun ⟨hβ, hx⟩ ↦ ?_, ?_⟩
  · refine ⟨⟨a.side, β.length, {start}, Set.univ⟩, List.mem_flatMap.2 ⟨β.length,
      List.mem_range.2 (by omega), ?_⟩, rfl, rfl, hx, trivial⟩
    cases a.side <;> simp
  · rintro ⟨r, hr, -, hd, hx, -⟩
    obtain ⟨n, hn, hr⟩ := List.mem_flatMap.1 hr
    rw [List.mem_range] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by have : n = β.length := hd; omega, hx⟩

/-! ### Rules -/

/-- A `Rule R l r c` is an instance of the composition schema that the rule system `R` permits,
combining a left constituent of category `l` with a right constituent of category `r` to give
`c`. Its degree is the length of its argument sequence `β`. -/
inductive Rule (R : RuleSystem α) : Cat α → Cat α → Cat α → Type _ where
  /-- Forward composition `X/Y Yβ ⇒ Xβ` (`>Bⁿ`), forward application `>` when `β = []`. -/
  | forward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) (h : R x ⟨.right, m, y⟩ β) :
      Rule R (.slash .right x m y) (y.pushArgs β) (x.pushArgs β)
  /-- Backward composition `Yβ X\Y ⇒ Xβ` (`<Bⁿ`), backward application `<` when `β = []`. -/
  | backward {x y : Cat α} {m : Modality} (β : List (Cat.Arg α)) (h : R x ⟨.left, m, y⟩ β) :
      Rule R (y.pushArgs β) (.slash .left x m y) (x.pushArgs β)

/-- The rule is a composition (of any degree or direction) rather than an application. -/
def Rule.IsComp {R : RuleSystem α} {l r c : Cat α} : Rule R l r c → Prop
  | .forward β _ | .backward β _ => β ≠ []

instance {R : RuleSystem α} {l r c : Cat α} : ∀ ru : Rule R l r c, Decidable ru.IsComp
  | .forward β _ | .backward β _ => inferInstanceAs (Decidable (β ≠ []))

/-- The rule is harmonic: the arguments it composes look the way the primary slash does.
Application is harmonic, and a composition that is not is crossing. -/
def Rule.IsHarmonic {R : RuleSystem α} {l r c : Cat α} : Rule R l r c → Prop
  | .forward β _ => ∀ b ∈ β, b.side = .right
  | .backward β _ => ∀ b ∈ β, b.side = .left

instance {R : RuleSystem α} {l r c : Cat α} : ∀ ru : Rule R l r c, Decidable ru.IsHarmonic
  | .forward β _ => inferInstanceAs (Decidable (∀ b ∈ β, b.side = .right))
  | .backward β _ => inferInstanceAs (Decidable (∀ b ∈ β, b.side = .left))

end CCG
