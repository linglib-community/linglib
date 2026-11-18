module

public import Linglib.Core.Order.UpperLower.Principal
public import Linglib.Semantics.Degree.Boundedness
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# Positive standards and Interpretive Economy

A standard is an upper set of degrees, and the positive form of a measure at it is the preimage of
the standard. Kennedy's `PositiveStandard`s are the degrees above the least, those from the greatest
and those above a contextual threshold, and Interpretive Economy uses a standard the scale itself
fixes when there is one. Reading "fixes" as [invariance under every
automorphism](##UpperSet.IsInvariant), [the invariant standards are the trivial and the endpoint
ones](##UpperSet.isInvariant_iff_of_exists_orderIso) wherever an automorphism carries any degree
between the endpoints to any other, so [a contextual standard is admitted exactly on an open
scale](##Boundedness.admits_contextual). [Only the minimum and the maximum are
complementary](##PositiveStandard.complementary_iff). A difference function measures on the ray
above a degree and so takes the minimum standard, at which [the positive form is a
comparative](##Set.preimage_projIci_comp_Ioi_bot).

## Implementation notes

Kennedy states Interpretive Economy as maximizing the contribution of conventional meaning; reading
the standards a scale contributes as those every automorphism fixes is this library's. The
preference for the maximum on a totally closed scale is Kennedy's and stays a stipulation
(`Boundedness.defaultStandard`).

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [kennedy-levin-2008]
* [klein-1980]
* [beltrama-2025]
* [morzycki-2012]
-/

@[expose] public section

/-! ### Invariant standards

A standard of a scale is an upper set of its degrees, and the positive form at it holds of what
the measure places in it, so that a stronger standard, a smaller upper set, entails a weaker one.
A standard is invariant when the order alone singles it out, every automorphism of the degrees
mapping it to itself. All degrees and none are invariant, as are the degrees above a least one
and those from a greatest one, and where any degree between the endpoints is carried to any
other by an automorphism, as on the canonical scales, these are all. -/

namespace UpperSet

section Invariant
variable {D : Type*}

/-- A standard is invariant when every order automorphism of the degrees maps it to itself. -/
def IsInvariant [Preorder D] (U : UpperSet D) : Prop := ∀ f : D ≃o D, UpperSet.map f U = U

variable [PartialOrder D] {U : UpperSet D} {m : D}

theorem isInvariant_bot : IsInvariant (⊥ : UpperSet D) := fun f ↦ map_bot (UpperSet.map f)

theorem isInvariant_top : IsInvariant (⊤ : UpperSet D) := fun f ↦ map_top (UpperSet.map f)

theorem isInvariant_Ioi_of_isBot (hm : IsBot m) : IsInvariant (UpperSet.Ioi m) := fun f ↦ by
  rw [UpperSet.map_Ioi, le_antisymm (by simpa using f.monotone (hm (f.symm m))) (hm (f m))]

theorem isInvariant_Ici_of_isTop (hm : IsTop m) : IsInvariant (UpperSet.Ici m) := fun f ↦ by
  rw [UpperSet.map_Ici, le_antisymm (hm (f m)) (by simpa using f.monotone (hm (f.symm m)))]

theorem IsInvariant.apply_mem (hU : IsInvariant U) (f : D ≃o D) {x : D} (hx : x ∈ U) :
    f x ∈ U := by
  rw [← hU f, UpperSet.mem_map]
  simpa using hx

end Invariant

section Homogeneous
variable {D : Type*} [LinearOrder D] {U : UpperSet D}

/-- Where an automorphism carries any degree strictly between the endpoints to any other, the
invariant standards are the trivial ones and the endpoint ones. -/
theorem isInvariant_iff_of_exists_orderIso (hI : ∃ x : D, ¬ IsBot x ∧ ¬ IsTop x)
    (h : ∀ x y : D, ¬ IsBot x → ¬ IsTop x → ¬ IsBot y → ¬ IsTop y → ∃ f : D ≃o D, f x = y) :
    IsInvariant U ↔
      U = ⊥ ∨ U = ⊤ ∨ (∃ m, IsBot m ∧ U = .Ioi m) ∨ ∃ m, IsTop m ∧ U = .Ici m := by
  refine ⟨fun hU ↦ ?_, ?_⟩
  · obtain ⟨x, hxb, hxt⟩ := hI
    by_cases hA : ∃ y ∈ U, ¬ IsBot y ∧ ¬ IsTop y
    · obtain ⟨y, hyU, hyb, hyt⟩ := hA
      -- with one degree between the endpoints, `U` holds every degree that is not least
      have hnb : ∀ z, ¬ IsBot z → z ∈ U := fun z hz ↦ by
        by_cases hzt : IsTop z
        · exact U.upper (hzt y) hyU
        · obtain ⟨f, rfl⟩ := h y z hyb hyt hz hzt
          exact hU.apply_mem f hyU
      by_cases hB : ∃ m : D, IsBot m
      · obtain ⟨m, hm⟩ := hB
        by_cases hmU : m ∈ U
        · exact .inl (SetLike.ext fun z ↦ by simpa using U.upper (hm z) hmU)
        · refine .inr (.inr (.inl ⟨m, hm, SetLike.ext fun z ↦ ?_⟩))
          simp only [UpperSet.mem_Ioi_iff]
          refine ⟨fun hz ↦ (hm z).lt_of_ne ?_, fun hz ↦ hnb z fun hz' ↦ hz.ne' ?_⟩
          · rintro rfl; exact hmU hz
          · exact le_antisymm (hz' m) (hm z)
      · push Not at hB
        exact .inl (SetLike.ext fun z ↦ by simpa using hnb z (hB z))
    · push Not at hA
      -- with none, `U` holds only greatest degrees, since `x` follows a least one
      have hb : ∀ z ∈ U, IsTop z := fun z hz ↦ by
        by_cases hzb : IsBot z
        · exact absurd (hA x (U.upper (hzb x) hz) hxb) hxt
        · exact hA z hz hzb
      by_cases hT : ∃ t, t ∈ U
      · obtain ⟨t, ht⟩ := hT
        refine .inr (.inr (.inr ⟨t, hb t ht, SetLike.ext fun z ↦ ?_⟩))
        simp only [UpperSet.mem_Ici_iff]
        exact ⟨fun hz ↦ hb z hz t, fun hz ↦ U.upper hz ht⟩
      · push Not at hT
        exact .inr (.inl (SetLike.ext fun z ↦ by simpa using fun h' ↦ hT z h'))
  · rintro (rfl | rfl | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    exacts [isInvariant_bot, isInvariant_top, isInvariant_Ioi_of_isBot hm,
      isInvariant_Ici_of_isTop hm]

theorem forall_isInvariant_iff_of_exists_orderIso (hI : ∃ x : D, ¬ IsBot x ∧ ¬ IsTop x)
    (h : ∀ x y : D, ¬ IsBot x → ¬ IsTop x → ¬ IsBot y → ¬ IsTop y → ∃ f : D ≃o D, f x = y) :
    (∀ U : UpperSet D, IsInvariant U → U = ⊥ ∨ U = ⊤) ↔
      (∀ m : D, ¬ IsBot m) ∧ ∀ m : D, ¬ IsTop m := by
  refine ⟨fun H ↦ ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩, fun ⟨hb, ht⟩ U hU ↦ ?_⟩
  · obtain ⟨x, hxb, -⟩ := hI
    rcases H _ (isInvariant_Ioi_of_isBot hm) with h' | h'
    · simpa using congrArg (m ∈ ·) h'
    · have hx : x ∈ UpperSet.Ioi m := (hm x).lt_of_ne fun h ↦ hxb (h ▸ hm)
      exact UpperSet.notMem_top (h' ▸ hx)
  · obtain ⟨x, -, hxt⟩ := hI
    rcases H _ (isInvariant_Ici_of_isTop hm) with h' | h'
    · exact hxt fun z ↦ (hm z).trans (by simpa using congrArg (x ∈ ·) h')
    · simpa using congrArg (m ∈ ·) h'
  · rcases (isInvariant_iff_of_exists_orderIso hI h).1 hU with h' | h' | ⟨m, hm, -⟩ | ⟨m, hm, -⟩
    exacts [.inl h', .inr h', (hb m hm).elim, (ht m hm).elim]

end Homogeneous

end UpperSet

theorem Boundedness.isInvariant_degreeShape_iff (b : Boundedness) {U : UpperSet b.DegreeShape} :
    U.IsInvariant ↔
      U = ⊥ ∨ U = ⊤ ∨ (∃ m, IsBot m ∧ U = .Ioi m) ∨ ∃ m, IsTop m ∧ U = .Ici m :=
  UpperSet.isInvariant_iff_of_exists_orderIso b.exists_not_isBot_not_isTop
    b.exists_orderIso_degreeShape

/-! ### Standards and Interpretive Economy

The positive form of a gradable predicate at a standard `U` is the preimage `μ ⁻¹' U` of the
standard under its measure, true of what the measure places in the standard. Kennedy's standards
are the degrees above the least, `Set.Ioi ⊥`, as for *wet* and *bent*; those from the greatest,
`Set.Ici ⊤`, as for *dry* and *full*; and those above a contextual threshold `θ`, `Set.Ioi θ`,
as for *tall*. When the least degree is below the greatest, the maximum standard is stronger than
the minimum (`UpperSet.Ioi_le_Ici`), and the minimum standard is the weakest nontrivial one,
covering the standard every degree meets (`UpperSet.Ici_covBy_Ioi`). Interpretive Economy
maximizes the contribution of conventional meaning, so a scale with an endpoint rules out the
contextual standard, and a totally closed scale admits both endpoint standards and prefers the
maximum. -/

/-- A positive standard is the kind of threshold the positive form compares a degree with, a
contextual norm on an open scale and an endpoint on a closed one ([kennedy-2007]), or a standard
an adjective fixes lexically outside that choice. -/
inductive PositiveStandard where
  /-- The norm of a comparison class, as for *tall*. -/
  | contextual
  /-- The minimum of the scale, as for *bent* and *wet*. -/
  | minEndpoint
  /-- The maximum of the scale, as for *full* and *dry*. -/
  | maxEndpoint
  /-- The minimum degree for pursuit ([beltrama-2025]). -/
  | necessity
  /-- A standard beyond that of the weak adjective on the same pole, as for *gigantic* and
  *pristine* ([morzycki-2012]). -/
  | extreme
  deriving DecidableEq, Repr

/-- The standards of a kind on a scale. A minimum standard is the set of degrees above a least
degree and a maximum standard the set from a greatest one; a contextual, necessity or extreme
standard is a threshold, the degrees above or from some degree, which the context or the lexicon
fixes and the scale does not. -/
def PositiveStandard.standards (s : PositiveStandard) (D : Type*) [Preorder D] :
    Set (UpperSet D) :=
  match s with
  | .minEndpoint => {U | ∃ m, IsBot m ∧ U = .Ioi m}
  | .maxEndpoint => {U | ∃ m, IsTop m ∧ U = .Ici m}
  | .contextual | .necessity | .extreme => {U | ∃ θ, U = .Ioi θ ∨ U = .Ici θ}

namespace PositiveStandard

/-- On a scale with a least degree the minimum standard is the degrees above it. -/
theorem standards_minEndpoint {D : Type*} [PartialOrder D] [OrderBot D] :
    minEndpoint.standards D = {UpperSet.Ioi ⊥} := by
  ext U
  simp [standards, isBot_iff_eq_bot]

/-- On a scale with a greatest degree the maximum standard is that degree alone. -/
theorem standards_maxEndpoint {D : Type*} [PartialOrder D] [OrderTop D] :
    maxEndpoint.standards D = {UpperSet.Ici ⊤} := by
  ext U
  simp [standards, isTop_iff_eq_top]

/-- A kind of standard requires a comparison class when the scale does not fix its standards, an
automorphism of some scale moving one of them. [kennedy-2007] argues against a comparison-class
argument of the positive form, as in [klein-1980], and states the positive form with a
standard-fixing function, `⟦pos⟧ = λg.λx. g(x) ⪰ s(g)` ((27)), which needs contextual information
about a domain to fix a threshold: a contextual or necessity standard, or an extreme one beyond
the degrees a context makes salient ([morzycki-2012]). -/
def RequiresComparisonClass (s : PositiveStandard) : Prop :=
  ∃ (D : Type) (_ : LinearOrder D), ∃ U ∈ s.standards D, ¬ U.IsInvariant

/-- The scale fixes exactly the endpoint standards. -/
theorem requiresComparisonClass_iff {s : PositiveStandard} :
    s.RequiresComparisonClass ↔ s ≠ .minEndpoint ∧ s ≠ .maxEndpoint := by
  refine ⟨fun ⟨D, _, U, hU, hn⟩ ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro rfl
    obtain ⟨m, hm, rfl⟩ := hU
    exact hn (UpperSet.isInvariant_Ioi_of_isBot hm)
  · rintro rfl
    obtain ⟨m, hm, rfl⟩ := hU
    exact hn (UpperSet.isInvariant_Ici_of_isTop hm)
  · have h0 : ¬ (UpperSet.Ioi (0 : ℤ)).IsInvariant := fun h ↦ by
      have := h (OrderIso.addRight 1)
      rw [UpperSet.map_Ioi] at this
      simpa using (UpperSet.Ioi_strictMono ℤ).injective this
    cases s
    case minEndpoint => exact absurd rfl h₁
    case maxEndpoint => exact absurd rfl h₂
    all_goals exact ⟨ℤ, inferInstance, UpperSet.Ioi 0, ⟨0, .inl rfl⟩, h0⟩

instance : DecidablePred RequiresComparisonClass :=
  fun _ ↦ decidable_of_iff _ requiresComparisonClass_iff.symm

/-- Two kinds of standard are complementary when on every scale a standard of the one and a
standard of the other on the reversed scale, where the antonym measures, partition the degrees,
so that the poles taking them are contradictory, denying one asserting the other
([kennedy-2007] (47)). -/
def Complementary (s t : PositiveStandard) : Prop :=
  ∀ (D : Type) [LinearOrder D], ∀ U ∈ s.standards D, ∀ V ∈ t.standards Dᵒᵈ,
    IsCompl (U : Set D) (OrderDual.toDual ⁻¹' V)

/-- Only the minimum and the maximum standards are complementary: any other pair leaves a gap or
an overlap on some scale. -/
theorem complementary_iff {s t : PositiveStandard} :
    s.Complementary t ↔
      s = .minEndpoint ∧ t = .maxEndpoint ∨ s = .maxEndpoint ∧ t = .minEndpoint := by
  constructor
  · intro h
    -- a standard of each kind on a closed scale and on its reversal, with three degrees as tests
    let rep : PositiveStandard → UpperSet (WithTop (WithBot ℤ))
      | .minEndpoint => .Ioi ⊥
      | .maxEndpoint => .Ici ⊤
      | _ => .Ioi ((0 : ℤ) : WithBot ℤ)
    let drep : PositiveStandard → UpperSet (WithTop (WithBot ℤ))ᵒᵈ
      | .minEndpoint => .Ioi ⊥
      | .maxEndpoint => .Ici ⊤
      | _ => .Ioi (OrderDual.toDual ((0 : ℤ) : WithBot ℤ))
    have hrep (s : PositiveStandard) : rep s ∈ s.standards _ := by
      cases s
      exacts [⟨_, .inl rfl⟩, ⟨⊥, isBot_bot, rfl⟩, ⟨⊤, isTop_top, rfl⟩, ⟨_, .inl rfl⟩,
        ⟨_, .inl rfl⟩]
    have hdrep (t : PositiveStandard) : drep t ∈ t.standards _ := by
      cases t
      exacts [⟨_, .inl rfl⟩, ⟨⊥, isBot_bot, rfl⟩, ⟨⊤, isTop_top, rfl⟩, ⟨_, .inl rfl⟩,
        ⟨_, .inl rfl⟩]
    have hx := fun x ↦ Set.ext_iff.1 (h _ _ (hrep s) _ (hdrep t)).compl_eq x
    have h0 := hx ((0 : ℤ) : WithBot ℤ)
    have h1 := hx ((1 : ℤ) : WithBot ℤ)
    have h2 := hx ((-1 : ℤ) : WithBot ℤ)
    cases s <;> cases t <;>
      simp only [rep, drep, UpperSet.coe_Ioi, UpperSet.coe_Ici, Set.mem_Ioi, Set.mem_Ici,
        Set.mem_compl_iff, Set.mem_preimage] at h0 h1 h2 <;>
      first | (exfalso; revert h0 h1 h2; decide) | simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) D _ U ⟨m, hm, rfl⟩ V ⟨m', hm', rfl⟩
    · have : OrderDual.ofDual m' = m := le_antisymm (OrderDual.toDual_le.1 (hm' _)) (hm _)
      have hV : OrderDual.toDual ⁻¹' (UpperSet.Ici m' : Set _) = Set.Iic m := by
        ext x; simp [← this, OrderDual.le_toDual]
      rw [hV, UpperSet.coe_Ioi, ← Set.compl_Ioi]
      exact isCompl_compl
    · have : OrderDual.ofDual m' = m := le_antisymm (hm _) (OrderDual.le_toDual.1 (hm' _))
      have hV : OrderDual.toDual ⁻¹' (UpperSet.Ioi m' : Set _) = Set.Iio m := by
        ext x; simp [← this, OrderDual.lt_toDual]
      rw [hV, UpperSet.coe_Ici, ← Set.compl_Ici]
      exact isCompl_compl

instance : DecidableRel Complementary := fun _ _ ↦ decidable_of_iff _ complementary_iff.symm

end PositiveStandard

/-! ### Difference functions

The difference function of a measure `μ` at a degree `d` is `Set.projIci d ∘ μ`, which measures on
the ray above `d` and sends every degree at or below `d` to `d`, the derived zero. The ray has a
least degree (`Boundedness.ofOrder_Ici`), so Interpretive Economy admits the minimum standard for
a difference function, giving the truth conditions of a comparative with standard `d`, and the
maximum standard exactly when the scale of `μ` has one. -/

section Difference
variable {α D : Type*} [LinearOrder D] {μ : α → D} {d : D}

/-- The positive form of a difference function at the minimum standard is the comparative with
standard `d` ([kennedy-mcnally-2005], [kennedy-levin-2008] (24)). -/
theorem Set.preimage_projIci_comp_Ioi_bot : (Set.projIci d ∘ μ) ⁻¹' Set.Ioi ⊥ = μ ⁻¹' Set.Ioi d :=
  Set.ext fun _ ↦ show ⊥ < Set.projIci d _ ↔ d < _ from
    bot_lt_iff_ne_bot.trans (Set.projIci_eq_self.not.trans not_le)

/-- Unless `d` is the greatest degree, the positive form of a difference function at the maximum
standard is that of `μ` itself ([kennedy-levin-2008] fn. 16). -/
theorem Set.preimage_projIci_comp_Ici_top [OrderTop D] (hd : d ≠ ⊤) :
    (Set.projIci d ∘ μ) ⁻¹' Set.Ici ⊤ = μ ⁻¹' Set.Ici ⊤ := by
  ext x
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_Ici, top_le_iff, Subtype.ext_iff,
    Set.coe_projIci, Set.Ici.coe_top, max_eq_top, hd, false_or]

end Difference

namespace Boundedness

/-- Interpretive Economy computes truth conditions from conventional meaning where it can,
allowing a contextual standard only where conventional meaning is insufficient ([kennedy-2007]
(66)). The standards a scale itself fixes are those every automorphism of its degrees fixes, and
the endpoint standards are among them (`UpperSet.isInvariant_Ioi_of_isBot`), so a scale admits an
endpoint standard where it has a standard of that kind, and the contextual standard only where it
fixes no standard but the trivial ones. The lexical necessity and extreme standards it never
admits. On the canonical scales the endpoint standards are the only nontrivial invariant ones
(`isInvariant_degreeShape_iff`). -/
def Admits (b : Boundedness) : PositiveStandard → Prop
  | .contextual  => ∀ U : UpperSet b.DegreeShape, U.IsInvariant → U = ⊥ ∨ U = ⊤
  | .minEndpoint => (PositiveStandard.minEndpoint.standards b.DegreeShape).Nonempty
  | .maxEndpoint => (PositiveStandard.maxEndpoint.standards b.DegreeShape).Nonempty
  | .necessity   => False
  | .extreme     => False

/-- The contextual standard is admitted exactly on a totally open scale, since a scale with an
endpoint fixes the endpoint standard ([kennedy-2007] (66)). -/
@[simp] theorem admits_contextual {b : Boundedness} : b.Admits .contextual ↔ b = .open_ := by
  rw [Admits, UpperSet.forall_isInvariant_iff_of_exists_orderIso b.exists_not_isBot_not_isTop
    b.exists_orderIso_degreeShape]
  simp only [← not_exists, exists_isBot_degreeShape, exists_isTop_degreeShape]
  cases b <;> decide

@[simp] theorem admits_minEndpoint {b : Boundedness} : b.Admits .minEndpoint ↔ b.HasMin := by
  rw [← exists_isBot_degreeShape]
  exact ⟨fun ⟨_, m, hm, _⟩ ↦ ⟨m, hm⟩, fun ⟨m, hm⟩ ↦ ⟨_, m, hm, rfl⟩⟩

@[simp] theorem admits_maxEndpoint {b : Boundedness} : b.Admits .maxEndpoint ↔ b.HasMax := by
  rw [← exists_isTop_degreeShape]
  exact ⟨fun ⟨_, m, hm, _⟩ ↦ ⟨m, hm⟩, fun ⟨m, hm⟩ ↦ ⟨_, m, hm, rfl⟩⟩

@[simp] theorem not_admits_necessity (b : Boundedness) : ¬ b.Admits .necessity := id

@[simp] theorem not_admits_extreme (b : Boundedness) : ¬ b.Admits .extreme := id

instance (b : Boundedness) : (s : PositiveStandard) → Decidable (b.Admits s)
  | .contextual  => decidable_of_iff _ admits_contextual.symm
  | .minEndpoint => decidable_of_iff _ admits_minEndpoint.symm
  | .maxEndpoint => decidable_of_iff _ admits_maxEndpoint.symm
  | .necessity   => isFalse id
  | .extreme     => isFalse id

theorem not_admits_contextual_of_ne_open {b : Boundedness} (h : b ≠ .open_) :
    ¬ b.Admits .contextual :=
  mt admits_contextual.1 h

/-- The default standard of a scale is the one Interpretive Economy forces where it admits only
one, and the maximum on a totally closed scale, since a maximum standard entails a minimum one. -/
def defaultStandard : Boundedness → PositiveStandard
  | .open_        => .contextual
  | .lowerClosed => .minEndpoint
  | .upperClosed => .maxEndpoint
  | .closed       => .maxEndpoint

theorem admits_defaultStandard (b : Boundedness) : b.Admits b.defaultStandard := by
  cases b <;> decide

/-- The default standard is the maximum exactly when the scale has one. -/
theorem defaultStandard_eq_maxEndpoint_iff {b : Boundedness} :
    b.defaultStandard = .maxEndpoint ↔ b.HasMax := by
  cases b <;> decide

/-- On degrees with a greatest one, the standard Interpretive Economy selects is the maximum
standard `UpperSet.Ici ⊤`, whether or not there is a least degree: the tag of the order and the
truth conditions of the positive form agree. -/
theorem standards_defaultStandard_ofOrder {D : Type*} [PartialOrder D] [OrderTop D] :
    (ofOrder D).defaultStandard.standards D = {UpperSet.Ici ⊤} := by
  rw [defaultStandard_eq_maxEndpoint_iff.2 hasMax_ofOrder_of_orderTop,
    PositiveStandard.standards_maxEndpoint]

/-- The default standards of a scale and its dual are complementary exactly when the scale has one
endpoint. An open scale gives both poles a contextual standard and a totally closed one gives both
the maximum, as for *full* and *empty*. -/
theorem complementary_defaultStandard_dual_iff {b : Boundedness} :
    b.defaultStandard.Complementary b.dual.defaultStandard ↔
      b = .lowerClosed ∨ b = .upperClosed := by
  cases b <;> decide

/-- A scale is relative when its default standard needs a comparison class, which is to say when
it is open, as for *tall*, *expensive* and *big*. -/
def IsRelative (b : Boundedness) : Prop := b.defaultStandard.RequiresComparisonClass

instance : DecidablePred IsRelative :=
  fun b ↦ inferInstanceAs (Decidable b.defaultStandard.RequiresComparisonClass)

/-- A scale with a least degree adjoined admits the minimum standard, and the maximum iff the
original scale has one ([kennedy-levin-2008] (23), (25)). -/
theorem admits_withMin_iff {b : Boundedness} {s : PositiveStandard} :
    b.withMin.Admits s ↔ s = .minEndpoint ∨ s = .maxEndpoint ∧ b.HasMax := by
  cases b <;> cases s <;> simp [withMin, HasMin, HasMax]

theorem defaultStandard_withMin (b : Boundedness) :
    b.withMin.defaultStandard = if b.HasMax then .maxEndpoint else .minEndpoint := by
  cases b <;> rfl

end Boundedness
