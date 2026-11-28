module

public import Linglib.Core.Order.UpperLower.Principal
public import Linglib.Semantics.Degree.Boundedness
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# Positive standards and Interpretive Economy

A standard on a scale `D` is an upper set of its degrees, and the positive form of a measure
`μ : α → D` at a standard `U` is the preimage `μ ⁻¹' U`. A minimum standard is the set
`UpperSet.Ioi m` of degrees above a least degree `m`, a maximum standard the set `UpperSet.Ici m`
of degrees from a greatest one, and a threshold standard `UpperSet.Ioi θ` or `UpperSet.Ici θ` for a
degree `θ` that the context or the lexicon supplies.

A scale fixes a standard when every order automorphism of its degrees maps the standard to itself.
On a linear order whose automorphisms carry any degree strictly between the endpoints to any
other, the standards fixed are all degrees, none, and the two endpoint standards. Interpretive
Economy admits a kind of standard on a scale when the scale has a standard of that kind and, if
the scale fixes a standard other than all degrees and none, fixes every standard of that kind.
Thresholds are thus admitted exactly on open scales and an endpoint standard exactly where the
endpoint exists.

## Main definitions

* `UpperSet.IsInvariant`: a standard every order automorphism maps to itself.
* `PositiveStandard`: the kinds of standard, with `PositiveStandard.standards` the standards of
  a kind on a scale.
* `PositiveStandard.RequiresComparisonClass`: some scale does not fix some standard of the kind.
* `PositiveStandard.Complementary`: on every scale a standard of one kind and a standard of the
  other on the reversed scale partition the degrees.
* `Boundedness.Admits`: Interpretive Economy, on the canonical scale of a boundedness.
* `Boundedness.defaultStandard`: the kind of standard a scale takes by default.

## Main results

* `UpperSet.isInvariant_iff_of_exists_orderIso`: the invariant standards of a linear order whose
  automorphisms are transitive between the endpoints.
* `Boundedness.admits_contextual`: a contextual standard is admitted exactly on an open scale.
* `Boundedness.le_of_mem_standards_defaultStandard`: off the open scale, the default standard is
  the strongest admitted one.
* `PositiveStandard.complementary_iff`: only the minimum and the maximum are complementary.

## Implementation notes

Kennedy states Interpretive Economy as a directive to maximize the contribution of conventional
meaning. Here the standards that the conventional meaning of a scale contributes are those every
automorphism fixes, the usual rendering of what a structure alone determines. `Boundedness.Admits`
is one condition for every kind, so which kinds a scale admits is proved and the lexical kinds get
no clause of their own: a necessity or an extreme standard is a threshold, admitted where a
contextual one is. The condition is evaluated on `Boundedness.DegreeShape`, the integers with
endpoints adjoined, since on an order with few automorphisms every standard is invariant.

On a totally closed scale both endpoint standards are admitted; `Boundedness.defaultStandard`
takes the maximum, the stronger of the two.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [kennedy-levin-2008]
* [lassiter-2017]
* [beltrama-2025]
* [morzycki-2012]
-/

@[expose] public section

/-! ### Invariant standards -/

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

theorem not_isInvariant_Ici {x : D} (f : D ≃o D) (h : f x ≠ x) : ¬ IsInvariant (UpperSet.Ici x) :=
  fun hU ↦ h (UpperSet.Ici_injective ((UpperSet.map_Ici f x).symm.trans (hU f)))

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

/-- Under the same hypothesis, some standard other than all degrees and none is invariant exactly
when the order has an endpoint. -/
theorem exists_isInvariant_ne_iff_of_exists_orderIso (hI : ∃ x : D, ¬ IsBot x ∧ ¬ IsTop x)
    (h : ∀ x y : D, ¬ IsBot x → ¬ IsTop x → ¬ IsBot y → ¬ IsTop y → ∃ f : D ≃o D, f x = y) :
    (∃ U : UpperSet D, U.IsInvariant ∧ U ≠ ⊥ ∧ U ≠ ⊤) ↔ (∃ m : D, IsBot m) ∨ ∃ m : D, IsTop m := by
  obtain ⟨x, hxb, hxt⟩ := hI
  refine ⟨fun ⟨U, hU, hb, ht⟩ ↦ ?_, ?_⟩
  · rcases (isInvariant_iff_of_exists_orderIso ⟨x, hxb, hxt⟩ h).1 hU with
      h' | h' | ⟨m, hm, -⟩ | ⟨m, hm, -⟩
    exacts [(hb h').elim, (ht h').elim, .inl ⟨m, hm⟩, .inr ⟨m, hm⟩]
  · rintro (⟨m, hm⟩ | ⟨m, hm⟩)
    · refine ⟨.Ioi m, isInvariant_Ioi_of_isBot hm, fun h' ↦ ?_, fun h' ↦ ?_⟩
      · simpa using congrArg (m ∈ ·) h'
      · exact UpperSet.notMem_top (h' ▸ (hm x).lt_of_ne fun h ↦ hxb (h ▸ hm) : x ∈ (⊤ : UpperSet D))
    · refine ⟨.Ici m, isInvariant_Ici_of_isTop hm, fun h' ↦ ?_, fun h' ↦ ?_⟩
      · exact hxt fun z ↦ (hm z).trans (by simpa using congrArg (x ∈ ·) h')
      · simpa using congrArg (m ∈ ·) h'

end Homogeneous

end UpperSet

/-! ### Kinds of standard -/

/-- A positive standard is a kind of standard for the positive form: the contextual norm of a
relative adjective, an endpoint of the scale for an absolute one ([kennedy-2007]), or a threshold
an adjective fixes lexically. -/
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

/-- A kind of standard requires a comparison class when some scale does not fix some standard of
the kind, so that a domain of comparison must supply it ([kennedy-2007]). -/
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

/-! ### Interpretive Economy -/

namespace Boundedness

variable {b : Boundedness} {s : PositiveStandard}

/-- The canonical scale of a boundedness fixes a standard other than all degrees and none exactly
when it has an endpoint. -/
theorem exists_isInvariant_ne_iff :
    (∃ U : UpperSet b.DegreeShape, U.IsInvariant ∧ U ≠ ⊥ ∧ U ≠ ⊤) ↔ b ≠ .open_ := by
  rw [UpperSet.exists_isInvariant_ne_iff_of_exists_orderIso b.exists_not_isBot_not_isTop
    b.exists_orderIso_degreeShape, exists_isBot_degreeShape, exists_isTop_degreeShape]
  cases b <;> decide

/-- Interpretive Economy ([kennedy-2007] (66)) admits a kind of standard on a scale when the scale
has a standard of that kind and, if the scale fixes a standard other than all degrees and none,
fixes every standard of that kind. -/
structure Admits (b : Boundedness) (s : PositiveStandard) : Prop where
  /-- The scale has a standard of the kind. -/
  nonempty : (s.standards b.DegreeShape).Nonempty
  /-- If the scale fixes a nontrivial standard, it fixes every standard of the kind. -/
  isInvariant : (∃ U : UpperSet b.DegreeShape, U.IsInvariant ∧ U ≠ ⊥ ∧ U ≠ ⊤) →
    ∀ U ∈ s.standards b.DegreeShape, U.IsInvariant

private theorem exists_orderIso_apply_ne (b : Boundedness) :
    ∃ (x : b.DegreeShape) (f : b.DegreeShape ≃o b.DegreeShape), f x ≠ x := by
  cases b
  · exact ⟨(0 : ℤ), OrderIso.addRight 1, by simp⟩
  · exact ⟨((0 : ℤ) : WithBot ℤ), (OrderIso.addRight 1).withBotCongr, by simp⟩
  · exact ⟨((0 : ℤ) : WithTop ℤ), (OrderIso.addRight 1).withTopCongr, by simp⟩
  · exact ⟨(((0 : ℤ) : WithBot ℤ) : WithTop (WithBot ℤ)),
      (OrderIso.addRight 1).withBotCongr.withTopCongr, by simp⟩

/-- A kind whose standards are the thresholds is admitted exactly on an open scale. -/
private theorem admits_iff_of_standards
    (h : s.standards b.DegreeShape = {U | ∃ θ, U = .Ioi θ ∨ U = .Ici θ}) :
    b.Admits s ↔ b = .open_ := by
  obtain ⟨x, f, hf⟩ := b.exists_orderIso_apply_ne
  refine ⟨fun hs ↦ by_contra fun hb ↦ ?_, fun hb ↦ ⟨?_, fun hU ↦ ?_⟩⟩
  · exact UpperSet.not_isInvariant_Ici f hf
      (hs.isInvariant (exists_isInvariant_ne_iff.2 hb) _ (h ▸ ⟨x, .inr rfl⟩))
  · exact h ▸ ⟨.Ici x, x, .inr rfl⟩
  · exact (exists_isInvariant_ne_iff.1 hU hb).elim

/-- The contextual standard is admitted exactly on a totally open scale, since a scale with an
endpoint fixes the endpoint standard. -/
@[simp] theorem admits_contextual : b.Admits .contextual ↔ b = .open_ :=
  admits_iff_of_standards rfl

@[simp] theorem admits_necessity : b.Admits .necessity ↔ b = .open_ :=
  admits_iff_of_standards rfl

@[simp] theorem admits_extreme : b.Admits .extreme ↔ b = .open_ :=
  admits_iff_of_standards rfl

@[simp] theorem admits_minEndpoint : b.Admits .minEndpoint ↔ b.HasMin := by
  rw [← exists_isBot_degreeShape]
  exact ⟨fun ⟨⟨_, m, hm, _⟩, _⟩ ↦ ⟨m, hm⟩, fun ⟨m, hm⟩ ↦ ⟨⟨_, m, hm, rfl⟩,
    fun _ _ ⟨_, hm', hU⟩ ↦ hU ▸ UpperSet.isInvariant_Ioi_of_isBot hm'⟩⟩

@[simp] theorem admits_maxEndpoint : b.Admits .maxEndpoint ↔ b.HasMax := by
  rw [← exists_isTop_degreeShape]
  exact ⟨fun ⟨⟨_, m, hm, _⟩, _⟩ ↦ ⟨m, hm⟩, fun ⟨m, hm⟩ ↦ ⟨⟨_, m, hm, rfl⟩,
    fun _ _ ⟨_, hm', hU⟩ ↦ hU ▸ UpperSet.isInvariant_Ici_of_isTop hm'⟩⟩

instance (b : Boundedness) : (s : PositiveStandard) → Decidable (b.Admits s)
  | .contextual  => decidable_of_iff _ admits_contextual.symm
  | .minEndpoint => decidable_of_iff _ admits_minEndpoint.symm
  | .maxEndpoint => decidable_of_iff _ admits_maxEndpoint.symm
  | .necessity   => decidable_of_iff _ admits_necessity.symm
  | .extreme     => decidable_of_iff _ admits_extreme.symm

theorem not_admits_contextual_of_ne_open (h : b ≠ .open_) :
    ¬ b.Admits .contextual :=
  mt admits_contextual.1 h

/-- The default standard of a scale is the kind Interpretive Economy admits where it admits one,
and the maximum on a totally closed scale. -/
def defaultStandard : Boundedness → PositiveStandard
  | .open_        => .contextual
  | .lowerClosed => .minEndpoint
  | .upperClosed => .maxEndpoint
  | .closed       => .maxEndpoint

theorem admits_defaultStandard (b : Boundedness) : b.Admits b.defaultStandard := by
  cases b <;> decide

/-- The default standard is the maximum exactly when the scale has one. -/
theorem defaultStandard_eq_maxEndpoint_iff :
    b.defaultStandard = .maxEndpoint ↔ b.HasMax := by
  cases b <;> decide

/-- Off the open scale the default standard is the strongest admitted one: every standard of an
admitted kind is entailed by the default standard. On a totally closed scale this is the
preference for the maximum, which entails the minimum ([kennedy-2007]). -/
theorem le_of_mem_standards_defaultStandard (hb : b ≠ .open_) (hs : b.Admits s)
    {U V : UpperSet b.DegreeShape} (hU : U ∈ s.standards b.DegreeShape)
    (hV : V ∈ b.defaultStandard.standards b.DegreeShape) : U ≤ V := by
  obtain ⟨x, hxb, -⟩ := b.exists_not_isBot_not_isTop
  cases b <;> cases s <;> simp [HasMin, HasMax] at hs hb
  all_goals
    obtain ⟨m, hm, rfl⟩ := hU
    obtain ⟨t, ht, rfl⟩ := hV
  · rw [le_antisymm (hm t) (ht m)]
  · rw [le_antisymm (ht m) (hm t)]
  · exact UpperSet.Ioi_le_Ici ((hm t).lt_of_ne fun h ↦ hxb fun y ↦ (ht x).trans (h ▸ hm y))
  · rw [le_antisymm (ht m) (hm t)]

/-- The default standards of a scale and its dual are complementary exactly when the scale has one
endpoint. An open scale gives both poles a contextual standard and a totally closed one gives both
the maximum, as for *full* and *empty*. -/
theorem complementary_defaultStandard_dual_iff :
    b.defaultStandard.Complementary b.dual.defaultStandard ↔
      b = .lowerClosed ∨ b = .upperClosed := by
  cases b <;> decide

/-- A scale is relative when its default standard requires a comparison class, as for *tall*,
*expensive* and *big*. -/
def IsRelative (b : Boundedness) : Prop := b.defaultStandard.RequiresComparisonClass

instance : DecidablePred IsRelative :=
  fun b ↦ inferInstanceAs (Decidable b.defaultStandard.RequiresComparisonClass)

/-- The relative scales are the open ones. -/
theorem isRelative_iff : b.IsRelative ↔ b = .open_ := by
  cases b <;> decide

/-- A scale with a least degree adjoined admits the minimum standard, and the maximum iff the
original scale has one ([kennedy-levin-2008] (23), (25)). -/
theorem admits_withMin_iff :
    b.withMin.Admits s ↔ s = .minEndpoint ∨ s = .maxEndpoint ∧ b.HasMax := by
  cases b <;> cases s <;> simp [withMin, HasMin, HasMax]

theorem defaultStandard_withMin (b : Boundedness) :
    b.withMin.defaultStandard = if b.HasMax then .maxEndpoint else .minEndpoint := by
  cases b <;> rfl

end Boundedness
