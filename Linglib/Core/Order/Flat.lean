module

public import Mathlib.Order.Cover
public import Mathlib.Data.Part
public import Linglib.Core.Order.PartialUnify

/-!
# The flat order

`Flat α` is `Option α` with the flat order: `⊥` below everything, distinct
values incomparable. It is the lift of the discrete order on `α` — the order
of partial values under extension — and is mathlib's order on `Part α`
carried on its decidable twin `Option` (`le_iff_ofOption_le`), where it
supports `DecidableEq`, `DecidableLE`, `#eval`, and constructor
pattern-matching. "Flat domain" is the domain-theory name for this poset
([winskel-1993]; the `flat` class of Isabelle/HOLCF).

The flat order is bounded-complete but not a lattice: meets are total (`SemilatticeInf`), joins
partial (`PartialUnify`). Linguistically it is one atomic feature slot, ordered by [shieber-1986]'s
and [carpenter-1992]'s subsumption; `Flat Bool` is the knowledge order of Kleene three-valued logic.
Feature bundles arise via the `Pi` `PartialUnify` instance, with `Compat` as consistency.

The order skeleton follows the `WithBot` mold (`Mathlib/Order/TypeTags.lean`,
`Mathlib/Order/WithBot.lean`) and is an `[UPSTREAM]` candidate for
`Mathlib/Order/Flat.lean`, coexisting with the namespaced `Module.Flat` and
`ConvexCone.Flat`. The `PartialUnify` instance and `compat_iff` stay here.

## Main declarations

* `Flat` — the order-carrying alias, with coercion `↑ : α → Flat α`, and
  `PartialOrder`, `OrderBot`, `SemilatticeInf` and `PartialUnify` instances
* `Flat.coe_le_coe`, `Flat.not_coe_le_bot` — the order, characterized
* `Flat.covBy_iff` — the covers, from `⊥` to a committed value: the order has height one
* `Flat.coe_inf_coe`, `Flat.disjoint_coe_coe`, `Flat.compat_coe_coe` — the meet,
  disjointness and compatibility of committed slots
* `Flat.unbotD` — the value, or a default at `⊥`, as `WithBot.unbotD`
* `Flat.or` — left-biased total merge, with `le_or_left`/`or_le`
* `Flat.compat_iff` — slot compatibility (`Compat`), characterized
* `Flat.unify_eq_top_of_ne` — distinct atoms do not unify (the
  non-distributivity witness)
-/

@[expose] public section


/-- `Flat α` is `Option α` carrying the flat information order: `⊥` below
everything, distinct values incomparable. A `def`, not an `abbrev`, so the
order instances do not leak onto bare `Option`. -/
def Flat (α : Type*) := Option α

namespace Flat

variable {α : Type*} {a b : α} {x y z : Flat α}

/-- The canonical map from `α` into `Flat α`. -/
@[coe, match_pattern] def some : α → Flat α :=
  Option.some

instance coe : Coe α (Flat α) :=
  ⟨some⟩

instance bot : Bot (Flat α) :=
  ⟨none⟩

instance inhabited : Inhabited (Flat α) :=
  ⟨⊥⟩

instance [DecidableEq α] : DecidableEq (Flat α) :=
  inferInstanceAs (DecidableEq (Option α))

instance [BEq α] : BEq (Flat α) :=
  inferInstanceAs (BEq (Option α))

instance [BEq α] [LawfulBEq α] : LawfulBEq (Flat α) :=
  inferInstanceAs (LawfulBEq (Option α))

instance [Repr α] : Repr (Flat α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | Option.some a => "↑" ++ repr a⟩

theorem coe_injective : Function.Injective ((↑) : α → Flat α) :=
  Option.some_injective _

@[simp, norm_cast] theorem coe_inj : (a : Flat α) = b ↔ a = b :=
  Option.some_inj

theorem none_eq_bot : (none : Flat α) = (⊥ : Flat α) := rfl

theorem some_eq_coe (a : α) : (Option.some a : Flat α) = (↑a : Flat α) := rfl

@[simp] theorem bot_ne_coe : ⊥ ≠ (a : Flat α) := nofun

@[simp] theorem coe_ne_bot : (a : Flat α) ≠ ⊥ := nofun

/-- Recursor for `Flat` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : Flat α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ x : Flat α, C x
  | ⊥ => bot
  | (a : α) => coe a

@[simp] theorem recBotCoe_bot {C : Flat α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d := rfl

@[simp] theorem recBotCoe_coe {C : Flat α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x := rfl

theorem ne_bot_iff_exists : x ≠ ⊥ ↔ ∃ a : α, x = ↑a := by
  cases x <;> simp

/-- The value of an element, or the default `d` at `⊥`, as `WithBot.unbotD`. -/
def unbotD (d : α) (x : Flat α) : α :=
  recBotCoe d id x

@[simp] theorem unbotD_bot (d : α) : unbotD d (⊥ : Flat α) = d := rfl

@[simp] theorem unbotD_coe (d b : α) : unbotD d (b : Flat α) = b := rfl

/-- The value of a committed slot. -/
def get (x : Flat α) (h : x ≠ ⊥) : α := Option.get x (Option.isSome_iff_ne_none.2 h)

@[simp] theorem coe_get (x : Flat α) (h : x ≠ ⊥) : (↑(x.get h) : Flat α) = x := Option.some_get _

@[simp] theorem get_coe (a : α) (h : (a : Flat α) ≠ ⊥) : (a : Flat α).get h = a := rfl

/-! ### The flat order -/

/-- Auxiliary definition for the order on `Flat`. -/
@[mk_iff le_def_aux]
protected inductive LE : Flat α → Flat α → Prop
  | protected bot_le (x : Flat α) : Flat.LE ⊥ x
  | protected refl (a : α) : Flat.LE ↑a ↑a

/-- The flat order on `Flat α`, defined by `⊥ ≤ x` and `↑a ≤ ↑a`. The
definition as an inductive predicate follows `WithBot.LE`; it cannot be
accidentally unfolded too far. -/
instance (priority := 10) instLE : LE (Flat α) where le := Flat.LE

lemma le_def : x ≤ y ↔ x = ⊥ ∨ ∃ a : α, x = ↑a ∧ y = ↑a := by
  rw [show (x ≤ y) = Flat.LE x y from rfl, le_def_aux]

@[simp, norm_cast] theorem coe_le_coe : (a : Flat α) ≤ b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .refl a⟩

@[simp] theorem not_coe_le_bot (a : α) : ¬(a : Flat α) ≤ ⊥ :=
  fun h => by cases h

instance : OrderBot (Flat α) where
  bot_le := Flat.LE.bot_le

instance : PartialOrder (Flat α) where
  le_refl x := by cases x with
    | bot => exact .bot_le _
    | coe a => exact .refl a
  le_trans x y z hxy hyz := by
    cases hxy with
    | bot_le => exact .bot_le _
    | refl => exact hyz
  le_antisymm x y hxy hyx := by
    cases hxy with
    | bot_le => cases hyx with | bot_le => rfl
    | refl => rfl

theorem coe_le_iff : (a : Flat α) ≤ y ↔ y = ↑a :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .refl a⟩

theorem isMax_coe (a : α) : IsMax (a : Flat α) := fun _ hy ↦ (coe_le_iff.1 hy).le

theorem isMax_of_ne_bot (hx : x ≠ ⊥) : IsMax x := by
  obtain ⟨a, rfl⟩ := ne_bot_iff_exists.1 hx
  exact isMax_coe a

instance [DecidableEq α] : DecidableLE (Flat α)
  | ⊥, _ => isTrue (.bot_le _)
  | (a : α), ⊥ => isFalse (not_coe_le_bot a)
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

theorem eq_of_le (h : x ≤ y) (hyx : y ≠ ⊥ → x ≠ ⊥) : x = y := by
  cases h with
  | bot_le y =>
    cases y with
    | bot => rfl
    | coe a => exact absurd (hyx coe_ne_bot) (by simp)
  | refl => rfl

/-! ### Covering -/

/-- The flat order has height one: its covers are the steps from `⊥` to a committed value. -/
theorem covBy_iff : x ⋖ y ↔ x = ⊥ ∧ y ≠ ⊥ := by
  constructor
  · intro h
    rcases le_def.1 h.1.le with rfl | ⟨a, rfl, rfl⟩
    · exact ⟨rfl, fun hy ↦ h.1.ne hy.symm⟩
    · exact absurd rfl h.1.ne
  · rintro ⟨rfl, hy⟩
    refine ⟨bot_lt_iff_ne_bot.2 hy, fun z hz hzy ↦ ?_⟩
    rcases le_def.1 hzy.le with rfl | ⟨a, rfl, rfl⟩
    · exact lt_irrefl _ hz
    · exact lt_irrefl _ hzy

@[simp] theorem bot_covBy_coe (a : α) : (⊥ : Flat α) ⋖ a :=
  covBy_iff.2 ⟨rfl, coe_ne_bot⟩

theorem le_iff_ofOption_le :
    x ≤ y ↔ Part.ofOption (x : Option α) ≤ Part.ofOption (y : Option α) := by
  constructor
  · rintro (_ | _)
    · exact fun i hi => absurd (Part.mem_ofOption.mp hi) nofun
    · exact le_rfl
  · intro h
    cases x with
    | bot => exact bot_le
    | coe a =>
      obtain rfl : y = ↑a :=
        Part.mem_ofOption.mp (h a (Part.mem_ofOption.mpr rfl))
      exact le_rfl

/-! ### Left-biased merge -/

/-- The left-biased total merge of two slots, keeping the first committed
value; the total companion of the partial join `Flat.unify`. -/
protected def or (x y : Flat α) : Flat α :=
  Option.or x y

@[simp] theorem bot_or (y : Flat α) : (⊥ : Flat α).or y = y := rfl

@[simp] theorem coe_or (a : α) (y : Flat α) : (↑a : Flat α).or y = ↑a := rfl

@[simp] theorem or_bot (x : Flat α) : x.or ⊥ = x := by cases x <;> rfl

theorem or_assoc (x y z : Flat α) : (x.or y).or z = x.or (y.or z) :=
  Option.or_assoc ..

theorem le_or_left (x y : Flat α) : x ≤ x.or y := by
  cases x <;> simp

theorem or_le (hx : x ≤ z) (hy : y ≤ z) : x.or y ≤ z := by
  cases x with
  | bot => exact hy
  | coe a => exact hx

@[simp] theorem or_self (x : Flat α) : x.or x = x := by cases x <;> rfl

/-! ### Meets -/

/-- The meet of two slots is their agreement, or `⊥` — the *generalization*
(anti-unification) of the two, order-dual to the partial join `PartialUnify`. -/
protected def inf [DecidableEq α] (x y : Flat α) : Flat α :=
  if x = y then x else ⊥

instance [DecidableEq α] : SemilatticeInf (Flat α) where
  inf := Flat.inf
  inf_le_left x y := by unfold Flat.inf; split <;> simp
  inf_le_right x y := by unfold Flat.inf; split <;> simp_all
  le_inf x y z hxy hxz := by
    cases hxy with
    | bot_le => exact bot_le
    | refl a =>
      obtain rfl : z = ↑a := by cases hxz; rfl
      simp [Flat.inf]

theorem inf_def [DecidableEq α] (x y : Flat α) : x ⊓ y = if x = y then x else ⊥ := rfl

@[simp] theorem coe_inf_coe [DecidableEq α] (a b : α) :
    (a : Flat α) ⊓ b = if a = b then (a : Flat α) else ⊥ := by
  simp [inf_def]

/-- Two committed slots are disjoint exactly when they disagree. -/
@[simp] theorem disjoint_coe_coe : Disjoint (a : Flat α) b ↔ a ≠ b := by
  constructor
  · rintro h rfl
    exact coe_ne_bot (disjoint_self.1 h)
  · rintro hab x hxa hxb
    cases x <;> simp_all

/-- Two committed slots are compatible exactly when they agree. -/
@[simp] theorem compat_coe_coe : Compat (a : Flat α) b ↔ a = b :=
  ⟨fun ⟨_, hu⟩ ↦ by
    obtain ⟨ha, hb⟩ := mem_upperBounds_pair.mp hu
    exact coe_inj.1 ((coe_le_iff.1 ha).symm.trans (coe_le_iff.1 hb)),
   fun h ↦ h ▸ compat_self _⟩

instance [DecidableEq α] : Decidable (Disjoint x y) :=
  decidable_of_iff _ _root_.disjoint_iff.symm

/-! ### Unification -/

/-- Unification of two slots merges equal commitments, treats `⊥` as
identity, and fails on distinct commitments. -/
protected def unify [DecidableEq α] : Flat α → Flat α → WithTop (Flat α)
  | ⊥, y => y
  | (a : α), ⊥ => (a : Flat α)
  | (a : α), (b : α) => if a = b then ((a : Flat α) : WithTop (Flat α)) else ⊤

private theorem unify_coe_coe [DecidableEq α] (a b : α) :
    Flat.unify (↑a : Flat α) ↑b = if a = b then ((a : Flat α) : WithTop (Flat α)) else ⊤ :=
  rfl

instance [DecidableEq α] : PartialUnify (Flat α) where
  unify := Flat.unify
  isLUB_of_unify_eq_coe := by
    intro x y z h
    match x, y with
    | ⊥, y =>
      obtain rfl : y = z := WithTop.coe_inj.mp h
      exact ⟨mem_upperBounds_pair.mpr ⟨bot_le, le_rfl⟩,
        fun u hu ↦ (mem_upperBounds_pair.mp hu).2⟩
    | (a : α), ⊥ =>
      obtain rfl : (↑a : Flat α) = z := WithTop.coe_inj.mp h
      exact ⟨mem_upperBounds_pair.mpr ⟨le_rfl, bot_le⟩,
        fun u hu ↦ (mem_upperBounds_pair.mp hu).1⟩
    | (a : α), (b : α) =>
      rw [unify_coe_coe] at h
      split at h
      · next hab =>
        subst hab
        obtain rfl : (↑a : Flat α) = z := WithTop.coe_inj.mp h
        rw [Set.pair_eq_singleton]
        exact isLUB_singleton
      · exact absurd h WithTop.top_ne_coe
  unify_ne_top_of_bddAbove := by
    intro x y ⟨u, hu⟩
    obtain ⟨hxu, hyu⟩ := mem_upperBounds_pair.mp hu
    match x, y with
    | ⊥, y => exact WithTop.coe_ne_top
    | (a : α), ⊥ => exact WithTop.coe_ne_top
    | (a : α), (b : α) =>
      obtain rfl : u = ↑a := coe_le_iff.mp hxu
      obtain rfl : a = b := coe_inj.mp (coe_le_iff.mp hyu)
      show Flat.unify (↑a : Flat α) ↑a ≠ ⊤
      rw [unify_coe_coe, ite_eq_left rfl]
      exact WithTop.coe_ne_top

/-- Two slots are compatible exactly when their committed values coincide;
an uncommitted slot is a wildcard. -/
theorem compat_iff : Compat x y ↔ ∀ a : α, x = ↑a → ∀ b : α, y = ↑b → a = b := by
  refine ⟨fun ⟨u, hu⟩ a ha b hb ↦ ?_, fun h ↦ ?_⟩
  · have hx := hu (Set.mem_insert x {y})
    have hy := hu (Set.mem_insert_of_mem x rfl)
    subst ha hb
    exact coe_inj.1 ((coe_le_iff.1 hx).symm.trans (coe_le_iff.1 hy))
  · rcases eq_or_ne x ⊥ with rfl | hx
    · exact bot_compat y
    rcases eq_or_ne y ⊥ with rfl | hy
    · exact compat_bot x
    obtain ⟨a, rfl⟩ := ne_bot_iff_exists.1 hx
    obtain ⟨b, rfl⟩ := ne_bot_iff_exists.1 hy
    obtain rfl := h a rfl b rfl
    exact compat_self _

theorem le_or_right (h : Compat x y) : y ≤ x.or y := by
  cases x with
  | bot => exact le_rfl
  | coe a =>
    rcases eq_or_ne y ⊥ with rfl | hy
    · exact bot_le
    obtain ⟨b, rfl⟩ := ne_bot_iff_exists.1 hy
    obtain rfl := compat_iff.1 h a rfl b rfl
    exact le_rfl

/-! ### Non-distributivity

The flat order is not distributive: three distinct atoms (with a top
adjoined) form the diamond M₃ — [carpenter-1992] takes subsumption orders
to be neither distributive nor modular in general. `Flat` carries only the
partial join (`PartialUnify`), so the distributive law cannot even be
*stated* on it directly; `unify_eq_top_of_ne` is the witness — distinct
atoms have no upper bound, so the join the law would require is undefined. -/

theorem unify_eq_top_of_ne [DecidableEq α] (h : a ≠ b) : Flat.unify (↑a : Flat α) ↑b = ⊤ := by
  rw [unify_coe_coe, ite_eq_right h]

end Flat
