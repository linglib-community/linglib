module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Basic
public import Linglib.Core.Order.Flat

/-!
# Variable assignments

A *variable assignment* maps variables to values. Three registers share
this file: total assignments (Tarski-style, [heim-kratzer-1998],
[henkin-monk-tarski-1971]), partial assignments (variables may be
unvalued, [spector-2026], [beaver-krahmer-2001]), and plural assignments
(sets of partial assignments — the information states of plural dynamic
semantics, [van-den-berg-1996], [brasoveanu-2008],
[haug-dalrymple-2020]).

## Main definitions

* `Assignment E`: total assignments `ℕ → E`, on the Heim–Kratzer
  ℕ-register.
* `PartialAssign Var D`: partial assignments `Var → Flat D`, ordered by extension, with
  `PartialAssign.domain` the variables an assignment values and `PartialAssign.single x d` the
  assignment valuing `x` alone.
* `PluralAssign Var D`: sets of partial assignments, with `PluralAssign.value` the values a
  variable takes across them and `PluralAssign.restrict` the restriction of
  [Spector][spector-2026]. A variable takes a single value `d` when its values are `{d}`, Spector's
  *atomic*.

## Main results

* `PartialAssign.le_iff_eqOn_domain`: one assignment extends another when it agrees with it on
  the other's domain.
* `PartialAssign.covBy_iff_exists_update`: one assignment covers another when it values exactly
  one more variable, the counterpart of `Set.covBy_iff_exists_insert`.
* `PluralAssign.value_eq_singleton_iff`: a single value as [Spector][spector-2026] states it.
* `PluralAssign.value_restrict_eq_singleton_iff`: a nonempty restriction of a variable to a value
  gives it that single value.

## Notation

* `g[n ↦ x]`: `Function.update g n x`, the assignment modification of
  [Heim and Kratzer][heim-kratzer-1998], scoped to `Assignment` (`open scoped Assignment`).

## Implementation notes

* `PartialAssign` takes values in `Flat D`, the decidable counterpart of
  mathlib's partial values `Part D` with the same order
  (`Flat.le_iff_ofOption_le`): `Part`-valued partiality would forfeit
  `DecidableEq` on assignments, which `Finset`-state systems (QBSML) and
  `decide`-checked studies need. The pointwise order is extension, `⊥` is
  the assignment valuing nothing, `g x = ⊥` says `x` is unvalued and
  `g x = ↑d` that it has the value `d`; there is no wrapper predicate.
* Update is mathlib's `Function.update`; `PartialAssign.update` only
  fuses the coercion (cf. `Finsupp.update`), and its lemmas are one-step
  consequences of the `Function.update_*` laws.
* Random assignment `[x]`, relating assignments that agree off `x`, is
  `DynamicSemantics.Update.randomAssign` at the function-type register structure; it is not
  redefined here.
* Use these names only for the variable-binding role — the state that
  quantifiers `update` and free variables look up. A `ℕ → E` that is not
  variable-binding state (interpretation tables, lookup arrays) should
  stay a plain function type.

## References

* [I. Heim, A. Kratzer, *Semantics in Generative Grammar* (1998)][heim-kratzer-1998]
* [L. Henkin, J. D. Monk and A. Tarski, *Cylindric algebras, part I*
  (1971)][henkin-monk-tarski-1971]
* [B. Spector, *Trivalence and transparency: A non-dynamic approach to anaphora*
  (2026)][spector-2026]
* [D. Beaver, E. Krahmer, *A Partial Account of Presupposition Projection*
  (2001)][beaver-krahmer-2001]
* [M. H. van den Berg, *Some aspects of the internal structure of discourse: the dynamics of
  nominal anaphora* (1996)][van-den-berg-1996]
* [A. Brasoveanu, *Donkey pluralities: plural information states versus non-atomic
  individuals* (2008)][brasoveanu-2008]
* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
-/

@[expose] public section

/-! ### Total assignments -/

/-- `Assignment E` is the type of total variable assignments, sending each index in `ℕ` to a value
in `E`: an entity for entity pronouns, a situation index for situation pronouns, a time for
temporal variables. -/
abbrev Assignment (E : Type*) := Nat → E

namespace Assignment

/-- `g[n ↦ x]` is the assignment sending `n` to `x` and agreeing with `g` elsewhere, the
assignment modification of [Heim and Kratzer][heim-kratzer-1998]. It is notation for
`Function.update g n x`. -/
scoped notation:max g "[" n " ↦ " x "]" => Function.update g n x

end Assignment

/-! ### Partial assignments -/

/-- `PartialAssign Var D` is the type of partial assignments of values in `D` to variables in
`Var`: `g x = ⊥` when `g` leaves `x` unvalued, and `g ≤ h` when `h` extends `g`. -/
abbrev PartialAssign (Var D : Type*) := Var → Flat D

namespace PartialAssign

variable {Var D : Type*} {g h : PartialAssign Var D} {x y : Var}

/-- `g.domain` is the set of variables that `g` values. -/
def domain (g : PartialAssign Var D) : Set Var := {x | g x ≠ ⊥}

@[simp] theorem mem_domain : x ∈ g.domain ↔ g x ≠ ⊥ := Iff.rfl

@[simp] theorem domain_bot : (⊥ : PartialAssign Var D).domain = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ h rfl

theorem le_iff_eqOn_domain : g ≤ h ↔ Set.EqOn g h g.domain := by
  refine Pi.le_def.trans (forall_congr' fun x ↦ ⟨fun hx hne ↦ Flat.eq_of_le hx fun _ ↦ hne,
    fun hx ↦ ?_⟩)
  rcases eq_or_ne (g x) ⊥ with h0 | hne
  · rw [h0]; exact bot_le
  · exact (hx hne).le

theorem domain_mono (hgh : g ≤ h) : g.domain ⊆ h.domain :=
  fun x hx ↦ ne_bot_of_le_ne_bot hx (hgh x)

theorem covBy_iff : g ⋖ h ↔ ∃ x, g x = ⊥ ∧ h x ≠ ⊥ ∧ ∀ y ≠ x, g y = h y := by
  simp only [Pi.covBy_iff, Flat.covBy_iff, and_assoc]

variable [DecidableEq Var]

/-- `g.update x d` sends `x` to `d` and agrees with `g` elsewhere. -/
def update (g : PartialAssign Var D) (x : Var) (d : D) :
    PartialAssign Var D :=
  Function.update g x ↑d

@[simp] theorem update_self (x : Var) (d : D) (g : PartialAssign Var D) :
    g.update x d x = ↑d :=
  Function.update_self ..

@[simp] theorem update_of_ne (h : y ≠ x) (d : D) (g : PartialAssign Var D) :
    g.update x d y = g y :=
  Function.update_of_ne h ..

theorem update_eq_self {x : Var} {a : D} (h : g x = ↑a) : g.update x a = g := by
  rw [update, ← h]; exact Function.update_eq_self x g

theorem update_comm (h : x ≠ y) (a b : D) (g : PartialAssign Var D) :
    (g.update x a).update y b = (g.update y b).update x a :=
  Function.update_comm h ..

@[simp] theorem update_idem (x : Var) (a b : D) (g : PartialAssign Var D) :
    (g.update x a).update x b = g.update x b :=
  Function.update_idem ..

@[simp] theorem domain_update (g : PartialAssign Var D) (x : Var) (d : D) :
    (g.update x d).domain = insert x g.domain := by
  ext y
  obtain rfl | hy := eq_or_ne y x <;> simp [*]

theorem covBy_update {x : Var} (hx : g x = ⊥) (d : D) : g ⋖ g.update x d :=
  covBy_iff.2 ⟨x, hx, by simp, fun _ hy ↦ (update_of_ne hy d g).symm⟩

theorem covBy_iff_exists_update : g ⋖ h ↔ ∃ x d, g x = ⊥ ∧ g.update x d = h := by
  refine ⟨fun hc ↦ ?_, fun ⟨x, d, hx, he⟩ ↦ he ▸ covBy_update hx d⟩
  obtain ⟨x, hx, hhx, hagree⟩ := covBy_iff.1 hc
  obtain ⟨d, hd⟩ := Flat.ne_bot_iff_exists.1 hhx
  refine ⟨x, d, hx, funext fun y ↦ ?_⟩
  obtain rfl | hy := eq_or_ne y x
  · simp [hd]
  · rw [update_of_ne hy, hagree y hy]

/-- `single x d` sends `x` to `d` and leaves every other variable unvalued. -/
def single (x : Var) (d : D) : PartialAssign Var D :=
  update ⊥ x d

theorem bot_update (x : Var) (d : D) : (⊥ : PartialAssign Var D).update x d = single x d :=
  rfl

@[simp] theorem single_eq_same {d : D} : single x d x = ↑d :=
  update_self ..

@[simp] theorem single_eq_of_ne {d : D} (h : y ≠ x) : single x d y = ⊥ :=
  update_of_ne h ..

@[simp] theorem domain_single (x : Var) (d : D) : (single x d).domain = {x} := by
  simp [single]

end PartialAssign

/-! ### Plural assignments -/

/-- `PluralAssign Var D` is the type of plural assignments, sets of partial assignments, which are
the plural information states of [van den Berg][van-den-berg-1996] and the assignment sets of
[Spector][spector-2026]. -/
abbrev PluralAssign (Var D : Type*) := Set (PartialAssign Var D)

namespace PluralAssign

variable {Var D : Type*} {G H : PluralAssign Var D} {g : PartialAssign Var D} {x : Var}
  {a d d' : D}

/-! #### Values -/

/-- `G.value x` is the set of values `x` takes in `G`; assignments leaving `x` unvalued
contribute none. -/
def value (G : PluralAssign Var D) (x : Var) : Set D :=
  {d | ∃ g ∈ G, g x = ↑d}

@[simp] theorem mem_value : d ∈ G.value x ↔ ∃ g ∈ G, g x = ↑d :=
  Iff.rfl

theorem value_mono (h : G ⊆ H) : G.value x ⊆ H.value x :=
  fun _ ⟨g, hg, hd⟩ ↦ ⟨g, h hg, hd⟩

@[simp] theorem value_empty : (∅ : PluralAssign Var D).value x = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hg, _⟩ ↦ hg

@[simp] theorem value_singleton : ({g} : PluralAssign Var D).value x = {d : D | g x = ↑d} := by
  ext
  simp

@[simp] theorem value_union : (G ∪ H).value x = G.value x ∪ H.value x := by
  ext
  simp [or_and_right, exists_or]

/-! #### Restriction -/

/-- `G.restrict x a` is the set of assignments in `G` sending `x` to `a`, the $G_{x=a}$ of
[Spector][spector-2026] (§6.2). -/
def restrict (G : PluralAssign Var D) (x : Var) (a : D) : PluralAssign Var D :=
  {g ∈ G | g x = ↑a}

@[simp] theorem mem_restrict : g ∈ G.restrict x a ↔ g ∈ G ∧ g x = ↑a :=
  Iff.rfl

theorem value_restrict_subset : (G.restrict x a).value x ⊆ {a} :=
  fun _ ⟨_, hg, hd⟩ ↦ Flat.coe_inj.1 (hd.symm.trans hg.2)

theorem value_restrict (h : (G.restrict x a).Nonempty) : (G.restrict x a).value x = {a} :=
  let ⟨g, hg⟩ := h
  (Set.Nonempty.subset_singleton_iff (s := (G.restrict x a).value x) ⟨a, g, hg, hg.2⟩).1
    value_restrict_subset

/-! #### Single values -/

theorem value_eq_singleton_iff :
    G.value x = {d} ↔ (∃ g ∈ G, g x = ↑d) ∧ ∀ g ∈ G, g x ≠ ⊥ → g x = ↑d := by
  refine Set.eq_singleton_iff_unique_mem.trans ⟨fun ⟨hex, hall⟩ ↦ ⟨hex, fun g hg hne ↦ ?_⟩,
    fun ⟨hex, hall⟩ ↦ ⟨hex, fun a ⟨g, hg, ha⟩ ↦ ?_⟩⟩
  · obtain ⟨a, ha⟩ := Flat.ne_bot_iff_exists.1 hne
    rw [ha, hall a ⟨g, hg, ha⟩]
  · exact Flat.coe_inj.1 (ha.symm.trans (hall g hg (ha ▸ Flat.coe_ne_bot)))

theorem eq_of_mem_restrict (h : G.value x = {d}) (hg : g ∈ G.restrict x a) : a = d :=
  h.subset ⟨g, hg.1, hg.2⟩

@[simp] theorem value_singleton_eq_singleton_iff :
    ({g} : PluralAssign Var D).value x = {d} ↔ g x = ↑d := by
  rw [value_singleton, Set.eq_singleton_iff_unique_mem]
  exact ⟨And.left, fun h ↦ ⟨h, fun _ hd' ↦ Flat.coe_inj.1 (hd'.symm.trans h)⟩⟩

theorem value_restrict_eq_singleton_iff :
    (G.restrict x a).value x = {d} ↔ (G.restrict x a).Nonempty ∧ d = a := by
  refine ⟨fun h ↦ ?_, fun ⟨hne, hd⟩ ↦ hd.symm ▸ value_restrict hne⟩
  have hd : d ∈ (G.restrict x a).value x := h ▸ rfl
  exact ⟨let ⟨g, hg, _⟩ := hd; ⟨g, hg⟩, value_restrict_subset hd⟩

end PluralAssign
