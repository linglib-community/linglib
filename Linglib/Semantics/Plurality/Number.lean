module

public import Linglib.Semantics.Mereology.Basic
public import Linglib.Syntax.Feature.Number.Decomposition

/-!
# Number features as region operators

Harbour decomposes grammatical number into three features acting on a region of a
join-semilattice of individuals. `[±atomic]` keeps the region's atoms or the rest, `[±minimal]`
its minimal elements or the rest, and `[±additive]` the elements whose join with any element of a
subregion stays in it. Features compose by application, so the dual is `[+minimal]` applied to
`[−atomic]`, and the trial `[+minimal]` applied to `[−minimal]` applied to `[−atomic]`. Which
bundle a value names depends on the number system: the plural of English is `[−atomic]`, that of
a language with a dual `[−atomic, −minimal]`. The systems a parameter setting generates, and the
cells of their bundles, are computed in `Studies/Harbour2014.lean`.

## Main definitions

* `Number.Feature.restrict`: the region a valued feature selects from a region.
* `Number.additiveIn`: the `[+additive]` elements of a subregion.

## Main results

* `Number.additive_subregion_is_cum`: the `[+additive]` elements form a cumulative predicate.
* `Number.singular_subset_minimal`: in a region without the null individual an atom is minimal,
  so `[+atomic]` entails `[+minimal]`.
* `Number.atomize_eq_of_atoms`: `[+minimal]` applied to a region of atoms changes nothing.
* `Number.not_restrict_minimal_false_atomize`: `[−minimal]` applied after `[+minimal]` is empty.

## Implementation notes

Harbour presupposes that the element lies in the region (`[±minimal]`) and in the subregion
(`[±additive]`); here these are conjuncts. Minimality is mathlib's `Minimal`, exposed as
`Mereology.atomize`. With a null individual in the region an atom has a proper part, so
`[+atomic]` no longer entails `[+minimal]`; Martí's revision of `[±minimal]` for that case, which
counts only parts of nonzero numerosity, is not modelled. `[−atomic]` gives the exclusive plural.
Whether the inclusive reading in downward-entailing contexts is a second meaning or an implicature
is open: Martí argues for the former within Harbour's typology, an inclusive-only plural lacking the
`[−atomic]` that duals and paucals are built on, and the experiments of Tieu, Bill, Romoli and Crain
favour the latter (`Studies/TieuEtAl2020.lean`). `Number.dom` states the inclusive-only reading of
a bundle, and competition recovers these regions from it for the singular and plural alone
(`Number.strengthen_plural`). The operators apply to events as well as individuals.

## References

* [harbour-2014] (9) and (10), p. 195; (20) and (21), p. 202; (30), p. 210
* [marti-2020a]
* [marti-2020b] pp. 3:30–3:31
* [marti-2022] (8) and (9), pp. 217–218; (40), p. 224
* [tieu-etal-2020]
* [link-1983]
-/

@[expose] public section

namespace Number

open Mereology (Atom CUM atomize)

variable {D : Type*}

section Additive

variable [SemilatticeSup D]

/-- `x` is additive in the region `Q` if `Q x` and `Q (x ⊔ y)` for every `y` with `Q y`, Harbour's
`[+additive]`. -/
def additiveIn (Q : D → Prop) (x : D) : Prop :=
  Q x ∧ ∀ y, Q y → Q (x ⊔ y)

theorem additiveIn_sup {Q : D → Prop} {x y : D} (hx : additiveIn Q x) (hy : additiveIn Q y) :
    additiveIn Q (x ⊔ y) := by
  refine ⟨hx.2 y hy.1, fun z hz => ?_⟩
  rw [sup_assoc]
  exact hx.2 (y ⊔ z) (hy.2 z hz)

/-- The additive elements of a region form a cumulative predicate. -/
theorem additive_subregion_is_cum (Q : D → Prop) : CUM (additiveIn Q) :=
  fun _ hx _ hy => additiveIn_sup hx hy

instance {Q : D → Prop} [Fintype D] [DecidablePred Q] (x : D) : Decidable (additiveIn Q x) :=
  decidable_of_iff (Q x ∧ ∀ y, Q y → Q (x ⊔ y)) Iff.rfl

end Additive

variable [PartialOrder D]

/-- The region a valued feature selects from the region `P`: `[+atomic]` its atoms and
`[−atomic]` the rest, `[+minimal]` its minimal elements and `[−minimal]` the rest. `[±additive]`
cuts a region at a height the region does not fix, and leaves it. -/
def Feature.restrict : Feature → Bool → (D → Prop) → D → Prop
  | .atomic, true, P => fun x ↦ P x ∧ Atom x
  | .atomic, false, P => fun x ↦ P x ∧ ¬ Atom x
  | .minimal, true, P => atomize P
  | .minimal, false, P => fun x ↦ P x ∧ ¬ atomize P x
  | .additive, _, P => P

theorem Feature.restrict_le (f : Feature) (v : Bool) (P : D → Prop) : f.restrict v P ≤ P :=
  match f, v with
  | .atomic, true | .atomic, false | .minimal, true | .minimal, false => fun _ h ↦ h.1
  | .additive, _ => le_rfl

/-- The minimal elements of a region of minimal elements are all of them, so
`(−minimal(+minimal(P)))` is empty. -/
theorem not_restrict_minimal_false_atomize (P : D → Prop) (x : D) :
    ¬ Feature.restrict .minimal false (atomize P) x :=
  fun h ↦ h.2 ⟨h.1, fun _ hy hyx ↦ h.1.2 hy.1 hyx⟩

/-- An atom of a region excluding the null individual is minimal in it, so
`[+atomic]` entails `[+minimal]`. -/
theorem singular_subset_minimal {P : D → Prop} (hP : ∀ y, P y → ¬ IsBot y) {x : D}
    (hx : Feature.restrict .atomic true P x) : atomize P x :=
  ⟨hx.1, fun _ hy hle => hx.2.2 (hP _ hy) hle⟩

/-- Over a region of atoms `[+minimal]` selects everything, so `(+minimal(+atomic(P)))` is
`(+atomic(P))`, the singular. -/
theorem atomize_eq_of_atoms {P : D → Prop} (hAll : ∀ x, P x → Atom x) : atomize P = P :=
  funext fun x => propext ⟨fun h => h.1, fun hPx =>
    singular_subset_minimal (fun y hy => (hAll y hy).not_isBot) ⟨hPx, hAll x hPx⟩⟩

end Number
