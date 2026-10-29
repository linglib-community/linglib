/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Anaphora.Basic
public import Linglib.Syntax.Minimalist.Clause.Spine
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Basic

/-!
# Ellipsis

Merchant's [E] feature on a head of a spine instructs the phonology not to pronounce the head's
complement. The sites of a spine are its heads and the adjunction sites of the phrases they project,
and they interleave in one linear order: V, the adjunction site of VP, v, that of vP, Voice, and so
on up. [E] on a head deletes an initial segment of that order, everything below the adjunction site
of the head's complement, so that the head itself and the adjuncts of its complement survive:
VP-ellipsis puts [E] on Voice and deletes vP, sluicing puts it on C and deletes TP, and v-stranding
VP-ellipsis puts it on v and deletes VP alone. Ordering ellipses by the height of [E], the deletion
domain is monotone, which is Sailor's generalization. The identity condition requires the elided
phrase to agree with its antecedent at every deleted site, so a mismatch at a site is tolerated
exactly when the ellipsis spares it. The two readings of *again* place [E] on Voice or on v.
[E]-deletion is one model of Hankamer and Sag's depth: the null sites of a spine are the
complements [E] silences and the null pro-forms.

## Main definitions

* `Minimalist.ClauseSpine.Site`, `Minimalist.ClauseSpine.rank`: the sites of a spine and their
  interleaved order.
* `Minimalist.ClauseSpine.Deletes`: the initial segment of sites [E] on a head deletes.
* `Minimalist.Ellipsis`: an [E] feature on a head of a spine, ordered by height, with its
  `Minimalist.Ellipsis.domain` and the identity condition `Minimalist.Ellipsis.Identical`.
* `Minimalist.AgainReading`: the two readings of *again* and their adjunction sites.
* `Minimalist.NullSite`: a null site of a spine, an [E] deletion domain or a null pro-form, with
  its `Anaphor.DepthModel` instance.

## Main results

* `Minimalist.Ellipsis.domain_mono`: Sailor's generalization, the deletion domain grows with the
  height of [E].
* `Minimalist.Ellipsis.identical_update_iff`: a mismatch at a single site is tolerated exactly
  when the ellipsis spares that site.
* `Minimalist.Ellipsis.eq_vpEllipsis_iff`, `Minimalist.Ellipsis.eq_vStrandingVPE_iff`,
  `Minimalist.Ellipsis.eq_vpEllipsis_iff_spares_voice`: the *again* test and the voice test, which
  place [E] on Voice or on v.

## Implementation notes

A site's rank is twice the index of its head on the spine, plus one for an adjunction site, so the
adjunction site of a phrase lies above its head and below the head that selects it, and an adjunct
of the complement of [E] survives the ellipsis as restitutive *again* survives [E] on v. A root
adjoined to a head, as a manner root adjoins to v, is part of that head and shares its site. A head
the spine lacks is ranked above every site of the spine and so is never deleted. A null site built
from [E] carries a site of its deletion domain, since a head at the bottom of a spine has no
complement to silence; that witness is what the surface condition of `Anaphor.DepthModel` asks
for.

## TODO

* The licensing condition on [E], that the elided complement be given, and the semantic identity
  condition, Merchant's e-GIVENness.

## References

* [merchant-2001]
* [merchant-2013]
* [kalyakin-2026]
* [sailor-2014]
* [liptak-saab-2014]
* [benz-salzmann-2025]
* [hankamer-sag-1976]
-/

@[expose] public section

namespace Minimalist

namespace ClauseSpine

/-- A site of a spine is a head, or the adjunction site of the phrase a head projects, where
adjuncts such as *again* and prenominal modifiers attach. -/
inductive Site
  | head (c : Cat)
  | adjunct (c : Cat)
  deriving DecidableEq, Repr

variable {s : ClauseSpine} {p q : Cat} {x y : Site}

/-- The rank of a site in the order of a spine's sites: the head of index `i` at `2 * i`, the
adjunction site of the phrase it projects at `2 * i + 1`. -/
def rank (s : ClauseSpine) : Site → ℕ
  | .head c => 2 * s.heads.idxOf c
  | .adjunct c => 2 * s.heads.idxOf c + 1

/-- [E] on `p` deletes the sites below the adjunction site of its complement: the heads below `p`
and the adjunction sites of the phrases inside its complement. -/
def Deletes (s : ClauseSpine) (p : Cat) (x : Site) : Prop := s.rank x + 1 < s.rank (.head p)

instance (s : ClauseSpine) (p : Cat) (x : Site) : Decidable (s.Deletes p x) :=
  inferInstanceAs (Decidable (_ < _))

/-- The [E]-bearing head survives its own ellipsis, which is the core of X-stranding: a head that
has moved to the [E]-bearing position is pronounced while its base position is deleted. -/
theorem not_deletes_head_self (s : ClauseSpine) (p : Cat) : ¬ s.Deletes p (.head p) := by
  simp [Deletes]

/-- A deletion domain is closed downward. -/
theorem Deletes.of_rank_le (h : s.Deletes p x) (hy : s.rank y ≤ s.rank x) : s.Deletes p y := by
  unfold Deletes at *
  omega

/-- What [E] on a head deletes, [E] on any head above it deletes too. -/
theorem Deletes.of_rank_head_le (h : s.Deletes q x)
    (hq : s.rank (.head q) ≤ s.rank (.head p)) : s.Deletes p x := by
  unfold Deletes at *
  omega

end ClauseSpine

/-! ### Ellipses -/

/-- An ellipsis is an [E] feature on a head of the spine `s`; its deletion domain is that head's
complement. -/
@[ext]
structure Ellipsis (s : ClauseSpine) where
  /-- The head carrying [E]. -/
  ePosition : Cat
  mem : ePosition ∈ s

namespace Ellipsis

open ClauseSpine

variable {s : ClauseSpine} {e e' : Ellipsis s} {x : Site}

/-- The index on the spine of the head carrying [E]. -/
def height (e : Ellipsis s) : ℕ := s.heads.idxOf e.ePosition

theorem height_injective : Function.Injective (height : Ellipsis s → ℕ) := fun e _ h ↦
  Ellipsis.ext ((List.idxOf_inj e.mem).1 h)

/-- Ellipses are ordered by the height of [E]. -/
instance : LinearOrder (Ellipsis s) := LinearOrder.lift' height height_injective

theorem le_iff_height_le : e ≤ e' ↔ e.height ≤ e'.height := Iff.rfl

theorem eq_iff_height_eq : e = e' ↔ e.height = e'.height := height_injective.eq_iff.symm

/-- `e.Deletes x` when the site `x` lies in the deletion domain of `e`. -/
def Deletes (e : Ellipsis s) (x : Site) : Prop := s.Deletes e.ePosition x

instance : Decidable (e.Deletes x) := inferInstanceAs (Decidable (s.Deletes _ _))

theorem deletes_iff : e.Deletes x ↔ s.rank x + 1 < 2 * e.height := Iff.rfl

theorem Deletes.of_rank_le {y : Site} (h : e.Deletes x) (hy : s.rank y ≤ s.rank x) :
    e.Deletes y :=
  ClauseSpine.Deletes.of_rank_le h hy

/-- `e.Spares x` when the site `x` is external to `e` and survives it. -/
def Spares (e : Ellipsis s) (x : Site) : Prop := ¬ e.Deletes x

instance : Decidable (e.Spares x) := inferInstanceAs (Decidable (¬ _))

theorem spares_ePosition (e : Ellipsis s) : e.Spares (.head e.ePosition) :=
  s.not_deletes_head_self _

/-- The deletion domain of `e`, the sites it leaves unpronounced. -/
def domain (e : Ellipsis s) : Set Site := {x | e.Deletes x}

@[simp] theorem mem_domain : x ∈ e.domain ↔ e.Deletes x := Iff.rfl

/-- Sailor's generalization. The deletion domain grows with the height of [E], so what an ellipsis
spares every lower ellipsis spares. -/
theorem domain_mono : Monotone (domain : Ellipsis s → Set Site) := fun _ _ h _ hx ↦ by
  rw [le_iff_height_le] at h
  simp only [mem_domain, deletes_iff] at *
  omega

theorem Spares.of_le (h : e.Spares x) (hle : e' ≤ e) : e'.Spares x :=
  fun h' ↦ h (domain_mono hle h')

/-! ### Identity -/

/-- The identity condition: the antecedent and the elided phrase, each an assignment of content to
the sites of the spine, agree at every site the ellipsis deletes. -/
def Identical {α : Type*} (e : Ellipsis s) (a t : Site → α) : Prop := Set.EqOn a t e.domain

theorem Identical.of_le {α : Type*} {a t : Site → α} (h : e.Identical a t) (hle : e' ≤ e) :
    e'.Identical a t :=
  h.mono (domain_mono hle)

/-- A mismatch at a single site is tolerated exactly when the ellipsis spares that site. -/
theorem identical_update_iff {α : Type*} [DecidableEq α] (a : Site → α) (x : Site) (v : α) :
    e.Identical a (Function.update a x v) ↔ a x = v ∨ e.Spares x := by
  refine ⟨fun h ↦ or_iff_not_imp_right.2 fun hx ↦ ?_, ?_⟩
  · simpa using h (not_not.1 hx)
  · rintro (rfl | hx) y hy
    · rw [Function.update_eq_self]
    · refine (Function.update_of_ne (fun hyx : y = x ↦ hx ?_) _ _).symm
      rw [← hyx]
      exact hy

end Ellipsis

/-! ### Ellipses of the clausal and nominal spines -/

namespace Ellipsis

/-- The clausal spine that ellipsis distinguishes, V, v, Voice, T and C. -/
def clausalSpine : ClauseSpine := ⟨[.V, .v, .Voice, .T, .C]⟩

/-- The nominal spine, N, the categorizer n, Num and D. -/
def nominalSpine : ClauseSpine := ⟨[.N, .n, .Num, .D]⟩

/-- Sluicing puts [E] on C and deletes TP. -/
def sluicing : Ellipsis clausalSpine := ⟨.C, by decide⟩

/-- VP-ellipsis puts [E] on Voice and deletes vP, so that Voice is external to the ellipsis. -/
def vpEllipsis : Ellipsis clausalSpine := ⟨.Voice, by decide⟩

/-- v-stranding VP-ellipsis puts [E] on v and deletes VP alone, stranding the light verb. -/
def vStrandingVPE : Ellipsis clausalSpine := ⟨.v, by decide⟩

/-- nP-ellipsis puts [E] on Num and deletes nP, the configuration [liptak-saab-2014] find in
Spanish: the noun, the categorizer and prenominal modifiers are all deleted. -/
def nPEllipsis : Ellipsis nominalSpine := ⟨.Num, by decide⟩

end Ellipsis

/-! ### Null sites and depth -/

/-- A null site of a spine: the complement an [E]-bearing head leaves unpronounced, which must
contain some site, or a null pro-form, a head without a complement, such as *pro* or an empty
noun. -/
inductive NullSite (s : ClauseSpine) where
  | elided (e : Ellipsis s) (h : ∃ x, e.Deletes x)
  | proform (x : ClauseSpine.Site)

namespace NullSite

variable {s : ClauseSpine}

/-- [E]-deletion yields a surface anaphor, and a null pro-form a deep one. -/
def depth : NullSite s → Anaphor.Depth
  | .elided .. => .surface
  | .proform _ => .deep

/-- The sites a null site leaves unpronounced, the deletion domain of an [E]-bearing head and none
for a pro-form. -/
def Silences : NullSite s → ClauseSpine.Site → Prop
  | .elided e _, x => e.Deletes x
  | .proform _, _ => False

/-- [E]-deletion realizes Hankamer and Sag's depth: an [E] site silences its complement, and a
null pro-form silences nothing. -/
instance : Anaphor.DepthModel (NullSite s) ClauseSpine.Site where
  depth := depth
  Silences := Silences
  exists_silences_of_surface
    | .elided _ h, _ => h
    | .proform _, h => nomatch h
  not_silences_of_deep
    | .elided .., _, h => nomatch h
    | .proform _, _, _ => id

instance : ∀ (n : NullSite s) (x : ClauseSpine.Site), Decidable (n.Silences x)
  | .elided e _, _ => inferInstanceAs (Decidable (e.Deletes _))
  | .proform _, _ => inferInstanceAs (Decidable False)

@[simp] theorem silences_elided {e : Ellipsis s} {h : ∃ x, e.Deletes x} {x : ClauseSpine.Site} :
    (elided e h).Silences x ↔ e.Deletes x := .rfl

/-- The head that bears [E] lies outside the site it silences, which is what lets a head moved
there strand. -/
theorem not_silences_ePosition {e : Ellipsis s} (h : ∃ x, e.Deletes x) :
    ¬ (elided e h).Silences (.head e.ePosition) :=
  e.spares_ePosition

end NullSite

/-! ### The two readings of *again* -/

/-- The two readings of *again* and their adjunction sites. Repetitive *again* adjoins to vP and
presupposes an earlier event, restitutive *again* adjoins to VP and presupposes an earlier result
state. -/
inductive AgainReading
  | repetitive
  | restitutive
  deriving DecidableEq, Repr

/-- The adjunction site of each reading. -/
def AgainReading.site : AgainReading → ClauseSpine.Site
  | .repetitive => .adjunct .v
  | .restitutive => .adjunct .V

namespace Ellipsis

variable {e : Ellipsis clausalSpine}

/-- The *again* test. An ellipsis sparing repetitive *again* and deleting restitutive *again*, as
English VP-ellipsis does, has [E] on Voice. -/
theorem eq_vpEllipsis_iff :
    e = vpEllipsis ↔
      e.Spares AgainReading.repetitive.site ∧ e.Deletes AgainReading.restitutive.site := by
  rw [eq_iff_height_eq]
  simp only [Spares, deletes_iff, AgainReading.site, ClauseSpine.rank]
  have : vpEllipsis.height = 2 := rfl
  have : clausalSpine.heads.idxOf Cat.v = 1 := rfl
  have : clausalSpine.heads.idxOf Cat.V = 0 := rfl
  omega

/-- The voice test. An ellipsis sparing Voice and deleting v, as English VP-ellipsis does in
tolerating voice mismatches and no others, has [E] on Voice. -/
theorem eq_vpEllipsis_iff_spares_voice :
    e = vpEllipsis ↔ e.Spares (.head .Voice) ∧ e.Deletes (.head .v) := by
  rw [eq_iff_height_eq]
  simp only [Spares, deletes_iff, ClauseSpine.rank]
  have : vpEllipsis.height = 2 := rfl
  have : clausalSpine.heads.idxOf Cat.Voice = 2 := rfl
  have : clausalSpine.heads.idxOf Cat.v = 1 := rfl
  omega

/-- The *again* test. An ellipsis deleting V and sparing restitutive *again* has [E] on v. -/
theorem eq_vStrandingVPE_iff :
    e = vStrandingVPE ↔ e.Deletes (.head .V) ∧ e.Spares AgainReading.restitutive.site := by
  rw [eq_iff_height_eq]
  simp only [Spares, deletes_iff, AgainReading.site, ClauseSpine.rank]
  have : vStrandingVPE.height = 1 := rfl
  have : clausalSpine.heads.idxOf Cat.V = 0 := rfl
  omega

end Ellipsis

end Minimalist
