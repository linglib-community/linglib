/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Anaphora.Basic
public import Linglib.Syntax.Minimalist.Clause.Spine

/-!
# Ellipsis

Merchant's [E] feature on a head of a spine instructs the phonology not to pronounce the head's
complement. Each kind of ellipsis is an [E]
feature on a head: VP-ellipsis puts it on Voice and deletes vP, sluicing puts it on C and deletes
TP, and v-stranding VP-ellipsis puts it on v and deletes VP alone. A site of a spine is a head or
the adjunction site of the phrase a head projects. [E] deletes the heads of its complement and the
adjuncts of the phrases properly inside it, so that the adjuncts of the phrase just below the
[E]-bearing head survive. A site outside the deletion domain survives and is invisible to the
identity condition, so a mismatch in a feature its head bears is tolerated. Lowering [E] shrinks the
domain, so whatever a higher ellipsis tolerates a lower one tolerates too, which is Sailor's
generalization, and a domain containing a head contains every head below it, so an ellipsis
tolerating a mismatch in a head tolerates one in any head above. The two readings of *again* fix the
position of [E]. [E]-deletion is one model of Hankamer and Sag's depth: the null sites of a spine
are the complements [E] silences and the null pro-forms.

## Main definitions

* `Minimalist.ClauseSpine.Site`: a head of a spine, or the adjunction site of the phrase it
  projects.
* `Minimalist.ClauseSpine.Deletes`: the sites [E] on a head deletes.
* `Minimalist.Ellipsis`: an [E] feature on a head of a spine, with
  `Minimalist.Ellipsis.sluicing`, `Minimalist.Ellipsis.vpEllipsis`,
  `Minimalist.Ellipsis.vStrandingVPE` on `Minimalist.Ellipsis.clausalSpine`, and
  `Minimalist.Ellipsis.nPEllipsis` on `Minimalist.Ellipsis.nominalSpine`.
* `Minimalist.Ellipsis.Mismatch`: the dimensions in which an elided phrase may differ from its
  antecedent, each regulated by a head of the spine.
* `Minimalist.AgainReading`: the two readings of *again* and their adjunction sites.
* `Minimalist.NullSite`: a null site of a spine, an [E] deletion domain or a null pro-form, with
  its `Anaphor.DepthModel` instance.

## Main results

* `Minimalist.ClauseSpine.not_deletes_head_self`: the [E]-bearing head survives its own ellipsis,
  the core of X-stranding.
* `Minimalist.ClauseSpine.Deletes.of_mem_below`, `Minimalist.Ellipsis.Tolerates.of_mem_below`:
  Sailor's generalization, what [E] on a head deletes [E] on any higher head deletes too.
* `Minimalist.Ellipsis.eq_vpEllipsis_iff`, `Minimalist.Ellipsis.eq_vStrandingVPE_iff`: the *again*
  test, which places [E] on Voice or on v.
* `Minimalist.NullSite.not_silences_ePosition`: the head bearing [E] lies outside the site it
  silences.

## Implementation notes

The adjunction site of a phrase lies below the head that selects the phrase but outside that head's
complement, so restitutive *again*, adjoined to VP, survives v-stranding VP-ellipsis while V does
not, and prenominal modifiers, adjoined to NP, survive [E] on n. A root adjoined to a head, as a
manner root adjoins to v, is part of that head and shares its site. A null
site built from [E] carries a site of its deletion domain, since a head at the bottom of a spine
has no complement to silence; that witness is what the surface condition of `Anaphor.DepthModel`
asks for.

## TODO

* The licensing condition on [E], that the elided complement be given, and the identity condition
  between an elided phrase and its antecedent; `Mismatch` records only the dimensions such a
  condition could ignore.

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

variable {s : ClauseSpine} {p q d : Cat} {x : Site}

/-- [E] on `p` deletes the heads of its complement, and the adjuncts of a phrase that some head of
the complement takes in its own complement, so that the adjuncts of the phrase just below `p`
survive. -/
def Deletes (s : ClauseSpine) (p : Cat) : Site → Prop
  | .head d => d ∈ s.below p
  | .adjunct d => ∃ e ∈ s.below p, d ∈ s.below e

instance (s : ClauseSpine) (p : Cat) : ∀ x, Decidable (s.Deletes p x)
  | .head _ => inferInstanceAs (Decidable (_ ∈ _))
  | .adjunct _ => inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The [E]-bearing head survives its own ellipsis, which is the core of X-stranding: a head that
has moved to the [E]-bearing position is pronounced while its base position is deleted. -/
theorem not_deletes_head_self (s : ClauseSpine) (p : Cat) : ¬ s.Deletes p (.head p) :=
  s.notMem_below_self p

/-- Sailor's generalization. What [E] on a head deletes, [E] on any head above it deletes too. -/
theorem Deletes.of_mem_below (h : s.Deletes q x) (hq : q ∈ s.below p) : s.Deletes p x := by
  have hpre := (s.below_prefix hq).subset
  cases x with
  | head d => exact hpre h
  | adjunct d =>
    obtain ⟨e, he, hd⟩ := h
    exact ⟨e, hpre he, hd⟩

/-- A deletion domain is closed downward: [E] deleting a head deletes every head below it. -/
theorem Deletes.head_of_mem_below (h : s.Deletes p (.head q)) (hd : d ∈ s.below q) :
    s.Deletes p (.head d) :=
  (s.below_prefix h).subset hd

end ClauseSpine

/-! ### Ellipsis types -/

/-- An ellipsis is an [E] feature on a head of the spine `s`; its deletion domain is that head's
complement. -/
structure Ellipsis (s : ClauseSpine) where
  /-- The head carrying [E]. -/
  ePosition : Cat
  deriving DecidableEq, Repr

namespace Ellipsis

/-- The clausal spine that ellipsis distinguishes, V, v, Voice, T and C. -/
def clausalSpine : ClauseSpine := ⟨[.V, .v, .Voice, .T, .C]⟩

/-- The nominal spine, N, the categorizer n, Num and D. -/
def nominalSpine : ClauseSpine := ⟨[.N, .n, .Num, .D]⟩

section Spine

variable {s : ClauseSpine} {e e' : Ellipsis s} {x : ClauseSpine.Site}

/-- `e.Deletes x` when the site `x` lies in the deletion domain of `e`. -/
def Deletes (e : Ellipsis s) (x : ClauseSpine.Site) : Prop := s.Deletes e.ePosition x

instance : Decidable (e.Deletes x) := inferInstanceAs (Decidable (s.Deletes _ _))

/-- `e.Spares x` when the site `x` is external to `e` and survives it. -/
def Spares (e : Ellipsis s) (x : ClauseSpine.Site) : Prop := ¬ e.Deletes x

instance : Decidable (e.Spares x) := inferInstanceAs (Decidable (¬ _))

theorem spares_ePosition (e : Ellipsis s) : e.Spares (.head e.ePosition) :=
  s.not_deletes_head_self _

/-- Sailor's generalization. What an ellipsis spares, every ellipsis whose [E] sits lower
spares. -/
theorem Spares.of_mem_below (h : e.Spares x) (hle : e'.ePosition ∈ s.below e.ePosition) :
    e'.Spares x :=
  fun h' ↦ h (h'.of_mem_below hle)

end Spine

/-- Sluicing puts [E] on C and deletes TP. -/
def sluicing : Ellipsis clausalSpine := ⟨.C⟩

/-- VP-ellipsis puts [E] on Voice and deletes vP, so that Voice is external to the ellipsis. -/
def vpEllipsis : Ellipsis clausalSpine := ⟨.Voice⟩

/-- v-stranding VP-ellipsis puts [E] on v and deletes VP alone, stranding the light verb. -/
def vStrandingVPE : Ellipsis clausalSpine := ⟨.v⟩

/-- nP-ellipsis puts [E] on Num and deletes nP, the configuration [liptak-saab-2014] find in
Spanish: the noun, the categorizer and prenominal modifiers are all deleted. -/
def nPEllipsis : Ellipsis nominalSpine := ⟨.Num⟩

/-! ### Mismatches -/

/-- A dimension in which an elided phrase may differ from its antecedent, each regulated by a head
of the spine: voice by Voice, the causative, dative, prepositional and middle alternations by
flavours of v, and the lexical verb by V. -/
inductive Mismatch
  | voice
  | transitivity
  | dative
  | prepositional
  | middle
  | lexical
  deriving DecidableEq, Repr

/-- The head that regulates each dimension. -/
def Mismatch.head : Mismatch → Cat
  | .voice => .Voice
  | .transitivity | .dative | .prepositional | .middle => .v
  | .lexical => .V

variable {e e' : Ellipsis clausalSpine}

/-- `e.Tolerates m` when the head regulating `m` is external to `e`, so that a mismatch in `m`
is invisible to the identity condition. -/
def Tolerates (e : Ellipsis clausalSpine) (m : Mismatch) : Prop := e.Spares (.head m.head)

instance (e : Ellipsis clausalSpine) (m : Mismatch) : Decidable (e.Tolerates m) :=
  inferInstanceAs (Decidable (e.Spares _))

/-- Sailor's generalization. A mismatch tolerated by an ellipsis is tolerated by every ellipsis
whose [E] sits lower. -/
theorem Tolerates.of_mem_below {m : Mismatch} (h : e.Tolerates m)
    (hle : e'.ePosition ∈ clausalSpine.below e.ePosition) : e'.Tolerates m :=
  Spares.of_mem_below h hle

/-- A mismatch tolerated by an ellipsis is tolerated in every head above the one regulating it,
since a deletion domain containing the higher head contains the lower. -/
theorem Tolerates.of_head_mem_below {m m' : Mismatch} (h : e.Tolerates m)
    (hm : m.head ∈ clausalSpine.below m'.head) : e.Tolerates m' :=
  fun h' ↦ h (ClauseSpine.Deletes.head_of_mem_below h' hm)

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

/-- The *again* test. An ellipsis sparing repetitive *again* and deleting restitutive *again*, as
English VP-ellipsis does, has [E] on Voice. -/
theorem eq_vpEllipsis_iff (e : Ellipsis clausalSpine) :
    e = vpEllipsis ↔
      e.Spares AgainReading.repetitive.site ∧ e.Deletes AgainReading.restitutive.site := by
  obtain ⟨p⟩ := e
  cases p <;> decide

/-- The *again* test. An ellipsis deleting V and sparing restitutive *again* has [E] on v. -/
theorem eq_vStrandingVPE_iff (e : Ellipsis clausalSpine) :
    e = vStrandingVPE ↔ e.Deletes (.head .V) ∧ e.Spares AgainReading.restitutive.site := by
  obtain ⟨p⟩ := e
  cases p <;> decide

end Ellipsis

end Minimalist
