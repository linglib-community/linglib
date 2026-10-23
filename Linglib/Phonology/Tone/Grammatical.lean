/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Edge
public import Linglib.Phonology.Tone.Basic

/-!
# Grammatical tone

Grammatical tone is a tonological operation restricted to a specific morpheme or construction,
or a natural class of them, and not attributable to the general tonal phonology. This file
gives Rolle's vocabulary for it over strings of tone-bearing units: the *grammatical tune* that
covaries with the construction, anchored at an edge of its host, and the four *dominance
effects* by which a trigger's tune interacts with the tones of its target-host. A dominant
trigger imposes its pattern whatever the target's tones, a recessive one only on an unvalued
target, and a neutral one leaves the target to the general phonology. Dominance is the
neutralisation of the target's valued–unvalued contrast, which Rolle calls transparadigmatic
uniformity, and `Dominance.isDominant_iff_uniform` derives his classification from it.

## Main definitions

* `TBU`, `TBU.IsValued`: a tone-bearing unit with its tonal root node, valued when the node
  is specified.
* `Tune`, `Tune.realize`: a grammatical tune, a melody anchored at an edge of the host, and
  its realisation over a number of units: one tone per unit from the anchored edge, the last
  tone reached spreading over the remainder.
* `overwrite`, `unvalue`: replacement of a host's tones by a tune, and their deletion.
* `Uniform`: transparadigmatic uniformity of an operation on hosts.
* `Dominance`, `Dominance.apply`: Rolle's replacive-dominant, subtractive-dominant,
  recessive, and neutral triggers, and the automatic operation each performs on its
  target-host.

## Main results

* `overwrite_unvalue`: a host and its unvalued projection are overwritten alike.
* `Dominance.isDominant_iff_uniform`: a trigger is dominant exactly when its operation is
  uniform across targets of the same segments.

## Implementation notes

A tone-bearing unit carries one root node, so contours are not represented and a tune longer
than its host is truncated at the anchored edge. The valuation window is coextensive with the
host, Rolle's default; local windows are not modelled. The neutral trigger's tune floats and
its docking is left to the general phonology, so its automatic operation is the identity on
the host. Which edge a tune anchors at is a property of the construction:
Akinbo and Fwangwar's M-H verbaliser anchors right, putting H on the final unit and M on the
rest.

## References

* [rolle-2018]
* [lionnet-mcpherson-rolle-2022]
* [inkelas-1998]
* [kiparsky-halle-1977]
* [hyman-2018a]
* [clements-goldsmith-1984]
* [akinbo-fwangwar-2026]
-/

@[expose] public section

namespace Tone

/-! ### Tone-bearing units -/

/-- A tone-bearing unit is segmental content of type `S`, a syllable or a mora, carrying one
tonal root node. -/
structure TBU (S : Type*) where
  seg : S
  tone : TRN
  deriving DecidableEq, Repr

namespace TBU

variable {S : Type*}

/-- A unit is valued when its root node is specified and unvalued when it is a free unit
([rolle-2018] Table 1, after [clements-goldsmith-1984]). -/
def IsValued (τ : TBU S) : Prop := τ.tone ≠ .empty

instance : DecidablePred (IsValued (S := S)) := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

end TBU

/-! ### Grammatical tunes -/

/-- A grammatical tune ([rolle-2018] (1a)) is the tone sequence that covaries with the
construction, anchored at an edge of its host. -/
structure Tune where
  melody : List TRN
  anchor : Edge
  deriving DecidableEq, Repr

namespace Tune

/-- A melody over `n` units from the left puts one tone on each unit, the last tone spreading
over the remaining units and an empty melody leaving them unvalued. -/
def realizeLeft : ℕ → List TRN → List TRN
  | 0, _ => []
  | n + 1, [] => List.replicate (n + 1) .empty
  | n + 1, [t] => t :: realizeLeft n [t]
  | n + 1, t :: t' :: ts => t :: realizeLeft n (t' :: ts)

/-- The tune realised over `n` units puts one tone on each unit from the anchored edge, the last
tone reached spreading over the remainder. -/
def realize (u : Tune) (n : ℕ) : List TRN :=
  u.anchor.orient (realizeLeft n (u.anchor.orient u.melody))

@[simp] theorem length_realizeLeft (n : ℕ) (m : List TRN) : (realizeLeft n m).length = n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    match m with
    | [] => simp [realizeLeft]
    | [t] => simp [realizeLeft, ih]
    | t :: t' :: ts => simp [realizeLeft, ih]

@[simp] theorem length_realize (u : Tune) (n : ℕ) : (u.realize n).length = n := by
  obtain ⟨m, e⟩ := u
  cases e <;> simp [realize]

theorem realizeLeft_singleton (n : ℕ) (t : TRN) : realizeLeft n [t] = List.replicate n t := by
  induction n with
  | zero => rfl
  | succ n ih => simp [realizeLeft, ih, List.replicate_succ]

@[simp] theorem realize_singleton (t : TRN) (e : Edge) (n : ℕ) :
    realize ⟨[t], e⟩ n = List.replicate n t := by
  cases e <;> simp [realize, realizeLeft_singleton]

theorem realize_pair_right (t₁ t₂ : TRN) (n : ℕ) :
    realize ⟨[t₁, t₂], .right⟩ (n + 1) = List.replicate n t₁ ++ [t₂] := by
  simp [realize, realizeLeft, realizeLeft_singleton]

end Tune

/-! ### Operations on a target-host -/

variable {S : Type*}

/-- The host with its tonal tier replaced. -/
def withTier (host : List (TBU S)) (tier : List TRN) : List (TBU S) :=
  host.zipWith (fun τ t ↦ { τ with tone := t }) tier

theorem withTier_eq_of_map_seg_eq : ∀ {h h' : List (TBU S)} (tier : List TRN),
    h.map TBU.seg = h'.map TBU.seg → withTier h tier = withTier h' tier
  | [], [], _, _ => rfl
  | [], _ :: _, _, hs | _ :: _, [], _, hs => by simp at hs
  | τ :: h, τ' :: h', [], _ => rfl
  | τ :: h, τ' :: h', t :: tier, hs => by
    simp only [List.map_cons, List.cons.injEq] at hs
    simp only [withTier, List.zipWith_cons_cons, hs.1]
    exact congrArg _ (withTier_eq_of_map_seg_eq tier hs.2)

theorem map_seg_withTier : ∀ (h : List (TBU S)) (tier : List TRN), tier.length = h.length →
    (withTier h tier).map TBU.seg = h.map TBU.seg
  | [], _, _ => by simp [withTier]
  | _ :: _, [], hl => by simp at hl
  | τ :: h, t :: tier, hl => by
    simp only [withTier, List.zipWith_cons_cons, List.map_cons]
    exact congrArg _ (map_seg_withTier h tier (by simpa using hl))

theorem map_tone_withTier : ∀ (h : List (TBU S)) (tier : List TRN), tier.length = h.length →
    (withTier h tier).map TBU.tone = tier
  | [], [], _ => rfl
  | [], _ :: _, hl | _ :: _, [], hl => by simp at hl
  | τ :: h, t :: tier, hl => by
    simp only [withTier, List.zipWith_cons_cons, List.map_cons]
    exact congrArg _ (map_tone_withTier h tier (by simpa using hl))

/-- Replacement of the host's tones by the tune ([rolle-2018] Def 1) is the tune realised over
the host's units. -/
def overwrite (host : List (TBU S)) (u : Tune) : List (TBU S) :=
  withTier host (u.realize host.length)

/-- Deletion of the host's tones ([rolle-2018] Def 2) leaves every unit unvalued. -/
def unvalue (host : List (TBU S)) : List (TBU S) :=
  host.map fun τ ↦ { τ with tone := .empty }

@[simp] theorem overwrite_nil (u : Tune) : overwrite ([] : List (TBU S)) u = [] := rfl

@[simp] theorem map_seg_overwrite (host : List (TBU S)) (u : Tune) :
    (overwrite host u).map TBU.seg = host.map TBU.seg :=
  map_seg_withTier _ _ (Tune.length_realize _ _)

@[simp] theorem map_tone_overwrite (host : List (TBU S)) (u : Tune) :
    (overwrite host u).map TBU.tone = u.realize host.length :=
  map_tone_withTier _ _ (Tune.length_realize _ _)

@[simp] theorem length_overwrite (host : List (TBU S)) (u : Tune) :
    (overwrite host u).length = host.length := by
  have := congrArg List.length (map_seg_overwrite host u)
  simpa only [List.length_map] using this

theorem map_tone_overwrite_singleton (host : List (TBU S)) (t : TRN) (e : Edge) :
    (overwrite host ⟨[t], e⟩).map TBU.tone = host.map fun _ ↦ t := by
  rw [map_tone_overwrite, Tune.realize_singleton, List.map_const']

@[simp] theorem map_seg_unvalue (host : List (TBU S)) :
    (unvalue host).map TBU.seg = host.map TBU.seg := by
  simp [unvalue]

/-- An operation on target-hosts is transparadigmatically uniform ([rolle-2018] ch. 5) when it
gives the same output for hosts of the same segments, whatever their tones. -/
def Uniform (op : List (TBU S) → List (TBU S)) : Prop :=
  ∀ ⦃h h' : List (TBU S)⦄, h.map TBU.seg = h'.map TBU.seg → op h = op h'

theorem overwrite_eq_of_map_seg_eq {h h' : List (TBU S)} (hs : h.map TBU.seg = h'.map TBU.seg)
    (u : Tune) : overwrite h u = overwrite h' u := by
  have hl : h.length = h'.length := by simpa using congrArg List.length hs
  show withTier h (u.realize h.length) = withTier h' (u.realize h'.length)
  rw [hl, withTier_eq_of_map_seg_eq _ hs]

theorem uniform_overwrite (u : Tune) : Uniform (overwrite (S := S) · u) :=
  fun _ _ hs ↦ overwrite_eq_of_map_seg_eq hs u

theorem uniform_unvalue : Uniform (unvalue (S := S)) := fun h h' hs ↦ by
  have : ∀ l : List (TBU S), unvalue l = (l.map TBU.seg).map fun s ↦ ⟨s, .empty⟩ := fun l ↦ by
    simp [unvalue, List.map_map, Function.comp_def]
  rw [this, this, hs]

/-- Overwriting erases, in that a host and its unvalued projection are overwritten alike, which
is why a replacive trigger neutralises the target's tones. -/
@[simp] theorem overwrite_unvalue (host : List (TBU S)) (u : Tune) :
    overwrite (unvalue host) u = overwrite host u :=
  overwrite_eq_of_map_seg_eq (map_seg_unvalue host) u

/-! ### Dominance effects -/

/-- [rolle-2018]'s dominance effects, his four types of trigger (Defs 1–4, Table 2) by how the
trigger's tune interacts with the tonal value of its target-host. Dominance is a lexical
idiosyncrasy of the trigger, predictable neither from its segments and prosody nor from the
markedness of the tune nor from its position relative to the target ([inkelas-1998]); the
terms are those of the accentual morphology of [kiparsky-halle-1977]. -/
inductive Dominance where
  /-- A replacive-dominant trigger (Def 1) replaces the underlying tones within the valuation
  window by the tune, whether by a floating tone or by spreading from the sponsor. Valued and
  unvalued targets come out alike, an intentional neutralisation in [hyman-2018a]'s sense. -/
  | replacive
  /-- A subtractive-dominant trigger (Def 2) deletes the underlying tones within the valuation
  window, with no tune to revalue them; the surface tones are supplied later by default. -/
  | subtractive
  /-- The tune of a recessive non-dominant trigger (Def 3) does not apply to a target valued
  within the valuation window, so it docks only to unvalued targets, as in privative systems
  with one contrastive tone. -/
  | recessive
  /-- A neutral non-dominant trigger (Def 4) has neither automatic replacement or deletion nor
  automatic non-application; the tune concatenates with the target and the general phonology
  decides its docking. -/
  | neutral
  deriving DecidableEq, Repr

namespace Dominance

/-- The dominant types, which neutralise the target's valued–unvalued contrast. -/
def IsDominant (d : Dominance) : Prop := d = .replacive ∨ d = .subtractive

instance : DecidablePred IsDominant := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The automatic operation a trigger of each type performs on its target-host, the valuation
window being the whole host. The four are replacement by the tune, deletion, docking of the tune
only to a wholly unvalued host, and nothing. -/
def apply (d : Dominance) (u : Tune) (host : List (TBU S)) : List (TBU S) :=
  match d with
  | .replacive => overwrite host u
  | .subtractive => unvalue host
  | .recessive => if ∃ τ ∈ host, τ.IsValued then host else overwrite host u
  | .neutral => host

@[simp] theorem apply_replacive (u : Tune) (host : List (TBU S)) :
    replacive.apply u host = overwrite host u := rfl

@[simp] theorem apply_subtractive (u : Tune) (host : List (TBU S)) :
    subtractive.apply u host = unvalue host := rfl

@[simp] theorem apply_neutral (u : Tune) (host : List (TBU S)) : neutral.apply u host = host :=
  rfl

theorem apply_recessive_of_valued (u : Tune) {host : List (TBU S)}
    (h : ∃ τ ∈ host, τ.IsValued) : recessive.apply u host = host := by
  simp [apply, h]

theorem apply_recessive_of_unvalued (u : Tune) {host : List (TBU S)}
    (h : ∀ τ ∈ host, ¬ τ.IsValued) : recessive.apply u host = overwrite host u := by
  simp only [apply]
  rw [ite_eq_right]
  rintro ⟨τ, hτ, hv⟩
  exact h τ hτ hv

theorem uniform_apply_of_isDominant {d : Dominance} (hd : d.IsDominant) (u : Tune) :
    Uniform (d.apply (S := S) u) := by
  rcases hd with rfl | rfl
  · exact uniform_overwrite u
  · exact uniform_unvalue

/-- Dominance is transparadigmatic uniformity ([rolle-2018] ch. 5), in that a trigger is dominant
exactly when its operation gives the same output for every target of the same segments. -/
theorem isDominant_iff_uniform [Inhabited S] (d : Dominance) :
    d.IsDominant ↔ ∀ u : Tune, Uniform (d.apply (S := S) u) := by
  refine ⟨fun hd u ↦ uniform_apply_of_isDominant hd u, fun hu ↦ ?_⟩
  cases d with
  | replacive => exact Or.inl rfl
  | subtractive => exact Or.inr rfl
  | recessive =>
    have := hu ⟨[.H], .left⟩ (h := [⟨default, .L⟩]) (h' := [⟨default, .empty⟩]) rfl
    simp [apply, TBU.IsValued, overwrite, withTier, Tune.realize, Tune.realizeLeft,
      TRN.L, TRN.H, TRN.empty] at this
  | neutral =>
    have := hu ⟨[.H], .left⟩ (h := [⟨default, .L⟩]) (h' := [⟨default, .H⟩]) rfl
    simp [TRN.L, TRN.H] at this

end Dominance

end Tone
