module

public import Linglib.Morphology.Nanosyntax.SyntacticObject
public import Mathlib.Data.List.Monad

/-!
# Nanosyntax: the lexicalization algorithm

In nanosyntax features merge one at a time, and the phrase a merger creates must be lexicalized
before the next feature merges. When it is not, material evacuates from the complement of the new
feature: first the closest labelled constituent that is not a remnant, the one holding the bottom
of the sequence, and then ever larger constituents around it, until the remnant phrase is
lexicalized. If no evacuation helps, the derivation returns to the previous merger and takes its
next option. A lexicalized object is pronounced as a whole, so an entry matching the new phrase,
or the whole object evacuation has built, overrides the exponents inside it.

The algorithm consults the lexicon only through a spellout function `σ`, the exponent of an
object if it has one. `mergeOptions σ t f` lists the ways of lexicalizing the merger of `f` with
`t` in order of preference, and `derivations σ t fs` folds it over a sequence in the list monad,
so that deriving `fs ++ gs` is deriving `fs` and, from each result in turn, `gs`
(`derivations_append`), which is backtracking. `lexicalize` returns the first derivation and
`exponents` what `spell` pronounces of it: a spellable object gets one exponent, and any other
object the exponents of its two daughters in order.

A derivation is always pronounced (`exponents_eq_none_iff`). Where spellable objects are closed
under constituents (`IsLowerSpellout`), as under any matching by containment, a sequence whose
spine is spellable is lexicalized without movement (`lexicalize_cons_of_isSome`), and where no
bare feature above the bottom is spellable the algorithm never evacuates
(`exponents_cons_of_forall_bare`). A derivation is its spine or has an unlabelled node
(`eq_pspine_or_hasUnlabelled`), so where no spellable object has an unlabelled node, a sequence
is pronounced with one exponent exactly when its spine is spellable
(`exponents_cons_eq_singleton_iff`), and then so is every initial part of it
(`exists_exponents_eq_singleton_of_prefix`).
The same holds, whatever objects are stored, of a spellout that reads only
the features of an object (`exists_exponents_eq_singleton_of_subset_of_isFeatureSpellout`), so
matching by sets of features derives no inverse marking.

## Implementation notes

* Evacuation leaves no trace and projects no label. A phrase that loses its complement stays as
  the bare phrase of its feature, and an unlabelled node that loses a daughter is not kept, so
  `evacuations` returns what is left of an object, if anything.
* `mergeOptions` follows the formulation with pied-piping, in which the constituent holding the
  bottom of the sequence evacuates first and then each node dominating it up to the whole
  complement. On an object with one evacuated constituent these are the movement of the
  specifier and of the complement.

## TODO

* The algorithm's last resort, a specifier built in a workspace of its own, which is where
  prefixes come from. A prefix stores a feature merged with a bare head, `phrase f (leaf g)`,
  which is not `phrase f (bare g)`.

## References

* [starke-2018]
* [declercq-et-al-2025]
* [caha-2009]
-/

@[expose] public section

namespace Morphology.Nanosyntax

open Minimalist.Next SyntacticObject

variable {F : Type}

/-! ### The algorithm -/

variable {α : Type*} (σ : SyntacticObject (Option F) → Option α)

/-- The ways of evacuating from an object, smallest evacuee first, each with what is left of the
object, if anything. An unlabelled node that loses a daughter is not kept. -/
def evacuations : PlanarSyntacticObject (Option F) →
    List (PlanarSyntacticObject (Option F) × Option (PlanarSyntacticObject (Option F)))
  | .mul (.mul a b) r =>
    (evacuations (.mul a b)).map (fun p ↦ (p.1, some (p.2.elim r (· * r)))) ++
      [(.mul (.mul a b) r, none)]
  | t => [(t, none)]

/-- The remnant phrase of `f` over what an evacuation leaves. -/
abbrev remnant (f : F) (m : Option (PlanarSyntacticObject (Option F))) :
    PlanarSyntacticObject (Option F) :=
  m.elim (pbare f) (pphrase f)

/-- The ways of lexicalizing the merger of `f` with `t`, in order of preference: the new phrase
whole, then each evacuation with the remnant phrase lexicalized. -/
def mergeOptions (t : PlanarSyntacticObject (Option F)) (f : F) :
    List (PlanarSyntacticObject (Option F)) :=
  ((σ (pphrase f t).toSyntacticObject).map fun _ ↦ pphrase f t).toList ++
    (evacuations t).filterMap fun p ↦
      (σ (remnant f p.2).toSyntacticObject).map fun _ ↦ p.1 * remnant f p.2

/-- The derivations of a sequence from an object, in order of preference. -/
def derivations (t : PlanarSyntacticObject (Option F)) (fs : List F) :
    List (PlanarSyntacticObject (Option F)) :=
  fs.foldlM (mergeOptions σ) t

@[simp] theorem derivations_nil (t : PlanarSyntacticObject (Option F)) :
    derivations σ t [] = [t] := rfl

theorem derivations_singleton (t : PlanarSyntacticObject (Option F)) (f : F) :
    derivations σ t [f] = mergeOptions σ t f := by simp [derivations]

theorem derivations_append (t : PlanarSyntacticObject (Option F)) (fs gs : List F) :
    derivations σ t (fs ++ gs) = (derivations σ t fs).flatMap (derivations σ · gs) :=
  List.foldlM_append

/-- The first derivation of a sequence, where the bare phrase of its bottom is spellable. -/
def lexicalize : List F → Option (PlanarSyntacticObject (Option F))
  | [] => none
  | f₀ :: fs => (σ (pbare f₀).toSyntacticObject).bind fun _ ↦ (derivations σ (pbare f₀) fs).head?

/-- A lexicalized object is pronounced whole; otherwise its daughters are pronounced in order. -/
def spell : PlanarSyntacticObject (Option F) → Option (List α)
  | .mul l r => ((σ (PlanarSyntacticObject.toSyntacticObject (.mul l r))).map fun x ↦ [x]) <|>
      (spell l).bind fun xs ↦ (spell r).map (xs ++ ·)
  | .of a => (σ (PlanarSyntacticObject.toSyntacticObject (.of a))).map fun x ↦ [x]

/-- The exponents the algorithm gives a feature sequence, in linear order. -/
def exponents (fs : List F) : Option (List α) := (lexicalize σ fs).bind (spell σ)

/-! ### Evacuation builds unlabelled nodes -/

variable {σ}

theorem exists_mul_of_mem_evacuations {t : PlanarSyntacticObject (Option F)}
    (ht : ∃ a b, t = a * b) :
    ∀ p ∈ evacuations t, ∃ a b, p.1 = a * b := by
  fun_induction evacuations t with
  | case1 a b r ih =>
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ih ⟨a, b, rfl⟩ q hq
    · rw [List.mem_singleton.1 hp]
      exact ⟨a * b, r, rfl⟩
  | case2 t _ =>
    intro p hp
    rw [List.mem_singleton.1 hp]
    exact ht

theorem exists_remnant_eq_mul (f : F) (m : Option (PlanarSyntacticObject (Option F))) :
    ∃ c d, remnant f m = c * d := by
  cases m <;> exact ⟨_, _, rfl⟩

theorem mem_mergeOptions {t t' : PlanarSyntacticObject (Option F)} {f : F} :
    t' ∈ mergeOptions σ t f ↔
      (σ (pphrase f t).toSyntacticObject).isSome ∧ t' = pphrase f t ∨
        ∃ p ∈ evacuations t, (σ (remnant f p.2).toSyntacticObject).isSome ∧
          t' = p.1 * remnant f p.2 := by
  simp only [mergeOptions, List.mem_append, Option.mem_toList, Option.map_eq_some_iff,
    List.mem_filterMap, Option.isSome_iff_exists]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨p, hp, x, hx, rfl⟩)
    · exact .inl ⟨⟨x, hx⟩, rfl⟩
    · exact .inr ⟨p, hp, ⟨x, hx⟩, rfl⟩
  · rintro (⟨⟨x, hx⟩, rfl⟩ | ⟨p, hp, ⟨x, hx⟩, rfl⟩)
    · exact .inl ⟨x, hx, rfl⟩
    · exact .inr ⟨p, hp, x, hx, rfl⟩

theorem hasUnlabelled_phrase {f : F} {s : SyntacticObject (Option F)} (h : HasUnlabelled s) :
    HasUnlabelled (phrase f s) := by
  obtain ⟨u, hu, hu'⟩ := h
  exact ⟨u, containsOrEq_mul.2 (.inr (.inr hu)), hu'⟩

/-- A derivation of a sequence is its spine or has an unlabelled node, and it is a product. -/
theorem eq_pspine_or_hasUnlabelled {f₀ : F} {fs : List F} {t : PlanarSyntacticObject (Option F)}
    (h : t ∈ derivations σ (pbare f₀) fs) :
    (t = pspine f₀ fs ∨ HasUnlabelled t.toSyntacticObject) ∧ ∃ a b, t = a * b := by
  induction fs using List.reverseRecOn generalizing t with
  | nil =>
    obtain rfl : t = pbare f₀ := by simpa using h
    exact ⟨.inl rfl, _, _, rfl⟩
  | append_singleton fs f ih =>
    rw [derivations_append] at h
    obtain ⟨t₁, h₁, h⟩ := List.mem_flatMap.1 h
    rw [derivations_singleton] at h
    obtain ⟨ht₁, hmul⟩ := ih h₁
    rcases mem_mergeOptions.1 h with ⟨-, rfl⟩ | ⟨p, hp, -, rfl⟩
    · refine ⟨?_, _, _, rfl⟩
      rcases ht₁ with rfl | ht₁
      · exact .inl (pspine_concat ..).symm
      · refine .inr ?_
        rw [PlanarSyntacticObject.toSyntacticObject_mul]
        exact hasUnlabelled_phrase ht₁
    · obtain ⟨a, b, hab⟩ := exists_mul_of_mem_evacuations hmul p hp
      obtain ⟨c, d, hcd⟩ := exists_remnant_eq_mul f p.2
      refine ⟨.inr ⟨_, Relation.ReflTransGen.refl, ?_⟩, _, _, rfl⟩
      rw [hab, hcd]
      exact ⟨a.toSyntacticObject, b.toSyntacticObject, c.toSyntacticObject, d.toSyntacticObject,
        by simp only [PlanarSyntacticObject.toSyntacticObject_mul]⟩

theorem evacuations_pspine (f₀ : F) (fs : List F) :
    evacuations (pspine f₀ fs) = [(pspine f₀ fs, none)] := by
  cases fs using List.reverseRecOn with
  | nil => rfl
  | append_singleton fs f => rw [pspine_concat]; rfl

/-- The evacuees of an evacuee of an object are evacuees of the object. -/
theorem exists_mem_evacuations_of_mem {t : PlanarSyntacticObject (Option F)} :
    ∀ p ∈ evacuations t, ∀ q ∈ evacuations p.1, ∃ q' ∈ evacuations t, q'.1 = q.1 := by
  fun_induction evacuations t with
  | case1 a b r ih =>
    intro p hp q hq
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      obtain ⟨q', hq', h⟩ := ih p₀ hp₀ q hq
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hq'), h⟩
    · rw [List.mem_singleton.1 hp] at hq
      exact ⟨q, hq, rfl⟩
  | case2 t ht =>
    intro p hp q hq
    have key : evacuations t = [(t, none)] := by
      unfold evacuations
      split
      · exact (ht _ _ _ rfl).elim
      · rfl
    rw [List.mem_singleton.1 hp, key] at hq
    exact ⟨q, hq, rfl⟩

/-! ### Pronunciation -/

theorem spell_mul (l r : PlanarSyntacticObject (Option F)) :
    spell σ (l * r) = (((σ (l * r).toSyntacticObject).map fun x ↦ [x]) <|>
      (spell σ l).bind fun xs ↦ (spell σ r).map (xs ++ ·)) := rfl

theorem spell_of_eq_some {t : PlanarSyntacticObject (Option F)} {x : α}
    (h : σ t.toSyntacticObject = some x) : spell σ t = some [x] := by
  cases t with
  | of a => simpa [spell] using h
  | mul l r =>
    rw [show FreeMagma.mul l r = l * r from rfl] at h ⊢
    rw [spell_mul, h]
    rfl

theorem spell_ne_nil (t : PlanarSyntacticObject (Option F)) : spell σ t ≠ some [] := by
  induction t with
  | of a => cases h : σ (PlanarSyntacticObject.toSyntacticObject (.of a)) <;> simp [spell, h]
  | mul l r ihl ihr =>
    rw [show FreeMagma.mul l r = l * r from rfl, spell_mul]
    generalize σ (PlanarSyntacticObject.toSyntacticObject (l * r)) = o
    intro hc
    rcases o with - | y
    · rcases hl : spell σ l with - | xs
      · simp [hl] at hc
      rcases hr : spell σ r with - | ys
      · simp [hl, hr] at hc
      simp [hl, hr] at hc
      exact ihl (hc.1 ▸ hl)
    · simp at hc

private theorem eq_some_of_spell_eq_singleton {l r : PlanarSyntacticObject (Option F)} {x : α}
    (h : spell σ (l * r) = some [x]) : σ (l * r).toSyntacticObject = some x := by
  rw [spell_mul] at h
  generalize σ (l * r).toSyntacticObject = o at h ⊢
  rcases o with - | y
  · rcases hl : spell σ l with - | xs
    · simp [hl] at h
    rcases hr : spell σ r with - | ys
    · simp [hl, hr] at h
    simp [hl, hr] at h
    rcases xs with - | ⟨a, xs⟩
    · exact absurd hl (spell_ne_nil l)
    · rcases ys with - | ⟨b, ys⟩
      · exact absurd hr (spell_ne_nil r)
      · simp at h
  · simpa using h

/-- An object is pronounced with one exponent exactly when it is lexicalized whole. -/
theorem spell_eq_some_singleton_iff {t : PlanarSyntacticObject (Option F)} {x : α} :
    spell σ t = some [x] ↔ σ t.toSyntacticObject = some x := by
  refine ⟨fun h ↦ ?_, spell_of_eq_some⟩
  cases t with
  | of a =>
    obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.1 h
    rw [hy, List.singleton_inj.1 hxy]
  | mul l r => exact eq_some_of_spell_eq_singleton h

theorem mem_evacuations_self (t : PlanarSyntacticObject (Option F)) :
    (t, none) ∈ evacuations t := by
  fun_induction evacuations t <;> simp

/-! ### Soundness -/

/-- Every evacuee of a derivation is pronounced, the derivation itself among them. -/
theorem isSome_spell_of_mem_derivations {f₀ : F} {fs : List F}
    {t : PlanarSyntacticObject (Option F)}
    (hb : (σ (bare f₀)).isSome) (h : t ∈ derivations σ (pbare f₀) fs) :
    (∀ p ∈ evacuations t, (spell σ p.1).isSome) ∧ ∃ a b, t = a * b := by
  induction fs using List.reverseRecOn generalizing t with
  | nil =>
    obtain rfl : t = pbare f₀ := by simpa using h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hb
    refine ⟨fun p hp ↦ ?_, _, _, rfl⟩
    rw [show evacuations (pbare f₀) = [(pbare f₀, none)] from rfl] at hp
    obtain rfl := List.mem_singleton.1 hp
    exact Option.isSome_iff_exists.2 ⟨_, spell_of_eq_some (t := pbare f₀) hx⟩
  | append_singleton fs f ih =>
    rw [derivations_append] at h
    obtain ⟨t₁, h₁, h⟩ := List.mem_flatMap.1 h
    rw [derivations_singleton] at h
    obtain ⟨ht₁, hmul⟩ := ih h₁
    rcases List.mem_append.1 h with h | h
    · obtain ⟨x, hx, rfl⟩ : ∃ x, σ (pphrase f t₁).toSyntacticObject = some x ∧
          pphrase f t₁ = t := by simpa using h
      refine ⟨fun p hp ↦ ?_, _, _, rfl⟩
      rw [show evacuations (pphrase f t₁) = [(pphrase f t₁, none)] from rfl] at hp
      obtain rfl := List.mem_singleton.1 hp
      exact Option.isSome_iff_exists.2 ⟨_, spell_of_eq_some hx⟩
    · obtain ⟨p, hp, h⟩ := List.mem_filterMap.1 h
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a, b, hab⟩ := exists_mul_of_mem_evacuations hmul p hp
      obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 (ht₁ p hp)
      have hwhole : (spell σ (p.1 * remnant f p.2)).isSome := by
        rw [spell_mul, hxs, spell_of_eq_some hx]
        cases σ (p.1 * remnant f p.2).toSyntacticObject <;> rfl
      refine ⟨fun q hq ↦ ?_, _, _, rfl⟩
      rw [hab, show evacuations (a * b * remnant f p.2) =
        (evacuations (a * b)).map (fun q ↦ (q.1, some (q.2.elim (remnant f p.2)
          (· * remnant f p.2)))) ++ [(a * b * remnant f p.2, none)] from rfl] at hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1 hq
        obtain ⟨q', hq', h'⟩ := exists_mem_evacuations_of_mem p hp q₀ (hab ▸ hq₀)
        exact h' ▸ ht₁ q' hq'
      · obtain rfl := List.mem_singleton.1 hq
        rw [hab] at hwhole
        exact hwhole

/-- A sequence the algorithm derives is pronounced. -/
theorem exponents_eq_none_iff {fs : List F} : exponents σ fs = none ↔ lexicalize σ fs = none := by
  rcases fs with - | ⟨f₀, fs⟩
  · simp [exponents, lexicalize]
  rcases h : lexicalize σ (f₀ :: fs) with - | t
  · simp [exponents, h]
  · obtain ⟨b, hb, ht⟩ := Option.bind_eq_some_iff.1 h
    have hb' : (σ (bare f₀)).isSome := Option.isSome_iff_exists.2 ⟨b, hb⟩
    obtain ⟨hs, a, c, rfl⟩ := isSome_spell_of_mem_derivations hb' (List.mem_of_mem_head? ht)
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 (hs _ (mem_evacuations_self _))
    simp [exponents, h, hxs]

/-! ### Short sequences -/

theorem exponents_singleton (f : F) : exponents σ [f] = (σ (bare f)).map fun x ↦ [x] := by
  rw [exponents, lexicalize, derivations_nil]
  rcases h : σ (bare f) with - | x
  · rw [show (pbare f).toSyntacticObject = bare f from rfl, h]
    rfl
  · rw [show (pbare f).toSyntacticObject = bare f from rfl, h]
    exact spell_of_eq_some (t := pbare f) h

theorem exponents_pair (f₁ f₂ : F) :
    exponents σ [f₁, f₂] = (σ (bare f₁)).bind fun x ↦
      ((σ (phrase f₂ (bare f₁))).map fun y ↦ [y]) <|>
        (σ (bare f₂)).bind fun y ↦
          ((σ (bare f₁ * bare f₂)).map fun z ↦ [z]) <|> some [x, y] := by
  have e₁ : (pbare f₁).toSyntacticObject = bare f₁ := rfl
  have e₂ : (pbare f₂).toSyntacticObject = bare f₂ := rfl
  have e₃ : (pphrase f₂ (pbare f₁)).toSyntacticObject = phrase f₂ (bare f₁) := rfl
  have e₄ : (pbare f₁ * pbare f₂).toSyntacticObject = bare f₁ * bare f₂ := rfl
  rw [exponents, lexicalize, derivations_singleton, mergeOptions,
    show evacuations (pbare f₁) = [(pbare f₁, none)] from rfl, e₁, e₃]
  rcases h₁ : σ (bare f₁) with - | x
  · rfl
  rcases hw : σ (phrase f₂ (bare f₁)) with - | y
  · rcases hs : σ (bare f₂) with - | z
    · simp [remnant, e₂, hs]
    · rcases ha : σ (bare f₁ * bare f₂) with - | w
      · simp [remnant, e₂, hs, spell_mul, e₄, ha, spell_of_eq_some (t := pbare f₁) h₁,
          spell_of_eq_some (t := pbare f₂) hs]
      · simp [remnant, e₂, hs, spell_mul, e₄, ha]
  · simp [spell_of_eq_some (t := pphrase f₂ (pbare f₁)) hw]

/-! ### Lexicalization without movement, and without stored evacuation -/

variable (σ) in
/-- Spellable objects are closed under constituents, as under any matching by containment. -/
def IsLowerSpellout : Prop :=
  ∀ s t : SyntacticObject (Option F), t.ContainsOrEq s → (σ t).isSome → (σ s).isSome

/-- A sequence whose spine is spellable is lexicalized without movement. -/
theorem lexicalize_cons_of_isSome (hσ : IsLowerSpellout σ) (f₀ : F) {fs : List F}
    (h : (σ (spine f₀ fs)).isSome) : lexicalize σ (f₀ :: fs) = some (pspine f₀ fs) := by
  have hb : (σ (pbare f₀).toSyntacticObject).isSome :=
    hσ _ _ (spine_containsOrEq_spine_iff.2 (List.nil_prefix (l := fs))) h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb
  rw [lexicalize, hb, Option.bind_some]
  induction fs using List.reverseRecOn with
  | nil => rfl
  | append_singleton fs f ih =>
    have hs : (σ (spine f₀ fs)).isSome :=
      hσ _ _ (spine_containsOrEq_spine_iff.2 (List.prefix_append fs [f])) h
    obtain ⟨ds, hds⟩ := List.head?_eq_some_iff.1 (ih hs)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    have hx' : σ (pphrase f (pspine f₀ fs)).toSyntacticObject = some x := by
      rw [← pspine_concat, toSyntacticObject_pspine, hx]
    rw [derivations_append, hds, List.flatMap_cons, derivations_singleton, mergeOptions, hx']
    simp

theorem exponents_cons_of_eq_some (hσ : IsLowerSpellout σ) (f₀ : F) {fs : List F} {x : α}
    (h : σ (spine f₀ fs) = some x) : exponents σ (f₀ :: fs) = some [x] := by
  rw [exponents, lexicalize_cons_of_isSome hσ f₀ (Option.isSome_iff_exists.2 ⟨x, h⟩),
    Option.bind_some]
  exact spell_of_eq_some (by rw [toSyntacticObject_pspine, h])

/-- Where spellable objects are closed under constituents and none has an unlabelled node, a
sequence is pronounced with one exponent exactly when its spine is spellable. -/
theorem exponents_cons_eq_singleton_iff (hσ : IsLowerSpellout σ)
    (hL : ∀ s, (σ s).isSome → ¬ HasUnlabelled s) {f₀ : F} {fs : List F} {x : α} :
    exponents σ (f₀ :: fs) = some [x] ↔ σ (spine f₀ fs) = some x := by
  refine ⟨fun h ↦ ?_, exponents_cons_of_eq_some hσ f₀⟩
  obtain ⟨t, ht, hs⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨b, -, ht⟩ := Option.bind_eq_some_iff.1 ht
  have hx := spell_eq_some_singleton_iff.1 hs
  obtain rfl | ht' := (eq_pspine_or_hasUnlabelled (List.mem_of_mem_head? ht)).1
  · rwa [toSyntacticObject_pspine] at hx
  · exact absurd ht' (hL _ (Option.isSome_iff_exists.2 ⟨x, hx⟩))

/-- Under the same hypotheses, a sequence pronounced with one exponent has every initial part
pronounced with one exponent. -/
theorem exists_exponents_eq_singleton_of_prefix (hσ : IsLowerSpellout σ)
    (hL : ∀ s, (σ s).isSome → ¬ HasUnlabelled s) {f₀ : F} {fs gs : List F} {x : α}
    (hgs : gs <+: fs) (h : exponents σ (f₀ :: fs) = some [x]) :
    ∃ y, exponents σ (f₀ :: gs) = some [y] := by
  have hx := (exponents_cons_eq_singleton_iff hσ hL).1 h
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1
    (hσ _ _ (spine_containsOrEq_spine_iff.2 hgs) (Option.isSome_iff_exists.2 ⟨x, hx⟩))
  exact ⟨y, exponents_cons_of_eq_some hσ f₀ hy⟩

/-- Where spellable objects are closed under constituents and no bare feature above the bottom
is spellable, the sequence gets the one exponent of its spine, or none. -/
theorem exponents_cons_of_forall_bare (hσ : IsLowerSpellout σ) (f₀ : F) {fs : List F}
    (h : ∀ f ∈ fs, σ (bare f) = none) :
    exponents σ (f₀ :: fs) = (σ (spine f₀ fs)).map fun x ↦ [x] := by
  rcases hx : σ (spine f₀ fs) with - | x
  · suffices hl : lexicalize σ (f₀ :: fs) = none by simp [exponents, hl]
    rw [lexicalize]
    rcases hb : σ (pbare f₀).toSyntacticObject with - | b
    · rfl
    rw [Option.bind_some]
    suffices hd : derivations σ (pbare f₀) fs =
        ((σ (spine f₀ fs)).map fun _ ↦ pspine f₀ fs).toList by rw [hd, hx]; rfl
    clear hx
    induction fs using List.reverseRecOn with
    | nil => rw [derivations_nil, spine_nil, show bare f₀ = (pbare f₀).toSyntacticObject from rfl,
        hb]; rfl
    | append_singleton fs f ih =>
      rw [derivations_append, ih fun g hg ↦ h g (List.mem_append_left _ hg)]
      rcases hs : σ (spine f₀ fs) with - | y
      · have : σ (spine f₀ (fs ++ [f])) = none := by
          by_contra hne
          have := hσ _ _ (spine_containsOrEq_spine_iff.2 (List.prefix_append fs [f]))
            (Option.isSome_iff_ne_none.2 hne)
          simp [hs] at this
        rw [this]
        rfl
      · have hbare : σ (pbare f).toSyntacticObject = none := h f (by simp)
        have hph : (pphrase f (pspine f₀ fs)).toSyntacticObject = spine f₀ (fs ++ [f]) := by
          rw [← pspine_concat, toSyntacticObject_pspine]
        simp only [Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        rw [derivations_singleton, mergeOptions, evacuations_pspine, hph,
          List.filterMap_cons_none (by
            show Option.map _ (σ (pbare f).toSyntacticObject) = none
            rw [hbare]; rfl),
          List.filterMap_nil, List.append_nil, pspine_concat]
  · exact exponents_cons_of_eq_some hσ f₀ hx

/-! ### Spellout by features -/

variable (σ) in
/-- A spellout that reads only the features of an object: an object whose features are among
those of a spellable object is spellable. -/
def IsFeatureSpellout : Prop :=
  ∀ s t : SyntacticObject (Option F), features s ⊆ features t → (σ t).isSome → (σ s).isSome

theorem IsFeatureSpellout.isLowerSpellout (hσ : IsFeatureSpellout σ) : IsLowerSpellout σ :=
  fun s t hst ↦ hσ s t (Multiset.subset_of_le (features_le_of_mem_terms (mem_terms.2 hst)))

theorem mem_features_spine {f₀ g : F} {fs : List F} :
    g ∈ features (spine f₀ fs) ↔ g = f₀ ∨ g ∈ fs := by
  induction fs using List.reverseRecOn with
  | nil => simp
  | append_singleton fs f ih =>
    simp [ih]
    tauto

/-- An evacuation divides the features of an object between the evacuee and what is left. -/
theorem features_add_of_mem_evacuations {t : PlanarSyntacticObject (Option F)} :
    ∀ p ∈ evacuations t, features p.1.toSyntacticObject +
      p.2.elim 0 (fun x ↦ features x.toSyntacticObject) = features t.toSyntacticObject := by
  fun_induction evacuations t with
  | case1 a b r ih =>
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      have h := ih q hq
      rw [show FreeMagma.mul (FreeMagma.mul a b) r = FreeMagma.mul a b * r from rfl,
        PlanarSyntacticObject.toSyntacticObject_mul, features_mul, ← h]
      rcases q with ⟨e, - | m⟩
      · simp
      · simp [PlanarSyntacticObject.toSyntacticObject_mul, add_assoc]
    · rw [List.mem_singleton.1 hp]
      simp
  | case2 t _ =>
    intro p hp
    rw [List.mem_singleton.1 hp]
    simp

/-- A derivation has the features of its sequence. -/
theorem mem_features_of_mem_derivations {f₀ : F} {fs : List F}
    {t : PlanarSyntacticObject (Option F)}
    (h : t ∈ derivations σ (pbare f₀) fs) {g : F} :
    g ∈ features t.toSyntacticObject ↔ g = f₀ ∨ g ∈ fs := by
  induction fs using List.reverseRecOn generalizing t with
  | nil =>
    obtain rfl : t = pbare f₀ := by simpa using h
    simp
  | append_singleton fs f ih =>
    rw [derivations_append] at h
    obtain ⟨t₁, h₁, h⟩ := List.mem_flatMap.1 h
    rw [derivations_singleton] at h
    have ih := ih h₁
    rcases List.mem_append.1 h with h | h
    · obtain ⟨x, -, rfl⟩ : ∃ x, σ (pphrase f t₁).toSyntacticObject = some x ∧
          pphrase f t₁ = t := by simpa using h
      rw [PlanarSyntacticObject.toSyntacticObject_mul, features_mul]
      simp [ih]
      tauto
    · obtain ⟨p, hp, h⟩ := List.mem_filterMap.1 h
      obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h
      have hy := features_add_of_mem_evacuations p hp
      rw [← hy] at ih
      rw [PlanarSyntacticObject.toSyntacticObject_mul, features_mul]
      rcases p with ⟨e, - | m⟩
      · simp only [Option.elim_none, add_zero] at ih
        simp [remnant, ih]
        tauto
      · simp only [Option.elim_some, Multiset.mem_add] at ih
        simp [remnant, PlanarSyntacticObject.toSyntacticObject_mul]
        tauto

/-- Under a spellout that reads only features, a sequence pronounced with one exponent has every
sequence of features drawn from it pronounced with one exponent, whatever objects the entries
store. -/
theorem exists_exponents_eq_singleton_of_subset_of_isFeatureSpellout (hσ : IsFeatureSpellout σ)
    {f₀ g₀ : F} {fs gs : List F} {x : α} (hgs : g₀ :: gs ⊆ f₀ :: fs)
    (h : exponents σ (f₀ :: fs) = some [x]) : ∃ y, exponents σ (g₀ :: gs) = some [y] := by
  obtain ⟨t, ht, hs⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨b, -, ht⟩ := Option.bind_eq_some_iff.1 ht
  have hmem := List.mem_of_mem_head? ht
  have hx := spell_eq_some_singleton_iff.1 hs
  have hsub : features (spine g₀ gs) ⊆ features t.toSyntacticObject := fun g hg ↦
    (mem_features_of_mem_derivations hmem).2
      (List.mem_cons.1 (hgs (List.mem_cons.2 (mem_features_spine.1 hg))))
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hσ _ _ hsub (Option.isSome_iff_exists.2 ⟨x, hx⟩))
  exact ⟨y, exponents_cons_of_eq_some hσ.isLowerSpellout g₀ hy⟩

end Morphology.Nanosyntax
