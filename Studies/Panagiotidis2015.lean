module

public import Linglib.Syntax.Minimalist.Spine
public import Mathlib.Data.Option.Basic

/-!
# Panagiotidis (2015): Categorial Features

A categorial feature is one of `[N]` and `[V]`, which impose a sortal and an extending-into-time
perspective on the complement of the head that bears them. A head bears at most one categorial
feature interpretably and at most one uninterpretably. A categorizer, *n* or *v*, bears an
interpretable feature and is a lexical head. A functional head bears an uninterpretable one, that
of the lexical head at the foot of its projection line (Categorial Deficiency). A Switch bears
both, as the head of a gerund bears `[N]` beside `[uV]`, and a root bears neither.

A projection line is the list of heads a phrase projects, from the bottom up. Its category is the
interpretable feature of its highest categorizer. An uninterpretable feature probes the complement
of its head, and the line converges when each `[uX]` finds `[X]` as the category of that
complement, the closest interpretable feature below it (categorial Agree).

In a convergent line a head merged over material without a categorizer bears no uninterpretable
feature, so a functional head takes no bare root as its complement. The functional heads of a
line whose categorizers all bear `[X]` all bear `[uX]`, which is biuniqueness. Between two heads
with different uninterpretable features there is a categorizer, which may be the lower of the two.
If the only heads with both features are Switches `[N][uV]` and no categorizer without an
uninterpretable feature is merged over functional structure, then no `[uV]` head lies above a
`[uN]` head, which is Phrasal Coherence, and a line through a Switch is nominal. With the features
of the substrate's nominal and verbal categories read off their families, an extended projection
that begins at its categorizer converges.

## Implementation notes

A projection line records the head that projects at each application of Merge, so specifiers and
the label of a phrase merged with a phrase are not represented.

Categorial Agree alone admits a verbalizing Switch `[V][uN]` and a lexical categorizer merged over
functional structure. The book takes neither to exist and derives neither, so the two restrictions
are hypotheses of the theorems that need them.

In `Head.ofCat` the lexical head of a family is the root, as in the substrate's citation of the
book, so a spine that leaves out the categorizer is functional structure over a bare root.
Adjectival and adpositional heads have no image: the book leaves the features of adjectives open
and does not take adpositions to form a category of this system.

## TODO

The licensing of roots by a categorizer at the interface, the labelling predictions of categorial
Agree, the phasehood of categorizers and Switches, and the size of the complement of a Switch are
not formalized.

## References

* [panagiotidis-2015]
* [grimshaw-2005]
* [embick-marantz-2008]
-/

@[expose] public section

namespace Panagiotidis2015

open Minimalist

/-- (7), p. 84: the categorial features, `N` a sortal perspective and `V` a perspective extending
into time. -/
inductive CategorialFeature where
  | N
  | V
  deriving DecidableEq, Repr

/-- The categorial features of a head. -/
structure Head where
  /-- The interpretable feature, which sets the perspective on the complement. -/
  interpretable : Option CategorialFeature := none
  /-- The uninterpretable feature, a probe for categorial Agree. -/
  uninterpretable : Option CategorialFeature := none
  deriving DecidableEq, Repr

namespace Head

/-- A root, which bears no categorial feature. -/
def root : Head := {}

/-- (11), p. 119: a lexical head bears an interpretable categorial feature. -/
def categorizer (X : CategorialFeature) : Head := ⟨some X, none⟩

/-- The nominalizer. -/
abbrev n : Head := categorizer .N

/-- The verbalizer. -/
abbrev v : Head := categorizer .V

/-- (11), p. 119: a functional head bears an uninterpretable categorial feature. -/
def functional (X : CategorialFeature) : Head := ⟨none, some X⟩

/-- (17), p. 143, and p. 172: a Switch bears an interpretable feature `X` and an uninterpretable
feature `Y`. -/
def switch (X Y : CategorialFeature) : Head := ⟨some X, some Y⟩

end Head

variable {l l₁ l₂ l₃ : List Head} {h h' k : Head} {X Y : CategorialFeature}

/-! ### The category of a projection line -/

/-- The category of a projection line is the interpretable feature of its highest categorizer, by
which the phrase is identified externally. -/
def category (l : List Head) : Option CategorialFeature :=
  (l.filterMap Head.interpretable).getLast?

@[simp] theorem category_nil : category [] = none := rfl

theorem category_append (l₁ l₂ : List Head) :
    category (l₁ ++ l₂) = (category l₂).or (category l₁) := by
  simp [category, List.getLast?_append]

@[simp] theorem category_singleton (h : Head) : category [h] = h.interpretable := by
  cases hi : h.interpretable <;> simp [category, hi]

@[simp] theorem category_concat (l : List Head) (h : Head) :
    category (l ++ [h]) = h.interpretable.or (category l) := by
  rw [category_append, category_singleton]

theorem category_eq_none_iff : category l = none ↔ ∀ h ∈ l, h.interpretable = none := by
  simp [category]

theorem exists_mem_of_category_eq_some (hl : category l = some X) :
    ∃ h ∈ l, h.interpretable = some X := by
  simpa using List.mem_of_getLast? hl

theorem category_eq_some_of_forall (hk : k ∈ l) (hkX : k.interpretable = some X)
    (hl : ∀ h ∈ l, ∀ Y ∈ h.interpretable, Y = X) : category l = some X := by
  cases hc : category l with
  | none => simp [category_eq_none_iff.1 hc k hk] at hkX
  | some Y =>
    obtain ⟨h, hh, hY⟩ := exists_mem_of_category_eq_some hc
    rw [hl h hh Y hY]

/-! ### Categorial Agree -/

/-- (14) and (16), pp. 125–126, with the minimality of p. 147: a projection line converges when
every uninterpretable feature `[uX]` finds `[X]` as the category of the complement of its head. -/
def Converges (l : List Head) : Prop :=
  ∀ l₁ h, l₁ ++ [h] <+: l → ∀ X ∈ h.uninterpretable, category l₁ = some X

theorem converges_iff_forall_getElem : Converges l ↔
    ∀ (i : ℕ) (hi : i < l.length), ∀ X ∈ l[i].uninterpretable, category (l.take i) = some X := by
  refine ⟨fun hl i hi ↦ hl _ _ ?_, ?_⟩
  · rw [← List.take_succ_eq_append_getElem hi]
    exact List.take_prefix _ _
  · rintro hl l₁ h ⟨t, rfl⟩
    simpa using hl l₁.length (by simp)

instance : DecidablePred Converges := fun _ ↦ decidable_of_iff _ converges_iff_forall_getElem.symm

@[simp] theorem converges_nil : Converges [] := fun l₁ h hp ↦ by simp at hp

theorem Converges.of_prefix (hl : Converges l₂) (hp : l₁ <+: l₂) : Converges l₁ :=
  fun a k hk ↦ hl a k (hk.trans hp)

-- Merging the head `h` with the line `l`.
theorem converges_concat : Converges (l ++ [h]) ↔
    Converges l ∧ ∀ X ∈ h.uninterpretable, category l = some X := by
  refine ⟨fun hl ↦ ⟨hl.of_prefix (List.prefix_append _ _), hl l h List.prefix_rfl⟩, ?_⟩
  rintro ⟨hl, hh⟩ l₁ k hp
  rcases List.prefix_concat_iff.1 hp with heq | hp
  · obtain ⟨rfl, hk⟩ := List.append_inj' heq rfl
    obtain rfl : k = h := by simpa using hk
    exact hh
  · exact hl l₁ k hp

theorem converges_cons_of_forall_mem {o : Option CategorialFeature}
    (hl : ∀ h ∈ l, (∀ Y ∈ h.interpretable, Y ∈ o) ∧ ∀ Y ∈ h.uninterpretable, Y ∈ o) :
    Converges (⟨o, none⟩ :: l) := by
  rintro (_ | ⟨k, l₁⟩) h hp X hX
  · obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hp
    simp at hX
  · obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.1 hp
    have hsub : ∀ x ∈ l₁ ++ [h], x ∈ l := fun x hx ↦ hp'.subset hx
    obtain rfl : o = some X := (hl h (hsub h (by simp))).2 X hX
    refine category_eq_some_of_forall (k := ⟨some X, none⟩) (by simp) rfl fun h' hh' Y hY ↦ ?_
    rcases List.mem_cons.1 hh' with rfl | hh'
    · exact (Option.some.inj hY).symm
    · exact (Option.some.inj ((hl h' (hsub h' (by simp [hh']))).1 Y hY)).symm

/-- A head merged over material without a categorizer bears no uninterpretable feature, so a
functional head takes no bare root as its complement, the part of the Categorization Assumption of
[embick-marantz-2008] that categorial Agree derives. -/
theorem Converges.uninterpretable_eq_none (hl : Converges (l₁ ++ h :: l₂))
    (h₁ : category l₁ = none) : h.uninterpretable = none :=
  Option.eq_none_iff_forall_ne_some.2 fun X hX ↦ by
    simpa [h₁] using hl l₁ h ⟨l₂, by simp⟩ X hX

/-- Biuniqueness: in a convergent line whose categorizers all bear `[X]`, every functional head
bears `[uX]`. -/
theorem Converges.uninterpretable_eq (hl : Converges l)
    (hX : ∀ h ∈ l, ∀ Y ∈ h.interpretable, Y = X) : ∀ h ∈ l, ∀ Y ∈ h.uninterpretable, Y = X := by
  intro h hh Y hY
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hh
  obtain ⟨k, hk, hkY⟩ := exists_mem_of_category_eq_some (hl l₁ h ⟨l₂, by simp⟩ Y hY)
  exact hX k (List.mem_append_left _ hk) Y hkY

/-- The category of a line switches only at a categorizer: between a head bearing `[uX]` and a
higher head bearing `[uY]` with `Y ≠ X` there is a head bearing `[Y]`, the lower of the two
possibly being that head. -/
theorem Converges.exists_mem_interpretable_of_ne (hl : Converges (l₁ ++ h :: l₂ ++ h' :: l₃))
    (hX : X ∈ h.uninterpretable) (hY : Y ∈ h'.uninterpretable) (hne : Y ≠ X) :
    ∃ k ∈ h :: l₂, k.interpretable = some Y := by
  have h₁ : category l₁ = some X := hl l₁ h ⟨l₂ ++ h' :: l₃, by simp⟩ X hX
  have h₂ : category (l₁ ++ h :: l₂) = some Y := hl _ h' ⟨l₃, by simp⟩ Y hY
  rw [category_append, h₁] at h₂
  cases hc : category (h :: l₂) with
  | none => simp [hc, hne.symm] at h₂
  | some Z =>
    obtain rfl : Z = Y := by simpa [hc] using h₂
    exact exists_mem_of_category_eq_some hc

/-- Phrasal Coherence: in a convergent line whose only heads with both features are Switches
`[N][uV]`, and in which no categorizer without an uninterpretable feature is merged over a head
with one, no head bearing `[uV]` lies above a head bearing `[uN]`. -/
theorem Converges.phrasal_coherence (hl : Converges l)
    (hsw : ∀ k ∈ l, k.interpretable ≠ none → k.uninterpretable ≠ none → k = .switch .N .V)
    (hlex : ∀ a k, a ++ [k] <+: l → k.interpretable ≠ none → k.uninterpretable = none →
      ∀ x ∈ a, x.uninterpretable = none)
    (hp : l₁ ++ h :: l₂ ++ [h'] <+: l) (hN : h.uninterpretable = some .N) :
    h'.uninterpretable ≠ some .V := by
  intro hV
  obtain ⟨k, hk, hkV⟩ :=
    (hl.of_prefix hp).exists_mem_interpretable_of_ne (l₃ := []) hN hV (by decide)
  by_cases hu : k.uninterpretable = none
  · rcases List.mem_cons.1 hk with rfl | hk
    · simp [hu] at hN
    · obtain ⟨a, b, rfl⟩ := List.append_of_mem hk
      have := hlex (l₁ ++ h :: a) k (List.IsPrefix.trans ⟨b ++ [h'], by simp⟩ hp) (by simp [hkV]) hu
        h (by simp)
      simp [this] at hN
  · have := hsw k (hp.subset (List.mem_append_left _ (List.mem_append_right _ hk)))
      (by simp [hkV]) hu
    simp [this, Head.switch] at hkV

-- (8), p. 139, and p. 161: under the same restrictions a line through a Switch is nominal.
theorem category_eq_some_N_of_mem
    (hsw : ∀ k ∈ l, k.interpretable ≠ none → k.uninterpretable ≠ none → k = .switch .N .V)
    (hlex : ∀ a k, a ++ [k] <+: l → k.interpretable ≠ none → k.uninterpretable = none →
      ∀ x ∈ a, x.uninterpretable = none)
    (hk : Head.switch .N .V ∈ l) : category l = some .N := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hk
  suffices h : category (.switch .N .V :: b) = some .N by simp [category_append, h]
  refine category_eq_some_of_forall List.mem_cons_self rfl fun x hx Y hY ↦ ?_
  rcases List.mem_cons.1 hx with rfl | hx
  · exact (Option.some.inj hY).symm
  · obtain ⟨c, d, rfl⟩ := List.append_of_mem hx
    by_cases hu : x.uninterpretable = none
    · have := hlex (a ++ .switch .N .V :: c) x ⟨d, by simp⟩ (by simp [Option.mem_def.1 hY]) hu
        (.switch .N .V) (by simp)
      simp [Head.switch] at this
    · have := hsw x (by simp) (by simp [Option.mem_def.1 hY]) hu
      simpa [this, Head.switch] using hY.symm

/-! ### The book's structures -/

-- (6), p. 63: the denominal verb *tape*, a verbalizer over a nominalized root.
example : Converges [.root, .n, .v] ∧ category [.root, .n, .v] = some .V := by decide

-- (13), p. 91: no functional head over a bare root.
example : ¬ Converges [.root, .functional X] := by cases X <;> decide

-- (10), p. 117: one `[V]` and three `[uV]`.
example : Converges [.v, .functional .V, .functional .V, .functional .V] := by decide

-- (17), p. 126: a `[uN]` head over a verbal line.
example : ¬ Converges [.v, .functional .V, .functional .N] := by decide

-- (18), p. 126: the lexical heads merged first and the functional heads above them.
example : ¬ Converges [.n, .v, .functional .V, .functional .N] := by decide

-- (19), p. 127: no line of functional heads alone.
example : ¬ Converges [.functional .V, .functional .V, .functional .V] := by decide

-- (20), p. 128: a lexical head merged over two functional heads.
example : ¬ Converges [.functional .V, .functional .V, .v] := by decide

-- (29), p. 132: no line begins with two functional heads.
example : ¬ Converges [.functional X, .functional Y] := by cases X <;> cases Y <;> decide

-- (30) and n. 22, p. 132: `[DP D n]` converges without a root and `[DP D Num]` does not.
example : Converges [.n, .functional .N] ∧ ¬ Converges [.functional .N, .functional .N] := by
  decide

-- (21), p. 145: *Albert's eating herring*, a nominal line over a verbal one.
example : Converges [.v, .functional .V, .switch .N .V, .functional .N] ∧
    category [.v, .functional .V, .switch .N .V, .functional .N] = some .N := by
  decide

-- (24), p. 147: the head merged over a Switch bears `[uN]`, not `[uV]`.
example : ¬ Converges [.root, .v, .functional .V, .functional .V, .switch .N .V,
    .functional .V] := by
  decide

-- (25), p. 147: two `[uN]` heads over a Switch over two `[uV]` heads.
example : Converges [.root, .v, .functional .V, .functional .V, .switch .N .V, .functional .N,
    .functional .N] := by
  decide

-- p. 156 and (70), p. 171: categorial Agree alone admits flip-flopping through a verbalizing
-- Switch and a lexical nominalizer over functional structure.
example : Converges [.v, .functional .V, .switch .N .V, .functional .N, .switch .V .N,
      .functional .V] ∧
    Converges [.root, .v, .functional .V, .n, .functional .N] := by
  decide

/-! ### Categorial Deficiency over the families -/

/-- (9), p. 89: `[N]` is interpretable on *n* and `[V]` on *v*. -/
def CategorialFeature.categorizer : CategorialFeature → Cat
  | .N => .n
  | .V => .v

/-- The categorial feature of a family: `[N]` for the nominal family and `[V]` for the verbal. -/
def CategorialFeature.ofFamily? : CatFamily → Option CategorialFeature
  | .nominal => some .N
  | .verbal => some .V
  | .adjectival | .adpositional => none

@[simp] theorem CategorialFeature.ofFamily?_family_categorizer (X : CategorialFeature) :
    ofFamily? X.categorizer.family = some X := by
  cases X <;> rfl

/-- (9), p. 117: in the nominal and verbal families the categorizer bears the feature of the
family interpretably, the lexical head is the root, and every other head bears the uninterpretable
version. -/
def Head.ofCat (c : Cat) : Option Head :=
  (CategorialFeature.ofFamily? c.family).map fun X ↦
    if c = X.categorizer then .categorizer X else if c = c.family.lexical then .root
    else .functional X

private theorem mapM_eq_some_map {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => by simp
  | a :: l, h => by
    simp [List.mapM_cons, h a List.mem_cons_self,
      mapM_eq_some_map (g := g) fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

/-- An extended projection that begins at the categorizer *n* or *v* converges. -/
theorem exists_converges_of_isExtendedProjection {s : Spine} (hs : s.IsExtendedProjection)
    (hX : s.heads.head? = some X.categorizer) : ∃ l ∈ s.heads.mapM Head.ofCat, Converges l := by
  obtain ⟨t, ht⟩ : ∃ t, s.heads = X.categorizer :: t := by
    cases hh : s.heads with
    | nil => simp [hh] at hX
    | cons c t => exact ⟨t, by simp_all⟩
  have hp := hs.pairwise
  rw [ht, List.pairwise_cons] at hp
  let g : Cat → Head := fun c ↦
    if c = X.categorizer then .categorizer X else if c = c.family.lexical then .root
    else .functional X
  have hg : ∀ c ∈ X.categorizer :: t, Head.ofCat c = some (g c) := fun c hc ↦ by
    have hcf : c.family = X.categorizer.family := by
      rcases List.mem_cons.1 hc with rfl | hc
      · rfl
      · exact (hp.1 c hc).family_eq.symm
    simp [Head.ofCat, hcf, g]
  refine ⟨_, by rw [ht]; exact mapM_eq_some_map hg, ?_⟩
  have hg₀ : g X.categorizer = ⟨some X, none⟩ := by simp [g, Head.categorizer]
  rw [List.map_cons, hg₀]
  refine converges_cons_of_forall_mem fun h hh ↦ ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hh
  simp only [g]
  split_ifs <;> simp [Head.categorizer, Head.root, Head.functional]

-- The finite clause `[V, v, T, C]`, the root below the verbalizer.
example : ∃ l ∈ Spine.cP.heads.mapM Head.ofCat, Converges l := by decide

-- p. 111: D merges only in the projection line of N and T only in that of V.
example : (∀ l ∈ [Cat.v, .T, .D].mapM Head.ofCat, ¬ Converges l) ∧
    ∀ l ∈ [Cat.n, .D, .T].mapM Head.ofCat, ¬ Converges l := by
  decide

-- (10), p. 90: no NumP or VoiceP over a bare root.
example : (∀ l ∈ [Cat.N, .Num].mapM Head.ofCat, ¬ Converges l) ∧
    ∀ l ∈ [Cat.V, .Voice].mapM Head.ofCat, ¬ Converges l := by
  decide

end Panagiotidis2015
