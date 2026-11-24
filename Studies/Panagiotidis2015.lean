module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Minimalist.Spine

/-!
# Panagiotidis (2015): Categorial Features

The categorial features `[N]` and `[V]` impose a sortal and an extending-into-time perspective on
the complement of the head that bears them. A head bears at most one of them interpretably and at
most one uninterpretably. A categorizer, *n* or *v*, bears an interpretable feature and is a
lexical head. A functional head bears an uninterpretable one, that of the lexical head at the foot
of its projection line (Categorial Deficiency). A Switch bears both, as the head of a gerund bears
`[N]` beside `[uV]`, and a root bears neither.

A projection line is the list of heads a phrase projects, from the bottom up, and it is built by
merging one head at a time. A projection has a category, the interpretable feature of its highest
categorizer, which is the feature of the head that a probe halted by any interpretable categorial
feature finds in it. A head merges over a projection when each of its uninterpretable features
`[uX]` finds `[X]` as that category (categorial Agree), and a line converges when every head of it
merges. Merge is taken relative to a relation `L` between projections and heads, which says what
may merge over what, so that restrictions on the heads of a grammar are compared as relations.

Under any licensing a head merged over material without a categorizer bears no uninterpretable
feature, so a functional head takes no bare root as its complement. The functional heads of a
line whose categorizers all bear `[X]` all bear `[uX]`, which is biuniqueness. Between two heads
with different uninterpretable features there is a categorizer, which may be the lower of the two.
Of two heads that merge, a head with an uninterpretable feature is the one that projects: a line
that begins with such a head does not converge, while heads without one merge in either order, so
categorial Agree labels the first kind of merger and is silent on the second.

The book adds a division of labour: a categorizer without an uninterpretable feature merges over
lexical material only, and the only head with both features is the Switch `[N][uV]`, which merges
over functional structure only. Under it every head that merges over a nominal projection with
functional structure leaves it so, so no `[uV]` head lies above a `[uN]` head, which is Phrasal
Coherence, and a line through a Switch is nominal. Categorial Agree alone licenses more lines than
the division of labour does.

With the features of the substrate's nominal and verbal categories read off their families, an
extended projection that begins at its categorizer converges.

## Implementation notes

A projection line records the head that projects at each application of Merge, so specifiers and
the label of a phrase merged with a phrase are not represented. A labelling prediction for two
heads is read as which of the two orders converges: one order, the head that projects; neither, a
merger that crashes; both, a merger that categorial Agree does not label.

Besides its category a projection records whether a head with an uninterpretable feature has been
merged, which is what the division of labour reads.

In `Head.ofCat` the lexical head of a family is the root, as in the substrate's citation of the
book, so a spine that leaves out the categorizer is functional structure over a bare root.
Adjectival and adpositional heads have no image: the book leaves the features of adjectives open
and does not take adpositions to form a category of this system. The families with an image are
those specified for a single categorial feature.

## TODO

The licensing of roots by a categorizer at the interface, the phasehood of categorizers and
Switches, and the size of the complement of a Switch are not formalized.

## References

* [panagiotidis-2015]
* [grimshaw-2005]
* [embick-marantz-2008]
-/

@[expose] public section

namespace Panagiotidis2015

open Minimalist

/-- The categorial features of a head, `N` a sortal perspective and `V` a perspective extending
into time ((7), p. 84). -/
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

/-! ### Projections -/

/-- Whether a projection contains a head with an uninterpretable feature. -/
inductive Layer where
  | lexical
  | functional
  deriving DecidableEq, Repr

/-- A projection as the next head to merge finds it. -/
structure Projection where
  /-- The interpretable feature of the highest categorizer, by which the phrase is identified
  externally. -/
  category : Option CategorialFeature := none
  /-- Whether a head with an uninterpretable feature has been merged. -/
  layer : Layer := .lexical
  deriving DecidableEq, Repr

namespace Projection

/-- The projection with no head, or with roots alone. -/
def bare : Projection := {}

/-- The projection of the head `h` merged over `p`. -/
def merge (p : Projection) (h : Head) : Projection :=
  ⟨h.interpretable.or p.category, if h.uninterpretable = none then p.layer else .functional⟩

end Projection

variable {l l₁ l₂ l₃ : List Head} {h h' k : Head} {p q : Projection} {X Y : CategorialFeature}

/-- (14) and (16), pp. 125–126, with the minimality of p. 147: the head `h` agrees with the
projection `p` when its uninterpretable feature `[uX]` finds `[X]` as the category of `p`. -/
def Head.Agrees (h : Head) (p : Projection) : Prop :=
  ∀ X ∈ h.uninterpretable, p.category = some X

instance : Decidable (h.Agrees p) := inferInstanceAs (Decidable (∀ X ∈ _, _))

/-! ### Merge under categorial Agree -/

section Agree

variable (L : Projection → Head → Prop) [DecidableRel L]

/-- The projection of `h` merged over `p`, when `L` licenses the merger and `h` agrees with
`p`. -/
def Projection.merge? (p : Projection) (h : Head) : Option Projection :=
  if L p h ∧ h.Agrees p then some (p.merge h) else none

/-- The projection of the line `l` merged over `p` head by head, when every head merges. -/
def Projection.extend (p : Projection) (l : List Head) : Option Projection :=
  l.foldlM (Projection.merge? L) p

/-- A projection line converges when every head of it merges. -/
def Converges (l : List Head) : Prop := (Projection.bare.extend L l).isSome

instance : DecidablePred (Converges L) := fun _ ↦ inferInstanceAs (Decidable (_ = true))

variable {L}

@[simp] theorem merge?_eq_some : p.merge? L h = some q ↔ L p h ∧ h.Agrees p ∧ p.merge h = q := by
  simp [Projection.merge?, and_assoc]

@[simp] theorem extend_nil : p.extend L [] = some p := rfl

@[simp] theorem extend_cons : p.extend L (h :: l) = (p.merge? L h).bind (·.extend L l) :=
  List.foldlM_cons

theorem extend_append : p.extend L (l₁ ++ l₂) = (p.extend L l₁).bind (·.extend L l₂) :=
  List.foldlM_append

theorem converges_iff : Converges L l ↔ ∃ q, Projection.bare.extend L l = some q :=
  Option.isSome_iff_exists

theorem extend_append_cons_eq_some :
    p.extend L (l₁ ++ h :: l₂) = some q ↔ ∃ p₁, p.extend L l₁ = some p₁ ∧
      L p₁ h ∧ h.Agrees p₁ ∧ (p₁.merge h).extend L l₂ = some q := by
  simp [extend_append, Option.bind_eq_some_iff, and_assoc]

-- A line that converges under a licensing converges under any weaker one.
theorem extend_mono {L' : Projection → Head → Prop} [DecidableRel L']
    (hL : ∀ p h, L p h → L' p h) :
    ∀ {l : List Head} {p : Projection}, p.extend L l = some q → p.extend L' l = some q
  | [], _, hq => hq
  | h :: l, p, hq => by
    rw [extend_cons, Option.bind_eq_some_iff] at hq ⊢
    obtain ⟨p₁, hp₁, hq⟩ := hq
    obtain ⟨hl, ha, rfl⟩ := merge?_eq_some.1 hp₁
    exact ⟨_, merge?_eq_some.2 ⟨hL _ _ hl, ha, rfl⟩, extend_mono hL hq⟩

theorem Converges.mono {L' : Projection → Head → Prop} [DecidableRel L']
    (hL : ∀ p h, L p h → L' p h) (hl : Converges L l) : Converges L' l :=
  let ⟨q, hq⟩ := converges_iff.1 hl
  converges_iff.2 ⟨q, extend_mono hL hq⟩

/-- The probe that any head with an interpretable categorial feature halts. -/
def categorialProbe : Probe Head := .relativized (·.interpretable ≠ none)

/-- The category of a projection is the feature of the head the categorial probe finds in the
line, searched from the top, or the category of the projection the line was merged over. -/
theorem category_of_extend (hq : p.extend L l = some q) :
    q.category = ((categorialProbe.search l.reverse).bind Head.interpretable).or p.category := by
  induction l using List.reverseRecOn generalizing q with
  | nil =>
    obtain rfl : p = q := by simpa using hq
    simp [Probe.search]
  | append_singleton l h ih =>
    obtain ⟨p₁, hp₁, -, -, hq⟩ := extend_append_cons_eq_some.1 hq
    obtain rfl : p₁.merge h = q := by simpa using hq
    cases hi : h.interpretable <;>
      simp [Projection.merge, ih hp₁, Probe.search, categorialProbe, hi]

theorem category_eq_of_forall (hq : p.extend L l = some q)
    (hl : ∀ k ∈ l, k.interpretable = none) : q.category = p.category := by
  have : categorialProbe.search l.reverse = none :=
    Probe.search_eq_none_iff.2 fun a ha ↦ by simpa [categorialProbe] using hl a (by simpa using ha)
  simp [category_of_extend hq, this]

theorem exists_mem_of_category (hq : p.extend L l = some q)
    (hX : q.category = some X) : p.category = some X ∨ ∃ k ∈ l, k.interpretable = some X := by
  rw [category_of_extend hq] at hX
  cases hs : categorialProbe.search l.reverse with
  | none => exact .inl (by simpa [hs] using hX)
  | some k =>
    have hk : k ∈ l := by simpa using List.mem_of_find?_eq_some hs
    cases hi : k.interpretable with
    | none => exact .inl (by simpa [hs, hi] using hX)
    | some Y => exact .inr ⟨k, hk, by simpa [hs, hi] using hX⟩

/-- A head merged over material without a categorizer bears no uninterpretable feature, so a
functional head takes no bare root as its complement, the part of the Categorization Assumption of
[embick-marantz-2008] that categorial Agree derives. -/
theorem Converges.uninterpretable_eq_none (hl : Converges L (l₁ ++ h :: l₂))
    (h₁ : ∀ k ∈ l₁, k.interpretable = none) : h.uninterpretable = none := by
  obtain ⟨q, hq⟩ := converges_iff.1 hl
  obtain ⟨p₁, hp₁, -, ha, -⟩ := extend_append_cons_eq_some.1 hq
  refine Option.eq_none_iff_forall_ne_some.2 fun X hX ↦ ?_
  simpa [category_eq_of_forall hp₁ h₁, Projection.bare] using ha X hX

/-- Biuniqueness: in a convergent line whose categorizers all bear `[X]`, every functional head
bears `[uX]`. -/
theorem Converges.uninterpretable_eq (hl : Converges L l)
    (hX : ∀ h ∈ l, ∀ Y ∈ h.interpretable, Y = X) : ∀ h ∈ l, ∀ Y ∈ h.uninterpretable, Y = X := by
  intro h hh Y hY
  obtain ⟨q, hq⟩ := converges_iff.1 hl
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hh
  obtain ⟨p₁, hp₁, -, ha, -⟩ := extend_append_cons_eq_some.1 hq
  rcases exists_mem_of_category hp₁ (ha Y hY) with hb | ⟨k, hk, hkY⟩
  · simp [Projection.bare] at hb
  · exact hX k (List.mem_append_left _ hk) Y hkY

-- The category of a line switches only at a categorizer, which may be the lower of the two heads.
theorem Converges.exists_mem_interpretable_of_ne
    (hl : Converges L (l₁ ++ h :: l₂ ++ h' :: l₃)) (hX : X ∈ h.uninterpretable)
    (hY : Y ∈ h'.uninterpretable) (hne : Y ≠ X) : ∃ k ∈ h :: l₂, k.interpretable = some Y := by
  obtain ⟨q, hq⟩ := converges_iff.1 hl
  obtain ⟨p₂, hp₂, -, ha', -⟩ := extend_append_cons_eq_some.1 hq
  obtain ⟨p₁, hp₁, hlh, ha, hp₂⟩ := extend_append_cons_eq_some.1 hp₂
  have h₂ : p₁.extend L (h :: l₂) = some p₂ :=
    (extend_append_cons_eq_some (l₁ := [])).2 ⟨p₁, rfl, hlh, ha, hp₂⟩
  refine (exists_mem_of_category h₂ (ha' Y hY)).resolve_left fun h₁ ↦ hne ?_
  exact Option.some.inj (h₁.symm.trans (ha X hX))

end Agree

/-! ### The division of labour between categorizers -/

/-- No restriction beyond categorial Agree. -/
def Free (_ : Projection) (_ : Head) : Prop := True

instance : DecidableRel Free := fun _ _ ↦ instDecidableTrue

/-- pp. 171–172: lexical categorizers categorize lexical material, and functional structure is
recategorized by a Switch, which nominalizes. -/
@[mk_iff]
structure DivisionOfLabour (p : Projection) (h : Head) : Prop where
  /-- A categorizer without an uninterpretable feature merges over lexical material. -/
  lexical : h.interpretable ≠ none → h.uninterpretable = none → p.layer = .lexical
  /-- A head with both features is the Switch `[N][uV]`. -/
  switch : h.interpretable ≠ none → h.uninterpretable ≠ none → h = .switch .N .V
  /-- A Switch merges over functional structure. -/
  functional : h.interpretable ≠ none → h.uninterpretable ≠ none → p.layer = .functional

instance : DecidableRel DivisionOfLabour := fun p h ↦
  decidable_of_iff' _ (divisionOfLabour_iff p h)

theorem merge?_nominal_functional
    (hq : (⟨some .N, .functional⟩ : Projection).merge? DivisionOfLabour h = some q) :
    q = ⟨some .N, .functional⟩ := by
  obtain ⟨hd, ha, rfl⟩ := merge?_eq_some.1 hq
  cases hi : h.interpretable with
  | none => simp [Projection.merge, hi]
  | some X =>
    by_cases hu : h.uninterpretable = none
    · simpa using hd.lexical (by simp [hi]) hu
    · simp [Projection.merge, hd.switch (by simp [hi]) hu, Head.switch]

-- Under the division of labour a nominal projection with functional structure stays one.
theorem extend_nominal_functional : ∀ {l : List Head},
    (⟨some .N, .functional⟩ : Projection).extend DivisionOfLabour l = some q →
      q = ⟨some .N, .functional⟩
  | [], hq => (Option.some.inj hq).symm
  | h :: l, hq => by
    rw [extend_cons, Option.bind_eq_some_iff] at hq
    obtain ⟨p₁, hp₁, hq⟩ := hq
    rw [merge?_nominal_functional hp₁] at hq
    exact extend_nominal_functional hq

theorem merge_of_uninterpretable_eq_N (hd : DivisionOfLabour p h) (ha : h.Agrees p)
    (hN : h.uninterpretable = some .N) : p.merge h = ⟨some .N, .functional⟩ := by
  have hi : h.interpretable = none := by
    by_contra hi
    simp [hd.switch hi (by simp [hN]), Head.switch] at hN
  simp [Projection.merge, hi, hN, ha .N hN]

/-- Phrasal Coherence: under the division of labour no head bearing `[uV]` lies above a head
bearing `[uN]` in a convergent line. -/
theorem Converges.phrasal_coherence
    (hl : Converges DivisionOfLabour (l₁ ++ h :: l₂ ++ h' :: l₃))
    (hN : h.uninterpretable = some .N) : h'.uninterpretable ≠ some .V := by
  obtain ⟨q, hq⟩ := converges_iff.1 hl
  obtain ⟨p₂, hp₂, -, ha', -⟩ := extend_append_cons_eq_some.1 hq
  obtain ⟨p₁, -, hd, ha, hp₂⟩ := extend_append_cons_eq_some.1 hp₂
  rw [merge_of_uninterpretable_eq_N hd ha hN] at hp₂
  obtain rfl := extend_nominal_functional hp₂
  exact fun hV ↦ by simpa using ha' .V hV

-- (8), p. 139, and p. 161: under the division of labour a line through a Switch is nominal.
theorem category_eq_of_switch_mem (hq : Projection.bare.extend DivisionOfLabour l = some q)
    (hk : Head.switch .N .V ∈ l) : q.category = some .N := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hk
  obtain ⟨p₁, -, -, -, hq⟩ := extend_append_cons_eq_some.1 hq
  have : p₁.merge (.switch .N .V) = ⟨some .N, .functional⟩ := by
    simp [Projection.merge, Head.switch]
  rw [this] at hq
  rw [extend_nominal_functional hq]

theorem extend_free_of_forall : ∀ {l : List Head} {p : Projection},
    (∀ h ∈ l, h.uninterpretable = none) → ∃ q, p.extend Free l = some q
  | [], p, _ => ⟨p, rfl⟩
  | h :: l, p, hl => by
    obtain ⟨q, hq⟩ := extend_free_of_forall (p := p.merge h)
      fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)
    have hm : p.merge? Free h = some (p.merge h) :=
      merge?_eq_some.2 ⟨trivial, fun X hX ↦ by simp [hl h List.mem_cons_self] at hX, rfl⟩
    exact ⟨q, by simp [hm, hq]⟩

-- Categorial Agree alone is silent on heads without an uninterpretable feature.
theorem converges_free_of_forall (hl : ∀ h ∈ l, h.uninterpretable = none) : Converges Free l :=
  converges_iff.2 (extend_free_of_forall hl)

/-! ### The book's structures

A structure the book derives converges under the division of labour, and so under categorial
Agree alone; a structure it stars does not converge under categorial Agree alone, and so under no
licensing. -/

-- (6), p. 63: the denominal verb *tape*, a verbalizer over a nominalized root.
example : ∃ q ∈ Projection.bare.extend DivisionOfLabour [.root, .n, .v], q.category = some .V := by
  decide

-- (13), p. 91: no functional head over a bare root.
example : ¬ Converges Free [.root, .functional X] := by cases X <;> decide

-- (10), p. 117: one `[V]` and three `[uV]`.
example : Converges DivisionOfLabour [.v, .functional .V, .functional .V, .functional .V] := by
  decide

-- (17), p. 126: a `[uN]` head over a verbal line.
example : ¬ Converges Free [.v, .functional .V, .functional .N] := by decide

-- (18), p. 126: the lexical heads merged first and the functional heads above them.
example : ¬ Converges Free [.n, .v, .functional .V, .functional .N] := by decide

-- (19), p. 127: no line of functional heads alone.
example : ¬ Converges Free [.functional .V, .functional .V, .functional .V] := by decide

-- (20), p. 128: a lexical head merged over two functional heads.
example : ¬ Converges Free [.functional .V, .functional .V, .v] := by decide

-- (21), p. 145: *Albert's eating herring*, a nominal line over a verbal one.
example : ∃ q ∈ Projection.bare.extend DivisionOfLabour
    [.v, .functional .V, .switch .N .V, .functional .N], q.category = some .N := by
  decide

-- (24), p. 147: the head merged over a Switch bears `[uN]`, not `[uV]`.
example : ¬ Converges Free [.root, .v, .functional .V, .functional .V, .switch .N .V,
    .functional .V] := by
  decide

-- (25), p. 147: two `[uN]` heads over a Switch over two `[uV]` heads.
example : Converges DivisionOfLabour [.root, .v, .functional .V, .functional .V, .switch .N .V,
    .functional .N, .functional .N] := by
  decide

-- p. 156: flip-flopping through a verbalizing Switch.
example : Converges Free [.v, .functional .V, .switch .N .V, .functional .N, .switch .V .N,
      .functional .V] ∧
    ¬ Converges DivisionOfLabour [.v, .functional .V, .switch .N .V, .functional .N,
      .switch .V .N, .functional .V] := by
  decide

-- (70), p. 171: a lexical nominalizer over functional structure.
example : Converges Free [.root, .v, .functional .V, .n, .functional .N] ∧
    ¬ Converges DivisionOfLabour [.root, .v, .functional .V, .n, .functional .N] := by
  decide

-- p. 164: a Switch over purely lexical material.
example : Converges Free [.root, .v, .switch .N .V] ∧
    ¬ Converges DivisionOfLabour [.root, .v, .switch .N .V] := by
  decide

/-! ### Labelling

The rows of (30), p. 132, for two heads, in the two orders in which one could project. -/

-- (29) and n. 22: two functional heads, as `*[T Asp]` and a pronoun `*[DP D Num]` without *n*.
example : ¬ Converges Free [.functional X, .functional Y] := by cases X <;> cases Y <;> decide

-- (23): a functional head and a lexical head, as `[DP D n]`; the functional head projects.
example : Converges DivisionOfLabour [.categorizer X, .functional X] ∧
    ¬ Converges Free [.functional X, .categorizer X] := by
  cases X <;> decide

-- (26): a functional head and a phrase, as `[DP the [NumP three little ducks]]`.
example : Converges DivisionOfLabour [.n, .functional .N, .functional .N] := by decide

-- A functional head and a root, as `*[Num cat]`.
example : ¬ Converges Free [.root, .functional X] ∧ ¬ Converges Free [.functional X, .root] := by
  cases X <;> decide

-- Two lexical heads, and a lexical head and a root as `[nP n cat]`: not labelled.
example : Converges Free [.categorizer X, .categorizer Y] ∧
    Converges Free [.categorizer Y, .categorizer X] ∧
    Converges Free [.root, .categorizer X] ∧ Converges Free [.categorizer X, .root] :=
  ⟨converges_free_of_forall (by simp [Head.categorizer]),
    converges_free_of_forall (by simp [Head.categorizer]),
    converges_free_of_forall (by simp [Head.categorizer, Head.root]),
    converges_free_of_forall (by simp [Head.categorizer, Head.root])⟩

/-! ### Categorial Deficiency over the families -/

/-- (9), p. 89: `[N]` is interpretable on *n* and `[V]` on *v*. -/
def categorizerOf : CategorialFeature → Cat
  | .N => .n
  | .V => .v

/-- The categorial feature of a family: `[N]` for the nominal family and `[V]` for the verbal. -/
def ofFamily? : CatFamily → Option CategorialFeature
  | .nominal => some .N
  | .verbal => some .V
  | .adjectival | .adpositional => none

@[simp] theorem ofFamily?_family_categorizerOf (X : CategorialFeature) :
    ofFamily? (categorizerOf X).family = some X := by
  cases X <;> rfl

-- The families with a feature are those the features `[±V, ±N]` specify for it alone.
theorem ofFamily?_eq_some_iff {f : CatFamily} : ofFamily? f = some X ↔ f.features = {X} := by
  cases f <;> cases X <;> decide

/-- (9), p. 117: in the nominal and verbal families the categorizer bears the feature of the
family interpretably, the lexical head is the root, and every other head bears the uninterpretable
version. -/
def Head.ofCat (c : Cat) : Option Head :=
  (ofFamily? c.family).map fun X ↦
    if c = categorizerOf X then Head.categorizer X else if c = c.family.lexical then Head.root
    else Head.functional X

/-- The projection of the categories `t` merged over `p` one by one, when each has a head that
merges. -/
def Projection.extendCat (L : Projection → Head → Prop) [DecidableRel L] (p : Projection)
    (t : List Cat) : Option Projection :=
  t.foldlM (fun p c ↦ (Head.ofCat c).bind (p.merge? L)) p

@[simp] theorem extendCat_cons {L : Projection → Head → Prop} [DecidableRel L] {c : Cat}
    {t : List Cat} :
    p.extendCat L (c :: t) = ((Head.ofCat c).bind (p.merge? L)).bind (·.extendCat L t) :=
  List.foldlM_cons

theorem exists_ofCat_of_family_eq {c : Cat} (hc : c.family = (categorizerOf X).family) :
    ∃ h, Head.ofCat c = some h ∧ (∀ Y ∈ h.interpretable, Y = X) ∧
      ∀ Y ∈ h.uninterpretable, Y = X := by
  simp only [Head.ofCat, hc, ofFamily?_family_categorizerOf, Option.map_some]
  split_ifs <;> refine ⟨_, rfl, ?_, ?_⟩ <;>
    simp [Head.categorizer, Head.root, Head.functional, eq_comm]

theorem extendCat_of_family_eq : ∀ {t : List Cat} {p : Projection}, p.category = some X →
    (∀ c ∈ t, c.family = (categorizerOf X).family) →
      ∃ q, p.extendCat Free t = some q ∧ q.category = some X
  | [], p, hp, _ => ⟨p, rfl, hp⟩
  | c :: t, p, hp, ht => by
    obtain ⟨h, hc, hi, hu⟩ := exists_ofCat_of_family_eq (ht c List.mem_cons_self)
    have hm : p.merge? Free h = some (p.merge h) :=
      merge?_eq_some.2 ⟨trivial, fun Y hY ↦ by rw [hp, hu Y hY], rfl⟩
    have hcat : (p.merge h).category = some X := by
      cases hi' : h.interpretable with
      | none => simp [Projection.merge, hi', hp]
      | some Y => simp [Projection.merge, hi', hi Y hi']
    obtain ⟨q, hq, hqX⟩ :=
      extendCat_of_family_eq hcat fun d hd ↦ ht d (List.mem_cons_of_mem _ hd)
    exact ⟨q, by simp [hc, hm, hq], hqX⟩

/-- An extended projection that begins at the categorizer *n* or *v* converges, with the category
of the categorizer. -/
theorem exists_extendCat_of_isExtendedProjection {s : Spine Cat} (hs : s.IsExtendedProjection)
    (hX : s.heads.head? = some (categorizerOf X)) :
    ∃ q, Projection.bare.extendCat Free s.heads = some q ∧ q.category = some X := by
  obtain ⟨t, ht⟩ : ∃ t, s.heads = categorizerOf X :: t := by
    cases hh : s.heads with
    | nil => simp [hh] at hX
    | cons c t => exact ⟨t, by simp_all⟩
  have hp := hs.pairwise
  rw [ht, List.pairwise_cons] at hp
  obtain ⟨q, hq, hqX⟩ := extendCat_of_family_eq (p := ⟨some X, .lexical⟩) rfl
    fun c hc ↦ (hp.1 c hc).family_eq.symm
  have h₀ : Head.ofCat (categorizerOf X) = some (.categorizer X) := by simp [Head.ofCat]
  have hm : Projection.bare.merge? Free (.categorizer X) = some ⟨some X, .lexical⟩ := by
    simp [Free, Head.Agrees, Head.categorizer, Projection.merge, Projection.bare]
  exact ⟨q, by simp [ht, h₀, hm, hq], hqX⟩

-- The finite clause `[V, v, T, C]`, the root below the verbalizer.
example : ∃ q ∈ Projection.bare.extendCat DivisionOfLabour Spine.cP.heads,
    q.category = some .V := by
  decide

-- p. 111: D merges only in the projection line of N and T only in that of V.
example : Projection.bare.extendCat Free [.v, .T, .D] = none ∧
    Projection.bare.extendCat Free [.n, .D, .T] = none := by
  decide

-- (10), p. 90: no NumP or VoiceP over a bare root.
example : Projection.bare.extendCat Free [.N, .Num] = none ∧
    Projection.bare.extendCat Free [.V, .Voice] = none := by
  decide

end Panagiotidis2015
