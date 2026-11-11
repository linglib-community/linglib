module

public import Linglib.Data.Examples.HymanMchombo1992
public import Linglib.Fragments.Chichewa.Verbs
public import Linglib.Fragments.Chichewa.Voice
public import Linglib.Phonology.OCP
public import Linglib.Data.Examples.Readers
public import Studies.Baker1985

/-!
# Hyman and Mchombo 1992: morphotactic constraints in the Chichewa verb stem

The Chichewa verbal suffixes are spelled out cyclically in order of scope, but a feature may first
mark off, or circumscribe, the final morph of its base. A pair of suffixes [surfaces in an order
exactly when valency, the Repeated Morph Constraint (RMC) and circumscription allow
it](##occurs_iff), and circumscription makes the negative filters
[redundant](##filtered_of_mem_spellOut). An applicative on a reciprocal base spells *-an-* again,
a morph [the RMC does not see](##rows_doubled), and [the only starred stem the account derives is
*mang-ir-an-its-*](##rows_spellOut). The order of applicative and passive follows the applied role
on the thematic hierarchy, [not the passive subject](##rows_passive).

## Implementation notes

* A feature's valency effect is that of the voice the fragment assigns it, added to or removed
  from any base; a voice that removes a core argument needs a base with at least the valency of
  its initial frame. The intensive, an adverbial, has no voice.
* The intensive is spelled out by the causative morph with a high tone (5b), so the RMC treats
  the two alike; the tone is written in capitals and the intensive reduplicates before another
  suffix (5a). As an adverbial it takes widest scope, so (3d), (7c) and (7d) owe its early
  position to circumscription (fn. 16).
* The causative marks off one morph after another (18), every other feature at most one
  (fn. 16), and a cycle leaving an obligatory circumscription undone has no output. The
  applicative spells *-an-* again on a base containing a reciprocal (24) unless the base's own
  *-an-* was marked off (22); the rule block's respelling of *-ir-* on a reciprocal cycle, which
  the RMC blocks in (24a), is omitted.
* The RMC is Menn and MacWhinney's constraint on two adjacent affixes, which Chichewa obeys by
  blocking the derivation (fn. 4). It skips the doubled *-an-*, the second of the paper's two
  explanations of (25), which it supports with (25b). The rows write a doubled *-an-* as `(R)`,
  after the label of (12c).
* Rows marked ? or ?* carry no claim beyond (25). The passive subjects of (27)–(30) are
  compared with Baker's rules applied, in the order of the suffixes, to a transitive root with
  an applied oblique.

## TODO

* The anti-cyclic spell-out the authors propose after (34), which fixes the causative's position
  before the other features are spelled out; the paper does not specify it further.
* The Cibemba data (20) and the phonological case for cyclic spell-out.
* The RMC between an affix and the end of the stem, by which fn. 4 bars the intensive after a stem
  ending in [ts] (*\*uts-ITS-*) but not after *opsy-* (*opsy-ETS-*).

## References

* [hyman-mchombo-1992]
* [menn-macwhinney-1984]
* [baker-1985]
* [creissels-2024]
-/

@[expose] public section

namespace HymanMchombo1992

open Morphology

/-! ### Features, suffixes and the RMC -/

/-- The morphosyntactic features the verbal suffixes spell out (1). -/
inductive Feature where
  | causative
  | applicative
  | reciprocal
  | passive
  | intensive
  deriving DecidableEq, Repr, Fintype

/-- An input lists the features in order of scope, innermost first (2). -/
abbrev Input := List Feature

namespace Feature

/-- The voice a feature realizes; the intensive, an adverbial, realizes none. -/
def voice? : Feature → Option Voice
  | causative => some Chichewa.causative
  | applicative => some Chichewa.applicative
  | reciprocal => some Chichewa.reciprocal
  | passive => some Chichewa.passive
  | intensive => none

/-- The morphs that spell out a feature are its voice's marker, and for the intensive the
causative's (5b). -/
def morphs : Feature → List Morph
  | causative | intensive => Chichewa.causative.marker
  | applicative => Chichewa.applicative.marker
  | reciprocal => Chichewa.reciprocal.marker
  | passive => Chichewa.passive.marker

end Feature

open Feature

/-- A suffix spells out a feature on its own cycle, or is the reciprocal *-an-* that an
applicative spells out a second time on a base containing a reciprocal (24), underlined in the
paper. -/
inductive Suffix where
  | spell (f : Feature)
  | doubled
  deriving DecidableEq, Repr

/-- The feature a suffix spells out; the doubled *-an-* spells the percolated reciprocal. -/
def Suffix.feature : Suffix → Feature
  | spell f => f
  | doubled => reciprocal

/-- A stem lists the suffixes that follow the root, in surface order. -/
abbrev Stem := List Suffix

/-- The Repeated Morph Constraint of [menn-macwhinney-1984] bars two features spelled out in
succession by the same morphs (4b): the OCP on the morph tier of the suffixes spelled out on their
own cycles. -/
abbrev RMC (s : Stem) : Prop :=
  OCP.IsCleanOn (· ≠ Suffix.doubled) (Feature.morphs ∘ Suffix.feature) s

/-! ### Cyclic spell-out -/

/-- Whether a circumscription must or may apply. -/
inductive Circumscription where
  | obligatory
  | optional
  deriving DecidableEq, Repr

/-- A set of circumscription rules says what the spell-out of `f` does to a base ending in the
morph of `g`. -/
abbrev Rules := Feature → Feature → Option Circumscription

/-- The rules (15) and (22) mark off *-ir-* and *-idw-* within the scope of the causative or the
intensive, and may mark off *-an-* within the scope of the applicative. -/
def rules₀ : Rules
  | causative, applicative | causative, passive | intensive, applicative
  | intensive, passive => some .obligatory
  | applicative, reciprocal => some .optional
  | _, _ => none

/-- With (36), the rules may also mark off *-an-* within the scope of the causative or the
intensive. -/
def rules : Rules
  | causative, reciprocal | intensive, reciprocal => some .optional
  | f, g => rules₀ f g

/-- The ways the spell-out of `f` splits a stem into the suffixes it keeps and the suffixes it
marks off: every marked-off suffix falls under a rule for `f`, only the causative marks off more
than one (18, fn. 16), and the last kept suffix is not one that `f` must mark off. -/
def splits (K : Rules) (f : Feature) (s : Stem) : List (Stem × Stem) :=
  ((List.range (s.length + 1)).map fun j ↦ (s.take j, s.drop j)).filter fun km ↦
    decide ((∀ x ∈ km.2, K f x.feature ≠ none) ∧ (f = causative ∨ km.2.length ≤ 1) ∧
      ∀ x ∈ km.1.getLast?, K f x.feature ≠ some .obligatory)

/-- The *-an-* the applicative spells out again on a base containing a reciprocal, whose feature
percolates from anywhere in the base (24), unless the base's own *-an-* was marked off (22). -/
def doubling (f : Feature) (s m : Stem) : Stem :=
  if f = applicative ∧ .spell reciprocal ∈ s ∧ m.head?.map Suffix.feature ≠ some reciprocal then
    [.doubled]
  else []

/-- A cycle spells out `f` on a stem `s` by placing the new morph after the kept suffixes and
before the marked-off ones; the RMC blocks a result that repeats a morph. -/
def cycle (K : Rules) (f : Feature) (s : Stem) : List Stem :=
  ((splits K f s).map fun km ↦ km.1 ++ .spell f :: (doubling f s km.2 ++ km.2)).filter
    fun t ↦ decide (RMC t)

/-- The stems the cyclic spell-out of an input derives, a cycle for each feature from the
innermost out. -/
def spellOut (K : Rules) (i : Input) : Finset Stem :=
  i.foldl (fun S f ↦ S.biUnion fun s ↦ (cycle K f s).toFinset) {[]}

section SpellOut

variable {K : Rules} {f : Feature} {i : Input} {s t : Stem}

theorem mem_splits {km : Stem × Stem} : km ∈ splits K f s ↔ km.1 ++ km.2 = s ∧
    (∀ x ∈ km.2, K f x.feature ≠ none) ∧ (f = causative ∨ km.2.length ≤ 1) ∧
      ∀ x ∈ km.1.getLast?, K f x.feature ≠ some .obligatory := by
  simp only [splits, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j, -, rfl⟩, h⟩
    exact ⟨List.take_append_drop j s, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨⟨km.1.length, by simp only [List.length_append]; omega, by simp⟩, h⟩

theorem mem_spellOut_concat :
    t ∈ spellOut K (i ++ [f]) ↔ ∃ s ∈ spellOut K i, t ∈ cycle K f s := by
  simp [spellOut, List.foldl_append]

theorem spellOut_induction {P : Input → Stem → Prop} (h : s ∈ spellOut K i) (nil : P [] [])
    (step : ∀ i f s t, P i s → t ∈ cycle K f s → P (i ++ [f]) t) : P i s := by
  induction i using List.reverseRecOn generalizing s with
  | nil => rwa [show s = [] by simpa [spellOut] using h]
  | append_singleton i f ih =>
    obtain ⟨s', hs', ht⟩ := mem_spellOut_concat.mp h
    exact step i f s' s (ih hs') ht

theorem rmc_of_mem_spellOut (h : s ∈ spellOut K i) : RMC s :=
  spellOut_induction (P := fun _ s ↦ RMC s) h (by decide) fun _ _ _ _ _ ht ↦
    of_decide_eq_true (List.mem_filter.mp ht).2

/-- The feature a suffix spells out on its own cycle, none for the doubled *-an-*. -/
def Suffix.own? : Suffix → Option Feature
  | spell f => some f
  | doubled => none

@[simp] theorem Suffix.own?_spell : (Suffix.spell f).own? = some f := rfl

theorem filterMap_own_doubling {m : Stem} : (doubling f s m).filterMap Suffix.own? = [] := by
  unfold doubling; split <;> rfl

-- Each feature of the input is spelled out on a cycle of its own, once.
theorem perm_of_mem_spellOut (h : s ∈ spellOut K i) : (s.filterMap Suffix.own?).Perm i :=
  spellOut_induction (P := fun i s ↦ (s.filterMap Suffix.own?).Perm i) h .nil fun i f s t hs ht ↦ by
    simp only [cycle, List.mem_filter, List.mem_map] at ht
    obtain ⟨⟨km, hkm, rfl⟩, -⟩ := ht
    obtain ⟨rfl, -⟩ := mem_splits.mp hkm
    simp only [List.filterMap_append, List.filterMap_cons, Suffix.own?_spell,
      filterMap_own_doubling, List.nil_append] at hs ⊢
    exact List.perm_middle.trans ((hs.cons f).trans (List.perm_append_singleton f i).symm)

/-! ### The filters (10) -/

/-- A stem satisfies the negative filters (10b) when no applicative or passive immediately
precedes a causative or an intensive. -/
def Filtered (s : Stem) : Prop :=
  s.IsChain fun x y ↦ ¬ (x.feature ∈ [applicative, passive] ∧ y.feature ∈ [causative, intensive])

theorem rules_eq_obligatory {f g : Feature} :
    rules f g = some .obligatory ↔ g ∈ [applicative, passive] ∧ f ∈ [causative, intensive] := by
  cases f <;> cases g <;> decide

theorem not_mem_of_rules_ne_none {f x : Feature} (h : rules f x ≠ none) :
    x ∉ [causative, intensive] := by
  cases f <;> cases x <;> simp_all [rules, rules₀]

theorem filtered_cons {x : Suffix} {l : Stem} (hl : Filtered l)
    (h : ∀ y ∈ l.head?, y.feature ∉ [causative, intensive]) : Filtered (x :: l) :=
  List.isChain_cons.mpr ⟨fun y hy hxy ↦ h y hy hxy.2, hl⟩

theorem Filtered.cycle (hs : Filtered s) (ht : t ∈ cycle rules f s) : Filtered t := by
  simp only [HymanMchombo1992.cycle, List.mem_filter, List.mem_map] at ht
  obtain ⟨⟨km, hkm, rfl⟩, -⟩ := ht
  obtain ⟨rfl, h2, -, h3⟩ := mem_splits.mp hkm
  have hm : ∀ x ∈ km.2, x.feature ∉ [causative, intensive] := fun x hx ↦
    not_mem_of_rules_ne_none (h2 x hx)
  have hd : ∀ y ∈ (doubling f (km.1 ++ km.2) km.2 ++ km.2).head?,
      y.feature ∉ [causative, intensive] := by
    unfold doubling
    split
    · simp [Suffix.feature]
    · exact fun y hy ↦ hm y (List.mem_of_mem_head? (by simpa using hy))
  have hr : Filtered (doubling f (km.1 ++ km.2) km.2 ++ km.2) := by
    unfold doubling
    split
    · exact filtered_cons hs.right_of_append fun y hy ↦ hm y (List.mem_of_mem_head? hy)
    · exact hs.right_of_append
  refine List.IsChain.append hs.left_of_append (filtered_cons hr hd) fun x hx y hy hxy ↦ ?_
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hy
  exact h3 x hx (rules_eq_obligatory.mpr hxy)

/-- Morphemic circumscription makes the filters (10) redundant: no stem the cyclic spell-out
derives violates them. -/
theorem filtered_of_mem_spellOut (h : s ∈ spellOut rules i) : Filtered s :=
  spellOut_induction (P := fun _ s ↦ Filtered s) h .nil fun _ _ _ _ hs ht ↦ hs.cycle ht

end SpellOut

-- (35)
theorem ambiguity_needs_late_rule :
    spellOut rules₀ [reciprocal, causative] = {[.spell reciprocal, .spell causative]} ∧
      spellOut rules [reciprocal, causative] =
        {[.spell reciprocal, .spell causative], [.spell causative, .spell reciprocal]} := by
  decide

/-! ### Valency -/

/-- A feature derives a valency from a base of valency `n` by adding what its voice's derived
frame adds to its initial frame, or removing what it removes; a voice that removes a core
argument applies only to a base with at least the valency of its initial frame. -/
def Feature.valency (f : Feature) (n : ℕ) : Option ℕ :=
  match f.voice? with
  | none => some n
  | some v =>
    if v.derived.valency < v.initial.valency ∧ n < v.initial.valency then none
    else some (n + v.derived.valency - v.initial.valency)

/-- The valency an input derives from a root of valency `n`, if every feature applies. -/
def Input.valency (i : Input) (n : ℕ) : Option ℕ := i.foldlM (fun n f ↦ f.valency n) n

theorem valency_of_mem {f : Feature} (hf : f ∈ [reciprocal, passive]) (n : ℕ) :
    f.valency n = if n < 2 then none else some (n - 1) := by
  have h₁ : Chichewa.reciprocal.initial.valency = 2 ∧ Chichewa.passive.initial.valency = 2 := by
    decide
  have h₂ : Chichewa.reciprocal.derived.valency = 1 ∧ Chichewa.passive.derived.valency = 1 := by
    decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;>
    simp only [Feature.valency, Feature.voice?, h₁, h₂] <;> split_ifs <;> first | rfl | omega

-- (4a)
theorem detransitivized_once : ∀ {i : Input} {n : ℕ}, n ≤ 2 → causative ∉ i → applicative ∉ i →
    (i.valency n).isSome → (i.filter (· ∈ [reciprocal, passive])).length ≤ n - 1
  | [], _, _, _, _, _ => by simp
  | f :: rest, n, hn, hc, ha, h => by
    simp only [List.mem_cons, not_or] at hc ha
    obtain ⟨m, hm, hrest⟩ : ∃ m, f.valency n = some m ∧ (Input.valency rest m).isSome := by
      simp only [Input.valency, List.foldlM_cons] at h
      cases hf : f.valency n with
      | none => simp [hf] at h
      | some m => exact ⟨m, rfl, by simpa [hf, Input.valency] using h⟩
    have ih := fun {m} hm ↦ detransitivized_once (i := rest) (n := m) hm hc.2 ha.2
    cases f with
    | causative => exact absurd rfl hc.1
    | applicative => exact absurd rfl ha.1
    | intensive =>
      simp only [Feature.valency, Feature.voice?, Option.some.injEq] at hm
      subst hm
      simpa using ih hn hrest
    | reciprocal | passive =>
      rw [valency_of_mem (by simp)] at hm
      split_ifs at hm with h2
      simp only [Option.some.injEq] at hm
      have := ih (m := m) (by omega) hrest
      rw [List.filter_cons_of_pos (by decide), List.length_cons]
      omega

/-- A root survives an input when the valency of its frame suffices for each feature. -/
def Licensed (v : Verb) (i : Input) : Prop :=
  ∃ fr ∈ v.valency.frames.head?, (i.valency fr.valency).isSome

instance (v : Verb) (i : Input) : Decidable (Licensed v i) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ### Pairs of suffixes -/

/-- Two suffixes surface in the order `f`, `g` on *mang-* 'tie' when an input of the two features
survives the root's valency and spells out a stem with `f` before `g`. -/
def Occurs (f g : Feature) : Prop :=
  ∃ i ∈ [[f, g], [g, f]], Licensed Chichewa.Verbs.mang i ∧
    ∃ s ∈ spellOut rules i, [Suffix.spell f, .spell g].Sublist s

instance (f g : Feature) : Decidable (Occurs f g) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _ ∧ ∃ _ ∈ _, _))

/-- Two suffixes surface in an order exactly when the root's valency admits them, their morphs
differ and no obligatory circumscription reverses them. Of the ten pairs, four surface in both
orders (3), two in neither (4) and four in one (7). -/
theorem occurs_iff {f g : Feature} (h : f ≠ g) :
    Occurs f g ↔ (Licensed Chichewa.Verbs.mang [f, g] ∨ Licensed Chichewa.Verbs.mang [g, f]) ∧
      f.morphs ≠ g.morphs ∧ rules g f ≠ some .obligatory := by
  revert h; revert f g; decide +kernel

/-! ### The thematic hierarchy -/

/-- The roles of the thematic hierarchy (31), lowest first. -/
inductive Role where
  | circumstantial
  | locative
  | patient
  | instrument
  | goal
  | benefactive
  | agent
  deriving DecidableEq, Repr, Fintype

/-- A role's height on the hierarchy (31). -/
def Role.height : Role → ℕ
  | .circumstantial => 0
  | .locative => 1
  | .patient => 2
  | .instrument => 3
  | .goal => 4
  | .benefactive => 5
  | .agent => 6

/-- The hierarchy (31), `agent > benefactive > goal > instrument > patient > locative >
circumstantial`. -/
instance : LinearOrder Role := LinearOrder.lift' Role.height (by decide)

/-- An applied argument is a participant between the agent and the patient (31). -/
def Role.IsArgument (r : Role) : Prop := Role.patient < r ∧ r < .agent

/-- An applied adjunct is a setting below the locative (31). -/
def Role.IsAdjunct (r : Role) : Prop := r < .locative

instance (r : Role) : Decidable r.IsArgument := inferInstanceAs (Decidable (_ ∧ _))

instance (r : Role) : Decidable r.IsAdjunct := inferInstanceAs (Decidable (_ < _))

/-- The role a feature's suffix targets (33): an agent for the causative, the prototypical
benefactive for the applicative and a patient for the reciprocal and the passive; the intensive,
an adverbial, ranks above every role. -/
def Feature.target : Feature → WithTop Role
  | causative => Role.agent
  | applicative => Role.benefactive
  | reciprocal | passive => Role.patient
  | intensive => ⊤

-- (33)
theorem target_lt_of_rules_ne_none {f g : Feature} (h : rules f g ≠ none) :
    g.target < f.target := by
  revert h; revert f g; decide

/-- The scopes an applicative of role `r` takes with the passive (31) put the applicative within
the passive for an applied argument, the passive within the applicative for an applied adjunct,
and either for a locative, which lies between them. -/
def Role.passiveScopes (r : Role) : List Input :=
  (if r.IsAdjunct then [] else [[applicative, passive]]) ++
    if r.IsArgument then [] else [[passive, applicative]]

/-! ### The paper's examples -/

/-- A feature by its letter in the rows. -/
def Feature.ofChar? : Char → Option Feature
  | 'C' => some causative
  | 'A' => some applicative
  | 'R' => some reciprocal
  | 'P' => some passive
  | 'I' => some intensive
  | _ => none

/-- A stem in the rows' letters, a doubled *-an-* written `(R)` as in (12c). -/
def Stem.ofChars? : List Char → Option Stem
  | [] => some []
  | '(' :: 'R' :: ')' :: cs => (.doubled :: ·) <$> ofChars? cs
  | c :: cs => (· :: ·) <$> (Suffix.spell <$> Feature.ofChar? c) <*> ofChars? cs

/-- A row's scope, innermost first. -/
def scope? (r : Datum) : Option Input := (r.feature? "scope").bind (·.toList.mapM Feature.ofChar?)

/-- A row's suffixes, in surface order. -/
def suffixes? (r : Datum) : Option Stem := (r.feature? "suffixes").bind (Stem.ofChars? ·.toList)

/-- A row's root. -/
def root? (r : Datum) : Option Verb :=
  r.parse? "root" [("mang", Chichewa.Verbs.mang), ("uk", Chichewa.Verbs.uk)]

/-- A row's applied role. -/
def role? (r : Datum) : Option Role :=
  r.parse? "role" [("benefactive", .benefactive), ("instrument", .instrument),
    ("locative", .locative), ("circumstantial", .circumstantial)]

/-- A row's passive subject, as a participant of [baker-1985]'s rules. -/
def subject? (r : Datum) : Option Baker1985.Arg :=
  r.parse? "subject" [("applied", .applied), ("patient", .patient)]

/-- The letters of a feature's morphs. -/
def Feature.form (f : Feature) : String := f.morphs.foldr (fun m w ↦ m.form ++ w) ""

/-- The intensive suffix as the source writes it, in capitals for its high tone. -/
def intensiveForm : String := "ITS"

-- (5b)
theorem intensiveForm_toList : intensiveForm.toList = causative.form.toList.map Char.toUpper := by
  decide +kernel

/-- A stem in the source's spelling, each suffix after a hyphen, the intensive reduplicated
before another suffix (5a). -/
def spell : Stem → String
  | [] => ""
  | [.spell intensive] => "-" ++ intensiveForm
  | .spell intensive :: s => "-" ++ intensiveForm ++ intensiveForm ++ spell s
  | x :: s => "-" ++ x.feature.form ++ spell s

theorem rows_parse :
    ∀ r ∈ Examples.all, (root? r).isSome ∧ (suffixes? r).isSome ∧
      ((scope? r).isSome ∨ (role? r).isSome ∧ (subject? r).isSome) := by
  decide +kernel

-- Each stem row's form is its root followed by the spelling of its suffixes.
theorem rows_form :
    ∀ r ∈ Examples.all, role? r = none → ∀ v ∈ root? r, ∀ s ∈ suffixes? r,
      r.primaryText = v.form ++ spell s ++ "-" ∨ r.primaryText = v.form ++ spell s ++ "-a" := by
  decide +kernel

/-- The cyclic spell-out derives every stem the paper accepts from its scope, on a root whose
valency survives it, and no stem the paper stars except *mang-ir-an-its-* from the scope of (34a),
which the paper stars as (34c). -/
theorem rows_spellOut :
    ∀ r ∈ Examples.all, ∀ v ∈ root? r, ∀ i ∈ scope? r, ∀ s ∈ suffixes? r,
      (r.judgment = .acceptable → Licensed v i ∧ s ∈ spellOut rules i) ∧
        (r.judgment = .ungrammatical → (Licensed v i ∧ s ∈ spellOut rules i ↔
          i = [reciprocal, applicative, causative] ∧
            s = [.spell applicative, .spell reciprocal, .spell causative])) := by
  decide +kernel

/-- Of the stems with a doubled *-an-*, all clean on the full morph tier, the RMC rejects exactly
the degraded triple applicatives of (25a); a causative between a doubled *-an-* and the next
*-ir-* rescues the form (25b). -/
theorem rows_doubled :
    ∀ r ∈ Examples.all, ∀ s ∈ suffixes? r, .doubled ∈ s →
      OCP.IsClean (s.map (Feature.morphs ∘ Suffix.feature)) ∧
        (RMC s ↔ r.judgment ∈ [.acceptable, .marginal]) := by
  decide +kernel

/-- The orders of applicative and passive the paper accepts are exactly those spelled out from
scopes the applied role allows ((27)–(31)), whichever argument is the passive subject; under
[baker-1985]'s rules, in any setting, *-idw-ir-* never makes the applied argument the subject,
as the locative of (29a) is. -/
theorem rows_passive (g : Baker1985.Grammar) :
    (∀ r ∈ Examples.all, ∀ ρ ∈ role? r, ∀ s ∈ suffixes? r, r.judgment = .acceptable →
      ∃ i ∈ ρ.passiveScopes, s ∈ spellOut rules i) ∧
    (∀ r ∈ Examples.all, ∀ ρ ∈ role? r, ∀ i ∈ ρ.passiveScopes, ∀ s ∈ spellOut rules i,
      ∃ r' ∈ Examples.all, role? r' = some ρ ∧ suffixes? r' = some s ∧
        r'.judgment = .acceptable) ∧
    ∃ r ∈ Examples.all, r.judgment = .acceptable ∧ role? r = some .locative ∧
      suffixes? r = some [.spell passive, .spell applicative] ∧ subject? r = some .applied ∧
      ∀ st ∈ Baker1985.outcomes g [.passive, .applicative] (Baker1985.initial true true),
        .applied ∉ st.subjects := by
  refine ⟨by decide +kernel, by decide +kernel, Examples.ex_29a_pa, by decide +kernel, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide,
    Baker1985.applied_subject_needs_applicative_first g true true⟩

end HymanMchombo1992
