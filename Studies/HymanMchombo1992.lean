module

public import Linglib.Data.Examples.HymanMchombo1992
public import Linglib.Fragments.Chichewa.Verbs
public import Linglib.Fragments.Chichewa.Voice
public import Linglib.Phonology.OCP

/-!
# Hyman and Mchombo 1992: morphotactic constraints in the Chichewa verb stem

Hyman and Mchombo study the orders in which the Chichewa verbal suffixes combine on a root such
as *mang-* 'tie': the causative *-its-*, the applicative *-ir-*, the reciprocal *-an-*, the
passive *-idw-* and the intensive *-ITS-*. Spell-out is cyclic and follows scope, but before a
feature is spelled out a final morph may be marked off, circumscribed, and restored after the
new one: *-ir-* and *-idw-* within the scope of the causative or the intensive, *-an-*
optionally within that of the applicative and, by the later rule (36), of the causative or the
intensive. The Repeated Morph Constraint (RMC) blocks two successive features spelled out by one
morph, an applicative on a reciprocal base spells *-an-* a second time, and the reciprocal and
the passive never combine, since a transitive verb is detransitivized only once. Circumscription
makes the negative filters (10) redundant (`filtered_of_mem_spellOut`). The authors close with
(34), which the cyclic account cannot exclude, and conclude that the causative is spelled out
first.

## Main definitions

* `Feature`, `Input`, `Stem`: the suffixal features, an input in order of scope, and a stem in
  surface order.
* `RMC`: the Repeated Morph Constraint, the OCP on the morph tier.
* `rules₀`, `rules`: the circumscriptions (15) and (22), and with them (36).
* `splits`, `cycle`, `spellOut`: the cyclic spell-out.
* `Feature.valency`, `Input.valency`: the valency each feature's voice derives.
* `Role`, `Feature.target?`, `Role.passiveScopes`: the thematic hierarchy (31) and its uses.

## Main results

* `filtered_of_mem_spellOut`: no spelled-out stem violates the filters (10).
* `rmc_of_mem_spellOut`, `mem_iff_of_mem_spellOut`: every spelled-out stem satisfies the RMC
  and spells out exactly the features of its input.
* `detransitivized_once`: (4a).
* `ambiguity_needs_late_rule`: (35), (36).
* `rank_lt_of_rules_ne_none`: (33), circumscription respects the hierarchy.
* `rows_spellOut`, `rows_cyclicFailures`, `rows_passive`, `rows_form`: the paper's examples.

## Implementation notes

* A feature's valency effect is that of the voice the fragment assigns it: it adds what the
  voice's derived frame adds to its initial frame or removes what it removes, and a voice that
  removes a core argument applies only to a base with at least the valency of its initial frame.
  The paper's one valency claim, (4a), is stated of `mang-`; the intensive, an adverbial, has no
  voice.
* The intensive is spelled out by the causative morph with a high tone (5b), so the RMC treats
  the two alike; the tone is written in capitals and the intensive reduplicates before another
  suffix (5a).
* The causative marks off one morph after another (18) and the intensive at most one (fn. 16);
  the applicative's only rule (22) marks off a single *-an-*. A cycle leaving an obligatory
  circumscription undone has no output. The respelled *-an-* (24) is added when the applicative
  is spelled out on a base containing a reciprocal and the base's own *-an-* was not marked off
  (22); the rule block's respelling of *-ir-* on a reciprocal cycle, which the paper shows
  blocked by the RMC, is omitted.
* The passive subjects of (27)–(30) are recorded on the rows and not derived, since the paper
  states only the order of the applicative and the passive. Rows marked ? or ?* carry no claim.

## TODO

* (25): the paper suggests that the degraded triple applicatives violate the RMC if respelled
  morphs are invisible, `OCP.IsCleanOn` on the tier without them; this needs stems that record
  which *-an-* is respelled.
* The Cibemba data (20) and the phonological case for cyclic spell-out.

## References

* [hyman-mchombo-1992]
* [creissels-2024]
-/

@[expose] public section

namespace HymanMchombo1992

open Morphology

/-! ### Features and their morphs -/

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

/-- A stem lists the features whose morphs follow the root, in surface order; a respelled *-an-*
is a second `reciprocal`. -/
abbrev Stem := List Feature

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

/-- The Repeated Morph Constraint bars two successive features spelled out by the same morphs
(4b); it is the OCP on the morph tier. -/
abbrev RMC (s : Stem) : Prop := OCP.IsClean (s.map Feature.morphs)

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

/-- The ways the spell-out of `f` splits a stem, given in reverse, into the material it keeps and
the material it marks off, which `m` accumulates. The causative marks off one morph after
another (18) and every other feature at most one (fn. 16), and a split that leaves an
obligatory circumscription undone is not one. -/
def splits (K : Rules) (f : Feature) : List Feature → Stem → List (Stem × Stem)
  | [], m => [([], m)]
  | g :: rest, m =>
    let mark := if f = causative ∨ m = [] then splits K f rest (g :: m) else []
    match K f g with
    | some .obligatory => mark
    | some .optional => ((g :: rest).reverse, m) :: mark
    | none => [((g :: rest).reverse, m)]

/-- The *-an-* the applicative spells out again on a base containing a reciprocal (24), unless
the base's own *-an-* was marked off (22). -/
def respelling (i : Input) (f : Feature) (m : Stem) : Stem :=
  if f = applicative ∧ reciprocal ∈ i ∧ m.head? ≠ some reciprocal then [reciprocal] else []

/-- A cycle spells out `f` on a stem `s` of the input `i` by placing the new morph after the kept
material and before the marked-off material; the RMC blocks a result that repeats a morph. -/
def cycle (K : Rules) (i : Input) (f : Feature) (s : Stem) : List Stem :=
  ((splits K f s.reverse []).map fun km ↦ km.1 ++ f :: (respelling i f km.2 ++ km.2)).filter
    fun t ↦ decide (RMC t)

/-- The stems the cyclic spell-out of an input derives. -/
def spellOut (K : Rules) (i : Input) : Finset Stem := go i.reverse
where
  /-- The stems of an input given in reverse. -/
  go : List Feature → Finset Stem
    | [] => {[]}
    | f :: rest => (go rest).biUnion fun s ↦ (cycle K rest.reverse f s).toFinset

theorem splits_spec {K : Rules} {f : Feature} : ∀ {rev : List Feature} {acc : Stem}
    {km : Stem × Stem}, km ∈ splits K f rev acc → km.1 ++ km.2 = rev.reverse ++ acc ∧
      (∀ x ∈ km.2, x ∈ acc ∨ K f x ≠ none) ∧ ∀ x ∈ km.1.getLast?, K f x ≠ some .obligatory
  | [], acc, km, h => by
    simp only [splits, List.mem_singleton] at h
    subst h
    exact ⟨rfl, fun x hx ↦ .inl hx, by simp⟩
  | g :: rest, acc, km, h => by
    have hmark : km ∈ (if f = causative ∨ acc = [] then splits K f rest (g :: acc) else []) →
        K f g ≠ none → km.1 ++ km.2 = (g :: rest).reverse ++ acc ∧
          (∀ x ∈ km.2, x ∈ acc ∨ K f x ≠ none) ∧
          ∀ x ∈ km.1.getLast?, K f x ≠ some .obligatory := by
      intro hm hg
      split at hm
      · obtain ⟨h1, h2, h3⟩ := splits_spec hm
        refine ⟨by simp [h1], fun x hx ↦ ?_, h3⟩
        rcases h2 x hx with hx | hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inr hg
          · exact .inl hx
        · exact .inr hx
      · simp at hm
    have hstop (hg : K f g ≠ some .obligatory) (hk : km = ((g :: rest).reverse, acc)) :
        km.1 ++ km.2 = (g :: rest).reverse ++ acc ∧
          (∀ x ∈ km.2, x ∈ acc ∨ K f x ≠ none) ∧
          ∀ x ∈ km.1.getLast?, K f x ≠ some .obligatory := by
      subst hk
      refine ⟨rfl, fun x hx ↦ .inl hx, fun x hx ↦ ?_⟩
      simp only [List.reverse_cons, List.getLast?_concat, Option.mem_def,
        Option.some.injEq] at hx
      exact hx ▸ hg
    simp only [splits] at h
    split at h
    · exact hmark h (by simp_all)
    · rcases List.mem_cons.mp h with h | h
      · exact hstop (by simp_all) h
      · exact hmark h (by simp_all)
    · exact hstop (by simp_all) (List.mem_singleton.mp h)

theorem mem_spellOut_go {K : Rules} {f : Feature} {rest : List Feature} {t : Stem} :
    t ∈ spellOut.go K (f :: rest) ↔ ∃ s ∈ spellOut.go K rest, t ∈ cycle K rest.reverse f s := by
  simp [spellOut.go]

/-- Every stem the cyclic spell-out derives satisfies the RMC. -/
theorem rmc_of_mem_spellOut {K : Rules} {i : Input} {s : Stem} (h : s ∈ spellOut K i) :
    RMC s := by
  unfold spellOut at h
  generalize i.reverse = l at h
  cases l with
  | nil =>
    simp only [spellOut.go, Finset.mem_singleton] at h
    exact h ▸ List.IsChain.nil
  | cons f rest =>
    obtain ⟨_, -, ht⟩ := mem_spellOut_go.mp h
    simp only [cycle, List.mem_filter, decide_eq_true_eq] at ht
    exact ht.2

/-- Every stem the cyclic spell-out derives spells out exactly the features of its input. -/
theorem mem_iff_of_mem_spellOut {K : Rules} {i : Input} {s : Stem} (h : s ∈ spellOut K i)
    (x : Feature) : x ∈ s ↔ x ∈ i := by
  rw [show x ∈ i ↔ x ∈ i.reverse from List.mem_reverse.symm]
  unfold spellOut at h
  generalize i.reverse = l at h
  induction l generalizing s with
  | nil =>
    simp only [spellOut.go, Finset.mem_singleton] at h
    simp [h]
  | cons f rest ih =>
    obtain ⟨s', hs', ht⟩ := mem_spellOut_go.mp h
    simp only [cycle, List.mem_filter, List.mem_map] at ht
    obtain ⟨⟨km, hkm, rfl⟩, -⟩ := ht
    obtain ⟨h1, -, -⟩ := splits_spec hkm
    rw [List.reverse_reverse, List.append_nil] at h1
    have hs := ih hs'
    rw [← h1] at hs
    simp only [List.mem_append, List.mem_cons] at hs ⊢
    unfold respelling
    split
    · rename_i hr
      simp only [List.mem_singleton]
      constructor
      · rintro (hx | rfl | rfl | hx)
        · exact .inr (hs.mp (.inl hx))
        · exact .inl rfl
        · exact .inr (by simpa using hr.2.1)
        · exact .inr (hs.mp (.inr hx))
      · rintro (rfl | hx)
        · exact .inr (.inl rfl)
        · rcases hs.mpr hx with hx | hx
          · exact .inl hx
          · exact .inr (.inr (.inr hx))
    · simp only [List.not_mem_nil, false_or]
      constructor
      · rintro (hx | rfl | hx)
        · exact .inr (hs.mp (.inl hx))
        · exact .inl rfl
        · exact .inr (hs.mp (.inr hx))
      · rintro (rfl | hx)
        · exact .inr (.inl rfl)
        · rcases hs.mpr hx with hx | hx
          · exact .inl hx
          · exact .inr (.inr hx)

/-! ### The filters (10) -/

/-- A stem satisfies the negative filters (10b) when no applicative or passive immediately
precedes a causative or an intensive. -/
def Filtered (s : Stem) : Prop :=
  s.IsChain fun f g ↦ ¬ (f ∈ [applicative, passive] ∧ g ∈ [causative, intensive])

theorem rules_eq_obligatory {f g : Feature} :
    rules f g = some .obligatory ↔ g ∈ [applicative, passive] ∧ f ∈ [causative, intensive] := by
  cases f <;> cases g <;> decide

theorem not_mem_of_rules_ne_none {f x : Feature} (h : rules f x ≠ none) :
    x ∉ [causative, intensive] := by
  cases f <;> cases x <;> simp_all [rules, rules₀]

theorem filtered_cons {f : Feature} {l : Stem} (hl : Filtered l)
    (h : ∀ y ∈ l.head?, y ∉ [causative, intensive]) : Filtered (f :: l) :=
  List.isChain_cons.mpr ⟨fun y hy hfy ↦ h y hy hfy.2, hl⟩

theorem Filtered.cycle {i : Input} {f : Feature} {s t : Stem} (hs : Filtered s)
    (ht : t ∈ cycle rules i f s) : Filtered t := by
  simp only [HymanMchombo1992.cycle, List.mem_filter, List.mem_map] at ht
  obtain ⟨⟨km, hkm, rfl⟩, -⟩ := ht
  obtain ⟨h1, h2, h3⟩ := splits_spec hkm
  rw [List.reverse_reverse, List.append_nil] at h1
  rw [← h1] at hs
  have hm : ∀ x ∈ km.2, x ∉ [causative, intensive] := fun x hx ↦
    not_mem_of_rules_ne_none ((h2 x hx).resolve_left List.not_mem_nil)
  have hr : Filtered (respelling i f km.2 ++ km.2) := by
    unfold respelling
    split
    · exact filtered_cons hs.right_of_append fun y hy ↦ hm y (List.mem_of_mem_head? hy)
    · exact hs.right_of_append
  have hhead : ∀ y ∈ (respelling i f km.2 ++ km.2).head?, y ∉ [causative, intensive] := by
    intro y hy
    unfold respelling at hy
    split at hy
    · simp only [List.singleton_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hy
      subst hy
      decide
    · exact hm y (List.mem_of_mem_head? (by simpa using hy))
  refine List.IsChain.append hs.left_of_append (filtered_cons hr hhead) fun x hx y hy hxy ↦ ?_
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hy
  exact h3 x hx (rules_eq_obligatory.mpr hxy)

/-- The filters (10) follow from circumscription, since no stem the cyclic spell-out derives has
an applicative or passive morph immediately before a causative or intensive one. -/
theorem filtered_of_mem_spellOut {i : Input} {s : Stem} (h : s ∈ spellOut rules i) :
    Filtered s := by
  unfold spellOut at h
  generalize i.reverse = l at h
  induction l generalizing s with
  | nil =>
    simp only [spellOut.go, Finset.mem_singleton] at h
    exact h ▸ List.IsChain.nil
  | cons f rest ih =>
    obtain ⟨s', hs', ht⟩ := mem_spellOut_go.mp h
    exact (ih hs').cycle ht

/-- A causativized reciprocal surfaces as *-its-an-* as well as *-an-its-* only by the
circumscription (36), so without it *-its-an-* would spell out only a reciprocalized causative
((35), (36)). -/
theorem ambiguity_needs_late_rule :
    spellOut rules₀ [reciprocal, causative] = {[reciprocal, causative]} ∧
      spellOut rules [reciprocal, causative] =
        {[reciprocal, causative], [causative, reciprocal]} := by
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

theorem valency_reciprocal (n : ℕ) :
    reciprocal.valency n = if n < 2 then none else some (n - 1) := by
  have h₁ : Chichewa.reciprocal.initial.valency = 2 := by decide
  have h₂ : Chichewa.reciprocal.derived.valency = 1 := by decide
  simp only [Feature.valency, Feature.voice?, h₁, h₂]
  split_ifs <;> first | rfl | omega

theorem valency_passive (n : ℕ) :
    passive.valency n = if n < 2 then none else some (n - 1) := by
  have h₁ : Chichewa.passive.initial.valency = 2 := by decide
  have h₂ : Chichewa.passive.derived.valency = 1 := by decide
  simp only [Feature.valency, Feature.voice?, h₁, h₂]
  split_ifs <;> first | rfl | omega

/-- A transitive verb is detransitivized only once (4a). With no causative or applicative to add
an argument, an input that a root of valency at most two survives has fewer reciprocals and
passives than the root has arguments. -/
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
      first | rw [valency_reciprocal] at hm | rw [valency_passive] at hm
      split_ifs at hm with h2
      simp only [Option.some.injEq] at hm
      have := ih (m := m) (by omega) hrest
      rw [List.filter_cons_of_pos (by decide), List.length_cons]
      omega

/-! ### The thematic hierarchy -/

/-- The roles of the thematic hierarchy (31). -/
inductive Role where
  | agent
  | benefactive
  | goal
  | instrument
  | patient
  | locative
  | circumstantial
  deriving DecidableEq, Repr, Fintype

/-- A role's place on the hierarchy (31), counted from the top. -/
def Role.rank : Role → ℕ
  | .agent => 0
  | .benefactive => 1
  | .goal => 2
  | .instrument => 3
  | .patient => 4
  | .locative => 5
  | .circumstantial => 6

/-- The role a feature's suffix targets (33) is an agent for the causative, the prototypical
benefactive for the applicative, and a patient for the reciprocal and the passive; the
intensive, an adverbial, targets none. -/
def Feature.target? : Feature → Option Role
  | causative => some .agent
  | applicative => some .benefactive
  | reciprocal | passive => some .patient
  | intensive => none

/-- A feature's place on the hierarchy, an adverbial above every role. -/
def Feature.rank (f : Feature) : WithBot ℕ := f.target?.map Role.rank

/-- Every circumscription marks off a suffix that targets a role lower on the hierarchy than the
feature that marks it off (33). The paper notes that a locative or circumstantial
applicative, below the patient, still precedes the reciprocal: the orders follow the affixes'
prototypical functions. -/
theorem rank_lt_of_rules_ne_none {f g : Feature} (h : rules f g ≠ none) : f.rank < g.rank := by
  revert h; revert f g; decide

/-- An applied argument, a participant above the patient on the hierarchy (31). -/
def Role.IsArgument (r : Role) : Prop := r.rank < Role.patient.rank

/-- An applied adjunct, a setting at the foot of the hierarchy (31). -/
def Role.IsAdjunct (r : Role) : Prop := ∀ r' : Role, r'.rank ≤ r.rank

instance (r : Role) : Decidable r.IsArgument := inferInstanceAs (Decidable (_ < _))

instance (r : Role) : Decidable r.IsAdjunct := inferInstanceAs (Decidable (∀ _, _))

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

/-- A row's feature as a sequence of features. -/
def features? (r : Datum) (key : String) : Option (List Feature) :=
  (r.feature? key).bind fun s ↦ s.toList.mapM Feature.ofChar?

/-- A row's scope, innermost first. -/
def scope? (r : Datum) : Option Input := features? r "scope"

/-- A row's suffixes, in surface order. -/
def suffixes? (r : Datum) : Option Stem := features? r "suffixes"

/-- A row's root. -/
def root? (r : Datum) : Option Verb :=
  r.parse? "root" [("mang", Chichewa.Verbs.mang), ("uk", Chichewa.Verbs.uk)]

/-- A row's applied role. -/
def role? (r : Datum) : Option Role :=
  r.parse? "role" [("benefactive", .benefactive), ("instrument", .instrument),
    ("locative", .locative), ("circumstantial", .circumstantial)]

/-- A root survives an input when the valency of its frame suffices for each feature. -/
def Licensed (v : Verb) (i : Input) : Prop :=
  ∃ fr ∈ v.valency.frames.head?, (i.valency fr.valency).isSome

instance (v : Verb) (i : Input) : Decidable (Licensed v i) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The letters of a feature's morphs. -/
def Feature.form (f : Feature) : String := f.morphs.foldr (fun m w ↦ m.form ++ w) ""

/-- The intensive suffix as the source writes it, in capitals for its high tone. -/
def intensiveForm : String := "ITS"

/-- The intensive suffix is the causative morph with a high tone (5b). -/
theorem intensiveForm_toList : intensiveForm.toList = causative.form.toList.map Char.toUpper := by
  decide +kernel

/-- A stem in the source's spelling, each suffix after a hyphen, the intensive reduplicated
before another suffix (5a). -/
def spell : Stem → String
  | [] => ""
  | [intensive] => "-" ++ intensiveForm
  | intensive :: s => "-" ++ intensiveForm ++ intensiveForm ++ spell s
  | f :: s => "-" ++ f.form ++ spell s

theorem rows_parse :
    ∀ r ∈ Examples.all, (root? r).isSome ∧ (suffixes? r).isSome ∧
      ((scope? r).isSome ∨ (role? r).isSome) := by
  decide +kernel

/-- Each stem row's form is its root followed by the spelling of its suffixes, as a bare stem or
with the final vowel *-a*. -/
theorem rows_form :
    ∀ r ∈ Examples.all, role? r = none → ∀ v ∈ root? r, ∀ s ∈ suffixes? r,
      r.primaryText = v.form ++ spell s ++ "-" ∨ r.primaryText = v.form ++ spell s ++ "-a" := by
  decide +kernel

/-- The rows the cyclic spell-out gets wrong are (34c), which it derives although the paper stars
it, and the triple applicative of (25a), whose degradation the paper leaves open. -/
def cyclicFailures : List String := ["hymanmchombo1992_34c", "hymanmchombo1992_25a_3"]

/-- Every stem the paper accepts survives its root's valency and is spelled out from its scope;
outside `cyclicFailures`, no stem it stars is. -/
theorem rows_spellOut :
    ∀ r ∈ Examples.all, ∀ v ∈ root? r, ∀ i ∈ scope? r, ∀ s ∈ suffixes? r,
      (r.judgment = .acceptable → Licensed v i ∧ s ∈ spellOut rules i) ∧
        (r.judgment = .ungrammatical → r.id ∉ cyclicFailures →
          ¬ (Licensed v i ∧ s ∈ spellOut rules i)) := by
  decide +kernel

/-- The stems in `cyclicFailures` are starred, yet survive their root's valency and are spelled
out from their scope ((34), (25)). -/
theorem rows_cyclicFailures :
    ∀ r ∈ Examples.all, r.id ∈ cyclicFailures → r.judgment = .ungrammatical ∧
      ∀ v ∈ root? r, ∀ i ∈ scope? r, ∀ s ∈ suffixes? r, Licensed v i ∧ s ∈ spellOut rules i := by
  decide +kernel

/-- Every order of applicative and passive the paper accepts is spelled out from a scope the
applied role allows, and every order so spelled out is accepted in some sentence ((27)–(31)). -/
theorem rows_passive :
    (∀ r ∈ Examples.all, ∀ ρ ∈ role? r, ∀ s ∈ suffixes? r, r.judgment = .acceptable →
      ∃ i ∈ ρ.passiveScopes, s ∈ spellOut rules i) ∧
    ∀ r ∈ Examples.all, ∀ ρ ∈ role? r, ∀ i ∈ ρ.passiveScopes, ∀ s ∈ spellOut rules i,
      ∃ r' ∈ Examples.all, role? r' = some ρ ∧ suffixes? r' = some s ∧
        r'.judgment = .acceptable := by
  decide +kernel

end HymanMchombo1992
