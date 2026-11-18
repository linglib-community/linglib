module

public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Relation.ReflTransGen
public import Studies.Buring2015
public import Studies.HartmannZimmermann2004
public import Linglib.Fragments.Hausa.Focus
public import Linglib.Data.Examples.AssmannEtAl2023
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Assmann, Büring, Jordanoska and Prüller (2023): Towards a Theory of Morphosyntactic Focus Marking

In languages that mark focus morphosyntactically, each focal marking marks one constituent,
possibly the whole clause, which may realize any focus within it, and Blocking chooses the most
specific marking available. [Each marking then realizes a continuous section of the
tree](##ordConnected_usable), and [none of its node's daughters exactly when each has a marking
of its own](##exocentric_iff), as Gùrùntùm's clausal marking does. English marks the clause by
default prosody and each default-weak daughter by reversal, and [Büring's unalternative semantics
is Blocking over that inventory](##target_mem_clause_iff), except that [a focus on subject and
verb is marked like narrow verb focus](##subject_verb), where the languages whose domain of focal
marking is the clause [mark it like the clause](##rows_marking).

## Implementation notes

* A focus is the set of its parts, so that non-constituent foci such as subject and verb are
  foci too; a constituent focus is a singleton.
* The clause skeleton has subject and VP, and verb and object within VP. Hausa's absolute form and
  Awing's absence of marking mark the clause, as the paper's default.
* An exocentric marking is defined by the first of the paper's two formulations, realizing no
  subconstituent; the second, realizing no one-word focus, agrees with it on every inventory
  here.
* The English theorems hold for any meanings of subject, verb and object, and any alternatives
  to them that differ from them.

## TODO

* [hartmann-zimmermann-2009] report narrow verb focus with a null object pronoun and no marker at
  all ((19a), (20a)), which the VP marking does not cover; their account ranks structural
  constraints on the marker's position above Focus Prominence (Sect. 3.3).
* Foci below the skeleton: the Gùrùntùm intra-VP phrase of footnote 4, whose own marking blocks
  the VP marking, the Hausa part-of-subject focus of (15), and the object-internal columns of
  Table 2.
* Focality (48) over several domains of focal marking, for the Wolof and Hausa double markings
  (42) and (43).

## References

* [assmann-etal-2023]
* [buring-2015]
* [hartmann-zimmermann-2004]
* [hartmann-zimmermann-2009]
* [fominyam-simik-2017]
-/

@[expose] public section

namespace AssmannEtAl2023

open Set WithAlternatives UnalternativeSemantics Buring2015

/-! ### Blocking -/

section Blocking

variable {C : Type*} [PartialOrder C] {inv F : Set C} {m m' d d' f g j : C}

/-- Blocking (45): a marking of constituent `m` is usable for a focus whose parts are `F` when `m`
is minimal among the constituents of the inventory that contain every part. -/
def Usable (inv : Set C) (m : C) (F : Set C) : Prop := Minimal (· ∈ inv ∩ upperBounds F) m

theorem usable_iff : Usable inv m F ↔
    m ∈ inv ∧ (∀ x ∈ F, x ≤ m) ∧ ∀ c ∈ inv, (∀ x ∈ F, x ≤ c) → c ≤ m → c = m := by
  simp only [Usable, minimal_iff, mem_inter_iff, mem_upperBounds, and_imp, and_assoc, eq_comm]

instance [Fintype C] [DecidableEq C] [DecidableLE C] [DecidablePred (· ∈ inv)]
    [DecidablePred (· ∈ F)] : Decidable (Usable inv m F) :=
  decidable_of_iff _ usable_iff.symm

theorem usable_singleton_iff :
    Usable inv m {f} ↔ m ∈ inv ∧ f ≤ m ∧ ∀ c ∈ inv, f ≤ c → c ≤ m → c = m := by
  simp [usable_iff]

-- Sect. 6.5
theorem usable_iff_of_isLUB (h : IsLUB F j) : Usable inv m F ↔ Usable inv m {j} := by
  have : upperBounds F = Ici j := Set.ext fun c ↦ (isLUB_iff_le_iff.1 h c).symm
  rw [Usable, Usable, this, upperBounds_singleton]

theorem Usable.of_le (h : Usable inv m {f}) (hfg : f ≤ g) (hgm : g ≤ m) : Usable inv m {g} := by
  rw [usable_singleton_iff] at *
  exact ⟨h.1, hgm, fun c hc hgc ↦ h.2.2 c hc (hfg.trans hgc)⟩

/-- The foci a marking realizes form a continuous section of the tree: with two foci it realizes
every constituent between them (p. 1376). -/
theorem ordConnected_usable : {f | Usable inv m {f}}.OrdConnected :=
  ⟨fun _ hf _ hg _ hx ↦ hf.of_le hx.1 (hx.2.trans (usable_singleton_iff.1 hg).2.1)⟩

-- p. 1376
theorem Usable.unique (hF : IsChain (· ≤ ·) (upperBounds F)) (h : Usable inv m F)
    (h' : Usable inv m' F) : m = m' :=
  (hF.total h.prop.2 h'.prop.2).elim (fun hle ↦ (h'.eq_of_ge h.prop hle).symm) (h.eq_of_ge h'.prop)

-- footnote 24
theorem usable_iff_notMem_of_covBy (hm : m ∈ inv) (hd : d ⋖ m) : Usable inv m {d} ↔ d ∉ inv := by
  rw [usable_singleton_iff]
  refine ⟨fun h hd' ↦ hd.ne (h.2.2 d hd' le_rfl hd.le), fun h ↦ ⟨hm, hd.le, fun c hc hdc hcm ↦ ?_⟩⟩
  obtain rfl | hdc := hdc.eq_or_lt
  · exact absurd hc h
  · exact hcm.eq_of_not_lt (hd.2 hdc)

/-- An exocentric marking marks a complex constituent and realizes no focus below it. -/
def Exocentric (inv : Set C) (m : C) : Prop := ¬ IsMin m ∧ ∀ f, Usable inv m {f} ↔ f = m

/-- A disjunctive marking realizes foci on two disjoint constituents. -/
def Disjunctive (inv : Set C) (m : C) : Prop :=
  ∃ a b, ¬ a ≤ b ∧ ¬ b ≤ a ∧ Usable inv m {a} ∧ Usable inv m {b}

section Decidable

variable [Fintype C] [DecidableEq C] [DecidableLE C] [DecidablePred (· ∈ inv)]

instance : Decidable (Exocentric inv m) :=
  inferInstanceAs (Decidable (¬ (∀ b, b ≤ m → m ≤ b) ∧ ∀ f, Usable inv m {f} ↔ f = m))

instance : Decidable (Disjunctive inv m) :=
  inferInstanceAs (Decidable (∃ a b, ¬ a ≤ b ∧ ¬ b ≤ a ∧ Usable inv m {a} ∧ Usable inv m {b}))

end Decidable

/-- A marking of a complex constituent is exocentric exactly when each daughter of the
constituent has a marking of its own (p. 1373). -/
theorem exocentric_iff [IsStronglyCoatomic C] :
    Exocentric inv m ↔ ¬ IsMin m ∧ m ∈ inv ∧ ∀ d, d ⋖ m → d ∈ inv := by
  refine ⟨fun ⟨hm, h⟩ ↦ ⟨hm, ((h m).2 rfl).prop.1, fun d hd ↦ ?_⟩, fun ⟨hmin, hm, h⟩ ↦
    ⟨hmin, fun f ↦ ⟨fun hu ↦ ?_, ?_⟩⟩⟩
  · by_contra hd'
    exact hd.ne ((h d).1 ((usable_iff_notMem_of_covBy ((h m).2 rfl).prop.1 hd).2 hd'))
  · refine (usable_singleton_iff.1 hu).2.1.eq_of_not_lt fun hf ↦ ?_
    obtain ⟨d, hfd, hd⟩ := exists_le_covBy_of_lt hf
    exact hd.ne ((usable_singleton_iff.1 hu).2.2 d (h d hd) hfd hd.le)
  · rintro rfl
    exact usable_singleton_iff.2 ⟨hm, le_rfl, fun c _ hc hcm ↦ le_antisymm hcm hc⟩

-- p. 1372
theorem disjunctive_of_covBy (hm : m ∈ inv) (hd : d ⋖ m) (hd' : d' ⋖ m) (hne : d ≠ d')
    (h : d ∉ inv) (h' : d' ∉ inv) : Disjunctive inv m :=
  ⟨d, d', fun hle ↦ hd.2 (hle.lt_of_ne hne) hd'.lt, fun hle ↦ hd'.2 (hle.lt_of_ne hne.symm) hd.lt,
    (usable_iff_notMem_of_covBy hm hd).2 h, (usable_iff_notMem_of_covBy hm hd').2 h'⟩

end Blocking

/-! ### The clause skeleton -/

/-- Subject and VP within the clause; verb and object within VP. -/
inductive Node
  | s | sbj | vp | v | obj
  deriving DecidableEq, Repr, Fintype

/-- The constituent immediately containing each node other than the clause. -/
def Node.parent : Node → Option Node
  | .s => none
  | .sbj | .vp => some .s
  | .v | .obj => some .vp

/-- Constituent containment, generated by the parent relation. -/
instance : PartialOrder Node :=
  partialOrderOfAcyclic (fun a b : Node ↦ a.parent = some b) (by decide)

instance : DecidableLE Node :=
  decidableLEOfCovers (covers := fun a b : Node ↦ a.parent = some b) [.s, .vp] (by decide)

instance : DecidableLT Node := decidableLTOfDecidableLE

theorem Node.covBy_iff {a b : Node} : a ⋖ b ↔ a.parent = some b := by
  simp only [CovBy]
  revert a b
  decide

/-! ### Inventories -/

/-- Gùrùntùm marks the subject by *a* before it, the VP by *a* between verb and object, and
the clause by clause-final *á* (35b). -/
def guruntum : Finset Node := {.sbj, .vp, .s}

/-- Buli marks the clause by *(à)lē* after the subject, the VP by *ká* before the object, and
the verb by *kámā* after the VP (35a). -/
def buli : Finset Node := {.s, .vp, .v}

/-- In Hausa the relative form marks the subject, and the absolute form, the default, marks the
clause (16). -/
def hausa : Finset Node := {.sbj, .s}

/-- Wolof marks the subject by *a*, the object by *la* with fronting, the VP by *da(fa)*, and the
clause by *na* or *ngi* (21). -/
def wolof : Finset Node := {.sbj, .obj, .vp, .s}

/-- Aymara marks the subject and the object by *-wa* on them, and the clause by *-wa* on the
verb (40). -/
def aymara : Finset Node := {.sbj, .obj, .s}

/-- Awing has no marking but that of the unmarked clause (41). -/
def awing : Finset Node := {.s}

-- Table 2
theorem usable_guruntum (m f : Node) :
    Usable guruntum m {f} ↔ m = if f ≤ .sbj then .sbj else if f ≤ .vp then .vp else .s := by
  revert m f; decide

-- Table 2
theorem usable_buli (m f : Node) :
    Usable buli m {f} ↔ m = if f ≤ .v then .v else if f ≤ .vp then .vp else .s := by
  revert m f; decide

-- Table 2
theorem usable_hausa (m f : Node) : Usable hausa m {f} ↔ m = if f ≤ .sbj then .sbj else .s := by
  revert m f; decide

-- Table 2
theorem usable_wolof (m f : Node) :
    Usable wolof m {f} ↔
      m = if f ≤ .sbj then .sbj else if f ≤ .obj then .obj else if f ≤ .vp then .vp else .s := by
  revert m f; decide

-- Table 2
theorem usable_aymara (m f : Node) :
    Usable aymara m {f} ↔ m = if f ≤ .sbj then .sbj else if f ≤ .obj then .obj else .s := by
  revert m f; decide

-- Table 2
theorem usable_awing (m f : Node) : Usable awing m {f} ↔ m = .s := by
  revert m f; decide

-- (29), Sect. 4.2.3
theorem guruntum_exocentric_disjunctive :
    Exocentric (guruntum : Set Node) .s ∧ Disjunctive (guruntum : Set Node) .vp := by
  refine ⟨exocentric_iff.2 ⟨fun h ↦ absurd (h (by decide : Node.sbj ≤ .s)) (by decide), by decide,
    fun d ↦ ?_⟩,
    disjunctive_of_covBy (d := .v) (d' := .obj) (by decide) (Node.covBy_iff.2 rfl)
      (Node.covBy_iff.2 rfl) (by decide) (by decide) (by decide)⟩
  rw [Node.covBy_iff]
  revert d
  decide

/-! ### The Hausa particle -/

/-- The gender of each node of a Hausa clause, given those of its subject and object: a verb, a
verb phrase and a clause have none. -/
def hausaGender (sbj obj : Option Hausa.Gender.Value) : Node → Option Hausa.Gender.Value
  | .sbj => sbj
  | .obj => obj
  | _ => none

-- (14), (17), p. 1359
theorem stabilizer_of_usable_obj {m : Node} (h : Usable hausa m {.obj})
    (gs go : Option Hausa.Gender.Value) :
    Hausa.stabilizer (hausaGender gs go m) = Hausa.ne ∧
      Hausa.stabilizer (hausaGender gs (some Hausa.kaza.gender) .obj) = Hausa.ce := by
  obtain rfl : m = .s := ((usable_hausa m .obj).1 h).trans (by decide)
  exact ⟨rfl, (Hausa.stabilizer_eq_ce_iff _).2 rfl⟩

/-! ### Tangale and the reflex analysis -/

open HartmannZimmermann2004

/-- Tangale follows Hausa in the progressive, where only subject focus must be marked
(footnote 13), and Gùrùntùm in the perfective, where verb, VP and object focus share a marking
(footnote 18). -/
def tangale : Tangale.TAM → Option (Finset Node)
  | .continuous => some hausa
  | .perfective => some guruntum
  | _ => none

/-- The focused constituent of a configuration as a node. -/
def focusNode : Focused → Node
  | .subject => .sbj
  | .verb => .v
  | .vp => .vp
  | .object => .obj

theorem overt_iff_not_usable_s :
    ∀ c : Config, c.WF → ∀ inv ∈ tangale c.tam,
      ((realize c).Nonempty ↔ ¬ Usable inv .s {focusNode c.focused}) := by
  intro c
  obtain ⟨f, a, t⟩ := c
  cases f <;> cases a <;> cases t <;> decide

/-! ### English -/

/-- The default-weak daughter of a branching node: English stresses the right daughter by
default (36a). -/
def Node.weakDaughter : Node → Option Node
  | .s => some .sbj
  | .vp => some .v
  | _ => none

/-- English focally marks the clause by default prosody and each default-weak daughter by
reversal (36b). -/
def english : Finset Node :=
  insert .s (Finset.univ.filter fun n ↦ ∃ p : Node, p.weakDaughter = some n)

-- Table 2
theorem usable_english (m f : Node) :
    Usable english m {f} ↔ m = if f ≤ .sbj then .sbj else if f ≤ .v then .v else .s := by
  revert m f; decide

-- p. 1374, p. 1384
theorem english_not_exocentric_disjunctive (m : Node) :
    ¬ Exocentric (english : Set Node) m ∧ ¬ Disjunctive (english : Set Node) m := by
  revert m; decide

/-- The node a prosody of the clause marks, given restrictions on the subject and on the verb:
reversal marks the daughter it promotes, and default prosody the clause (49), (52). A reversal
inside a demoted VP marks nothing. -/
def marked : Restriction → Restriction → Option Node
  | .weak, .weak => some .s
  | .strong, .weak => some .sbj
  | .weak, .strong => some .v
  | .strong, .strong => none

/-- The node of each of Büring's words. -/
def wordNode : Word → Node
  | .subj => .sbj
  | .verb => .v
  | .obj => .obj

/-- The words a focus on the parts `F` contains. -/
def words (F : Finset Node) : Finset Word := Finset.univ.filter fun w ↦ ∃ x ∈ F, wordNode w ≤ x

section English

variable {E R O : Type*} {s s' : E} {v v' : R} {o o' : O}

/-- Büring's unalternative semantics is Blocking over the English inventory: a constituent can be
the focus of a prosody exactly when the node the prosody marks is usable for it (Sect. 6.4). -/
theorem target_mem_clause_iff (hs : s' ≠ s) (hv : v' ≠ v) (ho : o' ≠ o) (ρ ρ' : Restriction)
    (f : Node) :
    target (s, v, o) (s', v', o') (words {f}) ∈ (clause s v o ρ ρ').alternatives ↔
      ∃ m ∈ marked ρ ρ', Usable english m {f} := by
  cases ρ <;> cases ρ' <;>
    simp only [target_mem_clause_weak_weak s v o hs hv ho, target_mem_clause_weak_strong s v o hv ho,
      target_mem_clause_strong_weak s v o hs hv ho, alternatives_clause_strong_strong,
      Set.mem_empty_iff_false,
      marked, Option.mem_def, Option.some.injEq, reduceCtorEq, false_and, exists_false] <;>
    revert f <;> decide

theorem isLUB_sbj_v : IsLUB {Node.sbj, .v} .s := by
  refine ⟨?_, fun x hx ↦ ?_⟩
  · simp only [upperBounds_insert, upperBounds_singleton, Set.mem_inter_iff, Set.mem_Ici]
    decide
  · simp only [upperBounds_insert, upperBounds_singleton, Set.mem_inter_iff, Set.mem_Ici] at hx
    revert x
    decide

/-- English marks a focus on subject and verb like narrow verb focus, which Blocking within the
clause forbids, since the smallest constituent containing both is the clause; in a language whose
domain of focal marking is the clause, such a focus is marked like the clause (Sect. 6.5). -/
theorem subject_verb (hv : v' ≠ v) (ho : o' ≠ o) :
    target (s, v, o) (s', v', o') (words {.sbj, .v}) ∈ (clause s v o .weak .strong).alternatives ∧
      ¬ Usable (english : Set Node) .v {.sbj, .v} ∧
      ∀ (inv : Set Node) m, Usable inv m {.sbj, .v} ↔ Usable inv m {.s} := by
  refine ⟨?_, ?_, fun _ _ ↦ usable_iff_of_isLUB isLUB_sbj_v⟩
  · rw [target_mem_clause_weak_strong s v o hv ho]
    decide
  · rw [usable_iff]
    decide

end English

/-! ### The paper's examples -/

/-- A reading as the focused constituent. -/
def Node.parse? : String → Option Node
  | "subject" => some .sbj
  | "verb" => some .v
  | "VP" => some .vp
  | "object" => some .obj
  | "clause" => some .s
  | _ => none

/-- The parts of the focus of a reading. -/
def focus? : String → Option (Finset Node)
  | "subject and verb" => some {.sbj, .v}
  | x => (Node.parse? x).map ({·})

/-- The inventory of a row's language. -/
def inventory? (r : Datum) : Option (Finset Node) :=
  r.byLanguage [(.guruntumMbaaru, guruntum), (.buliGhana, buli), (.hausa, hausa),
    (.wolof, wolof), (.centralAymara, aymara), (.awing, awing)]

/-- The constituent a row's marking marks as focal. -/
def marked? (r : Datum) : Option Node :=
  (r.byLanguage
    [(.guruntumMbaaru, [("a before subject", .sbj), ("a between verb and object", .vp),
        ("a clause-final", .s)]),
      (.buliGhana, [("le after subject", .s), ("ka before object", .vp), ("kama after VP", .v)]),
      (.hausa, [("relative form", .sbj), ("absolute form", .s)]),
      (.wolof, [("a", .sbj), ("la", .obj), ("dafa", .vp), ("na", .s), ("ngi", .s)]),
      (.centralAymara, [("wa on verb", .s)]), (.awing, [("none", .s)])]).bind
    (r.parse? "marking")

/-- The restrictions an English row's prosody puts on the subject and on the verb. -/
def prosody? (r : Datum) : Option (Restriction × Restriction) :=
  (r.byLanguage [(.english, [("nuclear stress on verb", (.weak, .strong))])]).bind
    (r.parse? "marking")

/-- Every reading of a row is acceptable and realized by the marking the row shows, which is
usable for it in its language's inventory. -/
theorem rows_marking :
    ∀ r ∈ Examples.all, ∀ inv ∈ inventory? r, ∀ m ∈ marked? r, ∀ x ∈ r.readings,
      ∀ F ∈ focus? x.1, x.2 = .acceptable ∧ Usable inv m F := by
  decide

/-- The particle a Hausa row shows. -/
def particle? (r : Datum) : Option Particle :=
  (r.byLanguage [(.hausa, [("cee after subject", Hausa.ce), ("nee clause-final", Hausa.ne),
    ("nee after subject", Hausa.ne), ("nee after object", Hausa.ne)])]).bind
    (r.parse? "particle")

-- (13), (14), (17)
theorem rows_stabilizer :
    ∀ r ∈ Examples.all, marked? r = some .s → ∀ p ∈ particle? r, p = Hausa.stabilizer none := by
  decide

-- (53)
theorem rows_english {E R O : Type*} {s s' : E} {v v' : R} {o o' : O} (hv : v' ≠ v)
    (ho : o' ≠ o) :
    ∀ r ∈ Examples.all, ∀ p ∈ prosody? r, ∀ x ∈ r.readings, ∀ F ∈ focus? x.1,
      (x.2 = .acceptable ↔
        target (s, v, o) (s', v', o') (words F) ∈ (clause s v o p.1 p.2).alternatives) := by
  have h : ∀ r ∈ Examples.all, ∀ p ∈ prosody? r, p = (.weak, .strong) := by decide
  have h' : ∀ r ∈ Examples.all, (.weak, .strong) ∈ prosody? r → ∀ x ∈ r.readings,
      ∀ F ∈ focus? x.1, (x.2 = .acceptable ↔ .verb ∈ words F ∧ .obj ∉ words F) := by decide
  intro r hr p hp
  obtain rfl := h r hr p hp
  simpa only [target_mem_clause_weak_strong s v o hv ho] using h' r hr hp

end AssmannEtAl2023
