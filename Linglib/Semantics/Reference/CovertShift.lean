module

public import Linglib.Semantics.Reference.Determiner

/-!
# Covert type shifts

A bare nominal becomes an argument by a covert type shift. Each shift makes a quantifier of the
restrictor: the definite ι and the anaphoric ι^x give the individual of the definite, ∃ the
existential over the restrictor, and kind formation ∩ the existential over the parts of the
restrictor's largest member, since a predicate of objects holds of a kind through its instances
(`CovertShift.quantifier`). On individuals with no proper parts ∩ and ι make the same quantifier;
with parts they differ, the individual of an entity lying below the existential over its parts
(`Quantifier.individual_le_some_Iic`).

A determiner lexicalizes a shift when it denotes that quantifier on every model
(`Determiner.Entry.Lexicalizes`). An article lexicalizes ι and ι^x by its strengths and ∃ by an
indefinite degree, a demonstrative and a possessive lexicalize none, and no determiner lexicalizes
∩ (`Determiner.Entry.not_lexicalizes_down`). The Blocking Principle bars a covert shift for the
nominals in the domain of a determiner that lexicalizes it (`Determiner.Inventory.Blocks`), and a
shift is available to a nominal when it is defined for it and not blocked
(`Determiner.Inventory.Available`).

Meaning Preservation ranks the shifts, and a bare nominal takes the highest-ranked of those
available. Both rankings in the literature have two tiers, and a two-tier ranking is the predicate
of its upper tier, `Prop` ordered by implication, so a shift applies when it is `MaximalFor` the
ranking among the available ones. Chierchia ranks ∩ alone above ι and ∃, `(· = .down)`, and Dayal
puts ι with ∩, `(· ≠ .exists)`, since ι too changes the type without adding quantificational
force. The two choose alike where no definite shift is available
(`CovertShift.maximalFor_available_eq_down_iff_ne_exists`) and part ways where ι is: under Dayal's
ranking ι applies whenever it is unblocked, under Chierchia's only where ∩ is undefined.

## Implementation notes

Whether ∩ is defined for a nominal is a proposition `down` that the consumer supplies; for
Chierchia's ∩ it is `Kind.down ∘ P ∈ K` (`Semantics/Reference/Kind.lean`). It depends on the
nominal's denotation and not on its number and countability alone, since a plural property
anchored to particular entities has no kind. The nominal's number is supplied too, since blocking
applies only within a determiner's domain. The quantifier of ∩ is taken at one situation and does
not record that restriction to kinds.

`Determiner.Entry.Lexicalizes` quantifies over models `(E W : Type)` inside a proposition, so the
models are in the lowest universe. A quantificational determiner is not counted as denoting the
quantifier of a shift: *some* leaves ∃ to the bare plural. An article's quantifiers are those of
its definite and indefinite readings, so no entry lexicalizes ∩; a definite determiner that also
forms kind terms, as Dayal analyses the Romance one, is a reading the entries do not record, and
`Studies/Dayal2004.lean` states that analysis on its own record of what a determiner
lexicalizes.

ι^x, the anaphoric definite of Jenks, postdates both rankings, and Moroney is the first to make
it a covert shift. It introduces no quantificational force, so Dayal's ranking puts it with ∩ and
ι, and Chierchia's with ι.

## References

* [chierchia-1998]
* [dayal-2004]
* [jenks-2018]
* [moroney-2021]
-/

@[expose] public section

/-- The covert type shifts are kind formation ∩, the definite ι and the existential ∃ of
[chierchia-1998], and the anaphoric definite ι^x of [jenks-2018], which [moroney-2021] makes
covert. -/
inductive CovertShift where
  | down
  | iota
  | iotaAnaphoric
  | exists
  deriving DecidableEq, Repr, Fintype

/-! ### The quantifier of a shift -/

namespace CovertShift

variable {E W : Type}

/-- The quantifier a covert shift makes of a restrictor: ι and ι^x give the individual of the
definite, ∃ the existential over the restrictor, and ∩ the existential over the parts of its
largest member, since a predicate of objects applies to a kind through its instances. -/
def quantifier [PartialOrder E] (τ : CovertShift) (R : (ℕ → E) → W → Set E) (d : ℕ) :
    (ℕ → E) → W → Quantifier E :=
  match τ with
  | .iota => (Definite.maximal R).quantifier
  | .iotaAnaphoric => (Definite.anaphoric R d).quantifier
  | .exists => fun g s ↦ Quantifier.Det.some (R g s)
  | .down => fun g s V ↦ ∃ x ∈ Definite.maximal R g s, Quantifier.Det.some (Set.Iic x) V

end CovertShift

namespace Determiner.Entry

open scoped Denotes

/-- A determiner lexicalizes a covert shift when it denotes the quantifier the shift makes of
every restrictor, on every model of individuals ordered by part-of, [dayal-2004]'s Blocking
Principle. An article lexicalizes ι and ι^x by its strengths and ∃ by an indefinite degree. A
demonstrative and a possessive lexicalize none, their presuppositions failing where the shifts
are defined (`not_lexicalizes_demonstrative`, `not_lexicalizes_possessive`), and no determiner
lexicalizes ∩ (`not_lexicalizes_down`): an article reaches the largest member of a restrictor
and not its parts. -/
def Lexicalizes (e : Entry) (τ : CovertShift) : Prop :=
  ∀ (E W : Type) [PartialOrder E] (R : (ℕ → E) → W → Set E) (d : ℕ),
    e.DenotesQuantifier R d (τ.quantifier R d)

/-- The restrictor true of everything, with two satisfiers in `Bool`, one above the other. -/
private abbrev top : (ℕ → Bool) → Unit → Set Bool := fun _ _ ↦ Set.univ

/-- The restrictor true of the larger of the two alone. -/
private abbrev one : (ℕ → Bool) → Unit → Set Bool := fun _ _ ↦ {true}

private theorem mem_maximal_top {g : ℕ → Bool} {x : Bool} :
    x ∈ Definite.maximal top g () ↔ x = true :=
  Definite.mem_maximal.trans
    ⟨fun h ↦ le_antisymm (Bool.le_true x) (h.2 (Set.mem_univ true)),
      fun h ↦ h ▸ ⟨trivial, fun b _ ↦ Bool.le_true b⟩⟩

private theorem mem_maximal_one {g : ℕ → Bool} {x : Bool} :
    x ∈ Definite.maximal one g () ↔ x = true :=
  Definite.mem_maximal.trans ⟨fun h ↦ h.1, fun h ↦ h ▸ isGreatest_singleton⟩

/-- The maximal definite picks the larger satisfier and the anaphoric one the indexed entity. -/
private theorem maximal_ne_anaphoric : Definite.maximal top ≠ Definite.anaphoric top 0 := by
  intro h
  have hm : false ∈ Definite.anaphoric top 0 (fun _ ↦ false) () :=
    Definite.mem_anaphoric.2 ⟨trivial, rfl⟩
  rw [← h, mem_maximal_top] at hm
  exact absurd hm (by decide)

/-- No reading of an article is the existential over two satisfiers. -/
private theorem ofStrength_quantifier_ne_some (p : Definite.Strength) :
    (Definite.ofStrength p top 0).quantifier ≠ fun g s ↦ Quantifier.Det.some (top g s) := by
  intro h
  have hs : (Definite.ofStrength p top 0).quantifier (fun _ ↦ true) () {false} :=
    (congrFun (congrFun (congrFun h fun _ ↦ true) ()) {false}).mpr ⟨false, trivial, rfl⟩
  obtain ⟨x, hx, hxf⟩ := hs
  cases p
  · exact absurd ((mem_maximal_top.1 hx).symm.trans hxf) (by decide)
  · exact absurd ((Definite.mem_anaphoric.1 hx).2.symm.trans hxf) (by decide)

theorem lexicalizes_article_iota_iff (a : Article) :
    (article a).Lexicalizes .iota ↔ .uniqueness ∈ a.strengths := by
  refine ⟨fun h ↦ ?_, fun h _ _ _ R d ↦ .inl ⟨_, ⟨_, h, rfl⟩, rfl⟩⟩
  rcases h Bool Unit top 0 with ⟨_, ⟨p, hp, rfl⟩, hk⟩ | ⟨-, hk⟩
  · cases p
    · exact hp
    · exact absurd (Definite.quantifier_injective hk).symm maximal_ne_anaphoric
  · exact absurd hk (ofStrength_quantifier_ne_some .uniqueness)

theorem lexicalizes_article_iotaAnaphoric_iff (a : Article) :
    (article a).Lexicalizes .iotaAnaphoric ↔ .familiarity ∈ a.strengths := by
  refine ⟨fun h ↦ ?_, fun h _ _ _ R d ↦ .inl ⟨_, ⟨_, h, rfl⟩, rfl⟩⟩
  rcases h Bool Unit top 0 with ⟨_, ⟨p, hp, rfl⟩, hk⟩ | ⟨-, hk⟩
  · cases p
    · exact absurd (Definite.quantifier_injective hk) maximal_ne_anaphoric
    · exact hp
  · exact absurd hk (ofStrength_quantifier_ne_some .familiarity)

theorem lexicalizes_article_exists_iff (a : Article) :
    (article a).Lexicalizes .exists ↔ ∃ δ ∈ a.definiteness, δ < .definite := by
  refine ⟨fun h ↦ ?_, fun h _ _ _ R d ↦ .inr ⟨h, rfl⟩⟩
  rcases h Bool Unit top 0 with ⟨_, ⟨p, -, rfl⟩, hk⟩ | ⟨h, -⟩
  · exact absurd hk (ofStrength_quantifier_ne_some p)
  · exact h

/-- An article does not lexicalize ∩: over a restrictor true of an individual and not of its
parts, ∩ holds of a set that has a part and lacks the individual, and no reading of the article
does. -/
theorem not_lexicalizes_article_down (a : Article) : ¬ (article a).Lexicalizes .down := by
  intro h
  have hd : CovertShift.quantifier .down one 0 (fun _ ↦ true) () {false} :=
    ⟨true, mem_maximal_one.2 rfl, false, Set.mem_Iic.2 (Bool.le_true false), rfl⟩
  rcases h Bool Unit one 0 with ⟨_, ⟨p, -, rfl⟩, hk⟩ | ⟨-, hk⟩
  · obtain ⟨x, hx, hxf⟩ := (congrFun (congrFun (congrFun hk fun _ ↦ true) ()) {false}).mpr hd
    cases p
    · exact absurd ((mem_maximal_one.1 hx).symm.trans hxf) (by decide)
    · exact absurd ((Definite.mem_anaphoric.1 hx).2.symm.trans hxf) (by decide)
  · obtain ⟨x, hx, hxf⟩ := (congrFun (congrFun (congrFun hk fun _ ↦ true) ()) {false}).mp hd
    exact absurd ((show x = true from hx).symm.trans hxf) (by decide)

/-- Every shift makes of the restrictor true of the one individual a quantifier that holds of
the set of everything. -/
private theorem quantifier_unit (τ : CovertShift) :
    τ.quantifier (fun (_ : ℕ → Unit) (_ : Unit) ↦ Set.univ) 0 (fun _ ↦ ()) () Set.univ := by
  have hm : () ∈ Definite.maximal (fun (_ : ℕ → Unit) (_ : Unit) ↦ Set.univ) (fun _ ↦ ()) () :=
    Definite.mem_maximal.2 ⟨trivial, fun _ _ ↦ le_rfl⟩
  cases τ
  · exact ⟨(), hm, (), Set.mem_Iic.2 le_rfl, trivial⟩
  · exact ⟨(), hm, trivial⟩
  · exact ⟨(), Definite.mem_anaphoric.2 ⟨trivial, rfl⟩, trivial⟩
  · exact ⟨(), trivial, trivial⟩

/-- A demonstrative lexicalizes no covert shift: where no referent has the indexed one in its
vicinity, it denotes nothing and each shift does. -/
theorem not_lexicalizes_demonstrative (dem : DemonstrativeDeterminer) (τ : CovertShift) :
    ¬ (demonstrative dem).Lexicalizes τ := fun h ↦ by
  obtain ⟨x, hx, -⟩ := (congrFun (congrFun (congrFun (h Unit Unit _ 0 ∅) fun _ ↦ ()) ())
    Set.univ).mpr (quantifier_unit τ)
  simpa using (DemonstrativeDeterminer.mem_denote.1 hx).1

/-- A possessive lexicalizes no covert shift: under the empty possession relation it denotes
nothing and each shift does. -/
theorem not_lexicalizes_possessive (p : PossessiveDeterminer) (τ : CovertShift) :
    ¬ (possessive p).Lexicalizes τ := fun h ↦ by
  obtain ⟨x, hx, -⟩ := (congrFun (congrFun (congrFun
    (h Unit Unit _ 0 (fun _ _ ↦ ()) fun _ _ _ _ ↦ False) fun _ ↦ ()) ()) Set.univ).mpr
    (quantifier_unit τ)
  rw [PossessiveDeterminer.denote_apply] at hx
  exact (Definite.mem_possessive.1 hx).1.2

theorem not_lexicalizes_quantifier (q : QuantificationalDeterminer) (τ : CovertShift) :
    ¬ (quantifier q).Lexicalizes τ :=
  fun h ↦ h Unit Unit (fun _ _ ↦ Set.univ) 0

theorem lexicalizes_iota_iff (e : Entry) : e.Lexicalizes .iota ↔ e.Marks .uniqueness := by
  cases e with
  | article a => exact lexicalizes_article_iota_iff a
  | demonstrative dem => exact iff_of_false (not_lexicalizes_demonstrative dem _) (by simp [Marks,
      strengths, uses])
  | quantifier q => exact iff_of_false (not_lexicalizes_quantifier q _) (by simp [Marks,
      strengths, uses])
  | possessive p => exact iff_of_false (not_lexicalizes_possessive p _) (by simp [Marks, strengths,
      uses])

theorem lexicalizes_iotaAnaphoric_iff (e : Entry) :
    e.Lexicalizes .iotaAnaphoric ↔ e.Marks .familiarity := by
  cases e with
  | article a => exact lexicalizes_article_iotaAnaphoric_iff a
  | demonstrative dem => exact iff_of_false (not_lexicalizes_demonstrative dem _) (by simp [Marks,
      strengths, uses])
  | quantifier q => exact iff_of_false (not_lexicalizes_quantifier q _) (by simp [Marks,
      strengths, uses])
  | possessive p => exact iff_of_false (not_lexicalizes_possessive p _) (by simp [Marks, strengths,
      uses])

theorem lexicalizes_exists_iff (e : Entry) :
    e.Lexicalizes .exists ↔ ∃ d ∈ e.definiteness, d < .definite := by
  cases e with
  | article a => exact lexicalizes_article_exists_iff a
  | demonstrative dem =>
    exact iff_of_false (not_lexicalizes_demonstrative dem _) (by simp [definiteness])
  | quantifier q => exact iff_of_false (not_lexicalizes_quantifier q _) (by simp [definiteness])
  | possessive p =>
    exact iff_of_false (not_lexicalizes_possessive p _) (by simp [definiteness])

/-- No determiner lexicalizes ∩. -/
theorem not_lexicalizes_down (e : Entry) : ¬ e.Lexicalizes .down := by
  cases e with
  | article a => exact not_lexicalizes_article_down a
  | demonstrative dem => exact not_lexicalizes_demonstrative dem _
  | quantifier q => exact not_lexicalizes_quantifier q _
  | possessive p => exact not_lexicalizes_possessive p _

instance (e : Entry) : DecidablePred e.Lexicalizes
  | .down => isFalse (not_lexicalizes_down e)
  | .iota => decidable_of_iff _ (lexicalizes_iota_iff e).symm
  | .iotaAnaphoric => decidable_of_iff _ (lexicalizes_iotaAnaphoric_iff e).symm
  | .exists => decidable_of_iff _ (lexicalizes_exists_iff e).symm

end Determiner.Entry

namespace Determiner.Inventory


/-- An inventory lexicalizes a covert shift when one of its determiners does. -/
def Lexicalizes (ds : Inventory) (τ : CovertShift) : Prop := ∃ e ∈ ds, e.Lexicalizes τ

instance (ds : Inventory) : DecidablePred ds.Lexicalizes := fun _ ↦ by
  unfold Lexicalizes; infer_instance

theorem not_lexicalizes_down (ds : Inventory) : ¬ ds.Lexicalizes .down :=
  fun ⟨e, _, h⟩ ↦ e.not_lexicalizes_down h

theorem lexicalizes_exists_iff (ds : Inventory) :
    ds.Lexicalizes .exists ↔ ds.Realizes .indefinite :=
  exists_congr fun e ↦ and_congr_right fun _ ↦ e.lexicalizes_exists_iff

theorem lexicalizes_iota_iff (ds : Inventory) : ds.Lexicalizes .iota ↔ ds.Realizes .unique :=
  exists_congr fun e ↦ and_congr_right fun _ ↦ e.lexicalizes_iota_iff

theorem lexicalizes_iotaAnaphoric_iff (ds : Inventory) :
    ds.Lexicalizes .iotaAnaphoric ↔ ds.Realizes .anaphoric :=
  exists_congr fun e ↦ and_congr_right fun _ ↦ e.lexicalizes_iotaAnaphoric_iff

/-- The Blocking Principle of [chierchia-1998], (39a) of [dayal-2004]: a covert shift is blocked
for a nominal of number `num` when a determiner whose domain holds such nominals lexicalizes it.
English *a* selects the singular, so it blocks ∃ for a bare singular and leaves ∃ to a bare plural
or a mass noun. An article marking familiarity alone, as Akan *nó*, leaves ι to the bare noun, and
a demonstrative blocks nothing. -/
def Blocks (ds : Inventory) (num : Number) (τ : CovertShift) : Prop :=
  ∃ e ∈ ds, e.Selects num ∧ e.Lexicalizes τ

instance (ds : Inventory) (num : Number) : DecidablePred (ds.Blocks num) := fun _ ↦ by
  unfold Blocks; infer_instance

variable {ds : Inventory} {num : Number} {τ : CovertShift}

theorem Blocks.lexicalizes (h : ds.Blocks num τ) : ds.Lexicalizes τ :=
  let ⟨e, he, _, h⟩ := h; ⟨e, he, h⟩

theorem not_blocks_down (ds : Inventory) (num : Number) : ¬ ds.Blocks num .down :=
  fun h ↦ ds.not_lexicalizes_down h.lexicalizes

/-- Where no determiner lexicalizing a shift selects a number, as no definite article in the
fragments does, a shift is blocked exactly when it is lexicalized. -/
theorem blocks_iff_lexicalizes (h : ∀ e ∈ ds, e.Lexicalizes τ → e.numberRestriction = none) :
    ds.Blocks num τ ↔ ds.Lexicalizes τ :=
  ⟨Blocks.lexicalizes, fun ⟨e, he, hl⟩ ↦ ⟨e, he, fun n hn ↦ by simp [h e he hl] at hn, hl⟩⟩

end Determiner.Inventory

/-! ### Availability and ranking -/

namespace Determiner.Inventory

/-- A covert shift is available to a bare nominal of number `num` in a language with the
determiners `ds` when it is defined for the nominal, ∩ only where `down` holds (for Chierchia's ∩,
`Kind.down ∘ P ∈ K`), and no determiner blocks it for that number. ∩ is undefined for a singular
count noun and for a property anchored to particular entities such as *parts of this machine*
([dayal-2004]'s fn. 1). -/
def Available (ds : Inventory) (num : Number) (down : Prop) (τ : CovertShift) : Prop :=
  (τ = .down → down) ∧ ¬ ds.Blocks num τ

instance (ds : Inventory) (num : Number) (down : Prop) [Decidable down] :
    DecidablePred (ds.Available num down) :=
  fun _ ↦ by unfold Available; infer_instance

variable {ds : Inventory} {num : Number} {down : Prop} {τ : CovertShift}

/-- A shift other than ∩ is available exactly when it is not blocked. -/
theorem available_iff_of_ne_down (h : τ ≠ .down) : ds.Available num down τ ↔ ¬ ds.Blocks num τ :=
  and_iff_right fun h' ↦ absurd h' h

end Determiner.Inventory

namespace CovertShift

private theorem maximalFor_prop_iff {ι : Type*} {P T : ι → Prop} {i : ι} :
    MaximalFor P T i ↔ P i ∧ (T i ∨ ∀ j, P j → ¬ T j) :=
  ⟨fun ⟨hi, h⟩ ↦ ⟨hi, or_iff_not_imp_left.2 fun hT _ hj hTj ↦ hT (h hj (fun _ ↦ hTj) hTj)⟩,
    fun ⟨hi, h⟩ ↦ ⟨hi, fun j hj _ hTj ↦ h.resolve_right fun h' ↦ h' j hj hTj⟩⟩

variable {A : CovertShift → Prop} {τ : CovertShift}

/-- Under Chierchia's ranking an available shift applies when it is ∩ or ∩ is unavailable. -/
theorem maximalFor_eq_down_iff :
    MaximalFor A (· = .down) τ ↔ A τ ∧ (τ = .down ∨ ¬ A .down) := by
  rw [maximalFor_prop_iff]
  exact and_congr_right fun _ ↦ or_congr_right
    ⟨fun h hd ↦ h _ hd rfl, fun h _ hj hd ↦ h (hd ▸ hj)⟩

/-- Under Dayal's ranking an available shift applies when it is not ∃ or only ∃ is available. -/
theorem maximalFor_ne_exists_iff :
    MaximalFor A (· ≠ .exists) τ ↔ A τ ∧ (τ ≠ .exists ∨ ∀ σ, A σ → σ = .exists) := by
  simp [maximalFor_prop_iff]

instance [DecidablePred A] : DecidablePred (MaximalFor A (· = CovertShift.down)) := fun _ ↦
  decidable_of_iff _ maximalFor_eq_down_iff.symm

instance [DecidablePred A] : DecidablePred (MaximalFor A (· ≠ CovertShift.exists)) := fun _ ↦
  decidable_of_iff _ maximalFor_ne_exists_iff.symm

open Determiner.Inventory

variable {ds : Determiner.Inventory} {num : Number} {down : Prop}

/-- Under Dayal's ranking ∩ applies wherever it is defined, since no determiner blocks it. -/
@[simp] theorem maximalFor_available_ne_exists_down :
    MaximalFor (ds.Available num down) (· ≠ .exists) .down ↔ down := by
  simp [maximalFor_ne_exists_iff, Available, not_blocks_down]

@[simp] theorem maximalFor_available_ne_exists_iota :
    MaximalFor (ds.Available num down) (· ≠ .exists) .iota ↔ ¬ ds.Blocks num .iota := by
  simp [maximalFor_ne_exists_iff, Available]

@[simp] theorem maximalFor_available_ne_exists_exists :
    MaximalFor (ds.Available num down) (· ≠ .exists) .exists ↔
      ¬ ds.Blocks num .exists ∧ ¬ down ∧ ds.Blocks num .iota ∧ ds.Blocks num .iotaAnaphoric := by
  simp only [maximalFor_ne_exists_iff, Available, ne_eq, not_true_eq_false, false_or]
  refine ⟨fun ⟨⟨_, h⟩, h'⟩ ↦ ⟨h, fun hd ↦ ?_, not_not.1 fun hι ↦ ?_, not_not.1 fun hx ↦ ?_⟩,
    fun ⟨h, hd, hι, hx⟩ ↦ ⟨⟨nofun, h⟩, fun σ ⟨hσ, hb⟩ ↦ ?_⟩⟩
  · exact absurd (h' .down ⟨fun _ ↦ hd, ds.not_blocks_down num⟩) nofun
  · exact absurd (h' .iota ⟨nofun, hι⟩) nofun
  · exact absurd (h' .iotaAnaphoric ⟨nofun, hx⟩) nofun
  · cases σ <;> simp_all

/-- Under Chierchia's ranking, too, ∩ applies wherever it is defined. -/
@[simp] theorem maximalFor_available_eq_down_down :
    MaximalFor (ds.Available num down) (· = .down) .down ↔ down := by
  simp [maximalFor_eq_down_iff, Available, not_blocks_down]

@[simp] theorem maximalFor_available_eq_down_iota :
    MaximalFor (ds.Available num down) (· = .down) .iota ↔ ¬ ds.Blocks num .iota ∧ ¬ down := by
  simp [maximalFor_eq_down_iff, Available, not_blocks_down]

@[simp] theorem maximalFor_available_eq_down_exists :
    MaximalFor (ds.Available num down) (· = .down) .exists ↔ ¬ ds.Blocks num .exists ∧ ¬ down := by
  simp [maximalFor_eq_down_iff, Available, not_blocks_down]

/-- Where the determiners block ι and ι^x, as a definite article used anaphorically does, the two
rankings select the same shifts. -/
theorem maximalFor_available_eq_down_iff_ne_exists (hι : ds.Blocks num .iota)
    (hx : ds.Blocks num .iotaAnaphoric) :
    MaximalFor (ds.Available num down) (· = .down) τ ↔
      MaximalFor (ds.Available num down) (· ≠ .exists) τ := by
  cases τ
  case iotaAnaphoric =>
    simp [maximalFor_eq_down_iff, maximalFor_ne_exists_iff, Available, hx]
  all_goals simp [hι, hx]

end CovertShift
