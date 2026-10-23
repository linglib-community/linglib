module

public import Linglib.Semantics.Possession.Relationalizer
public import Studies.Jenks2018
public import Linglib.Data.Examples.AhnZhu2025

/-!
# Ahn and Zhu (2025): A Bridge to Definiteness: Identifying Unique and Relational Definites through Bridging

Mandarin marks definiteness with bare nouns and with *na*-CL-N demonstrative descriptions. Ahn
and Zhu probe which mechanism each form carries through bridging, a definite whose referent was
never mentioned: part-whole bridging is resolvable by situational uniqueness, relational bridging
needs an anaphoric relatum. Four studies find that both forms bridge both ways, with a preference
for bare nouns in part-whole bridging; that English *that* is degraded where *na* is not; and,
decisively, that a bare noun bridges relationally only when the noun is lexically relational
(*zuozhe* 'author' but not *xiaoshuo-jia* 'novelist'), while *na* bridges with either. Neither an
anti-uniqueness presupposition on *na* nor an Index! principle forcing the indexed form whenever
an antecedent is available survives the data.

The analysis keeps the uniqueness ι for the bare noun and re-analyses *na* as a relationalizing
definite whose restrictor is the π-shifted noun, `ιx[P(x)(sᵣ) ∧ R(z,x)(sᵣ)]` for a contextual
relation `R` and an index `z`. That restrictor is `Possession.π P R z` (`na`); a relational
noun applied to the index is `Rel z`; felicity is `∃!` uniqueness. `na_of_two_satisfiers`
shows the relation restoring uniqueness
where the bare ι fails, `na_identity_iff` recovers the strong article as the identity-relation
case, and `na_iff_bare_of_related` isolates the situations where `R` is redundant and the two
forms compete on economy, which covers part-whole bridging (`na_seat_redundant`) and the moon.
The Study 4 item runs through both routes: the bare non-relational noun fails
(`bare_novelist_fails`) while `na_novelist`, `bare_author` and `na_ex_author` each pick the
author. `index_contradicted_by_bare_relational` states the comparison drawn with Index!, and the
closing theorems check the rows: *na* bridges everywhere (`na_bridges`), English *that* is out
in the paper's own bridging example (`that_degraded`), and the *of* and *de* diagnostics classify
the nouns (`of_iff_relational`, `de_of_relational`).

## TODO

The Studies' stimuli are printed unmarked, with mean ratings. The rating contrasts, that the bare
noun bridges relationally better with relational *author* than with sortal *novelist* (Study 4)
and that English *that* is degraded in bridging (Study 2), are results for `Data/Experiments`;
the claims over them are not yet stated.

## References

* [ahn-zhu-2025]
* [barker-2011]
* [jenks-2018]
* [schwarz-2009]
* [dayal-jiang-2023]
* [bremmers-etal-2022]
* [vikner-jensen-2002]
-/

@[expose] public section

namespace AhnZhu2025

open Possession

variable {E S : Type*} (P : E → S → Prop) (R : E → E → S → Prop) (z : E) (s : S)

/-! ### Bare nouns and *na* -/

/-- The *na* restrictor `na P R z x s ↔ P x s ∧ R z x s` is the noun relationalized by `π` with
the index `z` in the relatum slot, and the definite `ιx[P(x)(sᵣ) ∧ R(z,x)(sᵣ)]` is its `∃!`
witness. -/
abbrev na : E → S → Prop := π P R z

theorem na_of_two_satisfiers (h : ∃ a b, a ≠ b ∧ P a s ∧ P b s) (hR : ∃! x, P x s ∧ R z x s) :
    ¬ (∃! x, P x s) ∧ ∃! x, na P R z x s :=
  ⟨fun ⟨_, _, hu⟩ ↦ let ⟨_, _, hab, ha, hb⟩ := h; hab ((hu _ ha).trans (hu _ hb).symm), hR⟩

theorem na_identity_iff : (∃! x, na P (fun a b _ ↦ a = b) z x s) ↔ P z s :=
  ⟨fun ⟨_, ⟨h, hz⟩, _⟩ ↦ hz ▸ h, fun h ↦ ⟨z, ⟨h, rfl⟩, fun _ hy ↦ hy.2.symm⟩⟩

theorem na_iff_bare_of_related (h : ∀ x, P x s → R z x s) (x : E) : na P R z x s ↔ P x s :=
  ⟨And.left, fun hx ↦ ⟨hx, h x hx⟩⟩

theorem existsUnique_na_iff (h : ∀ x, P x s → R z x s) :
    (∃! x, na P R z x s) ↔ ∃! x, P x s :=
  existsUnique_congr (na_iff_bare_of_related P R z s h)

/-! ### Part-whole bridging: bike and seat -/

/-- The bike and its seat. -/
inductive Thing | bike | seat
  deriving DecidableEq

/-- *chezuo* 'seat'. -/
def seat : Thing → Unit → Prop := fun x _ ↦ x = .seat

/-- `partOf z x` holds when `x` is a part of `z`. -/
def partOf : Thing → Thing → Unit → Prop := fun z x _ ↦ z = .bike ∧ x = .seat

theorem bare_seat : ∃! x, seat x () := ⟨.seat, rfl, fun _ h ↦ h⟩

/-- *na ge chezuo* with `R` resolved to part-of has the same extension as the bare noun, so the
demonstrative's restriction is redundant and economy prefers the bare noun. -/
theorem na_seat_redundant (x : Thing) : na seat partOf .bike x () ↔ seat x () :=
  na_iff_bare_of_related seat partOf .bike () (fun _ h ↦ ⟨rfl, h⟩) x

/-! ### Relational bridging: the novel, its author, and another novelist -/

/-- The novel found, its author, and another novelist. -/
inductive Ind | theNovel | itsAuthor | anotherNovelist
  deriving DecidableEq

/-- *xiaoshuo-jia* 'novelist', a sortal noun true of both novelists. -/
def novelist : Ind → Unit → Prop := fun x _ ↦ x = .itsAuthor ∨ x = .anotherNovelist

/-- *zuozhe* 'author', where `author z x` holds when `x` is an author of `z`. -/
def author : Ind → Ind → Unit → Prop := fun z x _ ↦ z = .theNovel ∧ x = .itsAuthor

theorem bare_novelist_fails : ¬ ∃! x, novelist x () := by
  rintro ⟨x, -, hu⟩
  exact absurd ((hu _ (Or.inl rfl)).trans (hu _ (Or.inr rfl)).symm) (by decide)

theorem na_novelist : ∃! x, na novelist author .theNovel x () :=
  ⟨.itsAuthor, ⟨Or.inl rfl, rfl, rfl⟩, fun _ hy ↦ hy.2.2⟩

theorem bare_author : ∃! x, author .theNovel x () :=
  ⟨.itsAuthor, ⟨rfl, rfl⟩, fun _ hy ↦ hy.2⟩

/-- *na wei zuozhe* (53) is *na* over the relational noun with its relatum slot closed, and with
`R` resolved to the noun's own relation it is the bare relational reading. -/
theorem na_ex_author : ∃! x, na (⨆ z, author z) author .theNovel x () := by
  simpa only [na, π_iSup_self] using bare_author

/-! ### The Studies' rows -/

theorem na_bridges :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "naCL" →
      row.feature? "bridging_type" ≠ some "none" → row.judgment = .acceptable := by decide

theorem bare_partWhole :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "bare" →
      row.feature? "bridging_type" = some "partWhole" → row.judgment = .acceptable := by decide

theorem index_contradicted_by_bare_relational :
    ¬ Jenks2018.BareLicit Mandarin.Determiners.inventory (.bridging .relational) .none ∧
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "bare" →
      row.feature? "bridging_type" = some "relational" →
      row.feature? "noun_arity" = some "relational" → row.judgment = .acceptable :=
  ⟨by decide, by decide⟩

theorem that_degraded :
    ∀ row ∈ Examples.all, row.feature? "study" = some "none" →
      row.feature? "definite_form" = some "that" →
      row.feature? "bridging_type" ≠ some "none" → row.judgment ≠ .acceptable := by decide

theorem the_acceptable :
    ∀ row ∈ Examples.all, row.feature? "definite_form" = some "the" →
      row.judgment = .acceptable := by decide

theorem of_iff_relational :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "of" →
      (row.judgment = .acceptable ↔ row.feature? "noun_arity" = some "relational") := by decide

theorem de_of_relational :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "de" →
      row.feature? "noun_arity" = some "relational" → row.judgment = .acceptable := by decide

end AhnZhu2025
