module

public import Linglib.Syntax.Agreement.Target
public import Linglib.Fragments.Slavic.Russian.Case
public import Linglib.Fragments.Slavic.Russian.Gender

/-!
# Russian agreement targets

This file defines the Russian agreement targets whose forms Wade's grammar tabulates, the long
and the short adjective and the nonpast and the past finite verb, by their endings in each cell,
and derives what each inflects for.

A cell gives a person, a number, a gender with its animacy subgender and a case, Russian having
no definiteness. The long adjective is attributive and predicative and inflects for gender,
number and case, its subgender showing in the accusative. The short adjective is predicative and
inflects for gender and number. The nonpast verb of either conjugation inflects for person and
number, and the past tense for gender and number but not person, so that the two tenses of the
verb differ in what they agree in, as Corbett observes.

## Implementation notes

Whether an inflected value is copied from a controller is a question about a position and is
left to the studies: a predicative long form is inflected for case, but its case is fixed by
the copula, nominative or instrumental (Wade §156), rather than shared with the subject.

The feminine instrumental singular of the long adjective has a variant *-oju*, which survives
mainly in poetry (Wade §145) and which the table leaves out.

## References

* [wade-2020]
* [corbett-1998]
-/

@[expose] public section

namespace Russian.Agreement

open _root_.Agreement Function

/-! ### Cells -/

/-- The values Russian distinguishes in each dimension are the persons of the tripartition, the
singular and the plural, the genders with their subgenders, and the six cases, and it
distinguishes no definiteness. -/
abbrev Value : Dimension → Type
  | .person => {p : Person // ¬ p.MarksClusivity}
  | .number => Gender.numberSystem.values
  | .gender => Gender.Value × Gender.Animacy
  | .case => Case
  | .definiteness => Unit

/-- A cell of a Russian paradigm, a value in each dimension. -/
abbrev Cell := (d : Dimension) → Value d

/-- The third person masculine inanimate nominative singular, the cell from which the witnesses of
inflection depart. -/
private def base : Cell
  | .person => ⟨.third, by decide⟩
  | .number => Gender.numberSystem.value .singular
  | .gender => (.masc, .inanimate)
  | .case => .nom
  | .definiteness => ()

/-! ### The long adjective -/

/-- The endings of the hard-stem long adjective. -/
inductive LongEnding where
  /-- *-yj* (-ый). -/
  | yj
  /-- *-aja* (-ая). -/
  | aja
  /-- *-oe* (-ое). -/
  | oe
  /-- *-ye* (-ые). -/
  | ye
  /-- *-ogo* (-ого). -/
  | ogo
  /-- *-uju* (-ую). -/
  | uju
  /-- *-oj* (-ой). -/
  | oj
  /-- *-omu* (-ому). -/
  | omu
  /-- *-ym* (-ым). -/
  | ym
  /-- *-om* (-ом). -/
  | om
  /-- *-yx* (-ых). -/
  | yx
  /-- *-ymi* (-ыми). -/
  | ymi
  deriving DecidableEq, Repr, Fintype

/-- The ending of the hard-stem long adjective *nóvyj* 'new' by the gender and subgender of its
controller, its number and its case, the table of [wade-2020] §145. -/
def longEnding (g : Gender.Value) (a : Gender.Animacy) (n : Gender.numberSystem.values)
    (c : Case) : LongEnding :=
  Gender.numberSystem.elim (n := n)
    (match g, a, c with
      | .masc, _, .nom => .yj
      | .masc, .animate, .acc => .ogo
      | .masc, .inanimate, .acc => .yj
      | .fem, _, .nom => .aja
      | .fem, _, .acc => .uju
      | .fem, _, _ => .oj
      | .neut, _, .nom | .neut, _, .acc => .oe
      | _, _, .gen => .ogo
      | _, _, .dat => .omu
      | _, _, .inst => .ym
      | _, _, .loc => .om)
    (match a, c with
      | _, .nom => .ye
      | .animate, .acc => .yx
      | .inanimate, .acc => .ye
      | _, .gen | _, .loc => .yx
      | _, .dat => .ym
      | _, .inst => .ymi)

/-- The long adjective, used attributively and predicatively ([wade-2020] §155, §156), inflects
for gender, number and case. -/
def longAdjective : Target Value LongEnding :=
  .ofDependsOn {.attributive, .predicate}
    (fun x ↦ longEnding (x .gender).1 (x .gender).2 (x .number) (x .case)) {.gender, .number, .case}
    (fun x y h ↦ by simp only [h .gender (by simp), h .number (by simp), h .case (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, (.fem, .inanimate), by decide⟩,
        ⟨base, Gender.numberSystem.value .plural, by decide⟩, ⟨base, .gen, by decide⟩⟩)

/-- The animate accusative of the long adjective is its genitive exactly in the masculine
singular and the plural ([wade-2020] §47). -/
theorem longEnding_animate_acc_eq_gen_iff (g : Gender.Value) (n : Gender.numberSystem.values) :
    longEnding g .animate n .acc = longEnding g .animate n .gen ↔ g = .masc ∨ n.1 = .plural := by
  revert g n
  decide

theorem longEnding_inanimate_acc_eq_nom_iff (g : Gender.Value) (n : Gender.numberSystem.values) :
    longEnding g .inanimate n .acc = longEnding g .inanimate n .nom ↔
      g ≠ .fem ∨ n.1 = .plural := by
  revert g n
  decide

theorem injective_longEnding_nom (a : Gender.Animacy) :
    Injective (longEnding · a (Gender.numberSystem.value .singular) .nom) := by
  cases a <;> decide

/-! ### The short adjective -/

/-- The endings of the short adjective. -/
inductive ShortEnding where
  /-- No ending. -/
  | zero
  /-- *-a* (-а). -/
  | a
  /-- *-o* (-о). -/
  | o
  /-- *-y* (-ы). -/
  | y
  deriving DecidableEq, Repr, Fintype

/-- The ending of the short adjective *suróv* 'severe' by gender and number ([wade-2020] §159). -/
def shortEnding (g : Gender.Value) : Gender.numberSystem.values → ShortEnding :=
  Gender.numberSystem.elim (match g with | .masc => .zero | .fem => .a | .neut => .o) .y

/-- The short adjective, used predicatively ([wade-2020] §144), inflects for gender and
number. -/
def shortAdjective : Target Value ShortEnding :=
  .ofDependsOn {.predicate} (fun x ↦ shortEnding (x .gender).1 (x .number)) {.gender, .number}
    (fun x y h ↦ by simp only [h .gender (by simp), h .number (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, (.fem, .inanimate), by decide⟩,
        ⟨base, Gender.numberSystem.value .plural, by decide⟩⟩)

/-! ### The finite verb -/

/-- The two conjugations, of the endings in *-e-* and in *-i-* ([wade-2020] §213). -/
inductive Conjugation where
  | first
  | second
  deriving DecidableEq, Repr, Fintype

/-- The endings of the nonpast. -/
inductive NonpastEnding where
  /-- *-u* (-ю, or -у after a consonant). -/
  | u
  /-- *-eš'* (-ешь). -/
  | eš'
  /-- *-et* (-ет). -/
  | et
  /-- *-em* (-ем). -/
  | em
  /-- *-ete* (-ете). -/
  | ete
  /-- *-ut* (-ют, or -ут after a consonant). -/
  | ut
  /-- *-iš'* (-ишь). -/
  | iš'
  /-- *-it* (-ит). -/
  | it
  /-- *-im* (-им). -/
  | im
  /-- *-ite* (-ите). -/
  | ite
  /-- *-at* (-ят, or -ат after a palatal sibilant). -/
  | at
  deriving DecidableEq, Repr, Fintype

/-- The nonpast ending by conjugation, person and number ([wade-2020] §213). Clusivity is not
distinguished, so both first persons take the first person's ending. -/
def nonpastEnding (k : Conjugation) (p : Person) : Gender.numberSystem.values → NonpastEnding :=
  Gender.numberSystem.elim
    (match k, p with
      | .first, .second => .eš'
      | .first, .third => .et
      | .second, .second => .iš'
      | .second, .third => .it
      | _, _ => .u)
    (match k, p with
      | .first, .second => .ete
      | .first, .third => .ut
      | .first, _ => .em
      | .second, .second => .ite
      | .second, .third => .at
      | .second, _ => .im)

/-- The nonpast finite verb of each conjugation is predicative and inflects for person and
number. -/
def nonpastVerb (k : Conjugation) : Target Value NonpastEnding :=
  .ofDependsOn {.predicate} (fun x ↦ nonpastEnding k (x .person).1 (x .number)) {.person, .number}
    (fun x y h ↦ by simp only [h .person (by simp), h .number (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, ⟨.first, by decide⟩, by cases k <;> decide⟩,
        ⟨base, Gender.numberSystem.value .plural, by cases k <;> decide⟩⟩)

/-- The endings of the past tense, added to its *-l-*. -/
inductive PastEnding where
  /-- No ending. -/
  | zero
  /-- *-a* (-а). -/
  | a
  /-- *-o* (-о). -/
  | o
  /-- *-i* (-и). -/
  | i
  deriving DecidableEq, Repr, Fintype

/-- The past ending by gender and number ([wade-2020] §230). -/
def pastEnding (g : Gender.Value) : Gender.numberSystem.values → PastEnding :=
  Gender.numberSystem.elim (match g with | .masc => .zero | .fem => .a | .neut => .o) .i

/-- The past finite verb is predicative and inflects for gender and number, *ja pisal* or *ja
pisala* 'I was writing' by the speaker's gender ([wade-2020] §230). -/
def pastVerb : Target Value PastEnding :=
  .ofDependsOn {.predicate} (fun x ↦ pastEnding (x .gender).1 (x .number)) {.gender, .number}
    (fun x y h ↦ by simp only [h .gender (by simp), h .number (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, (.fem, .inanimate), by decide⟩,
        ⟨base, Gender.numberSystem.value .plural, by decide⟩⟩)

theorem injective_pastEnding : Injective (pastEnding · (Gender.numberSystem.value .singular)) := by
  decide

end Russian.Agreement
