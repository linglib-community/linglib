module

public import Linglib.Phonology.OptimalityTheory.Correspondence
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.Examples.Alderete2001

/-!
# Alderete 2001: dominance effects as transderivational anti-faithfulness

For every faithfulness constraint F there is an anti-faithfulness constraint ¬F, satisfied
exactly when F is violated at least once. Ranked above F on a base–derivative correspondence
that only some affixes subcategorize for, ¬F forces one alternation in the shared stem and no
more: ¬IDENT[voice] gives the Luo plural's voicing exchange, ¬MAX(Accent) the accent deletion
of Japanese dominant affixes — accented or not — and ¬NOFLOP(Tone) the dragging-to-falling
mutation of Limburg Dutch. Because ¬F reads the base–derivative relation, only an accent of
the base can satisfy it (strict base mutation), and what replaces the deleted structure is
decided by the rest of the grammar (grammar-dependence).

This file defines the transderivational diagram `tct`, the accent constraints on it, and the
paper's tableaux: `luo_exchange` (11), `dominant_accented` (21), `recessive` (22),
`dominant_unaccented` (23), `dragging_mutates` (52), `falling_stays` (53).
`strict_base_mutation` is (27) as a theorem about `Constraint.antifaithful`; the row theorems
`dominant_rows` and `recessive_rows` read (1), (17), (18) off the data.

## References

* [alderete-2001]
* [alderete-1999]
* [benua-1997]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace Alderete2001

open OptimalityTheory

/-! ### Transderivational correspondence -/

/-- The roles of a transderivational diagram are the input, its base, and the derivative. -/
inductive Role where
  | input
  | base
  | output
  deriving DecidableEq, Repr

variable {α : Type*}

/-- In the diagram of (8) the input and the base each correspond diagonally to the
derivative. -/
def tct (input base output : List α) : Correspondence Role α :=
  .diagram (fun | .input => input | .base => base | .output => output)
    fun r₁ r₂ => r₁ ≠ .output ∧ r₂ = .output

/-- Satisfying `¬F` for `F` the loss of `P` along some correspondence means some correspondent
of that relation loses `P`: anti-faithfulness on a base–derivative relation can only be met by
mutating the base ((27)). -/
theorem strict_base_mutation (P : α → Prop) [DecidablePred P] (c : Correspondence Role α)
    (r₁ r₂ : Role)
    (h : Constraint.antifaithful (c.maxViolFeature P r₁ r₂ |> fun n _ => n) () = 0) :
    ∃ p ∈ c.edge r₁ r₂, P (c.form r₁)[p.1] ∧ ¬ P (c.form r₂)[p.2] :=
  (Correspondence.maxViolFeature_pos_iff P c r₁ r₂).1
    ((Constraint.antifaithful_eq_zero_iff _ _).1 h)

/-! ### Luo: voicing exchange ((6), (11)) -/

/-- A Luo segment with its voicing where contrastive. -/
structure Seg where
  sym : Char
  voice : Option Bool
  deriving DecidableEq, Repr

def b : Seg := ⟨'b', some true⟩
def p : Seg := ⟨'p', some false⟩
def t : Seg := ⟨'t', some false⟩
def d : Seg := ⟨'d', some true⟩
def a : Seg := ⟨'a', none⟩
def e : Seg := ⟨'e', none⟩

/-- OO-IDENT[voice] between a base and a candidate derivative (10a). -/
def ooIdentVoice (base : List Seg) : Constraint (List Seg) := fun out =>
  (Correspondence.parallel base out).identViolFeature Seg.voice .lhs .rhs

/-- In (11a), under `¬OO-IDENT[voice] ≫ OO-IDENT[voice]` the plural of *bat* is *bed-e*. The
faithful *bet-e* violates the anti-faithfulness constraint, and the total reversal *ped-e*
satisfies it only with a gratuitous second violation of faithfulness. -/
theorem luo_exchange :
    (Tableau.ofList {[b, e, t, e], [b, e, d, e], [p, e, d, e]}
      [(ooIdentVoice [b, a, t]).antifaithful, ooIdentVoice [b, a, t]]).optimal =
      {[b, e, d, e]} := by
  decide

/-! ### Japanese: dominance effects ((17), (18), (21)–(23)) -/

/-- A syllable with its accent. -/
structure Syl where
  form : String
  accent : Bool
  deriving DecidableEq, Repr

/-- `s` accented, `s'` unaccented. -/
def acc (s : String) : Syl := ⟨s, true⟩
def un (s : String) : Syl := ⟨s, false⟩

/-- MAX(Accent) (14a) from role `r₁` to the derivative. -/
def maxAccent (input base : List Syl) (r₁ : Role) : Constraint (List Syl) := fun out =>
  (tct input base out).maxViolFeature (·.accent = true) r₁ .output

/-- DEP(Accent) (14b) from the input to the derivative. -/
def depAccent (input base : List Syl) : Constraint (List Syl) := fun out =>
  (tct input base out).depViolFeature (·.accent = true) .input .output

/-- CULMINATIVITY (15a) requires the word to bear an accent. -/
def culmin : Constraint (List Syl) := Constraint.binary fun out => out.all (!·.accent)

/-- The inputs and bases of (21)–(23) are *adá+ppó+i*, *yóm+tára* and *kóobe+kko*. -/
def adaInput : List Syl := [un "a", acc "da", acc "ppo", un "i"]
def adaBase : List Syl := [un "a", acc "da"]
def yomInput : List Syl := [acc "yom", acc "ta", un "ra"]
def yomBase : List Syl := [acc "yon", un "da"]
def koobeInput : List Syl := [acc "koo", un "be", un "kko"]
def koobeBase : List Syl := [acc "koo", un "be"]

/-- In (21) the dominant accented suffix *-ppó* under `¬OO-MAX ≫ OO-MAX ≫ IO-MAX` deletes the
base accent and keeps its own, giving *ada-ppó-i*. -/
theorem dominant_accented :
    (Tableau.ofList
      {[un "a", acc "da", un "ppo", un "i"], [un "a", un "da", un "ppo", un "i"],
        [un "a", un "da", acc "ppo", un "i"]}
      [(maxAccent adaInput adaBase .base).antifaithful, maxAccent adaInput adaBase .base,
        maxAccent adaInput adaBase .input]).optimal = {[un "a", un "da", acc "ppo", un "i"]} := by
  decide

/-- In (22) the recessive suffix *-tára*, with `OO-MAX ≫ ¬OO-MAX`, leaves the base accent,
giving *yón-dara*. -/
theorem recessive :
    (Tableau.ofList {[un "yon", acc "da", un "ra"], [acc "yon", un "da", un "ra"]}
      [maxAccent yomInput yomBase .base, (maxAccent yomInput yomBase .base).antifaithful]).optimal =
      {[acc "yon", un "da", un "ra"]} := by
  decide

/-- In (23) the dominant unaccented suffix *-kko* deletes the base accent, and with
`IO-DEP(Accent) ≫ CULMIN` nothing replaces it, giving *koobe-kko*, unaccented like any
accentless word. -/
theorem dominant_unaccented :
    (Tableau.ofList
      {[acc "koo", un "be", un "kko"], [un "koo", acc "be", un "kko"],
        [un "koo", un "be", un "kko"]}
      [(maxAccent koobeInput koobeBase .base).antifaithful, depAccent koobeInput koobeBase,
        culmin]).optimal = {[un "koo", un "be", un "kko"]} := by
  decide

/-! ### Limburg Dutch: dragging tone mutation ((42), (52)–(53))

A tonic syllable is its two moras' H links: the dragging tone is doubly linked, the falling
tone linked on the first mora only, and a rising tone — linked on the second only — is
unattested. -/

/-- ALIGN-L(H, σ) (44): a linked H must be linked to the first mora. -/
def alignL : Constraint (List Bool) := Constraint.binary fun t => t.head? = some false ∧ t.any id

/-- NOFLOP(Tone) between a base and a candidate counts the links of the base lost in the
derivative. -/
def noFlop (base : List Bool) : Constraint (List Bool) := fun out =>
  (Correspondence.parallel base out).maxViolFeature (· = true) .lhs .rhs

/-- NOSPREAD(Tone) counts the links inserted in the derivative. -/
def noSpread (base : List Bool) : Constraint (List Bool) := fun out =>
  (Correspondence.parallel base out).depViolFeature (· = true) .lhs .rhs

/-- In (52), under `ALIGN-L ≫ ¬OO-NOFLOP ≫ OO-NOFLOP` the dragging tone of *káál* loses its
second link, giving *káal-ə*, rather than its first, which would leave a rising tone. -/
theorem dragging_mutates :
    (Tableau.ofList {[true, false], [true, true], [false, true]}
      [alignL, (noFlop [true, true]).antifaithful, noFlop [true, true]]).optimal =
      {[true, false]} := by
  decide

/-- In (53) a falling-tone base cannot mutate, since losing its only link leaves the rising
tone ALIGN-L bans and spreading it violates NOSPREAD, so *stúur-ə* stays faithful. -/
theorem falling_stays :
    (Tableau.ofList {[true, false], [true, true], [false, true]}
      [alignL, (noFlop [true, false]).antifaithful, noSpread [true, false]]).optimal =
      {[true, false]} := by
  decide

/-! ### The data -/

open Examples

/-- A form's characters with the accent mark removed. -/
def stripAccent (s : String) : List Char :=
  s.toList.filterMap fun c =>
    match c with
    | 'á' => some 'a' | 'é' => some 'e' | 'í' => some 'i' | 'ó' => some 'o' | 'ú' => some 'u'
    | '́' => none
    | c => some c

/-- As in (17) and (18), with a dominant affix the derivative begins with the base
de-accented. -/
theorem dominant_rows :
    ∀ row ∈ Examples.all, row.feature? "affixClass" = some "dominant" →
      stripAccent ((row.feature? "base").getD "") <+: row.primaryText.toList := by
  decide

/-- As in (1), with a recessive affix the derivative begins with the base as it is. -/
theorem recessive_rows :
    ∀ row ∈ Examples.all, row.feature? "affixClass" = some "recessive" →
      ((row.feature? "base").getD "").toList <+: row.primaryText.toList := by
  decide

end Alderete2001
