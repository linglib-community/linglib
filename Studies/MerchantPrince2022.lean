module

public import Linglib.Phonology.OptimalityTheory.Grammar

/-!
# Merchant and Prince (2022): The Mother of All Tableaux

This file formalizes the bridge from tableaux to grammars in [merchant-prince-2022], which
studies the large-scale structure of an optimality-theoretic typology: the partition of the
rankings into grammars, the invariant that every violation tableau yielding the typology
instantiates, and its geometry. A row of a tableau asserted optimal generates the
elementary ranking conditions of its winner–loser comparisons (`rowERCs`), and the grammar of
that row is the grammar of those conditions in the hub of [merchant-riggle-2016]
(`rowGrammar`); its rankings are exactly those under which the row wins by lexicographic
optimality after [prince-smolensky-1993] (`mem_rowGrammar_legs_iff_lex`). The typology as
the partition of row grammars, the border-point pair, and the invariant itself are not
represented.

## References

* [merchant-prince-2022]
* [merchant-riggle-2016]
* [prince-smolensky-1993]
-/

@[expose] public section

namespace MerchantPrince2022

open OptimalityTheory

variable {C : Type*} [DecidableEq C] {n : ℕ}

/-- The ERC set of a tableau row `w`: `w`'s winner-loser ERCs against every *other*
candidate. These are the ranking conditions a leg must satisfy for `w` to be the
optimum ([prince-2002]). -/
def rowERCs (t : Tableau C n) (w : C) : Finset (ERC (Fin n)) :=
  (t.candidates.erase w).image (tableauERC t w)

/-- The **grammar of a tableau row** — the bridge from the Concrete-OT tableau
engine to the abstract `Grammar` hub ([merchant-prince-2022]; [merchant-riggle-2016]).
`h` is the consistency of the row's conditions, i.e. that `w` is a genuine,
non-harmonically-bounded optimum. -/
def rowGrammar (t : Tableau C n) (w : C)
    (h : (ERC.linearExtensions (rowERCs t w)).Nonempty) : Grammar n :=
  Grammar.ofERCs (rowERCs t w) h

@[simp] theorem mem_rowGrammar_legs {t : Tableau C n} {w : C}
    {h : (ERC.linearExtensions (rowERCs t w)).Nonempty} {r : Ranking (Fin n) n} :
    r ∈ (rowGrammar t w h).legs ↔ ∀ α ∈ rowERCs t w, ERC.SatisfiedBy r α := by
  simp only [rowGrammar, Grammar.legs_ofERCs, ERC.mem_linearExtensions]

/-- **The semantic anchor.** A row's grammar collects exactly the rankings under
which `w`'s violation profile, read in the ranking's priority order, lexicographically
dominates every competitor's — i.e. the rankings that select `w` as optimum
([prince-smolensky-1993]). This connects the abstract `Grammar` hub back to the
tableau's lexicographic evaluation. -/
theorem mem_rowGrammar_legs_iff_lex {t : Tableau C n} {w : C}
    {h : (ERC.linearExtensions (rowERCs t w)).Nonempty} {r : Ranking (Fin n) n} :
    r ∈ (rowGrammar t w h).legs ↔
      ∀ l ∈ t.candidates.erase w,
        r • t.profile w ≤ r • t.profile l := by
  rw [mem_rowGrammar_legs]
  unfold rowERCs
  constructor
  · intro hsat l hl
    exact (tableauERC_satisfiedBy_iff t r w l).mp
      (hsat _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩))
  · intro hlex α hα
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hα
    exact (tableauERC_satisfiedBy_iff t r w l).mpr (hlex l hl)

end MerchantPrince2022
