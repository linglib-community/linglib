module

public import Linglib.Phonology.OptimalityTheory.LinearExtension

/-!
# Stratal Optimality Theory

Stratal OT evaluates phonology cyclically, at successive levels of morphological structure (stem,
word, phrase), the output of each level being the input to the next. Each level, or stratum, has
its own ranking of the constraints, given as analyses print it: a relation on the constraints,
the Hasse diagram of the stratum, whose total rankings are its linear extensions
(`Ranking.Enumeration.IsLinearExtension`). Two constraints are [reranked](##Reranked)
between two strata when the strata order them in opposite ways, and then
[no total ranking serves both](##Reranked.not_isLinearExtension): the
strata are different grammars.

## References

* [kiparsky-2000]
-/

@[expose] public section

namespace OptimalityTheory.Stratal

variable {ι : Type*} {n : ℕ} {r₁ r₂ : ι → ι → Prop} {a b : ι}

/-- `a` and `b` are reranked between the strata with rankings `r₁` and `r₂` when `a` is ranked
above `b` in `r₁` and below it in `r₂`. -/
@[mk_iff]
structure Reranked (r₁ r₂ : ι → ι → Prop) (a b : ι) : Prop where
  /-- The constraints are distinct. -/
  ne : a ≠ b
  /-- The first stratum ranks `a` above `b`. -/
  fst : r₁ a b
  /-- The second stratum ranks `b` above `a`. -/
  snd : r₂ b a

instance [DecidableEq ι] [DecidableRel r₁] [DecidableRel r₂] : Decidable (Reranked r₁ r₂ a b) :=
  decidable_of_iff' _ (reranked_iff ..)

namespace Reranked

/-- Reranking read from the later stratum to the earlier. -/
protected theorem symm (h : Reranked r₁ r₂ a b) : Reranked r₂ r₁ b a :=
  ⟨h.ne.symm, h.snd, h.fst⟩

theorem mono {s₁ s₂ : ι → ι → Prop} (h : Reranked r₁ r₂ a b) (h₁ : r₁ ≤ s₁) (h₂ : r₂ ≤ s₂) :
    Reranked s₁ s₂ a b :=
  ⟨h.ne, h₁ a b h.fst, h₂ b a h.snd⟩

/-- Strata that rerank two constraints share no total ranking. -/
theorem not_isLinearExtension (h : Reranked r₁ r₂ a b) (σ : Ranking.Enumeration ι n) :
    ¬ (σ.IsLinearExtension r₁ ∧ σ.IsLinearExtension r₂) :=
  fun ⟨h₁, h₂⟩ ↦ h.ne (h₁.eq_of_rel_of_rel h₂ h.fst h.snd)

end Reranked

end OptimalityTheory.Stratal
