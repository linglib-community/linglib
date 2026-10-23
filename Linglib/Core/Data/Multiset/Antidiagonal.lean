/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Multiset.Powerset
public import Mathlib.Data.Multiset.Antidiagonal
public import Linglib.Core.Data.List.Zip

/-!
# Splits in `Multiset.antidiagonal`

`Multiset.antidiagonal w` enumerates the ordered splits `w = p.1 + p.2` with multiplicities.
This file reads it off a list's `sublists'`, slices it by the size of the first part, and counts
a split through `Multiset.powerset`.

## Main results

* `Multiset.antidiagonal_coe_sublists'`: the splits of a list are its `sublists'.revzip`.
* `Multiset.filter_card_fst_eq_antidiagonal`: the splits whose first part has `k` elements
  are indexed by `powersetCard k`.
* `Multiset.count_antidiagonal_eq_count_powerset`: the multiplicity of a split is that of its
  second part in the powerset.
-/

@[expose] public section

namespace Multiset

variable {α : Type*}

theorem antidiagonal_coe_sublists' (l : List α) :
    antidiagonal (l : Multiset α) =
      ((l.sublists'.revzip.map fun p => ((p.1 : Multiset α), (p.2 : Multiset α)) :
        List (Multiset α × Multiset α)) : Multiset (Multiset α × Multiset α)) := by
  rw [antidiagonal_coe', powersetAux', List.revzip_map]
  rfl

variable [DecidableEq α]

theorem filter_card_fst_eq_antidiagonal (s : Multiset α) (k : ℕ) :
    (s.antidiagonal.filter fun p ↦ card p.1 = k) = (s.powersetCard k).map fun t ↦ (t, s - t) := by
  rw [← map_swap_antidiagonal, antidiagonal_eq_map_powerset, map_map, filter_map,
    powersetCard_eq_filter]
  rfl

theorem count_antidiagonal_eq_count_powerset (s t : Multiset α) :
    (antidiagonal (s + t)).count (s, t) = (s + t).powerset.count t := by
  rw [antidiagonal_eq_map_powerset,
      show (s, t) = (s + t - t, t) by rw [Multiset.add_sub_cancel_right]]
  exact count_map_eq_count' _ _ (fun _ _ h => congrArg Prod.snd h) t

end Multiset
