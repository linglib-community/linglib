/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Batteries.Tactic.Alias

/-!
# A stand-in for Mathlib in the fixture for the check hash

Its library is not among the project's (`projectRoots` in `CheckClosure.lean`), so to
`checkClosure` its declarations are like Mathlib's: trusted, and renamed by deprecation. `twice` is
renamed to `double`, keeping the old name as a deprecated alias, while `addSelf` is deprecated in
favour of `double` without being an alias of it, so it is no rename.
-/

@[expose] public section

namespace ChecksFixtureDeps

def double (n : Nat) : Nat := 2 * n

@[deprecated double (since := "2026-01-01")] alias twice := double

@[deprecated double (since := "2026-01-01")] def addSelf (n : Nat) : Nat := n + n

end ChecksFixtureDeps
