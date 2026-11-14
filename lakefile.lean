import Lake
open Lake DSL

package linglib where
  version := v!"4.35.0"
  description := "A Lean 4 library for formal linguistics: semantics, syntax, pragmatics, morphology, phonology, and processing — formalized across competing frameworks for high interconnection density."
  homepage := "https://linglib.io/"
  keywords := #["linguistics", "formal-semantics", "formal-syntax", "phonology", "pragmatics", "morphology", "lean4", "mathlib"]
  -- Projects that depend on linglib at a release tag download the compiled files
  -- attached to that release (by .github/workflows/release-build.yml) instead of
  -- compiling linglib. If the download fails, Lake builds from source as before.
  preferReleaseBuild := true
  -- One archive for all platforms: linglib has no native code, and its .olean files
  -- do not depend on the operating system. Revisit if linglib adds native code.
  buildArchive := "linglib.tar.gz"
  leanOptions := #[⟨`autoImplicit, false⟩,
    -- TODO: remove once mathlib's strict-defeq transition completes; mathlib v4.35.0 still
    -- turns it off declaration by declaration (`DeriveFintype` enum path and simp
    -- defeq-matching break without it).
    ⟨`backward.isDefEq.respectTransparency, false⟩]

-- Documentation generator; pin must match lean-toolchain version
-- Find the right commit at: https://github.com/leanprover/doc-gen4/commits/main
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae"

-- Mathlib last so its dependency versions take precedence
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib Linglib where
  globs := #[.submodules `Linglib]

/-- The studies: one file per paper, formalizing the paper's data, model and predictions on top
    of `Linglib`. A library of its own, so that `Linglib` is the theory and data the studies are
    checked against, and `import Linglib` does not bring the studies in. -/
@[default_target]
lean_lib Studies where
  globs := #[.submodules `Studies]

/-- Blog essays: novel synthesis and explorations accompanying blog posts.
    These import from Linglib but are not part of the library proper. -/
lean_lib PsychVerbs where
  srcDir := "blog/lean"
  globs := #[.submodules `PsychVerbs]

lean_lib scratch where
  globs := #[.submodules `scratch]

/-- Declarations for `python3 scripts/checks.py selftest`, which checks that the hash of a
    statement closure changes exactly when what the statement says does. -/
lean_lib ChecksFixture where
  srcDir := "scripts/checks"
  roots := #[`ChecksFixture]

/-- A stand-in for Mathlib in the fixture of `checks.py selftest`, outside the project's
    libraries, with a constant renamed by deprecation. -/
lean_lib ChecksFixtureDeps where
  srcDir := "scripts/checks"
  roots := #[`ChecksFixtureDeps]

/-- The statement closures of declarations, read by `scripts/checks.py` to record and verify
    human checks that statements are faithful to their sources (`checks/`). -/
lean_exe checkClosure where
  root := `CheckClosure
  srcDir := "scripts/checks"
  supportInterpreter := true
