import Lake
open Lake DSL

package LemLib where
  version := v!"0.1.0"

@[default_target]
lean_lib LemLib where
  srcDir := "."
  globs := #[.one `LemLib, .submodules `LemLib]

/-- Fmap representation-change equivalence: retired reference implementation,
    kernel-checked equivalence theorems, and bounded-exhaustive property
    tests (arc-6 S3). Building it IS running it. -/
@[default_target]
lean_lib LemLibTest where
  srcDir := "."
  globs := #[.one `LemLibTest]
