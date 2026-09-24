# Runtime provenance and notices

Recorded 2026-09-24 against Lem source `38f87d5fa6b29ec90edfa457faba8a309e32c118`
and the cleanup's notice restoration (M8). This records source provenance;
it does not grant a new license or claim a legal review.

`LemLib.lean` contains Lean translations of the AVL set/map algorithms in
`ocaml-lib/pset.ml` and `ocaml-lib/pmap.ml`, inside the `Pset` and `Pmap`
namespaces. Their headers identify Xavier Leroy and copyright 1996 INRIA;
the Lem modifications are credited to Scott Owens (sets, 2010-10-28) and
Susmit Sarkar (maps, 2010-11-30). Those headers are retained verbatim in
`LemLib.lean`. The Lean implementations adapt the representation and
termination arguments, so “verbatim ports” was not a precise description.

The root [LICENSE](../LICENSE) assigns the OCaml source files the GNU
Library General Public License, Version 2, and includes its full text.
The translated portions retain those terms. The original headers also
refer to a linking exception; that wording is preserved, without inventing
an additional exception for Lean or asserting that the separate LGPL 2.1
exception attached to `src/ulib` applies to these portions. Maintainers
should resolve that inherited exception-reference ambiguity before making
more specific downstream licensing assurances, and reconcile the inherited
package-level SPDX metadata at that point. The `opam` license list is not
a replacement for these per-file terms. The remaining original
runtime code follows Lem's BSD-3-Clause default.

Distributions of the runtime should carry the root LICENSE and these
source notices. Neither the Lean port nor its proof/test results erase the
upstream attribution or turn the entire runtime into BSD-only code.
