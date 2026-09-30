# Native API reference and reproduction

[Generated API](API.md) · [binding manifest](api-manifest.json) ·
[library overview](../README.md)

The checked-in reference uses native doc-gen4 output for **all eight** shipped
Lean modules: five production leaves, their public root, the checked-use client
leaf, and its test root. Native records contain 104 production declaration entries
(including a generated `ext_iff` entry and an undocumented anonymous
`CompleteLattice` instance), 16 publicly named client entries (15 theorems and a
definition), one separate native instance-registry entry, and zero own entries
for the two reexport-only roots. This is not the complete transitive
private/generated standard-axiom audit. A release also requires the applicable
warning-fatal build, independent review and acceptance of the exact candidate;
neither this reference nor a manifest certifies those checks.

Signatures are native **displayed** Lean text. The adapter removes inert HTML
markup and collapses presentation whitespace, without eliding displayed
implicit binders, typeclasses or universe labels. The manifest's
`native_record_sha256` hashes the *raw bytes* of each native `.bmp` JSON record;
`raw_header_sha256` hashes verbatim header HTML; `signature_sha256` hashes the
UTF-8 normalized displayed signature retained in API.md. These hashes are not
interchangeable. Original source docstrings are reproduced where present.
`Supernatural.ext_iff` has a docstring inherited from the authored `ext`, not
an independently authored one. The anonymous lattice instance has **no**
native docstring; its clearly labeled explanatory catalogue text is original
to this documentation and points to its exact Lean source. Native `instances`
and `declarations` are both checked; no native entry is silently suppressed.

## Reproduce without development Git ancestry

The historical analyzed-input labels are `cc3e8d151c87585111df3abe6d2c40d9f10971c6`
and tree `15e99ee28ce447f921b0e74f9ad71e3ce85509b5`. They are **not** a
lookup requirement. Eleven independently pinned source and build-input SHA-256
hashes in `scripts/generate_api.py` and the manifest establish the immutable
analyzed bytes, even in a source-only archive or isolated parentless checkout.
The manifest cannot authenticate itself or name its own future commit; external
review must bind the **final** candidate commit/tree and those bytes.

Install `leanprover/lean4:v4.34.0-rc2` and the exact mathlib graph pinned in
`../lakefile.toml` and `../lake-manifest.json`. Clone `leanprover/doc-gen4` in
an independent checkout at `97d4ecdfc8e09e7f511724c25e303d448de6a3db`
(tree `ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`), using its own
committed manifest, and build its core-only `doc-gen4` executable there with
`lake build doc-gen4`. Do not modify this project's dependency pins. If the
native C compiler is absent from `PATH`, prepend `$(dirname "$(elan which lean)")`
while building the separate tool. Its build does not depend on mathlib.

From the project root, successfully fetch the matching mathlib cache **before**
any library build. `LEAN_NUM_THREADS` controls Lean runtime workers, not the
aggregate build process count or memory. The following historical native
extraction recipe is optional, not a mandatory release replay; the ordinary
warning-fatal default build includes the client root.

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake --wfail build
TOOL=/absolute/path/to/doc-gen4/.lake/build/bin/doc-gen4
OUT=/fresh/temporary/supernatural-native
REV=cc3e8d151c87585111df3abe6d2c40d9f10971c6
mkdir -p "$OUT/build" "$OUT/render"
for module in SupernaturalNumbers.Basic SupernaturalNumbers.NatEmbedding \
              SupernaturalNumbers.Order SupernaturalNumbers.Tower \
              SupernaturalNumbers.Characters SupernaturalNumbers \
              SupernaturalNumbersTests.ReleaseClients SupernaturalNumbersTests; do
  path="$(printf '%s' "$module" | tr . /).lean"
  LEAN_NUM_THREADS=2 lake env "$TOOL" single --build "$OUT/build" \
    "$module" "$OUT/build/api.db" \
    "https://example.invalid/commit/$REV/$path"
done
"$TOOL" bibPrepass --build "$OUT/render" --none
"$TOOL" fromDb --build "$OUT/render" --manifest "$OUT/render/manifest.json" \
  "$OUT/build/api.db" SupernaturalNumbers.Basic \
  SupernaturalNumbers.NatEmbedding SupernaturalNumbers.Order \
  SupernaturalNumbers.Tower SupernaturalNumbers.Characters SupernaturalNumbers \
  SupernaturalNumbersTests.ReleaseClients SupernaturalNumbersTests
python3 -B scripts/test_generate_api.py
python3 -B scripts/generate_api.py --native-data "$OUT/render/doc-data" \
  --source-revision "$REV" \
  --tool-revision 97d4ecdfc8e09e7f511724c25e303d448de6a3db --check
```

The `example.invalid` URI is only a nonresolving **native record identifier**;
it is not a verified upstream source location and does not appear as a link in
the shipped API. Omit `--check` only for an explicit authoring refresh;
`--check` compares existing generated bytes without writing. Both modes check
the exact source/pin bytes and eight raw native records **before** writing.
Optimized Python (`-O`) exits before writing. Tests use data-only corruption
fixtures, not substitute native provenance. Retain the original database, eight
raw record bytes, module/dependency graph, search path and complete command
receipts externally for independent review. Generated HTML, JavaScript, CSS,
fonts, third-party websites and dependency docstrings are not shipped.

This adapter draws on the Formal Frontier Root Stability native Markdown
adapter, Beacon's source-only reproduction correction and Anchor's Ideal
Completion recipe. Those precursors retain their own independent review status;
reuse does not convey approval. Only project docstrings and native displayed signatures are included,
not donor modules, upstream implementation, website assets or external texts.
Mathlib, Lean and doc-gen4 retain their upstream terms and attribution.
