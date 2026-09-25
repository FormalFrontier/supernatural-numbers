# Supernatural numbers

Authors: Formal Frontier Agents

A Lean library for prime-indexed supernatural numbers and their use in profinite
group theory. Exponents take values in `ℕ∞`; multiplication adds prime exponents,
and divisibility agrees with the pointwise exponent order. Infinite products
and suprema accommodate infinite exponents. The complete-lattice bottom is one;
`iSup` and `iInf` range over arbitrary `Sort` indices, while `iProd` has a
`Type`-indexed family.

This repository is a reusable mathematical library, not a statement that any
particular book has been completely formalized. It provides finite-quotient
supernatural orders of profinite groups, supernatural indices of **closed**
subgroups, a tower law for nested closed subgroups, and a torsion-order
comparison with rational-circle/Pontryagin characters of abelian torsion groups.
It does not assert these statements for arbitrary topological groups, arbitrary
subgroups, or nontorsion character groups.

## Modules and first use

`import SupernaturalNumbers` publicly reexports all five subject modules:

| Module | Selected public interfaces |
| --- | --- |
| `SupernaturalNumbers.Basic` | `Supernatural`, `exponent`, `bot_eq_one`, `iProd`, `ofPNat`, `ofPNatHom`, `ofPNat_mul`, `ofPNat_le_ofPNat_iff`, `dvd_iff_le` |
| `SupernaturalNumbers.NatEmbedding` | Explicit `ofNat`, `ofNatHom`, `ofNat_mul`, `ofNat_dvd_ofNat_iff`, supernatural l.c.m. |
| `SupernaturalNumbers.Order` | `profiniteOrder`, `profiniteIndex`, `torsionOrder`, finite-quotient bounds and subgroup identities |
| `SupernaturalNumbers.Tower` | `closedSubgroupWithin`, `profiniteIndex_tower`, finite-stage index tools |
| `SupernaturalNumbers.Characters` | `characterEquivProfiniteCharacter`, `profiniteCharacter`, `torsionOrder_eq_profiniteOrder_character` |

For smaller imports, use a subject module directly, for example
`import SupernaturalNumbers.NatEmbedding` for the arithmetic interfaces, or
`import SupernaturalNumbers.Tower` for profinite indices. Character comparison
requires `import SupernaturalNumbers.Characters`. Under Lean's module system,
use `public import` instead if declarations in **your own** module must export
the imported interfaces to its downstream consumers.

An example using just the public root import. The separate
`SupernaturalNumbersTests/ReleaseClients.lean` contains additional checked clients:

```lean
module
public import SupernaturalNumbers

theorem six_divides_thirty :
    Supernatural.ofNat 6 ∣ Supernatural.ofNat 30 := by
  rw [Supernatural.ofNat_dvd_ofNat_iff]
  decide
```

Positive naturals embed by `ofPNat`; the separate **explicit** all-natural
`ofNat` sends **zero to top**, so `ofNat 6 ∣ ofNat 0` but not conversely.
Neither map installs a global natural-to-supernatural coercion: write `ofNat n`
or `ofPNat n` rather than relying on numeral elaboration as a supernatural
number. The positive embedding and all-natural map preserve multiplication.

`profiniteOrder` ranges over finite continuous quotients of a profinite group;
`profiniteIndex H` takes a `ClosedSubgroup` of that group. The tower theorem
requires an actual proof `N ≤ H` for closed subgroups of the **same** profinite
group, and uses `closedSubgroupWithin H N hNH` inside the profinite group `H`.
`torsionOrder` uses finite additive subgroups and requires `IsAddTorsion A`.
The public `torsionOrder_eq_profiniteOrder_character A hA` only requires an
`AddCommGroup A` and `IsAddTorsion A`: its wrapper gives `A` the discrete
topology internally. The lower-level Pontryagin theorem instead assumes an
explicit `DiscreteTopology A`. See the finite `ZMod 6` and infinite-product
examples in the checked test library for the actual hypotheses and boundaries.

The [generated API](docs/API.md) gives all 104 native production entries and
16 publicly named checked-use client entries with their native displayed Lean
signatures, source links and original docstrings. Its
[reproduction and scope](docs/README.md) distinguish native generated/inherited
entries from authored declarations and the separate complete private/generated
and stored-proof release audit. The [hash manifest](docs/api-manifest.json) binds
eight native records and all eleven unchanged mathematical/build input files;
it cannot authenticate itself or certify a future release.

## Reproduce and check

Install the toolchain recorded in `lean-toolchain` (currently Lean
`v4.34.0-rc2`). `lakefile.toml` pins mathlib at
`e37d88a26f3791ed5a93daa1f949af1021b8d103`; `lake-manifest.json`
records its resolved dependencies. From this repository's root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
lake env lean -DwarningAsError=true SupernaturalNumbersTests/ReleaseClients.lean
lake env lean -DwarningAsError=true -T0 SupernaturalNumbersTests/ReleaseClients.lean
```

**Fetch the matching mathlib cache successfully before any build.** If that
fetch fails, diagnose it rather than rebuilding all of mathlib silently. The
default build includes the separate `SupernaturalNumbersTests` library; its
root imports `SupernaturalNumbersTests.ReleaseClients`. These tests demonstrate
root-import arithmetic, a genuinely infinite exponent, the zero boundary,
a finite closed-subgroup tower and a finite torsion-character comparison.
They also check automatic simplification of one and empty supernatural and
natural families, including the complete-lattice bottom projection, alongside
explicit use of the retained named arithmetic lemmas.
The commands check examples; they do not replace a full shipped-proof census,
separate stored-proof recheck or independent mathematical review.

### Measured build baseline

On September 25, 2026, a Linux x86_64 check of the unchanged eight Lean modules
with the pins above took **39.9 seconds** for eight sequential module builds
starting without project build outputs but **with the matching dependency cache**.
The largest sampled process-group resident memory was **2.41 GiB**. A subsequent
warm default build took **3.95 seconds**, with **0.84 GiB** sampled resident memory.
The commands used `LEAN_NUM_THREADS=1` and Lake `-Kjobs=2`; the runner imposed
a 64 GiB virtual-address limit per process and an 18 GiB process-group resident-
memory watchdog. These imposed limits are not measured memory requirements, and
sampled process-group peaks are not whole-container peak measurements.

This is a one-environment baseline, not a guarantee or a performance-improvement
claim. Cache download, dependency storage, native documentation generation and
the separate proof audit are excluded. Budget additional time and disk space for
those steps; a full mathlib source rebuild was not measured. On comparable
cache-ready hardware, expect project-only builds on the order of tens of seconds;
resource needs and timings can vary with the host and parallelism.

As of September 25, 2026, the mathematical library, `Supernatural.bot_eq_one`,
simplifier changes, checked clients, notices, LICENSE and earlier metadata were
independently reviewed (ordinary acceptance issue 12 / 40303 and integration
40306) at accepted internal `main` commit
`cc3e8d151c87585111df3abe6d2c40d9f10971c6` (tree
`15e99ee28ce447f921b0e74f9ad71e3ce85509b5`). The **new** generated API,
documentation tooling and revised metadata are author work pending whole-final-
candidate independent review, provenance/rights checks and integration. The
separate complete current-tree private/generated declaration and stored-body
audit is not certified by an authored-docstring inventory or these native docs.
An official internal or public release requires a revision-specific independent
acceptance record identifying the exact release commit/tree and applicable
proof, documentation, dependency, rights and public-history evidence. Neither
this README, a build, the manifest nor Lake's `0.1.0` version is a release registry.

Original repository code is licensed under Apache-2.0; see `LICENSE` and
the retained SPDX headers. Mathlib and other dependencies keep their own
notices and licenses. Formalization process and source attribution are recorded
in `formalization.yaml`; detailed source-level coverage is recorded separately.

## Contribution provenance

Beacon authored the original project implementation and module prose. The five
subject modules began in the following revisions (later development history is
retained):

| Module | Original contribution |
| --- | --- |
| Basic | `FormalFrontier/supernatural-numbers@e7d74e017f1d4f3a89c9a96af3880bb55222786b:SupernaturalNumbers/Basic.lean` |
| Order | `FormalFrontier/supernatural-numbers@d00f949a628d2c871f678e63e5d0fc9be1f07b59:SupernaturalNumbers/Order.lean` |
| Tower | `FormalFrontier/supernatural-numbers@d13dbd46dd486c21828bdd746001caae747d0b47:SupernaturalNumbers/Tower.lean` |
| Characters | `FormalFrontier/supernatural-numbers@e4b42857ddbaa0d1413a909f3c09a8a2655a74b8:SupernaturalNumbers/Characters.lean` |
| NatEmbedding | `FormalFrontier/supernatural-numbers@279a51fe37f9564931fc027545ed5202bdb22117:SupernaturalNumbers/NatEmbedding.lean` |

Worker-b contributed the readiness clients and metadata in
`FormalFrontier/supernatural-numbers@aa06e8cb4c359a2ae36c10632dd9b43d32692bd5:SupernaturalNumbersTests/ReleaseClients.lean`
and the documented bottom/simplification repair in
`FormalFrontier/supernatural-numbers@ec48995236f103daa39077c4b97f360b2ddf0133:SupernaturalNumbers/Basic.lean`;
Beacon assembled the notice and status corrections. These are AI-agent
contributions, not claims of a named human author or copyright holder.
Worker-b Hive Task `hive-request-64db144d6c068a16068b0f8d7266fa30d0f8d322`
(UID `d6907a4c-c8b1-4f99-a90d-830e128ab9c2`) authored the new API
documentation and adapter; its [origin and reuse](docs/README.md) are recorded
without suggesting inherited review approval.

The five initial project-generated ownership assertions naming "Formal Frontier
Authors" had no established ownership basis and have been removed under the
project's reviewed correction procedure. Their original revisions remain in
history. Apache-2.0 notices, collective author credit and actual contributor
provenance are retained; no replacement owner is asserted. This correction does
not remove any identified third-party notice or clear unrelated rights concerns.

The mathematical background includes
Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected second
edition v2.3 (May 2020), Definitions (1.1.5)--(1.1.6) and the consequences following
(1.1.6). This library uses mathematical ideas and mathlib interfaces; it does not
redistribute that book, its figures or source excerpts. Dependency source and
native HTML/website assets are not bundled; native signatures and this project's
docstrings are included in the Markdown API. Release review must separately check
the complete artifact's rights/provenance, including this documentation and
proposed published history; original-project standing authorization is not a
blanket third-party rights waiver, and Apache metadata
and a build alone do not establish that clearance.
