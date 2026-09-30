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

## Headline results

- **Arithmetic with arbitrary prime exponents.** A supernatural number has an
  `ℕ∞` exponent at every prime, without a finite-support restriction.
  Multiplication adds exponents and divisibility is pointwise order; the
  complete-lattice bottom is one. Infinite `iProd` uses suprema of exponent
  sums over finite subfamilies of a `Type`-indexed family, whereas `iSup` and
  `iInf` accept arbitrary `Sort` indices. The positive-natural `ofPNat` and
  explicit all-natural `ofNat` preserve multiplication and reflect
  divisibility; `ofNat 0 = ⊤` and neither map installs a numeral coercion.
  [`iSup_ofNat_dvd_iff`](SupernaturalNumbers/NatEmbedding.lean#L129)
  characterizes the supernatural least common multiple of a `Sort`-indexed
  natural-number family, including empty-family and zero cases. See
  [Basic](SupernaturalNumbers/Basic.lean) and
  [NatEmbedding](SupernaturalNumbers/NatEmbedding.lean).
- **The closed-subgroup index tower law.** The supernatural
  [`profiniteOrder`](SupernaturalNumbers/Order.lean#L34) and
  [`profiniteIndex`](SupernaturalNumbers/Order.lean#L43) use finite quotients
  of a profinite group. For closed subgroups `N ≤ H` of the **same** ambient
  profinite group,
  [`profiniteIndex_tower`](SupernaturalNumbers/Tower.lean#L306) proves
  `[G : N] = [G : H] * [H : N]`, taking the relative index in `H` via
  `closedSubgroupWithin H N hNH`. Normality is not required, but closedness
  and the common profinite ambient group are.
- **Torsion and character orders.** For an additive abelian group `A` with
  `IsAddTorsion A`,
  [`characterEquivProfiniteCharacter`](SupernaturalNumbers/Characters.lean#L402)
  identifies its rational-circle-valued characters with the additive group
  underlying its profinite character group; the
  [`torsionOrder_eq_profiniteOrder_character`](SupernaturalNumbers/Characters.lean#L451)
  theorem equates their supernatural orders. The topology-free wrapper gives
  `A` the discrete topology; the lower-level Pontryagin interface requires
  explicit topological assumptions. These noncomputable constructions make
  no nontorsion or general Pontryagin-duality claim.

Mathlib supplies prime-factorization, finite/profinite-group and Pontryagin
infrastructure; this library supplies the supernatural arithmetic and bridges.
See the [API reference](docs/API.md) and
[checked finite and infinite examples](SupernaturalNumbersTests/ReleaseClients.lean).

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
entries from authored declarations and the separate complete transitive
private/generated standard-axiom audit. The [hash manifest](docs/api-manifest.json) binds
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
For acceptance, the warning-fatal default build is accompanied by a complete
transitive standard-axiom audit, including private and generated declarations,
and independent review. The allowed axioms are `propext`, `Classical.choice`
and `Quot.sound`; the API inventory and build do not replace that audit.
An additional stored-proof replay or repeated client builds are not mandatory
gates. Applicable unchanged-input CI build/audit evidence can be reused.

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

The library includes the generated native API, checked clients, explanatory
documentation and formalization metadata alongside its mathematical modules.
The initial private publication and its review have separate exact-revision
records; this README and Lake's `0.1.0` version neither identify an accepted
successor nor certify a particular published GitHub snapshot. Each successor
needs its own revision-specific independent review, applicable build/axiom
evidence, rights/provenance assessment and verified release/publication record.
No complete-source formalization or public-visibility decision is claimed.

Original repository code is licensed under Apache-2.0; see `LICENSE` and
the retained SPDX headers. Mathlib and other dependencies keep their own
notices and licenses. Formalization process and source attribution are recorded
in `formalization.yaml`; detailed source-level coverage is recorded separately.

## Contribution provenance

Beacon contributed the initial mathematical implementation and module prose,
then assembled the notices and corrections. Other AI-agent contributions added
the checked clients, metadata, complete-lattice bottom/simplification repair and
native API documentation and adapter. Folio contributed the distinct headline
exposition used in this reader-facing summary. The adapter's
[recipe lineage](docs/README.md) credits its Root Stability and Anchor Ideal
precursors without transferring their review status. These are contributions
by AI agents under the collective “Formal Frontier Agents” author credit, not
claims of a separately identified human author or copyright holder.

The five initial project-generated ownership assertions naming "Formal Frontier
Authors" had no established ownership basis and have been removed under the
project's reviewed correction procedure. Apache-2.0 notices, collective author credit and actual contributor
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
