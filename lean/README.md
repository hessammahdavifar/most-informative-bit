# Courtade–Kumar Conjecture — Lean 4 Formalization

A Lean 4 formalization of the Courtade–Kumar theorem in:

**Hessam Mahdavifar and Ahmad Beirami.**  
**The Most Informative Bit and Beyond: A Proof of the Courtade–Kumar Conjecture and Multibit Extensions.**  
[arXiv:2609.26444](https://arxiv.org/abs/2609.26444), 2026.

This package contains the one-bit proof and its supporting estimates, together
with a pinned build configuration. The entry theorem is
[`MostInformativeBit.general_courtade_kumar`](MostInformativeBit/Main.lean).

## Formalized results

For uniform independent input bits $X$ and their output $Y$ through a binary
symmetric channel with crossover probability $p$, the one-bit theorem states

$$I(f(X);Y) \le 1-h_2(p).$$

The declared theorem covers every dimension, every Boolean function, and
$0 \le p \le 1$, including the endpoints:

```lean
theorem courtade_kumar_bits {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    GeneralCK.mutualInformation f p ≤ 1-GeneralCK.H p
```

Here `Cube n = Fin n → Bool`. Mutual information is defined from the actual
finite joint and marginal distributions, in bits; `GeneralCK.H` is binary entropy
in bits. See the [probability definitions](MostInformativeBit/Vendor/GeneralCK/Statement.lean)
and the [normalization equivalence](MostInformativeBit/SourceStatement.lean).

The manuscript uses the convention $p\le1/2$. The
[output-complement symmetry](MostInformativeBit/NoiseComplement.lean) proves
`mutualInformation f (1-p) = mutualInformation f p` directly from the finite
distributions. It extends the result to the whole interval. The theorem
`MostInformativeBit.general_courtade_kumar : GeneralCK.GeneralCourtadeKumar`
proves the exact full-range proposition used by
[Woodruff and coauthors' formalization](https://github.com/dpwoodru/general-courtade-kumar-lean).
`source_iff_general` also certifies that the manuscript's half-range formulation
and this full-range formulation are equivalent. The theorem `source_theorem`
retains the manuscript's original convention; `courtade_kumar` states the
equivalent bound in natural units. All four formulations are in
[Main.lean](MostInformativeBit/Main.lean).

## Build and verify

Install [Lean through elan](https://github.com/leanprover/elan), and use Python 3.9
or later for the verification script. From the repository root:

```sh
lake exe cache get
python3 scripts/verify.py
```

The first command fetches cached mathlib dependencies. The script builds all
project modules, elaborates [Check.lean](Check.lean), and checks all 21 axiom
reports. It rejects missing reports, `sorryAx`, and any nonstandard axiom.
Expected final output:

```text
PASS: build and 21 axiom audits; only propext, Classical.choice, Quot.sound.
```

The underlying Lean commands can also be run directly:

```sh
lake build
lake env lean Check.lean
```

Versions are pinned by [lean-toolchain](lean-toolchain) and
[lake-manifest.json](lake-manifest.json):

- Lean **4.33.0**, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`.

[GitHub Actions](.github/workflows/lean.yml) is configured to run the same build
and audit on pushes and pull requests. No hosted CI run is claimed by this source
package. The supplied archive reports a successful original build and axiom
audit. All 59 retained mathematical modules are byte-identical to that archive;
the root import and audit driver have been reduced to the CK scope. Source and
import consistency were checked for this edition, but its build and axiom audit
have not been rerun because Lean and Lake were unavailable in the editing
environment.

## Reading the proof

Start with [Main.lean](MostInformativeBit/Main.lean). The proof
combines monotone rearrangement, entropy flow, and low/middle/high correlation
estimates through a maximum principle. The supporting Fourier, scalar, pivotal
and channel estimates are in `MostInformativeBit/`.

[Check.lean](Check.lean) audits the final theorems and supporting results and
checks the bound written explicitly in terms of finite-distribution entropies.

## Trust, provenance and acknowledgments

Lean's kernel checks the proof terms. The supplied archive reports that the final
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; the
verification script enforces this allowed set. Rational certificate inequalities
are established inside Lean; an external numerical computation is not a proof
premise. As with any formalization, correspondence between the declared statement
and the intended mathematics must also be reviewed.

The formalized manuscript snapshot was the author-supplied
`most_informative_bit.zip`, SHA-256:

```text
34ed4ff76cae9b2b27464e100f7a15a1c16cba044a30b6b771bc0922f1e1d2b7
```

[provenance.json](provenance.json) records the manuscript member hashes, pinned
versions and hashes of the production Lean sources. It preserves the original
verification record separately from this edition's source checks. The arXiv link identifies
the paper; it is not a claim that the supplied archive is byte-identical to an
arXiv source release.

The supplied archive's recorded hash for `MiddleChannel.lean` differed from the
file it contained. This edition preserves that file unchanged, records its
actual hash, and retains the discrepancy in the provenance record.

The Lean implementation was developed with AI assistance under human direction,
using Codex/Astra and Claude/Opus sessions. The supplied archive reports kernel
checks and team source reviews; these are not represented as external peer review.
Mathematical attribution is to Mahdavifar and Beirami's paper.

The three files under `MostInformativeBit/Vendor/GeneralCK/` adapt finite
probability definitions and identities from
[dpwoodru/general-courtade-kumar-lean](https://github.com/dpwoodru/general-courtade-kumar-lean).
Their attribution and Apache-2.0 license are retained. This repository's proof
of the Mahdavifar–Beirami argument does not import that project's final theorem
or its generated certificate collection. See [NOTICE](NOTICE) for details.

## Citation

Please cite the paper when using this formalization. [CITATION.cff](CITATION.cff)
sets it as GitHub's preferred citation.

```bibtex
@misc{mahdavifar2026mostinformative,
  title         = {The Most Informative Bit and Beyond: A Proof of the
                   Courtade--Kumar Conjecture and Multibit Extensions},
  author        = {Mahdavifar, Hessam and Beirami, Ahmad},
  year          = {2026},
  eprint        = {2609.26444},
  archivePrefix = {arXiv},
  primaryClass  = {cs.IT},
  doi           = {10.48550/arXiv.2609.26444},
  url           = {https://arxiv.org/abs/2609.26444}
}
```

## License

The repository's code is licensed under the [Apache License 2.0](LICENSE).
Upstream copyright notices are preserved. This license does not change the
rights or authorship of the cited paper.
