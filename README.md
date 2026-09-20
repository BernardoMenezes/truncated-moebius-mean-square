# A scaling limit for the weighted mean square of the truncated Möbius divisor sum — Lean formalization

Lean 4 / Mathlib formalization companion to the manuscript *"A scaling limit
for the weighted mean square of the truncated Möbius divisor sum"*
(Rodrigo Menezes and Bernardo C Menezes, Independent researchers, 2026).

With `M(q,n) := ∑_{d ∣ q, d ≤ n} μ(d)` the truncated Möbius divisor sum and
`S(n) := ∑_{q > n} M(q,n)² / q²` the `q⁻²`-weighted tail, this repository
mechanically verifies **Theorem 1** of the paper.

## Theorem coverage

**Theorem 1 (proved end-to-end, no `sorry`)**, for every integer `n ≥ 1`:

- `S_decomposition`: the exact positive decomposition
  `S(n) = (1/ζ(2)) · ∑_{d > n} μ(d)² / J₂(d) + ζ(2) · ∑_{d ≤ n} J₂(d) · E_d(n)²`;
- `S_bounds`: `0 ≤ S(n) < (1 + 4ζ(2)) / n`;
- all supporting definitions and elementary lemmas, including the
  Parseval/Gram identity `1 + S(n) = ζ(2) ∑_{d ≤ n} J₂(d) A_d(n)²`, the
  Euler-product evaluations `ζ(2)⁻¹ = ∏_p (1 − p⁻²)` and
  `∑_{d ≥ 1} μ(d)² / J₂(d) = ζ(2)`, the evaluation
  `A_d(∞) = μ(d) / (ζ(2) J₂(d))` on squarefree `d`, the signed identity
  `2 ∑_{d ≤ n} μ(d) E_d(n) = 2 ζ(2)⁻¹ ∑_{d > n} μ² / J₂`, and the tail
  estimates `∑_{d > m} d⁻² ≤ 1/m` and `|E_d(n)| ≤ 2 / (dn)`.

The formal statements carry the hypothesis `1 ≤ n` explicitly: the
decomposition is false at `n = 0` (there `M(q,0) = 0`), matching the paper's
standing convention `n ≥ 1`.

**Theorems 2 and 3 (statements only).** Eleven declarations carry `sorry`,
all kept separate from the proof of Theorem 1:

*External analytic inputs (not in Mathlib):*

- `bdt_uniform_mean_square` — de la Bretèche–Dress–Tenenbaum (2020),
  Thm. 1.1: `S(x,z) = 𝔏·x + O(x / ℒ(3ξ)^c)`, uniform for `ξ ≤ z ≤ x/ξ`.
- `bdt_global` — BDT (2020), eq. (1.5): the global bound `S(x,z) ≪ x`.

*Elementary, but not yet available as named Mathlib results:*

- `block_limit` — the fixed-block limit (paper eq. 17); its input is the
  squarefree-sieve mean of `μ(Am)μ(Bm)` (paper eq. 16), elementary but not
  currently a named Mathlib result.
- `ramare_parseval` — Ramaré's identity `1 + S(n) = ζ(2)·S₁(n)` at `σ = 3/2`
  (finite-sum rearrangement of an absolutely convergent series).
- `Cconst_eq_closed` — the closed double-series form of `C` (rearrangement
  justified by absolute convergence).
- `Cconst_lower_bound` — `C ≥ 1/(2ζ(2))` from `D_j ≥ 0` and `D₁ = 1/ζ(2)`.

*Downstream consequences of the above:*

- `scaling_limit` — Theorem 2 (`n·S(n) → C`), from `block_limit` and
  `bdt_global`.
- `block_tail_law` — Theorem 3, a Stieltjes/partial-summation corollary of
  `bdt_uniform_mean_square`.
- `block_constant_tail` — the limiting block-constant tail (paper eq. 15),
  from `block_tail_law` and `block_limit`.
- `S1_tail` and `S1_tail_tendsto` — Theorem 2 restated through Ramaré's
  identity.

Consistent with the manuscript, the file does not assert the convergence
`D_J → 𝔏`: in the paper that convergence is numerical evidence only.

The Dress–Iwaniec–Tenenbaum constant `𝔏` enters the development only as an
`opaque` constant (an uninterpreted real parameter) in three of the stubbed
declarations: `bdt_uniform_mean_square`, `block_tail_law`, and
`block_constant_tail`. It appears nowhere in the proved Theorem 1 surface.

## Repository layout

- `TruncatedMoebiusMeanSquare.lean` — the entire development (~1900 lines),
  with a file header documenting what is proved and what is stubbed.
- `lakefile.toml` — package definition; pins `mathlib` at `v4.34.0`.
- `lean-toolchain` — pins Lean `4.34.0` (`leanprover/lean4:v4.34.0`).
- `lake-manifest.json` — pins the exact dependency commits.

## Requirements and build

Requires [elan](https://github.com/leanprover/elan) (the Lean version
manager); the pinned toolchain is installed automatically from
`lean-toolchain`.

```bash
lake exe cache get   # downloads precompiled Mathlib artifacts (recommended)
lake build           # verifies TruncatedMoebiusMeanSquare.lean
```

A successful `lake build` finishes with no errors. Warnings of the form
`declaration uses 'sorry'` appear only for the eleven explicitly stubbed
Theorem 2/3 declarations described above; the proof of Theorem 1 uses no
`sorry`.

Without `lake exe cache get`, Mathlib is compiled from source, which can
take several hours; with the cache, verifying this project takes a few
minutes on a typical machine.
