# A scaling limit for the weighted mean square of the truncated Möbius divisor sum — Lean formalization

Lean 4 / Mathlib formalization companion to the manuscript *"A scaling limit
for the weighted mean square of the truncated Möbius divisor sum"*
(R. Menezes, 2026).

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

**Theorems 2 and 3 (statements only).** The scaling limit `n·S(n) → C` and
the quantitative block-tail law are stated in the same file but not yet
proved: they depend on the uniform mean-square theorem of
de la Bretèche–Dress–Tenenbaum (2020), which is not currently in Mathlib.
That input and the defining properties of the Dress–Iwaniec–Tenenbaum
constant are recorded as explicitly marked hypotheses — twelve `sorry`-ed
declarations, kept separate from the proof of Theorem 1. Completing the
formalization of Theorems 2 and 3 reduces to formalizing this single
analytic input.

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
`declaration uses 'sorry'` appear only for the twelve explicitly stubbed
Theorem 2/3 declarations described above; the proof of Theorem 1 uses no
`sorry`.

Without `lake exe cache get`, Mathlib is compiled from source, which can
take several hours; with the cache, verifying this project takes a few
minutes on a typical machine.
