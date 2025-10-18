# Robust LCS Self-Testing

This repository contains research materials for the paper "Robust self-testing for linear constraint system games" (arXiv:1709.09267v2) by Andrea Coladangelo and Jalex Stark, along with a formal verification effort in Lean 4.

## Repository Structure

### LaTeX Paper (`arXiv-1709.09267v2/`)

The main paper proving robust self-testing results for Linear Constraint System (LCS) games over ℤ_d.

**Build the paper:**
```bash
cd arXiv-1709.09267v2
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

### Lean 4 Formalization (`RobustLCS/`)

A formal verification of the corrected state-dependent distance lemmas and exact self-test framework.

**Build the Lean formalization:**
```bash
lake update
lake build
```

**Project organization:**
- `RobustLCS/Core/` - Core definitions (density matrices, state-dependent distance, isometries)
- `RobustLCS/Exact/` - Exact self-test theorem (Theorem 4.1)
- `RobustLCS/Tactics/` - Helper tactics and simp lemmas

## Lean Formalization Status

### Phase 1: State-Dependent Distance (In Progress)
- ✅ Density matrix structure defined
- ✅ State-dependent distance D_ρ(X∥Y) defined
- 🔄 Lemma 4.4 properties (corrected version):
  - (a) D_ρ(X∥I)² formula
  - (b) Left-unitary invariance (⚠️ **not** right-multiplication)
  - (c) Triangle inequality
  - (d) Left-multiplication bound
  - (e) Chain sum bound
  - (f) Unitary push inequality
  - (g) Convexity
  - (h) Partial trace specialization (deferred)
  - (i) Isometry covariance
  - (j) Projection support

### Phase 2: Magic Square/Pentagram (Planned)
- Robust self-test for Magic Square (Theorem 6.9)
- Robust self-test for Magic Pentagram (Theorem 6.17)
- Pauli group specialization

### Phase 3: Product Games (Planned)
- Product game G^n (Theorem 6.32)

### Phase 4: General Theorem (Planned)
- General robust theorem (Theorem 4.16)
- Quantitative van Kampen (Proposition 4.8)

## Key Mathematical Concepts

**Solution Groups**: Presented groups Γ(H,l,ℤ_d) characterizing optimal LCS strategies via commutation and equation relations.

**State-Dependent Distance**: D_ρ(X∥Y) = √(Re Tr(ρ (X-Y)† (X-Y))) - a seminorm measuring operator distance weighted by quantum state ρ.

**Important Correction**: Lemma 4.4(b) only guarantees left-multiplication invariance D_ρ(UX∥UY) = D_ρ(X∥Y). The right-multiplication identity D_ρ(ZU∥I) = D_ρ(Z∥U†) does **not** hold in general.

## References

- arXiv:1709.09267v2 - Robust self-testing for linear constraint system games
- See `dump.txt` for peer review feedback and formalization discussion
- See `CLAUDE.md` for detailed codebase documentation
