# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This repository contains research materials for the paper "Robust self-testing for linear constraint system games" (arXiv:1709.09267v2) by Andrea Coladangelo and Jalex Stark. The work extends representation-theoretic frameworks for analyzing LCS games over ℤ_d and provides robust self-testing results for the Magic Square and Magic Pentagram games.

## Repository Structure

- **arXiv-1709.09267v2/**: Main paper directory containing LaTeX source files
  - `main.tex`: Main document that includes all sections
  - `introduction.tex`, `preliminaries.tex`, `linear-constraint-games.tex`, `self-testing.tex`, `specific-games.tex`, `conclusion.tex`, `appendix.tex`: Individual sections
  - `impossibility.tex`: Discusses why Magic Square/Pentagram fail for d≠2
  - `JalexMath.sty`: Custom LaTeX style package
  - `MagicSquare-figure*.pdf`: Generated figures (42 files)
  - `quant-van-kampen.pdf`: Diagram for quantitative van Kampen machinery
  - `main.bbl`: Bibliography file
  - **Arxiv v2 - Robust LCS self testing/**: Duplicate copy of source files

- **RobustLCS/**: Lean 4 formalization (in progress)
  - `Core/`: Core mathematical definitions
    - `Density.lean`: Density matrix structure and state-dependent distance
    - `MatrixFacts.lean`: Matrix helper lemmas (cyclicity, PSD properties)
    - `Isometry.lean`: Isometry definitions and properties
    - `StateDistance.lean`: Corrected Lemma 4.4 properties
  - `Exact/`: Exact self-test framework
    - `ExactSelfTest.lean`: Theorem 4.1 and supporting lemmas
  - `Tactics/`: Helper tactics and simplification lemmas

- **dump.txt**: Conversation transcript discussing peer review feedback and Lean 4 formalization blueprint

## LaTeX Build Process

The paper uses a modular structure. To build:

```bash
cd "arXiv-1709.09267v2"
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

The custom `JalexMath.sty` package must be in the same directory as `main.tex`.

## Key Mathematical Concepts

**Solution Groups**: The paper uses solution groups Γ(H,l,ℤ_d) to characterize algebraic relations in optimal LCS game strategies. The solution group is presented via:
- Commutation relations R_c (observables from different players commute)
- Equation relations R_eq (constraints from the game)

**State-Dependent Distance**: A central technical tool D_ρ(X∥Y) measuring operator distance weighted by a quantum state ρ. The paper's main technical lemma (4.4) establishes properties of this distance, with careful attention to left vs. right multiplication by unitaries.

**Pauli Groups**: The n-qubit Pauli group P_d^⊗n is equipped with a canonical form and presentation that enables the robust self-testing machinery.

## Known Issues & Corrections

The conversation in `dump.txt` documents a peer review process that identified an error in Lemma 4.4(b). The corrected version should:
- Only state left-multiplication invariance: D_ρ(UX∥UY) = D_ρ(X∥Y)
- **Not** claim right-multiplication invariance: D_ρ(ZU∥I) ≠ D_ρ(Z∥U†) in general
- Use triangle inequality + left-multiplication for places that relied on the incorrect form

## Lean 4 Formalization

The repository includes a formal verification effort using Lean 4 and mathlib4. The formalization is staged in four phases:

### Build Instructions

```bash
lake update
lake build
```

The project uses Lean v4.23.0 with mathlib v4.23.0 (matching the sister repository [pcp-rpg](../pcp-rpg)).

### Phase 1: State-Dependent Distance (In Progress)

**Status**: Core definitions complete, lemma proofs in progress

- ✅ [Density.lean](RobustLCS/Core/Density.lean): Density matrix structure with Hermiticity, PSD, and trace-1 constraints
- ✅ [StateDistance.lean](RobustLCS/Core/StateDistance.lean): State-dependent distance D_ρ(X∥Y) with corrected Lemma 4.4 properties
- 🔄 Lemma 4.4 properties (many have `sorry` placeholders):
  - (a) D_ρ(X∥I)² expansion formula
  - (b) Left-unitary invariance: D_ρ(UX∥UY) = D_ρ(X∥Y) ⚠️ **Only left multiplication**
  - (c) Triangle inequality
  - (d) Left-multiplication bound for unitaries
  - (e) Chain sum bound for products
  - (f) Unitary push inequality
  - (g) Convexity
  - (h) Partial trace specialization (deferred to later phase)
  - (i) Isometry covariance
  - (j) Projection support properties

**Architecture**: Uses finite-dimensional `Matrix n n ℂ` to avoid C*-algebra machinery. All proofs are routine finite-dimensional matrix calculations that need to be filled in.

### Phase 2: Magic Square/Pentagram (Planned)
- Robust self-test for Magic Square (Theorem 6.9)
- Robust self-test for Magic Pentagram (Theorem 6.17)
- Pauli group P₂^⊗n presentation and canonical forms

### Phase 3: Product Games (Planned)
- Product game G^n (Theorem 6.32) with O(n¹⁰ ε) bounds

### Phase 4: General Theorem (Planned)
- General robust theorem (Theorem 4.16)
- Quantitative van Kampen (Proposition 4.8) with diagrammatic rewriting

### Key Design Decisions

1. **Finite-dimensional only**: All operators are `Matrix n n ℂ`, avoiding infinite-dimensional functional analysis
2. **PSD via vectors**: Positive semidefiniteness encoded as `∀ v, 0 ≤ Re(v† ρ v)` rather than spectral decomposition
3. **Group theory**: Will use `presented_group` from mathlib for solution groups, with character theory for irrep selection
4. **Corrected Lemma 4.4(b)**: Explicitly documents that right-multiplication invariance does **not** hold

## Custom LaTeX Commands

Key macros defined in the paper:
- `\drho{ρ}{X}{Y}`: State-dependent distance D_ρ(X∥Y)
- `\epr`, `\eprp`: EPR state notation
- `\pauli`, `\paulin{n}`: Pauli group P_d^⊗n
- `\can`: Canonical form operator
- `\complexity{LCS}`: LCS complexity class

## Important Theorems

- **Theorem 4.1** (Exact self-test): If solution group Γ has unique irrep with J↦ω_d I, then winning strategies are unique up to isometry
- **Theorem 4.16** (Robust self-test): Main result giving O(d² Δ^10 ε) robustness bounds
- **Theorem 6.9** (Magic Square robust): O(ε) self-test for Magic Square game
- **Theorem 6.17** (Pentagram robust): O(ε) self-test for Magic Pentagram game
- **Theorem 6.32** (Product game): O(n^10 ε) self-test for n-fold products
