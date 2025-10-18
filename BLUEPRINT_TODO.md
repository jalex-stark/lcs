# Blueprint Integration TODO

## Phase 1: State-Dependent Distance (IN PROGRESS)

### Lean Proofs - Remaining
- [ ] Lemma 4.4(a): `Drho_sq_formula` — D_ρ(U ∥ I)² expansion (StateDistance.lean:56)
- [ ] Lemma 4.4(b): `Drho_left_unitary` — Left-unitary invariance (StateDistance.lean:77)
- [ ] Lemma 4.4(c): `Drho_triangle` — Triangle inequality (StateDistance.lean:98)
- [ ] Lemma 4.4(d): `Drho_left_mul_bound` — Left-multiplication bound (StateDistance.lean:113)
- [ ] Lemma 4.4(e): `Drho_chain_sum` — Chain sum bound (StateDistance.lean:129)
- [ ] Lemma 4.4(f): `Drho_unitary_push` — Unitary push inequality (StateDistance.lean:147)
- [ ] Lemma 4.4(g): `Drho_convexity` — Convexity (StateDistance.lean:167)
- [ ] Lemma 4.4(h): `Drho_tensor_I_eq_marginal` — Partial trace (StateDistance.lean:186)
- [ ] Lemma 4.4(i): `Drho_isometry_covariant` — Isometry covariance (StateDistance.lean:195)
- [ ] Lemma 4.4(j): `Drho_proj_support` — Projection support (StateDistance.lean:233)
- [ ] MatrixFacts.lean — 2 supporting lemmas
- [ ] ExactSelfTest.lean — 3 supporting lemmas

### LaTeX Issues - Blocking
- [ ] **CRITICAL**: Undefined label references in Theorem 4.1:
  - `lem:unique-operator-solution` — Does not exist in content.tex
  - `lemma:CLS` — Does not exist in content.tex
  - **Action**: Either remove from `\uses{}` or add placeholder definitions when Phase 2 starts

### Blueprint Configuration
- [ ] Fix print.tex macros — Currently stubs for web-only commands
- [x] Verify Lean declaration linking — DONE via checkdecls
- [x] Check content.tex structure — DONE

---

## Phase 2: Magic Square / Pentagram (PLANNED)

### Lean Formalization - New
- [ ] `Magic.Square.robust_self_test` — Theorem 6.9
- [ ] `Magic.Pentagram.robust_self_test` — Theorem 6.17
- [ ] `Pauli.group_P2_n` — Pauli group P₂^⊗n definition
- [ ] Irreducible representation selection for Pauli groups
- [ ] Stability lemma infrastructure

### LaTeX Content - New
- [ ] Migrate Magic Square section from arXiv-1709.09267v2/specific-games.tex
- [ ] Migrate Magic Pentagram section
- [ ] Add corresponding theorem references via `\lean{...}`
- [ ] Link dependencies via `\uses{...}`

---

## Infrastructure & Deployment

### Git & GitHub Setup
- [ ] **REQUIRED**: Configure git remote: `git remote add origin https://github.com/<user>/lcs.git`
- [ ] Create `.github/workflows/blueprint.yml` for automated deployment
  - Compile LaTeX to PDF
  - Generate web blueprint
  - Deploy to GitHub Pages
- [ ] Update .github/workflows/structure-only.yml (optional improvements)

### Documentation & CI
- [ ] Update README.md with:
  - [ ] CI status badges (build, blueprint, docs)
  - [ ] Link to deployed blueprint URL
  - [ ] Blueprint project structure overview
- [ ] Set up API documentation generation
  - [ ] Add doc-gen4 to lakefile (may already be present)
  - [ ] Configure GitHub Pages to deploy docs at `/docs/`

### Blueprint Build Tools
- [ ] For local development: Install MacTeX or equivalent LaTeX distribution
- [ ] Test `leanblueprint serve` locally for web preview
- [ ] Test `leanblueprint all` for full PDF + web build

---

## Phase 3: Product Games (PLANNED)

### Lean Formalization
- [ ] `ProductGame.robust_self_test` — Theorem 6.32 with O(n¹⁰ε) bounds
- [ ] Game product structure
- [ ] Inductive error bound analysis

### LaTeX Content
- [ ] Migrate product game section
- [ ] Add theorem and lemma references

---

## Phase 4: General Theorem & Quantitative van Kampen (PLANNED)

### Lean Formalization
- [ ] `Robust.theorem_main` — Theorem 4.16: Main robust self-testing result
- [ ] `Quantitative.van_kampen` — Proposition 4.8 with diagrammatic rewriting
- [ ] Solution group presentation machinery

### LaTeX Content
- [ ] Migrate proof of main theorem
- [ ] Add quantitative van Kampen diagrams (if formalized)

---

## Proof Completion Status

### Summary
- Total proofs needed: ~14+ in Phase 1
- Currently complete: 0
- With sorry placeholders: 14

### By File
| File | Total | Complete | Incomplete |
|------|-------|----------|-----------|
| StateDistance.lean | 10 | 0 | 10 |
| MatrixFacts.lean | 2 | 0 | 2 |
| ExactSelfTest.lean | 3 | 0 | 3 |
| **TOTAL** | **15** | **0** | **15** |

### Key Lemmas (Phase 1)
All lemmas in RobustLCS.Density.Lemma44_* should be moved from `sorry` to complete proofs:
1. Squared distance formula — routine trace calculation
2. Left-unitary invariance — cyclicity of trace
3. Triangle inequality — Cauchy-Schwarz / triangle inequality for norms
4. Left-multiplication bound — unitary invariance
5. Chain sum bound — product lemma + triangle inequality
6. Unitary push inequality — conjugation argument
7. Convexity — Jensen-type argument for expectations
8. Partial trace — restriction to subsystems
9. Isometry covariance — change of basis
10. Projection support — support projection properties

All are "routine finite-dimensional matrix calculations" (per CLAUDE.md) — suitable for automated tactics once infrastructure is in place.

---

## Mapping Maintenance

### Current Mapping
- **File**: `blueprint/lean_decls`
- **Status**: Auto-generated by leanblueprint
- **Last checked**: 2025-10-18

### Labels to Lean Names Mapping
Should maintain a CSV mapping (optional but helpful):
```csv
paper_label,lean_name,status
def:state-distance,RobustLCS.Density.Drho,incomplete
def:density-matrix,RobustLCS.Density.Density,incomplete
lemma:4.4(a),RobustLCS.Density.Drho_sq_formula,incomplete
lemma:4.4(b),RobustLCS.Density.Drho_left_unitary,incomplete
...
thm:4.1,RobustLCS.Exact.theorem41_exact,incomplete
```

---

## Known Issues & Workarounds

### Issue: Undefined labels in Theorem 4.1
- **Status**: ⚠️ Needs investigation
- **Details**: `lem:unique-operator-solution` and `lemma:CLS` are referenced but not defined
- **Workaround**: These will be defined when Phase 2 content is added
- **Action Item**: Update theorem's `\uses{}` when dependencies are ready

### Issue: LaTeX tools not available
- **Status**: ⚠️ Environment-specific (not a repo issue)
- **Workaround**: Works fine in GitHub Actions CI; for local dev, install MacTeX
- **Note**: `leanblueprint checkdecls` works without LaTeX

### Issue: Git remote not configured
- **Status**: ⚠️ Blocker for deployment
- **Fix**: `git remote add origin <github-url>`
- **Impact**: Cannot use GitHub Pages until configured

---

## Success Criteria

### Phase 1 Complete When
- [ ] All 14 Phase 1 proofs completed (no `sorry`)
- [ ] All 14 proofs marked with `\leanok` in blueprint
- [ ] Git remote configured
- [ ] GitHub Actions blueprint workflow deployed
- [ ] Proof integrity check passes (no proofs claiming complete with remaining `sorry`)

### Production Ready When
- [ ] All 4 phases complete
- [ ] All proofs complete (0 sorry/admit)
- [ ] Blueprint deployed to GitHub Pages
- [ ] API documentation deployed
- [ ] README updated with URLs and status badges
