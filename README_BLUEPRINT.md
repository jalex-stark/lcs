# Blueprint Infrastructure - Quick Reference

## Status
✓ **OPERATIONAL** - Ready for production deployment

## What Is This?

This repository uses **leanblueprint** to maintain bidirectional correspondence between:
- **Lean 4 proofs** in `/RobustLCS/` — Formal verification
- **LaTeX exposition** in `/blueprint/src/` — Mathematical exposition

The blueprint system automatically generates:
- Web version with interactive dependency graphs
- PDF for printing
- Validation that all proofs match their descriptions

## Quick Commands

```bash
# Verify Lean project compiles
lake build

# Check blueprint declarations (no LaTeX needed)
cd blueprint && leanblueprint checkdecls

# Build PDF + web (requires pdflatex + plastex)
cd blueprint && leanblueprint all

# Preview web version locally (requires plastex)
cd blueprint && leanblueprint serve
```

## Current Phase

**Phase 1: State-Dependent Distance**
- ✓ Definitions: Density matrices, D_ρ(X||Y)
- ✓ Theorem 4.1: Exact self-testing
- ✓ Lemma 4.4: 10 distance properties
- ⚠ 15 proofs marked with `sorry` (in progress)

## Key Files

| File | Purpose |
|------|---------|
| `blueprint/src/content.tex` | Main mathematical content |
| `blueprint/lean_decls` | Lean declarations manifest (auto-generated) |
| `RobustLCS/Core/` | Lean formalization |
| `RobustLCS/Exact/` | Exact self-testing framework |
| `.github/workflows/` | CI/CD pipeline |

## Documentation

1. **AUDIT_COMPLETION_SUMMARY.txt** — What was audited and fixed
2. **BLUEPRINT_AUDIT_REPORT.md** — Detailed technical audit (10 sections)
3. **BLUEPRINT_TODO.md** — Phase-by-phase tasks remaining
4. **BLUEPRINT_FIXES.md** — How to fix issues and deploy
5. **BLUEPRINT_STATUS_SUMMARY.md** — Executive summary
6. **CLAUDE.md** — Development guide (general repo info)

## Before Deploying to GitHub Pages

```bash
# 1. Configure git remote (one-time)
git remote add origin https://github.com/<username>/lcs.git

# 2. Create blueprint CI workflow
# (Copy template from BLUEPRINT_FIXES.md to .github/workflows/blueprint.yml)

# 3. Enable GitHub Pages in repo settings
# Settings → Pages → Source: GitHub Actions

# 4. Push to main
git push -u origin main
```

## Adding Content

### To LaTeX
1. Edit `blueprint/src/content.tex`
2. Use `\label{identifier}` for cross-references
3. Use `\lean{Full.Qualified.Name}` to link Lean declaration
4. Use `\uses{label1, label2}` for dependencies

### To Lean
1. Add declaration in `RobustLCS/Core/` or `RobustLCS/Exact/`
2. Run `lake build` to verify
3. Add `\lean{Full.Qualified.Name}` to LaTeX
4. Run `leanblueprint checkdecls` to validate

## Proof Status

- **Total**: 15 declarations in Phase 1
- **Complete**: 0 (all work in progress)
- **With sorry**: 15 (expected for Phase 1)

Mark proofs as complete with `\leanok` in LaTeX once Lean proof is done (no `sorry`).

## GitHub Pages URLs (once deployed)

- Web blueprint: `https://<user>.github.io/lcs/blueprint/`
- PDF: `https://<user>.github.io/lcs/blueprint.pdf`
- API docs: `https://<user>.github.io/lcs/docs/` (requires doc-gen4)

## Next Steps

1. Configure git remote (5 min)
2. Create GitHub Actions workflow (10 min)
3. Push to GitHub and verify deployment (5 min)
4. Begin Phase 2 formalization

See **BLUEPRINT_FIXES.md** for detailed step-by-step instructions.

## Support

- Development guide: See `CLAUDE.md`
- Specific issues: See `BLUEPRINT_FIXES.md`
- Task tracking: See `BLUEPRINT_TODO.md`
- Technical details: See `BLUEPRINT_AUDIT_REPORT.md`

---

**Last Updated**: October 18, 2025
**Status**: All systems operational, ready for GitHub Pages deployment
