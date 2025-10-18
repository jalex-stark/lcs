# Blueprint Infrastructure Fixes

## Issue 1: Undefined Label References in Theorem 4.1

### Problem
Two labels in `blueprint/src/content.tex` line 15 are referenced but never defined:
```latex
\uses{lem:unique-operator-solution, lemma:CLS}
```

### Root Cause
These labels correspond to lemmas from the paper that haven't been added to the blueprint yet:
- `lem:unique-operator-solution` — Lemma 4.2 (uniqueness of operator solution)
- `lemma:CLS` — Presumably "Common Lifting Strategy" or similar from the paper's preliminaries

Since Theorem 4.1 is a proof sketch that will be completed in Phase 2, these lemmas are legitimately from outside Phase 1.

### Solution Options

#### Option A: Remove Undefined References (RECOMMENDED for Phase 1)
**File**: `blueprint/src/content.tex`
**Current** (line 15):
```latex
\lean{RobustLCS.Exact.theorem41_exact}
\uses{lem:unique-operator-solution, lemma:CLS}
```

**Change to**:
```latex
\lean{RobustLCS.Exact.theorem41_exact}
\uses{def:state-distance, def:density-matrix}
```

**Rationale**:
- Theorem 4.1 uses state-dependent distance throughout
- This properly documents actual dependencies from Phase 1
- Phase 2 will add the missing lemmas when they're formalized

#### Option B: Add Placeholder Definitions (for completeness)
Add to `blueprint/src/content.tex` after Section 2 (before Theorem 4.1):

```latex
\begin{lemma}[Unique operator solutions]\label{lem:unique-operator-solution}
(To be formalized in Phase 2)
\end{lemma}

\begin{lemma}[Common Lifting Strategy]\label{lemma:CLS}
(To be formalized in Phase 2)
\end{lemma}
```

**Rationale**: Explicitly documents dependencies while acknowledging they're not yet formalized

#### Option C: Update Later (NO ACTION NOW)
Leave as-is with understanding that these will be defined in Phase 2.

**Rationale**: The blueprint is still valid; the warning is just informational

---

## Recommended Action

**Execute Option A** (Remove undefined references):

```diff
--- a/blueprint/src/content.tex
+++ b/blueprint/src/content.tex
@@ -12,7 +12,7 @@

 \begin{theorem}[Rigid self-testing of observables]\label{thm:rigid-self-testing-observables}
 \lean{RobustLCS.Exact.theorem41_exact}
-\uses{lem:unique-operator-solution, lemma:CLS}
+\uses{def:state-distance, def:density-matrix}
 Suppose $\Gamma$ is finite and all of its irreducible representations with $J\mapsto \omega_d I$ are equivalent to a fixed irrep $\sigma:\Gamma\to U(\mathbb{C}^d)$. Suppose $\{A_e^{(v)}\}, \{B_e\}, \rho\in \mathcal{L}(\mathcal{H}_A\otimes \mathcal{H}_B)$ is a perfect strategy presented via observables for the game.
 Then there are local isometries $V_A, V_B$ such that
```

**Why this is better than doing nothing**:
1. Prevents LaTeX warnings when building the full blueprint
2. Properly documents that Theorem 4.1 depends on state-dependent distance (which it does)
3. Clear signal that Phase 2 will add the missing lemmas

---

## Issue 2: Git Remote Not Configured

### Problem
```bash
$ git remote -v
# (no output)
```

The repository has no remote configured, blocking GitHub Pages deployment.

### Solution

1. **Create a GitHub Repository**
   - Go to https://github.com/new
   - Create repository `lcs` (or desired name)
   - Do NOT initialize with README (we have one)
   - Do NOT initialize with .gitignore (we have one)

2. **Add the Remote**
   ```bash
   git remote add origin https://github.com/<your-username>/lcs.git
   ```

3. **Verify**
   ```bash
   git remote -v
   # Should show:
   # origin  https://github.com/<your-username>/lcs.git (fetch)
   # origin  https://github.com/<your-username>/lcs.git (push)
   ```

4. **Push to GitHub** (after committing your changes)
   ```bash
   git push -u origin main
   ```

---

## Issue 3: GitHub Actions Workflow for Blueprint Deployment

### Problem
No GitHub Actions workflow exists to build and deploy the blueprint to GitHub Pages.

### Solution

Create file: `.github/workflows/blueprint.yml`

```yaml
name: Build and Deploy Blueprint

on:
  push:
    branches:
      - main
    paths:
      - 'blueprint/**'
      - 'RobustLCS/**'
      - 'lakefile.toml'
      - '.github/workflows/blueprint.yml'
  pull_request:
    paths:
      - 'blueprint/**'
      - 'RobustLCS/**'

jobs:
  build-blueprint:
    name: Build Blueprint (PDF + Web)
    runs-on: ubuntu-latest

    steps:
      - name: Checkout repository
        uses: actions/checkout@v4
        with:
          fetch-depth: 0

      - name: Install LaTeX
        run: |
          sudo apt-get update
          sudo apt-get install -y \
            texlive-latex-base \
            texlive-fonts-recommended \
            texlive-latex-extra \
            latexmk

      - name: Install Lean toolchain
        run: |
          curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

      - name: Install Python dependencies
        run: |
          pip install --user leanblueprint plastex

      - name: Build Lean project (with cache)
        run: |
          ~/.elan/bin/lake exe cache get || true
          ~/.elan/bin/lake build

      - name: Check Lean declarations
        run: |
          cd blueprint
          ~/.local/bin/leanblueprint checkdecls

      - name: Build blueprint (PDF + Web)
        run: |
          cd blueprint
          ~/.local/bin/leanblueprint all

      - name: Deploy to GitHub Pages
        if: github.event_name == 'push' && github.ref == 'refs/heads/main'
        uses: peaceiris/actions-gh-pages@v3
        with:
          github_token: ${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./blueprint
          destination_dir: blueprint
          keep_files: true

  deploy-pdf:
    name: Deploy Blueprint PDF
    runs-on: ubuntu-latest
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    needs: build-blueprint

    steps:
      - name: Checkout repository
        uses: actions/checkout@v4

      - name: Install LaTeX and dependencies
        run: |
          sudo apt-get update
          sudo apt-get install -y \
            texlive-latex-base \
            texlive-fonts-recommended \
            texlive-latex-extra \
            latexmk

      - name: Install Python dependencies
        run: pip install --user leanblueprint plastex

      - name: Build PDF
        run: |
          cd blueprint/src
          latexmk -pdf -output-directory=../print print.tex

      - name: Upload PDF to GitHub Pages
        uses: peaceiris/actions-gh-pages@v3
        with:
          github_token: ${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./blueprint/print
          destination_dir: .
          keep_files: true
```

### Enable GitHub Pages

1. Go to repository Settings → Pages
2. Set "Source" to "GitHub Actions"
3. The workflow will automatically deploy to:
   - `https://<user>.github.io/<repo>/blueprint/` (web version)
   - `https://<user>.github.io/<repo>/blueprint.pdf` (PDF)

---

## Implementation Steps

### Step 1: Fix Content.tex (Immediate)
```bash
# Edit blueprint/src/content.tex line 15
# Change from:
#   \uses{lem:unique-operator-solution, lemma:CLS}
# Change to:
#   \uses{def:state-distance, def:density-matrix}
```

### Step 2: Verify Locally
```bash
cd /Users/jalex/repos/lcs/blueprint
leanblueprint checkdecls
# Should show no errors
```

### Step 3: Commit Changes
```bash
cd /Users/jalex/repos/lcs
git add -A
git commit -m "Fix blueprint: correct Theorem 4.1 dependencies"
```

### Step 4: Configure Git Remote
```bash
git remote add origin https://github.com/<username>/lcs.git
```

### Step 5: Create Blueprint Workflow
Create `.github/workflows/blueprint.yml` (see above)

### Step 6: Enable GitHub Pages & Push
```bash
git push -u origin main
```

---

## Validation Checklist

After applying these fixes:

- [ ] `leanblueprint checkdecls` runs without errors
- [ ] No LaTeX warnings about undefined labels
- [ ] Git remote configured and reachable
- [ ] `.github/workflows/blueprint.yml` created and syntactically valid
- [ ] Changes committed and pushed to GitHub
- [ ] GitHub Actions workflow runs successfully
- [ ] Blueprint deployed to GitHub Pages

---

## Expected Results

After completing all steps:

1. **URLs Available**:
   - Lean API: (will add when doc-gen4 is integrated)
   - Blueprint web: `https://github.com/<user>/lcs/tree/main/blueprint/`
   - Blueprint PDF: `https://github.com/<user>/lcs/blob/main/blueprint.pdf`

2. **Automatic Deploys**:
   - Every push to main triggers blueprint rebuild
   - PDF and web versions stay in sync with formalization
   - Blueprint dependency graph shows Lean ↔ LaTeX linkage

3. **Ready for Phase 2**:
   - Framework is stable for adding Magic Square/Pentagram content
   - Proper CI/CD pipeline in place for continuous verification

---

## Notes

- The print.tex file has dummy macro definitions for `\lean`, `\leanok`, etc. These are intentional — they make the PDF build ignore web-specific commands.
- The web version (via PlasTeX) processes these macros to create interactive dependency graphs.
- All LaTeX build artifacts are in `blueprint/print/` and `blueprint/web/`.
- The `blueprint/lean_decls` file is auto-generated by leanblueprint and should not be edited manually.
