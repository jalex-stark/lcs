#!/usr/bin/env bash
set -euo pipefail

# init-git.sh: One-time git setup for RobustLCS project
#
# This script:
# - Initializes git repository if needed
# - Installs pre-commit hook for structure-only policy
# - Creates .gitignore for Lean artifacts
# - Makes initial commit

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Git Repository Setup for RobustLCS"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 1. Initialize git if needed
if [ ! -d ".git" ]; then
  echo "→ Initializing git repository..."
  git init
  git branch -M main
  echo "  ✓ Git initialized (branch: main)"
else
  echo "→ Git repository already exists"
fi

# 2. Create .gitignore for Lean artifacts
echo ""
echo "→ Creating .gitignore for Lean build artifacts..."
cat > .gitignore << 'EOF'
# Lean build artifacts
/.lake/
/build/
/leanpkg.path
*.olean
.cache/

# Blueprint artifacts (keep only source)
/blueprint/web/
/blueprint/print/
/blueprint/*.pdf
/blueprint/*.aux
/blueprint/*.log
/blueprint/*.out
/blueprint/*.toc

# IDE
.vscode/
.idea/
*.swp
*.swo
*~

# macOS
.DS_Store

# Python (for leanblueprint)
__pycache__/
*.pyc
.venv/
venv/
EOF
echo "  ✓ .gitignore created"

# 3. Install pre-commit hook
echo ""
echo "→ Installing pre-commit hook..."
mkdir -p .git/hooks

cat > .git/hooks/pre-commit << 'EOF'
#!/usr/bin/env bash
set -euo pipefail

# Pre-commit hook: enforce structure-only policy
# Prevents accidentally committing proof edits (allows PROOF_OK=1 override)

REPO_ROOT="$(git rev-parse --show-toplevel)"

# Get staged Lean files
changed=$(git diff --cached --name-only --diff-filter=ACMR | grep -E '\.lean$' || true)

if [ -z "$changed" ]; then
  # No Lean files changed, allow commit
  exit 0
fi

echo "Checking for proof edits in staged Lean files..."

# Run proof-guard on staged changes
if git diff --cached -- '*.lean' | "$REPO_ROOT/scripts/proof-guard.sh"; then
  exit 0
else
  exit 1
fi
EOF

chmod +x .git/hooks/pre-commit
echo "  ✓ Pre-commit hook installed at .git/hooks/pre-commit"

# 4. Make scripts executable
echo ""
echo "→ Making scripts executable..."
chmod +x scripts/*.sh
echo "  ✓ Scripts in scripts/ are now executable"

# 5. Show status
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Setup Complete!"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "Next steps:"
echo ""
echo "  1. Review .gitignore and adjust if needed"
echo "  2. Add files: git add ."
echo "  3. Create initial commit: git commit -m 'Initial commit: Lean formalization + LaTeX paper'"
echo ""
echo "  Optional: Connect to GitHub"
echo "    git remote add origin https://github.com/YOUR_USERNAME/YOUR_REPO.git"
echo "    git push -u origin main"
echo ""
echo "Structure-only policy is now enforced via pre-commit hook."
echo "To commit proof work, use: PROOF_OK=1 git commit -m '...'"
echo ""
