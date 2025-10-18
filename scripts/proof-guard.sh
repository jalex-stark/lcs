#!/usr/bin/env bash
set -euo pipefail

# proof-guard.sh: Detect proof-related changes in Lean files
#
# Usage:
#   git diff ... | ./scripts/proof-guard.sh
#   PROOF_OK=1 git diff ... | ./scripts/proof-guard.sh  # override
#
# Exit codes:
#   0 = no proof edits detected (or PROOF_OK=1)
#   1 = proof edits detected

# Allow override for legitimate proof work
if [ "${PROOF_OK:-0}" = "1" ]; then
  echo "✓ PROOF_OK=1 set, allowing proof edits"
  exit 0
fi

# Process diff input, extract added/modified lines
fail=0
file_context=""

while IFS= read -r line; do
  # Track current file for error messages
  if [[ "$line" =~ ^diff\ --git\ a/(.+)\ b/.+ ]]; then
    file_context="${BASH_REMATCH[1]}"
  fi

  # Only process added lines (start with '+')
  if [[ "$line" =~ ^[+] ]] && [[ ! "$line" =~ ^[+]{3} ]]; then
    # Remove leading '+'
    content="${line:1}"

    # Skip if line is a comment
    if [[ "$content" =~ ^[[:space:]]*-- ]]; then
      continue
    fi

    # Skip if line contains 'sorry' or 'admit'
    if [[ "$content" =~ sorry|admit ]]; then
      continue
    fi

    # Check for proof-related keywords
    # Match common tactics and term-mode proof constructs
    if [[ "$content" =~ ^[[:space:]]*(intro|have|obtain|cases|rcases|refine|apply|exact|simp|dsimp|rw|rewrite|constructor|by_cases|contradiction|decide|calc|match|fun|λ|rfl|refl|aesop|linarith|ring|omega|norm_num|field_simp|conv|induction|use|exists|ext|congr|trivial|assumption|done|focus|all_goals|any_goals|repeat|try|iterate|suffices|show|this)[[:space:]\(] ]]; then
      echo "❌ Proof-like change detected in ${file_context}:"
      echo "    ${content}"
      fail=1
    fi

    # Check for term-mode proof constructs that might not have space/paren
    # (more conservative patterns to reduce false positives)
    if [[ "$content" =~ \<\;|\;[[:space:]]*\<|\|[[:space:]]*rw|\|[[:space:]]*simp ]]; then
      echo "❌ Proof-like change detected in ${file_context}:"
      echo "    ${content}"
      fail=1
    fi
  fi
done

if [ "${fail}" -ne 0 ]; then
  echo ""
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "Structure-only policy: Proof edits detected"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo ""
  echo "This repository enforces a structure-only policy. You can:"
  echo ""
  echo "  1. Add proof edits as comments (prefix with '--'):"
  echo "     -- intro h; have h1 := ...; refine ..."
  echo ""
  echo "  2. Leave stubs with 'sorry' or 'admit':"
  echo "     theorem foo : ... := by sorry"
  echo ""
  echo "  3. Override if this is legitimate proof work:"
  echo "     PROOF_OK=1 git commit -m \"Prove Lemma 4.4(b)\""
  echo ""
  echo "See .claude/agents/structure-steward.md for policy details."
  echo ""
  exit 1
fi

echo "✓ No proof edits detected"
exit 0
