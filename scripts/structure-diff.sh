#!/usr/bin/env bash
set -euo pipefail

# structure-diff.sh: Show only structural changes in Lean files
#
# Usage:
#   ./scripts/structure-diff.sh [git-diff-args]
#   ./scripts/structure-diff.sh HEAD~1 HEAD
#   ./scripts/structure-diff.sh main..feature-branch
#
# This filters git diff output to show only structural changes:
# - New declarations (theorem, lemma, def, structure, class, instance)
# - Import changes
# - Namespace/section changes
# - Comments (module docs, docstrings, PLAN/DEPENDS/SKETCH)
# - Attribute annotations
#
# Hides changes to proof bodies (lines inside `by ...` blocks).

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

# Get diff with context
DIFF_ARGS=("$@")
if [ ${#DIFF_ARGS[@]} -eq 0 ]; then
  # Default: show staged changes
  DIFF_ARGS=("--cached")
fi

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Structural Changes Only"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Run git diff and filter
git diff "${DIFF_ARGS[@]}" -- '*.lean' | awk '
BEGIN {
  in_hunk = 0
  in_proof = 0
  file_header = ""
  hunk_header = ""
  show_hunk = 0
  buffered_lines = ""
}

# File headers (diff --git, index, ---, +++)
/^diff --git/ || /^index / || /^---/ || /^\+\+\+/ {
  file_header = file_header $0 "\n"
  next
}

# Hunk headers (@@ ... @@)
/^@@ / {
  if (show_hunk) {
    # Flush previous hunk
    if (file_header != "") {
      printf "%s", file_header
      file_header = ""
    }
    printf "%s", hunk_header
    printf "%s", buffered_lines
  }

  # Start new hunk
  hunk_header = $0 "\n"
  buffered_lines = ""
  show_hunk = 0
  in_hunk = 1
  next
}

# Process lines within hunks
in_hunk {
  line = $0

  # Detect proof start: lines with "by" followed by tactic
  # (Conservative: only flag if it looks like start of tactic proof)
  if (line ~ /^[+ ].*:=.*by[[:space:]]*$/ || line ~ /^[+ ].*:=.*by[[:space:]]+[a-z]/) {
    in_proof = 1
  }

  # Detect proof end: dedented line, or theorem/lemma/def keyword
  if (in_proof && (line ~ /^[+ ](theorem|lemma|def|instance|class|structure|end|namespace|section|import|open|variable|#)/ || line ~ /^[+ ]$/ || line ~ /^[+ ][^ ]/)) {
    in_proof = 0
  }

  # Determine if this line is structural
  is_structural = 0

  # Always show: imports, namespace, section, comments, blank lines
  if (line ~ /^[+ ](import|open|namespace|section|end|variable|#|$)/ || line ~ /^[+ ][[:space:]]*--/ || line ~ /^[+ ][[:space:]]*\/-/ || line ~ /^[+ ][[:space:]]*$/) {
    is_structural = 1
  }

  # Show new declarations (theorem, lemma, def, etc.)
  if (line ~ /^[+](theorem|lemma|def|instance|class|structure|inductive|abbrev|axiom|example)/) {
    is_structural = 1
  }

  # Show attribute changes
  if (line ~ /^[+]@\[/) {
    is_structural = 1
  }

  # Show declaration signatures (lines with type annotation :)
  # but not if we are in proof mode
  if (!in_proof && line ~ /^[+].*:/) {
    is_structural = 1
  }

  # Context lines (no +/-) are shown if structural content is nearby
  if (line ~ /^[^+\-]/) {
    is_structural = 1
  }

  # If inside proof and line is an added line (+), skip it
  if (in_proof && line ~ /^[+]/ && !is_structural) {
    buffered_lines = buffered_lines "    " substr(line, 2) " # (proof body change, hidden)\n"
    next
  }

  # Otherwise, buffer the line
  if (is_structural || line ~ /^[-]/) {
    buffered_lines = buffered_lines line "\n"
    show_hunk = 1
  }
}

END {
  # Flush final hunk if any
  if (show_hunk) {
    if (file_header != "") {
      printf "%s", file_header
    }
    printf "%s", hunk_header
    printf "%s", buffered_lines
  }
}
'

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "End of structural diff"
echo ""
echo "Note: Proof body changes are hidden. For full diff, use:"
echo "  git diff ${DIFF_ARGS[*]}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
