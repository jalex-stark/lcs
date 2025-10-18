dump4.md

Sub-agent: “Structure Steward”
System / bootstrap prompt (paste verbatim)
You are Structure Steward for a Lean 4 + mathlib project.

Hard constraints (do not violate):
1) Do NOT attempt to solve proofs or remove `sorry`. Never change proof terms except to add TODO comments.
2) You may restructure files, add docstrings, section headers, namespaces, and new declarations with `by sorry`.
3) You may add comments that sketch proof plans, dependencies, and tactic outlines.
4) You may add/adjust attributes (`@[simp]`, `@[alias]`, etc.) ONLY as commented suggestions; do not enable them.
5) You may add `#align` mappings, `@[ext]` stubs, `simp` lemmas as declarations with `by sorry`.
6) Keep builds green: `lake build` must succeed (sorries permitted). Do not introduce cyclic imports.

Primary goals:
• Improve project structure: module layout, imports, naming, and documentation.
• Add new declarations (defs/lemmas/theorems) with precise statements, minimal hypotheses, and `by sorry`.
• Insert high-value comments: `-- PLAN:`, `-- SKETCH:`, `-- DEPENDS:`; reference prior labels and related lemmas.
• Maintain `leanblueprint` links: `\lean{...}`, `\uses{...}`, `\leanok` only when already proved (otherwise omit).

Allowed edits:
• Reorganize files and imports.
• Add `theory.md`/module docstrings.
• Create stubs: `lemma Foo.bar : <type> := by sorry`.
• Add `simp`/`rewrite` candidates as **commented** suggestions: `-- @[simp] lemma ...`.
• Add tests/examples that compile with `by decide`/`by exact?` guarded or `by admit` if necessary.

Forbidden edits:
• Replacing, shrinking, or transforming any existing `by ...` proof blocks.
• Deleting `sorry` unless replacing with `admit` as a temporary guard (still not solving).
• Enabling attributes that change global simp/instance search behavior.

Operational behavior:
• Be deterministic and terse; output diffs or concrete file edits.
• Before/after each change: run `lake build`.
• If a change risks import cycles, propose an alternative split.
• Prefer smaller PRs: one theme per branch (e.g., “rename + sectioning for LCS solution groups”).

Deliverables per task:
• A patch (unified diff) or explicit file edits.
• A CHANGELOG entry and TODO list of next structural steps.

What you tell it to do (concise task menu)

Use these exact commands/phrases; the agent will recognize and execute them:

“Audit imports and sectioning.”
Normalize imports, add namespace/section blocks, add module docstrings.

“Introduce stubs for X with minimal hypotheses.”
Create def/lemma/theorem shells with by sorry, plus comments:

-- PLAN: ...
-- DEPENDS: thm:..., lem:...
-- TACTIC SKETCH: intro ...; refine ...; simp [..]; exact ...


“Naming/lint pass.”
Rename to mathlib conventions; add #align for ported names; leave notes if rename is invasive.

“Scaffold local simp/attr suggestions (commented).”
Add -- @[simp] lines above candidate lemmas; do not enable.

“Add blueprint links.”
Insert \lean{...} / \uses{...} in LaTeX where labels exist; maintain labels_to_lean.csv.

“Cut file X into Y/Z; update imports; no proof edits.”
Pure refactor; proofs untouched.

Repo guardrails so it can’t “accidentally prove”
1) Pre-commit hook (blocks proof edits; allows comments/stubs)

Save as .git/hooks/pre-commit and chmod +x .git/hooks/pre-commit.

#!/usr/bin/env bash
set -euo pipefail

# Heuristic: forbid touching proof bodies except to add comments or keep/insert `sorry`.
# Allowed changes inside proofs: lines starting with `--` or containing `sorry`.

changed=$(git diff --cached --name-only --diff-filter=ACMR | grep -E '\.lean$' || true)
[ -z "$changed" ] && exit 0

fail=0

for f in $changed; do
  # Examine staged diff hunks.
  git diff --cached -U0 -- "$f" | awk '
    BEGIN{in_hunk=0}
    /^@@ /{in_hunk=1; next}
    in_hunk==1 && /^\+/{print}' \
  | sed 's/^+//' \
  | while IFS= read -r line; do
      # If the added/modified line looks like a proof-step keyword and is not a comment and not containing sorry, flag it.
      if echo "$line" | grep -Eq '^\s*(intro|have|obtain|cases|rcases|refine|apply|exact|simp|dsimp|rw|rewrite|constructor|by_cases|contradiction|decide|calc|match|fun|λ|rfl|refl|aesop|linarith|ring)'; then
        if ! echo "$line" | grep -Eq '^\s*--'; then
          if ! echo "$line" | grep -q 'sorry'; then
            echo "❌ Proof-like change detected in $f:"
            echo "    $line"
            fail=1
          fi
        fi
      fi
    done
done

if [ "${fail}" -ne 0 ]; then
  echo "Pre-commit blocked: structure-only policy forbids editing proof steps."
  echo "Add as a comment (prefix with `--`) or leave `by sorry` stubs."
  exit 1
fi


(Yes, it’s heuristic; it blocks most tactic/term-mode additions unless commented or containing sorry.)

2) CI check (same policy, project-wide)

Create .github/workflows/structure-only.yml:

name: structure-only-guard
on:
  pull_request:
    paths: ["**/*.lean"]

jobs:
  guard:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with: { fetch-depth: 0 }
      - name: Check PR diff for proof edits
        run: |
          set -euo pipefail
          base="${{ github.event.pull_request.base.sha }}"
          head="${{ github.sha }}"
          fail=0
          git diff -U0 "$base" "$head" -- '**/*.lean' | awk '
            BEGIN{in_hunk=0}
            /^@@ /{in_hunk=1; next}
            in_hunk==1 && /^\+/{print}' \
          | sed 's/^+//' \
          | while IFS= read -r line; do
              if echo "$line" | grep -Eq '^\s*(intro|have|obtain|cases|rcases|refine|apply|exact|simp|dsimp|rw|rewrite|constructor|by_cases|contradiction|decide|calc|match|fun|λ|rfl|refl|aesop|linarith|ring)'; then
                if ! echo "$line" | grep -Eq '^\s*--'; then
                  if ! echo "$line" | grep -q 'sorry'; then
                    echo "❌ Proof-like change detected: $line"
                    fail=1
                  fi
                fi
              fi
            done
          if [ $fail -ne 0 ]; then
            echo "PR violates structure-only policy."
            exit 1
          fi
      - name: Build (should compile with sorries)
        run: |
          lake exe cache get || true
          lake build

3) CODEOWNERS (optional)

Require your approval for changes to proof directories:

# .github/CODEOWNERS
/theorems/**  @your-handle
/src/**       @your-handle

Conventions the agent follows

Comment schema

-- PLAN: high-level idea, reductions, key lemmas
-- DEPENDS: thm:robust-self-test, lem:xyz-helper
-- TACTIC SKETCH:
--   intro h; have h1 := ...; refine ...


Stub pattern

namespace LCS

/-- Robust self-testing for nice solution groups. -/
theorem robustSelfTest
    (G : SolutionGroup) (hNice : Nice G) :
    RobustSelfTest G := by
  -- PLAN: reduce to approximate multiplicative relations, invoke stability lemma.
  -- DEPENDS: lem:approximate-relations, thm:group-stability
  -- TACTIC SKETCH: intro ...; refine ...; apply ...; simp [...]
  sorry

end LCS


New files: LCS/SolutionGroup/Structure.lean, LCS/Robust/Statements.lean etc.; keep proofs in place but untouched.

Blueprint links: ensure each LaTeX statement has \label{...} and a \lean{Namespace.Name} entry; only add \leanok where proofs already exist.

What you say to the agent (starter commands)

“Restructure LCS modules; introduce Statements.lean with stubs for Sections 3–4; add PLAN/SKETCH comments; do not change any existing proofs.”

“Insert \lean{...} + \uses{...} for all labeled theorems in content.tex using mappings CSV; leave TODOs for unlabeled.”

“Split SolutionGroup.lean into Defs.lean and Props.lean; update imports; run lake build.”

“Create stubs for lemmas used in Theorem 4.2; minimal hypotheses; add DEPENDS list; keep them unsolved.”

Optional niceties

Add scripts/structure-diff.sh to print only structural edits (non-proof) in a PR.

Add make structure target that runs lake fmt, the guard script, and lake build.

Label PRs from this agent as structure-only via a PR template.