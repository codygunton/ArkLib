#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in ArkLib.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_lint=0
run_docs=0
run_site=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint] [--docs] [--site]

Default checks:
  - lake build
  - fail on non-`sorry` warnings under ArkLib/Data/
  - fail on non-`sorry` warnings under ArkLib/Interaction/
  - ./scripts/check-imports.sh
  - python3 ./scripts/check-docs-integrity.py

Optional checks:
  --lint   Run ./scripts/lint-style.sh
  --docs   Run DISABLE_EQUATIONS=1 lake build ArkLib:docs
  --site   Run ./scripts/build-web.sh (implies --docs)
EOF
}

for arg in "$@"; do
  case "$arg" in
    --lint)
      run_lint=1
      ;;
    --docs)
      run_docs=1
      ;;
    --site)
      run_docs=1
      run_site=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "ERROR: Unknown flag: $arg" >&2
      usage >&2
      exit 1
      ;;
  esac
done

build_log="$(mktemp "${TMPDIR:-/tmp}/arklib-validate-build.XXXXXX.log")"
cleanup() {
  rm -f "$build_log"
}
trap cleanup EXIT

echo "# Building project"
lake build 2>&1 | tee "$build_log"

echo ""
echo "# Checking Data warning budget"
python3 ./scripts/check-warning-log.py "$build_log" \
  --path-prefix ArkLib/Data/ \
  --exclude-substring 'declaration uses `sorry`' \
  --label 'ArkLib/Data non-sorry warnings'

echo ""
echo "# Checking Interaction warning budget"
python3 ./scripts/check-warning-log.py "$build_log" \
  --path-prefix ArkLib/Interaction/ \
  --exclude-substring 'declaration uses `sorry`' \
  --label 'ArkLib/Interaction non-sorry warnings'

echo ""
echo "# Checking umbrella imports"
./scripts/check-imports.sh

echo ""
echo "# Checking docs integrity"
python3 ./scripts/check-docs-integrity.py

if (( run_lint )); then
  echo ""
  echo "# Running Lean style lint"
  ./scripts/lint-style.sh
fi

if (( run_docs )); then
  echo ""
  echo "# Building API docs"
  # doc-gen4 can overflow the default shell stack or segfault when all core
  # roots are rendered in one process. Build the docInfo database through Lake,
  # then render the same docs in two safe root groups.
  ulimit -s unlimited
  DISABLE_EQUATIONS=1 lake build ArkLib:docInfo
  docgen=".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"
  build_dir=".lake/build"
  DISABLE_EQUATIONS=1 "$docgen" fromDb \
    --build "$build_dir" \
    --manifest "$build_dir/doc-manifest-arklib-lake.json" \
    "$build_dir/api-docs.db" ArkLib Init Std Lake
  DISABLE_EQUATIONS=1 "$docgen" fromDb \
    --build "$build_dir" \
    --manifest "$build_dir/doc-manifest-arklib-lean.json" \
    "$build_dir/api-docs.db" ArkLib Init Std Lean
fi

if (( run_site )); then
  echo ""
  echo "# Building website and blueprint outputs"
  ./scripts/build-web.sh
fi

echo ""
echo "All requested validation checks passed."
