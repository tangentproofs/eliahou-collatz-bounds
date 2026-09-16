#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
rg -n '^theorem |^lemma ' Results.lean
