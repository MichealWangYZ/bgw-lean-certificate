#!/usr/bin/env bash
# Source this file so every tool uses the project-local Lean installation.
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export ELAN_HOME="$PROJECT_ROOT/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"

