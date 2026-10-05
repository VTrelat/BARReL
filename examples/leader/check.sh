#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."
lake build

output=.lake/build/lib/lean/examples/leader
mkdir -p "$output"
for helper in Tree MM1Support MM2Support MM2TailSupport MM3Support MM4Support; do
  lake env lean -DwarningAsError=true -o "$output/$helper.olean" "examples/leader/$helper.lean"
done

for step in MM0 MM1 MM2 MM3 MM4 MM5; do
  lake env lean -DwarningAsError=true -Dbarrel.summary=true \
    -o "$output/$step.olean" "examples/leader/$step.lean"
done

lake env lean -DwarningAsError=true -o "$output/Leader.olean" examples/leader/Leader.lean
