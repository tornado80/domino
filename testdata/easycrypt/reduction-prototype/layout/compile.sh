#!/bin/bash
# Compiles one prototype of story 101 against a fresh export of its fixture.
# usage: compile.sh <domino> <project> <theorem> <prototype dir>
# It compiles every file of the prototype on its own, in dependency order: the router, the oracle
# files, the joining file, the proposition file. Compiling only the last file is not enough:
# `require` does not check the proofs of a required file again.
# Small fixtures only. Run it under a memory cap, e.g.
#   systemd-run --user --scope -p MemoryMax=6G timeout 600 compile.sh ...
set -euo pipefail
domino=$1 project=$2 theorem=$3 proto=$4
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
"$domino" easycrypt export --project "$project" --theorem "$theorem" --out "$work/out" --progress none >/dev/null
tree="$work/out/$theorem"
# The prototype replaces the exported reduction and proposition files.
rm -f "$tree"/Red_*.ec "$tree"/Prop_*.ec
cp "$proto"/*.ec "$tree"/
if grep -l admit "$proto"/*.ec; then echo "a prototype file admits" >&2; exit 1; fi
cd "$tree"
router=$(cd "$proto" && ls Red_*_Router.ec)
join="${router%_Router.ec}.ec"
oracles=$(cd "$proto" && ls Red_*.ec | grep -vx -e "$router" -e "$join")
for f in $router $oracles $join $(cd "$proto" && ls Prop_*.ec); do
  echo "compile $f"
  easycrypt compile -no-eco -I . "$f"
done
