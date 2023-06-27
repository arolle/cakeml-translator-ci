#!/usr/bin/env bash
# Build HOL4 with prerequisites for CakeML.
# then set HOL4 read-only and build CakeML
# The commits of HOL4 and CakeML match.

set -euxo pipefail

HOL_COMMIT="56875629a42860effd84a80abd66e63a4c7a4961"
CAKEML_COMMIT="a500b998760b855e6d32428c2e39ce0f69a89131"

DIR="$(pwd)"

export HOLDIR="$DIR/HOL"
echo ":: HOLDIR: $HOLDIR"
git clone https://github.com/HOL-Theorem-Prover/HOL/ "$HOLDIR"
cd "$HOLDIR"
git checkout "$HOL_COMMIT"

poly < tools/smart-configure.sml
./bin/build --fullbuild

# chmod --recursive u+w "$HOLDIR"

{
cat <<EOF
examples/algorithms
examples/algorithms/unification/triangular/first-order
examples/balanced_bst
examples/bootstrap
examples/Crypto/AES
examples/Crypto/RC6
examples/Crypto/TEA
examples/formal-languages
examples/formal-languages/regular
examples/formal-languages/context-free
examples/fun-op-sem/lprefix_lub
examples/l3-machine-code/common
examples/machine-code/decompiler
examples/machine-code/hoare-triple
examples/machine-code/multiword
examples/miller/miller
EOF
} | while read -r dir; do
  echo ":: building HOLDIR/$dir"
  cd "$HOLDIR/$dir" && $HOLDIR/bin/Holmake
done

# compile dependencies of CakeML twice to avoid the following later failure
# when compiling CakeML:
#    :: building CAKEMLDIR/misc
#    Scanning $(HOLDIR)/examples/formal-languages/context-free
#    Holmake failed with exception: Io {cause = SysErr ("Permission denied", SOME EACCES), function = "TextIO.openOut", name = ".HOLMK/NTpropertiesTheory.sml.d"}
#    Raised from: ./basis/TextIO.sml: 258:0 - 258:0

{
cat <<EOF
examples/algorithms
examples/algorithms/unification/triangular/first-order
examples/balanced_bst
examples/bootstrap
examples/Crypto/AES
examples/Crypto/RC6
examples/Crypto/TEA
examples/formal-languages
examples/formal-languages/regular
examples/formal-languages/context-free
examples/fun-op-sem/lprefix_lub
examples/l3-machine-code/common
examples/machine-code/decompiler
examples/machine-code/hoare-triple
examples/machine-code/multiword
examples/miller/miller
EOF
} | while read -r dir; do
  echo ":: building HOLDIR/$dir"
  cd "$HOLDIR/$dir" && $HOLDIR/bin/Holmake
done

chmod --recursive a-w "$HOLDIR"

export CAKEMLDIR="$DIR/cakeml"
git clone https://github.com/CakeML/cakeml "$CAKEMLDIR"
cd "$CAKEMLDIR"

echo ":: CAKEMLDIR: $CAKEMLDIR"

git checkout "$CAKEML_COMMIT"

{
cat <<EOF
developers
misc
semantics
basis/pure
characteristic
translator
translator/monadic
compiler/parsing
basis
unverified/sexpr-bootstrap
EOF
} | while read -r dir; do
  echo ":: building CAKEMLDIR/$dir"
  cd "$CAKEMLDIR/$dir" && "$HOLDIR/bin/Holmake"
done

{
cat <<EOF
developers
misc
semantics
basis/pure
characteristic
translator
translator/monadic
compiler/parsing
basis
unverified/sexpr-bootstrap
EOF
} | while read -r dir; do
  echo ":: building CAKEMLDIR/$dir"
  cd "$CAKEMLDIR/$dir" && "$HOLDIR/bin/Holmake"
done

