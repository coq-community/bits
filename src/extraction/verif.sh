#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
# Some handmade patching needed for unknown reasons
patch axioms8.ml magic.patch
patch axioms16.ml magic.patch

echo "Verifying 8bit"
ocamlbuild axioms8.native && ./axioms8.native
echo "... Ok"
echo "Verifying 16bit"
ocamlbuild test.native && ./test.native
echo "... Ok"
cd -
