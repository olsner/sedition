#!/bin/sh

set -e
#cabal update
exec cabal install -j`nproc`  --ghc-options=-dynamic --lib regex-posix trifecta network
