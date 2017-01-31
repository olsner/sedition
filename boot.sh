#!/bin/sh

set -e
cabal update
exec cabal install -j`nproc` regex-tdfa trifecta network
