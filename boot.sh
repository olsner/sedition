#!/bin/sh

set -e
cabal update
exec cabal install regex-tdfa trifecta network
